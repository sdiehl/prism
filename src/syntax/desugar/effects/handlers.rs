//! Handler-arm sugar and named handler instances. Resumability checks,
//! tail-resumptive/val/final clause lowering, and the `with f <- handler`
//! rewrite that clones handled ops into a fresh private effect.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::escape::{escapes, free_resume};
use super::{rw, Binding, InstanceOps, Vars};
use crate::error::{ErrKind, TypeError};
use crate::names::{self, CONT};
use crate::syntax::ast::{Core, EffOp, EffectDecl, Expr, Grade, HandlerArm, SugarArm, Ty, S};
use crate::syntax::desugar::{call, evar, sp, Cx};

pub(super) type Vals = Vec<(String, S<Expr<Core>>)>;

fn ty_vars(t: &Ty, out: &mut BTreeSet<String>) {
    if let Ty::Var(n) = t {
        out.insert(n.clone());
        return;
    }
    // Every other variant just recurses; the spine reaches App args, row-literal
    // labels, and a function's effect-row label arguments that the old hand-match
    // skipped.
    t.each_child(&mut |c| ty_vars(c, out));
}

// A var in the return type but no parameter and no effect parameter: fresh
// per perform site, so no value can ever flow back through the continuation.
fn poly_ret(sig: &EffOp, eff_params: &[String]) -> bool {
    let mut pv = BTreeSet::new();
    for p in &sig.params {
        ty_vars(p, &mut pv);
    }
    let mut rv = BTreeSet::new();
    ty_vars(&sig.ret, &mut rv);
    rv.into_iter()
        .any(|v| !pv.contains(&v) && !eff_params.contains(&v))
}

// The declared grade of `op`, or `Many` for an op with no signature in scope
// (a compiler-synthesized effect never carries a stricter grade at a user-
// written clause, so the check never bites it).
fn declared_grade(op: &str, cx: &Cx) -> Grade {
    cx.op_sigs
        .get(op)
        .map_or(Grade::Many, |(_, _, sig)| sig.grade)
}

// Reject a handler clause more general than its op's declared grade (the whole
// typing rule: clause grade at most op grade). The caret lands on the clause,
// naming the op, its declared grade, and what the clause did.
fn check_grade(op: &str, clause: Grade, span: Span, cx: &Cx) -> Result<(), TypeError> {
    let declared = declared_grade(op, cx);
    if clause <= declared {
        return Ok(());
    }
    let did = match clause {
        Grade::Never => unreachable!("Never is the least grade, never exceeds a declared grade"),
        Grade::Once => "this clause resumes the continuation",
        Grade::Many => "this clause may resume the continuation more than once",
    };
    let limit = match declared {
        Grade::Never => "which never resumes",
        Grade::Once => "which resumes exactly once, in tail position",
        Grade::Many => unreachable!("Many is the greatest grade, nothing exceeds it"),
    };
    Err(ErrKind::HandlerGradeExceeded {
        op: op.to_string(),
        grade: declared.word().to_string(),
        limit: limit.to_string(),
        did: did.to_string(),
    }
    .at(span))
}

// The grade of a bare (keyword-free) clause, read from how its body uses the
// continuation binder `k`. A single direct tail application is `Once`; no use is
// `Never`; anything else (more than one application, `k` used as a plain value,
// `k` applied under a nested lambda whose call count is unknown, or `k` resumed
// in non-tail position) is `Many`. This is the same single-shot classification
// `effect_lower::erase_var` recomputes over Core, run here as the up-front
// check; it is conservative, so a clause it cannot prove to be a single tail
// resume is `Many` and a stricter declared grade rejects it. The clause body
// starts in tail position.
fn bare_ctl_grade(body: &S<Expr<Core>>, k: &str) -> Grade {
    let mut direct = 0usize;
    let mut escaped = false;
    scan_k(body, k, false, true, &mut direct, &mut escaped);
    if escaped || direct > 1 {
        Grade::Many
    } else if direct == 1 {
        Grade::Once
    } else {
        Grade::Never
    }
}

// Classify every occurrence of `k` in `e`: a direct call head at lambda depth
// zero in tail position is a tail resume (counted); anything else is an escape.
// `under` tracks whether the subtree sits inside a lambda, where the call count
// is unknown. `tail` tracks whether the subtree sits in tail position, since
// `once` promises exactly-one resume in tail position: a resume that is an
// operand of some enclosing computation (non-tail) is not that single tail
// resume and forces `Many`. Core phase carries no `Sugar`, so this covers every
// residual `Expr` variant.
fn scan_k(
    e: &S<Expr<Core>>,
    k: &str,
    under: bool,
    tail: bool,
    direct: &mut usize,
    escaped: &mut bool,
) {
    match &e.node {
        Expr::Var(n) if n == k => *escaped = true,
        Expr::Call(h, args) => {
            if matches!(&h.node, Expr::Var(n) if n == k) {
                // Under a lambda the call count is unknown; in non-tail position
                // the resume is not the single tail resume `once` promises.
                // Either way it escapes the counted-tail-resume case.
                if under || !tail {
                    *escaped = true;
                } else {
                    *direct += 1;
                }
            } else {
                scan_k(h, k, under, false, direct, escaped);
            }
            for a in args {
                scan_k(a, k, under, false, direct, escaped);
            }
        }
        Expr::Lam(_, b) => scan_k(b, k, true, false, direct, escaped),
        // Tail position flows to the branch results; the scrutinee/condition and
        // the let-bound value are always non-tail.
        Expr::If(c, t, el) => {
            scan_k(c, k, under, false, direct, escaped);
            scan_k(t, k, under, tail, direct, escaped);
            scan_k(el, k, under, tail, direct, escaped);
        }
        Expr::Let(_, v, b) => {
            scan_k(v, k, under, false, direct, escaped);
            scan_k(b, k, under, tail, direct, escaped);
        }
        Expr::Match(scrut, arms) => {
            scan_k(scrut, k, under, false, direct, escaped);
            for a in arms {
                if let Some(g) = &a.guard {
                    scan_k(g, k, under, false, direct, escaped);
                }
                scan_k(&a.body, k, under, tail, direct, escaped);
            }
        }
        // Every other form (Bin, Neg, Tuple, records, index, ...) puts its
        // children in non-tail position: a resume there is an operand, not a
        // tail call.
        _ => e
            .node
            .each_child(&mut |child| scan_k(child, k, under, false, direct, escaped)),
    }
}

fn check_resumable(op: &str, span: Span, cx: &Cx) -> Result<(), TypeError> {
    if cx
        .op_sigs
        .get(op)
        .is_some_and(|(_, ps, sig)| poly_ret(sig, ps))
    {
        return Err(ErrKind::OpPolymorphicReturn { op: op.to_string() }.at(span));
    }
    Ok(())
}

// Lower handler arm sugar. `once op(ps) => e` is tail-resumptive for `op(ps, k)
// => k(e)`. `val v = e` binds e once before the handler installs, and each `v()`
// in the handled block resumes with it. `never op(ps) => e` never resumes,
// so a free `resume` is a targeted error and the hygienic CONT binder goes
// unused, discarding the captured continuation.
pub(super) fn rw_arms(
    arms: &[HandlerArm],
    env: &Vars,
    cx: &mut Cx,
) -> Result<(Vec<HandlerArm<Core>>, Vals), TypeError> {
    let mut vals = Vec::new();
    let mut arms2 = Vec::new();
    for a in arms {
        arms2.push(match a {
            HandlerArm::Return(x, body) => {
                let mut env2 = env.clone();
                env2.insert(x.clone(), Binding::Local);
                HandlerArm::Return(x.clone(), rw(body, &env2, cx)?)
            }
            HandlerArm::Op(op, ps, k, body) => {
                check_resumable(op, body.span, cx)?;
                let mut env2 = env.clone();
                for p in ps {
                    env2.insert(p.clone(), Binding::Local);
                }
                env2.insert(k.clone(), Binding::Local);
                let body2 = rw(body, &env2, cx)?;
                // A bare (keyword-free) clause's grade is read from how it uses `k`.
                check_grade(op, bare_ctl_grade(&body2, k), body.span, cx)?;
                HandlerArm::Op(op.clone(), ps.clone(), k.clone(), body2)
            }
            HandlerArm::Sugar(SugarArm::Once(op, ps, body)) => {
                check_resumable(op, body.span, cx)?;
                // `once` resumes exactly once, in tail position: grade Once.
                check_grade(op, Grade::Once, body.span, cx)?;
                let mut env2 = env.clone();
                for p in ps {
                    env2.insert(p.clone(), Binding::Local);
                }
                let body2 = rw(body, &env2, cx)?;
                let bs = body2.span;
                let resume = call(evar(CONT, Span::empty(bs.start)), vec![body2], bs);
                HandlerArm::Op(op.clone(), ps.clone(), CONT.into(), resume)
            }
            HandlerArm::Sugar(SugarArm::Val(v, init)) => {
                check_resumable(v, init.span, cx)?;
                // `val` resumes once with an install-time constant: grade One.
                check_grade(v, Grade::Once, init.span, cx)?;
                let init2 = rw(init, env, cx)?;
                let tmp = names::val_tmp(cx.next.bump());
                let is = init2.span;
                vals.push((tmp.clone(), init2));
                let resume = call(evar(CONT, Span::empty(is.start)), vec![evar(&tmp, is)], is);
                HandlerArm::Op(v.clone(), Vec::new(), CONT.into(), resume)
            }
            HandlerArm::Sugar(SugarArm::Never(op, ps, body)) => {
                if let Some(bad) = free_resume(body, false) {
                    return Err(ErrKind::NeverClauseResumes.at(bad));
                }
                // `never` never resumes (grade Never), the least grade, so it
                // satisfies any declared grade with no further check.
                let mut env2 = env.clone();
                for p in ps {
                    env2.insert(p.clone(), Binding::Local);
                }
                HandlerArm::Op(op.clone(), ps.clone(), CONT.into(), rw(body, &env2, cx)?)
            }
        });
    }
    Ok((arms2, vals))
}

pub(super) fn wrap_vals(vals: Vals, handled: S<Expr<Core>>, span: Span) -> S<Expr<Core>> {
    vals.into_iter().rev().fold(handled, |acc, (tmp, init)| {
        sp(Expr::Let(tmp, Box::new(init), Box::new(acc)), span)
    })
}

const fn arm_op(a: &HandlerArm) -> Option<&String> {
    match a {
        HandlerArm::Return(..) => None,
        HandlerArm::Op(op, ..)
        | HandlerArm::Sugar(
            SugarArm::Once(op, ..) | SugarArm::Never(op, ..) | SugarArm::Val(op, ..),
        ) => Some(op),
    }
}

fn rename_arm(a: HandlerArm, ops: &BTreeMap<String, String>) -> HandlerArm {
    let m = |op: String| ops.get(&op).cloned().unwrap_or(op);
    match a {
        HandlerArm::Return(x, b) => HandlerArm::Return(x, b),
        HandlerArm::Op(op, ps, k, b) => HandlerArm::Op(m(op), ps, k, b),
        HandlerArm::Sugar(SugarArm::Once(op, ps, b)) => {
            HandlerArm::Sugar(SugarArm::Once(m(op), ps, b))
        }
        HandlerArm::Sugar(SugarArm::Never(op, ps, b)) => {
            HandlerArm::Sugar(SugarArm::Never(m(op), ps, b))
        }
        HandlerArm::Sugar(SugarArm::Val(op, b)) => HandlerArm::Sugar(SugarArm::Val(m(op), b)),
    }
}

// `with f <- handler { .. }` generalizes the `var` machinery: the handled ops
// are cloned into a fresh private effect (op@f@n, unforgeable since `@` cannot
// appear in source identifiers), `f.op(args)` dispatches to it, the handle here
// discharges it, and the escape analysis keeps the instance from outliving its
// handler.
pub(super) fn rw_named(
    f: &str,
    body: &S<Expr>,
    arms: &[HandlerArm],
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    let n = cx.next.bump();
    let mut ops = BTreeMap::new();
    let mut eff = None;
    let mut eff_params = Vec::new();
    let mut decl_ops = Vec::new();
    for op in arms.iter().filter_map(arm_op) {
        let Some((src_eff, src_params, sig)) = cx.op_sigs.get(op) else {
            return Err(ErrKind::UnknownHandlerOp {
                op: op.clone(),
                handler: f.to_string(),
            }
            .at(span));
        };
        // All handled ops must come from one effect: the private EffectDecl below
        // records a single `eff_params`, so mixing effects would leave later ops'
        // signatures referencing type params that are not in scope.
        match &eff {
            None => {
                eff = Some(src_eff.clone());
                eff_params.clone_from(src_params);
            }
            Some(prev) if prev != src_eff => {
                return Err(ErrKind::HandlerMixesEffects {
                    handler: f.to_string(),
                    first: prev.clone(),
                    second: src_eff.clone(),
                }
                .at(span));
            }
            Some(_) => {}
        }
        let mangled = names::named_op(op, f, n);
        decl_ops.push(EffOp {
            name: mangled.clone(),
            params: sig.params.clone(),
            ret: sig.ret.clone(),
            // The cloned private op keeps the source op's declared grade, so a
            // named handler is checked against the same multiplicity.
            grade: sig.grade,
        });
        ops.insert(op.clone(), mangled);
    }
    let Some(eff) = eff else {
        return Err(ErrKind::HandlerNoOps {
            handler: f.to_string(),
        }
        .at(span));
    };
    let eff_name = names::named_effect(&eff, f, n);
    for op in &decl_ops {
        cx.op_sigs.insert(
            op.name.clone(),
            (eff_name.clone(), eff_params.clone(), op.clone()),
        );
    }
    cx.effects.push(EffectDecl {
        name: eff_name,
        params: eff_params,
        ops: decl_ops,
        span,
    });
    let renamed: Vec<HandlerArm> = arms.iter().cloned().map(|a| rename_arm(a, &ops)).collect();
    let (arms2, vals) = rw_arms(&renamed, env, cx)?;
    let mut env2 = env.clone();
    env2.insert(f.into(), Binding::Instance(InstanceOps::from_names(&ops)));
    let body2 = rw(body, &env2, cx)?;
    let opset: BTreeSet<String> = ops.into_values().collect();
    if let Some(bad) = escapes(&body2, &opset, &cx.ctors, &mut BTreeSet::new()) {
        return Err(ErrKind::HandlerEscapes {
            handler: f.to_string(),
        }
        .at(bad));
    }
    let handled = sp(Expr::Handle(Box::new(body2), arms2), span);
    Ok(wrap_vals(vals, handled, span))
}
