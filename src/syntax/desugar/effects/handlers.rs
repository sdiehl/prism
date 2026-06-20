//! Handler-arm sugar and named handler instances. Resumability checks,
//! tail-resumptive/val/final clause lowering, and the `with f <- handler`
//! rewrite that clones handled ops into a fresh private effect.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::escape::{escapes, free_resume};
use super::{rw, Binding, Vars};
use crate::error::TypeError;
use crate::names::{self, CONT};
use crate::syntax::ast::{Core, EffOp, EffectDecl, Expr, HandlerArm, SugarArm, Ty, S};
use crate::syntax::desugar::{call, evar, sp, Cx};

pub(super) type Vals = Vec<(String, S<Expr<Core>>)>;

fn ty_vars(t: &Ty, out: &mut BTreeSet<String>) {
    match t {
        Ty::Var(n) => {
            out.insert(n.clone());
        }
        Ty::Forall(_, b) => ty_vars(b, out),
        Ty::Fun(ps, _, r) => {
            for p in ps {
                ty_vars(p, out);
            }
            ty_vars(r, out);
        }
        Ty::Con(_, ps) | Ty::Tuple(ps) => {
            for p in ps {
                ty_vars(p, out);
            }
        }
        _ => {}
    }
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

fn check_resumable(op: &str, span: Span, cx: &Cx) -> Result<(), TypeError> {
    if cx
        .op_sigs
        .get(op)
        .is_some_and(|(_, ps, sig)| poly_ret(sig, ps))
    {
        return Err(TypeError::Other {
            span,
            msg: format!(
                "op `{op}` has a polymorphic return type and can only be handled by `final ctl`"
            ),
        });
    }
    Ok(())
}

// Lower handler arm sugar. `fun op(ps) => e` is tail-resumptive for `op(ps, k)
// => k(e)`. `val v = e` binds e once before the handler installs, and each `v()`
// in the handled block resumes with it. `final ctl op(ps) => e` never resumes,
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
                HandlerArm::Op(op.clone(), ps.clone(), k.clone(), rw(body, &env2, cx)?)
            }
            HandlerArm::Sugar(SugarArm::Fun(op, ps, body)) => {
                check_resumable(op, body.span, cx)?;
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
                let init2 = rw(init, env, cx)?;
                let tmp = names::val_tmp(cx.next.bump());
                let is = init2.span;
                vals.push((tmp.clone(), init2));
                let resume = call(evar(CONT, Span::empty(is.start)), vec![evar(&tmp, is)], is);
                HandlerArm::Op(v.clone(), Vec::new(), CONT.into(), resume)
            }
            HandlerArm::Sugar(SugarArm::Final(op, ps, body)) => {
                if let Some(bad) = free_resume(body, false) {
                    return Err(TypeError::Other {
                        span: bad,
                        msg: "final ctl clause cannot resume".into(),
                    });
                }
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
            SugarArm::Fun(op, ..) | SugarArm::Final(op, ..) | SugarArm::Val(op, ..),
        ) => Some(op),
    }
}

fn rename_arm(a: HandlerArm, ops: &BTreeMap<String, String>) -> HandlerArm {
    let m = |op: String| ops.get(&op).cloned().unwrap_or(op);
    match a {
        HandlerArm::Return(x, b) => HandlerArm::Return(x, b),
        HandlerArm::Op(op, ps, k, b) => HandlerArm::Op(m(op), ps, k, b),
        HandlerArm::Sugar(SugarArm::Fun(op, ps, b)) => {
            HandlerArm::Sugar(SugarArm::Fun(m(op), ps, b))
        }
        HandlerArm::Sugar(SugarArm::Final(op, ps, b)) => {
            HandlerArm::Sugar(SugarArm::Final(m(op), ps, b))
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
            return Err(TypeError::Other {
                span,
                msg: format!("unknown effect operation `{op}` in handler `{f}`"),
            });
        };
        if eff.is_none() {
            eff_params.clone_from(src_params);
        }
        eff.get_or_insert_with(|| src_eff.clone());
        let mangled = names::named_op(op, f, n);
        decl_ops.push(EffOp {
            name: mangled.clone(),
            params: sig.params.clone(),
            ret: sig.ret.clone(),
        });
        ops.insert(op.clone(), mangled);
    }
    let Some(eff) = eff else {
        return Err(TypeError::Other {
            span,
            msg: format!("handler `{f}` must handle at least one operation"),
        });
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
    env2.insert(f.into(), Binding::Inst(ops.clone()));
    let body2 = rw(body, &env2, cx)?;
    let opset: BTreeSet<String> = ops.into_values().collect();
    if let Some(bad) = escapes(&body2, &opset, &cx.ctors, &mut BTreeSet::new()) {
        return Err(TypeError::Other {
            span: bad,
            msg: format!("handler instance `{f}` escapes its `with` block: the value here is a function that still performs `{f}`'s operations after its handler is gone"),
        });
    }
    let handled = sp(Expr::Handle(Box::new(body2), arms2), span);
    Ok(wrap_vals(vals, handled, span))
}
