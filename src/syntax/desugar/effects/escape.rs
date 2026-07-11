//! Resume- and effect-escape analysis over surface and core expressions.
//!
//! Two read-only tree-walks the effect rewrite relies on: [`free_resume`] finds
//! the first free `resume` in a `never` body (scope-aware), and [`escapes`]
//! flags a handled block whose value would carry a scoped operation (a var's
//! get/put, a named handler's private ops) out of scope.

use std::collections::BTreeSet;

use marginalia::Span;

use super::pat_vars;
use crate::names;
use crate::syntax::ast::{Core, Expr, HandlerArm, Sugar, SugarArm, Surface, S};

const RESUME: &str = "resume";

// First free occurrence of `resume` in a never body. Scope-aware: any
// binder named resume (let, lambda, match pattern, var, handler arm) shadows
// it, and a shadowed subtree cannot contain a free use, so it prunes early.
pub(super) fn free_resume(e: &S<Expr>, sh: bool) -> Option<Span> {
    if sh {
        return None;
    }
    let fr = |x: &S<Expr>| free_resume(x, false);
    match &e.node {
        Expr::Var(x) if x == RESUME => Some(e.span),
        Expr::Let(x, v, b) => fr(v).or_else(|| free_resume(b, x == RESUME)),
        Expr::Lam(ps, b) => free_resume(b, ps.iter().any(|p| p.name == RESUME)),
        Expr::Match(s, arms) => fr(s).or_else(|| {
            arms.iter().find_map(|a| {
                let mut bound = BTreeSet::new();
                pat_vars(&a.pat, &mut bound);
                let sh2 = bound.contains(RESUME);
                (a.guard.as_ref().and_then(|g| free_resume(g, sh2)))
                    .or_else(|| free_resume(&a.body, sh2))
            })
        }),
        Expr::Handle(b, arms) => fr(b).or_else(|| arms.iter().find_map(free_resume_arm)),
        Expr::Sugar(s) => free_resume_sugar(s),
        _ => {
            let mut found = None;
            e.node.each_child(&mut |child| {
                if found.is_none() {
                    found = fr(child);
                }
            });
            found
        }
    }
}

fn free_resume_arm(a: &HandlerArm) -> Option<Span> {
    match a {
        HandlerArm::Return(x, body) => free_resume(body, x == RESUME),
        HandlerArm::Op(_, ps, k, body) => {
            free_resume(body, k == RESUME || ps.iter().any(|p| p == RESUME))
        }
        HandlerArm::Sugar(SugarArm::Once(_, ps, body) | SugarArm::Never(_, ps, body)) => {
            free_resume(body, ps.iter().any(|p| p == RESUME))
        }
        HandlerArm::Sugar(SugarArm::Val(_, body)) => free_resume(body, false),
    }
}

fn free_resume_sugar(s: &Sugar<Surface>) -> Option<Span> {
    let fr = |x: &S<Expr>| free_resume(x, false);
    match s {
        Sugar::VarDecl(x, v, b) => fr(v).or_else(|| free_resume(b, x == RESUME)),
        Sugar::NamedHandle(_, b, arms) => fr(b).or_else(|| arms.iter().find_map(free_resume_arm)),
        Sugar::Assign(_, b) | Sugar::OptChain(b, _) | Sugar::Probe(_, b) => fr(b),
        Sugar::IndexAssign(recv, key, v) => fr(recv).or_else(|| fr(key)).or_else(|| fr(v)),
        Sugar::Default(a, b) | Sugar::Transact(a, b) | Sugar::Compose(_, a, b) => {
            fr(a).or_else(|| fr(b))
        }
        Sugar::Throw(_, args) => args.iter().find_map(fr),
        Sugar::TryCatch(b, arms) => fr(b).or_else(|| {
            arms.iter()
                .find_map(|a| free_resume(&a.body, a.binders.iter().any(|p| p == RESUME)))
        }),
        Sugar::For(_, s, _, b) => fr(s).or_else(|| fr(b)),
        Sugar::Comp(h, _, s, _) => fr(h).or_else(|| fr(s)),
        Sugar::Range(pre, hi) => pre.iter().find_map(fr).or_else(|| fr(hi)),
        Sugar::While(cond, b) => cond.as_deref().and_then(fr).or_else(|| fr(b)),
        Sugar::Break | Sugar::Continue => None,
        Sugar::Return(e) => fr(e),
        Sugar::ReadPath(b, steps) => {
            fr(b).or_else(|| steps.iter().find_map(|s| s.sub_expr().and_then(fr)))
        }
    }
}

// True if `e` mentions any of the scoped operations (a var's get/put, or a
// named handler instance's private ops) anywhere.
fn mentions(e: &S<Expr<Core>>, ops: &BTreeSet<String>) -> bool {
    let mut found = false;
    walk(e, &mut |x| {
        if let Expr::Var(n) = &x.node {
            if ops.contains(n) {
                found = true;
            }
        }
    });
    found
}

// True if `e` contains a lambda that captures the scoped operations, or
// refers to a name already known to hold such a closure.
fn taints(e: &S<Expr<Core>>, ops: &BTreeSet<String>, tainted: &BTreeSet<String>) -> bool {
    let mut found = false;
    walk(e, &mut |x| match &x.node {
        Expr::Lam(_, b) if mentions(b, ops) => found = true,
        Expr::Var(n) if tainted.contains(n) => found = true,
        _ => {}
    });
    found
}

// Every name referenced anywhere in `e`, for the entry-point world-handler
// call-graph scan in the parent desugar module.
pub(in crate::syntax::desugar) fn referenced_names(
    e: &S<Expr<Core>>,
) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    walk(e, &mut |x| {
        if let Expr::Var(n) = &x.node {
            out.insert(n.clone());
        }
    });
    out
}

fn walk(e: &S<Expr<Core>>, f: &mut impl FnMut(&S<Expr<Core>>)) {
    f(e);
    e.node.each_child(&mut |child| walk(child, f));
}

// Walk the statement spine of the handled block and flag a block value that
// would carry the scoped operations out of scope: a closure performing one, a
// name bound to one, or a data value embedding one (tuple, list, ctor call,
// record create/update, projection from a tainted base, Ann/Inst wrappers).
// Runs on the post-rw body, so Assign/VarDecl/NamedHandle never appear; Bin
// yields a scalar and literals carry nothing. Residual hole: a non-ctor Call or
// Pipe result is opaque, since without types we cannot tell a call that consumes
// a tainted closure from one that returns it, and flagging every tainted
// argument would reject valid code. This check is therefore a friendlier early
// diagnostic, not the soundness boundary: a closure that does slip out this way
// still carries the var's private effect on its arrow row, so principal effect
// inference rejects it as an unhandled effect before the in-place `var` lowering
// runs (see tests/cases/var_escape_through_call.pr).
pub(super) fn escapes(
    e: &S<Expr<Core>>,
    ops: &BTreeSet<String>,
    ctors: &BTreeSet<String>,
    tainted: &mut BTreeSet<String>,
) -> Option<Span> {
    match &e.node {
        Expr::Let(x, v, b) => {
            if let (Expr::Handle(hb, _), Expr::Call(h, _)) = (&v.node, &b.node) {
                if names::is_var_runner(x) && matches!(&h.node, Expr::Var(n) if n == x) {
                    return escapes(hb, ops, ctors, tainted);
                }
            }
            if taints(v, ops, tainted) {
                tainted.insert(x.clone());
            } else {
                tainted.remove(x);
            }
            escapes(b, ops, ctors, tainted)
        }
        Expr::Lam(_, b) if mentions(b, ops) => Some(e.span),
        Expr::Var(n) if tainted.contains(n) => Some(e.span),
        Expr::If(_, t, f) => {
            escapes(t, ops, ctors, tainted).or_else(|| escapes(f, ops, ctors, &mut tainted.clone()))
        }
        Expr::Match(_, arms) => arms.iter().find_map(|a| {
            let mut t2 = tainted.clone();
            let mut bound = BTreeSet::new();
            pat_vars(&a.pat, &mut bound);
            for n in &bound {
                t2.remove(n);
            }
            escapes(&a.body, ops, ctors, &mut t2)
        }),
        Expr::Tuple(es) | Expr::List(es) => es
            .iter()
            .find_map(|v| escapes(v, ops, ctors, &mut tainted.clone())),
        Expr::Call(h, args) => match &h.node {
            Expr::Var(n) if ctors.contains(n) => args
                .iter()
                .find_map(|v| escapes(v, ops, ctors, &mut tainted.clone())),
            _ => None,
        },
        Expr::Pipe(v, h) => match &h.node {
            Expr::Var(n) if ctors.contains(n) => escapes(v, ops, ctors, tainted),
            _ => None,
        },
        Expr::RecordCreate(_, fs) => fs
            .iter()
            .find_map(|(_, v)| escapes(v, ops, ctors, &mut tainted.clone())),
        Expr::RecordUpdate(b, _, fs) => {
            escapes(b, ops, ctors, &mut tainted.clone()).or_else(|| {
                fs.iter()
                    .find_map(|(_, v)| escapes(v, ops, ctors, &mut tainted.clone()))
            })
        }
        Expr::RecordUpdatePath(b, ups) => {
            escapes(b, ops, ctors, &mut tainted.clone()).or_else(|| {
                ups.iter().find_map(|(steps, op)| {
                    steps
                        .iter()
                        .find_map(|s| {
                            s.sub_expr()
                                .and_then(|e| escapes(e, ops, ctors, &mut tainted.clone()))
                        })
                        .or_else(|| escapes(op.expr(), ops, ctors, &mut tainted.clone()))
                })
            })
        }
        Expr::IndexSet(recv, key, val) => escapes(recv, ops, ctors, &mut tainted.clone())
            .or_else(|| escapes(key, ops, ctors, &mut tainted.clone()))
            .or_else(|| escapes(val, ops, ctors, &mut tainted.clone())),
        Expr::Handle(b, _)
        | Expr::FieldAccess(b, _)
        | Expr::Ann(b, _)
        | Expr::Inst(b, _)
        | Expr::Mask(_, b)
        | Expr::Neg(b) => escapes(b, ops, ctors, tainted),
        Expr::Index(recv, key) => escapes(recv, ops, ctors, &mut tainted.clone())
            .or_else(|| escapes(key, ops, ctors, &mut tainted.clone())),
        _ => None,
    }
}

// Whether `token` occurs free in `e`: a bare occurrence not bound by an
// enclosing lambda parameter, `let`, or match-arm pattern. The shadow tracking
// is what `mentions` (hygienic op names, unshadowable) does not need.
fn token_free_in(e: &S<Expr<Core>>, token: &str) -> bool {
    match &e.node {
        Expr::Var(n) => n == token,
        Expr::Lam(ps, b) => !ps.iter().any(|p| p.name == token) && token_free_in(b, token),
        Expr::Let(x, v, b) => token_free_in(v, token) || (x != token && token_free_in(b, token)),
        Expr::Match(s, arms) => {
            token_free_in(s, token)
                || arms.iter().any(|a| {
                    let mut bound = BTreeSet::new();
                    pat_vars(&a.pat, &mut bound);
                    !bound.contains(token)
                        && (a.guard.as_ref().is_some_and(|g| token_free_in(g, token))
                            || token_free_in(&a.body, token))
                })
        }
        _ => {
            let mut found = false;
            e.node
                .each_child(&mut |c| found = found || token_free_in(c, token));
            found
        }
    }
}

// The `@ noescape` scoped-token analysis: does the VALUE of `e` carry `token`
// out? The structure mirrors `escapes` above; the difference is what carries.
// There the scoped things are effect-op names, escaping through closures that
// perform them; here the token is a first-class value, so a bare `Var(token)` in
// value position is itself the escape, and a lambda whose body uses the token
// free is a carrier (the closure could outlive the call). Shares `escapes`'s
// documented hole: a non-constructor call result is opaque, so a callee that
// smuggles its argument back out is not caught; this is a focused early
// diagnostic for the directly expressible escapes (returned, embedded in data,
// aliased, captured), not a full soundness boundary.
pub(in crate::syntax::desugar) fn token_escapes(
    e: &S<Expr<Core>>,
    token: &str,
    ctors: &BTreeSet<String>,
    tainted: &mut BTreeSet<String>,
) -> Option<Span> {
    let carries_here =
        |x: &S<Expr<Core>>| matches!(&x.node, Expr::Var(n) if n == token || tainted.contains(n));
    match &e.node {
        Expr::Var(n) if n == token || tainted.contains(n) => Some(e.span),
        Expr::Lam(ps, b) => {
            (!ps.iter().any(|p| p.name == token) && token_free_in(b, token)).then_some(e.span)
        }
        Expr::Let(x, v, b) => {
            if token_escapes(v, token, ctors, &mut tainted.clone()).is_some() || carries_here(v) {
                // The bound name now holds (something containing) the token.
                // Distinguishing "carries" from "is the final escape" is the
                // value-position question the recursion into `b` answers.
                tainted.insert(x.clone());
            } else {
                tainted.remove(x);
            }
            token_escapes(b, token, ctors, tainted)
        }
        Expr::If(_, t, f) => token_escapes(t, token, ctors, tainted)
            .or_else(|| token_escapes(f, token, ctors, &mut tainted.clone())),
        Expr::Match(_, arms) => arms.iter().find_map(|a| {
            let mut t2 = tainted.clone();
            let mut bound = BTreeSet::new();
            pat_vars(&a.pat, &mut bound);
            for n in &bound {
                t2.remove(n);
            }
            if bound.contains(token) {
                return None;
            }
            token_escapes(&a.body, token, ctors, &mut t2)
        }),
        Expr::Tuple(es) | Expr::List(es) => es
            .iter()
            .find_map(|v| token_escapes(v, token, ctors, &mut tainted.clone())),
        Expr::Call(h, args) => match &h.node {
            Expr::Var(n) if ctors.contains(n) => args
                .iter()
                .find_map(|v| token_escapes(v, token, ctors, &mut tainted.clone())),
            // A non-constructor call consumes its arguments; its result is
            // opaque (the shared documented hole).
            _ => None,
        },
        Expr::Pipe(v, h) => match &h.node {
            Expr::Var(n) if ctors.contains(n) => token_escapes(v, token, ctors, tainted),
            _ => None,
        },
        Expr::RecordCreate(_, fs) => fs
            .iter()
            .find_map(|(_, v)| token_escapes(v, token, ctors, &mut tainted.clone())),
        Expr::RecordUpdate(b, _, fs) => token_escapes(b, token, ctors, &mut tainted.clone())
            .or_else(|| {
                fs.iter()
                    .find_map(|(_, v)| token_escapes(v, token, ctors, &mut tainted.clone()))
            }),
        Expr::Handle(b, _)
        | Expr::FieldAccess(b, _)
        | Expr::Ann(b, _)
        | Expr::Inst(b, _)
        | Expr::Mask(_, b)
        | Expr::Neg(b) => token_escapes(b, token, ctors, tainted),
        _ => None,
    }
}
