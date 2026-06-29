//! Resume- and effect-escape analysis over surface and core expressions.
//!
//! Two read-only tree-walks the effect rewrite relies on: [`free_resume`] finds
//! the first free `resume` in a `final ctl` body (scope-aware), and [`escapes`]
//! flags a handled block whose value would carry a scoped operation (a var's
//! get/put, a named handler's private ops) out of scope.

use std::collections::BTreeSet;

use marginalia::Span;

use super::pat_vars;
use crate::names;
use crate::syntax::ast::{Core, Expr, HandlerArm, Sugar, SugarArm, Surface, S};

const RESUME: &str = "resume";

// First free occurrence of `resume` in a final ctl body. Scope-aware: any
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
        Expr::Bin(_, a, b) | Expr::Pipe(a, b) => fr(a).or_else(|| fr(b)),
        Expr::If(c, t, f) => fr(c).or_else(|| fr(t)).or_else(|| fr(f)),
        Expr::Call(f, args) => fr(f).or_else(|| args.iter().find_map(fr)),
        Expr::List(es) | Expr::Tuple(es) => es.iter().find_map(fr),
        Expr::FieldAccess(b, _) | Expr::Inst(b, _) | Expr::Ann(b, _) | Expr::Mask(_, b) => fr(b),
        Expr::Index(recv, key) => fr(recv).or_else(|| fr(key)),
        Expr::RecordCreate(_, fs) => fs.iter().find_map(|(_, v)| fr(v)),
        Expr::RecordUpdate(b, _, fs) => fr(b).or_else(|| fs.iter().find_map(|(_, v)| fr(v))),
        Expr::RecordUpdatePath(b, ups) => fr(b).or_else(|| {
            ups.iter().find_map(|(steps, op)| {
                steps
                    .iter()
                    .find_map(|s| s.sub_expr().and_then(fr))
                    .or_else(|| fr(op.expr()))
            })
        }),
        Expr::Sugar(s) => free_resume_sugar(s),
        _ => None,
    }
}

fn free_resume_arm(a: &HandlerArm) -> Option<Span> {
    match a {
        HandlerArm::Return(x, body) => free_resume(body, x == RESUME),
        HandlerArm::Op(_, ps, k, body) => {
            free_resume(body, k == RESUME || ps.iter().any(|p| p == RESUME))
        }
        HandlerArm::Sugar(SugarArm::Fun(_, ps, body) | SugarArm::Final(_, ps, body)) => {
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
        Sugar::Assign(_, b) | Sugar::OptChain(b, _) => fr(b),
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
    match &e.node {
        Expr::Bin(_, a, b) | Expr::Pipe(a, b) | Expr::Let(_, a, b) => {
            walk(a, f);
            walk(b, f);
        }
        Expr::If(a, b, c) => {
            walk(a, f);
            walk(b, f);
            walk(c, f);
        }
        Expr::Lam(_, a)
        | Expr::FieldAccess(a, _)
        | Expr::Inst(a, _)
        | Expr::Ann(a, _)
        | Expr::Mask(_, a) => {
            walk(a, f);
        }
        Expr::Index(recv, key) => {
            walk(recv, f);
            walk(key, f);
        }
        Expr::Call(h, args) => {
            walk(h, f);
            for a in args {
                walk(a, f);
            }
        }
        Expr::Match(s, arms) => {
            walk(s, f);
            for a in arms {
                if let Some(g) = &a.guard {
                    walk(g, f);
                }
                walk(&a.body, f);
            }
        }
        Expr::Handle(b, arms) => {
            walk(b, f);
            for a in arms {
                match a {
                    HandlerArm::Return(_, body) | HandlerArm::Op(_, _, _, body) => walk(body, f),
                    #[expect(
                        clippy::uninhabited_references,
                        reason = "Never is uninhabited in Core; arm is unreachable"
                    )]
                    HandlerArm::Sugar(never) => match *never {},
                }
            }
        }
        Expr::List(es) | Expr::Tuple(es) => {
            for a in es {
                walk(a, f);
            }
        }
        Expr::RecordCreate(_, fs) => {
            for (_, a) in fs {
                walk(a, f);
            }
        }
        Expr::RecordUpdate(b, _, fs) => {
            walk(b, f);
            for (_, a) in fs {
                walk(a, f);
            }
        }
        Expr::RecordUpdatePath(b, ups) => {
            walk(b, f);
            for (steps, op) in ups {
                for s in steps {
                    if let Some(e) = s.sub_expr() {
                        walk(e, f);
                    }
                }
                walk(op.expr(), f);
            }
        }
        _ => {}
    }
}

// Walk the statement spine of the handled block and flag a block value that
// would carry the scoped operations out of scope: a closure performing one, a
// name bound to one, or a data value embedding one (tuple, list, ctor call,
// record create/update, projection from a tainted base, Ann/Inst wrappers).
// Runs on the post-rw body, so Assign/VarDecl/NamedHandle never appear; Bin
// yields a scalar and literals carry nothing. Residual hole: a non-ctor Call or
// Pipe result is opaque, since without types we cannot tell a call that consumes
// a tainted closure from one that returns it, and flagging every tainted
// argument would reject valid code.
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
        Expr::Handle(b, _)
        | Expr::FieldAccess(b, _)
        | Expr::Ann(b, _)
        | Expr::Inst(b, _)
        | Expr::Mask(_, b) => escapes(b, ops, ctors, tainted),
        Expr::Index(recv, key) => escapes(recv, ops, ctors, &mut tainted.clone())
            .or_else(|| escapes(key, ops, ctors, &mut tainted.clone())),
        _ => None,
    }
}
