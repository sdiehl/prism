//! Stamp every expression node with a unique `NodeId`, the identity under which
//! the typechecker records a node's resolution for the elaborator to read back.
//!
//! Run as the last step of desugar, so identity is fixed on the exact tree both
//! the typechecker and the elaborator traverse. Decoupling identity from `Span`
//! is what lets desugar mint synthesized nodes at any source span (even a
//! duplicated one) and lets resolve leave per-module spans unshifted: a node's
//! resolution is keyed by its id, never its location.

use crate::syntax::ast::{Core, Decl, Expr, HandlerArm, NodeId, Program, S};

/// Assign every expression node in `prog` a fresh id, in a deterministic
/// pre-order walk. Only function and instance-method bodies carry Core exprs;
/// pattern synonyms are expanded away by this point.
pub(super) fn assign_ids(prog: &mut Program<Core>) {
    let mut next: u32 = 1;
    for f in &mut prog.fns {
        decl(f, &mut next);
    }
    for i in &mut prog.instances {
        for m in &mut i.methods {
            decl(m, &mut next);
        }
    }
}

/// Stamp a standalone expression (the REPL's interactively typed term, which
/// bypasses the program-level pipeline) so its dispatch sites resolve.
pub(super) fn assign_expr_ids(e: &mut S<Expr<Core>>) {
    let mut next: u32 = 1;
    expr(e, &mut next);
}

fn decl(d: &mut Decl<Core>, next: &mut u32) {
    // Core params drop their defaults, but stay total in case one survives.
    for p in &mut d.params {
        if let Some(e) = &mut p.default {
            expr(e, next);
        }
    }
    expr(&mut d.body, next);
}

fn expr(e: &mut S<Expr<Core>>, next: &mut u32) {
    e.id = NodeId(*next);
    *next += 1;
    match &mut e.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::Hole(_) => {}
        Expr::Bin(_, a, b) | Expr::Pipe(a, b) | Expr::Index(a, b) => {
            expr(a, next);
            expr(b, next);
        }
        Expr::If(a, b, c) | Expr::IndexSet(a, b, c) => {
            expr(a, next);
            expr(b, next);
            expr(c, next);
        }
        Expr::Let(_, v, b) => {
            expr(v, next);
            expr(b, next);
        }
        Expr::Lam(ps, b) => {
            for p in ps {
                if let Some(d) = &mut p.default {
                    expr(d, next);
                }
            }
            expr(b, next);
        }
        Expr::Call(f, args) => {
            expr(f, next);
            for a in args {
                expr(a, next);
            }
        }
        Expr::Match(s, arms) => {
            expr(s, next);
            for a in arms {
                if let Some(g) = &mut a.guard {
                    expr(g, next);
                }
                expr(&mut a.body, next);
            }
        }
        Expr::List(xs) | Expr::Tuple(xs) | Expr::UnboxedTuple(xs) => {
            for x in xs {
                expr(x, next);
            }
        }
        Expr::FieldAccess(a, _)
        | Expr::UnboxedField(a, _)
        | Expr::Mask(_, a)
        | Expr::Inst(a, _)
        | Expr::Ann(a, _)
        | Expr::Neg(a) => {
            expr(a, next);
        }
        Expr::RecordCreate(_, fs) | Expr::UnboxedRecord(fs) => {
            for (_, v) in fs {
                expr(v, next);
            }
        }
        Expr::RecordUpdate(b, _, fs) => {
            expr(b, next);
            for (_, v) in fs {
                expr(v, next);
            }
        }
        Expr::RecordUpdatePath(b, paths) => {
            expr(b, next);
            for (steps, op) in paths {
                for s in steps {
                    if let Some(se) = s.sub_expr_mut() {
                        expr(se, next);
                    }
                }
                expr(op.expr_mut(), next);
            }
        }
        Expr::Handle(b, arms, _) => {
            expr(b, next);
            for a in arms {
                match a {
                    HandlerArm::Return(_, body) | HandlerArm::Op(_, _, _, body) => expr(body, next),
                    #[expect(
                        clippy::uninhabited_references,
                        reason = "Never is uninhabited in Core; arm is unreachable"
                    )]
                    HandlerArm::Sugar(never) => match *never {},
                }
            }
        }
        #[expect(
            clippy::uninhabited_references,
            reason = "Never is uninhabited in Core; arm is unreachable"
        )]
        Expr::Marker(never) | Expr::Sugar(never) => match *never {},
    }
}
