//! View patterns: top-of-arm validation and the rewrite of a view arm into a
//! catchall that matches the view's result, plus the shared pattern-var walk.

use std::collections::BTreeSet;

use marginalia::Span;

use super::{rw, Vars};
use crate::error::TypeError;
use crate::names;
use crate::syntax::ast::{Arm, Core, Expr, Pattern, S};
use crate::syntax::desugar::{call, evar, sp, spat, Cx};

// View patterns are legal only at the top of a match arm: nested they would
// need backtracking through arbitrary user code mid-pattern.
pub(super) fn check_views(p: &S<Pattern>, top: bool, cx: &Cx) -> Result<(), TypeError> {
    match &p.node {
        Pattern::Ctor(n, ps) => {
            if let Some(&(arity, _)) = cx.patterns.get(n) {
                if !top {
                    return Err(TypeError::Other {
                        span: p.span,
                        msg: format!("view pattern `{n}` cannot be nested inside another pattern"),
                    });
                }
                if ps.len() != arity {
                    return Err(TypeError::Other {
                        span: p.span,
                        msg: format!(
                            "pattern `{n}` takes {arity} argument(s), {} given",
                            ps.len()
                        ),
                    });
                }
            }
            ps.iter().try_for_each(|q| check_views(q, false, cx))
        }
        Pattern::Tuple(ps) => ps.iter().try_for_each(|q| check_views(q, false, cx)),
        Pattern::Record(_, fs, _) => fs.iter().try_for_each(|(_, q)| check_views(q, false, cx)),
        _ => Ok(()),
    }
}

// A view arm `P(ps) [if g] => body` becomes a catchall arm that matches the
// view's result: `tmp => match view@P(tmp) of Some(ps') [if g] => body,
// _ => match tmp of <later arms>`. The view row drops out of the usefulness
// matrix like a guarded row, so a catchall arm is required; rw on the rebuilt
// tree handles any remaining view arms.
pub(super) fn rw_view_match(
    s: &S<Expr>,
    arms: &[Arm],
    idx: usize,
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    let a = &arms[idx];
    let Pattern::Ctor(pname, ps) = &a.pat.node else {
        unreachable!("ICE: rw_view_match on non-view arm")
    };
    let irrefutable =
        |a: &Arm| a.guard.is_none() && matches!(a.pat.node, Pattern::Var(_) | Pattern::Wild);
    let Some(catchall) = arms.iter().position(irrefutable) else {
        return Err(TypeError::Other {
            span: a.pat.span,
            msg: format!(
                "match through view pattern `{pname}` is never exhaustive: add a catchall arm"
            ),
        });
    };
    let vspan = a.pat.span;
    let tmp = names::pat_tmp(cx.next.bump());
    let sub = match ps.len() {
        0 => spat(Pattern::Wild, vspan),
        1 => ps[0].clone(),
        _ => spat(Pattern::Tuple(ps.clone()), vspan),
    };
    let mut post: Vec<Arm> = arms[idx + 1..].to_vec();
    if !post.iter().any(irrefutable) {
        post.push(arms[catchall].clone());
    }
    let fallback = sp(
        Expr::Match(Box::new(evar(&tmp, vspan)), post),
        Span::empty(vspan.start),
    );
    let view = call(
        evar(&names::pat_view(pname), Span::empty(vspan.start)),
        vec![evar(&tmp, vspan)],
        vspan,
    );
    let inner = sp(
        Expr::Match(
            Box::new(view),
            vec![
                Arm {
                    pat: spat(Pattern::Ctor("Some".into(), vec![sub]), vspan),
                    guard: a.guard.clone(),
                    body: a.body.clone(),
                },
                Arm {
                    pat: spat(Pattern::Wild, Span::empty(vspan.end)),
                    guard: None,
                    body: fallback,
                },
            ],
        ),
        Span::empty(vspan.start),
    );
    let mut outer: Vec<Arm> = arms[..idx].to_vec();
    outer.push(Arm {
        pat: spat(Pattern::Var(tmp), vspan),
        guard: None,
        body: inner,
    });
    rw(&sp(Expr::Match(Box::new(s.clone()), outer), span), env, cx)
}

pub(super) fn pat_vars(p: &S<Pattern>, out: &mut BTreeSet<String>) {
    match &p.node {
        Pattern::Var(x) => {
            out.insert(x.clone());
        }
        Pattern::Ctor(_, ps) | Pattern::Tuple(ps) => {
            for q in ps {
                pat_vars(q, out);
            }
        }
        Pattern::Record(_, fs, _) => {
            for (_, q) in fs {
                pat_vars(q, out);
            }
        }
        _ => {}
    }
}
