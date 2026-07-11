//! Named-argument resolution and default filling for calls of top-level fns.

use marginalia::Span;

use super::{rw, Vars};
use crate::error::{ErrKind, TypeError};
use crate::syntax::ast::{Core, Expr, Sugar, S};
use crate::syntax::desugar::{call, evar, Cx};

// Rewrite a call to a top-level fn, resolving named arguments and filling in
// defaults. All-positional under-application is a complete call only when every
// missing parameter is defaulted; otherwise it stays a partial application
// (currying). A named argument anywhere signals complete-call intent, so a
// still-missing non-defaulted parameter is an error. Defaults are capture-free,
// rewritten in an empty scope.
pub(super) fn fill_call(
    name: &str,
    sig: &[(String, Option<S<Expr>>)],
    args: &[S<Expr>],
    fspan: Span,
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    let n = sig.len();
    let named = args
        .iter()
        .any(|a| matches!(&a.node, Expr::Sugar(Sugar::Assign(..))));
    if !named {
        let k = args.len();
        if !sig[k..].iter().all(|(_, d)| d.is_some()) {
            let args2: Result<Vec<_>, _> = args.iter().map(|a| rw(a, env, cx)).collect();
            return Ok(call(evar(name, fspan), args2?, span));
        }
        let mut filled = Vec::with_capacity(n);
        for a in args {
            filled.push(rw(a, env, cx)?);
        }
        for (_, d) in &sig[k..] {
            filled.push(rw(d.as_ref().unwrap(), &Vars::new(), cx)?);
        }
        return Ok(call(evar(name, fspan), filled, span));
    }
    let mut slots: Vec<Option<S<Expr<Core>>>> = (0..n).map(|_| None).collect();
    let mut seen_named = false;
    let mut pos = 0usize;
    for a in args {
        if let Expr::Sugar(Sugar::Assign(k, v)) = &a.node {
            seen_named = true;
            let Some(j) = sig.iter().position(|(pn, _)| pn == k) else {
                return Err(ErrKind::NoParameter {
                    fn_name: name.to_string(),
                    param: k.clone(),
                }
                .at(a.span));
            };
            if slots[j].is_some() {
                return Err(ErrKind::ArgGivenTwice {
                    param: k.clone(),
                    fn_name: name.to_string(),
                }
                .at(a.span));
            }
            slots[j] = Some(rw(v, env, cx)?);
        } else {
            if seen_named {
                return Err(ErrKind::PositionalAfterNamed {
                    fn_name: name.to_string(),
                }
                .at(a.span));
            }
            if pos >= n {
                return Err(ErrKind::TooManyArgs {
                    fn_name: name.to_string(),
                    takes: n,
                }
                .at(a.span));
            }
            slots[pos] = Some(rw(a, env, cx)?);
            pos += 1;
        }
    }
    let mut filled = Vec::with_capacity(n);
    for (j, slot) in slots.into_iter().enumerate() {
        match slot {
            Some(e) => filled.push(e),
            None => match &sig[j].1 {
                Some(d) => filled.push(rw(d, &Vars::new(), cx)?),
                None => {
                    return Err(ErrKind::MissingArgument {
                        fn_name: name.to_string(),
                        param: sig[j].0.clone(),
                    }
                    .at(span));
                }
            },
        }
    }
    Ok(call(evar(name, fspan), filled, span))
}
