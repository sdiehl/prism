//! Parse-time grammar helpers and statement-level surface sugar.

use marginalia::Span;

use super::effects::{rw, Vars};
use super::{call, evar, sp, sp_sugar, Cx};
use crate::error::TypeError;
use crate::names;
use crate::syntax::ast::{Arm, Core, Expr, Marker, Param, Pattern, PatternDecl, Spanned, S};

#[must_use]
const fn with_sentinel(l: usize, r: usize) -> S<Expr> {
    Spanned {
        synth: false,
        node: Expr::Marker(Marker::With),
        span: Span::new(l, r),
    }
}

// The block a `with` wraps: the statements following its `;`, or, for a trailing
// `with` with nothing after it, the rejection sentinel spanning the statement so
// desugar reports one clear "nothing to wrap" error.
#[must_use]
pub fn with_rest(rest: Option<S<Expr>>, l: usize, r: usize) -> S<Expr> {
    rest.unwrap_or_else(|| with_sentinel(l, r))
}

// UFCS dot call: `recv.f(args)` becomes `f(recv, args)`. The callee's `synth`
// flag is the marker the formatter keys on to restore the dot surface; its span
// is a zero-width placeholder, distinct from the enclosing call's (spans key the
// type side-tables, so a shared span would collide).
#[must_use]
pub fn dot_call(recv: S<Expr>, name: String, args: Vec<S<Expr>>, l: usize, r: usize) -> S<Expr> {
    let callee = Spanned {
        synth: true,
        node: Expr::Var(name),
        span: Span::empty(l),
    };
    let mut all = vec![recv];
    all.extend(args);
    Spanned {
        synth: false,
        node: Expr::Call(Box::new(callee), all),
        span: Span::new(l, r),
    }
}

// `with` flattening sugar: the rest of the block becomes a lambda passed as the
// call's final argument. The lambda's `synth` flag is the marker the formatter
// keys on to restore the `with` surface; its zero-width span is a distinctness
// placeholder (spans key the type side-tables).
#[must_use]
pub fn with_stmt(
    binder: Option<String>,
    call: S<Expr>,
    rest: S<Expr>,
    l: usize,
    r: usize,
) -> S<Expr> {
    let params = binder
        .map(|x| {
            vec![Param {
                name: x,
                ty: None,
                borrow: false,
                default: None,
            }]
        })
        .unwrap_or_default();
    let lam = Spanned {
        synth: true,
        node: Expr::Lam(params, Box::new(rest)),
        span: Span::empty(l),
    };
    let node = match call.node {
        Expr::Call(f, mut args) => {
            args.push(lam);
            Expr::Call(f, args)
        }
        other => Expr::Call(
            Box::new(Spanned {
                synth: false,
                node: other,
                span: call.span,
            }),
            vec![lam],
        ),
    };
    Spanned {
        synth: false,
        node,
        span: Span::new(l, r),
    }
}

#[derive(Debug)]
pub enum IfTail {
    End,
    Rest(S<Expr>),
    Elif(S<Expr>, S<Expr>, Box<Self>),
}

// `if`/`elif` without a final `else` is a statement: the missing branch is
// `()` and any following statements run after the whole chain.
#[must_use]
pub fn open_if(c: S<Expr>, t: S<Expr>, tail: IfTail, l: usize, r: usize) -> S<Expr> {
    let mut arms = vec![(c, t)];
    let mut cur = tail;
    let rest = loop {
        match cur {
            IfTail::Elif(c2, t2, next) => {
                arms.push((c2, t2));
                cur = *next;
            }
            IfTail::End => break None,
            IfTail::Rest(e) => break Some(e),
        }
    };
    let end = arms.last().map_or(r, |(_, t)| t.span.end);
    let unit = sp(Expr::Unit, Span::new(end, end));
    let chain = arms.into_iter().rev().fold(unit, |els, (c2, t2)| {
        sp(
            Expr::If(Box::new(c2), Box::new(t2), Box::new(els)),
            Span::new(l, end),
        )
    });
    match rest {
        None => chain,
        Some(rest) => sp(
            Expr::Let("_".into(), Box::new(chain), Box::new(rest)),
            Span::new(l, r),
        ),
    }
}

// A pattern `let` is a one-arm match; the `synth` flag (set by `sp_sugar`) is
// the marker the formatter keys on to restore the `let` surface. Exhaustiveness
// checking then rejects refutable patterns with its normal error.
#[must_use]
pub fn let_pat(pat: S<Pattern>, v: S<Expr>, rest: S<Expr>, l: usize) -> S<Expr> {
    sp_sugar(
        Expr::Match(
            Box::new(v),
            vec![Arm {
                pat,
                guard: None,
                body: rest,
            }],
        ),
        Span::empty(l),
    )
}

// An interpolated literal parses to an `Interp`-marker call alternating literal
// segments and hole expressions; the `Interp` callee is the marker the formatter
// keys on to restore the string surface, and segment spans are zero-width
// placeholders. `desugar` expands the call to concat/show below.
#[must_use]
pub fn interp_lit(
    first: String,
    hole: S<Expr>,
    parts: Vec<(String, S<Expr>)>,
    last: String,
    l: usize,
    r: usize,
) -> S<Expr> {
    let z = Span::empty(l);
    let mut args = vec![sp(Expr::Str(first), z), hole];
    for (seg, h) in parts {
        args.push(sp(Expr::Str(seg), z));
        args.push(h);
    }
    args.push(sp(Expr::Str(last), z));
    sp(
        Expr::Call(Box::new(sp(Expr::Marker(Marker::Interp), z)), args),
        Span::new(l, r),
    )
}

// Even args are segments, odd args are holes: each hole renders through the
// type-directed `show` (identity on String) and the pieces fold into
// right-nested concat, so holes evaluate left to right.
pub(super) fn expand_interp(
    args: &[S<Expr>],
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    let mut pieces = Vec::new();
    for (i, a) in args.iter().enumerate() {
        if i % 2 == 0 {
            if !matches!(&a.node, Expr::Str(s) if s.is_empty()) {
                pieces.push(rw(a, env, cx)?);
            }
        } else {
            let h = rw(a, env, cx)?;
            let z = Span::new(h.span.end, h.span.end);
            let show = evar("show", z);
            pieces.push(call(show, vec![h], z));
        }
    }
    // `interp_lit` always emits at least one hole, so `pieces` is non-empty by
    // construction; surface a structured error rather than panic if a malformed
    // `Interp` slice ever reaches here.
    let Some(last) = pieces.pop() else {
        return Err(TypeError::Other {
            span,
            msg: "empty string interpolation".into(),
        });
    };
    Ok(pieces.into_iter().rev().fold(last, |acc, p| {
        call(evar("concat", span), vec![p, acc], span)
    }))
}

#[must_use]
pub fn try_mark(e: S<Expr>, l: usize, r: usize) -> S<Expr> {
    // The marker on the callee is what the formatter keys on to restore `e?`.
    let f = sp(Expr::Marker(Marker::Try), Span::empty(l));
    sp(Expr::Call(Box::new(f), vec![e]), Span::new(l, r))
}

pub(super) fn unwrap_try(e: S<Expr>) -> Result<S<Expr>, S<Expr>> {
    match e.node {
        // Move the single argument out by value via the slice pattern, so the
        // marker's one argument is bound directly with no fallible `pop`.
        Expr::Call(f, args) if matches!(&f.node, Expr::Marker(Marker::Try)) => {
            match <[S<Expr>; 1]>::try_from(args) {
                Ok([arg]) => Ok(arg),
                Err(args) => Err(Spanned {
                    synth: e.synth,
                    node: Expr::Call(f, args),
                    span: e.span,
                }),
            }
        }
        node => Err(Spanned {
            synth: e.synth,
            node,
            span: e.span,
        }),
    }
}

// `let x = e?` and bare `e?` statements: the rest of the block becomes the Ok
// arm and an Err rethrows, a two-arm match whose `synth` flag (set by
// `sp_sugar`) marks it for the formatter.
fn try_stmt(binder: Option<String>, scrut: S<Expr>, rest: S<Expr>, l: usize) -> S<Expr> {
    let s = scrut.span;
    let pat = |node| Spanned {
        synth: false,
        node,
        span: s,
    };
    let ok = pat(Pattern::Ctor(
        "Ok".into(),
        vec![pat(binder.map_or(Pattern::Wild, Pattern::Var))],
    ));
    let err = pat(Pattern::Ctor(
        "Err".into(),
        vec![pat(Pattern::Var(names::ERR.into()))],
    ));
    let rethrow = call(evar("Err", s), vec![evar(names::ERR, s)], s);
    let arms = vec![
        Arm {
            pat: ok,
            guard: None,
            body: rest,
        },
        Arm {
            pat: err,
            guard: None,
            body: rethrow,
        },
    ];
    sp_sugar(Expr::Match(Box::new(scrut), arms), Span::empty(l))
}

#[must_use]
pub fn seq_stmt(e: S<Expr>, rest: S<Expr>, l: usize, r: usize) -> S<Expr> {
    match unwrap_try(e) {
        Ok(scrut) => try_stmt(None, scrut, rest, l),
        Err(e) => sp(
            Expr::Let("_".into(), Box::new(e), Box::new(rest)),
            Span::new(l, r),
        ),
    }
}

#[must_use]
pub fn let_stmt(x: String, v: S<Expr>, rest: S<Expr>, l: usize, r: usize) -> S<Expr> {
    match unwrap_try(v) {
        Ok(scrut) => try_stmt(Some(x), scrut, rest, l),
        Err(v) => sp(Expr::Let(x, Box::new(v), Box::new(rest)), Span::new(l, r)),
    }
}

// Assemble a `pattern` declaration from its parsed clauses: exactly one
// `view` (a 1-parameter lambda), optionally one `make` (a lambda of the
// pattern's arity).
/// # Errors
/// Fails on duplicate, missing, or malformed clauses.
pub fn pattern_decl(
    name: String,
    params: Vec<String>,
    for_ty: String,
    clauses: Vec<(String, S<Expr>, Span)>,
    span: Span,
) -> Result<PatternDecl, (Span, String)> {
    let mut view = None;
    let mut make = None;
    for (kw, e, cspan) in clauses {
        let arity = match &e.node {
            Expr::Lam(ps, _) => ps.len(),
            // A bare identifier in a `view` clause names a class method, resolved
            // against the `for` class in lower_patterns (class-dispatched view).
            Expr::Var(_) if kw == "view" => 1,
            _ => return Err((cspan, format!("`{kw}` clause must be a lambda"))),
        };
        let want = if kw == "view" { 1 } else { params.len() };
        if arity != want {
            return Err((
                cspan,
                format!("`{kw}` for pattern `{name}` must take {want} argument(s), this lambda takes {arity}"),
            ));
        }
        let slot = if kw == "view" { &mut view } else { &mut make };
        if slot.replace(e).is_some() {
            return Err((
                cspan,
                format!("duplicate `{kw}` clause in pattern `{name}`"),
            ));
        }
    }
    let Some(view) = view else {
        return Err((span, format!("pattern `{name}` needs a `view` clause")));
    };
    Ok(PatternDecl {
        name,
        params,
        for_ty,
        view,
        make,
        span,
    })
}
