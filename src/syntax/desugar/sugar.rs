//! Parse-time grammar helpers and statement-level surface sugar.

use marginalia::Span;

use super::effects::{rw, Vars};
use super::{call, evar, sp, sp_sugar, Cx};
use crate::error::{ErrKind, TypeError};
use crate::kw;
use crate::names;
use crate::syntax::ast::{
    Arm, BinOp, Converter, Core, Expr, Marker, NodeId, Param, Pattern, PatternDecl, Rung, Spanned,
    StableDecl, Sugar, Ty, S,
};

// The `view` clause keyword of a `pattern` decl (the only single-parameter
// clause); any other keyword is the optional `make` clause. `kw::VIEW`/`kw::MAKE`
// are the canonical spellings.

// The flip messages shown when a `class`/`instance`/`effect` body is opened with
// a brace instead of layout. Each names the construct and the member it holds so
// the fix reads off the message.
pub const FLIP_CLASS: &str =
    "class bodies use layout: remove the braces and put each method on its own indented line";
pub const FLIP_INSTANCE: &str =
    "instance bodies use layout: remove the braces and put each member on its own indented line";
pub const FLIP_EFFECT: &str =
    "effect bodies use layout: remove the braces and put each operation on its own indented line";

// A leading op/clause word that names no grade. The grades are `never`, `once`,
// and `many`; `many` is the unmarked default, so it is also the message for a
// stray `ctl`/`fun`/`final`, which are no longer grade spellings.
#[must_use]
pub fn grade_word_msg(word: &str) -> String {
    format!(
        "`{word}` is not a grade: an operation grade is `never`, `once`, or `many`, \
         or omit it for `many`"
    )
}

// A handler clause written `many op(...)`: the multishot clause binds the
// continuation explicitly instead of taking a grade keyword.
pub const GRADE_MANY_CLAUSE: &str =
    "a `many` clause resumes explicitly: bind the continuation as the last parameter and call it, \
     `op(params, k) => ...`, with no leading grade";

// Shown when a type-argument position holds dimension arithmetic (`Vec(a, n + 1)`).
// The `Nat` kind unifies dimensions by equality of literals and variables only, so
// there is no `+` on a dimension; the message states what a dimension may be.
pub const DECLINE_DIM_ARITH: &str =
    "arithmetic on dimensions is not supported: a dimension is a plain natural literal \
     (`0`, `1`, `2`, ...) or a type variable, and dimensions unify by equality only";

// Shown when a multishot handler clause writes the retired trailing-continuation
// form (`op(params, k) => ...`). The continuation now follows `resume`, giving it a
// visibly special clause position instead of masquerading as a final parameter.
pub const MIGRATE_RESUME: &str =
    "a multishot handler clause names its continuation after `resume`: write \
     `op(params) resume k => ...` instead of trailing the continuation as a parameter";

// Shown when a float dot-operator (`+.` `*.` `<.` ...) appears. The plain
// operators became lane-polymorphic over Float, so the Float-only dotted spellings
// were removed; the parser still recognizes them structurally to point at the plain
// operator that now covers Float rather than failing as a bare parse error.
#[must_use]
pub fn dot_op_removed(dot: &str, plain: &str) -> String {
    format!(
        "the float dot-operator `{dot}` was removed: the plain operator `{plain}` is \
         lane-polymorphic over Float, so write `{plain}`"
    )
}

// Shown when a declaration writes the retired effect-before-result order
// (`: !{E} T`). The effect row now follows the result type, matching a function
// type's own `-> cod ! {row}`, so a signature reads left to right.
pub const MIGRATE_RET_ORDER: &str =
    "the effect row now follows the result type: write `: Result ! {Effects}` \
     instead of `: !{Effects} Result`";

// One entry of a `stable` block body: a version rung or a hand-written converter.
// The parser collects them interleaved (they share the comma-separated body);
// `build_stable` partitions them and enforces the ordering invariant.
#[derive(Debug)]
pub enum StableItem {
    Rung(Rung),
    Conv(Converter),
}

/// Assemble a `stable` block from its parsed entries.
///
/// The rungs (in declaration order, which is version order) come first and the
/// hand-written converters after; a rung following a converter is rejected so the
/// version history reads top to bottom.
///
/// # Errors
/// Fails on an empty block or a rung following a converter.
pub fn build_stable(
    name: String,
    items: Vec<StableItem>,
    span: Span,
) -> Result<StableDecl, (Span, String)> {
    let mut rungs = Vec::new();
    let mut converters = Vec::new();
    for item in items {
        match item {
            StableItem::Rung(r) => {
                if !converters.is_empty() {
                    return Err((
                        r.span,
                        format!(
                            "rung `{}` must come before the converters in `stable {name}`",
                            r.name
                        ),
                    ));
                }
                rungs.push(r);
            }
            StableItem::Conv(c) => converters.push(c),
        }
    }
    if rungs.is_empty() {
        return Err((span, format!("`stable {name}` declares no version rungs")));
    }
    Ok(StableDecl {
        name,
        rungs,
        converters,
        span,
    })
}

#[must_use]
const fn with_sentinel(l: usize, r: usize) -> S<Expr> {
    Spanned {
        id: NodeId::DUMMY,
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

// A usage row spelling exactly `@ noalloc` at the root of a `fn` return
// annotation is the declaration's allocation certificate, not part of the
// type: strip it onto the flag at parse. Any other row (reserved facts, or
// `noalloc` mixed with them) stays in the `Ty` so the checker rejects it with
// the reserved-fact diagnostic at its own span.
#[must_use]
pub fn lift_noalloc(ret: Option<Ty>) -> (Option<Ty>, bool) {
    match ret {
        Some(Ty::Coeffect(inner, row)) if row.is_noalloc_only() => (Some(*inner), true),
        other => (other, false),
    }
}

// UFCS dot call: `recv.f(args)` becomes `f(recv, args)`. The callee's `synth`
// flag is the marker the formatter keys on to restore the dot surface; its span
// is a zero-width placeholder, distinct from the enclosing call's (spans key the
// type side-tables, so a shared span would collide).
#[must_use]
pub fn dot_call(recv: S<Expr>, name: String, args: Vec<S<Expr>>, l: usize, r: usize) -> S<Expr> {
    let callee = Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::Var(name),
        span: Span::empty(l),
    };
    let mut all = vec![recv];
    all.extend(args);
    Spanned {
        id: NodeId::DUMMY,
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
        id: NodeId::DUMMY,
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
                id: NodeId::DUMMY,
                synth: false,
                node: other,
                span: call.span,
            }),
            vec![lam],
        ),
    };
    Spanned {
        id: NodeId::DUMMY,
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
            // An interpolated hole displays its value (raw for a string), so it
            // lowers to the internal display printer, not the quoting `show`.
            let display = evar(names::DISPLAY_FN, z);
            pieces.push(call(display, vec![h], z));
        }
    }
    // `interp_lit` always emits at least one hole, so `pieces` is non-empty by
    // construction; surface a structured error rather than panic if a malformed
    // `Interp` slice ever reaches here.
    let Some(last) = pieces.pop() else {
        return Err(ErrKind::EmptyInterpolation.at(span));
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
                    id: NodeId::DUMMY,
                    synth: e.synth,
                    node: Expr::Call(f, args),
                    span: e.span,
                }),
            }
        }
        node => Err(Spanned {
            id: NodeId::DUMMY,
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
        id: NodeId::DUMMY,
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

// `lvalue := value`: assign to a `var` (`Sugar::Assign`) or an index target
// `a[i]` (`Sugar::IndexAssign`). Any other left side is a parse error.
/// # Errors
/// Fails when the left side is neither a variable nor an index.
pub fn assign_stmt(
    lhs: S<Expr>,
    value: S<Expr>,
    l: usize,
    r: usize,
) -> Result<S<Expr>, (Span, String)> {
    let span = Span::new(l, r);
    match lhs.node {
        Expr::Var(name) => Ok(sp(Expr::Sugar(Sugar::Assign(name, Box::new(value))), span)),
        Expr::Index(recv, key) => Ok(sp(
            Expr::Sugar(Sugar::IndexAssign(recv, key, Box::new(value))),
            span,
        )),
        _ => Err((
            lhs.span,
            "the left side of `:=` must be a variable or an index `a[i]`".into(),
        )),
    }
}

// `lvalue <op>= e` on a `var` or index target. The index form reads the element
// with a synth `Index` so the formatter restores the `a[i] <op>= e` surface.
/// # Errors
/// Fails when the left side is neither a variable nor an index.
pub fn compound_stmt(
    lhs: S<Expr>,
    op: BinOp,
    value: S<Expr>,
    l: usize,
    r: usize,
) -> Result<S<Expr>, (Span, String)> {
    let span = Span::new(l, r);
    match lhs.node {
        Expr::Var(name) => Ok(compound_assign(name, op, value, l, r)),
        Expr::Index(recv, key) => {
            let read = Spanned {
                id: NodeId::DUMMY,
                synth: true,
                node: Expr::Index(recv.clone(), key.clone()),
                span,
            };
            let rhs = Spanned {
                id: NodeId::DUMMY,
                synth: true,
                node: Expr::Bin(op, Box::new(read), Box::new(value)),
                span,
            };
            Ok(sp(
                Expr::Sugar(Sugar::IndexAssign(recv, key, Box::new(rhs))),
                span,
            ))
        }
        _ => Err((
            lhs.span,
            "the left side of a compound assignment must be a variable or an index `a[i]`".into(),
        )),
    }
}

// `x <op>= e` is sugar for `x := x <op> e`. The synthesized RHS `Bin` is marked
// `synth` so the formatter restores the compound surface, while a hand-written
// `x := x + e` (a non-synth `Bin`) keeps its explicit form.
#[must_use]
pub fn compound_assign(x: String, op: BinOp, v: S<Expr>, l: usize, r: usize) -> S<Expr> {
    let span = Span::new(l, r);
    let lhs = sp(Expr::Var(x.clone()), span);
    let rhs = Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::Bin(op, Box::new(lhs), Box::new(v)),
        span,
    };
    sp(Expr::Sugar(Sugar::Assign(x, Box::new(rhs))), span)
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
            Expr::Var(_) if kw == kw::VIEW => 1,
            _ => return Err((cspan, format!("`{kw}` clause must be a lambda"))),
        };
        let want = if kw == kw::VIEW { 1 } else { params.len() };
        if arity != want {
            return Err((
                cspan,
                format!("`{kw}` for pattern `{name}` must take {want} argument(s), this lambda takes {arity}"),
            ));
        }
        let slot = if kw == kw::VIEW { &mut view } else { &mut make };
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
