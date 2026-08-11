//! Parse-time grammar helpers and statement-level surface sugar.

use marginalia::Span;

use crate::ast::{
    call, evar, sp, sp_sugar, Arm, BinOp, Converter, Expr, Marker, Migration, MigrationDir, NodeId,
    Param, PathOp, PathStep, Pattern, PatternDecl, ReflectKind, Rung, Spanned, StableDecl, Sugar,
    Total, Ty, S,
};
use crate::kw;
use crate::names;

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

// One entry of a `stable` block body: a version rung, a hand-written converter,
// or the migration table. The parser collects them interleaved (they share the
// comma-separated body); `build_stable` partitions them and enforces the
// ordering invariant.
#[derive(Debug)]
pub enum StableItem {
    Rung(Rung),
    Conv(Converter),
    Migrations(Vec<Migration>),
}

// Normalize a `version(...)` direction value: the contextual word `auto` (parsed
// as a bare variable) asks the compiler to derive that direction, anything else
// is a hand-supplied function. Done at parse time, before name resolution, so a
// resolver never sees the `auto` marker as a value reference.
#[must_use]
pub fn mig_dir(e: S<Expr>) -> MigrationDir {
    match &e.node {
        Expr::Var(v) if v == kw::AUTO => MigrationDir::Auto,
        _ => MigrationDir::Expr(e),
    }
}

/// Build a `reflect fn f` / `reflect type T` quotation, given the contextual
/// word that introduced it.
///
/// `reflect` is an ident rather than a reserved word, so the grammar can only
/// recognize the form by the `fn` / `type` that follows and must check the word
/// itself here; every arity of the form checks it the same way.
///
/// # Errors
/// Fails when the leading word is not `reflect`, which means the input is some
/// other juxtaposition of an identifier and a declaration keyword.
pub fn reflect_expr(
    word: &str,
    kind: ReflectKind,
    name: String,
    span: Span,
) -> Result<S<Expr>, (Span, String)> {
    if word == kw::REFLECT {
        Ok(sp(Expr::Sugar(Sugar::Reflect(kind, name)), span))
    } else {
        let form = kind.as_str();
        Err((
            span,
            format!("expected `{}` before `{form}`, found `{word}`", kw::REFLECT),
        ))
    }
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
    let mut migrations = Vec::new();
    let mut saw_body = false;
    for item in items {
        match item {
            StableItem::Rung(r) => {
                if saw_body {
                    return Err((
                        r.span,
                        format!(
                            "rung `{}` must come before the converters and migrations in \
                             `stable {name}`",
                            r.name
                        ),
                    ));
                }
                rungs.push(r);
            }
            StableItem::Conv(c) => {
                saw_body = true;
                converters.push(c);
            }
            StableItem::Migrations(rows) => {
                saw_body = true;
                if !migrations.is_empty() {
                    return Err((span, format!("`stable {name}` has two migration tables")));
                }
                migrations = rows;
            }
        }
    }
    if rungs.is_empty() {
        return Err((span, format!("`stable {name}` declares no version rungs")));
    }
    Ok(StableDecl {
        name,
        rungs,
        converters,
        migrations,
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

/// Classify the contextual leading declaration modifiers before a `fn`.
///
/// The canonical order is `test assume total`. Each stays an ordinary identifier
/// everywhere else (the grammar only reaches here in the leading-modifier
/// position), so a leading ident that is not one of them is a pointed
/// "not a declaration modifier" diagnostic rather than a bare parse failure.
///
/// # Errors
/// A message when the idents are not a valid ordered modifier prefix.
pub fn decl_mods(words: &[&str]) -> Result<(bool, Total), String> {
    let mut test = false;
    let mut rest = words;
    if let [first, tail @ ..] = rest {
        if *first == kw::TEST {
            test = true;
            rest = tail;
        }
    }
    let total = match rest {
        [] => Total::No,
        [t] if *t == kw::TOTAL => Total::Prove,
        [a, t] if *a == kw::ASSUME && *t == kw::TOTAL => Total::Assume,
        _ => {
            return Err(format!(
                "`{}` is not a declaration modifier; expected `test`, `total`, or \
                 `assume total` before `fn`",
                words.join(" ")
            ));
        }
    };
    Ok((test, total))
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
                pat: None,
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

// A parameter position holds a pattern, but a bare variable written there is the
// ordinary named parameter and not a match at all: `fn f(x)` binds `x`, it does
// not test against it, and the wildcard names a parameter the body ignores. Every
// other shape is a pattern parameter, whose name is filled in by [`params`].
#[must_use]
pub fn param(borrow: bool, pat: S<Pattern>, ty: Option<Ty>, default: Option<S<Expr>>) -> Param {
    let named = |name: String| Param {
        name,
        ty: ty.clone(),
        borrow,
        pat: None,
        default: default.clone(),
    };
    match &pat.node {
        Pattern::Var(x) => named(x.clone()),
        Pattern::Wild => named(names::WILD.into()),
        _ => Param {
            name: String::new(),
            ty,
            borrow,
            pat: Some(pat),
            default,
        },
    }
}

// Name each pattern parameter after its position. Every parameter list is built
// through here, so a pattern parameter is never handed on unnamed.
#[must_use]
pub fn params(ps: Vec<Param>) -> Vec<Param> {
    ps.into_iter()
        .enumerate()
        .map(|(i, mut p)| {
            if p.pat.is_some() {
                p.name = names::pat_param(i);
            }
            p
        })
        .collect()
}

// A pattern `let` is a one-arm match; the `synth` flag (set by `sp_sugar`) is
// the marker the formatter keys on to restore the `let` surface. Exhaustiveness
// checking then rejects refutable patterns with its normal error.
#[must_use]
pub fn let_pat(pat: S<Pattern>, v: S<Expr>, rest: S<Expr>, l: usize) -> S<Expr> {
    match unwrap_try(v) {
        Ok(scrut) => try_stmt(Some(pat), scrut, rest, l),
        Err(v) => sp_sugar(
            Expr::Match(
                Box::new(v),
                vec![Arm {
                    pat,
                    guard: None,
                    body: rest,
                    alt: false,
                }],
            ),
            Span::empty(l),
        ),
    }
}

// `let pat = v else fallback`: the rest of the block is what the pattern binds
// into, and `fallback` is the block's value when the pattern does not match, so
// a failed binding leaves the enclosing block at that point. A two-arm match
// whose `synth` flag (set by `sp_sugar`) marks it for the formatter; the
// fallback arm is a wildcard, which is what tells it apart from the `?` desugar
// (whose second arm is always an `Err` constructor). The wildcard carries the
// fallback's span, so a pattern that cannot fail reports its dead arm there.
#[must_use]
pub fn let_else(
    pat: S<Pattern>,
    v: S<Expr>,
    fallback: S<Expr>,
    rest: S<Expr>,
    l: usize,
) -> S<Expr> {
    let wild = Spanned {
        id: NodeId::DUMMY,
        synth: false,
        node: Pattern::Wild,
        span: fallback.span,
    };
    let arms = vec![
        Arm {
            pat,
            guard: None,
            body: rest,
            alt: false,
        },
        Arm {
            pat: wild,
            guard: None,
            body: fallback,
            alt: false,
        },
    ];
    sp_sugar(Expr::Match(Box::new(v), arms), Span::empty(l))
}

// Shown when a path literal reaches for a step that focuses more than one place.
// The literal denotes a lens, which names exactly one focus, so admitting a
// fan-out step would change what the literal is rather than extend it; the
// message points at the traversal the program can build by hand instead.
pub const PATH_FIELDS_ONLY: &str =
    "a path literal takes field steps only (`#path a.b.c`): `each`, `[i]`, `?Ctor` and `where` \
     focus more than one place, so build those with `traversal` instead of a path literal";

// Shown when the sigil is followed by some other word. The `#` has already
// committed the expression to this form, so a different word is a misspelling
// rather than a new construct.
pub const PATH_EXPECTED: &str = "expected `path` after `#` here";

// Shown when an anchored literal names a type and then stops: the anchor only
// says what the whole is, so without a field there is nothing to focus.
pub const PATH_ANCHOR_NEEDS_FIELD: &str =
    "an anchored path literal needs at least one field after the type: `#path Type.field`";

// The field names a path literal's operand denotes, outermost first. The operand
// is whatever the ordinary expression rules made of the path, so the root is the
// first field rather than a value: `#path a.b.c` arrives as the field access
// `a.b.c` and means the three steps `a`, `b`, `c`. The bracketed read spelling is
// the same path written another way and flattens to the same steps. Anything else
// focuses something other than one field chain and is refused here.
fn path_fields(e: &Expr, out: &mut Vec<String>) -> Result<(), String> {
    match e {
        // A qualified head (`Solver.metas.next`) lexes as one dotted token, so
        // the root may carry several segments; split them here and let
        // `path_lit` decide whether the first is a type anchor.
        Expr::Var(root) => out.extend(root.split('.').map(str::to_string)),
        Expr::FieldAccess(base, f) => {
            path_fields(&base.node, out)?;
            out.push(f.clone());
        }
        Expr::Sugar(Sugar::ReadPath(base, steps)) => {
            path_fields(&base.node, out)?;
            for s in steps {
                let PathStep::Field(f) = s else {
                    return Err(PATH_FIELDS_ONLY.to_string());
                };
                out.push(f.clone());
            }
        }
        _ => return Err(PATH_FIELDS_ONLY.to_string()),
    }
    Ok(())
}

/// Build the optic literal `#path a.b.c`.
///
/// It expands to the lens over the getter and setter a reader would otherwise
/// write out: the getter reads the field chain, the setter rebuilds it through
/// the same update path a record update takes. Both halves are ordinary surface
/// syntax, so the literal introduces nothing below the parser and performs
/// nothing. The binders are `@` sigiled and so cannot be captured by a field name
/// along the path, and that unspellable pair is what the formatter matches on to
/// print the literal back.
///
/// # Errors
/// Fails when the sigil is followed by a word other than `path`, and when the
/// operand is anything but a chain of plain field steps.
pub fn path_lit(word: &str, e: &S<Expr>, span: Span) -> Result<S<Expr>, String> {
    if word != kw::PATH {
        return Err(PATH_EXPECTED.to_string());
    }
    let mut fields = Vec::new();
    path_fields(&e.node, &mut fields)?;
    // `#path Type.a.b`: an uppercase head is a root-type anchor rather than a
    // field (fields are lowercase), carried onto both `whole@` binders as an
    // ordinary annotation. That is what lets the literal sit inline where
    // nothing else names the whole type, e.g. `gets_at(#path Solver.metas.next)`.
    let anchor = if fields
        .first()
        .is_some_and(|f| f.starts_with(char::is_uppercase))
    {
        Some(fields.remove(0))
    } else {
        None
    };
    if fields.is_empty() {
        return Err(PATH_ANCHOR_NEEDS_FIELD.to_string());
    }
    let whole_ty = anchor.map(|t| Ty::Con(t, Vec::new()));
    let par = |name: &str, ty: Option<Ty>| Param {
        name: name.into(),
        ty,
        borrow: false,
        pat: None,
        default: None,
    };
    let read = fields.iter().fold(evar(names::PATH_WHOLE, span), |acc, f| {
        sp(Expr::FieldAccess(Box::new(acc), f.clone()), span)
    });
    let getter = sp(
        Expr::Lam(
            vec![par(names::PATH_WHOLE, whole_ty.clone())],
            Box::new(read),
        ),
        span,
    );
    let steps: Vec<PathStep> = fields.into_iter().map(PathStep::Field).collect();
    let write = sp(
        Expr::RecordUpdatePath(
            Box::new(evar(names::PATH_WHOLE, span)),
            vec![(steps, PathOp::Set(evar(names::PATH_PART, span)))],
        ),
        span,
    );
    let setter = sp(
        Expr::Lam(
            vec![
                par(names::PATH_WHOLE, whole_ty),
                par(names::PATH_PART, None),
            ],
            Box::new(write),
        ),
        span,
    );
    Ok(sp_sugar(
        Expr::Call(Box::new(evar(names::LENS_FN, span)), vec![getter, setter]),
        span,
    ))
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

// `let pat = e?` and bare `e?` statements: the rest of the block becomes the
// Ok arm and an Err rethrows, a two-arm match whose `synth` flag (set by
// `sp_sugar`) marks it for the formatter.
fn try_stmt(binder: Option<S<Pattern>>, scrut: S<Expr>, rest: S<Expr>, l: usize) -> S<Expr> {
    let s = scrut.span;
    let scrut_pat = |node| Spanned {
        id: NodeId::DUMMY,
        synth: false,
        node,
        span: s,
    };
    let ok = scrut_pat(Pattern::Ctor(
        "Ok".into(),
        vec![binder.unwrap_or_else(|| scrut_pat(Pattern::Wild))],
    ));
    let err = scrut_pat(Pattern::Ctor(
        "Err".into(),
        vec![scrut_pat(Pattern::Var(names::ERR.into()))],
    ));
    let rethrow = call(evar("Err", s), vec![evar(names::ERR, s)], s);
    let arms = vec![
        Arm {
            pat: ok,
            guard: None,
            body: rest,
            alt: false,
        },
        Arm {
            pat: err,
            guard: None,
            body: rethrow,
            alt: false,
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
        Ok(scrut) => {
            // Preserve the historical identifier-binder span: statement `?`
            // has always attached it to the scrutinee, and the handwritten
            // parser mirrors this construction.
            let s = scrut.span;
            let binder = Spanned {
                id: NodeId::DUMMY,
                synth: false,
                node: Pattern::Var(x),
                span: s,
            };
            try_stmt(Some(binder), scrut, rest, l)
        }
        Err(v) => sp(Expr::Let(x, Box::new(v), Box::new(rest)), Span::new(l, r)),
    }
}

// The lvalue shapes a statement assignment accepts beyond a bare name: a chain
// of field accesses and index steps over a root variable, flattened to the
// path-update steps the brace form takes. Dotted (qualified) and uppercase
// roots are constructor references, never assignable, so they return `None`.
fn lvalue_path(e: &Expr) -> Option<(String, Vec<PathStep>)> {
    match e {
        Expr::Var(x) if !x.contains('.') && !x.starts_with(char::is_uppercase) => {
            Some((x.clone(), Vec::new()))
        }
        Expr::FieldAccess(base, f) => {
            let (root, mut steps) = lvalue_path(&base.node)?;
            steps.push(PathStep::Field(f.clone()));
            Some((root, steps))
        }
        Expr::Index(base, key) => {
            let (root, mut steps) = lvalue_path(&base.node)?;
            steps.push(PathStep::Index((**key).clone()));
            Some((root, steps))
        }
        _ => None,
    }
}

// `x.a[i].b OP rhs`: the statement is the brace update it abbreviates,
// `x := { x | a[i].b OP rhs }`. The brace node is synth, which is what the
// formatter matches on to restore the statement surface; a hand-written
// `x := { x | ... }` is non-synth and keeps its explicit form.
fn path_assign(root: String, steps: Vec<PathStep>, op: PathOp, l: usize, r: usize) -> S<Expr> {
    let span = Span::new(l, r);
    let update = Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::RecordUpdatePath(Box::new(evar(&root, span)), vec![(steps, op)]),
        span,
    };
    sp(Expr::Sugar(Sugar::Assign(root, Box::new(update))), span)
}

// Whether a flattened lvalue needs the path route: any field step does. A pure
// var/index chain keeps the older `Assign`/`IndexAssign` forms, so existing
// programs desugar exactly as before.
fn has_field_step(steps: &[PathStep]) -> bool {
    steps.iter().any(|s| matches!(s, PathStep::Field(_)))
}

// The ambient-state lvalue: a nonempty path rooted at a literal `get()` call,
// as in `get().metas.next += 1`. The root spells the effect operation actually
// performed, so nothing implicit is invented.
fn state_lvalue(e: &Expr) -> Option<Vec<PathStep>> {
    match e {
        Expr::Call(f, args)
            if args.is_empty() && matches!(&f.node, Expr::Var(n) if n == names::STATE_GET) =>
        {
            Some(Vec::new())
        }
        Expr::FieldAccess(base, f) => {
            let mut steps = state_lvalue(&base.node)?;
            steps.push(PathStep::Field(f.clone()));
            Some(steps)
        }
        Expr::Index(base, key) => {
            let mut steps = state_lvalue(&base.node)?;
            steps.push(PathStep::Index((**key).clone()));
            Some(steps)
        }
        _ => None,
    }
}

// `get().a.b OP rhs`: the statement is the longhand it abbreviates,
// `put({ get() | a.b OP rhs })`, with both names resolving in the program's
// own scope. The brace node is synth, which is what the formatter matches on
// to restore the statement surface.
fn state_assign(steps: Vec<PathStep>, op: PathOp, l: usize, r: usize) -> S<Expr> {
    let span = Span::new(l, r);
    let get_call = call(evar(names::STATE_GET, span), vec![], span);
    let update = Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::RecordUpdatePath(Box::new(get_call), vec![(steps, op)]),
        span,
    };
    call(evar(names::STATE_PUT, span), vec![update], span)
}

const ASSIGN_LHS_MSG: &str =
    "the left side of `:=` must be a variable, an index `a[i]`, or a field path rooted at a \
     variable (`x.a[i].b`)";

const COMPOUND_LHS_MSG: &str =
    "the left side of a compound assignment must be a variable, an index `a[i]`, or a field \
     path rooted at a variable (`x.a[i].b`)";

// `lvalue := value`: assign to a `var` (`Sugar::Assign`), an index target
// `a[i]` (`Sugar::IndexAssign`), or a field path rooted at a `var` (the brace
// update it abbreviates). Any other left side is a parse error.
/// # Errors
/// Fails when the left side is none of those shapes.
pub fn assign_stmt(
    lhs: S<Expr>,
    value: S<Expr>,
    l: usize,
    r: usize,
) -> Result<S<Expr>, (Span, String)> {
    let span = Span::new(l, r);
    if let Some((root, steps)) = lvalue_path(&lhs.node) {
        if has_field_step(&steps) {
            return Ok(path_assign(root, steps, PathOp::Set(value), l, r));
        }
    }
    if let Some(steps) = state_lvalue(&lhs.node) {
        if !steps.is_empty() {
            return Ok(state_assign(steps, PathOp::Set(value), l, r));
        }
    }
    match lhs.node {
        Expr::Var(name) => Ok(sp(Expr::Sugar(Sugar::Assign(name, Box::new(value))), span)),
        Expr::Index(recv, key) => Ok(sp(
            Expr::Sugar(Sugar::IndexAssign(recv, key, Box::new(value))),
            span,
        )),
        _ => Err((lhs.span, ASSIGN_LHS_MSG.into())),
    }
}

// `lvalue <op>= e` on a `var`, index, or field-path target. The index form
// reads the element with a synth `Index` so the formatter restores the
// `a[i] <op>= e` surface; the field-path form routes through the brace update.
/// # Errors
/// Fails when the left side is none of those shapes.
pub fn compound_stmt(
    lhs: S<Expr>,
    op: BinOp,
    value: S<Expr>,
    l: usize,
    r: usize,
) -> Result<S<Expr>, (Span, String)> {
    let span = Span::new(l, r);
    // Statement compounds read the focus first and set it, the shape
    // `a[i] += e` already has, rather than closing over the right operand in a
    // modifier lambda: the roots here are var cells or `get()`, so the re-read
    // is a pure perform, and no lambda means nothing for the var escape
    // analysis to mistake for a captured cell.
    let read_back = |lhs: &S<Expr>, value: S<Expr>| Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::Bin(
            op,
            Box::new(Spanned {
                id: NodeId::DUMMY,
                synth: true,
                node: lhs.node.clone(),
                span,
            }),
            Box::new(value),
        ),
        span,
    };
    if let Some((root, steps)) = lvalue_path(&lhs.node) {
        if has_field_step(&steps) {
            let rhs = read_back(&lhs, value);
            return Ok(path_assign(root, steps, PathOp::Set(rhs), l, r));
        }
    }
    if let Some(steps) = state_lvalue(&lhs.node) {
        if !steps.is_empty() {
            let rhs = read_back(&lhs, value);
            return Ok(state_assign(steps, PathOp::Set(rhs), l, r));
        }
    }
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
        _ => Err((lhs.span, COMPOUND_LHS_MSG.into())),
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

// `var x : T := e`: the annotation rides the initializer as a synth `Ann`, so
// `VarDecl`'s shape (and the codec seam that mirrors it) is unchanged while the
// var-cell desugar reads the type off the initializer and declares its get/put
// ops at `T` instead of an inference placeholder. That is what lets a
// var-rooted path update resolve its fields without an inline ascription.
#[must_use]
pub fn var_decl(
    x: String,
    ty: Option<Ty>,
    v: S<Expr>,
    rest: S<Expr>,
    l: usize,
    r: usize,
) -> S<Expr> {
    let span = Span::new(l, r);
    let init = match ty {
        Some(t) => Spanned {
            id: NodeId::DUMMY,
            synth: true,
            node: Expr::Ann(Box::new(v), t),
            span,
        },
        None => v,
    };
    sp(
        Expr::Sugar(Sugar::VarDecl(x, Box::new(init), Box::new(rest))),
        span,
    )
}

// `p <op>= e` inside a path update is sugar for `p ~ \(focus@) -> focus@ <op> e`.
// A modifier rather than a set-with-read so the base is evaluated once and an
// `each` step applies the operation at every focus. The lambda and its `Bin`
// body are synth and the binder is the unspellable `focus@`, which together are
// what the formatter matches on to restore `p <op>= e`; a hand-written
// `p ~ \(k) -> k + e` keeps its explicit form.
#[must_use]
pub fn compound_path_op(op: BinOp, v: S<Expr>, l: usize, r: usize) -> PathOp {
    let span = Span::new(l, r);
    let focus = evar(names::PATH_FOCUS, span);
    let body = Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::Bin(op, Box::new(focus), Box::new(v)),
        span,
    };
    let lam = Spanned {
        id: NodeId::DUMMY,
        synth: true,
        node: Expr::Lam(
            vec![Param {
                name: names::PATH_FOCUS.into(),
                ty: None,
                borrow: false,
                pat: None,
                default: None,
            }],
            Box::new(body),
        ),
        span,
    };
    PathOp::Modify(lam)
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
