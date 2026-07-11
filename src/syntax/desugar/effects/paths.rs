//! Lowering of the optic path steps (`each`, `?Ctor`) to ordinary core.
//!
//! `each` becomes an `fmap` over a functor; `?Ctor` becomes a `match` that
//! rebuilds the focused constructor and passes every other constructor through
//! (the prism law for update). This pass eliminates both before type checking,
//! so the checker and elaborator only ever see `Field`-only paths (the proven
//! single-focus rebuild). The result is ordinary surface code (`fmap`, `match`,
//! field access, single-focus `RecordUpdatePath`), handed back to `rw` to
//! finish; `Functor` and constructor resolution ride the normal pipeline.
//!
//! Paths sharing a field prefix up to the same optic step fold together so
//! `{ xs | each.a = 1, each.b = 2 }` traverses once and `{ s | ?C.a = 1, ?C.b
//! = 2 }` matches once; conflicting paths (one a prefix of another) are rejected
//! here, where the full step path is still visible.
//!
//! Every synthesized structural node gets a fresh span (the user's own RHS
//! expressions keep theirs): tc keys `path_res` and `span_types` by span, so two
//! synthesized `RecordUpdatePath`s reusing one span would alias their resolved
//! chains and rebuild the wrong constructor.

use std::collections::BTreeMap;

use marginalia::Span;

use super::{rw, synth_span, Cx, Vars};
use crate::error::{ErrKind, TypeError};
use crate::syntax::ast::{Arm, Core, Expr, PathOp, PathStep, Pattern, Sugar, S};
use crate::syntax::desugar::{call, evar, lam1, sp, spat};
use crate::{kw, names};

type Path = (Vec<PathStep>, PathOp);

const fn is_field(s: &PathStep) -> bool {
    matches!(s, PathStep::Field(_))
}

fn first_optic(steps: &[PathStep]) -> Option<usize> {
    steps.iter().position(|s| !is_field(s))
}

pub(super) fn has_optic(ups: &[Path]) -> bool {
    ups.iter().any(|(steps, _)| first_optic(steps).is_some())
}

// Rewrite `{ base | ups }` (which contains at least one optic step) into the
// `fmap`/`match` form, then finish lowering with `rw`. The base is let-bound
// once so an optic's traversal cannot re-evaluate an effectful base.
pub(super) fn lower_optics(
    base: &S<Expr>,
    ups: &[Path],
    env: &Vars,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr<Core>>, TypeError> {
    conflict_check(ups, span)?;
    let bname = names::path_base(cx.next.bump());
    let body = build_update(&evar(&bname, synth_span(cx)), ups.to_vec(), cx, span)?;
    let letted = sp(
        Expr::Let(bname, Box::new(base.clone()), Box::new(body)),
        synth_span(cx),
    );
    rw(&letted, env, cx)
}

// The surface update for `{ base | paths }`, where `base` is a bound variable.
// When a path starts with an optic step the base is the optic target; otherwise
// it is a record, and `optic`-bearing fields are set to the lowered traversal.
fn build_update(
    base: &S<Expr>,
    paths: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    if paths
        .iter()
        .any(|(steps, _)| steps.first().is_some_and(|s| !is_field(s)))
    {
        return dispatch(base.clone(), paths, cx, span);
    }
    let mut field_paths: Vec<Path> = Vec::new();
    let mut groups: BTreeMap<Vec<String>, Vec<Path>> = BTreeMap::new();
    for (steps, op) in paths {
        match first_optic(&steps) {
            None => field_paths.push((steps, op)),
            // The optic step stays at the head of the rest so `dispatch` sees it.
            Some(k) => {
                let prefix = steps[..k].iter().map(field_name).collect();
                groups
                    .entry(prefix)
                    .or_default()
                    .push((steps[k..].to_vec(), op));
            }
        }
    }
    for (prefix, rests) in groups {
        let container = field_chain(base, &prefix, cx);
        let built = dispatch(container, rests, cx, span)?;
        let prefix_steps = prefix.into_iter().map(PathStep::Field).collect();
        field_paths.push((prefix_steps, PathOp::Set(built)));
    }
    Ok(sp(
        Expr::RecordUpdatePath(Box::new(base.clone()), field_paths),
        synth_span(cx),
    ))
}

// All paths' first step is an optic step (homogeneous in kind by the target's
// type). `each` fans out with `fmap`; `?Ctor` narrows with a `match`.
fn dispatch(
    target: S<Expr>,
    paths: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    match &paths[0].0[0] {
        PathStep::Each => {
            let rests = paths
                .into_iter()
                .map(|(s, op)| (s[1..].to_vec(), op))
                .collect();
            map_over(target, rests, cx, span)
        }
        PathStep::Case(_) => case_over(target, paths, cx, span),
        PathStep::Index(_) => index_over(target, paths, cx, span),
        PathStep::Where(_) => where_guard(target, paths, cx, span),
        PathStep::Field(_) => unreachable!("dispatch is only entered on an optic step"),
    }
}

// `if p(focus) then <rest> else focus`: apply the rest only to a focus the
// predicate keeps, passing the rest through unchanged. The predicate is the one
// the first path carries; sibling paths through the same filter share it.
fn where_guard(
    focus: S<Expr>,
    paths: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    let PathStep::Where(pred) = &paths[0].0[0] else {
        unreachable!("where_guard entered on a non-`where` step");
    };
    let pred = pred.clone();
    let stripped = paths
        .into_iter()
        .map(|(s, op)| (s[1..].to_vec(), op))
        .collect();
    let kept = apply_paths(focus.clone(), stripped, cx, span)?;
    let cond = call(pred, vec![focus.clone()], synth_span(cx));
    Ok(sp(
        Expr::If(Box::new(cond), Box::new(kept), Box::new(focus)),
        synth_span(cx),
    ))
}

// `index_set(xs, i, update(xs[i]))` per `[i]` path, threaded left to right: each
// index path transforms the running container, so later writes see earlier ones
// (overlapping indices are last-wins, which sequencing gives for free). The
// element is read once into a binder so an effectful/expensive index is not
// re-evaluated.
fn index_over(
    target: S<Expr>,
    paths: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    let mut acc = target;
    for (steps, op) in paths {
        let PathStep::Index(idx) = &steps[0] else {
            unreachable!("index_over entered on a non-`[i]` step");
        };
        let idx = idx.clone();
        let rest = steps[1..].to_vec();
        let v = names::path_base(cx.next.bump());
        // `index_set(v, idx, new)` returns the rebuilt container. The non-set
        // cases read the old element first, a failable read; defaulting the whole
        // step to `v` makes an out-of-range index a no-op instead of leaking a
        // `Fail` to the caller.
        let inner = if rest.is_empty() {
            match op {
                // A set never needs the old element.
                PathOp::Set(val) => index_set(&v, idx, val, cx),
                PathOp::Modify(f) => {
                    let e = names::path_each(cx.next.bump());
                    let read = index_read(&v, idx.clone(), cx);
                    let new = call(f, vec![evar(&e, synth_span(cx))], synth_span(cx));
                    let set = index_set(&v, idx, new, cx);
                    let body = sp(Expr::Let(e, Box::new(read), Box::new(set)), synth_span(cx));
                    default_to(&v, body, cx)
                }
            }
        } else {
            let e = names::path_each(cx.next.bump());
            let read = index_read(&v, idx.clone(), cx);
            let new = build_update(&evar(&e, synth_span(cx)), vec![(rest, op)], cx, span)?;
            let set = index_set(&v, idx, new, cx);
            let body = sp(Expr::Let(e, Box::new(read), Box::new(set)), synth_span(cx));
            default_to(&v, body, cx)
        };
        acc = sp(Expr::Let(v, Box::new(acc), Box::new(inner)), synth_span(cx));
    }
    Ok(acc)
}

fn index_set(v: &str, idx: S<Expr>, val: S<Expr>, cx: &mut Cx) -> S<Expr> {
    sp(
        Expr::IndexSet(
            Box::new(evar(v, synth_span(cx))),
            Box::new(idx),
            Box::new(val),
        ),
        synth_span(cx),
    )
}

// `v[idx]`, the failable indexed read of the focused element.
fn index_read(v: &str, idx: S<Expr>, cx: &mut Cx) -> S<Expr> {
    sp(
        Expr::Index(Box::new(evar(v, synth_span(cx))), Box::new(idx)),
        synth_span(cx),
    )
}

// `body ?? v`: run `body` (which reads the indexed element) in a `Fail` context,
// falling back to the unchanged container `v` when the index is out of range.
fn default_to(v: &str, body: S<Expr>, cx: &mut Cx) -> S<Expr> {
    sp(
        Expr::Sugar(Sugar::Default(
            Box::new(body),
            Box::new(evar(v, synth_span(cx))),
        )),
        synth_span(cx),
    )
}

// `fmap(.., container)` applying the per-element `rests` (the steps after the
// `each`) to each element.
fn map_over(
    container: S<Expr>,
    rests: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    if let [(steps, _)] = rests.as_slice() {
        if steps.is_empty() {
            let op = rests.into_iter().next().expect("one rest").1;
            return Ok(match op {
                // `~ f` is exactly `fmap(f, xs)`, keeping `f` checked against the
                // element type so an unannotated lambda still resolves.
                PathOp::Modify(f) => fmap_call(f, container, cx),
                // `= v` ignores the element; bind it fresh and return `v`.
                PathOp::Set(v) => {
                    let lam = lam1(&names::path_each(cx.next.bump()), v, synth_span(cx));
                    fmap_call(lam, container, cx)
                }
            });
        }
    }
    let ename = names::path_each(cx.next.bump());
    let body = build_update(&evar(&ename, synth_span(cx)), rests, cx, span)?;
    let lam = lam1(&ename, body, synth_span(cx));
    Ok(fmap_call(lam, container, cx))
}

// `match target of { C(fields) => C(updated); ..; _ => target }`: rebuild each
// focused constructor, leaving the rest untouched (the prism law for update).
fn case_over(
    target: S<Expr>,
    paths: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    let mut by_ctor: BTreeMap<String, Vec<Path>> = BTreeMap::new();
    for (steps, op) in paths {
        let PathStep::Case(c) = &steps[0] else {
            unreachable!("case_over entered on a non-`?Ctor` step");
        };
        by_ctor
            .entry(c.clone())
            .or_default()
            .push((steps[1..].to_vec(), op));
    }
    // How many constructors the focused type has (from any path's constructor).
    let by_ctor_total = by_ctor
        .keys()
        .next()
        .and_then(|c| cx.ctor_total.get(c).copied());
    let mut arms = Vec::new();
    for (ctor, subs) in by_ctor {
        let (arity, fields) = cx
            .ctor_shapes
            .get(&ctor)
            .cloned()
            .ok_or_else(|| ErrKind::UnknownPathCtor { ctor: ctor.clone() }.at(span))?;
        let binders: Vec<String> = (0..arity)
            .map(|_| names::path_each(cx.next.bump()))
            .collect();
        let mut new_args: Vec<S<Expr>> = binders.iter().map(|b| evar(b, synth_span(cx))).collect();
        let mut by_field: BTreeMap<usize, Vec<Path>> = BTreeMap::new();
        let mut whole: Option<PathOp> = None;
        for (s, op) in subs {
            let Some(head) = s.first() else {
                whole = Some(op);
                continue;
            };
            let PathStep::Field(f) = head else {
                return Err(ErrKind::PathCtorNeedsField { ctor }.at(span));
            };
            let idx = fields.iter().position(|n| n == f).ok_or_else(|| {
                ErrKind::UnknownField {
                    field: f.clone(),
                    ctor: ctor.clone(),
                }
                .at(span)
            })?;
            by_field.entry(idx).or_default().push((s[1..].to_vec(), op));
        }
        for (idx, fpaths) in by_field {
            new_args[idx] = apply_paths(evar(&binders[idx], synth_span(cx)), fpaths, cx, span)?;
        }
        let rebuilt = call(evar(&ctor, synth_span(cx)), new_args, synth_span(cx));
        let body = match whole {
            None => rebuilt,
            Some(PathOp::Set(v)) => v,
            Some(PathOp::Modify(f)) => call(f, vec![rebuilt], synth_span(cx)),
        };
        let pat = spat(
            Pattern::Ctor(
                ctor.clone(),
                binders
                    .iter()
                    .map(|b| spat(Pattern::Var(b.clone()), synth_span(cx)))
                    .collect(),
            ),
            synth_span(cx),
        );
        arms.push(Arm {
            pat,
            guard: None,
            body,
        });
    }
    // The pass-through arm is for constructors no path touched; drop it when the
    // paths already cover every constructor, which would make it unreachable.
    let exhaustive = by_ctor_total == Some(arms.len());
    if !exhaustive {
        arms.push(Arm {
            pat: spat(Pattern::Wild, synth_span(cx)),
            guard: None,
            body: target.clone(),
        });
    }
    Ok(sp(Expr::Match(Box::new(target), arms), synth_span(cx)))
}

// Apply `paths` to a focus expression: a lone terminal applies the op directly
// (`= v` is `v`, `~ f` is `f(focus)`); otherwise recurse through `build_update`.
fn apply_paths(
    focus: S<Expr>,
    paths: Vec<Path>,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    if let [(steps, _)] = paths.as_slice() {
        if steps.is_empty() {
            return Ok(match paths.into_iter().next().expect("one path").1 {
                PathOp::Set(v) => v,
                PathOp::Modify(f) => call(f, vec![focus], synth_span(cx)),
            });
        }
    }
    build_update(&focus, paths, cx, span)
}

// `s.[path]`: the list of foci `path` selects, the read twin of the update. A
// `Field`/`[i]` step descends, `each` flat-maps, `?Ctor` previews (zero or one),
// `where` filters; the leaf focus is a one-element list, concatenated up.
pub(super) fn read_path(
    base: &S<Expr>,
    steps: &[PathStep],
    env: &Vars,
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr<Core>>, TypeError> {
    let body = to_list(base.clone(), steps, cx, span)?;
    rw(&body, env, cx)
}

const fn nil(cx: &mut Cx) -> S<Expr> {
    sp(Expr::List(Vec::new()), synth_span(cx))
}

fn to_list(
    focus: S<Expr>,
    steps: &[PathStep],
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    let Some(step) = steps.first() else {
        // The leaf focus, as a one-element list.
        return Ok(sp(Expr::List(vec![focus]), synth_span(cx)));
    };
    let rest = &steps[1..];
    match step {
        PathStep::Field(f) => {
            let inner = sp(
                Expr::FieldAccess(Box::new(focus), f.clone()),
                synth_span(cx),
            );
            to_list(inner, rest, cx, span)
        }
        PathStep::Each => {
            let e = names::path_each(cx.next.bump());
            let body = to_list(evar(&e, synth_span(cx)), rest, cx, span)?;
            let lam = lam1(&e, body, synth_span(cx));
            // concat_map(\e -> <foci of e>, focus)
            Ok(call(
                evar(names::CONCAT_MAP_FN, synth_span(cx)),
                vec![lam, focus],
                synth_span(cx),
            ))
        }
        PathStep::Where(pred) => {
            let kept = to_list(focus.clone(), rest, cx, span)?;
            let cond = call(pred.clone(), vec![focus], synth_span(cx));
            let none = nil(cx);
            Ok(sp(
                Expr::If(Box::new(cond), Box::new(kept), Box::new(none)),
                synth_span(cx),
            ))
        }
        PathStep::Index(idx) => {
            let read = sp(
                Expr::Index(Box::new(focus), Box::new(idx.clone())),
                synth_span(cx),
            );
            let inner = to_list(read, rest, cx, span)?;
            // An out-of-range index selects no focus.
            let none = nil(cx);
            Ok(sp(
                Expr::Sugar(Sugar::Default(Box::new(inner), Box::new(none))),
                synth_span(cx),
            ))
        }
        PathStep::Case(ctor) => to_list_case(focus, ctor, rest, cx, span),
    }
}

// `match focus of { C(fields) => <foci>; _ => [] }`: preview through a prism.
fn to_list_case(
    focus: S<Expr>,
    ctor: &str,
    rest: &[PathStep],
    cx: &mut Cx,
    span: Span,
) -> Result<S<Expr>, TypeError> {
    let (arity, fields) = cx.ctor_shapes.get(ctor).cloned().ok_or_else(|| {
        ErrKind::UnknownPathCtor {
            ctor: ctor.to_string(),
        }
        .at(span)
    })?;
    let binders: Vec<String> = (0..arity)
        .map(|_| names::path_each(cx.next.bump()))
        .collect();
    let body = if let Some(PathStep::Field(f)) = rest.first() {
        let idx = fields.iter().position(|n| n == f).ok_or_else(|| {
            ErrKind::UnknownField {
                field: f.clone(),
                ctor: ctor.to_string(),
            }
            .at(span)
        })?;
        to_list(evar(&binders[idx], synth_span(cx)), &rest[1..], cx, span)?
    } else if rest.is_empty() {
        // `?C` alone previews the whole matched constructor.
        let rebuilt = call(
            evar(ctor, synth_span(cx)),
            binders.iter().map(|b| evar(b, synth_span(cx))).collect(),
            synth_span(cx),
        );
        sp(Expr::List(vec![rebuilt]), synth_span(cx))
    } else {
        return Err(ErrKind::PathCtorNeedsField {
            ctor: ctor.to_string(),
        }
        .at(span));
    };
    let pat = spat(
        Pattern::Ctor(
            ctor.to_string(),
            binders
                .iter()
                .map(|b| spat(Pattern::Var(b.clone()), synth_span(cx)))
                .collect(),
        ),
        synth_span(cx),
    );
    let mut arms = vec![Arm {
        pat,
        guard: None,
        body,
    }];
    // Drop the unreachable pass-through arm when the type has one constructor.
    if cx.ctor_total.get(ctor).copied() != Some(1) {
        arms.push(Arm {
            pat: spat(Pattern::Wild, synth_span(cx)),
            guard: None,
            body: nil(cx),
        });
    }
    Ok(sp(Expr::Match(Box::new(focus), arms), synth_span(cx)))
}

fn fmap_call(f: S<Expr>, container: S<Expr>, cx: &mut Cx) -> S<Expr> {
    call(
        evar(names::FMAP_METHOD, synth_span(cx)),
        vec![f, container],
        synth_span(cx),
    )
}

fn field_chain(base: &S<Expr>, fields: &[String], cx: &mut Cx) -> S<Expr> {
    fields.iter().fold(base.clone(), |acc, f| {
        sp(Expr::FieldAccess(Box::new(acc), f.clone()), synth_span(cx))
    })
}

fn field_name(s: &PathStep) -> String {
    match s {
        PathStep::Field(f) => f.clone(),
        _ => unreachable!("a prefix before the first optic step is all fields"),
    }
}

fn conflict_check(ups: &[Path], span: Span) -> Result<(), TypeError> {
    for (i, (p, _)) in ups.iter().enumerate() {
        for (q, _) in &ups[i + 1..] {
            if is_prefix(p, q) || is_prefix(q, p) {
                return Err(ErrKind::ConflictingUpdatePaths {
                    a: show_path(p),
                    b: show_path(q),
                }
                .at(span));
            }
        }
    }
    Ok(())
}

// Whether `short` is a step-by-step prefix of `long`, so the two paths write
// overlapping foci. `Index` steps never match: distinct (or even equal) indices
// compose by sequencing in `index_over`, so they are not flagged here.
fn is_prefix(short: &[PathStep], long: &[PathStep]) -> bool {
    short.len() <= long.len()
        && short.iter().zip(long).all(|(a, b)| match (a, b) {
            (PathStep::Field(x), PathStep::Field(y)) | (PathStep::Case(x), PathStep::Case(y)) => {
                x == y
            }
            (PathStep::Each, PathStep::Each) | (PathStep::Where(_), PathStep::Where(_)) => true,
            _ => false,
        })
}

fn show_path(steps: &[PathStep]) -> String {
    steps
        .iter()
        .map(|s| match s {
            PathStep::Field(f) => f.clone(),
            PathStep::Each => kw::EACH.into(),
            PathStep::Case(c) => format!("{}{c}", kw::QUESTION),
            PathStep::Index(_) => "[..]".into(),
            PathStep::Where(_) => kw::WHERE.into(),
        })
        .collect::<Vec<_>>()
        .join(".")
}
