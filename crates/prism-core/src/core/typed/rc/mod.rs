//! Reference-count insertion for witness-carrying Core.
//!
//! This is the typed counterpart of [`super::super::fbip::insert_rc`]. It keeps
//! the same ownership partition, free-variable decisions, borrow masks, and
//! name-stable insertion order while retaining the witness for every inserted
//! `dup` and `drop` operand.

mod census;
mod ops;
mod scope;
mod spine;
#[cfg(test)]
mod tests;
mod thunks;

use std::collections::{BTreeMap, BTreeSet};

use crate::core::fbip::Sigs;
use crate::types::scalar_plan;
use crate::types::ty::EffRow;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use super::specialize_support::{binder_occurrence, free_comp_vars, substitute_terms};
use super::{
    CompSig, EffectLowered, Owned, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn,
    TypedPattern, TypedValue, TypedValueKind, UncheckedTypedCore,
};
use census::{borrowed_call_vars, leaf_census, occurrences, Census};
use ops::{defer_call_drops, drop_, dup, dup_each};
use scope::{bind_scope, operand, unbind_scope, Scope};
use spine::rc_bind_spine;
use thunks::rc_thunks;

type Set = BTreeSet<Sym>;

/// Insert precise reference-count operations without erasing type witnesses.
#[must_use]
pub fn insert_rc(core: TypedCore<EffectLowered>, sigs: &Sigs) -> UncheckedTypedCore<Owned> {
    let mut scope = Scope::new();
    let mut fresh = Fresh::new();
    let fns = core
        .into_unchecked()
        .into_functions()
        .into_iter()
        .map(|function| {
            let mask = sigs.get(&function.name).map(Vec::as_slice);
            let owned: Set = function
                .params
                .iter()
                .enumerate()
                .filter(|(index, _)| !borrowed_at(mask, *index))
                .map(|(_, binder)| binder.name)
                .collect();
            let borrowed: Set = function
                .params
                .iter()
                .enumerate()
                .filter(|(index, _)| borrowed_at(mask, *index))
                .map(|(_, binder)| binder.name)
                .collect();
            let undo = bind_scope(&mut scope, &function.params);
            let body = rc(
                &function.body,
                &owned,
                &borrowed,
                sigs,
                &mut scope,
                &mut fresh,
            );
            unbind_scope(&mut scope, undo);
            TypedCoreFn::new(
                function.name,
                function.params,
                body,
                function.sig,
                function.dict_arity,
            )
        })
        .collect();
    UncheckedTypedCore::new(fns)
}

fn borrowed_at(mask: Option<&[bool]>, index: usize) -> bool {
    mask.is_some_and(|entries| entries.get(index).copied().unwrap_or(false))
}

// `Sym` orders by intern id, which is intentionally unrelated to the stable
// emitted order. RC operations are therefore sorted by their textual names.
fn by_name(syms: impl IntoIterator<Item = Sym>) -> Vec<Sym> {
    let mut names: Vec<Sym> = syms.into_iter().collect();
    names.sort_by(|lhs, rhs| lhs.as_str().cmp(rhs.as_str()));
    names
}

fn rc(
    comp: &TypedComp,
    owned: &Set,
    borrowed: &Set,
    sigs: &Sigs,
    scope: &mut Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    match &comp.kind {
        TypedCompKind::Bind(..) => rc_bind_spine(comp, owned, borrowed, sigs, scope, fresh),
        TypedCompKind::If(condition, yes, no) => TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::If(
                condition.clone(),
                Box::new(rc(yes, owned, borrowed, sigs, scope, fresh)),
                Box::new(rc(no, owned, borrowed, sigs, scope, fresh)),
            ),
        ),
        TypedCompKind::Case(scrutinee, arms) => {
            // Matching on a loaned cell reads it without taking a reference: no
            // arm drops the cell (it is not owned here), and the pattern binders
            // become loans on its fields, kept live by whatever keeps the parent
            // live. Consuming uses of a field still retain first via the
            // borrowed leaf rule below. Wrappers are transparent through
            // `referenced_binding`, matching what erasure leaves behind.
            let loaned = scrutinee
                .referenced_binding()
                .is_some_and(|name| borrowed.contains(&name));
            let tracked: Set = owned.union(borrowed).copied().collect();
            TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Case(
                    scrutinee.clone(),
                    arms.iter()
                        .map(|(pattern, body)| {
                            let unshadowed = unshadow_arm(pattern, body, &tracked, fresh);
                            let (pattern, body) = unshadowed
                                .as_ref()
                                .map_or((pattern, body), |(pattern, body)| (pattern, body));
                            (
                                pattern.clone(),
                                rc_arm(pattern, body, owned, borrowed, sigs, scope, fresh, loaned),
                            )
                        })
                        .collect(),
                ),
            )
        }
        TypedCompKind::Lam(params, body) => {
            let params_set: Set = params.iter().map(|binder| binder.name).collect();
            let captures: Set = free_comp_vars(body)
                .difference(&params_set)
                .copied()
                .collect();
            let undo = bind_scope(scope, params);
            let body = rc(body, &params_set, &captures, sigs, scope, fresh);
            unbind_scope(scope, undo);
            TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Lam(params.clone(), Box::new(body)),
            )
        }
        TypedCompKind::Mask(effects, body) => TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::Mask(
                effects.clone(),
                Box::new(rc(body, owned, borrowed, sigs, scope, fresh)),
            ),
        ),
        // Effect lowering eliminates every `Handle` before RC runs: the
        // `EffectLowered` marker means handlers have already been rewritten into
        // evidence threading, state passing, or the free-monad driver. A handler
        // surviving to RC is a structural IR-invariant violation with no correct
        // reference-count treatment (there is no runtime handler to count
        // against), so it is a genuine compiler bug, not a case to handle. This
        // is deliberately a hard invariant, unlike the tier cascade's silent
        // declines: RC is post-commit and has no downgrade.
        TypedCompKind::Handle { .. } => {
            unreachable!("effect lowering removes every Handle before reference counting")
        }
        _ => {
            // The optimizer may leave a cell-owning value directly in a
            // borrowed argument; anchor each one to a fresh binder first so
            // the ordinary ownership rules below see a variable whose last
            // use is the loan and defer its release past the call.
            if let Some(anchored) = rebind_borrowed_temporaries(comp, sigs, fresh) {
                return rc(&anchored, owned, borrowed, sigs, scope, fresh);
            }
            let mut census = Census::new();
            leaf_census(comp, &mut census, sigs);
            let borrowed_call = borrowed_call_vars(comp, sigs);
            let deferred: Set = owned.intersection(&borrowed_call).copied().collect();
            let mut out = rc_thunks(comp, sigs, scope, fresh);
            if !deferred.is_empty() {
                out = defer_call_drops(out, &deferred, scope, fresh);
            }
            for name in by_name(owned.iter().copied()) {
                let seen = occurrences(&census, name);
                if deferred.contains(&name) {
                    // The call borrows the name, so nothing here consumes the
                    // reference the site owns: every occurrence needs its own.
                    out = dup_each(seen, out);
                } else if let Some((consumed, duplicated)) = seen.split_first() {
                    // The first occurrence spends the owned reference; the rest
                    // each need one, and `consumed` is only a witness that the
                    // site had a use to spend it on.
                    let _ = consumed;
                    out = dup_each(duplicated, out);
                } else {
                    out = drop_(name, out, scope);
                }
            }
            for name in by_name(borrowed.iter().copied()) {
                out = dup_each(occurrences(&census, name), out);
            }
            out
        }
    }
}

// A borrowed position may hold a value as it stands only when the loan has
// something to borrow without taking ownership: a variable names a reference
// the caller retains, and a scalar literal whose encoding plan owns no fresh
// heap cell (a zero or tagged word, or the static cell a `Str` literal names)
// has nothing to own. Every other value materializes a fresh cell at codegen:
// wide numeric literals box per use, and a constructor, tuple, or thunk
// allocates. The borrow convention says the callee will not consume that cell,
// so without an owner it leaks; such a value must be anchored to a binder the
// caller can release. Mirrors `fbip::scalar_without_cell`, which makes the
// erased checker refuse whatever this pass failed to anchor.
fn anchored_borrow_arg(value: &TypedValue) -> bool {
    value.referenced_binding().is_some() || scalar_without_cell(&value.kind)
}

fn scalar_without_cell(kind: &TypedValueKind) -> bool {
    kind.literal_scalar_type()
        .and_then(|ty| scalar_plan(&ty).ok())
        .is_some_and(|plan| !plan.owns_fresh_cell())
}

// Rewrite a call so every borrowed position holds a value the loan can anchor
// to. Borrow masks are committed before the typed optimizer runs, so
// simplification may inline a cell-owning value (a boxed scalar literal, a
// freshly built structure) directly into a borrowed argument. Re-anchoring it
// as `bind %rc = return v in call .. %rc ..` hands the ordinary machinery an
// owned binder whose only use is the loan, which defers exactly one release to
// just after the call.
fn rebind_borrowed_temporaries(
    comp: &TypedComp,
    sigs: &Sigs,
    fresh: &mut Fresh,
) -> Option<TypedComp> {
    let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = &comp.kind
    else {
        return None;
    };
    let mask = sigs.get(callee).map(Vec::as_slice);
    let loose = |(index, argument): (usize, &TypedValue)| -> bool {
        borrowed_at(mask, index) && !anchored_borrow_arg(argument)
    };
    if !args.iter().enumerate().any(loose) {
        return None;
    }
    let mut anchors: Vec<(TypedBinder, TypedValue)> = Vec::new();
    let args = args
        .iter()
        .enumerate()
        .map(|(index, argument)| {
            if !loose((index, argument)) {
                return argument.clone();
            }
            let binder = TypedBinder::new(
                Sym::from(names::fresh_binder(names::FRESH_RC, fresh.bump())),
                argument.ty.clone(),
            );
            let anchored = TypedValue::new(
                binder.ty().clone(),
                TypedValueKind::Var {
                    name: binder.name(),
                    instantiation: Vec::new(),
                },
            );
            anchors.push((binder, argument.clone()));
            anchored
        })
        .collect();
    let mut out = TypedComp::new(
        comp.sig.clone(),
        TypedCompKind::Call {
            callee: *callee,
            instantiation: instantiation.clone(),
            args,
        },
    );
    for (binder, value) in anchors.into_iter().rev() {
        let returned = TypedComp::new(
            CompSig::new(value.ty.clone(), EffRow::Empty),
            TypedCompKind::Return(value),
        );
        out = TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::Bind(Box::new(returned), binder, Box::new(out)),
        );
    }
    Some(out)
}

fn pattern_binders(pattern: &TypedPattern) -> Vec<TypedBinder> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.clone()],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().cloned().collect()
        }
    }
}

/// Rebind pattern binders that reuse a name the match site still tracks.
///
/// A field binder spelled like a reference the site owns or borrows hides that
/// reference for the whole arm: every occurrence in the body denotes the field,
/// and the outer reference has none left there. Free variables are names, so
/// the liveness test in [`rc_arm`] would read those field occurrences as uses
/// of the outer reference, judge it live, and emit no release for it, leaking
/// its cell and everything the cell holds. Nor could the release be recovered
/// inside the arm, where the outer name no longer denotes the outer cell.
///
/// Renaming the binder restores the arm to the shape it would have had without
/// the collision, and the ordinary dead-name rule then releases the outer
/// reference exactly once. Fresh names are unforgeable, so the rename cannot
/// collide in turn.
fn unshadow_arm(
    pattern: &TypedPattern,
    body: &TypedComp,
    tracked: &Set,
    fresh: &mut Fresh,
) -> Option<(TypedPattern, TypedComp)> {
    let mut renames = BTreeMap::new();
    for binder in pattern_binders(pattern) {
        if tracked.contains(&binder.name) {
            let mut rebound = binder.clone();
            rebound.name = Sym::from(names::fresh_binder(names::FRESH_RC, fresh.bump()));
            renames.insert(binder.name, rebound);
        }
    }
    if renames.is_empty() {
        return None;
    }
    let substitution: BTreeMap<Sym, TypedValue> = renames
        .iter()
        .map(|(shadowed, rebound)| (*shadowed, binder_occurrence(rebound)))
        .collect();
    let body = substitute_terms(body, &substitution, fresh.counter(), names::FRESH_RC);
    Some((rename_binders(pattern, &renames), body))
}

fn rename_binders(pattern: &TypedPattern, renames: &BTreeMap<Sym, TypedBinder>) -> TypedPattern {
    let rebind = |binder: &TypedBinder| {
        renames
            .get(&binder.name)
            .cloned()
            .unwrap_or_else(|| binder.clone())
    };
    let rebind_fields = |fields: &Vec<Option<TypedBinder>>| {
        fields
            .iter()
            .map(|field| field.as_ref().map(&rebind))
            .collect()
    };
    match pattern {
        TypedPattern::Wild => TypedPattern::Wild,
        TypedPattern::Var(binder) => TypedPattern::Var(rebind(binder)),
        TypedPattern::Ctor {
            name,
            instantiation,
            fields,
        } => TypedPattern::Ctor {
            name: *name,
            instantiation: instantiation.clone(),
            fields: rebind_fields(fields),
        },
        TypedPattern::Tuple(fields) => TypedPattern::Tuple(rebind_fields(fields)),
    }
}

#[allow(clippy::too_many_arguments)]
fn rc_arm(
    pattern: &TypedPattern,
    body: &TypedComp,
    owned: &Set,
    borrowed: &Set,
    sigs: &Sigs,
    scope: &mut Scope,
    fresh: &mut Fresh,
    loaned: bool,
) -> TypedComp {
    let body_free = free_comp_vars(body);
    let binders = pattern_binders(pattern);
    let fields: Set = binders.iter().map(|binder| binder.name).collect();
    let live = by_name(fields.intersection(&body_free).copied());
    let dead = by_name(
        owned
            .iter()
            .filter(|name| !body_free.contains(*name))
            .copied(),
    );
    let mut body_owned: Set = owned.intersection(&body_free).copied().collect();
    let mut body_borrowed: Set = borrowed.intersection(&body_free).copied().collect();
    if loaned {
        body_borrowed.extend(live.iter().copied());
    } else {
        body_owned.extend(live.iter().copied());
    }
    // The wraps resolve against the arm scope (fields visible), so the arm's
    // binders stay installed until after they are emitted.
    let undo = bind_scope(scope, &binders);
    let mut out = rc(body, &body_owned, &body_borrowed, sigs, scope, fresh);
    for name in &dead {
        out = drop_(*name, out, scope);
    }
    // A live field of an owned scrutinee is retained as it is projected out,
    // before the body that reads it exists, so the binder the pattern
    // introduced is the witness rather than any occurrence of it. A loaned
    // scrutinee's fields are loans themselves and retain nothing here.
    if !loaned {
        for name in live.iter().rev() {
            out = dup(operand(scope, *name), out);
        }
    }
    unbind_scope(scope, undo);
    out
}
