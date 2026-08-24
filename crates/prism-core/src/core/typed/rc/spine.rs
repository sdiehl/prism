//! Rewriting a right-leaning `Bind` chain in one pass over its levels.

use std::collections::BTreeMap;

use crate::core::fbip::Sigs;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;

use super::super::specialize_support::{
    binder_occurrence, free_comp_var_witnesses, free_comp_vars,
};
use super::super::{CompSig, TypedBinder, TypedComp, TypedCompKind, TypedValue};
use super::ops::{pure_unit, seq};
use super::scope::{operand, unbind_scope, Scope, ScopeUndo};
use super::{by_name, rc, Set};

/// One right-spine `Bind` level and the free-variable facts its ownership
/// partition needs.
struct SpineStep<'a> {
    sig: &'a CompSig,
    first: &'a TypedComp,
    binder: &'a TypedBinder,
    /// The free names of `first`, each with the occurrence that produced it.
    /// Membership answers the ownership tests, and the value answers which
    /// occurrence a retain emitted at this level is retaining.
    first_refs: BTreeMap<Sym, TypedValue>,
    /// How many suffix components reference the binder's name while it is in
    /// scope; the forward pass restores this count once the level is done.
    prev_count: u32,
}

/// A rewritten spine level, ready to be reassembled from the tail outward.
struct SpineLevel<'a> {
    sig: &'a CompSig,
    binder: &'a TypedBinder,
    first: TypedComp,
    shared_ops: Vec<TypedValue>,
    dead_ops: Vec<TypedValue>,
}

/// Rewrite a right-leaning `Bind` chain in one pass over its levels.
///
/// A per-level recursion would recompute `free_comp_vars` on both subtrees at
/// every step, which is quadratic in the chain length. This walk derives the
/// same facts bottom-up: a backward pass over the spine accumulates a count of
/// how many suffix components reference each name, and the forward pass peels
/// one component's contribution back off per level, leaving exactly the
/// membership the recursive formulation computed from scratch. Counting
/// components (not occurrences) suffices because every decision below is a
/// set-membership test. The ownership partition, operand resolution point,
/// and dup/drop wrap order are unchanged, so the emitted tree is identical.
// The renamed reference a level's first component reads, when that is all it
// does. Wrappers are transparent through `referenced_binding`, matching what
// erasure leaves behind.
fn alias_source(comp: &TypedComp) -> Option<Sym> {
    match &comp.kind {
        TypedCompKind::Return(value) => value.referenced_binding(),
        _ => None,
    }
}

pub(super) fn rc_bind_spine(
    comp: &TypedComp,
    owned: &Set,
    borrowed: &Set,
    sigs: &Sigs,
    scope: &mut Scope,
    fresh: &mut Fresh,
) -> TypedComp {
    let mut steps = Vec::new();
    let mut cursor = comp;
    while let TypedCompKind::Bind(first, binder, rest) = &cursor.kind {
        steps.push(SpineStep {
            sig: &cursor.sig,
            first,
            binder,
            first_refs: free_comp_var_witnesses(first),
            prev_count: 0,
        });
        cursor = rest;
    }
    let tail = cursor;

    // Backward pass: `live` maps each name to the number of remaining spine
    // components (suffix firsts plus the tail) in which it occurs free. A
    // binder's occurrences are bound over its rest, so its count is saved and
    // withdrawn before the defining component's own free set is added back
    // (where the same name may legitimately reference an outer binding).
    let mut live: BTreeMap<Sym, u32> = free_comp_vars(tail)
        .into_iter()
        .map(|name| (name, 1))
        .collect();
    for step in steps.iter_mut().rev() {
        step.prev_count = live.remove(&step.binder.name).unwrap_or(0);
        for name in step.first_refs.keys() {
            *live.entry(*name).or_insert(0) += 1;
        }
    }

    // Forward pass: at each level, removing the defining component's
    // contribution leaves `live` keyed by exactly the free variables of the
    // chain rest with the binder excluded, the `rest_free` of the recursive
    // formulation. Ownership then splits as before: names live on both sides
    // are dupped, names live on neither are dropped, and the binder joins the
    // owned set for the rest of the chain.
    let mut owned = owned.clone();
    let mut borrowed = borrowed.clone();
    let mut undo: ScopeUndo = Vec::with_capacity(steps.len());
    let mut levels: Vec<SpineLevel<'_>> = Vec::with_capacity(steps.len());
    for step in &steps {
        for name in step.first_refs.keys() {
            if let Some(count) = live.get_mut(name) {
                if *count > 1 {
                    *count -= 1;
                } else {
                    live.remove(name);
                }
            }
        }
        let first_owned: Set = owned
            .iter()
            .filter(|name| step.first_refs.contains_key(*name))
            .copied()
            .collect();
        let mut rest_owned: Set = owned
            .iter()
            .filter(|name| live.contains_key(*name))
            .copied()
            .collect();
        let shared = by_name(
            first_owned
                .iter()
                .filter(|name| rest_owned.contains(*name))
                .copied(),
        );
        let dead = by_name(
            owned
                .iter()
                .filter(|name| !step.first_refs.contains_key(*name) && !live.contains_key(*name))
                .copied(),
        );
        let first_borrowed: Set = borrowed
            .iter()
            .filter(|name| step.first_refs.contains_key(*name))
            .copied()
            .collect();
        let mut rest_borrowed: Set = borrowed
            .iter()
            .filter(|name| live.contains_key(*name))
            .copied()
            .collect();
        // A first that merely renames a loaned reference extends the loan: the
        // binder reads the same cell the loan keeps live, so no retain is
        // inserted for the occurrence and the binder joins the borrowed set
        // for the rest of the chain instead of the owned set. Representation
        // wrappers are transparent here exactly as they are under erasure, so
        // the erased token checker keys on the identical syntactic shape.
        let alias = step.binder.name.as_str() != "_"
            && alias_source(step.first).is_some_and(|name| borrowed.contains(&name));
        // A shared name is free in `first` by construction, so its retain names
        // the occurrence there rather than a lookup by name. A dead name has no
        // occurrence at this level to point at, which is what makes it dead, so
        // its release names the binder that introduced it.
        let shared_ops: Vec<TypedValue> = shared
            .iter()
            .map(|name| step.first_refs[name].clone())
            .collect();
        let dead_ops: Vec<TypedValue> = dead.iter().map(|name| operand(scope, *name)).collect();
        let first = if alias {
            step.first.clone()
        } else {
            rc(
                step.first,
                &first_owned,
                &first_borrowed,
                sigs,
                scope,
                fresh,
            )
        };
        undo.push((
            step.binder.name,
            scope.insert(step.binder.name, binder_occurrence(step.binder)),
        ));
        if alias {
            rest_borrowed.insert(step.binder.name);
        } else {
            rest_owned.insert(step.binder.name);
        }
        owned = rest_owned;
        borrowed = rest_borrowed;
        if step.prev_count > 0 {
            live.insert(step.binder.name, step.prev_count);
        }
        levels.push(SpineLevel {
            sig: step.sig,
            binder: step.binder,
            first,
            shared_ops,
            dead_ops,
        });
    }
    let mut out = rc(tail, &owned, &borrowed, sigs, scope, fresh);
    unbind_scope(scope, undo);

    // Reassemble from the tail outward; per level the dups wrap the bind and
    // the drops wrap the dups, each in ascending name order.
    for level in levels.into_iter().rev() {
        out = TypedComp::new(
            level.sig.clone(),
            TypedCompKind::Bind(Box::new(level.first), level.binder.clone(), Box::new(out)),
        );
        for value in level.shared_ops {
            out = seq(TypedComp::new(pure_unit(), TypedCompKind::Dup(value)), out);
        }
        for value in level.dead_ops {
            out = seq(TypedComp::new(pure_unit(), TypedCompKind::Drop(value)), out);
        }
    }
    out
}
