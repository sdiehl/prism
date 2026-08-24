//! The scope a release resolves against.
//!
//! Every other reference-count operation names an occurrence in the subtree that
//! justified it. A release is the exception: it discharges a name the site owns
//! and does not use, so no occurrence of it exists there to point at, and the
//! binder that introduced it has to answer instead. This is the map that keeps
//! those binders reachable.

use std::collections::BTreeMap;

use prism_common::sym::Sym;

use super::super::specialize_support::binder_occurrence;
use super::super::{TypedBinder, TypedValue};

pub(super) type Scope = BTreeMap<Sym, TypedValue>;

// The scope is one shared map mutated in place: cloning it per binder made
// deep bind chains quadratic in the number of globals plus locals. Each entry
// records the value it displaced so a reverse replay restores the enclosing
// scope exactly, including a shadowed global or outer local of the same name.
pub(super) type ScopeUndo = Vec<(Sym, Option<TypedValue>)>;

pub(super) fn bind_scope(scope: &mut Scope, binders: &[TypedBinder]) -> ScopeUndo {
    binders
        .iter()
        .map(|binder| {
            (
                binder.name,
                scope.insert(binder.name, binder_occurrence(binder)),
            )
        })
        .collect()
}

pub(super) fn unbind_scope(scope: &mut Scope, undo: ScopeUndo) {
    for (name, displaced) in undo.into_iter().rev() {
        match displaced {
            Some(value) => {
                scope.insert(name, value);
            }
            None => {
                scope.remove(&name);
            }
        }
    }
}

// The scope answers for binders only. A `drop` discharges a name the site owns
// and does not use, so no occurrence of it exists there to point at, and the
// binder that introduced it is the witness. Every other operation takes its
// witness from an occurrence in the subtree that justified it, so nothing
// reaches here that a lexical binder cannot answer.
//
// Unlike the effect-lowering cascade, RC has no downgrade: it runs once on the
// committed lowered tree and emits the dup/drop operations codegen relies on
// for memory safety. A missing scope entry means the RC pass cannot know the
// operand's runtime representation, and a guessed representation would emit a
// mistyped dup/drop (a leak or a use-after-free), strictly worse than a loud
// failure. So this invariant deliberately stays a hard check rather than a
// silent decline; it is unreachable on verified input, which the typed
// verifier guarantees before RC ever runs.
pub(super) fn operand(scope: &Scope, name: Sym) -> TypedValue {
    scope
        .get(&name)
        .unwrap_or_else(|| panic!("verified RC operand {name} is out of scope"))
        .clone()
}
