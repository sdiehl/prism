//! Counting the references one leaf holds, and naming each one.
//!
//! The census is the single walk the ownership rules read. Its per-name length
//! is the count they compare against the reference the site owns, and its
//! entries are the terms they emit operations against, so the decision to insert
//! an operation and the justification for it cannot drift apart.

use std::collections::BTreeMap;

use crate::core::fbip::Sigs;
use prism_common::sym::Sym;

use super::super::specialize_support::free_comp_var_witnesses;
use super::super::{TypedComp, TypedCompKind, TypedValue, TypedValueKind};
use super::{borrowed_at, Set};

/// Every occurrence of a name in one leaf, in traversal order.
///
/// The length is the count the ownership rules read, and the entries are the
/// witnesses those rules emit against, so the decision to insert an operation
/// and the term that justifies it come out of one walk and cannot disagree.
pub(super) type Census = BTreeMap<Sym, Vec<TypedValue>>;

/// The occurrences of `name` this leaf holds, empty when it holds none.
pub(super) fn occurrences(census: &Census, name: Sym) -> &[TypedValue] {
    census.get(&name).map_or(&[], Vec::as_slice)
}

pub(super) fn borrowed_call_vars(comp: &TypedComp, sigs: &Sigs) -> Set {
    let TypedCompKind::Call { callee, args, .. } = &comp.kind else {
        return Set::new();
    };
    let mask = sigs.get(callee).map(Vec::as_slice);
    args.iter()
        .enumerate()
        .filter(|(index, _)| borrowed_at(mask, *index))
        // The retained set names the caller's own variables a borrowed
        // position leaves owned. By the time this census runs, anchoring has
        // rebound every cell-owning non-variable at a borrowed position to a
        // fresh binder, so the only non-variables left are scalars the backend
        // represents without a heap cell; those own nothing to retain and are
        // correctly absent from the set.
        .filter_map(|(_, arg)| arg.referenced_binding())
        .collect()
}

fn census_value(value: &TypedValue, census: &mut Census) {
    match &value.kind {
        TypedValueKind::Var { name, .. } => census.entry(*name).or_default().push(value.clone()),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                census_value(field, census);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                census_value(field, census);
            }
        }
        // A thunk cell captures one reference per distinct free name however many
        // times the suspended body reads it, so the census takes one witness per
        // name here rather than one per occurrence.
        TypedValueKind::Thunk(body) => {
            for (name, witness) in free_comp_var_witnesses(body) {
                census.entry(name).or_default().push(witness);
            }
        }
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => census_value(inner, census),
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => {}
    }
}

pub(super) fn leaf_census(comp: &TypedComp, census: &mut Census, sigs: &Sigs) {
    match &comp.kind {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => census_value(value, census),
        TypedCompKind::RefSet(cell, value) | TypedCompKind::InitAt(cell, value) => {
            census_value(cell, census);
            census_value(value, census);
        }
        TypedCompKind::App { callee, args, .. } => {
            // Same rule as a thunk: the closure holds one reference per captured
            // name, not one per read.
            for (name, witness) in free_comp_var_witnesses(callee) {
                census.entry(name).or_default().push(witness);
            }
            for arg in args {
                census_value(arg, census);
            }
        }
        TypedCompKind::Prim(_, lhs, rhs) => {
            census_value(lhs, census);
            census_value(rhs, census);
        }
        TypedCompKind::Call { callee, args, .. } => {
            let mask = sigs.get(callee).map(Vec::as_slice);
            for (index, arg) in args.iter().enumerate() {
                if !borrowed_at(mask, index) {
                    census_value(arg, census);
                }
            }
        }
        TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. }
        | TypedCompKind::Io(_, args) => {
            for arg in args {
                census_value(arg, census);
            }
        }
        TypedCompKind::Bind(_, _, _)
        | TypedCompKind::Lam(_, _)
        | TypedCompKind::If(_, _, _)
        | TypedCompKind::Case(_, _)
        | TypedCompKind::Handle { .. }
        | TypedCompKind::Mask(_, _)
        | TypedCompKind::UnboxedProject(_, _)
        | TypedCompKind::Dup(_)
        | TypedCompKind::Drop(_)
        | TypedCompKind::WithReuse { .. }
        | TypedCompKind::Reuse(_, _) => {}
    }
}
