//! Reference-count insertion for witness-carrying Core.

mod census;
mod ops;
mod rename;
mod scope;
mod spine;
#[cfg(test)]
mod tests;
mod worklist;

use std::collections::BTreeSet;

use crate::core::fbip::Sigs;
use crate::types::scalar_plan;
use prism_common::sym::Sym;

use super::{
    EffectLowered, Owned, TypedBinder, TypedCore, TypedPattern, TypedValue, TypedValueKind,
    UncheckedTypedCore,
};

type Set = BTreeSet<Sym>;

/// Insert precise reference-count operations without erasing type witnesses.
#[must_use]
pub fn insert_rc(core: TypedCore<EffectLowered>, sigs: &Sigs) -> UncheckedTypedCore<Owned> {
    worklist::insert(core, sigs)
}

fn borrowed_at(mask: Option<&[bool]>, index: usize) -> bool {
    mask.is_some_and(|entries| entries.get(index).copied().unwrap_or(false))
}

fn referenced_binding(mut value: &TypedValue) -> Option<Sym> {
    loop {
        match &value.kind {
            TypedValueKind::Var { name, .. } => return Some(*name),
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::LoweredRepr {
                value: inner,
                proof: _,
            }
            | TypedValueKind::NewtypeRepr { value: inner, .. } => value = inner,
            _ => return None,
        }
    }
}

// `Sym` orders by intern id rather than emitted name.
fn by_name(syms: impl IntoIterator<Item = Sym>) -> Vec<Sym> {
    let mut names: Vec<Sym> = syms.into_iter().collect();
    names.sort_by(|lhs, rhs| lhs.as_str().cmp(rhs.as_str()));
    names
}

fn anchored_borrow_arg(value: &TypedValue) -> bool {
    referenced_binding(value).is_some() || scalar_without_cell(&value.kind)
}

fn scalar_without_cell(mut kind: &TypedValueKind) -> bool {
    while let TypedValueKind::Reinterpret(inner)
    | TypedValueKind::LoweredRepr {
        value: inner,
        proof: _,
    }
    | TypedValueKind::NewtypeRepr { value: inner, .. } = kind
    {
        kind = &inner.kind;
    }
    kind.literal_scalar_type()
        .and_then(|ty| scalar_plan(&ty).ok())
        .is_some_and(|plan| !plan.owns_fresh_cell())
}

fn pattern_binders(pattern: &TypedPattern) -> Vec<&TypedBinder> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().collect()
        }
    }
}
