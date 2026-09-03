//! The shared optimizer fact domain over typed Core values.
//!
//! A fact records what a binder provably holds in the region where the entry
//! is live: a literal, a must-alias of another in-scope name, a constructor
//! application, or a product. Facts are must-facts only; nothing speculative
//! is stored, and a binder whose value does not classify simply has no entry.
//! Consumers (today the simplifier; the inliner and specializer as the domain
//! grows) query this environment instead of rediscovering value shapes with
//! private maps.
//!
//! Two invariants bound the domain:
//!
//! - The stored value is always the original, possibly representation-wrapped,
//!   value. Classification looks through [`peel`]; every rewrite that consumes
//!   a fact carries the original value forward unchanged, so a
//!   `Reinterpret`/`LoweredRepr`/`NewtypeRepr` wrapper is never lost.
//! - An entry dies with its scope: [`FactEnv::narrow`] removes entries a
//!   binder shadows and entries whose value mentions a shadowed name, so no
//!   fact survives into a region where inlining it would capture.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use super::specialize_support::free_value_vars;
use super::{TypedBinder, TypedValue, TypedValueKind};

/// The shape a fact asserts about a binder's value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FactKind {
    /// A literal: `Int`, `I64`, `U64`, `Float`, `Bool`, `Unit`, or `Str`.
    Constant,
    /// A must-alias: the binder holds exactly another in-scope name's value.
    Alias,
    /// A constructor application with its field values.
    Constructor,
    /// A tuple, unboxed-tuple, or unboxed-record product with its field
    /// values.
    Product,
}

/// One retained fact: the classified shape and the original stored value.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fact<'a> {
    pub kind: FactKind,
    pub value: &'a TypedValue,
}

/// A scrutinee shape proven by an enclosing match arm, recorded without
/// materializing a constructor value: a `Ctor` value needs its runtime tag,
/// which only the verifier's signatures know, so the refinement instead names
/// the constructor and the arm's field binders. Its consumer collapses a
/// nested case by rebinding those binders, never by substituting a fabricated
/// value into the program.
#[derive(Clone, Debug)]
pub(crate) struct RefinedCtor {
    /// The constructor the scrutinee proved to be.
    pub name: Sym,
    /// The enclosing arm's field binders, where its pattern bound them.
    pub fields: Vec<Option<TypedBinder>>,
}

/// A value looked through any representation-only wrapper: those erase away
/// transparently, so shape recognition must see the represented value.
/// Rewrites keep the original (wrapped) value.
pub(crate) fn peel(mut value: &TypedValue) -> &TypedValue {
    loop {
        match &value.kind {
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::LoweredRepr {
                value: inner,
                proof: _,
            }
            | TypedValueKind::NewtypeRepr { value: inner, .. } => value = inner,
            _ => return value,
        }
    }
}

/// Classify a value's peeled head as a fact shape, or `None` when the value
/// proves nothing worth retaining. A thunk deliberately does not classify:
/// remembering one invites inlining that duplicates work.
pub(crate) fn classify(value: &TypedValue) -> Option<FactKind> {
    match &peel(value).kind {
        TypedValueKind::Ctor { .. } => Some(FactKind::Constructor),
        TypedValueKind::Tuple(_)
        | TypedValueKind::UnboxedTuple(_)
        | TypedValueKind::UnboxedRecord(_) => Some(FactKind::Product),
        TypedValueKind::Var { .. } => Some(FactKind::Alias),
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => Some(FactKind::Constant),
        _ => None,
    }
}

/// A value whose head PROVES what it can and cannot match: a constructor,
/// product, or literal. A bare variable is deliberately not discriminable; its
/// runtime shape is unknown, so pattern mismatch against it is never a proof.
pub(crate) fn discriminable(value: &TypedValue) -> bool {
    matches!(
        classify(value),
        Some(FactKind::Constant | FactKind::Constructor | FactKind::Product)
    )
}

/// The binder-to-fact environment for one scope region.
#[derive(Clone, Debug, Default)]
pub(crate) struct FactEnv {
    entries: BTreeMap<Sym, (FactKind, TypedValue)>,
    refinements: BTreeMap<Sym, RefinedCtor>,
}

impl FactEnv {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record what `name` holds, if the value classifies as a fact. A value
    /// that proves nothing leaves no entry.
    pub(crate) fn bind(&mut self, name: Sym, value: &TypedValue) {
        if let Some(kind) = classify(value) {
            self.entries.insert(name, (kind, value.clone()));
        }
    }

    /// The fact retained for `name`, if any.
    pub(crate) fn fact(&self, name: Sym) -> Option<Fact<'_>> {
        self.entries
            .get(&name)
            .map(|(kind, value)| Fact { kind: *kind, value })
    }

    /// Record that `name` is proven to be the given constructor in this
    /// region.
    pub(crate) fn refine_ctor(&mut self, name: Sym, refined: RefinedCtor) {
        self.refinements.insert(name, refined);
    }

    /// The constructor refinement proven for `name` in this region, if any.
    pub(crate) fn refinement(&self, name: Sym) -> Option<&RefinedCtor> {
        self.refinements.get(&name)
    }

    /// The environment with every entry `binders` invalidates removed: those
    /// whose key a binder shadows, and those whose value (or, for a
    /// refinement, whose recorded field binders) mentions a shadowed name
    /// (inlining which would capture).
    pub(crate) fn narrow(&self, binders: &[Sym]) -> Self {
        if binders.is_empty() {
            return self.clone();
        }
        let shadowed: BTreeSet<Sym> = binders.iter().copied().collect();
        Self {
            entries: self
                .entries
                .iter()
                .filter(|(name, (_, value))| {
                    !shadowed.contains(name) && free_value_vars(value).is_disjoint(&shadowed)
                })
                .map(|(name, entry)| (*name, entry.clone()))
                .collect(),
            refinements: self
                .refinements
                .iter()
                .filter(|(name, refined)| {
                    !shadowed.contains(name)
                        && refined
                            .fields
                            .iter()
                            .flatten()
                            .all(|binder| !shadowed.contains(&binder.name()))
                })
                .map(|(name, refined)| (*name, refined.clone()))
                .collect(),
        }
    }

    /// Resolve a scrutinee to a value whose head shape is known, through at
    /// most one environment hop. A binder aliasing another binder is not
    /// chased here; copy-propagation rewrites the occurrence first.
    pub(crate) fn known_shape(&self, scrutinee: &TypedValue) -> Option<TypedValue> {
        match classify(scrutinee)? {
            FactKind::Constant | FactKind::Constructor | FactKind::Product => {
                Some(scrutinee.clone())
            }
            FactKind::Alias => {
                let TypedValueKind::Var { name, .. } = &peel(scrutinee).kind else {
                    return None;
                };
                match self.fact(*name)? {
                    Fact {
                        kind: FactKind::Alias,
                        ..
                    } => None,
                    Fact { value, .. } => Some(value.clone()),
                }
            }
        }
    }
}
