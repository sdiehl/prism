//! Independent proof checker for witness-carrying Core.
//!
//! This module deliberately does not call inference or unification. Every
//! polymorphic use carries an explicit instantiation; checking substitutes that
//! evidence into a declared scheme and compares the stored witnesses exactly.

use std::fmt;

use prism_common::sym::Sym;

use super::violation::Violation;

mod check;
mod compat;
mod env;
mod instantiate;
mod subst;

#[cfg(test)]
mod tests;

pub use check::TypedCorePhase;
pub use compat::{
    lowered_representation_conversion, representation_preserving, representation_preserving_stable,
    union_rows,
};
pub use env::{ConstructorSig, MonoConstructor, MonoOperation, OperationSig, VerifyEnv};
pub use instantiate::{
    instantiate_constructor, instantiate_fn, instantiate_operation, instantiate_value_scheme,
    scheme_to_fn_sig,
};
pub use subst::{
    rename_bound_core, substitute_core_type, substitute_fn_sig, substitute_label, substitute_row,
    substitute_sig, substitute_type,
};

pub(in crate::core::typed) use check::check_functions;
pub(in crate::core::typed) use compat::row_included;

#[cfg(test)]
use compat::core_subtype;

/// Positions whose failures are classified by name elsewhere in the tree.
///
/// Most sites are written inline where they are checked, because nothing but a
/// sentence depends on them. These are the ones a caller matches on, so they
/// have a single definition rather than a literal per use site.
const SITE_INTEGER_LITERAL: &str = "integer literal";
const SITE_CONSTRUCTOR_FIELD: &str = "constructor field";
const SITE_PRODUCT_FIELD: &str = "product field";
const SITE_RC_SEQUENCE_WITNESS: &str = "RC sequence witness";
const SITE_DUP: &str = "dup";
const SITE_INIT_AT: &str = "init-at";
const SITE_INIT_AT_CELL: &str = "init-at cell";
const SITE_IO_OPERATION: &str = "I/O operation";

/// One failed typed-Core judgment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreViolation {
    function: Sym,
    path: String,
    kind: Violation,
}

impl CoreViolation {
    /// Function containing the invalid node.
    #[must_use]
    pub const fn function(&self) -> Sym {
        self.function
    }

    /// Stable structural path from the function body to the invalid witness.
    #[must_use]
    pub fn path(&self) -> &str {
        &self.path
    }

    /// The named judgment that failed.
    ///
    /// Match on this to classify a failure. The rendered [`Self::message`] is
    /// for people and its wording is not a contract.
    #[must_use]
    pub const fn kind(&self) -> &Violation {
        &self.kind
    }

    /// Human-readable failed judgment.
    #[must_use]
    pub fn message(&self) -> String {
        self.kind.to_string()
    }
}

impl fmt::Display for CoreViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}: {}", self.function, self.path, self.kind)
    }
}

impl std::error::Error for CoreViolation {}

#[cfg(test)]
use prism_syntax::names::{self, ALLOC_OP, IO_EFFECT};

#[cfg(test)]
use super::violation::{
    InstantiationError, QuantifierKind, RcOperandFault, RcSequenceFault, ReuseFault, RowRelation,
    Site, TypeRelation,
};
#[cfg(test)]
use super::{
    ArenaPrepared, BinderErasure, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType,
    EffectLowered, Elaborated, Owned, ReuseLowered, TypedBinder, TypedComp, TypedCompKind,
    TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue, TypedValueKind,
};
#[cfg(test)]
use crate::core::builtins::Builtin;
#[cfg(test)]
use crate::core::IoOp;
#[cfg(test)]
use crate::types::ty::{EffRow, Label};
#[cfg(test)]
use crate::types::Type;
