use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use crate::core::builtins::Builtin;
use crate::types::ty::Label;

use super::super::{CoreFnSig, CoreQuantifier, CoreType};

/// The declared shape of a data constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorSig {
    pub(super) quantifiers: Vec<CoreQuantifier>,
    pub(super) tag: usize,
    pub(super) fields: Vec<CoreType>,
    pub(super) result: CoreType,
}

impl ConstructorSig {
    #[must_use]
    pub const fn new(
        quantifiers: Vec<CoreQuantifier>,
        tag: usize,
        fields: Vec<CoreType>,
        result: CoreType,
    ) -> Self {
        Self {
            quantifiers,
            tag,
            fields,
            result,
        }
    }

    #[must_use]
    pub fn quantifiers(&self) -> &[CoreQuantifier] {
        &self.quantifiers
    }
}

/// The declared signature and owning effect of an operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationSig {
    pub(super) quantifiers: Vec<CoreQuantifier>,
    pub(super) params: Vec<CoreType>,
    pub(super) result: CoreType,
    pub(super) effect: Label,
}

impl OperationSig {
    #[must_use]
    pub const fn new(
        quantifiers: Vec<CoreQuantifier>,
        params: Vec<CoreType>,
        result: CoreType,
        effect: Label,
    ) -> Self {
        Self {
            quantifiers,
            params,
            result,
            effect,
        }
    }

    #[must_use]
    pub fn quantifiers(&self) -> &[CoreQuantifier] {
        &self.quantifiers
    }

    #[must_use]
    pub fn params(&self) -> &[CoreType] {
        &self.params
    }

    #[must_use]
    pub const fn result(&self) -> &CoreType {
        &self.result
    }

    #[must_use]
    pub const fn effect(&self) -> &Label {
        &self.effect
    }
}

/// Declarations needed to check Core nodes independently of the producer.
#[derive(Clone, Debug, Default)]
pub struct VerifyEnv {
    pub(super) constructors: BTreeMap<Sym, ConstructorSig>,
    pub(super) newtype_constructors: BTreeSet<Sym>,
    pub(super) boxed_nominals: BTreeSet<Sym>,
    pub(super) operations: BTreeMap<Sym, OperationSig>,
    pub(super) builtin_overrides: BTreeMap<u64, CoreFnSig>,
}

impl VerifyEnv {
    /// An empty environment, suitable for Core containing only functions and
    /// intrinsic nodes.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            constructors: BTreeMap::new(),
            newtype_constructors: BTreeSet::new(),
            boxed_nominals: BTreeSet::new(),
            operations: BTreeMap::new(),
            builtin_overrides: BTreeMap::new(),
        }
    }

    pub fn insert_constructor(&mut self, name: Sym, sig: ConstructorSig) {
        self.constructors.insert(name, sig);
    }

    pub fn mark_newtype_constructor(&mut self, name: Sym) {
        self.newtype_constructors.insert(name);
    }

    /// Record declaration evidence that nominal type `name` is an allocated,
    /// non-zero runtime cell (it survives mandatory representation passes with
    /// its wrapper intact).
    pub fn mark_boxed_nominal(&mut self, name: Sym) {
        self.boxed_nominals.insert(name);
    }

    /// Whether declaration evidence marks nominal type `name` as an allocated
    /// cell. `false` means no evidence, not a proof of transparency.
    #[must_use]
    pub fn nominal_is_boxed(&self, name: Sym) -> bool {
        self.boxed_nominals.contains(&name)
    }

    pub fn insert_operation(&mut self, name: Sym, sig: OperationSig) {
        self.operations.insert(name, sig);
    }

    pub fn insert_builtin_override(&mut self, op: Builtin, sig: CoreFnSig) {
        self.builtin_overrides.insert(op.wire(), sig);
    }

    #[must_use]
    pub fn constructor(&self, name: Sym) -> Option<&ConstructorSig> {
        self.constructors.get(&name)
    }

    #[must_use]
    pub fn operation(&self, name: Sym) -> Option<&OperationSig> {
        self.operations.get(&name)
    }

    #[must_use]
    pub const fn operations(&self) -> &BTreeMap<Sym, OperationSig> {
        &self.operations
    }

    #[must_use]
    pub fn builtin_override(&self, op: Builtin) -> Option<&CoreFnSig> {
        self.builtin_overrides.get(&op.wire())
    }
}

#[derive(Clone, Debug)]
pub struct MonoConstructor {
    pub tag: usize,
    pub fields: Vec<CoreType>,
    pub result: CoreType,
}

#[derive(Clone, Debug)]
pub struct MonoOperation {
    pub params: Vec<CoreType>,
    pub result: CoreType,
    pub effect: Label,
}
