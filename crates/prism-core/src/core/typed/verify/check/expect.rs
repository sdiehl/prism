//! Expected-type, signature, instantiation, and row-join checks.

use crate::types::ty::EffRow;
use crate::types::Type;

use super::super::super::violation::{
    InstantiationSubject, RowRelation, Site, TypeRelation, Violation,
};
use super::super::super::{CompSig, CoreFnSig, CoreInstantiation, CoreType};
use super::super::compat::{core_subtype, row_included, union_rows as canonical_union_rows};
use super::super::env::{ConstructorSig, OperationSig};
use super::super::instantiate::{
    instantiate_constructor as instantiate_constructor_sig, instantiate_fn as instantiate_fn_sig,
    instantiate_operation as instantiate_operation_sig, scheme_to_fn_sig, MonoConstructor,
    MonoOperation,
};
use super::phase::TypedCorePhase;
use super::Checker;

impl<P: TypedCorePhase> Checker<'_, P> {
    pub(super) fn registry_signature(
        &mut self,
        text: &str,
        context: impl Into<Site>,
    ) -> Option<CoreFnSig> {
        let context = context.into();
        match crate::types::sig::parse_checked_signature("typed-core verifier", text) {
            Ok(ty) => match scheme_to_fn_sig(ty) {
                Ok(signature) => Some(signature),
                Err(error) => {
                    self.fail(Violation::CanonicalSignature {
                        site: context,
                        error,
                    });
                    None
                }
            },
            Err(error) => {
                self.fail(Violation::CanonicalSignatureParse {
                    site: context,
                    error: error.to_string(),
                });
                None
            }
        }
    }

    pub(super) fn instantiate_fn(
        &mut self,
        signature: &CoreFnSig,
        arguments: &[CoreInstantiation],
        context: impl Into<Site>,
    ) -> Option<CoreFnSig> {
        let context = context.into();
        self.check_instantiation(arguments);
        match instantiate_fn_sig(signature, arguments) {
            Ok(signature) => Some(signature),
            Err(error) => {
                self.fail(Violation::Instantiation {
                    subject: InstantiationSubject::At(context),
                    error,
                });
                None
            }
        }
    }

    pub(super) fn instantiate_constructor(
        &mut self,
        signature: &ConstructorSig,
        arguments: &[CoreInstantiation],
    ) -> Option<MonoConstructor> {
        self.check_instantiation(arguments);
        match instantiate_constructor_sig(signature, arguments) {
            Ok(signature) => Some(signature),
            Err(error) => {
                self.fail(Violation::Instantiation {
                    subject: InstantiationSubject::At(Site::At("constructor")),
                    error,
                });
                None
            }
        }
    }

    pub(super) fn instantiate_operation(
        &mut self,
        signature: &OperationSig,
        arguments: &[CoreInstantiation],
    ) -> Option<MonoOperation> {
        self.check_instantiation(arguments);
        match instantiate_operation_sig(signature, arguments) {
            Ok(signature) => Some(signature),
            Err(error) => {
                self.fail(Violation::Instantiation {
                    subject: InstantiationSubject::At(Site::At("operation")),
                    error,
                });
                None
            }
        }
    }

    pub(super) fn expect_source(
        &mut self,
        actual: &CoreType,
        expected: &Type,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        self.expect_type(actual, &CoreType::Source(expected.clone()), context);
    }

    pub(super) fn expect_type(
        &mut self,
        actual: &CoreType,
        expected: &CoreType,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        if actual != expected {
            self.fail(Violation::TypeMismatch {
                site: context,
                relation: TypeRelation::Equal,
                actual: actual.clone(),
                expected: expected.clone(),
            });
        }
    }

    pub(super) fn expect_subtype_type(
        &mut self,
        actual: &CoreType,
        expected: &CoreType,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        if !core_subtype(actual, expected) {
            self.fail(Violation::TypeMismatch {
                site: context,
                relation: TypeRelation::Subtype,
                actual: actual.clone(),
                expected: expected.clone(),
            });
        }
    }

    pub(super) fn expect_row(
        &mut self,
        actual: &EffRow,
        expected: &EffRow,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        if actual != expected {
            self.fail(Violation::RowMismatch {
                site: context,
                relation: RowRelation::Equal,
                actual: actual.clone(),
                expected: expected.clone(),
            });
        }
    }

    pub(super) fn expect_sig(
        &mut self,
        actual: &CompSig,
        expected: &CompSig,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        self.expect_type(actual.result(), expected.result(), context);
        self.expect_row(actual.effects(), expected.effects(), context);
    }

    pub(super) fn expect_subtype_sig(
        &mut self,
        actual: &CompSig,
        expected: &CompSig,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        self.expect_subtype_type(actual.result(), expected.result(), context);
        if !row_included(actual.effects(), expected.effects()) {
            self.fail(Violation::RowMismatch {
                site: context,
                relation: RowRelation::Subrow,
                actual: actual.effects().clone(),
                expected: expected.effects().clone(),
            });
        }
    }

    /// The Bind discipline for a node whose signature is derived from a
    /// subcomputation it observes: the stored result may refine the derived
    /// result, but the stored row must include every derived effect. A node
    /// never sheds effects it observes (forcing Thunk(Int ! {IO}) cannot be
    /// labelled Int ! {}).
    pub(super) fn expect_supertype_sig(
        &mut self,
        actual: &CompSig,
        derived: &CompSig,
        context: impl Into<Site>,
    ) {
        let context = context.into();
        self.expect_subtype_type(actual.result(), derived.result(), context);
        if !row_included(derived.effects(), actual.effects()) {
            self.fail(Violation::RowMismatch {
                site: context,
                relation: RowRelation::Includes,
                actual: actual.effects().clone(),
                expected: derived.effects().clone(),
            });
        }
    }

    pub(super) fn union_rows(
        &mut self,
        left: &EffRow,
        right: &EffRow,
        context: impl Into<Site>,
    ) -> Option<EffRow> {
        let context = context.into();
        match canonical_union_rows(left, right) {
            Ok(row) => Some(row),
            Err(error) => {
                self.fail(Violation::RowUnion {
                    site: context,
                    error,
                });
                None
            }
        }
    }
}
