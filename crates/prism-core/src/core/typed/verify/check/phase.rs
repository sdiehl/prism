//! Phase vocabulary and well-formedness checks for typed Core witnesses.

use std::collections::BTreeSet;

use crate::types::ty::EffRow;
use crate::types::Type;

use super::super::super::violation::{QuantifierKind, Site, Violation};
use super::super::super::{
    ArenaPrepared, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, EffectLowered,
    Elaborated, LoweredType, Owned, ReuseLowered,
};
use super::Checker;

mod sealed {
    pub trait Sealed {}
}

/// A typed-Core stage with a fixed legal node vocabulary.
pub trait TypedCorePhase: sealed::Sealed {
    #[doc(hidden)]
    const ALLOW_EFFECT_NODES: bool;
    #[doc(hidden)]
    const ALLOW_INIT_AT_NODES: bool;
    #[doc(hidden)]
    const ALLOW_REF_NODES: bool;
    #[doc(hidden)]
    const ALLOW_RC_NODES: bool;
    #[doc(hidden)]
    const ALLOW_REUSE_NODES: bool;
    #[doc(hidden)]
    const ALLOW_LOWERED_ABI: bool;
    #[doc(hidden)]
    const NAME: &'static str;
}

macro_rules! phase {
    ($phase:ty, $name:literal, $effect:literal, $init_at:literal, $refs:literal, $rc:literal, $reuse:literal, $lowered:literal) => {
        impl sealed::Sealed for $phase {}
        impl TypedCorePhase for $phase {
            const ALLOW_EFFECT_NODES: bool = $effect;
            const ALLOW_INIT_AT_NODES: bool = $init_at;
            const ALLOW_REF_NODES: bool = $refs;
            const ALLOW_RC_NODES: bool = $rc;
            const ALLOW_REUSE_NODES: bool = $reuse;
            const ALLOW_LOWERED_ABI: bool = $lowered;
            const NAME: &'static str = $name;
        }
    };
}

phase!(
    Elaborated,
    "elaborated",
    true,
    false,
    false,
    false,
    false,
    false
);
phase!(
    ArenaPrepared,
    "arena-prepared",
    true,
    true,
    false,
    false,
    false,
    false
);
phase!(
    EffectLowered,
    "effect-lowered",
    false,
    true,
    true,
    false,
    false,
    true
);
phase!(Owned, "owned", false, true, true, true, false, true);
phase!(
    ReuseLowered,
    "reuse-lowered",
    false,
    true,
    true,
    true,
    true,
    true
);

impl<P: TypedCorePhase> Checker<'_, P> {
    pub(super) fn check_instantiation(&mut self, arguments: &[CoreInstantiation]) {
        for argument in arguments {
            match argument {
                CoreInstantiation::Type(ty) => self.check_source_type(ty),
                CoreInstantiation::Row(row) => self.check_row(row),
            }
        }
    }

    pub(super) fn check_fn_sig(&mut self, signature: &CoreFnSig) {
        for parameter in signature.params() {
            self.check_core_type(parameter);
        }
        self.check_sig(signature.body());
    }

    pub(super) fn check_sig(&mut self, signature: &CompSig) {
        self.check_core_type(signature.result());
        self.check_row(signature.effects());
    }

    pub(super) fn check_core_type(&mut self, ty: &CoreType) {
        match ty {
            CoreType::Source(ty) => self.check_source_type(ty),
            CoreType::Thunk(signature) => self.check_sig(signature),
            CoreType::Function(signature) => {
                let old_types = self.allowed_types.clone();
                let old_rows = self.allowed_rows.clone();
                let mut local_types = BTreeSet::new();
                let mut local_rows = BTreeSet::new();
                for quantifier in signature.quantifiers() {
                    match quantifier {
                        CoreQuantifier::Type(name) => {
                            if local_rows.contains(name) || !local_types.insert(*name) {
                                self.fail(Violation::DuplicateQuantifier {
                                    kind: QuantifierKind::Type,
                                    nested: true,
                                    name: *name,
                                });
                            }
                            self.allowed_types.insert(*name);
                        }
                        CoreQuantifier::Row(name) => {
                            if local_types.contains(name) || !local_rows.insert(*name) {
                                self.fail(Violation::DuplicateQuantifier {
                                    kind: QuantifierKind::Row,
                                    nested: true,
                                    name: *name,
                                });
                            }
                            self.allowed_rows.insert(*name);
                        }
                    }
                }
                self.check_fn_sig(signature);
                self.allowed_types = old_types;
                self.allowed_rows = old_rows;
            }
            CoreType::Ref(inner) | CoreType::ReuseToken(inner) => self.check_core_type(inner),
            CoreType::Lowered(kind) => {
                if !P::ALLOW_LOWERED_ABI {
                    self.fail(Violation::LoweredAbiIllegal {
                        phase: P::NAME,
                        found: kind.clone(),
                    });
                }
                match kind {
                    LoweredType::Word => {}
                    LoweredType::Eff(row)
                    | LoweredType::Queue(row)
                    | LoweredType::QueueView(row) => self.check_row(row),
                }
            }
        }
    }

    pub(super) fn check_source_type(&mut self, ty: &Type) {
        let mut existentials = BTreeSet::new();
        ty.free_exist(&mut existentials);
        if !existentials.is_empty() {
            self.fail(Violation::UnsolvedMeta {
                kind: QuantifierKind::Type,
                ty: ty.clone(),
            });
        }
        let mut row_existentials = BTreeSet::new();
        ty.free_exist_row(&mut row_existentials);
        if !row_existentials.is_empty() {
            self.fail(Violation::UnsolvedMeta {
                kind: QuantifierKind::Row,
                ty: ty.clone(),
            });
        }
        let mut type_variables = BTreeSet::new();
        ty.free_ty_vars(&mut type_variables);
        let unbound_types: Vec<_> = type_variables
            .difference(&self.allowed_types)
            .copied()
            .collect();
        for name in unbound_types {
            self.fail(Violation::UnboundRigid {
                kind: QuantifierKind::Type,
                name,
                ty: ty.clone(),
            });
        }
        let mut row_variables = BTreeSet::new();
        ty.free_row_vars(&mut row_variables);
        let unbound_rows: Vec<_> = row_variables
            .difference(&self.allowed_rows)
            .copied()
            .collect();
        for name in unbound_rows {
            self.fail(Violation::UnboundRigid {
                kind: QuantifierKind::Row,
                name,
                ty: ty.clone(),
            });
        }
        check_type_rows(ty, &mut |row| self.check_row(row));
    }

    pub(super) fn check_row(&mut self, row: &EffRow) {
        if !row.is_canonical() {
            self.fail(Violation::RowNotCanonical { row: row.clone() });
        }
        let mut exists = BTreeSet::new();
        row.free_exist_row(&mut exists);
        if !exists.is_empty() {
            self.fail(Violation::UnsolvedRowMeta { row: row.clone() });
        }
        if let EffRow::Var(name) = row.tail() {
            if !self.allowed_rows.contains(name) {
                self.fail(Violation::UnboundRigidRow { name: *name });
            }
        }
        for label in row.labels() {
            for argument in &label.args {
                self.check_source_type(argument);
            }
        }
    }

    pub(super) fn require_effect_node(&mut self, node: &'static str) {
        if !P::ALLOW_EFFECT_NODES {
            self.fail(Violation::PhaseIllegal {
                what: Site::At(node),
                phase: P::NAME,
            });
        }
    }

    pub(super) fn require_init_at_node(&mut self, node: &'static str) {
        if !P::ALLOW_INIT_AT_NODES {
            self.fail(Violation::PhaseIllegal {
                what: Site::At(node),
                phase: P::NAME,
            });
        }
    }

    pub(super) fn require_ref_node(&mut self, node: &'static str) {
        if !P::ALLOW_REF_NODES {
            self.fail(Violation::PhaseIllegal {
                what: Site::At(node),
                phase: P::NAME,
            });
        }
    }

    pub(super) fn require_rc_node(&mut self, node: &'static str) {
        if !P::ALLOW_RC_NODES {
            self.fail(Violation::PhaseIllegal {
                what: Site::At(node),
                phase: P::NAME,
            });
        }
    }

    pub(super) fn require_reuse_node(&mut self, node: &'static str) {
        if !P::ALLOW_REUSE_NODES {
            self.fail(Violation::PhaseIllegal {
                what: Site::At(node),
                phase: P::NAME,
            });
        }
    }
}

fn check_type_rows(ty: &Type, f: &mut impl FnMut(&EffRow)) {
    match ty {
        Type::Forall(_, body)
        | Type::RowForall(_, body)
        | Type::OrNull(body)
        | Type::Coeffect(body, _) => check_type_rows(body, f),
        Type::Fun(params, row, result) => {
            for ty in params {
                check_type_rows(ty, f);
            }
            f(row);
            check_type_rows(result, f);
        }
        Type::Con(_, arguments) | Type::Tuple(arguments) | Type::UnboxedTuple(arguments) => {
            for ty in arguments {
                check_type_rows(ty, f);
            }
        }
        Type::UnboxedRecord(fields) => {
            for (_, ty) in fields {
                check_type_rows(ty, f);
            }
        }
        Type::App(head, argument) => {
            check_type_rows(head, f);
            check_type_rows(argument, f);
        }
        Type::Row(row) => f(row),
        Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str
        | Type::Var(_)
        | Type::Exist(_)
        | Type::Nat(_) => {}
    }
}
