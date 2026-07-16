//! Effect-label discharge for the typed erasures.
//!
//! An erased handler was the proof that its private effect never escaped its
//! region, so every sig in the rewritten region has that one label subtracted
//! from its row. Rows are unions of leaf rows, so uniform label removal is
//! exactly the recomputation; the rewrite also reaches rows nested inside
//! witness types (thunk and closure signatures) and row instantiation
//! arguments. Source-level types are the checker's own and carry the private
//! label only through row-polymorphic instantiation, which the instantiation
//! hook discharges.

use crate::sym::Sym;
use crate::types::ty::EffRow;

use super::super::specialize_support::Rewrite;
use super::super::{CompSig, CoreFnSig, CoreInstantiation, CoreType, LoweredType};

pub(super) fn subtract_row(row: &EffRow, label: Sym) -> EffRow {
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|l| l.name != label)
            .cloned(),
        row.tail().clone(),
    )
}

/// Discharge one private effect label from every sig in a region, leaving the
/// term structure untouched. Erasure rewrites that also replace nodes (the
/// var-to-cell pass) layer their node cases on top of these hooks.
pub(super) struct SubtractEffect {
    pub(super) label: Sym,
}

impl SubtractEffect {
    pub(super) fn sig(&mut self, sig: &CompSig) -> CompSig {
        CompSig::new(
            self.ty(sig.result()),
            subtract_row(sig.effects(), self.label),
        )
    }

    pub(super) fn ty(&mut self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.sig(sig))),
            CoreType::Function(signature) => CoreType::Function(Box::new(CoreFnSig::new(
                signature.quantifiers().to_vec(),
                signature.params().iter().map(|p| self.ty(p)).collect(),
                self.sig(signature.body()),
            ))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.ty(inner))),
            CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(self.ty(inner))),
            CoreType::Source(_) | CoreType::Lowered(LoweredType::Word) => ty.clone(),
            CoreType::Lowered(kind) => CoreType::Lowered(match kind {
                LoweredType::Eff(row) => LoweredType::Eff(subtract_row(row, self.label)),
                LoweredType::Queue(row) => LoweredType::Queue(subtract_row(row, self.label)),
                LoweredType::QueueView(row) => {
                    LoweredType::QueueView(subtract_row(row, self.label))
                }
                LoweredType::Word => unreachable!("word handled above"),
            }),
        }
    }
}

impl Rewrite for SubtractEffect {
    type Ctx = ();

    fn fn_sig(&mut self, sig: &CoreFnSig, (): &()) -> CoreFnSig {
        CoreFnSig::new(
            sig.quantifiers().to_vec(),
            sig.params().iter().map(|param| self.ty(param)).collect(),
            self.sig(sig.body()),
        )
    }

    fn comp_sig(&mut self, sig: &CompSig, (): &()) -> CompSig {
        self.sig(sig)
    }

    fn core_type(&mut self, ty: &CoreType, (): &()) -> CoreType {
        self.ty(ty)
    }

    fn instantiation(&mut self, instantiation: &CoreInstantiation, (): &()) -> CoreInstantiation {
        match instantiation {
            CoreInstantiation::Row(row) => CoreInstantiation::Row(subtract_row(row, self.label)),
            CoreInstantiation::Type(_) => instantiation.clone(),
        }
    }
}
