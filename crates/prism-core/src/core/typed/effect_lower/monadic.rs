//! Typed free-monad translation.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::builtins::Builtin;
use crate::core::cbpv::CoreOp;
use crate::core::effect_abi::{FreeMonadDriver, EBIND};
use crate::types::ty::EffRow;
use crate::types::Type;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;
use prism_syntax::names::ENTRY_POINT;

use super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::verify::{instantiate_fn, lowered_representation_conversion};
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue, TypedValueKind,
};
use super::abi;
use super::analysis::{Effects, MonadicRegionPlan, MonadicScope};
use super::decline::{Decline, Refusal, Site};
use super::evidence::OpIds;
use super::flow::{self, ThunkFlow};
use super::latent::Latent;
use super::plan;
use super::residual::Rows;
use super::union_effects;
use super::walk;

mod recognize;
mod rewrite;
mod selective;

use recognize::{
    answered_thunk, forced_var, function_applied_once_tail, state_clause, state_return,
    FnAnswerLowering, ResumeRepresentation,
};
pub use selective::{lower_region, lower_selective, lower_whole};

/// What a binder displaced when it entered scope, restored when it leaves.
struct Shadowed {
    name: Sym,
    local: Option<CoreType>,
    word: Option<CoreType>,
    resume: bool,
    signature: Option<flow::Sig>,
}

/// The confined-region facts a selective lowering consults: which declarations
/// share the free-monad convention, what each function can still perform, and
/// which suspended computations the region owns.
#[derive(Debug)]
pub struct Region<'a> {
    pub plan: &'a MonadicRegionPlan,
    pub latent: &'a Latent,
    pub flow: &'a ThunkFlow,
    pub native_enabled: bool,
}

/// Translate computations into the row-indexed effect runtime while retaining
/// the source type of every value stored in its existential word slots.
#[derive(Debug)]
pub struct Monadic<'a> {
    ops: &'a OpIds,
    fresh: &'a mut Fresh,
    row: EffRow,
    /// The row the monadic convention uses for a computation this declaration
    /// suspends. Equal to `row` wherever the declaration is itself monadic;
    /// outside a confined region it is the declaration's residual row instead,
    /// because a thunk the region owns performs what its own body performs and
    /// not what the declaration building it performs, while `row` has to stay
    /// the source row so the direct rewrite around it is left alone.
    suspension_row: EffRow,
    calls: &'a BTreeMap<Sym, CoreFnSig>,
    generated: Vec<TypedCoreFn>,
    generated_signatures: BTreeMap<Sym, CoreFnSig>,
    quantifiers: Vec<CoreQuantifier>,
    locals: BTreeMap<Sym, CoreType>,
    /// What forcing each thunk-valued binder in lexical scope can still
    /// perform, threaded beside `locals` because the convention a thunk was
    /// built at is not recoverable from its type: a monadic thunk and a direct
    /// one share the shape `Thunk(_)`, so the rewrite has to remember.
    thunk_sigs: flow::Loc,
    word_binders: BTreeMap<Sym, CoreType>,
    resume_aliases: BTreeSet<Sym>,
    resume_representation: ResumeRepresentation,
    region_plan: Option<&'a MonadicRegionPlan>,
    /// Why a confined attempt was refused, if one was. Carried rather than
    /// discarded so the plan artifact and the fallback warning can say why the
    /// program is paying for the wider region.
    refusal: Option<(Refusal, Site)>,
    latent: Option<&'a Latent>,
    flow: Option<&'a ThunkFlow>,
    native_enabled: bool,
}

#[cfg(test)]
mod tests;
