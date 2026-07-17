//! Shared effect-lowering contracts.
//!
//! These are semantic labels and checker facts consumed by the typed lowering
//! pipeline and public reporting APIs. They do not contain an executable
//! lowering implementation.

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::sym::Sym;
use crate::syntax::ast::Grade;

/// Each effect operation's declared resumption grade, keyed by its symbol.
///
/// An operation absent from the map is conservatively treated as multishot by
/// the typed variable-erasure analysis.
pub type OpGrades = BTreeMap<Sym, Grade>;

/// Effect-lowering tier, ordered from cheapest to most general.
#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum EffectStrategy {
    Pure,
    Evidence,
    StateFusion,
    LocalPartial,
    SelectiveFreeMonad,
    WholeProgramFreeMonad,
}

impl EffectStrategy {
    /// Frozen diagnostic and manifest spelling.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Pure => "pure",
            Self::Evidence => "evidence",
            Self::StateFusion => "state-fusion",
            Self::LocalPartial => "local-partial",
            Self::SelectiveFreeMonad => "selective-free-monad",
            Self::WholeProgramFreeMonad => "whole-program-free-monad",
        }
    }
}

impl fmt::Display for EffectStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// Lowering tiers in cost order, cheapest first.
pub const EFFECT_TIERS: [EffectStrategy; 6] = [
    EffectStrategy::Pure,
    EffectStrategy::Evidence,
    EffectStrategy::StateFusion,
    EffectStrategy::LocalPartial,
    EffectStrategy::SelectiveFreeMonad,
    EffectStrategy::WholeProgramFreeMonad,
];
