//! Shared effect-lowering contracts.
//!
//! These are semantic labels and checker facts consumed by the typed lowering
//! pipeline and public reporting APIs. They do not contain an executable
//! lowering implementation.

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};

use prism_common::sym::Sym;
use prism_syntax::ast::Grade;

/// Each effect operation's declared resumption grade, keyed by its symbol.
///
/// An operation absent from the map is conservatively treated as multishot by
/// the typed variable-erasure analysis.
pub type OpGrades = BTreeMap<Sym, Grade>;

/// Effect-lowering tier, ordered from cheapest to most general.
///
/// Declaration order is cost order, so the derived `Ord` is the cost comparison
/// every consumer uses. The same ladder as a table is [`EFFECT_TIERS`], computed
/// from the `next_costlier` chain rather than written out a second time.
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
    /// The cheapest rung, where the cascade starts.
    pub const CHEAPEST: Self = Self::Pure;

    /// The costliest rung, and the only one legal for every program.
    pub const COSTLIEST: Self = Self::WholeProgramFreeMonad;

    /// How many rungs the ladder has, counted along the cost chain.
    pub const COUNT: usize = {
        let mut n = 1;
        let mut tier = Self::CHEAPEST;
        while let Some(next) = tier.next_costlier() {
            tier = next;
            n += 1;
        }
        n
    };

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

    /// Whether the experimental exclusion knob may skip this rung.
    ///
    /// Only a middle engine, one strictly between the ladder's two terminals.
    /// The cheapest ([`CHEAPEST`](Self::CHEAPEST), Pure) is the absence of
    /// lowering: a program with no effects lands there and has no other rung to
    /// be forced onto. The costliest ([`COSTLIEST`](Self::COSTLIEST), the
    /// whole-program free monad) is the only rung legal for every program, so
    /// nothing sits below it to fall to. Excluding either could not be honored,
    /// so the knob refuses to record it rather than accept a silent no-op. The
    /// bounds are read off the ladder's own endpoints, so this cannot drift from
    /// the cost order.
    #[must_use]
    pub const fn is_excludable(self) -> bool {
        (self as u8) > (Self::CHEAPEST as u8) && (self as u8) < (Self::COSTLIEST as u8)
    }

    /// The next rung up the cost ladder, or `None` at the top.
    ///
    /// The single home of the cost order. [`EFFECT_TIERS`] and
    /// [`COUNT`](Self::COUNT) are both walked out of this chain, so a tier cannot
    /// be added without placing it here (the match is exhaustive) and cannot then
    /// be missing from the table.
    const fn next_costlier(self) -> Option<Self> {
        match self {
            Self::Pure => Some(Self::Evidence),
            Self::Evidence => Some(Self::StateFusion),
            Self::StateFusion => Some(Self::LocalPartial),
            Self::LocalPartial => Some(Self::SelectiveFreeMonad),
            Self::SelectiveFreeMonad => Some(Self::WholeProgramFreeMonad),
            Self::WholeProgramFreeMonad => None,
        }
    }

    /// The ladder as an array, cheapest first: walk the chain from the cheapest
    /// rung. A chain longer than [`COUNT`](Self::COUNT) is a compile-time
    /// out-of-bounds index rather than a silently truncated table.
    const fn cost_order() -> [Self; Self::COUNT] {
        let mut tiers = [Self::CHEAPEST; Self::COUNT];
        let mut i = 1;
        while let Some(next) = tiers[i - 1].next_costlier() {
            tiers[i] = next;
            i += 1;
        }
        tiers
    }
}

impl fmt::Display for EffectStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// Lowering tiers in cost order, cheapest first. Derived from the tier ladder's
/// own cost chain, not a second copy of it.
pub const EFFECT_TIERS: [EffectStrategy; EffectStrategy::COUNT] = EffectStrategy::cost_order();

#[cfg(test)]
mod tests {
    use super::{EffectStrategy, EFFECT_TIERS};

    #[test]
    fn tier_table_is_the_enum_in_ascending_cost_order() {
        // The table is walked out of the cost chain, so what is left to pin is
        // that the chain agrees with the derived `Ord` consumers compare with
        // (`DynFlags::admits` ranks a rung against a floor with it). A tier
        // declared out of cost order, or declared and never linked into the
        // chain, moves its discriminant off its table index and fails here.
        assert_eq!(EFFECT_TIERS.len(), EffectStrategy::COUNT);
        assert_eq!(EFFECT_TIERS.first(), Some(&EffectStrategy::CHEAPEST));
        assert_eq!(EFFECT_TIERS.last(), Some(&EffectStrategy::COSTLIEST));
        for (i, tier) in EFFECT_TIERS.iter().enumerate() {
            assert_eq!(*tier as usize, i, "{tier} is declared out of cost order");
            assert!(
                i == 0 || EFFECT_TIERS[i - 1] < *tier,
                "{tier} does not sort above the rung below it"
            );
        }
    }
}
