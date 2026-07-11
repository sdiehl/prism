//! The coeffect row: the compiler's bookkeeping for the surface usage row.
//!
//! `!{...}` is the effect row (what a computation may do, discharged by
//! handlers); `T @ {...}` is the usage row (what the context may do with a
//! value, discharged by boundaries). Internally the structure is named the
//! coeffect row; every user-facing diagnostic says "usage". This module is the
//! single canonical home for the vocabulary: the fact enum, its spellings, and
//! the (axis, polarity, lattice) coordinates each fact carries. Nothing outside
//! this module re-spells a fact name.
//!
//! Rows are sets: parse rejects duplicates and same-axis conflicts, and the
//! canonical order (alphabetical by spelling) is what the formatter prints and
//! what enters a definition's content hash, so `@ {once, portable}` and
//! `@ {portable, once}` can never hash differently.
//!
//! In this release exactly one fact is wired: `noalloc` at the root of a `fn`
//! declaration's return annotation is the allocation certificate (the heir of
//! the retired `without alloc` / `\ alloc` spellings). Every other fact parses
//! and is rejected as reserved, so no package can establish an incompatible
//! meaning before the checker arrives.

use std::fmt;

/// One usage fact. The discriminant order is the canonical (alphabetical)
/// order; keep the variants sorted by spelling.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CoeffectFact {
    Aliased,
    BoundedStack,
    Linear,
    Local,
    Many,
    Noalloc,
    Noescape,
    Once,
    Portable,
    Unique,
}

/// Which independent lattice a fact belongs to.
///
/// Facts from one exclusive axis cannot combine in a single row
/// (`@ {once, many}` is a contradiction); the fip axis is non-exclusive
/// because its facts compose (`linear` plus `bounded_stack` is the strict
/// fip promise).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis {
    Mobility,
    Escape,
    Multiplicity,
    Aliasing,
    Allocation,
    Fip,
}

/// Checking direction.
///
/// A past fact constrains how the value was built: the producer proves it and
/// it flows covariantly with the value. A future fact constrains how the
/// consumer may use it: the consumer promises it and it flows contravariantly.
/// The classification is the variance discipline directly, stated by proof
/// obligation, not by an algebraic comonadic/monadic split.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Polarity {
    Past,
    Future,
}

impl CoeffectFact {
    /// Every fact, in canonical (alphabetical) order.
    pub const ALL: [Self; 10] = [
        Self::Aliased,
        Self::BoundedStack,
        Self::Linear,
        Self::Local,
        Self::Many,
        Self::Noalloc,
        Self::Noescape,
        Self::Once,
        Self::Portable,
        Self::Unique,
    ];

    /// The canonical source spelling.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Aliased => "aliased",
            Self::BoundedStack => "bounded_stack",
            Self::Linear => "linear",
            Self::Local => "local",
            Self::Many => "many",
            Self::Noalloc => "noalloc",
            Self::Noescape => "noescape",
            Self::Once => "once",
            Self::Portable => "portable",
            Self::Unique => "unique",
        }
    }

    /// Parse a usage-position identifier; `None` means an unknown fact (a hard
    /// error at the parse site, never a warning).
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|f| f.name() == s)
    }

    #[must_use]
    pub const fn axis(self) -> Axis {
        match self {
            Self::Portable => Axis::Mobility,
            Self::Local | Self::Noescape => Axis::Escape,
            Self::Once | Self::Many => Axis::Multiplicity,
            Self::Unique | Self::Aliased => Axis::Aliasing,
            Self::Noalloc => Axis::Allocation,
            Self::Linear | Self::BoundedStack => Axis::Fip,
        }
    }

    #[must_use]
    pub const fn polarity(self) -> Polarity {
        match self {
            Self::Portable
            | Self::Noalloc
            | Self::Linear
            | Self::BoundedStack
            | Self::Unique
            | Self::Aliased => Polarity::Past,
            Self::Local | Self::Noescape | Self::Once | Self::Many => Polarity::Future,
        }
    }

    /// Whether two distinct facts on this axis contradict each other. The fip
    /// axis composes; every other multi-fact axis is a choice of one point.
    #[must_use]
    pub const fn axis_is_exclusive(self) -> bool {
        !matches!(self.axis(), Axis::Fip)
    }

    /// Whether the checker behind this fact exists. Everything else parses and
    /// rejects as reserved.
    #[must_use]
    pub const fn is_wired(self) -> bool {
        matches!(
            self,
            Self::Noalloc | Self::Once | Self::Portable | Self::Noescape
        )
    }
}

impl fmt::Display for CoeffectFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A parsed usage row: a set of facts held in canonical (alphabetical) order.
///
/// Construction happens only through [`CoeffectRow::new`], which is where the
/// set discipline (no duplicates, no same-axis contradictions, never empty) is
/// enforced, so a row that exists is canonical by construction.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CoeffectRow {
    facts: Vec<CoeffectFact>,
}

/// Why a written row is not a row. The parse site renders these with the
/// user-facing "usage" vocabulary and its own span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowError {
    Empty,
    Unknown(String),
    Duplicate(CoeffectFact),
    Conflict(CoeffectFact, CoeffectFact),
}

impl fmt::Display for RowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "a usage row cannot be empty"),
            Self::Unknown(s) => write!(f, "unknown usage fact `{s}`"),
            Self::Duplicate(fact) => write!(f, "duplicate usage fact `{fact}`"),
            Self::Conflict(a, b) => write!(
                f,
                "usage facts `{a}` and `{b}` contradict each other (same axis)"
            ),
        }
    }
}

impl CoeffectRow {
    /// Build a row from spellings in source order, enforcing the set
    /// discipline and canonicalizing the order.
    ///
    /// # Errors
    /// Rejects an empty list, an unknown spelling, a duplicate fact, and two
    /// distinct facts on the same exclusive axis.
    pub fn new<S: AsRef<str>>(names: &[S]) -> Result<Self, RowError> {
        if names.is_empty() {
            return Err(RowError::Empty);
        }
        let mut facts: Vec<CoeffectFact> = Vec::with_capacity(names.len());
        for name in names {
            let fact = CoeffectFact::parse(name.as_ref())
                .ok_or_else(|| RowError::Unknown(name.as_ref().to_string()))?;
            if facts.contains(&fact) {
                return Err(RowError::Duplicate(fact));
            }
            if let Some(&prior) = facts
                .iter()
                .find(|p| p.axis() == fact.axis() && fact.axis_is_exclusive())
            {
                return Err(RowError::Conflict(prior, fact));
            }
            facts.push(fact);
        }
        facts.sort_unstable();
        Ok(Self { facts })
    }

    /// The facts in canonical (alphabetical) order.
    #[must_use]
    pub fn facts(&self) -> &[CoeffectFact] {
        &self.facts
    }

    /// Whether this row is exactly the wired allocation certificate.
    #[must_use]
    pub fn is_noalloc_only(&self) -> bool {
        self.facts == [CoeffectFact::Noalloc]
    }

    /// Whether every fact is a multiplicity (`once`/`many`), the usage contract a
    /// closure-typed value may carry: `(T -> U) @ once`. Other axes (mobility,
    /// escape) attach to a value through their own positions, not this one.
    #[must_use]
    pub fn is_multiplicity_only(&self) -> bool {
        self.facts.iter().all(|f| f.axis() == Axis::Multiplicity)
    }

    /// Whether every fact is a closure-usage contract a function-typed value may
    /// carry: a multiplicity (`once`/`many`) or a mobility (`portable`). These are
    /// the axes checked at a closure boundary; `@ {once, portable}` is the mobile
    /// single-use contract `teleport` requires.
    #[must_use]
    pub fn is_closure_contract(&self) -> bool {
        self.facts
            .iter()
            .all(|f| matches!(f.axis(), Axis::Multiplicity | Axis::Mobility))
    }

    /// Whether this row claims `portable` (mobility): the closure may be moved to a
    /// fresh runtime because its captures are all portable.
    #[must_use]
    pub fn is_portable(&self) -> bool {
        self.facts.contains(&CoeffectFact::Portable)
    }

    /// Whether this row is exactly the scoped-token contract `@ noescape`: valid
    /// on a domain of a function type (`(Builder @ noescape) -> a`), promising the
    /// callback does not let that argument outlive the call.
    #[must_use]
    pub fn is_noescape_only(&self) -> bool {
        self.facts == [CoeffectFact::Noescape]
    }

    /// The multiplicity this row claims, if it names one: `once` is stronger than
    /// the default `many`. `None` when the row carries no multiplicity fact.
    #[must_use]
    pub fn multiplicity(&self) -> Option<CoeffectFact> {
        self.facts
            .iter()
            .copied()
            .find(|f| f.axis() == Axis::Multiplicity)
    }

    /// The first fact whose checker does not exist yet, if any: the one to
    /// name in the reserved diagnostic.
    #[must_use]
    pub fn first_unwired(&self) -> Option<CoeffectFact> {
        self.facts.iter().copied().find(|f| !f.is_wired())
    }
}

impl fmt::Display for CoeffectRow {
    /// The canonical surface spelling: `@ fact` for a singleton, spaced
    /// braces `@ {a, b}` otherwise. The formatter prints rows through this.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.as_slice() {
            [one] => write!(f, "@ {one}"),
            many => {
                write!(f, "@ {{")?;
                for (i, fact) in many.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{fact}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Spelling round-trip: the table is its own inverse, and no two facts
    // share a spelling.
    #[test]
    fn names_round_trip() {
        for fact in CoeffectFact::ALL {
            assert_eq!(CoeffectFact::parse(fact.name()), Some(fact));
        }
        assert_eq!(CoeffectFact::parse("nonsense"), None);
    }

    // The variant order is the canonical order the formatter and hash rely on.
    #[test]
    fn canonical_order_is_alphabetical() {
        let names: Vec<_> = CoeffectFact::ALL.iter().map(|f| f.name()).collect();
        let mut sorted = names.clone();
        sorted.sort_unstable();
        assert_eq!(names, sorted);
    }

    #[test]
    fn rows_canonicalize_and_reject() {
        let row = CoeffectRow::new(&["portable", "once"]).unwrap();
        assert_eq!(row.to_string(), "@ {once, portable}");
        let single = CoeffectRow::new(&["noalloc"]).unwrap();
        assert_eq!(single.to_string(), "@ noalloc");
        assert!(single.is_noalloc_only());
        assert_eq!(CoeffectRow::new::<&str>(&[]), Err(RowError::Empty));
        assert!(matches!(
            CoeffectRow::new(&["fast"]),
            Err(RowError::Unknown(_))
        ));
        assert_eq!(
            CoeffectRow::new(&["once", "once"]),
            Err(RowError::Duplicate(CoeffectFact::Once))
        );
        assert_eq!(
            CoeffectRow::new(&["once", "many"]),
            Err(RowError::Conflict(CoeffectFact::Once, CoeffectFact::Many))
        );
        assert_eq!(
            CoeffectRow::new(&["local", "noescape"]),
            Err(RowError::Conflict(
                CoeffectFact::Local,
                CoeffectFact::Noescape
            ))
        );
        // The fip axis composes rather than conflicts.
        let fip = CoeffectRow::new(&["bounded_stack", "linear"]).unwrap();
        assert_eq!(fip.to_string(), "@ {bounded_stack, linear}");
    }
}
