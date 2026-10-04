//! Operation numbering.
//!
//! Every effect operation in a program gets a stable integer id, so the tag a
//! reified operation carries, the order a fused label lists its operations in,
//! and the order a trap reports them in agree across compilations and across
//! machines. The numbering is alphabetical by operation name rather than by
//! intern order, because intern order is a property of how the front end
//! happened to walk the source and is not a content address.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

/// The effect ops of a program, numbered alphabetically by name so operation
/// tags and trap order are stable across compilations.
#[derive(Debug)]
pub struct OpIds {
    ids: BTreeMap<Sym, i64>,
    /// [`op`](Self::op)'s inverse table: ids are dense positions in the sorted
    /// name order, so the name an id numbers is a direct index.
    names: Vec<Sym>,
}

impl OpIds {
    /// Assign every op an id. `None` when a program declares more ops than an
    /// `i64` can number.
    #[must_use]
    pub fn assign(ops: &BTreeSet<Sym>) -> Option<Self> {
        let mut names: Vec<Sym> = ops.iter().copied().collect();
        names.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        let ids = names
            .iter()
            .enumerate()
            .map(|(i, name)| i64::try_from(i).ok().map(|id| (*name, id)))
            .collect::<Option<BTreeMap<_, _>>>()?;
        Some(Self { ids, names })
    }

    #[must_use]
    pub fn id(&self, op: Sym) -> Option<i64> {
        self.ids.get(&op).copied()
    }

    /// The inverse of [`id`](Self::id).
    #[must_use]
    pub fn op(&self, id: i64) -> Option<Sym> {
        usize::try_from(id)
            .ok()
            .and_then(|i| self.names.get(i))
            .copied()
    }

    #[must_use]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (Sym, i64)> + '_ {
        self.ids.iter().map(|(name, id)| (*name, *id))
    }

    /// Map a set of ops to their ids in ascending order. Every list keyed by
    /// operation uses this one ordering, so a producer and its consumer agree
    /// positionally without having to compare names.
    pub fn ids_of<'a>(&self, ops: impl IntoIterator<Item = &'a Sym>) -> Option<Vec<i64>> {
        let mut v: Vec<i64> = ops
            .into_iter()
            .map(|op| self.id(*op))
            .collect::<Option<_>>()?;
        v.sort_unstable();
        v.dedup();
        Some(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    // Ids are alphabetical by name, not by intern order, so operation tags and
    // trap order stay stable however the program interned its symbols.
    #[test]
    fn op_ids_are_alphabetical_not_intern_order() {
        // Intern in reverse order, so intern ids disagree with names.
        let zulu = sym("zulu");
        let alpha = sym("alpha");
        let ops: BTreeSet<Sym> = [zulu, alpha].into_iter().collect();
        let ids = OpIds::assign(&ops).expect("ids assign");
        assert_eq!(ids.id(alpha), Some(0));
        assert_eq!(ids.id(zulu), Some(1));
    }

    // Operation-keyed lists line up positionally everywhere, so a set of ops
    // always maps to ascending ids with duplicates collapsed.
    #[test]
    fn op_order_is_ascending_and_deduplicated() {
        let ops: BTreeSet<Sym> = [sym("b"), sym("a"), sym("c")].into_iter().collect();
        let ids = OpIds::assign(&ops).expect("ids assign");
        let wanted = [sym("c"), sym("a"), sym("c")];
        assert_eq!(ids.ids_of(wanted.iter()), Some(vec![0, 2]));
    }
}
