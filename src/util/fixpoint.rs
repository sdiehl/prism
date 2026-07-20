//! A least-fixpoint over a finite map-of-sets lattice.
//!
//! Each round recomputes, per key, `next[k] = current[k] | step(k, current)`:
//! a union, never a replace, so every value only grows. Because the lattice is
//! finite and each round is monotone, the measure "elements not yet added"
//! strictly decreases on every non-stationary round, so the iteration reaches
//! its least fixpoint and stops. Termination is structural: no iteration cap and
//! no non-monotonicity backstop are meaningful here.

use std::collections::{BTreeMap, BTreeSet};

/// Solve `x = seed ⊔ step(x)` for the least `x`.
///
/// Each value is a set and `⊔` is per-key union. `step(k, current)` returns the
/// contribution for key `k` given the current assignment; it must be monotone in
/// `current` (a larger input never yields a smaller output), which set-union
/// accumulation always is. The key set is fixed to `seed`'s keys.
#[must_use]
pub(crate) fn least_fixpoint<K, T>(
    seed: BTreeMap<K, BTreeSet<T>>,
    step: impl Fn(&K, &BTreeMap<K, BTreeSet<T>>) -> BTreeSet<T>,
) -> BTreeMap<K, BTreeSet<T>>
where
    K: Ord + Clone,
    T: Ord + Clone,
{
    let mut current = seed;
    let keys: Vec<K> = current.keys().cloned().collect();
    loop {
        let mut changed = false;
        let mut next = current.clone();
        for k in &keys {
            let add = step(k, &current);
            // `next` is a clone of `current` and `k` came from its keys, so the
            // slot is always present.
            if let Some(slot) = next.get_mut(k) {
                let before = slot.len();
                slot.extend(add);
                changed |= slot.len() != before;
            }
        }
        current = next;
        if !changed {
            return current;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Latent-set propagation over a call graph: each node's set is its own ops
    // plus everything latent in the nodes it calls. Exercises the cases a cap
    // would have masked: a self-loop and a mutual-recursion cycle.
    fn solve(
        calls: &BTreeMap<&'static str, Vec<&'static str>>,
        own: &BTreeMap<&'static str, BTreeSet<&'static str>>,
    ) -> BTreeMap<&'static str, BTreeSet<&'static str>> {
        let seed = calls.keys().map(|k| (*k, BTreeSet::new())).collect();
        least_fixpoint(seed, |k, cur| {
            let mut s = own.get(k).cloned().unwrap_or_default();
            for callee in &calls[k] {
                s.extend(cur[callee].iter().copied());
            }
            s
        })
    }

    #[test]
    fn cycles_and_self_loops_converge() {
        let calls = BTreeMap::from([
            ("f", vec!["f"]), // self-loop
            ("g", vec!["h"]), // mutual recursion g <-> h
            ("h", vec!["g"]),
            ("a", vec!["b"]), // a -> b -> c chain
            ("b", vec!["c"]),
            ("c", vec![]),
        ]);
        let own = BTreeMap::from([
            ("f", BTreeSet::from(["A"])),
            ("g", BTreeSet::from(["B"])),
            ("h", BTreeSet::from(["C"])),
            ("c", BTreeSet::from(["D"])),
        ]);
        let r = solve(&calls, &own);
        assert_eq!(r["f"], BTreeSet::from(["A"]));
        assert_eq!(r["g"], BTreeSet::from(["B", "C"]));
        assert_eq!(r["h"], BTreeSet::from(["B", "C"]));
        assert_eq!(r["a"], BTreeSet::from(["D"]));
        assert_eq!(r["b"], BTreeSet::from(["D"]));
        assert_eq!(r["c"], BTreeSet::from(["D"]));
    }
}
