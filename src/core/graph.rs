//! The dependency graph over elaborated Core, and the reachability queries that
//! make the codebase queryable by structure rather than by grep.
//!
//! An edge `a -> b` means `a`'s body calls or captures the top-level definition
//! `b`; this is the same adjacency the content hasher walks for its Merkle
//! substitution (`hash.rs::sccs`), surfaced here so `prism query` can answer "who
//! calls this," "what breaks if I change this" (the transitive dependent
//! closure), and "what does this transitively depend on."

use std::collections::{BTreeMap, BTreeSet};

use super::cbpv::{self, Core};
use super::fv;
use crate::sym::Sym;

/// Forward and reverse direct-dependency adjacency over a program's top-level
/// definitions.
///
/// Builtins and constructors are not nodes (they are leaves of the Merkle DAG),
/// so an edge exists only between two definitions in `core.fns`.
#[derive(Debug)]
pub struct DepGraph {
    fwd: BTreeMap<Sym, BTreeSet<Sym>>,
    rev: BTreeMap<Sym, BTreeSet<Sym>>,
}

impl DepGraph {
    /// Build the graph from elaborated Core. A definition depends on another when
    /// its body names it as a call head or captures it as a free variable; a
    /// self-reference (recursion) is not an edge, so a function is never its own
    /// caller or dependency.
    #[must_use]
    pub fn of(core: &Core) -> Self {
        let nodes: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
        let mut fwd: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
        let mut rev: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
        for f in &core.fns {
            let mut deps = BTreeSet::new();
            let mut calls = Vec::new();
            cbpv::calls_in(&f.body, &mut calls);
            for c in calls {
                if c != f.name && nodes.contains(&c) {
                    deps.insert(c);
                }
            }
            for v in fv::comp(&f.body) {
                if v != f.name && nodes.contains(&v) {
                    deps.insert(v);
                }
            }
            for d in &deps {
                rev.entry(*d).or_default().insert(f.name);
            }
            rev.entry(f.name).or_default();
            fwd.insert(f.name, deps);
        }
        Self { fwd, rev }
    }

    /// Whether `s` is a definition in the graph.
    #[must_use]
    pub fn contains(&self, s: Sym) -> bool {
        self.fwd.contains_key(&s)
    }

    /// The direct dependencies of `s` (the Merkle children): definitions its body
    /// calls or captures.
    #[must_use]
    pub fn direct_deps(&self, s: Sym) -> BTreeSet<Sym> {
        self.fwd.get(&s).cloned().unwrap_or_default()
    }

    /// The direct callers of `s`: definitions whose body names `s`.
    #[must_use]
    pub fn direct_callers(&self, s: Sym) -> BTreeSet<Sym> {
        self.rev.get(&s).cloned().unwrap_or_default()
    }

    /// Everything that transitively depends on `s`: the exact set a change to `s`
    /// would force to re-hash and re-check (the Merkle closure).
    #[must_use]
    pub fn dependents(&self, s: Sym) -> BTreeSet<Sym> {
        Self::closure(s, &self.rev)
    }

    /// Everything `s` transitively depends on.
    #[must_use]
    pub fn dependencies(&self, s: Sym) -> BTreeSet<Sym> {
        Self::closure(s, &self.fwd)
    }

    fn closure(start: Sym, adj: &BTreeMap<Sym, BTreeSet<Sym>>) -> BTreeSet<Sym> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![start];
        while let Some(n) = stack.pop() {
            for &m in adj.get(&n).into_iter().flatten() {
                if seen.insert(m) {
                    stack.push(m);
                }
            }
        }
        seen.remove(&start);
        seen
    }

    /// Resolve a user-supplied name to the definitions it could mean: an exact
    /// canonical match (`Data.List.map`), or any definition whose unqualified
    /// tail equals `name` (`map` matches `Data.List.map`, `helper` matches
    /// `Data.Map@helper`). Sorted, so the caller can report candidates stably.
    #[must_use]
    pub fn resolve(&self, name: &str) -> Vec<Sym> {
        self.fwd
            .keys()
            .copied()
            .filter(|s| {
                let t = s.as_str();
                t == name || t.rsplit(['.', '@']).next() == Some(name)
            })
            .collect()
    }
}
