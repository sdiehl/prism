use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

#[cfg(feature = "native")]
use crate::error::Error;
#[cfg(feature = "native")]
use crate::lineage::FactScope;
use crate::lineage::{FactInput, FactOutcome, FactRecorder, QueryFact, QueryKind};
#[cfg(feature = "native")]
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::store::disk::{resolve_store_path, Store};

use super::front::Front;
use super::modules::CheckedModule;
#[cfg(feature = "native")]
use super::Config;

const QUERY_KEY_INPUT: &str = "query-key";

#[derive(Debug, Default)]
struct Inner {
    fronts: Mutex<BTreeMap<String, Front>>,
    modules: Mutex<BTreeMap<String, CheckedModule>>,
    decisions: Mutex<BTreeMap<(QueryKind, String), QueryDecision>>,
    facts: FactRecorder,
    hits: AtomicU64,
    misses: AtomicU64,
    writes: AtomicU64,
}

/// One compiler-command session with in-memory frontend and module-query caches.
///
/// Killing or dropping a session only loses reuse; it cannot change compilation
/// results. Successful artifacts alone are cached. Exact keys commit to raw
/// source/module bytes; token-semantic aliases permit trivia-only reuse after the
/// current source has been reparsed to refresh spans and diagnostics. Both key
/// forms commit to the relevant compiler configuration.
#[derive(Clone, Debug, Default)]
pub struct CompilerSession(Arc<Inner>);

/// One query-boundary decision captured for lineage explanation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryDecision {
    /// Durable query family.
    pub kind: QueryKind,
    /// Stable logical artifact identity within the family.
    pub identity: String,
    /// Whether the exact artifact was reused.
    pub reused: bool,
    /// Ordered semantic inputs to the query.
    pub inputs: Vec<FactInput>,
    /// Immutable output object identity, when one was produced.
    pub output: Option<String>,
    /// Final result of this query boundary.
    pub outcome: FactOutcome,
    /// Input facts that forced recomputation, empty on a hit.
    pub reasons: Vec<String>,
}

impl QueryDecision {
    pub(super) fn new(
        kind: QueryKind,
        identity: String,
        query_key: String,
        outcome: FactOutcome,
        output: Option<String>,
        reasons: Vec<String>,
    ) -> Self {
        Self {
            kind,
            identity,
            reused: outcome == FactOutcome::Hit,
            inputs: vec![FactInput {
                name: QUERY_KEY_INPUT.to_string(),
                identity: query_key,
            }],
            output,
            outcome,
            reasons,
        }
    }

    fn fact(&self) -> QueryFact {
        QueryFact {
            kind: self.kind,
            identity: self.identity.clone(),
            inputs: self.inputs.clone(),
            output: self.output.clone(),
            outcome: self.outcome,
            reasons: self.reasons.clone(),
        }
    }
}

/// Snapshot of a [`CompilerSession`]'s query decisions.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SessionStats {
    /// Successful in-memory artifact lookups.
    pub hits: u64,
    /// Lookups that required normal compilation.
    pub misses: u64,
    /// Successful frontend or independently checked module artifacts inserted.
    pub writes: u64,
}

impl CompilerSession {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn stats(&self) -> SessionStats {
        SessionStats {
            hits: self.0.hits.load(Ordering::Relaxed),
            misses: self.0.misses.load(Ordering::Relaxed),
            writes: self.0.writes.load(Ordering::Relaxed),
        }
    }

    /// Decisions recorded by optimizer and backend query boundaries.
    #[must_use]
    pub fn decisions(&self) -> Vec<QueryDecision> {
        self.0
            .decisions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .values()
            .cloned()
            .collect()
    }

    /// Drop every in-memory artifact while retaining the counters.
    pub fn clear(&self) {
        self.0
            .fronts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clear();
        self.0
            .modules
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clear();
        self.0
            .decisions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clear();
        self.0.facts.clear();
    }

    #[cfg(feature = "native")]
    pub(super) fn commit_decisions(&self, roots: &[Root], cfg: &Config) -> Result<(), Error> {
        if !cfg.flags.compiler_cache || cfg.flags.store {
            self.0.facts.clear();
            return Ok(());
        }
        let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
        self.0
            .facts
            .commit_retiring(&store, &FactScope::of_roots(roots), &[QueryKind::Effect])
    }

    pub(super) fn record_hit(&self) {
        self.0.hits.fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn record_miss(&self) {
        self.0.misses.fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn record_write(&self) {
        self.0.writes.fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn record_decision(&self, decision: QueryDecision) {
        self.0.facts.record(decision.fact());
        self.0
            .decisions
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert((decision.kind, decision.identity.clone()), decision);
    }

    pub(super) fn lookup(&self, key: &str) -> Option<Front> {
        self.0
            .fronts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(key)
            .cloned()
    }

    pub(super) fn lookup_module(&self, key: &str) -> Option<CheckedModule> {
        self.0
            .modules
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(key)
            .cloned()
    }

    pub(super) fn insert_module(&self, key: String, module: CheckedModule) {
        self.0
            .modules
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(key, module);
    }

    pub(super) fn insert_aliases(&self, keys: impl IntoIterator<Item = String>, front: &Front) {
        {
            let mut fronts = self
                .0
                .fronts
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            for key in keys {
                fronts.insert(key, front.clone());
            }
        }
        self.record_write();
    }
}
