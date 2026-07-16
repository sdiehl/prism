//! Persisted query-decision facts: one versioned model for every compiler
//! query boundary.
//!
//! A [`QueryFact`] records what one durable query decided: its stable kind and
//! logical identity, the ordered semantic input identities it consumed, the
//! output object identity it produced (when it produced one), the hit, miss,
//! write, or cutoff outcome, and deterministic reason data. Facts assemble into
//! a [`FactGraph`] whose nodes are digest-named and whose edges run from each
//! query to its inputs and output, mirroring the sidecar graph discipline.
//!
//! Two adjacent graphs per workspace scope live in the store's decisions layer
//! as a [`FactLedger`]: recording a fact rotates the last recorded fact for the
//! same identity into the previous graph, so `why-recompiled` explains from the
//! previous/current graph diff ([`FactLedger::diff`]) rather than session-only
//! events, and keeps explaining after the source files are gone. Serialized
//! bytes are a pure function of the facts: graphs sort by (kind, identity),
//! nothing records a timestamp, and no map-iteration order leaks.
//!
//! Like every decision record, the ledger is explanatory metadata: it never
//! authorizes cache reuse, and losing it only loses explanations.

use std::collections::BTreeMap;
use std::sync::Mutex;

use serde::{Deserialize, Serialize};
use serde_json::json;

use crate::error::Error;
use crate::resolve::Root;
use crate::store::disk::Store;

use super::node_id::{minted_id, NodeId};

/// The versioned envelope of a serialized fact graph.
pub const FACT_GRAPH_FORMAT: &str = "prism-query-fact-graph-v1";
/// The versioned envelope of the persisted previous/current ledger.
pub const FACT_LEDGER_FORMAT: &str = "prism-query-fact-ledger-v1";
/// The store decisions-layer kind the ledger is filed under.
pub const FACT_DECISION_KIND: &str = "query-facts";
// Domain separator for the workspace-scope locator derivation.
const FACT_SCOPE_SCHEMA: &[u8] = b"prism-query-fact-scope-v1";
// The stable descriptor of an embedded (compiled-in) module root.
const ROOT_EMBEDDED_DESCRIPTOR: &str = "embedded-stdlib";
// Query-kind discriminants, matching the `rename_all = "kebab-case"` serde tags
// on `QueryKind`. One home, echoed by `QueryKind::tag`; the round-trip is
// guarded by a unit test so a rename cannot silently drift.
const KIND_MODULE: &str = "module";
const KIND_OPTIMIZER: &str = "optimizer";
const KIND_EFFECT: &str = "effect";
const KIND_BACKEND_SCC: &str = "backend-scc";
const KIND_CLOSURE_PLAN: &str = "closure-plan";
const KIND_OBJECT: &str = "object";
const KIND_LINK: &str = "link";
// Outcome discriminants, same one-home discipline as the kind tags.
const OUTCOME_HIT: &str = "hit";
const OUTCOME_MISS: &str = "miss";
const OUTCOME_WRITE: &str = "write";
const OUTCOME_CUTOFF: &str = "cutoff";
// Node-identity domain tags: a query, one of its inputs, and its output mint
// distinct node ids even when their identity strings coincide.
const FACT_NODE_QUERY: &str = "query";
const FACT_NODE_INPUT: &str = "query-input";
const FACT_NODE_OUTPUT: &str = "query-output";

/// The durable query family a fact belongs to.
///
/// Six kinds are active compiler producers: module checking, SCC-local
/// optimization, backend SCC codegen, closure planning, object emission, and
/// final linking. [`QueryKind::Effect`] is retained as a historical wire tag so
/// ledgers written by older compilers remain readable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum QueryKind {
    Module,
    Optimizer,
    Effect,
    BackendScc,
    ClosurePlan,
    Object,
    Link,
}

impl QueryKind {
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Module => KIND_MODULE,
            Self::Optimizer => KIND_OPTIMIZER,
            Self::Effect => KIND_EFFECT,
            Self::BackendScc => KIND_BACKEND_SCC,
            Self::ClosurePlan => KIND_CLOSURE_PLAN,
            Self::Object => KIND_OBJECT,
            Self::Link => KIND_LINK,
        }
    }
}

/// What one query run did.
///
/// A reuse of the exact artifact is a `Hit`; a recomputation is a `Miss` with
/// no prior fact to compare against, a `Write` when it moved the output, or a
/// `Cutoff` when the output identity stayed put, authorizing downstream reuse.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FactOutcome {
    Hit,
    Miss,
    Write,
    Cutoff,
}

impl FactOutcome {
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Hit => OUTCOME_HIT,
            Self::Miss => OUTCOME_MISS,
            Self::Write => OUTCOME_WRITE,
            Self::Cutoff => OUTCOME_CUTOFF,
        }
    }
}

/// One ordered semantic input of a query: a caller-chosen slot name and the
/// content identity observed in that slot.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FactInput {
    pub name: String,
    pub identity: String,
}

/// One recorded query decision. All active and historical query kinds share this
/// type; the kind plus the logical identity is the stable key a diff aligns on.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct QueryFact {
    pub kind: QueryKind,
    /// Stable logical identity within the kind (a module path, an SCC label,
    /// an artifact name), never a digest of this run's bytes.
    pub identity: String,
    /// Ordered semantic input identities, in the query's canonical slot order.
    pub inputs: Vec<FactInput>,
    /// The output object identity, when the query produced one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output: Option<String>,
    pub outcome: FactOutcome,
    /// Deterministic reason data explaining a non-hit, empty on a hit.
    pub reasons: Vec<String>,
}

impl QueryFact {
    /// The digest-derived node id of this query in the fact graph, minted over
    /// its stable key so the same logical query names the same node across runs.
    #[must_use]
    pub fn node_id(&self) -> NodeId {
        minted_id(format!("{FACT_NODE_QUERY}\n{}\n{}", self.kind.tag(), self.identity).as_bytes())
    }
}

/// The operation a fact-graph edge records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FactEdgeKind {
    /// The query consumed this input identity.
    Input,
    /// The query produced this output identity.
    Output,
}

/// A directed, kinded edge from a query node to an input or output node.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FactEdge {
    pub from: NodeId,
    pub to: NodeId,
    pub kind: FactEdgeKind,
}

fn input_node_id(input: &FactInput) -> NodeId {
    minted_id(format!("{FACT_NODE_INPUT}\n{}\n{}", input.name, input.identity).as_bytes())
}

fn output_node_id(identity: &str) -> NodeId {
    minted_id(format!("{FACT_NODE_OUTPUT}\n{identity}").as_bytes())
}

/// A sealed set of query facts: sorted by (kind, identity), one fact per key,
/// independent of insertion or completion order.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct FactGraph {
    facts: Vec<QueryFact>,
}

impl FactGraph {
    /// Seal a batch of facts: full-content sort, then keep exactly one fact per
    /// (kind, identity). The result is a pure function of the fact set, so
    /// parallel completion order cannot reach the serialized bytes.
    #[must_use]
    pub fn new(mut facts: Vec<QueryFact>) -> Self {
        facts.sort();
        facts.dedup_by(|a, b| a.kind == b.kind && a.identity == b.identity);
        Self { facts }
    }

    #[must_use]
    pub fn facts(&self) -> &[QueryFact] {
        &self.facts
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// The fact recorded for this stable key, if any.
    #[must_use]
    pub fn get(&self, kind: QueryKind, identity: &str) -> Option<&QueryFact> {
        self.position(kind, identity).ok().map(|i| &self.facts[i])
    }

    fn position(&self, kind: QueryKind, identity: &str) -> Result<usize, usize> {
        self.facts
            .binary_search_by(|fact| (fact.kind, fact.identity.as_str()).cmp(&(kind, identity)))
    }

    fn upsert(&mut self, fact: QueryFact) {
        match self.position(fact.kind, &fact.identity) {
            Ok(i) => self.facts[i] = fact,
            Err(i) => self.facts.insert(i, fact),
        }
    }

    fn take(&mut self, kind: QueryKind, identity: &str) -> Option<QueryFact> {
        self.position(kind, identity)
            .ok()
            .map(|i| self.facts.remove(i))
    }

    /// The edges from each query node to its input and output nodes, sorted and
    /// deduplicated. Derived from the facts themselves, so the edge relation can
    /// never drift from the recorded inputs and outputs.
    #[must_use]
    pub fn edges(&self) -> Vec<FactEdge> {
        let mut edges = Vec::new();
        for fact in &self.facts {
            let from = fact.node_id();
            for input in &fact.inputs {
                edges.push(FactEdge {
                    from: from.clone(),
                    to: input_node_id(input),
                    kind: FactEdgeKind::Input,
                });
            }
            if let Some(output) = &fact.output {
                edges.push(FactEdge {
                    from: from.clone(),
                    to: output_node_id(output),
                    kind: FactEdgeKind::Output,
                });
            }
        }
        edges.sort();
        edges.dedup();
        edges
    }

    /// Stable pretty JSON of the graph under its versioned envelope, with the
    /// derived edges materialized. Byte-identical for identical fact sets.
    ///
    /// # Errors
    /// Fails only if JSON serialization fails.
    pub fn to_json_string(&self) -> Result<String, Error> {
        let value = json!({
            "format": FACT_GRAPH_FORMAT,
            "facts": self.facts,
            "edges": self.edges(),
        });
        serde_json::to_string_pretty(&value).map_err(|e| Error::ResolveLineage(e.to_string()))
    }
}

// The on-disk shape of the ledger, under its own versioned header on top of the
// decisions layer's format line. A wrong-version document is refused on read.
#[derive(Serialize, Deserialize)]
struct FactLedgerDoc {
    format: String,
    previous: Vec<QueryFact>,
    current: Vec<QueryFact>,
}

/// The two adjacent fact graphs of one workspace scope: the facts as of the
/// previous recording of each query, and the facts as of the latest.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FactLedger {
    pub previous: FactGraph,
    pub current: FactGraph,
}

impl FactLedger {
    /// Read the ledger for a scope; an absent record is an empty ledger.
    ///
    /// # Errors
    /// Fails on a filesystem error, a malformed document, or a version the
    /// reader does not speak; a damaged ledger is refused, never misread.
    pub fn load(store: &Store, scope: &FactScope) -> Result<Self, Error> {
        let Some(bytes) = store
            .get_decision(FACT_DECISION_KIND, scope.locator())
            .map_err(Error::Io)?
        else {
            return Ok(Self::default());
        };
        let doc: FactLedgerDoc = serde_json::from_slice(&bytes)
            .map_err(|e| Error::ResolveLineage(format!("malformed query fact ledger: {e}")))?;
        if doc.format != FACT_LEDGER_FORMAT {
            return Err(Error::ResolveLineage(format!(
                "query fact ledger has format {:?}; this build reads {FACT_LEDGER_FORMAT:?}",
                doc.format
            )));
        }
        Ok(Self {
            previous: FactGraph::new(doc.previous),
            current: FactGraph::new(doc.current),
        })
    }

    // Record one fact: the last recorded fact for the same stable key rotates
    // into the previous graph, so previous/current always describe two adjacent
    // recordings of that query.
    fn record(&mut self, fact: QueryFact) {
        if let Some(old) = self.current.take(fact.kind, &fact.identity) {
            self.previous.upsert(old);
        }
        self.current.upsert(fact);
    }

    // Retire every current fact from a producer this compiler no longer runs.
    // The last active fact becomes the previous side of a Removed diff, keeping
    // the upgrade explainable while preventing stale facts from masquerading as
    // current compiler decisions.
    fn retire_kind(&mut self, kind: QueryKind) {
        let identities = self
            .current
            .facts()
            .iter()
            .filter(|fact| fact.kind == kind)
            .map(|fact| fact.identity.clone())
            .collect::<Vec<_>>();
        for identity in identities {
            if let Some(old) = self.current.take(kind, &identity) {
                self.previous.upsert(old);
            }
        }
    }

    fn save(&self, store: &Store, scope: &FactScope) -> Result<(), Error> {
        let doc = FactLedgerDoc {
            format: FACT_LEDGER_FORMAT.to_string(),
            previous: self.previous.facts().to_vec(),
            current: self.current.facts().to_vec(),
        };
        let bytes = serde_json::to_vec(&doc)
            .map_err(|e| Error::ResolveLineage(format!("encode query fact ledger: {e}")))?;
        store
            .put_decision(FACT_DECISION_KIND, scope.locator(), &bytes)
            .map_err(Error::Io)
    }

    /// Align the previous and current graphs by stable query identity.
    #[must_use]
    pub fn diff(&self) -> FactDiff {
        let mut keys: Vec<(QueryKind, &str)> = self
            .previous
            .facts()
            .iter()
            .chain(self.current.facts())
            .map(|fact| (fact.kind, fact.identity.as_str()))
            .collect();
        keys.sort_unstable();
        keys.dedup();
        let entries = keys
            .into_iter()
            .map(|(kind, identity)| {
                let previous = self.previous.get(kind, identity).cloned();
                let current = self.current.get(kind, identity).cloned();
                let change = match (&previous, &current) {
                    (None, Some(_)) => FactChange::Added,
                    (Some(_), None) => FactChange::Removed,
                    (Some(p), Some(c)) => {
                        let changes = changed_inputs(p, c);
                        if changes.is_empty() && p.output == c.output {
                            FactChange::Unchanged
                        } else {
                            FactChange::InputsChanged(changes)
                        }
                    }
                    (None, None) => FactChange::Unchanged,
                };
                FactDiffEntry {
                    kind,
                    identity: identity.to_string(),
                    previous,
                    current,
                    change,
                }
            })
            .collect();
        FactDiff { entries }
    }
}

/// How one aligned query moved between the previous and current graphs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum FactChange {
    /// Present only in the current graph.
    Added,
    /// Present only in the previous graph.
    Removed,
    /// Present in both with input or output identities that moved.
    InputsChanged(Vec<InputChange>),
    /// Present in both with identical inputs and output.
    Unchanged,
}

/// How one named input slot moved between two facts of the same query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum InputDelta {
    Added,
    Removed,
    Changed,
}

/// One input slot that differs between the previous and current fact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct InputChange {
    pub name: String,
    pub delta: InputDelta,
}

/// One aligned query in a previous/current graph diff.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FactDiffEntry {
    pub kind: QueryKind,
    pub identity: String,
    pub previous: Option<QueryFact>,
    pub current: Option<QueryFact>,
    pub change: FactChange,
}

/// The previous/current alignment of a scope's fact graphs, sorted by stable
/// query identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FactDiff {
    pub entries: Vec<FactDiffEntry>,
}

/// The input slots that differ between two facts of the same query.
///
/// Changes come in the current fact's slot order, with slots dropped since the
/// previous fact appended in their previous order; deterministic because both
/// input lists are.
#[must_use]
pub fn changed_inputs(previous: &QueryFact, current: &QueryFact) -> Vec<InputChange> {
    let mut changes = Vec::new();
    for input in &current.inputs {
        let old = previous
            .inputs
            .iter()
            .find(|candidate| candidate.name == input.name);
        match old {
            None => changes.push(InputChange {
                name: input.name.clone(),
                delta: InputDelta::Added,
            }),
            Some(old) if old.identity != input.identity => changes.push(InputChange {
                name: input.name.clone(),
                delta: InputDelta::Changed,
            }),
            Some(_) => {}
        }
    }
    for input in &previous.inputs {
        if !current
            .inputs
            .iter()
            .any(|candidate| candidate.name == input.name)
        {
            changes.push(InputChange {
                name: input.name.clone(),
                delta: InputDelta::Removed,
            });
        }
    }
    changes
}

/// Kind-agnostic prose for a set of input changes, for query kinds without a
/// bespoke phrasing of their slots.
#[must_use]
pub fn describe_input_changes(changes: &[InputChange]) -> Vec<String> {
    changes
        .iter()
        .map(|change| match change.delta {
            InputDelta::Added => format!("input `{}` was added", change.name),
            InputDelta::Removed => format!("input `{}` was removed", change.name),
            InputDelta::Changed => format!("input `{}` changed", change.name),
        })
        .collect()
}

/// The outcome of a query run, derived in one place: a reuse is a hit; a
/// recomputation is a miss with no prior fact, a cutoff when the output
/// identity held, and a write when the output moved.
#[must_use]
pub fn outcome_of(previous: Option<&QueryFact>, output: Option<&str>, reused: bool) -> FactOutcome {
    if reused {
        return FactOutcome::Hit;
    }
    match previous {
        None => FactOutcome::Miss,
        Some(previous) if previous.output.is_some() && previous.output.as_deref() == output => {
            FactOutcome::Cutoff
        }
        Some(_) => FactOutcome::Write,
    }
}

/// The workspace scope a ledger is filed under: a digest of the module search
/// roots, so builds over the same roots share one ledger and unrelated
/// workspaces never collide.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactScope {
    locator: String,
}

impl FactScope {
    #[must_use]
    pub fn of_roots(roots: &[Root]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(FACT_SCOPE_SCHEMA);
        for root in roots {
            // Fixed-width per-root digests, so no root descriptor can forge a
            // boundary into its neighbor.
            hasher.update(blake3::hash(root_descriptor(root).as_bytes()).as_bytes());
        }
        Self {
            locator: hasher.finalize().to_hex().to_string(),
        }
    }

    /// The hex locator the decisions layer files this scope under.
    #[must_use]
    pub fn locator(&self) -> &str {
        &self.locator
    }
}

fn root_descriptor(root: &Root) -> String {
    match root {
        Root::Dir(path) => format!("dir:{}", path.to_string_lossy()),
        Root::Embedded(_) => ROOT_EMBEDDED_DESCRIPTOR.to_string(),
        Root::SourceBundle {
            label, identity, ..
        } => format!("bundle:{label}:{identity:?}"),
    }
}

/// Record a batch of facts into a scope's ledger with one read-modify-write.
///
/// # Errors
/// Fails on a filesystem error or a malformed existing ledger.
pub fn record_facts(store: &Store, scope: &FactScope, facts: Vec<QueryFact>) -> Result<(), Error> {
    record_facts_retiring(store, scope, facts, &[])
}

fn record_facts_retiring(
    store: &Store,
    scope: &FactScope,
    facts: Vec<QueryFact>,
    retired_kinds: &[QueryKind],
) -> Result<(), Error> {
    if facts.is_empty() && retired_kinds.is_empty() {
        return Ok(());
    }
    let batch = FactGraph::new(facts);
    let mut ledger = FactLedger::load(store, scope)?;
    for &kind in retired_kinds {
        ledger.retire_kind(kind);
    }
    for fact in batch.facts {
        ledger.record(fact);
    }
    ledger.save(store, scope)
}

/// Record one fact into a scope's ledger.
///
/// # Errors
/// Fails on a filesystem error or a malformed existing ledger.
pub fn record_fact(store: &Store, scope: &FactScope, fact: QueryFact) -> Result<(), Error> {
    record_facts(store, scope, vec![fact])
}

/// The narrow recording seam for query boundaries that complete in parallel.
///
/// Workers `record` facts in any completion order, and one caller commits the
/// sealed batch in a single ledger read-modify-write. The committed bytes are
/// a pure function of the fact set, never of completion order.
#[derive(Debug, Default)]
pub struct FactRecorder {
    facts: Mutex<BTreeMap<(QueryKind, String), QueryFact>>,
}

impl FactRecorder {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Buffer one fact; safe from any worker thread.
    pub fn record(&self, fact: QueryFact) {
        self.facts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert((fact.kind, fact.identity.clone()), fact);
    }

    /// Discard every buffered fact without touching the durable ledger.
    pub fn clear(&self) {
        self.facts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clear();
    }

    /// Commit every buffered fact to the scope's ledger and clear the buffer.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed existing ledger.
    pub fn commit(&self, store: &Store, scope: &FactScope) -> Result<(), Error> {
        self.commit_retiring(store, scope, &[])
    }

    /// Commit buffered facts and retire stale current facts from inactive query
    /// producers in the same ledger update.
    ///
    /// # Errors
    /// Fails on a filesystem error or a malformed existing ledger.
    pub fn commit_retiring(
        &self,
        store: &Store,
        scope: &FactScope,
        retired_kinds: &[QueryKind],
    ) -> Result<(), Error> {
        let facts = std::mem::take(
            &mut *self
                .facts
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        )
        .into_values()
        .collect();
        record_facts_retiring(store, scope, facts, retired_kinds)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The `tag` consts must match the serde discriminants: node ids and human
    // labels mint over the tags while the wire uses the serde names.
    #[test]
    fn kind_and_outcome_tags_match_serialization() {
        for kind in [
            QueryKind::Module,
            QueryKind::Optimizer,
            QueryKind::Effect,
            QueryKind::BackendScc,
            QueryKind::ClosurePlan,
            QueryKind::Object,
            QueryKind::Link,
        ] {
            let value = serde_json::to_value(kind).unwrap();
            assert_eq!(value.as_str(), Some(kind.tag()));
        }
        for outcome in [
            FactOutcome::Hit,
            FactOutcome::Miss,
            FactOutcome::Write,
            FactOutcome::Cutoff,
        ] {
            let value = serde_json::to_value(outcome).unwrap();
            assert_eq!(value.as_str(), Some(outcome.tag()));
        }
    }

    fn fact(identity: &str, source: &str) -> QueryFact {
        QueryFact {
            kind: QueryKind::Module,
            identity: identity.to_string(),
            inputs: vec![FactInput {
                name: "source".to_string(),
                identity: source.to_string(),
            }],
            output: Some(format!("out-{source}")),
            outcome: FactOutcome::Miss,
            reasons: Vec::new(),
        }
    }

    // Graph bytes are a pure function of the fact set, not insertion order.
    #[test]
    fn graph_bytes_ignore_insertion_order() {
        let forward = FactGraph::new(vec![fact("A", "1"), fact("B", "2")]);
        let backward = FactGraph::new(vec![fact("B", "2"), fact("A", "1")]);
        assert_eq!(
            forward.to_json_string().unwrap(),
            backward.to_json_string().unwrap()
        );
    }

    // Every fact contributes one edge per input and one for its output, and the
    // query node id is stable across runs of the same logical query.
    #[test]
    fn edges_join_query_to_inputs_and_output() {
        let graph = FactGraph::new(vec![fact("A", "1")]);
        let edges = graph.edges();
        assert_eq!(edges.len(), 2);
        let from = graph.facts()[0].node_id();
        assert!(edges.iter().all(|edge| edge.from == from));
        assert_eq!(
            edges
                .iter()
                .filter(|e| e.kind == FactEdgeKind::Input)
                .count(),
            1
        );
        assert_eq!(
            edges
                .iter()
                .filter(|e| e.kind == FactEdgeKind::Output)
                .count(),
            1
        );
        assert_eq!(fact("A", "other").node_id(), graph.facts()[0].node_id());
    }

    // Recording rotates the same identity's last fact into the previous graph
    // and leaves other identities untouched.
    #[test]
    fn recording_rotates_previous_per_identity() {
        let mut ledger = FactLedger::default();
        ledger.record(fact("A", "1"));
        ledger.record(fact("B", "1"));
        ledger.record(fact("A", "2"));
        assert_eq!(
            ledger.previous.get(QueryKind::Module, "A"),
            Some(&fact("A", "1"))
        );
        assert_eq!(
            ledger.current.get(QueryKind::Module, "A"),
            Some(&fact("A", "2"))
        );
        assert_eq!(ledger.previous.get(QueryKind::Module, "B"), None);
        let diff = ledger.diff();
        let a = diff
            .entries
            .iter()
            .find(|entry| entry.identity == "A")
            .unwrap();
        assert_eq!(
            a.change,
            FactChange::InputsChanged(vec![InputChange {
                name: "source".to_string(),
                delta: InputDelta::Changed,
            }])
        );
    }

    #[test]
    fn outcomes_derive_from_previous_and_output() {
        let previous = fact("A", "1");
        assert_eq!(outcome_of(None, Some("x"), true), FactOutcome::Hit);
        assert_eq!(outcome_of(None, Some("x"), false), FactOutcome::Miss);
        assert_eq!(
            outcome_of(Some(&previous), Some("out-1"), false),
            FactOutcome::Cutoff
        );
        assert_eq!(
            outcome_of(Some(&previous), Some("out-2"), false),
            FactOutcome::Write
        );
    }
}
