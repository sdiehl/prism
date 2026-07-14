//! Lineage: the shared, content-addressed provenance graph and its queries.
//!
//! A lineage sidecar is a typed graph whose nodes are named by digest and whose
//! edges say which operation produced what, so an emitted artifact or a recorded run
//! can explain what produced it. One envelope serves many producers; the subsystem
//! is split by concept:
//!
//! - `graph`: the node/edge vocabulary, digest identity, the versioned envelope,
//!   the determinism seal, and the typed relations every query reads.
//! - `build`: collecting and assembling a project-build sidecar (plus the v1
//!   adapter and the sidecar's on-disk siting and reader).
//! - `run`: collecting and assembling a recorded-run sidecar from provenance events.
//! - `explain`: `why-output`, walking the graph backward to an `explain::Explanation`.
//! - [`diff`]: aligning two graphs by logical key into a `diff::DiffReport`.
//! - [`verify`]: rehashing content nodes and closing the record loop by replay.
//! - `render`: all human prose, consuming the answer objects the queries produce.
//! - `facts`: persisted query-decision facts with previous/current graph diffs,
//!   feeding `why-recompiled` from the store rather than session-only events.

#[cfg(feature = "native")]
mod build;
#[cfg(feature = "native")]
mod cert;
#[cfg(feature = "native")]
mod diff;
#[cfg(feature = "native")]
mod docs;
#[cfg(feature = "native")]
mod explain;
mod facts;
#[cfg(feature = "native")]
mod graph;
mod node_id;
#[cfg(feature = "native")]
mod render;
#[cfg(feature = "native")]
mod run;
#[cfg(feature = "native")]
mod verify;

#[cfg(feature = "native")]
pub use build::{
    read_lineage, sidecar_of, sidecar_path_for, write_sidecar, BuildLineage, BuildLineageInput,
};
#[cfg(feature = "native")]
pub use cert::{check_cert, mint_lineage_cert, mint_replay_cert};
#[cfg(feature = "native")]
pub use diff::{diff, DiffEntry, DiffReport, LogicalKey, MovedEntry};
#[cfg(feature = "native")]
pub use docs::{
    docs_manifest_path, verify_manifest_identity, write_docs_manifest, DocsLineage,
    DocsLineageInput, DocsPageInput, DoctestInput,
};
#[cfg(feature = "native")]
pub use explain::{
    why_output, why_world_state, Explanation, SelectedOutput, WorldExplanation, WorldForkCrossed,
    WorldRun,
};
pub use facts::{
    changed_inputs, describe_input_changes, outcome_of, record_fact, record_facts, FactChange,
    FactDiff, FactDiffEntry, FactEdge, FactEdgeKind, FactGraph, FactInput, FactLedger, FactOutcome,
    FactRecorder, FactScope, InputChange, InputDelta, QueryFact, QueryKind, FACT_DECISION_KIND,
    FACT_GRAPH_FORMAT, FACT_LEDGER_FORMAT,
};
#[cfg(feature = "native")]
pub use graph::{
    backend_name, ArgvPayload, BuildRequest, CompilerPayload, CompilerRow, DiagnosticPayload,
    DocsGeneratorPayload, DoctestPayload, Edge, EdgeKind, EnvReadPayload, FileWritePayload,
    InputFilePayload, LineageArtifact, LineageCache, LineageGraph, LineageRoot, Node, NodeKind,
    OutputPayload, ReplayRelation, RequestKind, RootRole, TracePayload, Variant, WorldForkPayload,
    WorldLawPayload, WorldStatePayload, WriteMode, BACKEND_INTERPRETER, DOCS_GENERATOR_FORMAT,
    DOCS_MANIFEST_FILE, DOCS_PAGE_KIND, LINEAGE_EXTENSION, LINEAGE_FORMAT, LINEAGE_GRAPH_FORMAT,
    REPLAY_EXTENSION, STDOUT_SELECTOR,
};
pub use node_id::NodeId;
#[cfg(feature = "native")]
pub use render::{render_diff, render_explanation, render_human, render_world_explanation};
#[cfg(feature = "native")]
pub use run::{replay_relation, run_entry, write_run_sidecar, RunLineage, RunLineageInput};
#[cfg(feature = "native")]
pub use verify::{
    resolve_replay_file, verify, verify_run_replay, verify_world, RunVerification, VerifyReport,
    WorldVerifyReport,
};

#[cfg(all(test, feature = "native"))]
mod tests;
