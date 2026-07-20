//! The shared lineage graph: node/edge vocabulary, digest identity, the versioned
//! envelope, and the typed relations every query reads.
//!
//! A lineage graph is a set of digest-named [`Node`]s joined by kinded [`Edge`]s
//! that fan out from one [`NodeKind::Request`]. This module owns the types, their
//! content-derived identities, the determinism seal ([`finalize`]), the on-disk
//! envelope ([`LineageGraph::to_json_string`]), and the
//! relation accessors ([`LineageGraph::request`], [`LineageGraph::inputs_of`], ...)
//! that let explain, diff, and verify read the graph without scanning raw edges.
//!
//! Build assembly lives in [`super::build`], run assembly in [`super::run`].

use std::fs;
use std::io;
use std::path::Path;

use crate::error::Error;
use crate::lineage::provenance::{self, EVENT_HASH_SCHEME};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

pub(crate) use super::node_id::minted_id;
pub(super) use super::node_id::NodeId;

/// The build-lineage projection embedded inside a package-world report (see
/// [`super::build::BuildLineage::to_json`]); not the standalone sidecar envelope,
/// which is [`LINEAGE_GRAPH_FORMAT`].
pub const LINEAGE_FORMAT: &str = "prism-build-lineage-v1";
/// The shared lineage graph envelope every producer emits.
pub const LINEAGE_GRAPH_FORMAT: &str = "prism-lineage-graph-v1";
pub const LINEAGE_EXTENSION: &str = "plineage";
/// The fixed file name a docs manifest is written under, beside the generated
/// pages (`<outdir>/docs.plineage`). One home so the writer and every verifier
/// name the same file.
pub const DOCS_MANIFEST_FILE: &str = "docs.plineage";
/// The artifact kind stamped on a documentation page node, so a page reads back
/// as a page rather than a build artifact.
pub const DOCS_PAGE_KIND: &str = "docs-page";
/// The docs generator's format identifier, carried by the generator node so a
/// manifest names which renderer produced its pages.
pub const DOCS_GENERATOR_FORMAT: &str = "prism-docs-markdown-v1";
/// The extension of the sibling trace a run sidecar falls back to when its own
/// trace node does not record a replay-file relation (older sidecars).
///
/// A run written as `foo.plineage` records its trace as `foo.replay`; a current
/// sidecar names that relation explicitly, and only pre-relation files rely on this.
pub const REPLAY_EXTENSION: &str = "replay";
/// The literal output selector that names a run's captured stdout in `why-output`.
pub const STDOUT_SELECTOR: &str = "stdout";
pub(crate) const ARTIFACT_DIGEST_SCHEME: &str = "blake3";
// Minted node ids (request, compiler identity, diagnostics, cache summary) commit
// their canonical payload bytes under this scheme; root and artifact nodes reuse
// the content digest they already carry.
const BACKEND_LLVM: &str = "llvm";
const BACKEND_MLIR: &str = "mlir";
// Node-kind discriminants, matching the `rename_all = "kebab-case"` serde tags on
// `NodeKind`. Defined once here and echoed by `NodeKind::tag`; the round-trip is
// guarded by a unit test so a rename cannot silently drift.
const NODE_REQUEST: &str = "request";
const NODE_SOURCE_ROOT: &str = "source-root";
const NODE_STDLIB_ROOT: &str = "stdlib-root";
const NODE_PACKAGE_ROOT: &str = "package-root";
const NODE_COMPILER_IDENTITY: &str = "compiler-identity";
const NODE_ARTIFACT: &str = "artifact";
const NODE_DIAGNOSTIC: &str = "diagnostic";
const NODE_CACHE_SUMMARY: &str = "cache-summary";
// Run-lineage node kinds. Same family, same one-home discipline as the build
// kinds above; the round-trip against the serde discriminants is guarded by the
// same unit test.
const NODE_TRACE: &str = "trace";
const NODE_ARGV: &str = "argv";
const NODE_ENV_READ: &str = "env-read";
const NODE_INPUT_FILE: &str = "input-file";
const NODE_STDOUT: &str = "stdout";
const NODE_FILE_WRITE: &str = "file-write";
// World-lineage node kinds: the timeline export the PRISM WORLD resident emits.
// Same family, same one-home discipline; the round-trip against the serde
// discriminants is guarded by the same unit test. The web emitter mirrors these
// exact spellings (web/src/prism-world.ts names this file as their one home).
const NODE_WORLD_LAW: &str = "world-law";
const NODE_WORLD_STATE: &str = "world-state";
const NODE_WORLD_FORK: &str = "world-fork";
// Docs-lineage node kinds: the generator that rendered the pages, and one node
// per doctest that ran. Pages themselves reuse the shared `artifact` node kind
// (stamped `docs-page`), so they rehash through the same `verify` path.
const NODE_DOCS_GENERATOR: &str = "docs-generator";
const NODE_DOCTEST: &str = "doctest";
// Write-mode discriminants, matching the `rename_all = "kebab-case"` tags on
// `WriteMode` and echoed by `WriteMode::tag`; the same unit test checks the round-trip.
const WRITE_MODE_WRITE: &str = "write";
const WRITE_MODE_APPEND: &str = "append";
const WRITE_MODE_REMOVE: &str = "remove";
// The interpreter's backend label in a run's compiler identity, distinguishing a
// recorded interpreter run from a native build in the shared graph.
pub const BACKEND_INTERPRETER: &str = "interpreter";

/// The kind of build request that produced a lineage graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RequestKind {
    /// A `prism build` over a project manifest.
    ProjectBuild,
    /// A `prism check-world` pass over a package universe.
    CheckWorld,
    /// A recorded `prism run` of a program.
    Run,
    /// A `prism docs` documentation generation.
    Docs,
}

/// The role a root input plays in a build.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RootRole {
    Source,
    Stdlib,
    Package,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuildRequest {
    pub kind: RequestKind,
    pub path: String,
    pub entry: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageRoot {
    pub role: RootRole,
    pub name: Option<String>,
    pub origin: Option<String>,
    pub artifact_kind: String,
    pub scheme: String,
    pub root: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageArtifact {
    pub kind: String,
    pub path: String,
    pub digest_scheme: String,
    pub digest: String,
    pub bytes: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageCache {
    pub enabled: bool,
    pub objects_hit: usize,
    pub objects_written: usize,
    pub meta_written: usize,
    pub names_bound: usize,
}

impl BuildRequest {
    #[must_use]
    pub fn project(manifest: &Path, entry: &Path) -> Self {
        Self {
            kind: RequestKind::ProjectBuild,
            path: manifest.display().to_string(),
            entry: entry.display().to_string(),
        }
    }

    /// The request that names a recorded run: the entry file both locates and
    /// names the program.
    #[must_use]
    pub fn run(entry: &Path) -> Self {
        Self {
            kind: RequestKind::Run,
            path: entry.display().to_string(),
            entry: entry.display().to_string(),
        }
    }

    /// The request that names a documentation build: the project or file that was
    /// documented locates and names it.
    #[must_use]
    pub fn docs(path: &Path, entry: &Path) -> Self {
        Self {
            kind: RequestKind::Docs,
            path: path.display().to_string(),
            entry: entry.display().to_string(),
        }
    }
}

impl LineageCache {
    #[must_use]
    pub const fn disabled() -> Self {
        Self {
            enabled: false,
            objects_hit: 0,
            objects_written: 0,
            meta_written: 0,
            names_bound: 0,
        }
    }

    #[must_use]
    pub const fn from_stats(stats: crate::store::disk::CommitStats) -> Self {
        Self {
            enabled: true,
            objects_hit: stats.objects_hit,
            objects_written: stats.objects_written,
            meta_written: stats.meta_written,
            names_bound: stats.names_bound,
        }
    }

    // Newline-separated canonical encoding of the summary fields, in one place, so
    // the minted cache-summary node id is a pure function of the recorded numbers.
    pub(crate) fn canonical_bytes(&self) -> String {
        format!(
            "{}\n{}\n{}\n{}\n{}",
            self.enabled,
            self.objects_hit,
            self.objects_written,
            self.meta_written,
            self.names_bound
        )
    }
}

impl LineageRoot {
    #[must_use]
    pub fn descriptor(&self) -> String {
        match (&self.name, &self.origin) {
            (Some(name), Some(origin)) => format!(
                "{}@{}@{}@{}:{}",
                name, origin, self.artifact_kind, self.scheme, self.root
            ),
            _ => format!("{}@{}:{}", self.artifact_kind, self.scheme, self.root),
        }
    }

    // A root node names itself by the content identity it already carries.
    pub(crate) fn node_id(&self) -> NodeId {
        NodeId(format!("{}:{}", self.scheme, self.root))
    }
}

impl LineageArtifact {
    pub(crate) fn from_path(kind: &str, path: &Path) -> io::Result<Self> {
        let bytes = fs::read(path)?;
        Ok(Self::from_bytes(kind, path, &bytes))
    }

    /// An artifact digested from bytes already in hand, named by a caller-chosen
    /// (typically output-dir-relative) path. Used for documentation pages, whose
    /// content the generator holds before writing.
    #[must_use]
    pub fn from_bytes(kind: &str, path: &Path, bytes: &[u8]) -> Self {
        Self {
            kind: kind.to_string(),
            path: path.display().to_string(),
            digest_scheme: ARTIFACT_DIGEST_SCHEME.to_string(),
            digest: blake3::hash(bytes).to_hex().to_string(),
            bytes: bytes.len() as u64,
        }
    }

    // An artifact node is named by its content digest, so tampered bytes cannot
    // keep the same node id.
    pub(crate) fn node_id(&self) -> NodeId {
        NodeId(format!("{}:{}", self.digest_scheme, self.digest))
    }
}

/// One `key = value` row of the compiler identity fingerprint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerRow {
    pub key: String,
    pub value: String,
}

/// The compiler identity that produced a build: the fingerprint plus its rows.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerPayload {
    pub fingerprint: String,
    pub rows: Vec<CompilerRow>,
}

/// A diagnostic emitted during the build.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagnosticPayload {
    pub message: String,
}

/// The replay-file relation a run's trace records about itself: where the durable
/// `.replay` trace sits relative to the sidecar, and the digest of its bytes.
///
/// Making the trace self-describing lets `verify-lineage` resolve and check the
/// trace from the graph, so a moved or tampered replay file is a named error rather
/// than a silent sibling-extension convention.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayRelation {
    /// The trace's path relative to the sidecar's own directory.
    pub path: String,
    pub scheme: String,
    pub digest: String,
}

/// The digest of a recorded run's provenance-event sequence.
///
/// The scheme, the fold over the per-event hashes, and the event count. A record
/// and a replay of the same trace produce the identical digest, so this node is
/// stable across both. `replay` names the durable trace file the digest came from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TracePayload {
    pub scheme: String,
    pub hash: String,
    pub events: usize,
    /// The durable `.replay` file this trace was written to, if the run recorded it.
    /// Absent on pre-relation sidecars, which verify against the sibling extension.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay: Option<ReplayRelation>,
}

/// The program arguments a recorded run observed, inline (they are small).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArgvPayload {
    pub args: Vec<String>,
}

/// One distinct environment variable a run observed, named by its value's digest
/// rather than the value bytes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvReadPayload {
    pub name: String,
    pub value_scheme: String,
    pub value_digest: String,
}

/// One distinct file a run read through `FileSystem`, named by the content digest
/// of the bytes actually observed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InputFilePayload {
    pub path: String,
    pub digest_scheme: String,
    pub digest: String,
    pub bytes: u64,
}

/// A produced output stream (stdout), named by the digest of the captured bytes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutputPayload {
    pub digest_scheme: String,
    pub digest: String,
    pub bytes: u64,
}

/// How a recorded run mutated a file: a full write, an append, or a removal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WriteMode {
    /// A full-content write (`write_file` / `write_bytes`); the digest names the
    /// bytes the file holds after the write.
    Write,
    /// An append; the digest names the appended chunk, not the whole file.
    Append,
    /// A removal; there is no content, so the digest is of the empty byte string.
    Remove,
}

impl WriteMode {
    #[must_use]
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::Write => WRITE_MODE_WRITE,
            Self::Append => WRITE_MODE_APPEND,
            Self::Remove => WRITE_MODE_REMOVE,
        }
    }
}

/// One file a recorded run produced, named by the digest of its committed content.
///
/// A plain [`WriteMode::Write`] can be rehashed against the file's final on-disk
/// state; an append or removal cannot (later writes may have changed the file), so
/// verification records but skips them.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FileWritePayload {
    pub path: String,
    pub mode: WriteMode,
    pub digest_scheme: String,
    pub digest: String,
    pub bytes: u64,
}

impl TracePayload {
    // A trace node names itself by its own trace hash. The replay relation is
    // descriptive metadata and never enters the identity.
    pub(crate) fn node_id(&self) -> NodeId {
        NodeId(format!("{}:{}", self.scheme, self.hash))
    }
}

/// A cellular-universe law: its birth/survival rule and step-function content hash.
///
/// The node id is that hash, so a law node needs no separate identity edge (the id
/// already is the hash the resident shows).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldLawPayload {
    pub rule: String,
    pub law_hash: String,
}

/// One evolved grid state on a branch: its position in the timeline.
///
/// The node id is the domain-tagged content hash of the grid the resident computes,
/// so two clients that reach the same grid name the same state node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldStatePayload {
    pub tick: u32,
    pub branch: u32,
    pub dims: String,
}

/// A branch point: where a fork left its parent, and whether it poked a cell.
///
/// The node id is minted over the fork's canonical encoding and the two states it
/// joins, so two forks with the same parameters and outcome coincide.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldForkPayload {
    pub parent_branch: u32,
    pub fork_tick: u32,
    pub perturbed: bool,
}

impl WorldLawPayload {
    // A law node names itself by the content hash the resident already shows.
    pub(crate) fn node_id(&self) -> NodeId {
        NodeId(self.law_hash.clone())
    }
}

impl ArgvPayload {
    // The argv node is minted over a newline-safe canonical encoding: the argument
    // count, then each argument's content digest, so an embedded newline cannot
    // forge a boundary.
    pub(crate) fn node_id(&self) -> NodeId {
        let mut canonical = self.args.len().to_string();
        for arg in &self.args {
            canonical.push('\n');
            canonical.push_str(&provenance::sha256_hex(arg.as_bytes()));
        }
        minted_id(canonical.as_bytes())
    }
}

impl EnvReadPayload {
    // Minted over the variable name digest and its scheme-tagged value digest, so a
    // changed value or a changed name moves the node.
    pub(crate) fn node_id(&self) -> NodeId {
        minted_id(
            format!(
                "{}\n{}:{}",
                provenance::sha256_hex(self.name.as_bytes()),
                self.value_scheme,
                self.value_digest
            )
            .as_bytes(),
        )
    }
}

impl InputFilePayload {
    // Named by role and content digest, so tampered input bytes cannot keep the
    // same node and identical stdout bytes cannot collide with the input node.
    pub(crate) fn node_id(&self) -> NodeId {
        NodeId(format!("input-file:{}:{}", self.digest_scheme, self.digest))
    }
}

impl OutputPayload {
    pub(crate) fn node_id(&self) -> NodeId {
        NodeId(format!("stdout:{}:{}", self.digest_scheme, self.digest))
    }
}

impl FileWritePayload {
    // Minted over the mode, path, and content digest: two writes to the same path
    // with different content move the node, and writes of the same bytes to
    // different paths stay distinct (unlike a content-addressed input file).
    pub(crate) fn node_id(&self) -> NodeId {
        minted_id(
            format!(
                "{}\n{}\n{}:{}",
                self.mode.tag(),
                self.path,
                self.digest_scheme,
                self.digest
            )
            .as_bytes(),
        )
    }
}

/// The documentation generator that rendered a manifest's pages: its format
/// identifier, so a manifest names the renderer whose output it pins.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DocsGeneratorPayload {
    pub format: String,
}

/// One doctest that ran during a documentation build.
///
/// It records where the doctest came from and the digest of its observed output.
/// The node id is minted over both, so two doctests at distinct locations stay
/// distinct even with identical output, and a changed output moves the node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DoctestPayload {
    pub location: String,
    pub output_scheme: String,
    pub output_digest: String,
}

impl DocsGeneratorPayload {
    // The generator node is minted over its format identifier.
    pub(crate) fn node_id(&self) -> NodeId {
        minted_id(self.format.as_bytes())
    }
}

impl DoctestPayload {
    pub(crate) fn node_id(&self) -> NodeId {
        minted_id(
            format!(
                "{}\n{}:{}",
                provenance::sha256_hex(self.location.as_bytes()),
                self.output_scheme,
                self.output_digest
            )
            .as_bytes(),
        )
    }
}

/// A lineage graph node: a digest-named identity carrying a per-kind payload.
///
/// The `kind` discriminant and its payload serialize as a single adjacently
/// tagged object (`{"kind": ..., "payload": {...}}`) flattened beside `id`, so the
/// on-disk shape is `{"id", "kind", "payload"}` with exactly one kind tag and a
/// typed payload that decodes with field-named errors.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Node {
    pub id: NodeId,
    #[serde(flatten)]
    pub kind: NodeKind,
}

/// The node kinds of the graph. Each carries the typed payload for that kind.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "payload", rename_all = "kebab-case")]
pub enum NodeKind {
    Request(BuildRequest),
    SourceRoot(LineageRoot),
    StdlibRoot(LineageRoot),
    PackageRoot(LineageRoot),
    CompilerIdentity(CompilerPayload),
    Artifact(LineageArtifact),
    Diagnostic(DiagnosticPayload),
    CacheSummary(LineageCache),
    Trace(TracePayload),
    Argv(ArgvPayload),
    EnvRead(EnvReadPayload),
    InputFile(InputFilePayload),
    Stdout(OutputPayload),
    FileWrite(FileWritePayload),
    WorldLaw(WorldLawPayload),
    WorldState(WorldStatePayload),
    WorldFork(WorldForkPayload),
    DocsGenerator(DocsGeneratorPayload),
    Doctest(DoctestPayload),
}

impl NodeKind {
    #[must_use]
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::Request(_) => NODE_REQUEST,
            Self::SourceRoot(_) => NODE_SOURCE_ROOT,
            Self::StdlibRoot(_) => NODE_STDLIB_ROOT,
            Self::PackageRoot(_) => NODE_PACKAGE_ROOT,
            Self::CompilerIdentity(_) => NODE_COMPILER_IDENTITY,
            Self::Artifact(_) => NODE_ARTIFACT,
            Self::Diagnostic(_) => NODE_DIAGNOSTIC,
            Self::CacheSummary(_) => NODE_CACHE_SUMMARY,
            Self::Trace(_) => NODE_TRACE,
            Self::Argv(_) => NODE_ARGV,
            Self::EnvRead(_) => NODE_ENV_READ,
            Self::InputFile(_) => NODE_INPUT_FILE,
            Self::Stdout(_) => NODE_STDOUT,
            Self::FileWrite(_) => NODE_FILE_WRITE,
            Self::WorldLaw(_) => NODE_WORLD_LAW,
            Self::WorldState(_) => NODE_WORLD_STATE,
            Self::WorldFork(_) => NODE_WORLD_FORK,
            Self::DocsGenerator(_) => NODE_DOCS_GENERATOR,
            Self::Doctest(_) => NODE_DOCTEST,
        }
    }
}

/// The operation an edge records: which producer consumed or produced what.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EdgeKind {
    /// The request consumed a root input.
    Input,
    /// The request produced an artifact.
    Produced,
    /// The request is identified by the compiler identity.
    IdentifiedBy,
    /// The request is justified by a cache summary or diagnostic.
    Justified,
}

/// A directed, kinded edge between two nodes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Edge {
    pub from: NodeId,
    pub to: NodeId,
    pub kind: EdgeKind,
}

/// The named variant of the shared graph a producer emits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Variant {
    /// A project build sidecar.
    Build,
    /// A recorded-run sidecar.
    Run,
    /// A PRISM WORLD timeline export: branchable execution-prefix states over one
    /// or more laws, with self-certifying content-hash ids.
    World,
    /// A documentation-build manifest: the roots and compiler that produced a set
    /// of pages, the generator that rendered them, and the doctests that ran.
    Docs,
}

/// The shared, versioned lineage graph: one envelope, many producers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageGraph {
    pub format: String,
    pub variant: Variant,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
}

impl LineageGraph {
    /// Stable pretty JSON for the sidecar. Byte-identical for identical inputs.
    ///
    /// # Errors
    /// Fails only if JSON serialization fails.
    pub fn to_json_string(&self) -> Result<String, Error> {
        serde_json::to_string_pretty(self).map_err(|e| Error::ResolveLineage(e.to_string()))
    }

    // --- Typed relations -------------------------------------------------------
    //
    // Queries read the graph through these accessors rather than scanning raw
    // from/to edges, so the graph's shape (one request at the center) is stated in
    // one place and the one-request assumption is checked, not ambient.

    /// The single request node, or an error when the graph has none or several.
    ///
    /// Every current graph has exactly one request at its center; making that a
    /// checked accessor means a malformed multi-request graph fails loudly rather
    /// than a query silently picking one.
    ///
    /// # Errors
    /// Fails if the graph has zero or more than one request node.
    pub fn request(&self) -> Result<&Node, Error> {
        let mut requests = self
            .nodes
            .iter()
            .filter(|node| matches!(node.kind, NodeKind::Request(_)));
        let first = requests
            .next()
            .ok_or_else(|| Error::ResolveLineage("lineage: graph has no request node".into()))?;
        if requests.next().is_some() {
            return Err(Error::ResolveLineage(
                "lineage: graph has more than one request node".into(),
            ));
        }
        Ok(first)
    }

    /// The node that produced `output`: the source of the one edge into it.
    #[must_use]
    pub fn producer_of(&self, output: &NodeId) -> Option<&Node> {
        let from = self.edges.iter().find(|edge| &edge.to == output)?;
        self.node(&from.from)
    }

    /// The nodes the request consumed as inputs.
    #[must_use]
    pub fn inputs_of(&self, request: &NodeId) -> Vec<&Node> {
        self.targets(request, EdgeKind::Input)
    }

    /// The nodes the request produced as outputs.
    #[must_use]
    pub fn outputs_of(&self, request: &NodeId) -> Vec<&Node> {
        self.targets(request, EdgeKind::Produced)
    }

    /// The compiler identity the request is stamped with, if any.
    #[must_use]
    pub fn identity_of(&self, request: &NodeId) -> Option<&Node> {
        self.targets(request, EdgeKind::IdentifiedBy)
            .into_iter()
            .next()
    }

    // The nodes reached from `from` by an edge of `kind`, in node order.
    fn targets(&self, from: &NodeId, kind: EdgeKind) -> Vec<&Node> {
        let reached: std::collections::BTreeSet<&NodeId> = self
            .edges
            .iter()
            .filter(|edge| &edge.from == from && edge.kind == kind)
            .map(|edge| &edge.to)
            .collect();
        self.nodes
            .iter()
            .filter(|node| reached.contains(&node.id))
            .collect()
    }

    // The node with this id, if present.
    pub(crate) fn node(&self, id: &NodeId) -> Option<&Node> {
        self.nodes.iter().find(|node| &node.id == id)
    }

    // The run's trace payload, if this is a run graph.
    pub(crate) fn trace(&self) -> Option<&TracePayload> {
        self.nodes.iter().find_map(|node| match &node.kind {
            NodeKind::Trace(trace) => Some(trace),
            _ => None,
        })
    }

    // The compiler identity payload, if present.
    pub(crate) fn compiler(&self) -> Option<&CompilerPayload> {
        self.nodes.iter().find_map(|node| match &node.kind {
            NodeKind::CompilerIdentity(compiler) => Some(compiler),
            _ => None,
        })
    }

    // The first request payload, for tolerant rendering that must not fail on a
    // malformed graph the way [`request`] does.
    pub(crate) fn first_request(&self) -> Option<&BuildRequest> {
        self.nodes.iter().find_map(|node| match &node.kind {
            NodeKind::Request(request) => Some(request),
            _ => None,
        })
    }

    // --- World relations -------------------------------------------------------

    /// The world-state node whose id is `id`, or whose id begins with `id` when the
    /// prefix names exactly one state (the resident shows truncated hashes, so a
    /// selector copied from the page resolves). An ambiguous prefix is an error.
    ///
    /// # Errors
    /// Fails if no state matches, or a short prefix matches more than one.
    pub(crate) fn world_state_by_selector(&self, id: &str) -> Result<&Node, Error> {
        if let Some(exact) = self
            .nodes
            .iter()
            .find(|node| matches!(node.kind, NodeKind::WorldState(_)) && node.id.0 == id)
        {
            return Ok(exact);
        }
        let mut matches = self.nodes.iter().filter(|node| {
            matches!(node.kind, NodeKind::WorldState(_)) && node.id.0.starts_with(id)
        });
        let first = matches.next().ok_or_else(|| {
            Error::ResolveLineage(format!("lineage why: no world state named `{id}`"))
        })?;
        if matches.next().is_some() {
            return Err(Error::ResolveLineage(format!(
                "lineage why: `{id}` is an ambiguous state prefix"
            )));
        }
        Ok(first)
    }

    // The single predecessor state of a state node: the world-state it reached by
    // its one input edge. A seed (tick 0) has none.
    pub(crate) fn predecessor_state(&self, state: &NodeId) -> Option<&Node> {
        self.inputs_of(state)
            .into_iter()
            .find(|node| matches!(node.kind, NodeKind::WorldState(_)))
    }

    // The law node a state stepped under: the target of its one identified-by edge.
    pub(crate) fn law_of(&self, state: &NodeId) -> Option<&WorldLawPayload> {
        match self.identity_of(state).map(|node| &node.kind) {
            Some(NodeKind::WorldLaw(law)) => Some(law),
            _ => None,
        }
    }

    // The fork nodes whose produced edge lands on `state` (the branch points whose
    // first divergent state is `state`). Empty for a state no fork diverged into.
    pub(crate) fn forks_into(&self, state: &NodeId) -> Vec<&Node> {
        let sources: std::collections::BTreeSet<&NodeId> = self
            .edges
            .iter()
            .filter(|edge| &edge.to == state && edge.kind == EdgeKind::Produced)
            .map(|edge| &edge.from)
            .collect();
        self.nodes
            .iter()
            .filter(|node| {
                matches!(node.kind, NodeKind::WorldFork(_)) && sources.contains(&node.id)
            })
            .collect()
    }

    // Every world-law node, for a timeline summary.
    pub(crate) fn world_laws(&self) -> Vec<(&NodeId, &WorldLawPayload)> {
        self.nodes
            .iter()
            .filter_map(|node| match &node.kind {
                NodeKind::WorldLaw(law) => Some((&node.id, law)),
                _ => None,
            })
            .collect()
    }

    // Every world-state node.
    pub(crate) fn world_states(&self) -> Vec<(&NodeId, &WorldStatePayload)> {
        self.nodes
            .iter()
            .filter_map(|node| match &node.kind {
                NodeKind::WorldState(state) => Some((&node.id, state)),
                _ => None,
            })
            .collect()
    }

    // Every world-fork node.
    pub(crate) fn world_forks(&self) -> Vec<(&NodeId, &WorldForkPayload)> {
        self.nodes
            .iter()
            .filter_map(|node| match &node.kind {
                NodeKind::WorldFork(fork) => Some((&node.id, fork)),
                _ => None,
            })
            .collect()
    }
}

// Merge nodes that share a digest, pin a run-to-run order over both nodes and
// edges, and seal the graph under its shared envelope. Every producer ends here so
// determinism (sorted, deduped, byte-stable serialization) is defined once.
pub(crate) fn finalize(
    variant: Variant,
    mut nodes: Vec<Node>,
    mut edges: Vec<Edge>,
) -> LineageGraph {
    nodes.sort_by(|a, b| a.id.cmp(&b.id).then_with(|| a.kind.tag().cmp(b.kind.tag())));
    nodes.dedup_by(|a, b| a.id == b.id);
    edges.sort();
    edges.dedup();
    LineageGraph {
        format: LINEAGE_GRAPH_FORMAT.to_string(),
        variant,
        nodes,
        edges,
    }
}

// The source, Std, and package roots as `(node kind, root)` pairs, in the order a
// build or run star lays them out. Shared so both variants name roots identically.
pub(crate) fn root_nodes(
    source: &LineageRoot,
    stdlib: &LineageRoot,
    packages: &[LineageRoot],
) -> Vec<(NodeKind, LineageRoot)> {
    let mut out = vec![
        (NodeKind::SourceRoot(source.clone()), source.clone()),
        (NodeKind::StdlibRoot(stdlib.clone()), stdlib.clone()),
    ];
    for package in packages {
        out.push((NodeKind::PackageRoot(package.clone()), package.clone()));
    }
    out
}

// Canonical encoding of a request: newline-separated kind tag, path, and entry.
pub(crate) fn request_node_id(request: &BuildRequest) -> NodeId {
    minted_id(
        format!(
            "{}\n{}\n{}",
            request_kind_tag(request.kind),
            request.path,
            request.entry
        )
        .as_bytes(),
    )
}

// Canonical encoding of a world fork: the kind tag, the parent branch, fork tick,
// and perturb flag, then the two states the fork joins. Minting over the joined
// state ids makes the id a pure function of the fork's outcome, so two identical
// forks coincide and any change to where it forked from or diverged to moves it.
// The web emitter mirrors this exact byte encoding so a browser-minted fork id
// equals the one this crate would mint for the same timeline.
pub(crate) fn world_fork_node_id(
    payload: &WorldForkPayload,
    parent_state: &NodeId,
    divergent_state: &NodeId,
) -> NodeId {
    minted_id(
        format!(
            "{NODE_WORLD_FORK}\n{}\n{}\n{}\n{}\n{}",
            payload.parent_branch,
            payload.fork_tick,
            payload.perturbed,
            parent_state.0,
            divergent_state.0
        )
        .as_bytes(),
    )
}

// The serde discriminant string for a request kind, in one place so identity
// minting and human rendering agree on the label.
pub(crate) fn request_kind_tag(kind: RequestKind) -> String {
    serde_json::to_value(kind)
        .ok()
        .and_then(|v| v.as_str().map(str::to_string))
        .unwrap_or_default()
}

// Recompute a content digest under the scheme the node committed to. The two
// schemes in the graph are the build artifacts' blake3 and the run protocol's
// sha256; an unrecognized scheme is a hard error, never a silent pass.
pub(crate) fn recompute_digest(scheme: &str, bytes: &[u8]) -> Result<String, Error> {
    match scheme {
        ARTIFACT_DIGEST_SCHEME => Ok(blake3::hash(bytes).to_hex().to_string()),
        EVENT_HASH_SCHEME => Ok(provenance::sha256_hex(bytes)),
        other => Err(Error::ResolveLineage(format!(
            "lineage verify: unknown digest scheme `{other}`"
        ))),
    }
}

#[must_use]
pub const fn backend_name(mlir: bool) -> &'static str {
    if mlir {
        BACKEND_MLIR
    } else {
        BACKEND_LLVM
    }
}

// The build-lineage-v1 root projection, shared by the v1 report body and adapter.
pub(crate) fn root_json(root: &LineageRoot) -> Value {
    json!({
        "role": root.role,
        "name": root.name,
        "origin": root.origin,
        "artifact_kind": root.artifact_kind,
        "scheme": root.scheme,
        "root": root.root,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // The `NodeKind::tag` consts must match the serde `rename_all` discriminants,
    // because nodes sort by (id, tag) while serializing under the serde tag.
    #[test]
    fn node_tags_match_serialization() {
        let cache = LineageCache::disabled();
        let node = Node {
            id: NodeId("x".to_string()),
            kind: NodeKind::CacheSummary(cache),
        };
        let value = serde_json::to_value(&node).unwrap();
        assert_eq!(value["kind"].as_str(), Some(node.kind.tag()));
        assert_eq!(node.kind.tag(), NODE_CACHE_SUMMARY);
    }

    // The `WriteMode::tag` consts must match the serde discriminants, for the same
    // reason `file-write` node ids fold the mode tag into their identity.
    #[test]
    fn write_mode_tags_match_serialization() {
        for mode in [WriteMode::Write, WriteMode::Append, WriteMode::Remove] {
            let value = serde_json::to_value(mode).unwrap();
            assert_eq!(value.as_str(), Some(mode.tag()));
        }
    }

    // A multi-request graph makes the typed accessor error rather than silently
    // pick one; a single-request graph resolves.
    #[test]
    fn request_accessor_rejects_zero_or_many() {
        let empty = LineageGraph {
            format: LINEAGE_GRAPH_FORMAT.to_string(),
            variant: Variant::Run,
            nodes: Vec::new(),
            edges: Vec::new(),
        };
        assert!(empty.request().is_err(), "no request must error");

        let request = |entry: &str| Node {
            id: minted_id(entry.as_bytes()),
            kind: NodeKind::Request(BuildRequest::run(Path::new(entry))),
        };
        let one = LineageGraph {
            format: LINEAGE_GRAPH_FORMAT.to_string(),
            variant: Variant::Run,
            nodes: vec![request("a.pr")],
            edges: Vec::new(),
        };
        assert!(one.request().is_ok(), "one request resolves");

        let two = LineageGraph {
            format: LINEAGE_GRAPH_FORMAT.to_string(),
            variant: Variant::Run,
            nodes: vec![request("a.pr"), request("b.pr")],
            edges: Vec::new(),
        };
        let err = two.request().unwrap_err().to_string();
        assert!(
            err.contains("more than one"),
            "many requests must error: {err}"
        );
    }
}
