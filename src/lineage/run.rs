//! Run-lineage collection and assembly.
//!
//! A recorded `prism run` folds its provenance events into the facts a run sidecar
//! explains: the roots and compiler identity a build carries, plus what the run
//! observed (argv, environment reads, input files), produced (stdout, file writes),
//! and the digest of its provenance-event trace. [`RunLineage::to_graph`] lays these
//! out as the same request-centered star a build uses.

use std::collections::BTreeMap;
use std::path::Path;

use crate::driver::{ArtifactIdentity, BuildIdentity};
use crate::error::Error;
use crate::provenance::{
    self, CapEvent, CapOp, EventValue, ObservationTrace, EVENT_HASH_SCHEME, OP_ENV_GETENV,
    OP_FS_APPEND_FILE, OP_FS_READ_FILE, OP_FS_READ_FILE_BYTES, OP_FS_REMOVE_FILE,
    OP_FS_WRITE_BYTES, OP_FS_WRITE_FILE,
};
use crate::resolve::Root;
use crate::Config;

use super::build::{compiler_payload_of, lineage_root, source_lineage_root};
use super::graph::{
    self, ArgvPayload, Edge, EdgeKind, EnvReadPayload, FileWritePayload, InputFilePayload,
    LineageGraph, LineageRoot, Node, NodeKind, OutputPayload, ReplayRelation, RootRole,
    TracePayload, Variant, WriteMode,
};
use super::BuildRequest;

/// The facts a recorded run explains.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunLineage {
    pub request: BuildRequest,
    pub source: LineageRoot,
    pub stdlib: LineageRoot,
    pub packages: Vec<LineageRoot>,
    pub compiler: ArtifactIdentity,
    pub argv: Vec<String>,
    pub env_reads: Vec<EnvReadPayload>,
    pub input_files: Vec<InputFilePayload>,
    pub file_writes: Vec<FileWritePayload>,
    pub stdout: OutputPayload,
    pub trace: TracePayload,
}

/// The inputs [`RunLineage::collect`] reads: the run's source and search path (for
/// the one identity computation), plus what the recorded run observed and produced.
#[derive(Debug)]
pub struct RunLineageInput<'a> {
    pub request: BuildRequest,
    pub source: &'a str,
    pub roots: &'a [Root],
    pub cfg: &'a Config,
    pub backend: &'a str,
    pub argv: Vec<String>,
    pub events: &'a [CapEvent],
    /// The run's complete ordered observation artifact.
    pub observations: &'a ObservationTrace,
    /// The run's captured stdout transcript.
    pub stdout: &'a str,
    /// The durable `.replay` file the trace was written to, if the caller recorded
    /// it, so the sidecar's trace node describes where its trace lives.
    pub replay: Option<ReplayRelation>,
}

impl RunLineage {
    /// Gather a run sidecar from the run's identity and its provenance events.
    ///
    /// The roots and compiler identity come from the one `BuildIdentity`, exactly
    /// as a build sidecar's do; the run-specific nodes are folded from the events.
    ///
    /// # Errors
    /// Fails if source identity cannot be computed or the roots omit Std.
    pub fn collect(input: RunLineageInput<'_>) -> Result<Self, Error> {
        let identity =
            BuildIdentity::from_source(input.source, input.roots, input.cfg, input.backend)?;
        let stdlib = identity
            .stdlib
            .as_ref()
            .map(|root| lineage_root(RootRole::Stdlib, root))
            .ok_or_else(|| Error::ResolveLineage("lineage: run roots do not include Std".into()))?;
        let packages = identity
            .packages
            .iter()
            .map(|root| lineage_root(RootRole::Package, root))
            .collect();
        let (env_reads, input_files) = observed_inputs(input.events);
        let file_writes = observed_outputs(input.events);
        let digest = input.observations.trace_digest();
        Ok(Self {
            request: input.request,
            source: source_lineage_root(&identity.source),
            stdlib,
            packages,
            compiler: identity.artifact,
            argv: input.argv,
            env_reads,
            input_files,
            file_writes,
            stdout: output_payload(input.stdout.as_bytes()),
            trace: TracePayload {
                scheme: digest.scheme.to_string(),
                hash: digest.hash,
                events: digest.events,
                replay: input.replay,
            },
        })
    }

    /// Lift the collected run facts into the shared lineage graph.
    #[must_use]
    pub fn to_graph(&self) -> LineageGraph {
        assemble_run(self)
    }
}

// Fold a run's provenance events into its distinct environment reads and input
// files. Only value-bearing reads produce nodes: a `file_exists` probe is an event
// in the trace digest but observes no bytes, so it names no input-file node.
fn observed_inputs(events: &[CapEvent]) -> (Vec<EnvReadPayload>, Vec<InputFilePayload>) {
    let mut env_reads = Vec::new();
    let mut input_files = Vec::new();
    for event in events {
        let arg = event.args.first().and_then(EventValue::as_str);
        let content = event.result.content_bytes();
        match (event.op, arg, content) {
            (OP_ENV_GETENV, Some(name), Some(value)) => env_reads.push(EnvReadPayload {
                name: name.to_string(),
                value_scheme: EVENT_HASH_SCHEME.to_string(),
                value_digest: provenance::sha256_hex(&value),
            }),
            (OP_FS_READ_FILE | OP_FS_READ_FILE_BYTES, Some(path), Some(bytes)) => {
                input_files.push(InputFilePayload {
                    path: path.to_string(),
                    digest_scheme: EVENT_HASH_SCHEME.to_string(),
                    digest: provenance::sha256_hex(&bytes),
                    bytes: bytes.len() as u64,
                });
            }
            _ => {}
        }
    }
    (env_reads, input_files)
}

// The write mode a provenance op label denotes, or `None` if the op is not a file
// write. One home for the op-to-mode mapping, keeping the family in sync with the
// interpreter's `write_obs` labels.
const fn write_mode_of(op: CapOp) -> Option<WriteMode> {
    match op {
        OP_FS_WRITE_FILE | OP_FS_WRITE_BYTES => Some(WriteMode::Write),
        OP_FS_APPEND_FILE => Some(WriteMode::Append),
        OP_FS_REMOVE_FILE => Some(WriteMode::Remove),
        _ => None,
    }
}

// Fold a run's write events into its produced files, one node per path (the last
// write to a path wins, so a plain write's node names the file's final content and
// rehashes against disk). An append's digest names the appended chunk; a removal
// has no content and digests the empty string.
fn observed_outputs(events: &[CapEvent]) -> Vec<FileWritePayload> {
    let mut by_path: BTreeMap<String, FileWritePayload> = BTreeMap::new();
    for event in events {
        let Some(mode) = write_mode_of(event.op) else {
            continue;
        };
        let Some(path) = event.args.first().and_then(EventValue::as_str) else {
            continue;
        };
        let content = event.result.content_bytes().unwrap_or_default();
        by_path.insert(
            path.to_string(),
            FileWritePayload {
                path: path.to_string(),
                mode,
                digest_scheme: EVENT_HASH_SCHEME.to_string(),
                digest: provenance::sha256_hex(&content),
                bytes: content.len() as u64,
            },
        );
    }
    by_path.into_values().collect()
}

fn output_payload(bytes: &[u8]) -> OutputPayload {
    OutputPayload {
        digest_scheme: EVENT_HASH_SCHEME.to_string(),
        digest: provenance::sha256_hex(bytes),
        bytes: bytes.len() as u64,
    }
}

// Assemble a run graph. Roots, argv, and observed environment/file reads are the
// run's inputs; the compiler identifies it; the trace digest, stdout, and file
// writes are what it produced. Every edge fans out from the request node.
fn assemble_run(run: &RunLineage) -> LineageGraph {
    let request_id = graph::request_node_id(&run.request);
    let mut nodes = vec![Node {
        id: request_id.clone(),
        kind: NodeKind::Request(run.request.clone()),
    }];
    let mut edges = Vec::new();

    for (role, root) in graph::root_nodes(&run.source, &run.stdlib, &run.packages) {
        let id = root.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Input,
        });
        nodes.push(Node { id, kind: role });
    }

    let compiler = compiler_payload_of(&run.compiler);
    let compiler_id = graph::minted_id(compiler.fingerprint.as_bytes());
    edges.push(Edge {
        from: request_id.clone(),
        to: compiler_id.clone(),
        kind: EdgeKind::IdentifiedBy,
    });
    nodes.push(Node {
        id: compiler_id,
        kind: NodeKind::CompilerIdentity(compiler),
    });

    let argv = ArgvPayload {
        args: run.argv.clone(),
    };
    let argv_id = argv.node_id();
    edges.push(Edge {
        from: request_id.clone(),
        to: argv_id.clone(),
        kind: EdgeKind::Input,
    });
    nodes.push(Node {
        id: argv_id,
        kind: NodeKind::Argv(argv),
    });

    for env in &run.env_reads {
        let id = env.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Input,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::EnvRead(env.clone()),
        });
    }

    for file in &run.input_files {
        let id = file.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Input,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::InputFile(file.clone()),
        });
    }

    let trace_id = run.trace.node_id();
    edges.push(Edge {
        from: request_id.clone(),
        to: trace_id.clone(),
        kind: EdgeKind::Produced,
    });
    nodes.push(Node {
        id: trace_id,
        kind: NodeKind::Trace(run.trace.clone()),
    });

    let stdout_id = run.stdout.node_id();
    edges.push(Edge {
        from: request_id.clone(),
        to: stdout_id.clone(),
        kind: EdgeKind::Produced,
    });
    nodes.push(Node {
        id: stdout_id,
        kind: NodeKind::Stdout(run.stdout.clone()),
    });

    for write in &run.file_writes {
        let id = write.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Produced,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::FileWrite(write.clone()),
        });
    }

    graph::finalize(Variant::Run, nodes, edges)
}

/// Write a run-lineage sidecar to `path`.
///
/// Unlike a build sidecar, a run sidecar is not sited beside a single artifact; the
/// caller names the path (the `--lineage` argument), so it is written verbatim.
///
/// # Errors
/// Fails on serialization or filesystem errors.
pub fn write_run_sidecar(path: &Path, run: &RunLineage) -> Result<(), Error> {
    std::fs::write(path, run.to_graph().to_json_string()?.as_bytes()).map_err(Error::Io)
}

/// The program a run sidecar was recorded against, as recorded in its request.
/// Resolving it relative to the sidecar's own directory lets a moved sidecar find
/// its sibling program.
///
/// # Errors
/// Fails if the graph has no single request node, or it is not a run request.
pub fn run_entry(graph: &LineageGraph) -> Result<String, Error> {
    match &graph.request()?.kind {
        NodeKind::Request(request) if request.kind == super::RequestKind::Run => {
            Ok(request.entry.clone())
        }
        _ => Err(Error::ResolveLineage(
            "verify-lineage: not a run sidecar (no run request)".into(),
        )),
    }
}

/// The replay-file relation for a run whose sidecar sits at `sidecar`.
///
/// The durable trace being written to `replay` is described by its path relative to
/// the sidecar's directory and the digest of `trace_bytes`.
///
/// The recorded path assumes the trace sits beside its sidecar (the CLI writes them
/// together); when it does not, verification falls back to the sibling extension.
#[must_use]
pub fn replay_relation(sidecar: &Path, replay: &Path, trace_bytes: &[u8]) -> ReplayRelation {
    let dir = sidecar.parent().unwrap_or_else(|| Path::new(""));
    let relative = replay.strip_prefix(dir).unwrap_or(replay);
    ReplayRelation {
        path: relative.display().to_string(),
        scheme: EVENT_HASH_SCHEME.to_string(),
        digest: provenance::sha256_hex(trace_bytes),
    }
}
