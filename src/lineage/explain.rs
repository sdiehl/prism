//! `why-output`: explain a single output by walking the graph backward.
//!
//! An output selector (the literal `stdout`, or a path matched against artifact,
//! input-file, and file-write nodes) resolves to a node; the query walks back to
//! the single request that produced it and gathers that request's inputs and
//! identity into an [`Explanation`]. The answer is a typed value built purely from
//! the graph, so it explains an output even after its source files have moved on
//! disk, and a `--json` projection cannot drift from the human rendering.

use serde::{Deserialize, Serialize};

use crate::error::Error;

use super::graph::{
    ArgvPayload, CompilerPayload, EnvReadPayload, FileWritePayload, InputFilePayload,
    LineageArtifact, LineageGraph, LineageRoot, NodeKind, OutputPayload, TracePayload,
    WorldStatePayload, STDOUT_SELECTOR,
};
use super::BuildRequest;

/// The output node a `why-output` query resolved to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", tag = "kind", content = "payload")]
pub enum SelectedOutput {
    /// A run's captured stdout.
    Stdout(OutputPayload),
    /// A built artifact, matched by path.
    Artifact(LineageArtifact),
    /// An input file, matched by path (a run consumed it).
    InputFile(InputFilePayload),
    /// A file the run produced, matched by path.
    FileWrite(FileWritePayload),
}

impl SelectedOutput {
    pub(crate) fn node_id(&self) -> super::graph::NodeId {
        match self {
            Self::Stdout(o) => o.node_id(),
            Self::Artifact(a) => a.node_id(),
            Self::InputFile(f) => f.node_id(),
            Self::FileWrite(w) => w.node_id(),
        }
    }

    pub(crate) fn describe(&self) -> String {
        match self {
            Self::Stdout(o) => format!("stdout ({}:{})", o.digest_scheme, o.digest),
            Self::Artifact(a) => format!("artifact {}", a.path),
            Self::InputFile(f) => format!("input file {}", f.path),
            Self::FileWrite(w) => format!("written file {}", w.path),
        }
    }
}

/// The backward explanation of one output.
///
/// The request that produced it, the inputs it consumed grouped and sorted, and the
/// compiler identity that stamped it. Built purely from the graph, so it explains an
/// output even after its source files have moved on disk.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Explanation {
    pub selected: SelectedOutput,
    pub request: BuildRequest,
    pub source: Option<LineageRoot>,
    pub stdlib: Option<LineageRoot>,
    pub packages: Vec<LineageRoot>,
    pub argv: Option<ArgvPayload>,
    pub env_reads: Vec<EnvReadPayload>,
    pub input_files: Vec<InputFilePayload>,
    pub trace: Option<TracePayload>,
    pub compiler: Option<CompilerPayload>,
}

/// Explain why `selector` exists: walk backward from the named output to the
/// request that produced it, then gather that request's inputs and identity.
///
/// `selector` is either the literal `stdout` (a run's stdout node) or a path
/// matched against artifact, file-write, and input-file nodes. The walk never
/// touches the filesystem; only rendering later mentions on-disk paths.
///
/// # Errors
/// Fails if the graph has no single request, the selector's producer is not that
/// request, or the selector matches no output node (the error lists every
/// selectable output).
pub fn why_output(graph: &LineageGraph, selector: &str) -> Result<Explanation, Error> {
    let selected = select_output(graph, selector)?;
    // The one-request invariant is checked here; the selected output must hang off
    // that request (in these single-request stars, every output does).
    let request_node = graph.request()?;
    let NodeKind::Request(request) = &request_node.kind else {
        unreachable!("request() returns a request node")
    };
    let produced_by = graph.producer_of(&selected.node_id()).map(|node| &node.id);
    if produced_by != Some(&request_node.id) {
        return Err(Error::ResolveLineage(format!(
            "why-output: `{selector}` is not produced by the graph's request"
        )));
    }

    let mut explanation = Explanation {
        selected,
        request: request.clone(),
        source: None,
        stdlib: None,
        packages: Vec::new(),
        argv: None,
        env_reads: Vec::new(),
        input_files: Vec::new(),
        trace: None,
        compiler: None,
    };
    for input in graph.inputs_of(&request_node.id) {
        match &input.kind {
            NodeKind::SourceRoot(r) => explanation.source = Some(r.clone()),
            NodeKind::StdlibRoot(r) => explanation.stdlib = Some(r.clone()),
            NodeKind::PackageRoot(r) => explanation.packages.push(r.clone()),
            NodeKind::Argv(a) => explanation.argv = Some(a.clone()),
            NodeKind::EnvRead(e) => explanation.env_reads.push(e.clone()),
            NodeKind::InputFile(f) => explanation.input_files.push(f.clone()),
            _ => {}
        }
    }
    if let Some(NodeKind::CompilerIdentity(c)) =
        graph.identity_of(&request_node.id).map(|n| &n.kind)
    {
        explanation.compiler = Some(c.clone());
    }
    explanation.trace = graph
        .outputs_of(&request_node.id)
        .into_iter()
        .find_map(|node| match &node.kind {
            NodeKind::Trace(t) => Some(t.clone()),
            _ => None,
        });

    // Deterministic, legible ordering within each input group.
    explanation
        .packages
        .sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.root.cmp(&b.root)));
    explanation.env_reads.sort_by(|a, b| a.name.cmp(&b.name));
    explanation.input_files.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(explanation)
}

/// One compressed stretch of history: consecutive ticks under one law on a branch.
///
/// The walk emits these instead of one line per tick, so a long unbranched run
/// reads as `ticks N..M under law X`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldRun {
    pub branch: u32,
    pub from_tick: u32,
    pub to_tick: u32,
    pub law_rule: String,
    pub law_hash: String,
}

/// A fork crossed while walking a state back to the seed: where the timeline
/// branched and whether that fork poked a cell.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldForkCrossed {
    pub parent_branch: u32,
    pub fork_tick: u32,
    pub perturbed: bool,
}

/// The backward explanation of one world state: its timeline position and the
/// compressed history of laws and fork points that produced it, back to the seed.
///
/// Built purely from the graph's self-certifying ids, so it explains an exported
/// timeline with no access to the wasm that computed it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldExplanation {
    pub state_id: String,
    pub state: WorldStatePayload,
    /// Newest first: the selected state's run, then each earlier run back to the
    /// seed.
    pub runs: Vec<WorldRun>,
    /// Fork points crossed on the way back, newest first.
    pub forks: Vec<WorldForkCrossed>,
}

/// Explain a world state by walking its predecessor chain back to the seed.
///
/// `selector` names a state by its full content-hash id or an unambiguous prefix
/// (the resident shows truncated hashes). The walk follows each state's single
/// predecessor edge, reads the law it stepped under, compresses consecutive
/// same-law ticks into runs, and records any fork whose divergent state lies on
/// the chain. The graph's ids are self-certifying, so no re-derivation is needed.
///
/// # Errors
/// Fails if the selector names no world state, is an ambiguous prefix, or a state
/// on the chain carries no law edge (a malformed graph).
pub fn why_world_state(graph: &LineageGraph, selector: &str) -> Result<WorldExplanation, Error> {
    let start = graph.world_state_by_selector(selector)?;
    let NodeKind::WorldState(start_state) = &start.kind else {
        unreachable!("world_state_by_selector returns a world-state node")
    };

    // Walk the single-predecessor chain from the selected state to the seed,
    // recording each step's (tick, branch, law) and any fork it diverged from.
    let mut steps: Vec<(WorldStatePayload, String, String)> = Vec::new();
    let mut forks: Vec<WorldForkCrossed> = Vec::new();
    let mut cursor = Some(start);
    while let Some(node) = cursor {
        let NodeKind::WorldState(state) = &node.kind else {
            break;
        };
        let law = graph.law_of(&node.id).ok_or_else(|| {
            Error::ResolveLineage(format!(
                "lineage why: world state `{}` has no law edge",
                node.id.0
            ))
        })?;
        steps.push((state.clone(), law.rule.clone(), law.law_hash.clone()));
        for fork in graph.forks_into(&node.id) {
            if let NodeKind::WorldFork(f) = &fork.kind {
                forks.push(WorldForkCrossed {
                    parent_branch: f.parent_branch,
                    fork_tick: f.fork_tick,
                    perturbed: f.perturbed,
                });
            }
        }
        cursor = graph.predecessor_state(&node.id);
    }

    Ok(WorldExplanation {
        state_id: start.id.0.clone(),
        state: start_state.clone(),
        runs: compress_runs(&steps),
        forks,
    })
}

// Fold consecutive same-law steps (already newest-first) into runs, each spanning
// the tick range it covers. A run closes when the law hash changes, which is where
// a fork switched laws, so the run boundaries are the timeline's law changes.
fn compress_runs(steps: &[(WorldStatePayload, String, String)]) -> Vec<WorldRun> {
    let mut runs: Vec<WorldRun> = Vec::new();
    for (state, rule, hash) in steps {
        match runs.last_mut() {
            Some(run) if &run.law_hash == hash && run.branch == state.branch => {
                run.from_tick = run.from_tick.min(state.tick);
                run.to_tick = run.to_tick.max(state.tick);
            }
            _ => runs.push(WorldRun {
                branch: state.branch,
                from_tick: state.tick,
                to_tick: state.tick,
                law_rule: rule.clone(),
                law_hash: hash.clone(),
            }),
        }
    }
    runs
}

// Resolve a selector to a concrete output node, or fail with the available ones. A
// written file takes precedence over an input file of the same path: a program that
// reads and rewrites a file selects the output it produced.
fn select_output(graph: &LineageGraph, selector: &str) -> Result<SelectedOutput, Error> {
    if selector == STDOUT_SELECTOR {
        if let Some(stdout) = graph.nodes.iter().find_map(|node| match &node.kind {
            NodeKind::Stdout(o) => Some(o.clone()),
            _ => None,
        }) {
            return Ok(SelectedOutput::Stdout(stdout));
        }
    }
    for node in &graph.nodes {
        match &node.kind {
            NodeKind::Artifact(a) if a.path == selector => {
                return Ok(SelectedOutput::Artifact(a.clone()))
            }
            NodeKind::FileWrite(w) if w.path == selector => {
                return Ok(SelectedOutput::FileWrite(w.clone()))
            }
            _ => {}
        }
    }
    for node in &graph.nodes {
        if let NodeKind::InputFile(f) = &node.kind {
            if f.path == selector {
                return Ok(SelectedOutput::InputFile(f.clone()));
            }
        }
    }
    Err(Error::ResolveLineage(format!(
        "why-output: no output named `{selector}`; available outputs: {}",
        available_outputs(graph).join(", ")
    )))
}

// Every selectable output, in deterministic order: `stdout` when present, then
// artifact, file-write, and input-file paths sorted.
fn available_outputs(graph: &LineageGraph) -> Vec<String> {
    let mut out = Vec::new();
    if graph
        .nodes
        .iter()
        .any(|node| matches!(node.kind, NodeKind::Stdout(_)))
    {
        out.push(STDOUT_SELECTOR.to_string());
    }
    let mut paths: Vec<String> = graph
        .nodes
        .iter()
        .filter_map(|node| match &node.kind {
            NodeKind::Artifact(a) => Some(a.path.clone()),
            NodeKind::FileWrite(w) => Some(w.path.clone()),
            NodeKind::InputFile(f) => Some(f.path.clone()),
            _ => None,
        })
        .collect();
    paths.sort();
    paths.dedup();
    out.extend(paths);
    out
}
