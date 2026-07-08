//! Verification: rehash a graph's content nodes, and close the record loop by
//! replay.
//!
//! [`verify`] rehashes the artifacts, input files, and plainly written files a
//! graph names against the bytes on disk. [`verify_run_replay`] additionally
//! confirms a run sidecar by a fresh replay, comparing the recomputed trace and
//! stdout digests and the written-file digests. [`resolve_replay_file`] resolves the
//! durable trace from the graph's self-description, with distinct errors for a
//! missing and a tampered replay file.
//!
//! Append and removal writes cannot be rehashed against a file's final state (a
//! later write may have changed it), so they are recorded but skipped, counted in a
//! distinct `skipped` category rather than silently passed.

use std::fs;
use std::path::Path;

use crate::error::Error;
use crate::provenance::TraceDigest;

use std::collections::BTreeSet;

use super::graph::{
    self, EdgeKind, LineageGraph, NodeId, NodeKind, WorldForkPayload, WriteMode, REPLAY_EXTENSION,
};

/// What a rehash pass checked.
///
/// The nodes that rehashed to their recorded digest, and the append/removal writes
/// that were recorded but not rehashable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifyReport {
    pub checked: usize,
    pub skipped: usize,
}

/// Rehash the graph's content nodes from `base_dir` and reject on mismatch.
///
/// A build sidecar's artifacts, and a run sidecar's input and written files, keep
/// their recorded paths under `base_dir`. A missing file and a changed byte are
/// distinct errors; both name the node, and a mismatch names both the recorded
/// and the recomputed digest. Append and removal writes are counted as skipped
/// rather than rehashed.
///
/// # Errors
/// Fails if a recorded file is missing, unreadable, or hashes to a different digest
/// than the graph recorded (or carries an unknown digest scheme).
pub fn verify(graph: &LineageGraph, base_dir: &Path) -> Result<VerifyReport, Error> {
    let mut checked = 0;
    let mut skipped = 0;
    for node in &graph.nodes {
        match &node.kind {
            NodeKind::Artifact(artifact) => {
                verify_content(
                    "artifact",
                    &artifact.path,
                    &base_dir.join(&artifact.path),
                    &artifact.digest_scheme,
                    &artifact.digest,
                )?;
                checked += 1;
            }
            NodeKind::InputFile(file) => {
                verify_content(
                    "input file",
                    &file.path,
                    &base_dir.join(&file.path),
                    &file.digest_scheme,
                    &file.digest,
                )?;
                checked += 1;
            }
            NodeKind::FileWrite(write) => match write.mode {
                // A plain write's digest names the file's final content, so it
                // rehashes against disk. An append or removal cannot (a later write
                // may have changed the file); it is recorded but skipped.
                WriteMode::Write => {
                    verify_content(
                        "written file",
                        &write.path,
                        &base_dir.join(&write.path),
                        &write.digest_scheme,
                        &write.digest,
                    )?;
                    checked += 1;
                }
                WriteMode::Append | WriteMode::Remove => skipped += 1,
            },
            _ => {}
        }
    }
    Ok(VerifyReport { checked, skipped })
}

/// What a structural world-timeline check confirmed: a well-formed graph.
///
/// A world timeline is not re-derived (that would re-run the wasm); its ids are
/// self-certifying content hashes, so verification is the graph invariants plus the
/// stated node counts, not a recompute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorldVerifyReport {
    pub laws: usize,
    pub states: usize,
    pub forks: usize,
}

/// Structurally verify a world timeline export.
///
/// Every edge endpoint exists, every state has exactly one law edge, every law and
/// fork id self-certifies (a law id is its hash; a fork id is the mint of its
/// payload and endpoints), and every fork's parent and divergent states resolve.
/// This checks the graph is well-formed, not that re-evolving the wasm reproduces
/// the hashes (re-derivation is left to a future phase).
///
/// # Errors
/// Fails if an edge names a missing node, a state has zero or several law edges,
/// or a fork's input/produced state does not resolve to a world state.
pub fn verify_world(graph: &LineageGraph) -> Result<WorldVerifyReport, Error> {
    let ids: std::collections::BTreeSet<&str> =
        graph.nodes.iter().map(|node| node.id.0.as_str()).collect();
    for edge in &graph.edges {
        for (role, endpoint) in [("from", &edge.from), ("to", &edge.to)] {
            if !ids.contains(endpoint.0.as_str()) {
                return Err(Error::Resolve(format!(
                    "lineage verify: world edge {role} endpoint `{}` names no node",
                    endpoint.0
                )));
            }
        }
    }

    // A law node's id must be the very hash it carries: the id is self-certifying,
    // so a law whose id and payload disagree is malformed.
    let laws = graph.world_laws();
    for (id, law) in &laws {
        if law.node_id() != **id {
            return Err(Error::Resolve(format!(
                "lineage verify: world law `{}` id does not match its hash `{}`",
                id.0, law.law_hash
            )));
        }
    }
    let law_ids: std::collections::BTreeSet<&str> =
        laws.iter().map(|(id, _)| id.0.as_str()).collect();
    let states = graph.world_states();
    for (id, state) in &states {
        let law_edges: Vec<&str> = graph
            .edges
            .iter()
            .filter(|edge| &edge.from == *id && edge.kind == EdgeKind::IdentifiedBy)
            .map(|edge| edge.to.0.as_str())
            .collect();
        if law_edges.len() != 1 {
            return Err(Error::Resolve(format!(
                "lineage verify: world state at branch {} tick {} has {} law edges, expected 1",
                state.branch,
                state.tick,
                law_edges.len()
            )));
        }
        if !law_ids.contains(law_edges[0]) {
            return Err(Error::Resolve(format!(
                "lineage verify: world state at branch {} tick {} is identified by `{}`, not a law node",
                state.branch, state.tick, law_edges[0]
            )));
        }
    }

    // Each fork joins two states: an input edge to the parent state it forked from
    // and a produced edge to its first divergent state. Both must resolve to states,
    // and the fork's id must be the mint of its payload and those two endpoints, so
    // the fork id is self-certifying like the law and state ids.
    let state_ids: std::collections::BTreeSet<&str> =
        states.iter().map(|(id, _)| id.0.as_str()).collect();
    let forks = graph.world_forks();
    for (id, fork) in &forks {
        let parent = fork_endpoint(graph, id, EdgeKind::Input, "parent", fork, &state_ids)?;
        let divergent =
            fork_endpoint(graph, id, EdgeKind::Produced, "divergent", fork, &state_ids)?;
        let minted = graph::world_fork_node_id(fork, &parent, &divergent);
        if minted != **id {
            return Err(Error::Resolve(format!(
                "lineage verify: world fork at branch {} tick {} id does not match its mint",
                fork.parent_branch, fork.fork_tick
            )));
        }
    }

    Ok(WorldVerifyReport {
        laws: law_ids.len(),
        states: states.len(),
        forks: forks.len(),
    })
}

// Resolve a fork's single `kind` edge to a state node id, failing if it is missing
// or does not land on a world state.
fn fork_endpoint(
    graph: &LineageGraph,
    fork_id: &NodeId,
    kind: EdgeKind,
    label: &str,
    fork: &WorldForkPayload,
    state_ids: &BTreeSet<&str>,
) -> Result<NodeId, Error> {
    let target = graph
        .edges
        .iter()
        .find(|edge| &edge.from == fork_id && edge.kind == kind)
        .map(|edge| &edge.to)
        .ok_or_else(|| {
            Error::Resolve(format!(
                "lineage verify: world fork at branch {} tick {} has no {label} state edge",
                fork.parent_branch, fork.fork_tick
            ))
        })?;
    if !state_ids.contains(target.0.as_str()) {
        return Err(Error::Resolve(format!(
            "lineage verify: world fork at branch {} tick {} {label} state `{}` does not resolve",
            fork.parent_branch, fork.fork_tick, target.0
        )));
    }
    Ok(target.clone())
}

// Read `resolved`, rehash under `scheme`, and reject on a missing file or a
// digest mismatch. `kind`/`label` name the node in both error styles.
fn verify_content(
    kind: &str,
    label: &str,
    resolved: &Path,
    scheme: &str,
    digest: &str,
) -> Result<(), Error> {
    let bytes = fs::read(resolved).map_err(|e| {
        Error::Resolve(format!(
            "lineage verify: missing {kind} `{}`: {e}",
            resolved.display()
        ))
    })?;
    let actual = graph::recompute_digest(scheme, &bytes)?;
    if actual != digest {
        return Err(Error::Resolve(format!(
            "lineage verify: {kind} `{label}` changed: recorded {scheme}:{digest}, \
             bytes hash to {scheme}:{actual}"
        )));
    }
    Ok(())
}

/// What a `--verify-lineage` pass confirmed.
///
/// The replayed trace, the replayed stdout, the input files rehashed from disk, and
/// the plainly written files rehashed from disk (with the appends/removals skipped).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunVerification {
    pub trace_events: usize,
    pub stdout_bytes: u64,
    pub input_files: usize,
    pub written_files: usize,
    pub skipped_writes: usize,
}

/// Verify a run sidecar against a fresh replay: compare the recomputed trace digest
/// and stdout digest, and rehash the recorded input and written files from `base_dir`.
///
/// `replayed_trace` and `replayed_stdout` come from replaying the sidecar's trace
/// against its program; the file digests are rehashed from current bytes, so this is
/// verification by replay, not by trusting the sidecar's own numbers.
///
/// # Errors
/// Fails if the graph is not a run sidecar, or any recorded digest disagrees with
/// the replay (each mismatch names the node and both digests).
pub fn verify_run_replay(
    graph: &LineageGraph,
    replayed_trace: &TraceDigest,
    replayed_stdout: &[u8],
    base_dir: &Path,
) -> Result<RunVerification, Error> {
    let trace = graph.trace().ok_or_else(|| {
        Error::Resolve("verify-lineage: not a run sidecar (no trace node)".into())
    })?;
    if trace.scheme != replayed_trace.scheme || trace.hash != replayed_trace.hash {
        return Err(Error::Resolve(format!(
            "verify-lineage: trace node changed: recorded {}:{}, replay computes {}:{}",
            trace.scheme, trace.hash, replayed_trace.scheme, replayed_trace.hash
        )));
    }

    let stdout = graph
        .nodes
        .iter()
        .find_map(|node| match &node.kind {
            NodeKind::Stdout(o) => Some(o),
            _ => None,
        })
        .ok_or_else(|| {
            Error::Resolve("verify-lineage: not a run sidecar (no stdout node)".into())
        })?;
    let actual_stdout = graph::recompute_digest(&stdout.digest_scheme, replayed_stdout)?;
    if actual_stdout != stdout.digest {
        return Err(Error::Resolve(format!(
            "verify-lineage: stdout node changed: recorded {}:{}, replay computes {}:{}",
            stdout.digest_scheme, stdout.digest, stdout.digest_scheme, actual_stdout
        )));
    }

    let mut input_files = 0;
    let mut written_files = 0;
    let mut skipped_writes = 0;
    for node in &graph.nodes {
        match &node.kind {
            NodeKind::InputFile(file) => {
                verify_content(
                    "input file",
                    &file.path,
                    &base_dir.join(&file.path),
                    &file.digest_scheme,
                    &file.digest,
                )?;
                input_files += 1;
            }
            NodeKind::FileWrite(write) => match write.mode {
                WriteMode::Write => {
                    verify_content(
                        "written file",
                        &write.path,
                        &base_dir.join(&write.path),
                        &write.digest_scheme,
                        &write.digest,
                    )?;
                    written_files += 1;
                }
                WriteMode::Append | WriteMode::Remove => skipped_writes += 1,
            },
            _ => {}
        }
    }
    Ok(RunVerification {
        trace_events: trace.events,
        stdout_bytes: stdout.bytes,
        input_files,
        written_files,
        skipped_writes,
    })
}

/// Resolve the durable `.replay` trace for a run sidecar and confirm it is intact.
///
/// A current sidecar's trace node records the replay file's relation (its path
/// relative to `sidecar_dir` and a digest of its bytes); this reads and verifies
/// that file, returning its path. A pre-relation sidecar has no such field, so this
/// falls back to the sibling `.replay` beside `sidecar` without a digest check.
///
/// # Errors
/// Fails with distinct messages when the recorded replay file is missing versus when
/// its bytes no longer match the recorded digest.
pub fn resolve_replay_file(
    graph: &LineageGraph,
    sidecar: &Path,
    sidecar_dir: &Path,
) -> Result<std::path::PathBuf, Error> {
    let Some(relation) = graph.trace().and_then(|trace| trace.replay.as_ref()) else {
        // Older sidecars, written before the trace recorded its replay relation,
        // lack the field; fall back to the sibling `.replay` beside the sidecar.
        return Ok(sidecar.with_extension(REPLAY_EXTENSION));
    };
    let path = sidecar_dir.join(&relation.path);
    let bytes = fs::read(&path).map_err(|e| {
        Error::Resolve(format!(
            "verify-lineage: replay file `{}` is missing: {e}",
            path.display()
        ))
    })?;
    let actual = graph::recompute_digest(&relation.scheme, &bytes)?;
    if actual != relation.digest {
        return Err(Error::Resolve(format!(
            "verify-lineage: replay file `{}` changed: recorded {}:{}, bytes hash to {}:{}",
            path.display(),
            relation.scheme,
            relation.digest,
            relation.scheme,
            actual
        )));
    }
    Ok(path)
}
