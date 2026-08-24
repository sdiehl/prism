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
//!
//! Every path a graph names is untrusted input here. A recorded path that claims to
//! be relative to the directory being verified must stay inside it, and the replay
//! trace, the one recorded path whose bytes are fed back into an evaluator, must be
//! relative and contained (the recorder refuses to mint any other kind).

use std::fs;
use std::path::{Component, Path, PathBuf};

use crate::provenance::TraceDigest;
use prism_syntax::error::Error;

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
                    base_dir,
                    &artifact.path,
                    &artifact.digest_scheme,
                    &artifact.digest,
                )?;
                checked += 1;
            }
            NodeKind::InputFile(file) => {
                verify_content(
                    "input file",
                    base_dir,
                    &file.path,
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
                        base_dir,
                        &write.path,
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
/// Verification checks graph invariants and node counts. Re-deriving the timeline
/// would re-run wasm, while its ids are already self-certifying content hashes.
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
/// This checks the graph is well-formed; it does not re-evolve the wasm to
/// reproduce the hashes.
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
                return Err(Error::ResolveLineage(format!(
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
            return Err(Error::ResolveLineage(format!(
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
            return Err(Error::ResolveLineage(format!(
                "lineage verify: world state at branch {} tick {} has {} law edges, expected 1",
                state.branch,
                state.tick,
                law_edges.len()
            )));
        }
        if !law_ids.contains(law_edges[0]) {
            return Err(Error::ResolveLineage(format!(
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
            return Err(Error::ResolveLineage(format!(
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
            Error::ResolveLineage(format!(
                "lineage verify: world fork at branch {} tick {} has no {label} state edge",
                fork.parent_branch, fork.fork_tick
            ))
        })?;
    if !state_ids.contains(target.0.as_str()) {
        return Err(Error::ResolveLineage(format!(
            "lineage verify: world fork at branch {} tick {} {label} state `{}` does not resolve",
            fork.parent_branch, fork.fork_tick, target.0
        )));
    }
    Ok(target.clone())
}

/// True when `path` is a non-empty relative path built only of plain (or `.`)
/// components, so joining it under a directory can never name a location outside
/// that directory.
///
/// The one containment rule, shared by the verifier and the recorder so that the
/// recorder refuses to mint a replay path no verifier would accept, rather than
/// writing a sidecar that fails only later.
#[must_use]
pub fn stays_inside(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && path
            .components()
            .all(|c| matches!(c, Component::Normal(_) | Component::CurDir))
}

// Resolve the recorded replay path against the directory it is verified under,
// failing if it is empty, absolute, or climbs out of `base_dir`.
//
// The graph is untrusted input to a verifier, and this is the path whose bytes are
// replayed rather than merely rehashed, so it may only name a
// location INSIDE `base_dir`: an absolute path (which `Path::join` would let replace
// `base_dir` outright) and any `..` component are rejected rather than normalized
// away, so what gets read and rehashed is always the file the graph literally names
// under the directory the caller chose. Containment is checked on components alone;
// a symlink inside `base_dir` is followed like any other path, exactly as the
// recording run would have.
fn resolve_under(base_dir: &Path, kind: &str, recorded: &str) -> Result<PathBuf, Error> {
    let relative = Path::new(recorded);
    if !stays_inside(relative) {
        return Err(Error::ResolveLineage(format!(
            "lineage verify: {kind} path `{recorded}` escapes the directory being verified \
             (an absolute path or a `..` component is refused, never followed)"
        )));
    }
    Ok(base_dir.join(relative))
}

// Resolve a graph-recorded content path, which the recorder writes as the location
// the recording run itself saw.
//
// A relative path is joined under `base_dir` and must stay inside it: `..` would
// name a file the caller never pointed the verifier at, and an empty path names
// nothing. An absolute path is read where it says, because that is what a build
// records for its artifacts and what a run records for the files it touched; there
// is no relative spelling of a file that lives outside the sidecar's directory.
// Rehashing is a read: what containment buys here is that the *caller's* directory
// choice is honored for every path that claims to be inside it.
fn resolve_recorded(base_dir: &Path, kind: &str, recorded: &str) -> Result<PathBuf, Error> {
    let path = Path::new(recorded);
    let contained = path.is_absolute() || stays_inside(path);
    if !contained {
        return Err(Error::ResolveLineage(format!(
            "lineage verify: {kind} path `{recorded}` escapes the directory being verified \
             (an empty path, or a relative one with a `..` component, is refused, \
             never followed)"
        )));
    }
    Ok(base_dir.join(path))
}

// Resolve `path` under `base_dir`, read it, rehash under `scheme`, and reject on an
// escaping path, a missing file, or a digest mismatch. `kind` names the node.
fn verify_content(
    kind: &str,
    base_dir: &Path,
    path: &str,
    scheme: &str,
    digest: &str,
) -> Result<(), Error> {
    let resolved = resolve_recorded(base_dir, kind, path)?;
    let bytes = fs::read(&resolved).map_err(|e| {
        Error::ResolveLineage(format!(
            "lineage verify: missing {kind} `{}`: {e}",
            resolved.display()
        ))
    })?;
    let actual = graph::recompute_digest(scheme, &bytes)?;
    if actual != digest {
        return Err(Error::ResolveLineage(format!(
            "lineage verify: {kind} `{path}` changed: recorded {scheme}:{digest}, \
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
        Error::ResolveLineage("verify-lineage: not a run sidecar (no trace node)".into())
    })?;
    if trace.scheme != replayed_trace.scheme || trace.hash != replayed_trace.hash {
        return Err(Error::ResolveLineage(format!(
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
            Error::ResolveLineage("verify-lineage: not a run sidecar (no stdout node)".into())
        })?;
    let actual_stdout = graph::recompute_digest(&stdout.digest_scheme, replayed_stdout)?;
    if actual_stdout != stdout.digest {
        return Err(Error::ResolveLineage(format!(
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
                    base_dir,
                    &file.path,
                    &file.digest_scheme,
                    &file.digest,
                )?;
                input_files += 1;
            }
            NodeKind::FileWrite(write) => match write.mode {
                WriteMode::Write => {
                    verify_content(
                        "written file",
                        base_dir,
                        &write.path,
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
/// A sidecar's trace node records the replay file's relation (its path relative to
/// `sidecar_dir` and a digest of its bytes); this reads and verifies that file,
/// returning its path.
///
/// A sidecar that does not record the relation is rejected rather than guessed at.
/// Falling back to the sibling `.replay` beside `sidecar` would verify a file the
/// graph never committed to, and would do so without a digest check: a pass that
/// checked nothing, indistinguishable from one that checked everything.
///
/// # Errors
/// Fails with distinct messages when the trace records no replay relation, when the
/// recorded path escapes `sidecar_dir`, when the file is missing, and when its bytes
/// no longer match the recorded digest.
pub fn resolve_replay_file(
    graph: &LineageGraph,
    sidecar: &Path,
    sidecar_dir: &Path,
) -> Result<PathBuf, Error> {
    let Some(relation) = graph.trace().and_then(|trace| trace.replay.as_ref()) else {
        return Err(Error::ResolveLineage(format!(
            "verify-lineage: sidecar `{}` records no replay-file relation, so its `.{}` trace \
             cannot be verified; re-record the run to produce a checkable sidecar",
            sidecar.display(),
            REPLAY_EXTENSION
        )));
    };
    let path = resolve_under(sidecar_dir, "replay file", &relation.path)?;
    let bytes = fs::read(&path).map_err(|e| {
        Error::ResolveLineage(format!(
            "verify-lineage: replay file `{}` is missing: {e}",
            path.display()
        ))
    })?;
    let actual = graph::recompute_digest(&relation.scheme, &bytes)?;
    if actual != relation.digest {
        return Err(Error::ResolveLineage(format!(
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

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{resolve_recorded, resolve_replay_file, resolve_under, stays_inside};
    use crate::graph::{self, Node, NodeId, NodeKind, TracePayload, Variant};
    use crate::provenance::EVENT_HASH_SCHEME;

    // Every escape shape a hostile graph can record: absolute, parent-climbing
    // (bare and buried), and empty. Each must be refused, never joined.
    #[test]
    fn resolve_under_refuses_a_path_that_escapes_the_verified_directory() {
        let base = Path::new("out");
        for hostile in [
            "/etc/passwd",
            "../trace.replay",
            "sub/../../trace.replay",
            "",
        ] {
            assert!(
                !stays_inside(Path::new(hostile)),
                "`{hostile}` must not count as contained"
            );
            let err = resolve_under(base, "replay file", hostile)
                .expect_err("an escaping path must be refused");
            assert!(
                err.to_string().contains("escapes"),
                "`{hostile}` must be named an escape, got: {err}"
            );
        }
    }

    #[test]
    fn resolve_under_joins_a_contained_path() {
        let resolved = resolve_under(Path::new("out"), "replay file", "sub/trace.replay")
            .expect("a plain relative path resolves");
        assert_eq!(resolved, Path::new("out").join("sub/trace.replay"));
    }

    // A content path is read where it was recorded: a build names its artifacts by
    // the absolute path it wrote them to, and no relative spelling exists for a file
    // outside the sidecar's directory. A path claiming to be relative still may not
    // climb out of the directory the caller chose.
    #[test]
    fn resolve_recorded_reads_an_absolute_path_where_it_says_and_contains_relative_ones() {
        let base = Path::new("out");
        assert_eq!(
            resolve_recorded(base, "artifact", "/tmp/build/app").expect("absolute resolves"),
            Path::new("/tmp/build/app"),
        );
        assert_eq!(
            resolve_recorded(base, "artifact", "sub/app").expect("relative resolves"),
            base.join("sub/app"),
        );
        for hostile in ["../app", "sub/../../app", ""] {
            let err = resolve_recorded(base, "artifact", hostile)
                .expect_err("a climbing or empty path must be refused");
            assert!(
                err.to_string().contains("escapes"),
                "`{hostile}` must be named an escape, got: {err}"
            );
        }
    }

    // A trace node with no replay relation must be refused outright: falling back to
    // a sibling file would verify bytes the graph never committed to.
    #[test]
    fn a_sidecar_without_a_replay_relation_is_refused() {
        let trace = Node {
            id: NodeId("ab".repeat(32)),
            kind: NodeKind::Trace(TracePayload {
                scheme: EVENT_HASH_SCHEME.to_string(),
                hash: "cd".repeat(32),
                events: 1,
                replay: None,
            }),
        };
        let graph = graph::finalize(Variant::Run, vec![trace], vec![]);
        let err = resolve_replay_file(&graph, Path::new("out/run.plineage"), Path::new("out"))
            .expect_err("a relation-free sidecar must not be guessed at");
        assert!(
            err.to_string().contains("records no replay-file relation"),
            "the refusal must name the missing relation, got: {err}"
        );
    }
}
