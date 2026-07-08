//! `lineage --diff`: align two graphs by logical key, not by node id.
//!
//! Node ids are digests, so they never align on their own; a changed byte would
//! read as an added-and-removed pair. Each node is keyed by what it logically is (a
//! path, a name, a role, or a singleton kind), so a node whose bytes changed appears
//! once as `moved`. The result is a typed [`DiffReport`], serialized for `--json` or
//! rendered for a human by [`super::render`].

use serde::{Deserialize, Serialize};

use super::graph::{LineageGraph, Node, NodeId, NodeKind};

/// The logical identity a node keeps across two graphs.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LogicalKey {
    // Singletons per graph, one of each kind.
    Request,
    SourceRoot,
    StdlibRoot,
    Compiler,
    Argv,
    Trace,
    Stdout,
    CacheSummary,
    // Keyed by their logical name.
    PackageRoot(String),
    Artifact(String),
    InputFile(String),
    FileWrite(String),
    EnvRead(String),
    Diagnostic(String),
    // World timeline nodes align by their logical place, not their content hash: a
    // law by its rule, a state by its (branch, tick) position, a fork by where it
    // branched, so a re-evolved timeline diffs a moved state once.
    WorldLaw(String),
    WorldState(String),
    WorldFork(String),
    // Docs nodes: the generator is a singleton; a doctest aligns by its source
    // location, so a changed output moves that doctest once.
    DocsGenerator,
    Doctest(String),
}

impl LogicalKey {
    #[must_use]
    pub fn of(node: &Node) -> Self {
        match &node.kind {
            NodeKind::Request(_) => Self::Request,
            NodeKind::SourceRoot(_) => Self::SourceRoot,
            NodeKind::StdlibRoot(_) => Self::StdlibRoot,
            NodeKind::CompilerIdentity(_) => Self::Compiler,
            NodeKind::Argv(_) => Self::Argv,
            NodeKind::Trace(_) => Self::Trace,
            NodeKind::Stdout(_) => Self::Stdout,
            NodeKind::CacheSummary(_) => Self::CacheSummary,
            NodeKind::PackageRoot(r) => {
                Self::PackageRoot(r.name.clone().unwrap_or_else(|| r.root.clone()))
            }
            NodeKind::Artifact(a) => Self::Artifact(a.path.clone()),
            NodeKind::InputFile(f) => Self::InputFile(f.path.clone()),
            NodeKind::FileWrite(w) => Self::FileWrite(w.path.clone()),
            NodeKind::EnvRead(e) => Self::EnvRead(e.name.clone()),
            NodeKind::Diagnostic(d) => Self::Diagnostic(d.message.clone()),
            NodeKind::WorldLaw(l) => Self::WorldLaw(l.rule.clone()),
            NodeKind::WorldState(s) => Self::WorldState(format!("{}@{}", s.branch, s.tick)),
            NodeKind::WorldFork(f) => {
                Self::WorldFork(format!("{}@{}", f.parent_branch, f.fork_tick))
            }
            NodeKind::DocsGenerator(_) => Self::DocsGenerator,
            NodeKind::Doctest(t) => Self::Doctest(t.location.clone()),
        }
    }

    /// A short human label for a diff section.
    #[must_use]
    pub fn label(&self) -> String {
        match self {
            Self::Request => "request".to_string(),
            Self::SourceRoot => "source-root".to_string(),
            Self::StdlibRoot => "stdlib-root".to_string(),
            Self::Compiler => "compiler".to_string(),
            Self::Argv => "argv".to_string(),
            Self::Trace => "trace".to_string(),
            Self::Stdout => "stdout".to_string(),
            Self::CacheSummary => "cache-summary".to_string(),
            Self::PackageRoot(name) => format!("package-root {name}"),
            Self::Artifact(path) => format!("artifact {path}"),
            Self::InputFile(path) => format!("input-file {path}"),
            Self::FileWrite(path) => format!("file-write {path}"),
            Self::EnvRead(name) => format!("env-read {name}"),
            Self::Diagnostic(message) => format!("diagnostic {message}"),
            Self::WorldLaw(rule) => format!("world-law {rule}"),
            Self::WorldState(pos) => format!("world-state {pos}"),
            Self::WorldFork(at) => format!("world-fork {at}"),
            Self::DocsGenerator => "docs-generator".to_string(),
            Self::Doctest(location) => format!("doctest {location}"),
        }
    }
}

/// A node present in both graphs under the same key: preserved (same digest) or
/// added/removed (present in one).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffEntry {
    pub key: LogicalKey,
    pub digest: NodeId,
}

/// A node whose digest changed between the two graphs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MovedEntry {
    pub key: LogicalKey,
    pub old: NodeId,
    pub new: NodeId,
}

/// The alignment of two lineage graphs by logical key.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffReport {
    pub preserved: Vec<DiffEntry>,
    pub moved: Vec<MovedEntry>,
    pub added: Vec<DiffEntry>,
    pub removed: Vec<DiffEntry>,
}

impl DiffReport {
    /// Whether anything moved, was added, or was removed. Preserved-only diffs are
    /// clean, so this is the CI-gate verdict.
    #[must_use]
    pub const fn changed(&self) -> bool {
        !self.moved.is_empty() || !self.added.is_empty() || !self.removed.is_empty()
    }
}

/// Diff two lineage graphs by logical key.
///
/// Every node is keyed by what it logically is (a path, a name, a role, or a
/// singleton kind), not by its digest id, so a node whose bytes changed appears
/// once as `moved` rather than as an add/remove pair.
#[must_use]
pub fn diff(old: &LineageGraph, new: &LineageGraph) -> DiffReport {
    let old_map = keyed(old);
    let new_map = keyed(new);
    let mut preserved = Vec::new();
    let mut moved = Vec::new();
    let mut added = Vec::new();
    let mut removed = Vec::new();
    for (key, old_id) in &old_map {
        match new_map.get(key) {
            Some(new_id) if new_id == old_id => preserved.push(DiffEntry {
                key: key.clone(),
                digest: old_id.clone(),
            }),
            Some(new_id) => moved.push(MovedEntry {
                key: key.clone(),
                old: old_id.clone(),
                new: new_id.clone(),
            }),
            None => removed.push(DiffEntry {
                key: key.clone(),
                digest: old_id.clone(),
            }),
        }
    }
    for (key, new_id) in &new_map {
        if !old_map.contains_key(key) {
            added.push(DiffEntry {
                key: key.clone(),
                digest: new_id.clone(),
            });
        }
    }
    // The maps are already key-sorted; sort each section by key so the report is a
    // pure function of the two graphs.
    preserved.sort_by(|a, b| a.key.cmp(&b.key));
    moved.sort_by(|a, b| a.key.cmp(&b.key));
    added.sort_by(|a, b| a.key.cmp(&b.key));
    removed.sort_by(|a, b| a.key.cmp(&b.key));
    DiffReport {
        preserved,
        moved,
        added,
        removed,
    }
}

fn keyed(graph: &LineageGraph) -> std::collections::BTreeMap<LogicalKey, NodeId> {
    graph
        .nodes
        .iter()
        .map(|node| (LogicalKey::of(node), node.id.clone()))
        .collect()
}
