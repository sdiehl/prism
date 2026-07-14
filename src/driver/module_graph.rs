use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::error::Error;
use crate::parse::parse;
use crate::resolve::{load, Root};

use super::input::field;
use super::ROOT_MODULE_NAME;

/// Version tag for serialized compiler module-query graphs.
pub const MODULE_GRAPH_FORMAT: &str = "prism-module-query-graph-v1";
const ROOT_NODE_COUNT: usize = 1;

/// One source module and its direct import edges.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleGraphNode {
    /// Canonical dotted module name, or `<root>` for the entry source.
    pub name: String,
    /// BLAKE3 of the exact source bytes at the query trust boundary.
    pub source_digest: String,
    /// Canonical sorted direct imports.
    pub dependencies: Vec<String>,
    /// Digest over this complete node.
    pub digest: String,
}

/// Deterministic dependency graph used to schedule per-module queries.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleGraph {
    /// Versioned serialization and graph-semantics tag.
    pub format: String,
    /// Name-sorted graph nodes.
    pub nodes: Vec<ModuleGraphNode>,
    /// Digest over every ordered node and edge.
    pub digest: String,
}

/// Why one module query belongs to an invalidation closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleInvalidationCause {
    /// The module was added, removed, or its exact source/import node changed.
    InputChanged,
    /// One or more direct dependencies belong to the closure.
    DependencyChanged { dependencies: Vec<String> },
}

/// One deterministically ordered member of a module invalidation closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleInvalidation {
    /// Canonical module name.
    pub name: String,
    /// Direct or transitive reason this module query must be reconsidered.
    pub cause: ModuleInvalidationCause,
}

impl ModuleGraph {
    /// Serialize the canonical graph.
    ///
    /// # Errors
    /// Fails only if serialization of this closed structure fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Deserialize and verify a module graph.
    ///
    /// # Errors
    /// Fails on malformed JSON, a foreign format, noncanonical ordering, or any
    /// node/graph digest mismatch.
    pub fn from_json(text: &str) -> Result<Self, String> {
        let graph: Self = serde_json::from_str(text).map_err(|e| e.to_string())?;
        graph.validate()?;
        Ok(graph)
    }

    /// Compute the exact reverse-dependency closure between two raw module
    /// query graphs, including removed nodes for cache eviction explanations.
    ///
    /// # Errors
    /// Fails if either graph is malformed or self-inconsistent.
    pub fn invalidation_closure(&self, previous: &Self) -> Result<Vec<ModuleInvalidation>, String> {
        self.validate()?;
        previous.validate()?;
        let current = self
            .nodes
            .iter()
            .map(|node| (node.name.as_str(), node))
            .collect::<BTreeMap<_, _>>();
        let old = previous
            .nodes
            .iter()
            .map(|node| (node.name.as_str(), node))
            .collect::<BTreeMap<_, _>>();
        let names = current
            .keys()
            .chain(old.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let direct = names
            .into_iter()
            .filter(|name| {
                current.get(name).map(|node| &node.digest) != old.get(name).map(|node| &node.digest)
            })
            .map(str::to_string)
            .collect::<BTreeSet<_>>();

        let mut reverse = BTreeMap::<String, BTreeSet<String>>::new();
        for node in self.nodes.iter().chain(&previous.nodes) {
            for dependency in &node.dependencies {
                reverse
                    .entry(dependency.clone())
                    .or_default()
                    .insert(node.name.clone());
            }
        }
        let mut closure = direct.clone();
        let mut queue = direct.iter().cloned().collect::<VecDeque<_>>();
        while let Some(changed) = queue.pop_front() {
            if let Some(dependents) = reverse.get(&changed) {
                for dependent in dependents {
                    if closure.insert(dependent.clone()) {
                        queue.push_back(dependent.clone());
                    }
                }
            }
        }

        let invalidated = closure.clone();
        Ok(closure
            .into_iter()
            .map(|name| {
                let cause = if direct.contains(&name) {
                    ModuleInvalidationCause::InputChanged
                } else {
                    let dependencies = self
                        .nodes
                        .iter()
                        .chain(&previous.nodes)
                        .filter(|node| node.name == name)
                        .flat_map(|node| node.dependencies.iter())
                        .filter(|dependency| invalidated.contains(*dependency))
                        .cloned()
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    ModuleInvalidationCause::DependencyChanged { dependencies }
                };
                ModuleInvalidation { name, cause }
            })
            .collect())
    }

    fn validate(&self) -> Result<(), String> {
        if self.format != MODULE_GRAPH_FORMAT {
            return Err(format!("unsupported module graph format {:?}", self.format));
        }
        if !self
            .nodes
            .windows(2)
            .all(|pair| pair[0].name < pair[1].name)
        {
            return Err("module graph nodes are not in canonical order".to_string());
        }
        for node in &self.nodes {
            if !node.dependencies.windows(2).all(|pair| pair[0] < pair[1]) {
                return Err(format!(
                    "module graph dependencies for {} are not canonical",
                    node.name
                ));
            }
            let derived = node_digest(&node.name, &node.source_digest, &node.dependencies);
            if derived != node.digest {
                return Err(format!(
                    "module graph node {} has digest {}, derived {derived}",
                    node.name, node.digest
                ));
            }
        }
        let derived = graph_digest(&self.nodes);
        if derived != self.digest {
            return Err(format!(
                "module graph digest mismatch: stored {}, derived {derived}",
                self.digest
            ));
        }
        Ok(())
    }
}

/// Resolve the exact deterministic module-query graph for an entry source.
///
/// # Errors
/// Fails when the entry or any selected module cannot be parsed or loaded.
pub fn module_graph(src: &str, roots: &[Root]) -> Result<ModuleGraph, Error> {
    let root = parse(src)?.program;
    let modules = load(&root, roots)?;
    let mut nodes = Vec::with_capacity(modules.len() + ROOT_NODE_COUNT);
    nodes.push(graph_node(ROOT_MODULE_NAME, src, &root.imports));
    nodes.extend(
        modules
            .iter()
            .map(|module| graph_node(&module.path.join("."), &module.source, &module.prog.imports)),
    );
    nodes.sort_by(|a, b| a.name.cmp(&b.name));
    let digest = graph_digest(&nodes);
    Ok(ModuleGraph {
        format: MODULE_GRAPH_FORMAT.to_string(),
        nodes,
        digest,
    })
}

fn graph_node(
    name: &str,
    source: &str,
    imports: &[crate::syntax::ast::ImportDecl],
) -> ModuleGraphNode {
    let source_digest = blake3::hash(source.as_bytes()).to_hex().to_string();
    let mut dependencies = imports
        .iter()
        .map(|import| import.path.join("."))
        .collect::<Vec<_>>();
    dependencies.sort();
    dependencies.dedup();
    let digest = node_digest(name, &source_digest, &dependencies);
    ModuleGraphNode {
        name: name.to_string(),
        source_digest,
        dependencies,
        digest,
    }
}

fn node_digest(name: &str, source_digest: &str, dependencies: &[String]) -> String {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, MODULE_GRAPH_FORMAT.as_bytes());
    field(&mut hasher, name.as_bytes());
    field(&mut hasher, source_digest.as_bytes());
    for dependency in dependencies {
        field(&mut hasher, dependency.as_bytes());
    }
    hasher.finalize().to_hex().to_string()
}

fn graph_digest(nodes: &[ModuleGraphNode]) -> String {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, MODULE_GRAPH_FORMAT.as_bytes());
    for node in nodes {
        field(&mut hasher, node.name.as_bytes());
        field(&mut hasher, node.digest.as_bytes());
    }
    hasher.finalize().to_hex().to_string()
}
