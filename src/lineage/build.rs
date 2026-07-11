//! Build-lineage collection and assembly.
//!
//! A `prism build` (and `check-world`) records the facts it already knows into a
//! [`BuildLineage`], then [`BuildLineage::to_graph`] lifts them into the shared
//! [`LineageGraph`]. Older `prism-build-lineage-v1` sidecars are lifted through the
//! same assembler by [`from_v1`], so a lifted old sidecar is byte-identical to the
//! graph a fresh build emits. This module also owns the sidecar's on-disk siting
//! (a `.plineage` beside the artifact) and the reader that decodes either format.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use crate::driver::{ArtifactIdentity, BuildIdentity, BuildRoot, NamespaceIdentity};
use crate::error::Error;
use crate::resolve::Root;
use crate::store::disk::CommitStats;
use crate::Config;

use super::graph::{
    self, CompilerPayload, CompilerRow, DiagnosticPayload, Edge, EdgeKind, LineageArtifact,
    LineageCache, LineageGraph, LineageRoot, Node, NodeKind, RootRole, Variant, LINEAGE_EXTENSION,
    LINEAGE_FORMAT, LINEAGE_GRAPH_FORMAT,
};
use super::BuildRequest;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildLineage {
    pub request: BuildRequest,
    pub source: LineageRoot,
    pub stdlib: LineageRoot,
    pub packages: Vec<LineageRoot>,
    pub compiler: ArtifactIdentity,
    pub artifacts: Vec<LineageArtifact>,
    pub cache: LineageCache,
    pub diagnostics: Vec<String>,
}

#[derive(Debug)]
pub struct BuildLineageInput<'a> {
    pub request: BuildRequest,
    pub source: &'a str,
    pub roots: &'a [Root],
    pub cfg: &'a Config,
    pub backend: &'a str,
    pub artifacts: Vec<(&'a str, PathBuf)>,
    pub cache: Option<CommitStats>,
    pub diagnostics: Vec<String>,
}

impl BuildLineage {
    /// Build the sidecar data from facts already known to the driver.
    ///
    /// # Errors
    /// Fails if source identity cannot be computed or an emitted artifact cannot
    /// be read for digesting.
    pub fn collect(input: BuildLineageInput<'_>) -> Result<Self, Error> {
        // The one identity computation: source root, Std root, package roots, and the
        // compiler/artifact identity assembled once, then read here rather than
        // re-derived from the search path.
        let identity =
            BuildIdentity::from_source(input.source, input.roots, input.cfg, input.backend)?;
        let stdlib = identity
            .stdlib
            .as_ref()
            .map(|root| lineage_root(RootRole::Stdlib, root))
            .ok_or_else(|| {
                Error::ResolveLineage("lineage: build roots do not include Std".into())
            })?;
        let packages = identity
            .packages
            .iter()
            .map(|root| lineage_root(RootRole::Package, root))
            .collect();
        let artifacts = input
            .artifacts
            .into_iter()
            .map(|(kind, path)| LineageArtifact::from_path(kind, &path))
            .collect::<io::Result<Vec<_>>>()
            .map_err(Error::Io)?;
        Ok(Self {
            request: input.request,
            source: source_lineage_root(&identity.source),
            stdlib,
            packages,
            compiler: identity.artifact,
            artifacts,
            cache: input
                .cache
                .map_or_else(LineageCache::disabled, LineageCache::from_stats),
            diagnostics: input.diagnostics,
        })
    }

    /// The build-lineage-v1 projection, still emitted inside package-world reports.
    #[must_use]
    pub fn to_json(&self) -> Value {
        json!({
            "format": LINEAGE_FORMAT,
            "request": {
                "kind": self.request.kind,
                "path": self.request.path,
                "entry": self.request.entry,
            },
            "inputs": {
                "source": graph::root_json(&self.source),
                "stdlib": graph::root_json(&self.stdlib),
                "packages": self.packages.iter().map(graph::root_json).collect::<Vec<_>>(),
            },
            "compiler": {
                "identity": self.compiler.fingerprint(),
                "rows": self.compiler.rows().into_iter().map(|row| {
                    json!({ "key": row.field.label(), "value": row.value })
                }).collect::<Vec<_>>(),
            },
            "artifacts": self.artifacts.iter().map(|artifact| {
                json!({
                    "kind": artifact.kind,
                    "path": artifact.path,
                    "digest_scheme": artifact.digest_scheme,
                    "digest": artifact.digest,
                    "bytes": artifact.bytes,
                })
            }).collect::<Vec<_>>(),
            "cache": {
                "enabled": self.cache.enabled,
                "objects_hit": self.cache.objects_hit,
                "objects_written": self.cache.objects_written,
                "meta_written": self.cache.meta_written,
                "names_bound": self.cache.names_bound,
            },
            "diagnostics": self.diagnostics,
        })
    }

    /// Lift the collected facts into the shared lineage graph.
    #[must_use]
    pub fn to_graph(&self) -> LineageGraph {
        let compiler = compiler_payload_of(&self.compiler);
        assemble(
            &self.request,
            &self.source,
            &self.stdlib,
            &self.packages,
            &compiler,
            &self.artifacts,
            &self.cache,
            &self.diagnostics,
        )
    }
}

// The single graph assembler shared by a fresh build (`to_graph`) and the v1
// adapter (`from_v1`), so a lifted old sidecar is byte-identical to the graph the
// same build would emit today. Every edge fans out from the request node: inputs
// for the roots, an identity edge for the compiler, produced edges for artifacts,
// and justification edges for the cache summary and diagnostics.
#[allow(clippy::too_many_arguments)]
fn assemble(
    request: &BuildRequest,
    source: &LineageRoot,
    stdlib: &LineageRoot,
    packages: &[LineageRoot],
    compiler: &CompilerPayload,
    artifacts: &[LineageArtifact],
    cache: &LineageCache,
    diagnostics: &[String],
) -> LineageGraph {
    let request_id = graph::request_node_id(request);
    let mut nodes = vec![Node {
        id: request_id.clone(),
        kind: NodeKind::Request(request.clone()),
    }];
    let mut edges = Vec::new();

    for (role, root) in graph::root_nodes(source, stdlib, packages) {
        let id = root.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Input,
        });
        nodes.push(Node { id, kind: role });
    }

    let compiler_id = graph::minted_id(compiler.fingerprint.as_bytes());
    edges.push(Edge {
        from: request_id.clone(),
        to: compiler_id.clone(),
        kind: EdgeKind::IdentifiedBy,
    });
    nodes.push(Node {
        id: compiler_id,
        kind: NodeKind::CompilerIdentity(compiler.clone()),
    });

    for artifact in artifacts {
        let id = artifact.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Produced,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::Artifact(artifact.clone()),
        });
    }

    let cache_id = graph::minted_id(cache.canonical_bytes().as_bytes());
    edges.push(Edge {
        from: request_id.clone(),
        to: cache_id.clone(),
        kind: EdgeKind::Justified,
    });
    nodes.push(Node {
        id: cache_id,
        kind: NodeKind::CacheSummary(*cache),
    });

    for message in diagnostics {
        let id = graph::minted_id(message.as_bytes());
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Justified,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::Diagnostic(DiagnosticPayload {
                message: message.clone(),
            }),
        });
    }

    graph::finalize(Variant::Build, nodes, edges)
}

/// Lift a build-lineage-v1 sidecar value into the typed graph.
///
/// # Errors
/// Fails if the value is not a `prism-build-lineage-v1` document or a typed field
/// fails to decode.
pub(crate) fn from_v1(value: &Value) -> Result<LineageGraph, Error> {
    if value.get("format").and_then(Value::as_str) != Some(LINEAGE_FORMAT) {
        return Err(Error::ResolveLineage(format!(
            "lineage: not a {LINEAGE_FORMAT} document"
        )));
    }
    let request = graph::decode_field::<BuildRequest>(value, "request")?;
    let inputs = &value["inputs"];
    let source = graph::decode_field::<LineageRoot>(inputs, "source")?;
    let stdlib = graph::decode_field::<LineageRoot>(inputs, "stdlib")?;
    let packages = graph::decode_field::<Vec<LineageRoot>>(inputs, "packages")?;
    let compiler = CompilerPayload {
        fingerprint: value["compiler"]["identity"]
            .as_str()
            .unwrap_or_default()
            .to_string(),
        rows: graph::decode_field::<Vec<CompilerRow>>(&value["compiler"], "rows")?,
    };
    let artifacts = graph::decode_field::<Vec<LineageArtifact>>(value, "artifacts")?;
    let cache = graph::decode_field::<LineageCache>(value, "cache")?;
    let diagnostics = graph::decode_field::<Vec<String>>(value, "diagnostics").unwrap_or_default();
    Ok(assemble(
        &request,
        &source,
        &stdlib,
        &packages,
        &compiler,
        &artifacts,
        &cache,
        &diagnostics,
    ))
}

// The compiler-identity payload for a build or run: the fingerprint plus its rows.
// One home, so build and run graphs name the compiler identically.
pub(crate) fn compiler_payload_of(identity: &ArtifactIdentity) -> CompilerPayload {
    CompilerPayload {
        fingerprint: identity.fingerprint(),
        rows: identity
            .rows()
            .into_iter()
            .map(|row| CompilerRow {
                key: row.field.label().to_string(),
                value: row.value,
            })
            .collect(),
    }
}

// A program's own namespace root as a source root node. Shared by build and run
// collection so a program is named identically whichever produced the sidecar.
pub(crate) fn source_lineage_root(source: &NamespaceIdentity) -> LineageRoot {
    LineageRoot {
        role: RootRole::Source,
        name: None,
        origin: None,
        artifact_kind: source.kind.to_string(),
        scheme: source.scheme.to_string(),
        root: source.root.clone().into_string(),
    }
}

// Project a resolved build root into a sidecar root node. Std and package roots
// differ only in the role and whether a `(name, origin)` is present; the content
// digest, scheme, and artifact kind come straight from the shared identity walk.
pub(crate) fn lineage_root(role: RootRole, root: &BuildRoot) -> LineageRoot {
    let (name, origin) = root.package.as_ref().map_or((None, None), |p| {
        (Some(p.name.clone()), Some(p.origin.clone()))
    });
    LineageRoot {
        role,
        name,
        origin,
        artifact_kind: root.artifact_kind.clone(),
        scheme: root.scheme.clone(),
        root: root.root.clone(),
    }
}

#[must_use]
pub fn sidecar_path_for(artifact: &Path) -> PathBuf {
    let file_name = artifact
        .file_name()
        .map_or_else(|| "artifact".into(), |name| name.to_string_lossy());
    let sidecar = format!("{file_name}.{LINEAGE_EXTENSION}");
    artifact.with_file_name(sidecar)
}

/// Resolve the sidecar path for `file`: `file` itself if it is a `.plineage`, its
/// sibling sidecar otherwise.
#[must_use]
pub fn sidecar_of(file: &Path) -> PathBuf {
    if file.extension().and_then(|ext| ext.to_str()) == Some(LINEAGE_EXTENSION) {
        file.to_path_buf()
    } else {
        sidecar_path_for(file)
    }
}

/// Write a lineage sidecar beside `artifact`.
///
/// # Errors
/// Fails on serialization or filesystem errors.
pub fn write_sidecar(artifact: &Path, lineage: &BuildLineage) -> Result<PathBuf, Error> {
    let path = sidecar_path_for(artifact);
    fs::write(&path, lineage.to_graph().to_json_string()?.as_bytes()).map_err(Error::Io)?;
    Ok(path)
}

/// Read and decode a lineage sidecar into the typed graph. If `file` is not itself
/// a `.plineage`, its sibling sidecar is read.
///
/// # Errors
/// Fails on filesystem or decode errors. A `prism-build-lineage-v1` sidecar is
/// lifted through `from_v1`; any other format is rejected.
pub fn read_lineage(file: &Path) -> Result<LineageGraph, Error> {
    let path = sidecar_of(file);
    let text = fs::read_to_string(&path).map_err(Error::Io)?;
    let value =
        serde_json::from_str::<Value>(&text).map_err(|e| Error::ResolveLineage(e.to_string()))?;
    match value.get("format").and_then(Value::as_str) {
        Some(LINEAGE_GRAPH_FORMAT) => serde_json::from_str::<LineageGraph>(&text)
            .map_err(|e| Error::ResolveLineage(format!("{}: {e}", path.display()))),
        Some(LINEAGE_FORMAT) => from_v1(&value),
        other => Err(Error::ResolveLineage(format!(
            "{} is not a lineage graph (format {})",
            path.display(),
            other.unwrap_or("<missing>")
        ))),
    }
}
