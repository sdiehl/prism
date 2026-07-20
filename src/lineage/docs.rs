//! Docs-lineage collection and assembly.
//!
//! `prism docs` records what it documented into a [`DocsLineage`], then
//! [`DocsLineage::to_graph`] lifts it into the shared [`LineageGraph`] as the
//! [`Variant::Docs`] manifest written beside the pages (`<outdir>/docs.plineage`).
//! A manifest names the same roots and compiler identity a build carries, plus the
//! generator that rendered the pages, one page node per emitted page (an
//! `artifact` stamped `docs-page`, so it rehashes through the shared verifier), and
//! one doctest node per doctest that ran.
//!
//! `prism docs` is the one manifest writer; verification (`--verify-manifest` and
//! `check-world`) only reads and rehashes, never synthesizes.

use std::fs;
use std::path::{Path, PathBuf};

use crate::driver::{ArtifactIdentity, BuildIdentity};
use crate::error::Error;
use crate::lineage::provenance::{self, EVENT_HASH_SCHEME};
use crate::resolve::Root;
use crate::Config;

use super::build::{compiler_payload_of, lineage_root, source_lineage_root};
use super::graph::{
    self, DocsGeneratorPayload, DoctestPayload, Edge, EdgeKind, LineageArtifact, LineageGraph,
    LineageRoot, Node, NodeId, NodeKind, RootRole, Variant, DOCS_GENERATOR_FORMAT,
    DOCS_MANIFEST_FILE, DOCS_PAGE_KIND,
};
use super::BuildRequest;

/// One documented page, as the generator holds it before writing: its path
/// relative to the docs output directory, and its rendered bytes.
#[derive(Debug, Clone)]
pub struct DocsPageInput {
    pub path: String,
    pub bytes: Vec<u8>,
}

/// One doctest that ran: where it came from and the observable output it produced.
#[derive(Debug, Clone)]
pub struct DoctestInput {
    pub location: String,
    pub output: String,
}

/// The facts a documentation build records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocsLineage {
    pub request: BuildRequest,
    pub source: LineageRoot,
    pub stdlib: LineageRoot,
    pub packages: Vec<LineageRoot>,
    pub compiler: ArtifactIdentity,
    pub generator: DocsGeneratorPayload,
    pub pages: Vec<LineageArtifact>,
    pub doctests: Vec<DoctestPayload>,
}

/// The inputs [`DocsLineage::collect`] reads: the documented source and search path
/// (for the one identity computation), plus the rendered pages and the doctests
/// that ran.
#[derive(Debug)]
pub struct DocsLineageInput<'a> {
    pub request: BuildRequest,
    pub source: &'a str,
    pub roots: &'a [Root],
    pub cfg: &'a Config,
    pub backend: &'a str,
    pub pages: Vec<DocsPageInput>,
    pub doctests: Vec<DoctestInput>,
}

impl DocsLineage {
    /// Gather a docs manifest from the build's identity and its rendered output.
    ///
    /// The roots and compiler identity come from the one `BuildIdentity`, exactly
    /// as a build sidecar's do; the pages and doctests are digested here.
    ///
    /// # Errors
    /// Fails if source identity cannot be computed or the roots omit Std.
    pub fn collect(input: DocsLineageInput<'_>) -> Result<Self, Error> {
        let identity =
            BuildIdentity::from_source(input.source, input.roots, input.cfg, input.backend)?;
        let stdlib = identity
            .stdlib
            .as_ref()
            .map(|root| lineage_root(RootRole::Stdlib, root))
            .ok_or_else(|| {
                Error::ResolveLineage("lineage: docs roots do not include Std".into())
            })?;
        let packages = identity
            .packages
            .iter()
            .map(|root| lineage_root(RootRole::Package, root))
            .collect();
        let pages = input
            .pages
            .iter()
            .map(|page| {
                LineageArtifact::from_bytes(DOCS_PAGE_KIND, Path::new(&page.path), &page.bytes)
            })
            .collect();
        let doctests = input
            .doctests
            .iter()
            .map(|test| DoctestPayload {
                location: test.location.clone(),
                output_scheme: EVENT_HASH_SCHEME.to_string(),
                output_digest: provenance::sha256_hex(test.output.as_bytes()),
            })
            .collect();
        Ok(Self {
            request: input.request,
            source: source_lineage_root(&identity.source),
            stdlib,
            packages,
            compiler: identity.artifact,
            generator: DocsGeneratorPayload {
                format: DOCS_GENERATOR_FORMAT.to_string(),
            },
            pages,
            doctests,
        })
    }

    /// Lift the collected docs facts into the shared lineage graph.
    #[must_use]
    pub fn to_graph(&self) -> LineageGraph {
        assemble_docs(self)
    }
}

// Assemble a docs graph. Roots are the manifest's inputs; the compiler and the
// generator both identify it; the pages and the doctests are what it produced.
// Every edge fans out from the request node.
fn assemble_docs(docs: &DocsLineage) -> LineageGraph {
    let request_id = graph::request_node_id(&docs.request);
    let mut nodes = vec![Node {
        id: request_id.clone(),
        kind: NodeKind::Request(docs.request.clone()),
    }];
    let mut edges = Vec::new();

    for (role, root) in graph::root_nodes(&docs.source, &docs.stdlib, &docs.packages) {
        let id = root.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Input,
        });
        nodes.push(Node { id, kind: role });
    }

    let compiler = compiler_payload_of(&docs.compiler);
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

    let generator_id = docs.generator.node_id();
    edges.push(Edge {
        from: request_id.clone(),
        to: generator_id.clone(),
        kind: EdgeKind::IdentifiedBy,
    });
    nodes.push(Node {
        id: generator_id,
        kind: NodeKind::DocsGenerator(docs.generator.clone()),
    });

    for page in &docs.pages {
        let id = page.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Produced,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::Artifact(page.clone()),
        });
    }

    for test in &docs.doctests {
        let id = test.node_id();
        edges.push(Edge {
            from: request_id.clone(),
            to: id.clone(),
            kind: EdgeKind::Produced,
        });
        nodes.push(Node {
            id,
            kind: NodeKind::Doctest(test.clone()),
        });
    }

    graph::finalize(Variant::Docs, nodes, edges)
}

/// The manifest path for a docs output directory (`<outdir>/docs.plineage`).
#[must_use]
pub fn docs_manifest_path(outdir: &Path) -> PathBuf {
    outdir.join(DOCS_MANIFEST_FILE)
}

/// Write a docs manifest into `outdir` as `docs.plineage`.
///
/// The file is newline-terminated: the manifest is a committed artifact, and a
/// text file ending without a newline fights every tool that normalizes one on.
///
/// # Errors
/// Fails on serialization or filesystem errors.
pub fn write_docs_manifest(outdir: &Path, docs: &DocsLineage) -> Result<PathBuf, Error> {
    let path = docs_manifest_path(outdir);
    let mut body = docs.to_graph().to_json_string()?;
    body.push('\n');
    fs::write(&path, body.as_bytes()).map_err(Error::Io)?;
    Ok(path)
}

/// Confirm a stored docs manifest still names the roots the current source resolves to.
///
/// A moved dependency (or Std, or source, or compiler) root fails verification
/// rather than silently documenting against a new one.
///
/// The roots and compiler are content-addressed nodes, so a recomputed identity
/// whose node is absent from the stored graph names exactly what moved.
///
/// # Errors
/// Fails if identity cannot be recomputed, or a recomputed root/compiler node is
/// not present in the stored manifest (naming the drifted input).
pub fn verify_manifest_identity(
    stored: &LineageGraph,
    source: &str,
    roots: &[Root],
    cfg: &Config,
    backend: &str,
) -> Result<(), Error> {
    let fresh = DocsLineage::collect(DocsLineageInput {
        request: stored_request(stored)?,
        source,
        roots,
        cfg,
        backend,
        pages: Vec::new(),
        doctests: Vec::new(),
    })?;
    let stored_ids: std::collections::BTreeSet<&NodeId> =
        stored.nodes.iter().map(|node| &node.id).collect();
    for (label, id) in expected_identity_ids(&fresh) {
        if !stored_ids.contains(&id) {
            return Err(Error::ResolveLineage(format!(
                "docs verify: {label} root moved since the manifest was written \
                 (current {} is not in the manifest)",
                id.0
            )));
        }
    }
    Ok(())
}

// The request the manifest recorded, so a re-collection names the same program.
fn stored_request(stored: &LineageGraph) -> Result<BuildRequest, Error> {
    match &stored.request()?.kind {
        NodeKind::Request(request) => Ok(request.clone()),
        _ => Err(Error::ResolveLineage(
            "docs verify: manifest has no request node".into(),
        )),
    }
}

// The content-addressed node ids a fresh identity must still occupy: the source,
// Std, and package roots and the compiler identity. A doc page or doctest is not
// an identity input, so it is not checked here (rehashing covers the pages).
fn expected_identity_ids(fresh: &DocsLineage) -> Vec<(&'static str, NodeId)> {
    let mut out = vec![
        ("source", fresh.source.node_id()),
        ("stdlib", fresh.stdlib.node_id()),
    ];
    for package in &fresh.packages {
        out.push(("dependency", package.node_id()));
    }
    let compiler = compiler_payload_of(&fresh.compiler);
    out.push((
        "compiler",
        graph::minted_id(compiler.fingerprint.as_bytes()),
    ));
    out
}
