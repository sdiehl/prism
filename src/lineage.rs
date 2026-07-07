//! Minimal build-lineage sidecar support.
//!
//! This is deliberately a bridge, not a build system: it records the facts the
//! current explicit project-build path already knows, so an emitted artifact can
//! explain which source, Std, package roots, compiler identity, cache outcome, and
//! diagnostics produced it.

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use crate::core::HASH_SCHEME;
use crate::driver::{namespace_identity, stdlib_hash, ArtifactIdentity};
use crate::error::Error;
use crate::resolve::{Root, SourceBundleKind};
use crate::store::disk::CommitStats;
use crate::Config;

pub const LINEAGE_FORMAT: &str = "prism-build-lineage-v1";
pub const LINEAGE_EXTENSION: &str = "plineage";
const ARTIFACT_DIGEST_SCHEME: &str = "blake3";
const BACKEND_LLVM: &str = "llvm";
const BACKEND_MLIR: &str = "mlir";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildRequest {
    pub kind: String,
    pub path: String,
    pub entry: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineageRoot {
    pub role: String,
    pub name: Option<String>,
    pub origin: Option<String>,
    pub artifact_kind: String,
    pub scheme: String,
    pub root: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineageArtifact {
    pub kind: String,
    pub path: String,
    pub digest_scheme: String,
    pub digest: String,
    pub bytes: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineageCache {
    pub enabled: bool,
    pub objects_hit: usize,
    pub objects_written: usize,
    pub meta_written: usize,
    pub names_bound: usize,
}

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

impl BuildRequest {
    #[must_use]
    pub fn project(manifest: &Path, entry: &Path) -> Self {
        Self {
            kind: "project-build".to_string(),
            path: manifest.display().to_string(),
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
    pub const fn from_stats(stats: CommitStats) -> Self {
        Self {
            enabled: true,
            objects_hit: stats.objects_hit,
            objects_written: stats.objects_written,
            meta_written: stats.meta_written,
            names_bound: stats.names_bound,
        }
    }
}

impl BuildLineage {
    /// Build the sidecar data from facts already known to the driver.
    ///
    /// # Errors
    /// Fails if source identity cannot be computed or an emitted artifact cannot
    /// be read for digesting.
    pub fn collect(input: BuildLineageInput<'_>) -> Result<Self, Error> {
        let source_identity = namespace_identity(input.source, input.roots)?;
        let (stdlib, packages) = root_lineage(input.roots)?;
        let mut compiler = input
            .cfg
            .artifact_identity_for(input.backend)
            .with_source_root(source_identity.root.clone())
            .with_stdlib_root(stdlib.root.clone())
            .with_package_roots(packages.iter().map(LineageRoot::descriptor));
        compiler.backend = input.backend.to_string();
        let artifacts = input
            .artifacts
            .into_iter()
            .map(|(kind, path)| LineageArtifact::from_path(kind, &path))
            .collect::<io::Result<Vec<_>>>()
            .map_err(Error::Io)?;
        Ok(Self {
            request: input.request,
            source: LineageRoot {
                role: "source".to_string(),
                name: None,
                origin: None,
                artifact_kind: source_identity.kind.to_string(),
                scheme: source_identity.scheme.to_string(),
                root: source_identity.root,
            },
            stdlib,
            packages,
            compiler,
            artifacts,
            cache: input
                .cache
                .map_or_else(LineageCache::disabled, LineageCache::from_stats),
            diagnostics: input.diagnostics,
        })
    }

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
                "source": root_json(&self.source),
                "stdlib": root_json(&self.stdlib),
                "packages": self.packages.iter().map(root_json).collect::<Vec<_>>(),
            },
            "compiler": {
                "identity": self.compiler.fingerprint(),
                "rows": self.compiler.rows().into_iter().map(|(key, value)| {
                    json!({ "key": key, "value": value })
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

    /// Stable pretty JSON for the sidecar.
    ///
    /// # Errors
    /// Fails only if JSON serialization fails.
    pub fn to_json_string(&self) -> Result<String, Error> {
        serde_json::to_string_pretty(&self.to_json()).map_err(|e| Error::Resolve(e.to_string()))
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
}

impl LineageArtifact {
    fn from_path(kind: &str, path: &Path) -> io::Result<Self> {
        let bytes = fs::read(path)?;
        Ok(Self {
            kind: kind.to_string(),
            path: path.display().to_string(),
            digest_scheme: ARTIFACT_DIGEST_SCHEME.to_string(),
            digest: blake3::hash(&bytes).to_hex().to_string(),
            bytes: bytes.len() as u64,
        })
    }
}

fn root_json(root: &LineageRoot) -> Value {
    json!({
        "role": root.role,
        "name": root.name,
        "origin": root.origin,
        "artifact_kind": root.artifact_kind,
        "scheme": root.scheme,
        "root": root.root,
    })
}

fn root_lineage(roots: &[Root]) -> Result<(LineageRoot, Vec<LineageRoot>), Error> {
    let mut stdlib = None;
    let mut packages = Vec::new();
    let mut saw_embedded_std = false;
    for root in roots {
        match root {
            Root::Embedded(_) => saw_embedded_std = true,
            Root::Dir(_) => {}
            Root::SourceBundle { .. } => {
                if let Some(identity) = root.source_bundle_identity() {
                    match &identity.kind {
                        SourceBundleKind::Std => {
                            stdlib = Some(LineageRoot {
                                role: "stdlib".to_string(),
                                name: None,
                                origin: None,
                                artifact_kind: identity.artifact_kind.to_string(),
                                scheme: identity.scheme.clone(),
                                root: identity.root.clone(),
                            });
                        }
                        SourceBundleKind::Package { name, origin } => {
                            packages.push(LineageRoot {
                                role: "package".to_string(),
                                name: Some(name.clone()),
                                origin: Some(origin.as_str().to_string()),
                                artifact_kind: identity.artifact_kind.to_string(),
                                scheme: identity.scheme.clone(),
                                root: identity.root.clone(),
                            });
                        }
                    }
                }
            }
        }
    }
    if stdlib.is_none() && saw_embedded_std {
        stdlib = Some(LineageRoot {
            role: "stdlib".to_string(),
            name: None,
            origin: None,
            artifact_kind: "embedded-stdlib".to_string(),
            scheme: HASH_SCHEME.to_string(),
            root: stdlib_hash()?.root,
        });
    }
    packages.sort_by_key(LineageRoot::descriptor);
    stdlib
        .map(|std| (std, packages))
        .ok_or_else(|| Error::Resolve("lineage: build roots do not include Std".into()))
}

#[must_use]
pub fn sidecar_path_for(artifact: &Path) -> PathBuf {
    let file_name = artifact
        .file_name()
        .map_or_else(|| "artifact".into(), |name| name.to_string_lossy());
    let sidecar = format!("{file_name}.{LINEAGE_EXTENSION}");
    artifact.with_file_name(sidecar)
}

/// Write a lineage sidecar beside `artifact`.
///
/// # Errors
/// Fails on serialization or filesystem errors.
pub fn write_sidecar(artifact: &Path, lineage: &BuildLineage) -> Result<PathBuf, Error> {
    let path = sidecar_path_for(artifact);
    fs::write(&path, lineage.to_json_string()?.as_bytes()).map_err(Error::Io)?;
    Ok(path)
}

/// Read a lineage sidecar. If `file` is not itself a `.plineage`, read its
/// sibling sidecar.
///
/// # Errors
/// Fails on filesystem or JSON errors.
pub fn read_lineage_value(file: &Path) -> Result<Value, Error> {
    let path = if file.extension().and_then(|ext| ext.to_str()) == Some(LINEAGE_EXTENSION) {
        file.to_path_buf()
    } else {
        sidecar_path_for(file)
    };
    let text = fs::read_to_string(&path).map_err(Error::Io)?;
    let value = serde_json::from_str::<Value>(&text).map_err(|e| Error::Resolve(e.to_string()))?;
    if value.get("format").and_then(Value::as_str) != Some(LINEAGE_FORMAT) {
        return Err(Error::Resolve(format!(
            "{} is not a {LINEAGE_FORMAT} file",
            path.display()
        )));
    }
    Ok(value)
}

#[must_use]
pub fn render_human(value: &Value) -> String {
    let mut out = String::new();
    let request = &value["request"];
    let _ = writeln!(
        out,
        "lineage {}",
        request["path"].as_str().unwrap_or("<unknown>")
    );
    let _ = writeln!(
        out,
        "why: artifact exists because `{}` compiled `{}` with the recorded inputs",
        request["kind"].as_str().unwrap_or("build"),
        request["entry"].as_str().unwrap_or("<unknown>")
    );
    render_input(&mut out, "source", &value["inputs"]["source"]);
    render_input(&mut out, "stdlib", &value["inputs"]["stdlib"]);
    if let Some(packages) = value["inputs"]["packages"].as_array() {
        for package in packages {
            render_input(&mut out, "package", package);
        }
    }
    let _ = writeln!(out, "compiler:");
    if let Some(rows) = value["compiler"]["rows"].as_array() {
        for row in rows {
            let _ = writeln!(
                out,
                "  {} = {}",
                row["key"].as_str().unwrap_or("?"),
                row["value"].as_str().unwrap_or("?")
            );
        }
    }
    let _ = writeln!(out, "artifacts:");
    if let Some(artifacts) = value["artifacts"].as_array() {
        for artifact in artifacts {
            let _ = writeln!(
                out,
                "  {} {} {}:{} ({} bytes)",
                artifact["kind"].as_str().unwrap_or("artifact"),
                artifact["path"].as_str().unwrap_or("<unknown>"),
                artifact["digest_scheme"].as_str().unwrap_or("digest"),
                artifact["digest"].as_str().unwrap_or("?"),
                artifact["bytes"].as_u64().unwrap_or(0)
            );
        }
    }
    let cache = &value["cache"];
    let _ = writeln!(
        out,
        "cache: enabled={} hit={} written={}",
        cache["enabled"].as_bool().unwrap_or(false),
        cache["objects_hit"].as_u64().unwrap_or(0),
        cache["objects_written"].as_u64().unwrap_or(0)
    );
    out
}

fn render_input(out: &mut String, label: &str, value: &Value) {
    let name = value["name"].as_str().unwrap_or("-");
    let origin = value["origin"].as_str().unwrap_or("-");
    let _ = writeln!(
        out,
        "{label}: kind={} scheme={} root={} name={} origin={}",
        value["artifact_kind"].as_str().unwrap_or("?"),
        value["scheme"].as_str().unwrap_or("?"),
        value["root"].as_str().unwrap_or("?"),
        name,
        origin
    );
}

#[must_use]
pub const fn backend_name(mlir: bool) -> &'static str {
    if mlir {
        BACKEND_MLIR
    } else {
        BACKEND_LLVM
    }
}
