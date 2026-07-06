//! `prism export`: materialize a namespace back to canonical `.pr` text.
//!
//! The store speaks in hashes and anonymous Core; a developer sometimes needs
//! text. Export projects a namespace to a formatted `.pr` file through the
//! formatter, whose idempotent round-trip makes that text a faithful lens over the
//! store rather than a second source of truth. Beside it, a small manifest records
//! the namespace root the text corresponds to, tying the projection to the store's
//! content identity.
//!
//! The guarantee is deliberately narrow: **source-stability**. The emitted text is
//! canonical, so `export -> re-ingest -> export` is a fixpoint at the text level.
//! Hash-stability across a full store-to-text-to-store round trip is *not*
//! promised here: reconstructing surface syntax from anonymous Core (a
//! decompiler) is out of scope, so export reformats the source it is given rather
//! than decompiling the stored Core. What is stored may drop metadata that a
//! re-elaboration of the text would not reproduce, which is why decision 4 of the
//! package-manager design stays open.

use std::fs;
use std::path::{Path, PathBuf};

use crate::driver::{namespace_identity, NamespaceIdentity, NAMESPACE_ARTIFACT_KIND};
use crate::error::Error;
use crate::resolve::Root;

// The manifest that pins an exported `.pr` to the namespace identity it projects.
// Line-oriented and versioned, in the same house style as the store's own index
// files.
const EXPORT_MANIFEST_HEADER_V1: &str = "prism-pkg-export\tv1";
pub const EXPORT_MANIFEST_HEADER: &str = "prism-pkg-export\tv2";
const MANIFEST_EXT: &str = "namespace";
const SOURCE_EXT: &str = "pr";
const FIELD_SEP: char = '\t';
const KEY_SCHEME: &str = "scheme";
const KEY_KIND: &str = "kind";
const KEY_ROOT: &str = "root";

/// What one [`export`] wrote.
#[derive(Debug, Clone)]
pub struct ExportResult {
    /// The canonical `.pr` source file written.
    pub source_path: PathBuf,
    /// The manifest pinning the namespace root.
    pub manifest_path: PathBuf,
    /// The namespace root the exported text corresponds to.
    pub root: String,
    /// The hash scheme that gives `root` its meaning.
    pub scheme: &'static str,
    /// The artifact kind the root names.
    pub kind: &'static str,
}

/// Parsed identity manifest for an exported namespace projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportManifest {
    /// The hash scheme that gives `root` its meaning.
    pub scheme: String,
    /// The artifact kind the root names.
    pub kind: String,
    /// The namespace root the exported text corresponds to.
    pub root: String,
}

impl ExportManifest {
    /// Verify this manifest against a freshly recomputed namespace identity.
    ///
    /// # Errors
    /// Fails when the scheme, kind, or root differs.
    pub fn verify(&self, identity: &NamespaceIdentity) -> Result<(), Error> {
        if self.scheme != identity.scheme {
            return Err(Error::Resolve(format!(
                "export manifest uses hash scheme {}, but this namespace uses {}",
                self.scheme, identity.scheme
            )));
        }
        if self.kind != identity.kind {
            return Err(Error::Resolve(format!(
                "export manifest names artifact kind {}, but this namespace is {}",
                self.kind, identity.kind
            )));
        }
        if self.root != identity.root {
            return Err(Error::Resolve(format!(
                "export manifest pins root {}, but this namespace is {}",
                self.root, identity.root
            )));
        }
        Ok(())
    }
}

/// Parse a `.namespace` manifest written by [`export`].
///
/// # Errors
/// Fails on an unrecognized header or a missing identity field.
pub fn parse_manifest(text: &str) -> Result<ExportManifest, Error> {
    let mut lines = text.lines();
    let header = lines.next();
    if header != Some(EXPORT_MANIFEST_HEADER) && header != Some(EXPORT_MANIFEST_HEADER_V1) {
        return Err(Error::Resolve(format!(
            "export manifest: missing or unrecognized header (expected {EXPORT_MANIFEST_HEADER:?})"
        )));
    }
    let mut scheme = None;
    let mut kind = None;
    let mut root = None;
    for line in lines {
        let Some((key, value)) = line.split_once(FIELD_SEP) else {
            continue;
        };
        match key {
            KEY_SCHEME => scheme = Some(value.to_string()),
            KEY_KIND => kind = Some(value.to_string()),
            KEY_ROOT => root = Some(value.to_string()),
            _ => {}
        }
    }
    let scheme = scheme.ok_or_else(|| Error::Resolve("export manifest: missing scheme".into()))?;
    let kind = kind.unwrap_or_else(|| NAMESPACE_ARTIFACT_KIND.to_string());
    let root = root.ok_or_else(|| Error::Resolve("export manifest: missing root".into()))?;
    Ok(ExportManifest { scheme, kind, root })
}

/// Parse and verify a `.namespace` manifest against `identity`.
///
/// # Errors
/// Fails when parsing fails or when any identity field differs.
pub fn verify_manifest(text: &str, identity: &NamespaceIdentity) -> Result<ExportManifest, Error> {
    let manifest = parse_manifest(text)?;
    manifest.verify(identity)?;
    Ok(manifest)
}

/// Materialize a namespace to `out_dir`.
///
/// `user_src` is the developer's source (formatted and written as `<stem>.pr`);
/// `full_src` is the same source with the prelude prepended (elaborated to derive
/// the namespace root). Splitting them keeps the emitted text free of the prelude
/// while the root still commits to the whole elaborated program.
///
/// # Errors
/// A formatter error, a front-end error while deriving the root, or a filesystem
/// error.
pub fn export(
    user_src: &str,
    full_src: &str,
    roots: &[Root],
    out_dir: &Path,
    stem: &str,
) -> Result<ExportResult, Error> {
    let formatted = crate::fmt::format(user_src)?;
    let identity = namespace_identity(full_src, roots)?;

    fs::create_dir_all(out_dir).map_err(Error::Io)?;
    let source_path = out_dir.join(format!("{stem}.{SOURCE_EXT}"));
    let manifest_path = out_dir.join(format!("{stem}.{MANIFEST_EXT}"));

    fs::write(&source_path, formatted.as_bytes()).map_err(Error::Io)?;
    fs::write(&manifest_path, manifest_body(&identity).as_bytes()).map_err(Error::Io)?;

    Ok(ExportResult {
        source_path,
        manifest_path,
        root: identity.root,
        scheme: identity.scheme,
        kind: identity.kind,
    })
}

// The manifest body: hash scheme, artifact kind, and namespace root, versioned.
fn manifest_body(identity: &NamespaceIdentity) -> String {
    format!(
        "{EXPORT_MANIFEST_HEADER}\n{KEY_SCHEME}{FIELD_SEP}{}\n{KEY_KIND}{FIELD_SEP}{}\n{KEY_ROOT}{FIELD_SEP}{}\n",
        identity.scheme, identity.kind, identity.root
    )
}

/// The `prism export` command body: write the canonical projection and return the
/// human-facing message to print.
///
/// # Errors
/// A formatter, front-end, or filesystem error.
pub fn export_cmd(
    user_src: &str,
    full_src: &str,
    roots: &[Root],
    out_dir: &Path,
    stem: &str,
) -> Result<String, Error> {
    let r = export(user_src, full_src, roots, out_dir, stem)?;
    Ok(format!(
        "exported namespace {} (root {})\n  source   {}\n  manifest {}",
        stem,
        &r.root[..crate::core::HASH_PREFIX_HEX.min(r.root.len())],
        r.source_path.display(),
        r.manifest_path.display(),
    ))
}
