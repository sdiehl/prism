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

use crate::core::HASH_SCHEME;
use crate::driver::namespace_root;
use crate::error::Error;
use crate::resolve::Root;

// The manifest that pins an exported `.pr` to the namespace root it projects.
// Line-oriented and versioned, in the same house style as the store's own index
// files.
const EXPORT_HEADER: &str = "prism-pkg-export\tv1";
const MANIFEST_EXT: &str = "namespace";
const SOURCE_EXT: &str = "pr";

/// What one [`export`] wrote.
#[derive(Debug, Clone)]
pub struct ExportResult {
    /// The canonical `.pr` source file written.
    pub source_path: PathBuf,
    /// The manifest pinning the namespace root.
    pub manifest_path: PathBuf,
    /// The namespace root the exported text corresponds to.
    pub root: String,
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
    let root = namespace_root(full_src, roots)?;

    fs::create_dir_all(out_dir).map_err(Error::Io)?;
    let source_path = out_dir.join(format!("{stem}.{SOURCE_EXT}"));
    let manifest_path = out_dir.join(format!("{stem}.{MANIFEST_EXT}"));

    fs::write(&source_path, formatted.as_bytes()).map_err(Error::Io)?;
    fs::write(&manifest_path, manifest_body(&root).as_bytes()).map_err(Error::Io)?;

    Ok(ExportResult {
        source_path,
        manifest_path,
        root,
    })
}

// The manifest body: the hash scheme and the namespace root, versioned.
fn manifest_body(root: &str) -> String {
    format!("{EXPORT_HEADER}\nscheme\t{HASH_SCHEME}\nroot\t{root}\n")
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
