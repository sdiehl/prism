//! Deriving and checking the stable-migration lock manifest.
//!
//! The pure identity scheme, the manifest data model, and the drift comparison
//! live in `crate::stable_lock`; building one family's record from its `stable`
//! block lives in `syntax::desugar::stable`. This module is the orchestration that
//! ties them to the compiler front end: it parses a source for its `stable`
//! blocks, elaborates it to the one canonical identity surface (pre-optimizer
//! Core), reads each generated converter's canonical semantic hash from that
//! surface, and assembles or verifies the manifest.
//!
//! The hashes are taken exactly where every other content hash is taken, through
//! `elaborated` and `hash_program`, so a locked migration's identity is a pure
//! function of the source and cannot move with the backend, the optimizer level,
//! or the checkout root. A committed manifest is a sibling file: absent means the
//! family is not locked and not checked, exactly as an unfrozen rung is not
//! checked; present means the next build re-derives it and a mismatch is a hard
//! error.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use marginalia::Span;

use crate::core::fbip::borrow_sigs;
use crate::core::{fip_annots, hash_program, HASH_PREFIX_HEX};
use crate::error::{ErrKind, Error};
use crate::resolve::Root;
use crate::stable_lock::{first_drift, Drift, LockManifest};
use crate::syntax::desugar::family_lock;

use super::{elaborated, hash_meta};

/// The suffix appended to a source file name to name its committed lock manifest.
/// A sibling file rather than an inline badge, because the migration identities it
/// records are taken over Core and are not available to the source-only formatter.
const MANIFEST_SUFFIX: &str = ".stable-lock";

/// The committed lock manifest path for a source file: its name plus the manifest
/// suffix, so `save.pr` locks in `save.pr.stable-lock` beside it.
#[must_use]
pub fn manifest_path(source: &Path) -> PathBuf {
    let mut name: OsString = source.as_os_str().to_owned();
    name.push(MANIFEST_SUFFIX);
    PathBuf::from(name)
}

/// Derive the lock manifest for a source: every `stable` family that declares a
/// `migrations` table, recorded with its rung shape digests, adjacent edge
/// identities, and supported route identities.
///
/// # Errors
/// Fails on any front-end error or a malformed `stable` block.
pub fn derive(full: &str, roots: &[Root]) -> Result<LockManifest, Error> {
    Ok(derive_with_spans(full, roots)?.0)
}

// Derive the manifest and, alongside it, each locked family's declaration span,
// so a drift diagnostic can point at the block. The span map is not serialized; it
// exists only to place the error.
fn derive_with_spans(
    full: &str,
    roots: &[Root],
) -> Result<(LockManifest, BTreeMap<String, Span>), Error> {
    let parsed = crate::parse::parse(full)?.program;
    let (program, checked, core) = elaborated(full, roots)?;
    let defs = hash_program(
        &core,
        &hash_meta(&checked, &borrow_sigs(&program), &fip_annots(&program)),
    );
    let mut manifest = LockManifest::empty();
    let mut spans = BTreeMap::new();
    for sd in &parsed.stable {
        if let Some((lock, span)) = family_lock(sd, &defs)? {
            manifest.families.insert(sd.name.clone(), lock);
            spans.insert(sd.name.clone(), span);
        }
    }
    Ok((manifest, spans))
}

/// Re-derive `full`'s locked families and check them against a committed manifest.
///
/// Every family the manifest locks is re-derived and compared by identity; a
/// family the manifest does not lock is ignored. A drifted identity is a hard
/// [`ErrKind::StableLockDrift`], naming the changed direction, the old and new
/// component hashes, and the derived loss paths.
///
/// # Errors
/// Fails on any front-end error, a malformed block, or a locked family that
/// drifted.
pub fn verify(full: &str, roots: &[Root], committed: &LockManifest) -> Result<(), Error> {
    let (derived, spans) = derive_with_spans(full, roots)?;
    if let Some(drift) = first_drift(committed, &derived) {
        let span = spans.get(&drift.family).copied().unwrap_or_default();
        return Err(drift_error(&drift, span));
    }
    Ok(())
}

/// Read the committed lock manifest beside `source`, or `None` when the family is
/// unlocked (no manifest file).
///
/// # Errors
/// Fails on a filesystem error or a malformed or foreign-format manifest.
pub fn read_committed(source: &Path) -> Result<Option<LockManifest>, Error> {
    let path = manifest_path(source);
    match std::fs::read_to_string(&path) {
        Ok(text) => LockManifest::from_text(&text)
            .map(Some)
            .map_err(Error::ResolveCommand),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(Error::Io(e)),
    }
}

/// Enforce a committed lock manifest beside `source` if one exists; a no-op when
/// the family is unlocked. The build-time enforcement hook.
///
/// # Errors
/// Fails on any front-end error, a malformed block, or a locked family that
/// drifted.
pub fn enforce(source: &Path, full: &str, roots: &[Root]) -> Result<(), Error> {
    read_committed(source)?.map_or(Ok(()), |committed| verify(full, roots, &committed))
}

// Render a drift into its diagnostic, truncating each identity to the display
// width the `core-hash`/`shape` dumps use so the message stays readable while
// remaining a deterministic function of the source.
fn drift_error(drift: &Drift, span: Span) -> Error {
    let changes = drift
        .changes
        .iter()
        .map(|c| format!("{}: {} -> {}", c.label, short(&c.old), short(&c.new)))
        .collect::<Vec<_>>()
        .join("\n  ");
    let loss = if drift.loss.is_empty() {
        "none".to_string()
    } else {
        drift.loss.join(", ")
    };
    ErrKind::StableLockDrift {
        block: drift.family.clone(),
        edge: drift.edge.clone(),
        changes,
        loss,
    }
    .at(span)
    .into()
}

// The leading nibbles of a hash, matching the human-facing dump width. A short
// marker (`absent`, `removed`) passes through unchanged.
fn short(hash: &str) -> String {
    if hash.len() > HASH_PREFIX_HEX && hash.bytes().all(|b| b.is_ascii_hexdigit()) {
        format!("{}...", &hash[..HASH_PREFIX_HEX])
    } else {
        hash.to_string()
    }
}
