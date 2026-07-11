//! The package manager: the outward face of the content-addressed store.
//!
//! `src/store/` owns the *bytes* (the codec, the on-disk two-layer object store).
//! This module is what that store looks like from the outside, to a developer who
//! fetches, publishes, and audits packages. It adds no power over the store; every
//! mechanism here is transport, naming, and trust layered on the immutable
//! content-addressed objects the store already holds.
//!
//! The submodules:
//!
//! - [`writer`]: a narrow, format-preserving editor for the `[dependencies]`
//!   table of `prism.toml`, for `prism add`.
//! - [`lock`]: `prism.lock`, the committed pin of every resolved root hash. A
//!   locked hash is terminal, never re-resolved on a warm cache.
//! - [`resolve`]: the Merkle-DAG closure over pinned root hashes, read through the
//!   transport seam; no version solving, no diamond conflicts.
//! - [`cmd`]: the `prism add` and `prism why` command bodies.
//! - [`transport`]: the [`transport::Transport`] trait (fetch, publish, and index
//!   access as trait operations, never ambient IO scattered through a resolver),
//!   its disk and git-backed adapters, and the Merkle-closure push/pull that
//!   dedups against the shared standard-library baseline.
//! - [`trust`]: the one signed artifact, the package-identity -> root index, plus
//!   a local append-only transparency log and the `audit`/`publish` logic over
//!   them. The signature itself is produced by an external tool behind a narrow
//!   seam, so no cryptographic dependency enters the compiler.
//! - [`export`]: materialize a namespace back to canonical `.pr` text through the
//!   formatter, a faithful source-level lens over the store.
//!
//! Integrity is the hash and needs no signature: a tampered blob fails its content
//! hash on fetch ([`transport::verify`]). The only thing a hash cannot
//! self-certify is the mapping from a package identity to a root hash, and that
//! mapping is the sole signed artifact.

pub mod cmd;
pub mod export;
pub mod lock;
pub mod resolve;
pub mod std_source;
pub mod transport;
pub mod trust;
pub mod writer;

use std::collections::BTreeSet;
use std::io;
use std::path::Path;

use crate::core::{Digest, HASH_SCHEME};
use crate::error::Error;
use crate::flags::{DynFlags, SignMode};
use crate::pkg::lock::{Lock, LockEntry};
use crate::pkg::transport::{DiskTransport, Transport};
use crate::pkg::trust::{parse_index, verify_signature, IndexRow, Verdict, INDEX_KIND_SOURCE};
use crate::project::{DepSource, Dependency};
use crate::resolve::{Root, SourceBundleIdentity, SourceBundleOrigin};
use crate::store::disk::Store;

use std_source::decode_source_bundle;

const STD_SOURCE_LABEL_PREFIX: &str = "<stdlib ";
const PACKAGE_SOURCE_LABEL_PREFIX: &str = "<package ";

/// The standard library the compiler embeds, rendered as its single root hash.
///
/// This is the value a lockfile pins against ([`lock::Lock::pin_std`]): "the Std
/// this build resolved to" is exactly this fold. Recomputing it and comparing to
/// the pin is how a build tells whether it ships the same standard library the
/// lock was written for ([`std_pin_status`]).
///
/// # Errors
/// Fails if the Std pin uses a foreign hash scheme, or if the embedded standard
/// library does not elaborate, a compiler bug.
pub fn stdlib_root() -> Result<String, Error> {
    Ok(crate::driver::stdlib_hash()?.root.into_string())
}

/// Where a lockfile's Std pin stands against the standard library this compiler
/// embeds.
///
/// The three cases are the whole distribution story the store supports
/// today: a lock can be unpinned, agree, or disagree, and a disagreement is
/// named exactly (both roots) rather than papered over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdPin {
    /// The lock records no Std root; the build runs against the embedded stdlib.
    Unpinned,
    /// The pinned root equals the embedded stdlib's root: this build is on the
    /// standard library the lock was resolved against.
    Match,
    /// The pinned root differs from the embedded stdlib's: the compiler ships a
    /// different Std than the lock was written for. Both roots are reported.
    Mismatch { pinned: String, embedded: String },
}

/// Compare `lock`'s Std pin against the standard library this compiler embeds.
///
/// A program or package pins the Std root it was resolved against; this is the
/// check that a later build is running on that same standard library. Two locks
/// that pin different Std roots describe different worlds and are told apart here
/// rather than silently coexisting, the same way two dependency hashes do.
///
/// # Errors
/// Fails only if the embedded standard library does not elaborate, a compiler bug.
pub fn std_pin_status(lock: &Lock) -> Result<StdPin, Error> {
    let Some(pinned) = lock.std_root() else {
        return Ok(StdPin::Unpinned);
    };
    if lock.std_scheme() != Some(HASH_SCHEME) {
        lock.validate_current_scheme()?;
    }
    let embedded = stdlib_root()?;
    if pinned == embedded {
        Ok(StdPin::Match)
    } else {
        Ok(StdPin::Mismatch {
            pinned: pinned.to_string(),
            embedded,
        })
    }
}

/// Resolve the standard-library source root a project build should search.
///
/// An unpinned lock, or a pin matching this compiler's embedded stdlib, uses the
/// embedded source table. A different pin is loaded as a source bundle from the
/// configured content-addressed store, keyed by the pinned Std root.
///
/// # Errors
/// Fails when the embedded stdlib cannot be hashed, the local store cannot be
/// read, the pinned root is absent from the store, or the stored source bundle is
/// malformed.
pub fn stdlib_source_root(lock: &Lock, store_root: &Path) -> Result<Root, Error> {
    let Some(pinned) = lock.std_root() else {
        return Ok(Root::Embedded(crate::stdlib::STDLIB));
    };
    lock.validate_current_scheme()?;
    let embedded = stdlib_root()?;
    if pinned == embedded {
        return Ok(Root::Embedded(crate::stdlib::STDLIB));
    }

    let store = Store::open_or_create(store_root)?;
    let bytes = match store.get(pinned) {
        Ok(bytes) => bytes,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return Err(Error::ResolvePackage(format!(
                "prism.lock pins Std root {pinned}, but this compiler embeds {embedded} and no \
                 stdlib source bundle for {pinned} was found in {}",
                store_root.display()
            )));
        }
        Err(e) => return Err(Error::Io(e)),
    };
    let modules = decode_source_bundle(&bytes)?;
    Ok(Root::identified_source_bundle(
        std_source_label(pinned),
        SourceBundleIdentity::stdlib(HASH_SCHEME, pinned),
        modules,
    ))
}

fn std_source_label(root: &str) -> String {
    format!("{STD_SOURCE_LABEL_PREFIX}{root}>")
}

/// Resolve store-served package roots for a project's locked non-path dependencies.
///
/// Hash dependencies are exact bundle pins: the bundle's BLAKE3 digest must equal
/// the lockfile hash. Git dependencies add the signed-index check: the configured
/// index must authenticate `origin name@version -> hash` before the source bundle
/// is admitted to the module search path. Path dependencies are already
/// represented as source directories in [`crate::project::Project::dep_src_dirs`].
///
/// # Errors
/// Fails when a non-path dependency is missing from `prism.lock`, the lock row no
/// longer matches the manifest source, the package bundle is absent or malformed,
/// or a git dependency is not authenticated by the configured index policy.
pub fn package_source_roots(
    lock: &Lock,
    dependencies: &[Dependency],
    store_root: &Path,
    flags: &DynFlags,
) -> Result<Vec<Root>, Error> {
    lock.validate_current_scheme()?;
    let store = Store::open_or_create(store_root)?;
    let mut roots = Vec::new();
    for dep in dependencies {
        match &dep.source {
            DepSource::Path(_) => {}
            DepSource::Hash(hex) => {
                let entry = locked_dependency(lock, dep)?;
                if entry.hash != *hex {
                    return Err(Error::ResolvePackage(format!(
                        "dependency `{}` is pinned to {} in prism.lock but {} in prism.toml",
                        dep.name, entry.hash, hex
                    )));
                }
                roots.push(package_source_root(
                    &store,
                    &dep.name,
                    SourceBundleOrigin::HashPin,
                    &entry.hash,
                )?);
            }
            DepSource::Git { url, version } => {
                let entry = locked_dependency(lock, dep)?;
                let signed = signed_index_pointer(url, &dep.name, version, store_root, flags)?;
                if signed.scheme != entry.scheme {
                    return Err(Error::ResolvePackage(format!(
                        "signed index points {}@{} under scheme {}, but prism.lock pins {}",
                        dep.name, version, signed.scheme, entry.scheme
                    )));
                }
                if signed.root != entry.hash {
                    return Err(Error::ResolvePackage(format!(
                        "signed index points {}@{} at {}, but prism.lock pins {}",
                        dep.name, version, signed.root, entry.hash
                    )));
                }
                roots.push(package_source_root(
                    &store,
                    &dep.name,
                    SourceBundleOrigin::Git(url.clone()),
                    &entry.hash,
                )?);
            }
        }
    }
    Ok(roots)
}

fn locked_dependency<'a>(lock: &'a Lock, dep: &Dependency) -> Result<&'a LockEntry, Error> {
    let entry = lock.get(&dep.name).ok_or_else(|| {
        Error::ResolvePackage(format!(
            "dependency `{}` is not pinned in prism.lock; run `prism add` or update the lockfile",
            dep.name
        ))
    })?;
    if entry.source != dep.source {
        return Err(Error::ResolvePackage(format!(
            "dependency `{}` source changed since prism.lock was written",
            dep.name
        )));
    }
    Ok(entry)
}

fn package_source_root(
    store: &Store,
    name: &str,
    origin: SourceBundleOrigin,
    root: &str,
) -> Result<Root, Error> {
    let bytes = match store.get(root) {
        Ok(bytes) => bytes,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return Err(Error::ResolvePackage(format!(
                "dependency `{name}` is pinned to {root}, but no source bundle for {root} was found \
                 in the package store"
            )));
        }
        Err(e) => return Err(Error::Io(e)),
    };
    let got = blake3::hash(&bytes).to_hex().to_string();
    if got != root {
        return Err(Error::ResolvePackage(format!(
            "dependency `{name}` source bundle hash mismatch: lock pins {root}, store contains {got}"
        )));
    }
    let modules = decode_source_bundle(&bytes)?;
    Ok(Root::identified_source_bundle(
        package_source_label(name, root),
        SourceBundleIdentity::package_with_origin(name, origin, HASH_SCHEME, root),
        modules,
    ))
}

fn package_source_label(name: &str, root: &str) -> String {
    format!("{PACKAGE_SOURCE_LABEL_PREFIX}{name} {root}>")
}

/// Resolve a git package origin, name, and tag through the signed package index.
///
/// # Errors
/// Fails when the index is absent, has an unacceptable signature verdict, or has
/// no pointer for `origin name@version`.
pub fn signed_index_pointer(
    origin: &str,
    name: &str,
    version: &str,
    store_root: &Path,
    flags: &DynFlags,
) -> Result<IndexRow, Error> {
    let transport = DiskTransport::open(store_root)?;
    let artifact = transport.index_artifact()?.ok_or_else(|| {
        Error::ResolvePackage(format!(
            "dependency `{name}` is a git package, but no signed package index was found"
        ))
    })?;
    match verify_signature(&artifact, flags) {
        Verdict::Valid { .. } => {}
        Verdict::Unsigned if flags.sign_mode == SignMode::Unsigned => {}
        Verdict::Unsigned => {
            return Err(Error::ResolvePackage(
                "package index is unsigned; set PRISM_SIGN_MODE=unsigned only for local dev".into(),
            ));
        }
        Verdict::Invalid(msg) => {
            return Err(Error::ResolvePackage(format!(
                "package index signature did not verify: {msg}"
            )));
        }
        Verdict::Unavailable(msg) => {
            return Err(Error::ResolvePackage(format!(
                "package index signature unverifiable: {msg}"
            )));
        }
    }
    let rows = parse_index(&artifact.body);
    let row = rows
        .iter()
        .find(|row| row.origin == origin && row.name == name && row.tag == version)
        .ok_or_else(|| {
            Error::ResolvePackage(format!(
                "signed index has no pointer for {origin} {name}@{version}"
            ))
        })?;
    if row.scheme != HASH_SCHEME {
        return Err(Error::ResolvePackage(format!(
            "signed index pointer for {origin} {name}@{version} uses foreign hash scheme {}; \
             this build speaks {}",
            row.scheme, HASH_SCHEME
        )));
    }
    if row.kind != INDEX_KIND_SOURCE {
        return Err(Error::ResolvePackage(format!(
            "signed index pointer for {origin} {name}@{version} names artifact kind {}, \
             but dependency resolution requires {INDEX_KIND_SOURCE}",
            row.kind
        )));
    }
    Ok(row.clone())
}

/// The set of content hashes reachable from the shared standard-library root.
///
/// This is the zero-cost baseline both a sender and a receiver assume: everything
/// reachable from [`crate::driver::stdlib_hash`]'s root is already present on any
/// peer that speaks the same compiler, so it never travels. The push/pull closure
/// walk in [`transport`] prunes at these hashes.
///
/// # Errors
/// Fails only if the embedded standard library does not elaborate, which is a
/// compiler bug.
pub fn stdlib_baseline() -> Result<BTreeSet<String>, Error> {
    let h = crate::driver::stdlib_hash()?;
    Ok(h.defs.values().cloned().map(Digest::into_string).collect())
}
