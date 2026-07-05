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
//! - [`trust`]: the one signed artifact, the `name -> root` index, plus a local
//!   append-only transparency log and the `audit`/`publish` logic over them. The
//!   signature itself is produced by an external tool behind a narrow seam, so no
//!   cryptographic dependency enters the compiler.
//! - [`export`]: materialize a namespace back to canonical `.pr` text through the
//!   formatter, a faithful source-level lens over the store.
//!
//! Integrity is the hash and needs no signature: a tampered blob fails its content
//! hash on fetch ([`transport::verify`]). The only thing a hash cannot
//! self-certify is the mapping from a human name to a root hash, and that mapping
//! is the sole signed artifact.

pub mod cmd;
pub mod export;
pub mod lock;
pub mod resolve;
pub mod transport;
pub mod trust;
pub mod writer;

use std::collections::BTreeSet;

use crate::error::Error;
use crate::pkg::lock::Lock;

/// The standard library the compiler embeds, rendered as its single root hash.
///
/// This is the value a lockfile pins against ([`lock::Lock::pin_std`]): "the Std
/// this build resolved to" is exactly this fold. Recomputing it and comparing to
/// the pin is how a build tells whether it ships the same standard library the
/// lock was written for ([`std_pin_status`]).
///
/// # Errors
/// Fails only if the embedded standard library does not elaborate, a compiler bug.
pub fn stdlib_root() -> Result<String, Error> {
    Ok(crate::driver::stdlib_hash()?.root)
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
    Ok(h.defs.values().cloned().collect())
}
