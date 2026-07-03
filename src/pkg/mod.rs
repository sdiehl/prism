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
