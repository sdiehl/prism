//! Verification caching over the content-addressed store.
//!
//! A check that passes for a content hash is recorded once and, while that hash,
//! hash scheme, and full artifact identity are unchanged, never re-run: an
//! unchanged hash under the same compiler/target/backend/flags is a recorded
//! pass rather than a fresh verification. Check cost therefore tracks the Merkle
//! closure of a change (the definitions whose hash actually moved) rather than
//! the size of the suite. This is the store-layer form of the invariant the
//! `hash_parity` gate proves and the `store_oracle` from-scratch versus
//! incremental pair backstops: equal hash implies an already-verified artifact
//! only under the identity that produced the verdict.
//!
//! This is the logic over the raw record I/O ([`Store::put_verified`](crate::store::disk::Store::put_verified) /
//! [`Store::verified`](crate::store::disk::Store::verified)): the canonical `check-kind` names in one place, and the
//! "does a passing record exist under the hash scheme in force" query the raw
//! `Vec<VerifiedRecord>` does not answer. Only passes are recorded, mirroring
//! the record layer's design: a failure is the absence of a pass, so a failing
//! check always re-runs.
//!
//! Trust: keying a skip on the content hash trusts the hasher, and that trust is
//! earned, not assumed. The hasher is gated independently and blind to itself by
//! `hash_parity` (equal hash implies byte-identical IR) and the `store_oracle`
//! pair (a from-scratch build and an incremental one emit byte-identical
//! objects), both of which compare real artifact bytes rather than hashes. A
//! false-equal hash would fail those gates first, so a verified record for a
//! hash is sound to reuse. The interpreter/native parity *gate cache* keeps a
//! deliberately hasher-independent key (source bytes plus a toolchain
//! fingerprint, `tests/common`); this store cache is the complementary layer
//! that survives edits which do not move the hash.
//!
//! The hash is pre-optimizer elaborated identity, so a verdict is keyed to what
//! the program *is*, not how it was optimized; optimizer level and every other
//! toolchain choice ride in the verification fingerprint, not the identity. A
//! record therefore vouches for a definition under the fingerprint that produced
//! it, and a toolchain or optimizer change is a fingerprint change that retires
//! the old verdict without moving the hash.

use std::io;

use crate::core::HASH_SCHEME;
use crate::driver::ArtifactIdentity;
use crate::store::disk::{Store, VerifiedRecord};

/// The checks a content hash can carry a verification for.
///
/// The canonical home for the `check-kind` strings the store's `verified/`
/// records use; every producer and consumer references these rather than
/// retyping a literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckKind {
    /// Interpreter/native output parity for the program the hash names.
    Parity,
    /// The definition's doctests.
    Doctest,
    /// A named test that exercises the definition.
    Test,
}

impl CheckKind {
    /// The `check-kind` name recorded in a [`VerifiedRecord`].
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Parity => "parity",
            Self::Doctest => "doctest",
            Self::Test => "test",
        }
    }
}

/// Structured identity for a verification verdict.
///
/// Store records persist the stable fingerprint string, but callers must arrive
/// here through [`ArtifactIdentity`] so the verifier cannot be keyed by an
/// ad-hoc backend name, path, or process-local cache token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationIdentity {
    fingerprint: String,
}

impl VerificationIdentity {
    #[must_use]
    pub fn from_artifact(identity: &ArtifactIdentity) -> Self {
        Self {
            fingerprint: identity.fingerprint(),
        }
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.fingerprint
    }
}

/// Record that `kind` passed for `hash` under the hash scheme and artifact
/// identity in force.
///
/// Only passes are recorded, so a failing check leaves no record and re-runs.
///
/// # Errors
/// Fails on a filesystem error or an ill-formed hash.
pub fn record_pass(
    store: &Store,
    hash: &str,
    kind: CheckKind,
    identity: &VerificationIdentity,
) -> io::Result<()> {
    store.put_verified(
        hash,
        &VerifiedRecord {
            kind: kind.as_str().to_string(),
            scheme: HASH_SCHEME.to_string(),
            identity: identity.as_str().to_string(),
            passed: true,
        },
    )
}

/// Whether `hash` already carries a passing `kind` record under the current
/// hash scheme and the requested artifact identity.
///
/// A scheme bump makes every older record invisible (its `scheme` field no
/// longer matches `HASH_SCHEME`), and a toolchain/target/backend/flag change
/// makes every older record invisible (its `identity` field no longer matches),
/// so a stale verdict is never served across either identity transition.
///
/// # Errors
/// Fails on a filesystem error or a malformed record.
pub fn is_verified(
    store: &Store,
    hash: &str,
    kind: CheckKind,
    identity: &VerificationIdentity,
) -> io::Result<bool> {
    Ok(store.verified(hash)?.iter().any(|r| {
        r.passed
            && r.scheme == HASH_SCHEME
            && r.identity == identity.as_str()
            && r.kind == kind.as_str()
    }))
}
