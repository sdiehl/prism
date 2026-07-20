//! Content-addressed storage and closure verification for verification evidence.
//!
//! A receipt ([`SmtResult`]) and a certificate ([`SmtCertificate`]) are ordinary
//! immutable objects in the content-addressed store, keyed by their own digest. A
//! passing `unsat` receipt additionally binds a reuse ref keyed by the exact query
//! and solver identity, so an unchanged obligation re-verified with the same
//! pinned solver reuses the recorded pass rather than re-running the solver. Only
//! an `unsat` solver-oracle receipt is ever bound as reusable evidence.
//!
//! [`verify_closure`] is the fail-closed gate over a certificate: a receipt bound
//! to a different query, a receipt that is not a reusable `unsat`, a missing or
//! stale dependency certificate, a partial or pending dependency, a trusted
//! assumption, or a dependency cycle each yields
//! [`ClosureStatus::FailedClosed`], never a silent pass.

use std::collections::BTreeSet;
use std::io;

use crate::store::disk::Store;
use crate::verify::certificate::{ClosureStatus, Completeness, SmtCertificate};
use crate::verify::result::{SmtResult, SolverId};

/// The reuse-ref key prefix: the single home for the reusable-evidence namespace.
const RESULT_REUSE_PREFIX: &str = "smt-result";

/// The maximum dependency depth a closure walk will follow before failing closed,
/// a guard against a hostile deep or cyclic dependency graph.
const MAX_CLOSURE_DEPTH: usize = 256;

/// Store a receipt as an immutable object keyed by its digest, and, when it is
/// reusable evidence, bind the reuse ref for its exact query and solver identity.
/// Returns the receipt digest.
///
/// # Errors
/// A filesystem error or a content-hash collision (two different receipts on one
/// digest, a hashing bug).
pub(crate) fn put_result(store: &Store, result: &SmtResult) -> io::Result<String> {
    let digest = result.digest();
    store.put(&digest, &result.encode())?;
    if result.is_reusable_evidence() {
        store.set_ref(&reuse_key(&result.query_digest, &result.solver), &digest)?;
    }
    Ok(digest)
}

/// Store a certificate as an immutable object keyed by its digest. Returns the
/// certificate digest.
///
/// # Errors
/// A filesystem error or a content-hash collision.
pub(crate) fn put_certificate(store: &Store, cert: &SmtCertificate) -> io::Result<String> {
    let digest = cert.digest();
    store.put(&digest, &cert.encode())?;
    Ok(digest)
}

/// The reusable `unsat` receipt for `query_digest` under `solver`, if one is
/// recorded and still valid. Fail-closed: a dangling ref, a corrupt object, a
/// digest mismatch, a query-binding mismatch, a solver-identity mismatch, or a
/// non-`unsat` status all read as "no reusable evidence" (`None`), never a hit.
///
/// # Errors
/// A filesystem error other than a missing object.
pub(crate) fn reusable_unsat(
    store: &Store,
    query_digest: &str,
    solver: &SolverId,
) -> io::Result<Option<SmtResult>> {
    let Some(receipt_digest) = store.get_ref(&reuse_key(query_digest, solver))? else {
        return Ok(None);
    };
    let bytes = match store.get(&receipt_digest) {
        Ok(b) => b,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let Ok(result) = SmtResult::decode(&bytes) else {
        return Ok(None);
    };
    // Re-address, re-bind to the exact query and solver, and re-check the status:
    // any doubt is a cold miss, so a stale or forged ref can never serve evidence.
    let usable = result.digest() == receipt_digest
        && result.matches_query(query_digest)
        && result.solver == *solver
        && result.is_reusable_evidence();
    Ok(usable.then_some(result))
}

/// Verify a certificate's dependency closure against the store. Fail-closed.
pub(crate) fn verify_closure(store: &Store, cert: &SmtCertificate) -> ClosureStatus {
    let mut visiting = BTreeSet::new();
    verify_closure_at(store, cert, &mut visiting, 0)
}

fn verify_closure_at(
    store: &Store,
    cert: &SmtCertificate,
    visiting: &mut BTreeSet<String>,
    depth: usize,
) -> ClosureStatus {
    if depth > MAX_CLOSURE_DEPTH {
        return ClosureStatus::FailedClosed("dependency closure exceeds the depth budget".into());
    }
    let digest = cert.digest();
    if !visiting.insert(digest.clone()) {
        return ClosureStatus::FailedClosed(format!(
            "dependency cycle at certificate {}",
            short(&digest)
        ));
    }
    let verdict = match cert.completeness {
        Completeness::Pending => ClosureStatus::Incomplete(
            "certificate claims pending: an obligation is not discharged".into(),
        ),
        Completeness::Partial => ClosureStatus::Incomplete(
            "certificate claims partial: a dependency is not closed".into(),
        ),
        Completeness::Complete => verify_complete(store, cert, visiting, depth),
    };
    visiting.remove(&digest);
    verdict
}

/// The obligation, assumption, and dependency checks for a certificate that claims
/// completeness. Every branch that is not a clean pass fails closed.
fn verify_complete(
    store: &Store,
    cert: &SmtCertificate,
    visiting: &mut BTreeSet<String>,
    depth: usize,
) -> ClosureStatus {
    // A complete certificate trusts no unaccounted assumption.
    if let Some(a) = cert.assumptions.first() {
        return ClosureStatus::FailedClosed(format!(
            "complete certificate rests on a trusted assumption {}",
            short(a)
        ));
    }
    for ob in &cert.obligations {
        if ob.receipts.is_empty() {
            return ClosureStatus::FailedClosed(format!(
                "obligation {} carries no receipt",
                short(&ob.query_digest)
            ));
        }
        for receipt_digest in &ob.receipts {
            if let Some(reason) = receipt_fails(store, &ob.query_digest, receipt_digest) {
                return ClosureStatus::FailedClosed(reason);
            }
        }
    }
    for dep in &cert.dependencies {
        match load_certificate(store, dep) {
            Ok(Some(dep_cert)) => match verify_closure_at(store, &dep_cert, visiting, depth + 1) {
                ClosureStatus::Verified => {}
                ClosureStatus::FailedClosed(reason) => {
                    return ClosureStatus::FailedClosed(format!(
                        "dependency {} failed closed: {reason}",
                        short(dep)
                    ));
                }
                ClosureStatus::Incomplete(reason) => {
                    return ClosureStatus::FailedClosed(format!(
                        "dependency {} is not complete: {reason}",
                        short(dep)
                    ));
                }
            },
            Ok(None) => {
                return ClosureStatus::FailedClosed(format!(
                    "dependency certificate {} is missing or stale",
                    short(dep)
                ));
            }
            Err(e) => {
                return ClosureStatus::FailedClosed(format!(
                    "dependency certificate {} unreadable: {e}",
                    short(dep)
                ));
            }
        }
    }
    ClosureStatus::Verified
}

/// Why a receipt does not discharge `query_digest`, or `None` when it does: it
/// must load, re-address to its digest, bind to the query, and be a reusable
/// `unsat`.
fn receipt_fails(store: &Store, query_digest: &str, receipt_digest: &str) -> Option<String> {
    let bytes = match store.get(receipt_digest) {
        Ok(b) => b,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return Some(format!("receipt {} is missing", short(receipt_digest)));
        }
        Err(e) => return Some(format!("receipt {} unreadable: {e}", short(receipt_digest))),
    };
    let Ok(result) = SmtResult::decode(&bytes) else {
        return Some(format!("receipt {} is corrupt", short(receipt_digest)));
    };
    if result.digest() != receipt_digest {
        return Some(format!("receipt {} digest mismatch", short(receipt_digest)));
    }
    if !result.matches_query(query_digest) {
        return Some(format!(
            "receipt {} is bound to a different query",
            short(receipt_digest)
        ));
    }
    if !result.is_reusable_evidence() {
        return Some(format!(
            "receipt {} is {}, not a reusable unsat",
            short(receipt_digest),
            result.status.label()
        ));
    }
    None
}

/// Load and content-check a stored certificate. `Ok(None)` when absent or when the
/// stored bytes do not re-address to `digest` (a stale or forged reference).
///
/// # Errors
/// A filesystem error other than a missing object.
pub(crate) fn load_certificate(store: &Store, digest: &str) -> io::Result<Option<SmtCertificate>> {
    let bytes = match store.get(digest) {
        Ok(b) => b,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let Ok(cert) = SmtCertificate::decode(&bytes) else {
        return Ok(None);
    };
    if cert.digest() != digest {
        return Ok(None);
    }
    Ok(Some(cert))
}

/// The reuse-ref name for a query answered by a specific solver identity. The
/// solver identity is hashed in, so a flag or version change moves the key (and
/// therefore never reuses a receipt from a different answerer) without touching the
/// query digest.
fn reuse_key(query_digest: &str, solver: &SolverId) -> String {
    format!("{RESULT_REUSE_PREFIX}:{query_digest}:{}", solver.digest())
}

/// A short digest prefix for human-facing failure reasons.
fn short(digest: &str) -> &str {
    let end = digest.len().min(12);
    &digest[..end]
}
