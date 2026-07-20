//! Lineage certificates: the two facts `lineage verify` can persist as a
//! digest-named artifact over a sidecar's own digest.
//!
//! A certificate rides the store's `cert`-kind envelope ([`crate::store::cert`]);
//! this module is the glue that reads a sidecar graph and a verification report and
//! mints the envelope, and checks a minted certificate against a sidecar's bytes.
//! The subject a certificate vouches for is the sha256 of the sidecar bytes, spelled
//! `scheme:hex` like every other digest-named node id, computed in one place
//! ([`sidecar_subject`]) so minting and checking cannot drift.

use crate::error::Error;
use crate::lineage::provenance::{sha256_hex, EVENT_HASH_SCHEME};
use crate::store::cert::{
    check_lineage_cert, encode_lineage_cert, lineage_cert, replay_cert, CertStatus,
};

use super::graph::LineageGraph;
use super::verify::{RunVerification, VerifyReport};

// The sidecar digest a certificate vouches for: the sha256 of the sidecar bytes,
// spelled `scheme:hex`. The one home for the subject format, shared by minting and
// checking.
fn sidecar_subject(sidecar_bytes: &[u8]) -> String {
    format!("{EVENT_HASH_SCHEME}:{}", sha256_hex(sidecar_bytes))
}

/// Mint a `replay-verified` certificate over `sidecar_bytes` from a passed replay.
///
/// The subject is the sidecar's digest; the evidence is the recorded trace digest,
/// the compiler fingerprint the run was stamped with, and the replayed counts.
///
/// # Errors
/// Fails if the graph is not a run sidecar (no trace node to name).
pub fn mint_replay_cert(
    graph: &LineageGraph,
    verification: &RunVerification,
    sidecar_bytes: &[u8],
) -> Result<Vec<u8>, Error> {
    let subject = sidecar_subject(sidecar_bytes);
    let trace = graph.trace().ok_or_else(|| {
        Error::ResolveLineage("lineage certify: not a run sidecar (no trace node)".into())
    })?;
    let trace_digest = format!("{}:{}", trace.scheme, trace.hash);
    let fingerprint = graph.compiler().map_or("", |c| c.fingerprint.as_str());
    let cert = replay_cert(
        &subject,
        &trace_digest,
        fingerprint,
        verification.trace_events,
        verification.stdout_bytes,
        verification.input_files,
    );
    Ok(encode_lineage_cert(&cert))
}

/// Mint a `lineage-verified` certificate over `sidecar_bytes` from a passed rehash.
///
/// The subject is the sidecar's digest; the evidence is the compiler fingerprint
/// and the rehash counts.
#[must_use]
pub fn mint_lineage_cert(
    graph: &LineageGraph,
    report: &VerifyReport,
    sidecar_bytes: &[u8],
) -> Vec<u8> {
    let subject = sidecar_subject(sidecar_bytes);
    let fingerprint = graph.compiler().map_or("", |c| c.fingerprint.as_str());
    let cert = lineage_cert(&subject, fingerprint, report.checked, report.skipped);
    encode_lineage_cert(&cert)
}

/// Check a certificate's bytes against the sidecar it names.
///
/// Recomputes the sidecar's digest and validates the certificate's bindings (the
/// parity-cert discipline: scheme, subject digest, claim recognition), never by
/// re-running the verification. A tampered sidecar moves its digest, so the binding
/// fails and names both digests; an unrecognized claim is recognized-but-untrusted.
#[must_use]
pub fn check_cert(cert_bytes: &[u8], sidecar_bytes: &[u8]) -> CertStatus {
    check_lineage_cert(cert_bytes, &sidecar_subject(sidecar_bytes))
}
