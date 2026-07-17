//! The `cert`-kind wire envelope: a digest that attests a property of another
//! digest.
//!
//! # The envelope
//!
//! A certificate is the one wire envelope, read left to right, the header checked
//! before the body (the same discipline as the `def` codec, whose byte primitives
//! this shares):
//!
//! ```text
//!   +------------+------+------------------+--------------+
//!   | scheme tag | kind | contract digest  |     body     |
//!   +------------+------+------------------+--------------+
//!
//!   scheme tag       length-prefixed string, "prism-core-hash-v1"; a foreign
//!                    scheme is rejected before anything else
//!   kind             uvarint, the cert kind (WireKind::Cert)
//!   contract digest  length-prefixed hex, the SUBJECT hash this certificate
//!                    attests a property of. It rides the contract slot precisely
//!                    because it is the "other digest" the envelope is about, so a
//!                    reader confirms which hash a certificate concerns before it
//!                    decodes the body (`prism audit` matches it against a root).
//!   body:
//!     claim     uvarint  the property claimed (the `CLAIM_*` family)
//!     scheme    string   the hash scheme the claim was established under
//!     check     string   the check that established it (a `verify::CheckKind`)
//!     compiler  string   the attesting compiler version
//!     backend_a string   the first of the two independent backends that agreed
//!     backend_b string   the second
//! ```
//!
//! The certificate's own identity is the content hash of this whole envelope, so
//! it is a `value` whose body records the claim and the attesting context and
//! whose contract names the digest it vouches for: two digests (itself and its
//! subject) and a claim, following the same wire-envelope discipline as every
//! other stored value.
//!
//! # The claim vocabulary
//!
//! The parity claim [`Claim::ParityPassed`] is live over a core hash. Two more
//! claims are live over a lineage sidecar's digest ([`LineageClaim::ReplayVerified`]
//! and [`LineageClaim::LineageVerified`]); they ride the identical scheme, kind, and
//! codec, differing only in a body that carries evidence rows instead of a backend
//! pair. The varint claim family is one global number space (parity 0, the reserved
//! Lean-checked rung 1, replay-verified 2, lineage-verified 3), so a claim number
//! means the same thing to every reader. Any claim a build does not verify decodes
//! as its `Reserved` variant and is reported as recognized-but-untrusted rather than
//! an error, so an old build reads a newer certificate's envelope without mistaking
//! it for corruption. Claim [`CLAIM_LEAN_CHECKED`] is reserved for a Lean-checked
//! property drawn from `models/Prism.lean`.
//!
//! # Totality
//!
//! [`decode_cert`] never panics on hostile bytes: every varint is byte-capped and
//! every length is bounded (the shared `def`-codec reader), the scheme and kind are
//! checked before the body, and trailing bytes are rejected. Decode is a `Result`.

use std::io;

use crate::core::{HASH_PREFIX_HEX, HASH_SCHEME};
use crate::driver::WireKind;
use crate::store::codec::{put_str, put_uvarint, Reader};
use crate::store::disk::{Store, Written};
use crate::store::verify::CheckKind;
use crate::store::CodecError;

// The attesting compiler version, the one source of truth being the crate version.
const COMPILER_VERSION: &str = env!("CARGO_PKG_VERSION");

// The claim vocabulary, pinned as varint discriminants so the binary body and any
// reader agree on the family. Exactly one is live; the rest are reserved.
const CLAIM_PARITY_PASSED: u64 = 0;
/// The reserved discriminant for a Lean-checked property (`models/Prism.lean`).
/// This build neither emits nor verifies it.
pub const CLAIM_LEAN_CHECKED: u64 = 1;
// The two lineage claims, over a sidecar digest rather than a core hash. Same
// global number space as the parity family above; a reader keys the body shape on
// the number.
const CLAIM_REPLAY_VERIFIED: u64 = 2;
const CLAIM_LINEAGE_VERIFIED: u64 = 3;

/// The human-facing name of the one live claim.
pub const CLAIM_PARITY_PASSED_NAME: &str = "parity-passed";
/// The human-facing name reserved for the Lean-checked claim.
pub const CLAIM_LEAN_CHECKED_NAME: &str = "lean-checked";
/// The human-facing name of the replay-verification claim.
pub const CLAIM_REPLAY_VERIFIED_NAME: &str = "replay-verified";
/// The human-facing name of the artifact/edge rehash claim.
pub const CLAIM_LINEAGE_VERIFIED_NAME: &str = "lineage-verified";

// The evidence-row keys a lineage certificate carries: one home for the family so
// a minter and a reader never retype a key. A row is a `key = value` string pair,
// small and few.
const EVIDENCE_TRACE_DIGEST: &str = "trace-digest";
const EVIDENCE_COMPILER_FINGERPRINT: &str = "compiler-fingerprint";
const EVIDENCE_TRACE_EVENTS: &str = "trace-events";
const EVIDENCE_STDOUT_BYTES: &str = "stdout-bytes";
const EVIDENCE_INPUT_FILES: &str = "input-files";
const EVIDENCE_FILES_REHASHED: &str = "files-rehashed";
const EVIDENCE_WRITES_SKIPPED: &str = "writes-skipped";
// A lineage certificate carries a handful of evidence rows, never thousands, so a
// wild count from hostile bytes is rejected before any allocation.
const MAX_EVIDENCE_ROWS: u64 = 64;

/// The two independent backends the parity gate compares. A certificate records
/// which pair agreed, so the attestation names its own evidence.
pub const BACKEND_INTERP: &str = "interp";
/// The native LLVM backend, the other half of the parity gate's pair.
pub const BACKEND_LLVM: &str = "llvm";

/// The property a certificate claims about its subject digest.
///
/// One member is live ([`ParityPassed`](Self::ParityPassed)); [`Reserved`](Self::Reserved)
/// carries any discriminant outside this build's verified claim set, so the
/// certificate's envelope still decodes here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Claim {
    /// The subject's output was byte-identical across two independent backends
    /// (the parity oracle passed) under the recorded scheme.
    ParityPassed,
    /// A claim this build recognizes structurally but cannot verify: the reserved
    /// slot for external claims (Lean-checked and beyond). The wrapped discriminant is
    /// preserved so the frame round-trips.
    Reserved(u64),
}

impl Claim {
    const fn to_varint(&self) -> u64 {
        match self {
            Self::ParityPassed => CLAIM_PARITY_PASSED,
            Self::Reserved(n) => *n,
        }
    }

    const fn from_varint(n: u64) -> Self {
        if n == CLAIM_PARITY_PASSED {
            Self::ParityPassed
        } else {
            Self::Reserved(n)
        }
    }
}

/// The human-facing name of a reserved claim discriminant.
fn reserved_claim_name(n: u64) -> String {
    if n == CLAIM_LEAN_CHECKED {
        CLAIM_LEAN_CHECKED_NAME.to_string()
    } else {
        format!("reserved-claim-{n}")
    }
}

/// A certificate: a claim about a subject digest, plus the context that attests it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cert {
    /// The content hash whose property this certificate attests (the envelope's
    /// contract digest).
    pub subject: String,
    /// The property claimed.
    pub claim: Claim,
    /// The hash scheme the claim was established under; a scheme bump retires it.
    pub scheme: String,
    /// The check that established the claim (a [`CheckKind`] name).
    pub check: String,
    /// The attesting compiler version.
    pub compiler: String,
    /// The two independent backends whose agreement is the evidence.
    pub backends: (String, String),
}

/// Build the one live certificate: a parity-passed record for `subject`, attested
/// by this compiler over the current scheme and the given backend pair.
#[must_use]
pub fn parity_cert(subject: &str, backends: (&str, &str)) -> Cert {
    Cert {
        subject: subject.to_string(),
        claim: Claim::ParityPassed,
        scheme: HASH_SCHEME.to_string(),
        check: CheckKind::Parity.as_str().to_string(),
        compiler: COMPILER_VERSION.to_string(),
        backends: (backends.0.to_string(), backends.1.to_string()),
    }
}

/// Serialize a certificate to its `cert`-kind envelope. The bytes are its identity.
#[must_use]
pub fn encode_cert(cert: &Cert) -> Vec<u8> {
    let mut out = Vec::new();
    put_str(&mut out, HASH_SCHEME);
    put_uvarint(&mut out, u64::from(WireKind::Cert.varint()));
    put_str(&mut out, &cert.subject);
    put_uvarint(&mut out, cert.claim.to_varint());
    put_str(&mut out, &cert.scheme);
    put_str(&mut out, &cert.check);
    put_str(&mut out, &cert.compiler);
    put_str(&mut out, &cert.backends.0);
    put_str(&mut out, &cert.backends.1);
    out
}

/// Decode a `cert`-kind envelope. Total: a `Result`, never a panic, header checked
/// before the body, trailing bytes rejected.
///
/// # Errors
/// A foreign scheme, a non-cert kind, a truncated or oversized field, or trailing
/// bytes.
pub fn decode_cert(bytes: &[u8]) -> Result<Cert, CodecError> {
    let mut r = Reader::new(bytes);
    if r.string()? != HASH_SCHEME {
        return Err(CodecError::Scheme);
    }
    if r.uvarint()? != u64::from(WireKind::Cert.varint()) {
        return Err(CodecError::Kind);
    }
    let subject = r.string()?;
    let claim = Claim::from_varint(r.uvarint()?);
    let scheme = r.string()?;
    let check = r.string()?;
    let compiler = r.string()?;
    let backend_a = r.string()?;
    let backend_b = r.string()?;
    if !r.at_end() {
        return Err(CodecError::TrailingBytes);
    }
    Ok(Cert {
        subject,
        claim,
        scheme,
        check,
        compiler,
        backends: (backend_a, backend_b),
    })
}

/// Write `cert` into the store, keyed by its subject. Idempotent: re-emitting the
/// same certificate is a [`Written::Hit`].
///
/// # Errors
/// A filesystem error, or a byte mismatch against a different certificate already
/// stored for the subject.
pub fn emit(store: &Store, cert: &Cert) -> io::Result<Written> {
    store.put_cert(&cert.subject, &encode_cert(cert))
}

/// The outcome of checking a subject's certificate during an audit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertStatus {
    /// A recognized, verifiable certificate. Carries the one-line description to
    /// append to the audit's per-root line.
    Verified(String),
    /// A well-formed certificate whose claim is outside this build's verified
    /// claim set. Not a failure; the description names the reserved claim.
    Unverifiable(String),
    /// A corrupt, foreign-scheme, or mismatched certificate: a named failure.
    Failed(String),
    /// No certificate exists for the subject. Never a failure.
    Absent,
}

/// Read and verify the certificate a subject carries, if any.
///
/// A decode failure, a subject that does not match, or a foreign scheme is a named
/// [`CertStatus::Failed`]; an absent certificate is [`CertStatus::Absent`]; a
/// reserved claim is [`CertStatus::Unverifiable`]; the one live claim under the
/// current scheme is [`CertStatus::Verified`].
#[must_use]
pub fn check_cert(store: &Store, subject: &str) -> CertStatus {
    let bytes = match store.get_cert(subject) {
        Ok(Some(b)) => b,
        Ok(None) => return CertStatus::Absent,
        Err(e) => return CertStatus::Failed(format!("certificate unreadable: {e}")),
    };
    let cert = match decode_cert(&bytes) {
        Ok(c) => c,
        Err(e) => return CertStatus::Failed(format!("corrupt certificate ({e})")),
    };
    if cert.subject != subject {
        return CertStatus::Failed(format!(
            "certificate subject {} does not match root {}",
            short(&cert.subject),
            short(subject)
        ));
    }
    if cert.scheme != HASH_SCHEME {
        return CertStatus::Failed(format!(
            "certificate made under foreign scheme {:?}; this build speaks {HASH_SCHEME:?}",
            cert.scheme
        ));
    }
    match cert.claim {
        Claim::ParityPassed => CertStatus::Verified(format!(
            "{CLAIM_PARITY_PASSED_NAME}@{} by {}",
            cert.scheme, cert.compiler
        )),
        Claim::Reserved(n) => CertStatus::Unverifiable(format!(
            "{} (claim is recognized but unverified by this build)",
            reserved_claim_name(n)
        )),
    }
}

// A short hash prefix for human-facing lines, matching the store's display habit.
fn short(hash: &str) -> &str {
    hash.char_indices()
        .map(|(i, _)| i)
        .chain(std::iter::once(hash.len()))
        .take_while(|&i| i <= HASH_PREFIX_HEX)
        .last()
        .map_or("", |n| &hash[..n])
}

// --- Lineage certificates --------------------------------------------------
//
// A lineage certificate rides the same `cert`-kind envelope as the parity one: the
// scheme tag, the kind varint, and the subject digest are the header, and the body
// carries the claim, the attesting scheme and compiler, and a small list of
// evidence rows. The subject is a lineage sidecar's own digest (a `scheme:hex`
// string), so the certificate is a digest-named artifact over another digest.

/// The property a lineage certificate claims about a sidecar digest.
///
/// Two members are live; [`Reserved`](Self::Reserved) carries any discriminant this
/// build does not verify, so a newer certificate's envelope still decodes here and
/// is reported recognized-but-untrusted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LineageClaim {
    /// A run sidecar replayed to its recorded trace, stdout, and input digests
    /// (`lineage verify --replay` passed).
    ReplayVerified,
    /// A build or docs sidecar's artifact bytes and graph edges rehash to their
    /// recorded digests (`lineage verify` passed).
    LineageVerified,
    /// A claim this build recognizes structurally but does not verify: a future
    /// rung. The discriminant is preserved so the frame round-trips.
    Reserved(u64),
}

impl LineageClaim {
    const fn to_varint(&self) -> u64 {
        match self {
            Self::ReplayVerified => CLAIM_REPLAY_VERIFIED,
            Self::LineageVerified => CLAIM_LINEAGE_VERIFIED,
            Self::Reserved(n) => *n,
        }
    }

    const fn from_varint(n: u64) -> Self {
        if n == CLAIM_REPLAY_VERIFIED {
            Self::ReplayVerified
        } else if n == CLAIM_LINEAGE_VERIFIED {
            Self::LineageVerified
        } else {
            Self::Reserved(n)
        }
    }

    /// The human-facing name of the claim.
    #[must_use]
    pub fn name(&self) -> String {
        match self {
            Self::ReplayVerified => CLAIM_REPLAY_VERIFIED_NAME.to_string(),
            Self::LineageVerified => CLAIM_LINEAGE_VERIFIED_NAME.to_string(),
            Self::Reserved(n) => reserved_claim_name(*n),
        }
    }
}

/// One `key = value` evidence row of a lineage certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertRow {
    pub key: String,
    pub value: String,
}

/// A lineage certificate: a claim about a sidecar digest, plus the evidence rows
/// that attest it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineageCert {
    /// The sidecar digest this vouches for, a `scheme:hex` string (the envelope's
    /// contract digest).
    pub subject: String,
    /// The property claimed.
    pub claim: LineageClaim,
    /// The hash scheme the certificate's own identity is under; a scheme bump
    /// retires it.
    pub scheme: String,
    /// The attesting compiler version.
    pub compiler: String,
    /// The recorded facts the claim rests on (trace digest, counts, and so on).
    pub evidence: Vec<CertRow>,
}

fn evidence_row(key: &str, value: &str) -> CertRow {
    CertRow {
        key: key.to_string(),
        value: value.to_string(),
    }
}

/// Build a `replay-verified` certificate for `subject`, the digest of the run
/// sidecar whose replay just matched.
#[must_use]
pub fn replay_cert(
    subject: &str,
    trace_digest: &str,
    compiler_fingerprint: &str,
    events: usize,
    stdout_bytes: u64,
    input_files: usize,
) -> LineageCert {
    LineageCert {
        subject: subject.to_string(),
        claim: LineageClaim::ReplayVerified,
        scheme: HASH_SCHEME.to_string(),
        compiler: COMPILER_VERSION.to_string(),
        evidence: vec![
            evidence_row(EVIDENCE_TRACE_DIGEST, trace_digest),
            evidence_row(EVIDENCE_COMPILER_FINGERPRINT, compiler_fingerprint),
            evidence_row(EVIDENCE_TRACE_EVENTS, &events.to_string()),
            evidence_row(EVIDENCE_STDOUT_BYTES, &stdout_bytes.to_string()),
            evidence_row(EVIDENCE_INPUT_FILES, &input_files.to_string()),
        ],
    }
}

/// Build a `lineage-verified` certificate for `subject`, the digest of the build or
/// docs sidecar whose artifacts just rehashed.
#[must_use]
pub fn lineage_cert(
    subject: &str,
    compiler_fingerprint: &str,
    files_rehashed: usize,
    writes_skipped: usize,
) -> LineageCert {
    LineageCert {
        subject: subject.to_string(),
        claim: LineageClaim::LineageVerified,
        scheme: HASH_SCHEME.to_string(),
        compiler: COMPILER_VERSION.to_string(),
        evidence: vec![
            evidence_row(EVIDENCE_COMPILER_FINGERPRINT, compiler_fingerprint),
            evidence_row(EVIDENCE_FILES_REHASHED, &files_rehashed.to_string()),
            evidence_row(EVIDENCE_WRITES_SKIPPED, &writes_skipped.to_string()),
        ],
    }
}

/// Serialize a lineage certificate to its `cert`-kind envelope. The bytes are its
/// identity.
#[must_use]
pub fn encode_lineage_cert(cert: &LineageCert) -> Vec<u8> {
    let mut out = Vec::new();
    put_str(&mut out, HASH_SCHEME);
    put_uvarint(&mut out, u64::from(WireKind::Cert.varint()));
    put_str(&mut out, &cert.subject);
    put_uvarint(&mut out, cert.claim.to_varint());
    put_str(&mut out, &cert.scheme);
    put_str(&mut out, &cert.compiler);
    put_uvarint(
        &mut out,
        u64::try_from(cert.evidence.len()).unwrap_or(u64::MAX),
    );
    for r in &cert.evidence {
        put_str(&mut out, &r.key);
        put_str(&mut out, &r.value);
    }
    out
}

/// Decode a lineage `cert`-kind envelope. Total: a `Result`, never a panic, header
/// checked before the body, the evidence count capped, trailing bytes rejected.
///
/// # Errors
/// A foreign scheme, a non-cert kind, a truncated or oversized field, an
/// over-count of evidence rows, or trailing bytes.
pub fn decode_lineage_cert(bytes: &[u8]) -> Result<LineageCert, CodecError> {
    let mut r = Reader::new(bytes);
    if r.string()? != HASH_SCHEME {
        return Err(CodecError::Scheme);
    }
    if r.uvarint()? != u64::from(WireKind::Cert.varint()) {
        return Err(CodecError::Kind);
    }
    let subject = r.string()?;
    let claim = LineageClaim::from_varint(r.uvarint()?);
    let scheme = r.string()?;
    let compiler = r.string()?;
    let count = r.uvarint()?;
    if count > MAX_EVIDENCE_ROWS {
        return Err(CodecError::TooLarge);
    }
    let mut evidence = Vec::new();
    for _ in 0..count {
        let key = r.string()?;
        let value = r.string()?;
        evidence.push(CertRow { key, value });
    }
    if !r.at_end() {
        return Err(CodecError::TrailingBytes);
    }
    Ok(LineageCert {
        subject,
        claim,
        scheme,
        compiler,
        evidence,
    })
}

/// Check a lineage certificate's bytes against the digest recomputed from the
/// sidecar it names.
///
/// This mirrors the parity [`check_cert`] discipline: it validates the digest
/// bindings, not by re-running the verification, but by confirming the scheme, the
/// subject digest binding, and the claim recognition. Tampering the underlying
/// sidecar moves its digest, so the subject-binding check fails and names both
/// digests. A corrupt or foreign-scheme certificate is a named [`CertStatus::Failed`];
/// an unrecognized claim is [`CertStatus::Unverifiable`] (recognized-but-untrusted,
/// never silently accepted); a recognized claim whose binding holds is
/// [`CertStatus::Verified`].
#[must_use]
pub fn check_lineage_cert(bytes: &[u8], recomputed_subject: &str) -> CertStatus {
    let cert = match decode_lineage_cert(bytes) {
        Ok(c) => c,
        Err(e) => return CertStatus::Failed(format!("corrupt lineage certificate ({e})")),
    };
    if cert.scheme != HASH_SCHEME {
        return CertStatus::Failed(format!(
            "lineage certificate made under foreign scheme {:?}; this build speaks {HASH_SCHEME:?}",
            cert.scheme
        ));
    }
    if cert.subject != recomputed_subject {
        return CertStatus::Failed(format!(
            "sidecar digest mismatch: certificate vouches for {}, sidecar bytes hash to {}",
            short(&cert.subject),
            short(recomputed_subject)
        ));
    }
    match &cert.claim {
        LineageClaim::ReplayVerified | LineageClaim::LineageVerified => CertStatus::Verified(
            format!("{}@{} by {}", cert.claim.name(), cert.scheme, cert.compiler),
        ),
        LineageClaim::Reserved(n) => CertStatus::Unverifiable(format!(
            "{} (claim not recognized by this build; recognized-but-untrusted)",
            reserved_claim_name(*n)
        )),
    }
}
