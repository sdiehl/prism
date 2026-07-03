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
//! Exactly one claim is live this release: [`Claim::ParityPassed`]. The shape is
//! reserved for future kinds (a Lean-checked property drawn from `models/Prism.lean`
//! is the intended next rung, claim [`CLAIM_LEAN_CHECKED`]); any claim this build
//! does not verify decodes as [`Claim::Reserved`] and is reported as
//! recognized-but-unverifiable rather than an error, so an old build reads a newer
//! certificate's envelope without mistaking it for corruption.
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
/// The reserved discriminant for a Lean-checked property (`models/Prism.lean`),
/// the intended next rung of the ladder; not emitted or verified this release.
pub const CLAIM_LEAN_CHECKED: u64 = 1;

/// The human-facing name of the one live claim.
pub const CLAIM_PARITY_PASSED_NAME: &str = "parity-passed";
/// The human-facing name reserved for the Lean-checked claim.
pub const CLAIM_LEAN_CHECKED_NAME: &str = "lean-checked";

/// The two independent backends the parity gate compares. A certificate records
/// which pair agreed, so the attestation names its own evidence.
pub const BACKEND_INTERP: &str = "interp";
/// The native LLVM backend, the other half of the parity gate's pair.
pub const BACKEND_LLVM: &str = "llvm";

/// The property a certificate claims about its subject digest.
///
/// One member is live ([`ParityPassed`](Self::ParityPassed)); [`Reserved`](Self::Reserved)
/// carries any discriminant this build does not yet verify, so a newer
/// certificate's envelope still decodes here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Claim {
    /// The subject's output was byte-identical across two independent backends
    /// (the parity oracle passed) under the recorded scheme.
    ParityPassed,
    /// A claim this build recognizes structurally but cannot verify: the reserved
    /// slot for future rungs (Lean-checked and beyond). The wrapped discriminant is
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
    /// A well-formed certificate whose claim this build does not yet verify (a
    /// reserved rung). Not a failure; the description names the reserved claim.
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
            "{} (claim reserved for a future release)",
            reserved_claim_name(n)
        )),
    }
}

// A short hash prefix for human-facing lines, matching the store's display habit.
fn short(hash: &str) -> &str {
    let n = HASH_PREFIX_HEX.min(hash.len());
    &hash[..n]
}
