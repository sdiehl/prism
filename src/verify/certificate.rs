//! The `prism-smt-certificate-v1` artifact: a content-addressed certificate over a
//! subject's obligations, carrying its dependency closure.
//!
//! A certificate names a subject (a contract or query digest), the obligation
//! query digests it covers with the receipt digest(s) that discharged each, the
//! dependency certificate digests it rests on, and any trusted assumption digests.
//! A [`Completeness::Complete`] certificate is reusable evidence only when the
//! whole closure holds: every obligation is a bound `unsat` solver-oracle receipt,
//! every dependency is itself a verified complete certificate, and no assumption is
//! trusted. The closure check ([`crate::verify::store::verify_closure`]) is
//! fail-closed: a missing, stale, partial, mismatched, or assumption-bearing
//! dependency yields [`ClosureStatus::FailedClosed`], never a silent pass.
//!
//! Trust stays honest: the live class is [`CertTrust::SolverOracle`]. Even two
//! agreeing solvers are solver-oracle evidence, not an independently checked
//! proof; the mixed and proof-checked classes are reserved and unimplemented.

use crate::store::codec::{put_str, put_uvarint, Reader};
use crate::store::CodecError;

/// The schema tag; the single home for this string, written first into every
/// frame so the digest is domain-separated by construction.
pub(crate) const SCHEMA: &str = "prism-smt-certificate-v1";

// The completeness vocabulary, pinned as frozen varint discriminants.
const COMPLETE: u64 = 0;
const PENDING: u64 = 1;
const PARTIAL: u64 = 2;

// The certificate trust vocabulary. Only solver-oracle is live; mixed and
// proof-checked are reserved so a certificate can never silently claim more.
const CERT_TRUST_SOLVER_ORACLE: u64 = 0;
/// The reserved discriminant for a certificate mixing solver-oracle and
/// independently checked evidence.
pub(crate) const CERT_TRUST_MIXED: u64 = 1;
/// The reserved discriminant for a fully proof-checked certificate.
pub(crate) const CERT_TRUST_PROOF_CHECKED: u64 = 2;

// A certificate holds a bounded number of obligations, dependencies, and
// assumptions; a wild count from hostile bytes is rejected before any allocation.
const MAX_OBLIGATIONS: u64 = 1 << 16;
const MAX_RECEIPTS_PER_OBLIGATION: u64 = 64;
const MAX_DEPENDENCIES: u64 = 1 << 16;
const MAX_ASSUMPTIONS: u64 = 1 << 16;

/// How much of a subject's proof a certificate carries.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Completeness {
    /// Every obligation is discharged and every dependency closes.
    Complete,
    /// Some obligation is not yet discharged (outside the fragment, or undecided).
    Pending,
    /// Some obligation is discharged but a dependency is missing or open.
    Partial,
}

impl Completeness {
    const fn to_varint(self) -> u64 {
        match self {
            Self::Complete => COMPLETE,
            Self::Pending => PENDING,
            Self::Partial => PARTIAL,
        }
    }

    const fn from_varint(n: u64) -> Result<Self, CodecError> {
        match n {
            COMPLETE => Ok(Self::Complete),
            PENDING => Ok(Self::Pending),
            PARTIAL => Ok(Self::Partial),
            _ => Err(CodecError::Malformed),
        }
    }

    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::Pending => "pending",
            Self::Partial => "partial",
        }
    }
}

/// The trust class of a certificate.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum CertTrust {
    /// Solver-oracle evidence (one solver, or several in agreement). The only live
    /// class: agreement is stronger provenance, still not an independent proof.
    SolverOracle,
    /// A class this build recognizes but does not implement (mixed, proof-checked,
    /// and beyond); the discriminant round-trips.
    Reserved(u64),
}

impl CertTrust {
    const fn to_varint(&self) -> u64 {
        match self {
            Self::SolverOracle => CERT_TRUST_SOLVER_ORACLE,
            Self::Reserved(n) => *n,
        }
    }

    const fn from_varint(n: u64) -> Self {
        if n == CERT_TRUST_SOLVER_ORACLE {
            Self::SolverOracle
        } else {
            Self::Reserved(n)
        }
    }

    pub(crate) fn label(&self) -> String {
        match self {
            Self::SolverOracle => "solver-oracle".to_string(),
            Self::Reserved(n) if *n == CERT_TRUST_MIXED => "mixed (reserved)".to_string(),
            Self::Reserved(n) if *n == CERT_TRUST_PROOF_CHECKED => {
                "proof-checked (reserved)".to_string()
            }
            Self::Reserved(n) => format!("reserved-trust-{n}"),
        }
    }
}

/// One certified obligation: the query digest and the receipt digest(s) that
/// discharged it. Several receipts encode multi-solver agreement; the closure
/// requires every one to be a bound `unsat` for this query.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct CertObligation {
    pub(crate) query_digest: String,
    pub(crate) receipts: Vec<String>,
}

/// A `prism-smt-certificate-v1` certificate.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct SmtCertificate {
    /// The subject this certifies: a contract or definition digest for a function
    /// certificate, or a bare query digest for a single-obligation leaf.
    pub(crate) subject: String,
    /// The obligations covered and the receipts that discharged them.
    pub(crate) obligations: Vec<CertObligation>,
    /// The dependency certificate digests this rests on (the callee-contract cone).
    pub(crate) dependencies: Vec<String>,
    /// The trusted assumption digests. A complete certificate has none: an
    /// unaccounted trusted assumption fails the closure closed.
    pub(crate) assumptions: Vec<String>,
    pub(crate) completeness: Completeness,
    pub(crate) trust: CertTrust,
}

impl SmtCertificate {
    /// The content identity of the certificate: a blake3 over its canonical frame,
    /// which leads with the schema tag.
    pub(crate) fn digest(&self) -> String {
        blake3::hash(&self.encode()).to_hex().to_string()
    }

    /// The canonical frame. The bytes are the identity.
    pub(crate) fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        put_str(&mut out, SCHEMA);
        put_str(&mut out, &self.subject);
        put_uvarint(&mut out, len64(self.obligations.len()));
        for ob in &self.obligations {
            put_str(&mut out, &ob.query_digest);
            put_uvarint(&mut out, len64(ob.receipts.len()));
            for r in &ob.receipts {
                put_str(&mut out, r);
            }
        }
        put_str_list(&mut out, &self.dependencies);
        put_str_list(&mut out, &self.assumptions);
        put_uvarint(&mut out, self.completeness.to_varint());
        put_uvarint(&mut out, self.trust.to_varint());
        out
    }

    /// Decode a certificate frame. Total: a `Result`, header checked before the
    /// body, every count capped, trailing bytes rejected.
    ///
    /// # Errors
    /// A foreign scheme, an unknown completeness discriminant, a truncated or
    /// oversized field, an over-count, or trailing bytes.
    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, CodecError> {
        let mut r = Reader::new(bytes);
        if r.string()? != SCHEMA {
            return Err(CodecError::Scheme);
        }
        let subject = r.string()?;
        let ob_count = capped(r.uvarint()?, MAX_OBLIGATIONS)?;
        let mut obligations = Vec::new();
        for _ in 0..ob_count {
            let query_digest = r.string()?;
            let receipt_count = capped(r.uvarint()?, MAX_RECEIPTS_PER_OBLIGATION)?;
            let mut receipts = Vec::new();
            for _ in 0..receipt_count {
                receipts.push(r.string()?);
            }
            obligations.push(CertObligation {
                query_digest,
                receipts,
            });
        }
        let dependencies = str_list(&mut r, MAX_DEPENDENCIES)?;
        let assumptions = str_list(&mut r, MAX_ASSUMPTIONS)?;
        let completeness = Completeness::from_varint(r.uvarint()?)?;
        let trust = CertTrust::from_varint(r.uvarint()?);
        if !r.at_end() {
            return Err(CodecError::TrailingBytes);
        }
        Ok(Self {
            subject,
            obligations,
            dependencies,
            assumptions,
            completeness,
            trust,
        })
    }
}

/// The verdict of checking a certificate's dependency closure against a store.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum ClosureStatus {
    /// The whole closure holds: reusable evidence.
    Verified,
    /// A structural failure: a missing, stale, partial, mismatched, or
    /// assumption-bearing dependency. Names the first reason. Never a silent pass.
    FailedClosed(String),
    /// The certificate honestly claims it is not complete.
    Incomplete(String),
}

fn put_str_list(out: &mut Vec<u8>, items: &[String]) {
    put_uvarint(out, len64(items.len()));
    for s in items {
        put_str(out, s);
    }
}

fn str_list(r: &mut Reader<'_>, cap: u64) -> Result<Vec<String>, CodecError> {
    let count = capped(r.uvarint()?, cap)?;
    let mut out = Vec::new();
    for _ in 0..count {
        out.push(r.string()?);
    }
    Ok(out)
}

const fn capped(n: u64, cap: u64) -> Result<u64, CodecError> {
    if n > cap {
        Err(CodecError::TooLarge)
    } else {
        Ok(n)
    }
}

fn len64(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}
