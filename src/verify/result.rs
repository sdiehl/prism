//! The `prism-smt-result-v1` artifact: a normalized, content-addressed solver
//! receipt for exactly one query digest.
//!
//! A solver is an untrusted external search engine over bytes Prism has already
//! fixed. Everything a solver can do (`unsat`, `sat` with a model, `unknown`, a
//! timeout, a crash, or hostile/contradictory output) collapses into the six
//! [`ResultStatus`] members. The receipt binds the query digest it answers, so it
//! can never be replayed against a different obligation, and it records the exact
//! solver identity (family, version, semantic flags) so a flag or version change
//! moves the *receipt* identity while leaving the *query* identity untouched.
//!
//! An `unsat` is an honest [`Trust::SolverOracle`] receipt naming the trusted
//! solver, never an independently checked proof: the proof-checked rung is
//! reserved ([`TRUST_PROOF_CHECKED`]) and unimplemented. Only an `unsat`
//! solver-oracle receipt is reusable evidence; a `sat`, `unknown`, or any
//! infrastructure status never becomes a success.

use crate::store::codec::{put_str, put_uvarint, Reader};
use crate::store::CodecError;

/// The schema tag; the single home for this string, written first into every
/// frame so the digest is domain-separated by construction.
pub(crate) const SCHEMA: &str = "prism-smt-result-v1";

// The normalized status vocabulary, pinned as frozen varint discriminants so the
// binary body and any reader agree. This is a closed set: an unknown discriminant
// is corruption, not a future extension.
const STATUS_UNSAT: u64 = 0;
const STATUS_SAT: u64 = 1;
const STATUS_UNKNOWN: u64 = 2;
const STATUS_TIMEOUT: u64 = 3;
const STATUS_CRASH: u64 = 4;
const STATUS_MALFORMED: u64 = 5;

// The trust vocabulary. Only the solver-oracle class is live; the proof-checked
// rung is reserved so a receipt can never silently claim an independent proof.
const TRUST_SOLVER_ORACLE: u64 = 0;
/// The reserved discriminant for an independently proof-checked receipt. This
/// build neither emits nor verifies it; the class stays reserved.
pub(crate) const TRUST_PROOF_CHECKED: u64 = 1;

// A receipt carries a handful of solver flags and a small model, never thousands;
// a wild count from hostile bytes is rejected before any allocation.
const MAX_FLAGS: u64 = 64;
const MAX_MODEL_BINDINGS: u64 = 4096;

/// The normalized outcome of one `check-sat`. Exactly one of six, whatever the
/// solver did.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ResultStatus {
    /// `unsat`: the obligation is discharged under the SMT-LIB semantics. The only
    /// status that is reusable evidence.
    Unsat,
    /// `sat`: a counterexample exists; the model rides alongside when recovered.
    Sat,
    /// `unknown`: the solver did not decide.
    Unknown,
    /// The solver exceeded the resource policy and was killed.
    Timeout,
    /// A launch failure, a signal, or an exit with no parseable status.
    Crash,
    /// Output that named no status, contradicted itself, or was an `(error ...)`.
    Malformed,
}

impl ResultStatus {
    const fn to_varint(self) -> u64 {
        match self {
            Self::Unsat => STATUS_UNSAT,
            Self::Sat => STATUS_SAT,
            Self::Unknown => STATUS_UNKNOWN,
            Self::Timeout => STATUS_TIMEOUT,
            Self::Crash => STATUS_CRASH,
            Self::Malformed => STATUS_MALFORMED,
        }
    }

    const fn from_varint(n: u64) -> Result<Self, CodecError> {
        match n {
            STATUS_UNSAT => Ok(Self::Unsat),
            STATUS_SAT => Ok(Self::Sat),
            STATUS_UNKNOWN => Ok(Self::Unknown),
            STATUS_TIMEOUT => Ok(Self::Timeout),
            STATUS_CRASH => Ok(Self::Crash),
            STATUS_MALFORMED => Ok(Self::Malformed),
            _ => Err(CodecError::Malformed),
        }
    }

    /// The human-facing status word.
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Unsat => "unsat",
            Self::Sat => "sat",
            Self::Unknown => "unknown",
            Self::Timeout => "timeout",
            Self::Crash => "crash",
            Self::Malformed => "malformed",
        }
    }
}

/// The trust class of a receipt.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Trust {
    /// A named external solver was trusted for this `unsat`. The only live class.
    SolverOracle,
    /// A class this build recognizes structurally but does not implement (the
    /// reserved proof-checked rung and beyond); the discriminant round-trips.
    Reserved(u64),
}

impl Trust {
    const fn to_varint(&self) -> u64 {
        match self {
            Self::SolverOracle => TRUST_SOLVER_ORACLE,
            Self::Reserved(n) => *n,
        }
    }

    const fn from_varint(n: u64) -> Self {
        if n == TRUST_SOLVER_ORACLE {
            Self::SolverOracle
        } else {
            Self::Reserved(n)
        }
    }

    pub(crate) fn label(&self) -> String {
        match self {
            Self::SolverOracle => "solver-oracle".to_string(),
            Self::Reserved(n) if *n == TRUST_PROOF_CHECKED => {
                "proof-checked (reserved, unverified by this build)".to_string()
            }
            Self::Reserved(n) => format!("reserved-trust-{n}"),
        }
    }
}

/// The exact identity of the solver that produced a receipt. The receipt digest
/// commits to it, so a flag or version change moves the receipt identity; the
/// query digest is independent of it, so the same change never moves the query.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct SolverId {
    /// The stable family name (`z3`, `cvc5`, or `generic:<exe>`).
    pub(crate) family: String,
    /// The probed `--version` line, normalized to one trimmed line.
    pub(crate) version: String,
    /// The exact semantic flags passed. Physical resource limits (timeout, memory)
    /// are policy and are deliberately absent here.
    pub(crate) flags: Vec<String>,
}

impl SolverId {
    /// A stable content digest of the solver identity, used to key reusable
    /// evidence by exact answerer.
    pub(crate) fn digest(&self) -> String {
        let mut buf = Vec::new();
        put_str(&mut buf, &self.family);
        put_str(&mut buf, &self.version);
        put_uvarint(&mut buf, len64(self.flags.len()));
        for f in &self.flags {
            put_str(&mut buf, f);
        }
        blake3::hash(&buf).to_hex().to_string()
    }
}

/// One binding of a normalized `sat` model: a variable's canonical name and the
/// solver's value for it, both bounded strings.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct ModelBinding {
    pub(crate) name: String,
    pub(crate) value: String,
}

/// A `prism-smt-result-v1` receipt: the normalized answer to one query, bound to
/// that query's digest and to the solver that produced it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct SmtResult {
    /// The query digest this receipt answers. The binding a receipt can never
    /// escape: it is checked against the requested query before any reuse.
    pub(crate) query_digest: String,
    pub(crate) status: ResultStatus,
    pub(crate) trust: Trust,
    pub(crate) solver: SolverId,
    /// The normalized `sat` model, empty unless the status is `sat`.
    pub(crate) model: Vec<ModelBinding>,
}

impl SmtResult {
    /// A solver-oracle receipt for one query digest.
    pub(crate) fn oracle(
        query_digest: String,
        status: ResultStatus,
        solver: SolverId,
        model: Vec<ModelBinding>,
    ) -> Self {
        Self {
            query_digest,
            status,
            trust: Trust::SolverOracle,
            solver,
            // A model is only meaningful for `sat`; discard any stray bindings.
            model: if status == ResultStatus::Sat {
                model
            } else {
                Vec::new()
            },
        }
    }

    /// The content identity of the receipt: a blake3 over its canonical frame,
    /// which leads with the schema tag and commits to the solver identity, so a
    /// flag or version change moves this digest.
    pub(crate) fn digest(&self) -> String {
        blake3::hash(&self.encode()).to_hex().to_string()
    }

    /// Whether this receipt is reusable proof evidence: an `unsat` under the live
    /// solver-oracle trust class. A `sat`, `unknown`, or any infrastructure status
    /// never qualifies, and a reserved trust class never qualifies.
    pub(crate) fn is_reusable_evidence(&self) -> bool {
        self.status == ResultStatus::Unsat && self.trust == Trust::SolverOracle
    }

    /// Whether this receipt answers exactly `query_digest`. A receipt built for one
    /// query can never stand in for another.
    pub(crate) fn matches_query(&self, query_digest: &str) -> bool {
        self.query_digest == query_digest
    }

    /// The canonical frame. The bytes are the identity.
    pub(crate) fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        put_str(&mut out, SCHEMA);
        put_str(&mut out, &self.query_digest);
        put_uvarint(&mut out, self.status.to_varint());
        put_uvarint(&mut out, self.trust.to_varint());
        put_str(&mut out, &self.solver.family);
        put_str(&mut out, &self.solver.version);
        put_uvarint(&mut out, len64(self.solver.flags.len()));
        for f in &self.solver.flags {
            put_str(&mut out, f);
        }
        put_uvarint(&mut out, len64(self.model.len()));
        for b in &self.model {
            put_str(&mut out, &b.name);
            put_str(&mut out, &b.value);
        }
        out
    }

    /// Decode a receipt frame. Total: a `Result`, header checked before the body,
    /// counts capped, trailing bytes rejected.
    ///
    /// # Errors
    /// A foreign scheme, an unknown status discriminant, a truncated or oversized
    /// field, an over-count, or trailing bytes.
    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, CodecError> {
        let mut r = Reader::new(bytes);
        if r.string()? != SCHEMA {
            return Err(CodecError::Scheme);
        }
        let query_digest = r.string()?;
        let status = ResultStatus::from_varint(r.uvarint()?)?;
        let trust = Trust::from_varint(r.uvarint()?);
        let family = r.string()?;
        let version = r.string()?;
        let flag_count = r.uvarint()?;
        if flag_count > MAX_FLAGS {
            return Err(CodecError::TooLarge);
        }
        let mut flags = Vec::new();
        for _ in 0..flag_count {
            flags.push(r.string()?);
        }
        let model_count = r.uvarint()?;
        if model_count > MAX_MODEL_BINDINGS {
            return Err(CodecError::TooLarge);
        }
        let mut model = Vec::new();
        for _ in 0..model_count {
            let name = r.string()?;
            let value = r.string()?;
            model.push(ModelBinding { name, value });
        }
        if !r.at_end() {
            return Err(CodecError::TrailingBytes);
        }
        Ok(Self {
            query_digest,
            status,
            trust,
            solver: SolverId {
                family,
                version,
                flags,
            },
            model,
        })
    }

    /// A one-line honest description. An `unsat` names the trusted solver and its
    /// trust class; it is never rendered as an independently checked proof.
    pub(crate) fn render(&self) -> String {
        match self.status {
            ResultStatus::Unsat => format!(
                "unsat: {} receipt trusting {} {}",
                self.trust.label(),
                self.solver.family,
                self.solver.version
            ),
            other => format!(
                "{} (trusting {} {})",
                other.label(),
                self.solver.family,
                self.solver.version
            ),
        }
    }
}

/// Encode a collection length as the `u64` the codec uses, saturating rather than
/// wrapping so a pathological length stays a total function of the input.
fn len64(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}
