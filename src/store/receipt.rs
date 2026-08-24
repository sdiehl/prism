//! The shadow-parser comparison receipt.
//!
//! What a shadow run proved, kept apart from what it merely measured.
//!
//! A shadow run parses a corpus twice, once with the authoritative parser and
//! once with the parser written in Prism, and compares the results. The receipt
//! is the record of that comparison. It is split across two store layers, and
//! the split is the design rather than an implementation detail:
//!
//! - the **certificate** carries the facts that are a function of the inputs:
//!   the two parser identities, the corpus identity, both syntax hashes, the
//!   diagnostic verdict, the downstream Core hash, and the compiler-work
//!   counters. Certificates are immutable on write, so re-running an unchanged
//!   comparison must produce byte-identical bytes or the store refuses it. That
//!   refusal is the point: it turns a second run into a reproduction check that
//!   nobody has to remember to perform.
//! - the **decision** carries the readings that are a function of the machine:
//!   wall time per phase. Those legitimately differ between two correct runs, so
//!   they go to the last-write-wins layer. Putting them in the certificate would
//!   make an honest re-run a corruption error, and the only way to keep the
//!   certificate writable would be to stop attesting anything.
//!
//! Both are keyed by the same subject, so a reader holding the comparison
//! identity finds the proof and the reading together without a second index.
//!
//! **Anti-vacuity.** A receipt may not claim a phase it did not exercise.
//! [`ShadowReceipt::new`](crate::store::receipt::ShadowReceipt::new) rejects a
//! phase whose Core visits are zero, so "the
//! optimizer ran and cost nothing" cannot be recorded as a success; it is either
//! a phase that did not run or an instrument that did not observe it, and both
//! are reasons to refuse rather than to attest. The check is on visits alone:
//! rebuilt nodes are legitimately zero for a read-only phase.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io;
use std::time::Duration;

use prism_common::digest::Digest;

use crate::core::HASH_SCHEME;
use crate::driver::PhaseTally;
use crate::store::cert::{
    decode_row_body, encode_row_body, CertRow, CertStatus, CLAIM_SHADOW_PARSE_AGREED,
    CLAIM_SHADOW_PARSE_AGREED_NAME,
};
use crate::store::disk::{Store, Written};
use crate::store::CodecError;

// The attesting compiler version, the one source of truth being the crate version.
const COMPILER_VERSION: &str = env!("CARGO_PKG_VERSION");

// The decision layer's kind for a shadow run's machine readings. Lowercase and
// hyphens only, which is what the decision path validator accepts.
const TIMING_KIND: &str = "shadow-parse-timing";
// The versioned tag the timing decision's bytes lead with, so a reader that finds
// an older shape rejects it instead of misreading it.
const TIMING_FORMAT: &str = "prism-shadow-parse-timing-v1";

// The certificate's evidence-row keys. One home for the family: a minter and a
// reader never retype a key, and adding a fact means adding it here.
const ROW_AUTHORITY: &str = "authority";
const ROW_SHADOW: &str = "shadow";
const ROW_CORPUS: &str = "corpus";
const ROW_CORPUS_FILES: &str = "corpus-files";
const ROW_SYNTAX_HASH_AUTHORITY: &str = "syntax-hash-authority";
const ROW_SYNTAX_HASH_SHADOW: &str = "syntax-hash-shadow";
const ROW_DIAGNOSTICS: &str = "diagnostics";
const ROW_CORE_HASH: &str = "core-hash";
const ROW_MAX_DEPTH: &str = "max-depth";

// Per-phase rows are `phase.<name>.<field>`, one family built from these parts so
// the spelling has a single home on both the minting and the reading side.
const PHASE_PREFIX: &str = "phase.";
const PHASE_INVOCATIONS: &str = "invocations";
const PHASE_VISITS: &str = "visits";
const PHASE_REBUILT: &str = "rebuilt";

// The diagnostic verdict's two spellings. A divergence count rides the second, so
// a reader never has to infer disagreement from a missing row.
const DIAGNOSTICS_AGREED: &str = "agreed";
const DIAGNOSTICS_DIVERGED_PREFIX: &str = "diverged:";

/// Why a receipt could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptError {
    /// A phase was offered with no Core visits recorded. Either it did not run or
    /// the instrument did not observe it; a receipt may claim neither.
    VacuousPhase(String),
    /// No phases were offered at all, which would attest a comparison that
    /// exercised nothing.
    NoPhases,
    /// The comparison covered no corpus files.
    EmptyCorpus,
}

impl std::fmt::Display for ReceiptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VacuousPhase(phase) => write!(
                f,
                "phase {phase:?} recorded no Core visits; a receipt cannot claim to have \
                 exercised a phase whose counter stayed zero"
            ),
            Self::NoPhases => f.write_str("a receipt must record at least one exercised phase"),
            Self::EmptyCorpus => f.write_str("a receipt must cover at least one corpus file"),
        }
    }
}

impl std::error::Error for ReceiptError {}

/// What the two parsers were run over, and what they were.
///
/// Every field is an identity rather than a path, so a receipt names what was
/// compared in terms a later reader can re-derive.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comparison {
    /// The authoritative parser's artifact identity.
    pub authority: String,
    /// The shadow parser's artifact identity.
    pub shadow: String,
    /// The corpus's source-tree identity.
    pub corpus: String,
    /// How many sources the comparison covered.
    pub corpus_files: usize,
    /// The syntax hash the authoritative parser produced.
    pub syntax_hash_authority: String,
    /// The syntax hash the shadow parser produced. Equal to the authority's on an
    /// agreeing run; recorded separately so a divergent run says where it split.
    pub syntax_hash_shadow: String,
    /// The Core hash the compared syntax elaborated to, which is the downstream
    /// consequence a parser change would show up in.
    pub core_hash: String,
    /// How many sources the two parsers disagreed on. Zero is the agreeing case.
    pub divergences: usize,
}

/// A shadow-run comparison receipt: its deterministic half.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShadowReceipt {
    /// The comparison's own identity, derived from what was compared. Both store
    /// layers key on it.
    pub subject: Digest,
    /// The hash scheme the receipt's identity is under; a scheme bump retires it.
    pub scheme: String,
    /// The attesting compiler version.
    pub compiler: String,
    /// What was compared.
    pub comparison: Comparison,
    /// The deepest traversal any phase reached during the run.
    pub max_depth: u64,
    /// Per-phase invocations and structural work, keyed by phase label.
    pub phases: BTreeMap<String, PhaseWork>,
}

/// One phase's contribution to a receipt: the deterministic part of a
/// [`PhaseTally`], with the wall time left behind.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PhaseWork {
    /// How many times the phase ran.
    pub invocations: usize,
    /// Core nodes the phase entered.
    pub visits: u64,
    /// Core nodes the phase reconstructed.
    pub rebuilt: u64,
}

impl ShadowReceipt {
    /// Build a receipt from a comparison and the phase tallies the run produced.
    ///
    /// Phases with no recorded structural work are dropped rather than attested:
    /// the front end works on the AST and never charges the Core counters, so
    /// including it would put a row of zeros next to rows that mean something.
    /// A phase offered explicitly through `exercised` must have work, and does
    /// not silently drop.
    ///
    /// # Errors
    /// An `exercised` phase with no Core visits, an empty corpus, or a run that
    /// exercised nothing.
    pub fn new(
        comparison: Comparison,
        tallies: &BTreeMap<&'static str, PhaseTally>,
        exercised: &[&str],
    ) -> Result<Self, ReceiptError> {
        if comparison.corpus_files == 0 {
            return Err(ReceiptError::EmptyCorpus);
        }
        for phase in exercised {
            let visits = tallies.get(*phase).map_or(0, |t| t.work.visits);
            if visits == 0 {
                return Err(ReceiptError::VacuousPhase((*phase).to_string()));
            }
        }
        let phases: BTreeMap<String, PhaseWork> = tallies
            .iter()
            .filter(|(_, tally)| !tally.work.is_silent())
            .map(|(phase, tally)| {
                (
                    (*phase).to_string(),
                    PhaseWork {
                        invocations: tally.invocations,
                        visits: tally.work.visits,
                        rebuilt: tally.work.rebuilt,
                    },
                )
            })
            .collect();
        if phases.is_empty() {
            return Err(ReceiptError::NoPhases);
        }
        let max_depth = tallies
            .values()
            .map(|t| t.work.max_depth)
            .max()
            .unwrap_or(0);
        Ok(Self {
            subject: Digest::from(subject_of(&comparison)),
            scheme: HASH_SCHEME.to_string(),
            compiler: COMPILER_VERSION.to_string(),
            comparison,
            max_depth,
            phases,
        })
    }

    /// Whether the two parsers agreed on every source.
    #[must_use]
    pub const fn agreed(&self) -> bool {
        self.comparison.divergences == 0
    }

    // The evidence rows, in the order the envelope carries them. Sorted within the
    // per-phase family by the map's own order, so two runs of the same comparison
    // emit the same bytes.
    fn rows(&self) -> Vec<CertRow> {
        let c = &self.comparison;
        let diagnostics = if self.agreed() {
            DIAGNOSTICS_AGREED.to_string()
        } else {
            format!("{DIAGNOSTICS_DIVERGED_PREFIX}{}", c.divergences)
        };
        let mut rows = vec![
            row(ROW_AUTHORITY, &c.authority),
            row(ROW_SHADOW, &c.shadow),
            row(ROW_CORPUS, &c.corpus),
            row(ROW_CORPUS_FILES, &c.corpus_files.to_string()),
            row(ROW_SYNTAX_HASH_AUTHORITY, &c.syntax_hash_authority),
            row(ROW_SYNTAX_HASH_SHADOW, &c.syntax_hash_shadow),
            row(ROW_DIAGNOSTICS, &diagnostics),
            row(ROW_CORE_HASH, &c.core_hash),
            row(ROW_MAX_DEPTH, &self.max_depth.to_string()),
        ];
        for (phase, work) in &self.phases {
            rows.push(row(
                &phase_key(phase, PHASE_INVOCATIONS),
                &work.invocations.to_string(),
            ));
            rows.push(row(
                &phase_key(phase, PHASE_VISITS),
                &work.visits.to_string(),
            ));
            rows.push(row(
                &phase_key(phase, PHASE_REBUILT),
                &work.rebuilt.to_string(),
            ));
        }
        rows
    }
}

fn row(key: &str, value: &str) -> CertRow {
    CertRow {
        key: key.to_string(),
        value: value.to_string(),
    }
}

fn phase_key(phase: &str, field: &str) -> String {
    format!("{PHASE_PREFIX}{phase}.{field}")
}

// The comparison's identity: a hash over exactly the facts that decide whether
// two runs are the same comparison. Deliberately not over the whole receipt,
// which carries the counters: a counter change with the same inputs must collide
// with the stored certificate and be reported, not quietly land under a new
// subject where nobody would look for it.
fn subject_of(c: &Comparison) -> String {
    let mut h = blake3::Hasher::new();
    for field in [
        &c.authority,
        &c.shadow,
        &c.corpus,
        &c.syntax_hash_authority,
        &c.syntax_hash_shadow,
        &c.core_hash,
    ] {
        h.update(&(field.len() as u64).to_le_bytes());
        h.update(field.as_bytes());
    }
    // Full hex, not the display prefix: this is an identity two store layers key
    // on, and a truncation that reads well in a terminal is not a reason to lose
    // collision resistance in a directory name.
    h.finalize().to_hex().to_string()
}

/// Serialize a receipt to its `cert`-kind envelope. The bytes are its identity.
#[must_use]
pub fn encode(receipt: &ShadowReceipt) -> Vec<u8> {
    encode_row_body(
        &receipt.subject,
        CLAIM_SHADOW_PARSE_AGREED,
        &receipt.scheme,
        &receipt.compiler,
        &receipt.rows(),
    )
}

/// Decode a receipt's `cert`-kind envelope.
///
/// # Errors
/// A foreign scheme, a non-cert kind, a claim from another family, a truncated or
/// oversized field, an over-count of rows, trailing bytes, or a row whose value
/// does not parse as the number its key promises.
pub fn decode(bytes: &[u8]) -> Result<ShadowReceipt, CodecError> {
    let body = decode_row_body(bytes)?;
    if body.claim != CLAIM_SHADOW_PARSE_AGREED {
        return Err(CodecError::Kind);
    }
    let mut fields: BTreeMap<&str, &str> = BTreeMap::new();
    let mut phases: BTreeMap<String, PhaseWork> = BTreeMap::new();
    for r in &body.rows {
        if let Some(rest) = r.key.strip_prefix(PHASE_PREFIX) {
            let (phase, field) = rest.rsplit_once('.').ok_or(CodecError::Malformed)?;
            let entry = phases.entry(phase.to_string()).or_default();
            match field {
                PHASE_INVOCATIONS => entry.invocations = parse_num(&r.value)?,
                PHASE_VISITS => entry.visits = parse_num(&r.value)?,
                PHASE_REBUILT => entry.rebuilt = parse_num(&r.value)?,
                _ => return Err(CodecError::Malformed),
            }
        } else {
            fields.insert(r.key.as_str(), r.value.as_str());
        }
    }
    let take = |key: &str| fields.get(key).copied().unwrap_or_default().to_string();
    let diagnostics = take(ROW_DIAGNOSTICS);
    let divergences = match diagnostics.strip_prefix(DIAGNOSTICS_DIVERGED_PREFIX) {
        Some(n) => parse_num(n)?,
        None if diagnostics == DIAGNOSTICS_AGREED => 0,
        None => return Err(CodecError::Malformed),
    };
    Ok(ShadowReceipt {
        subject: Digest::from(body.subject),
        scheme: body.scheme,
        compiler: body.compiler,
        comparison: Comparison {
            authority: take(ROW_AUTHORITY),
            shadow: take(ROW_SHADOW),
            corpus: take(ROW_CORPUS),
            corpus_files: parse_num(&take(ROW_CORPUS_FILES))?,
            syntax_hash_authority: take(ROW_SYNTAX_HASH_AUTHORITY),
            syntax_hash_shadow: take(ROW_SYNTAX_HASH_SHADOW),
            core_hash: take(ROW_CORE_HASH),
            divergences,
        },
        max_depth: parse_num(&take(ROW_MAX_DEPTH))?,
        phases,
    })
}

// A row value that promises to be a number. Hostile bytes get a codec error, not
// a panic and not a silent zero.
fn parse_num<T: std::str::FromStr>(s: &str) -> Result<T, CodecError> {
    s.parse().map_err(|_| CodecError::Malformed)
}

/// Write a receipt's deterministic half into the store, keyed by its subject.
///
/// Idempotent by construction: an unchanged comparison re-emits the same bytes
/// and answers [`Written::Hit`]. A comparison whose inputs match but whose
/// counters moved is a byte mismatch, which the certificate layer reports as
/// corruption. That is the intended alarm and not a bug to work around: the same
/// parser over the same corpus doing a different amount of work is exactly the
/// event the receipt exists to catch.
///
/// # Errors
/// A filesystem error, or a byte mismatch against a receipt already stored for
/// the subject.
pub fn emit(store: &Store, receipt: &ShadowReceipt) -> io::Result<Written> {
    store.put_cert(&receipt.subject, &encode(receipt))
}

/// Read the receipt stored for a comparison subject, if any.
///
/// # Errors
/// A filesystem error.
pub fn get(store: &Store, subject: &str) -> io::Result<Option<Result<ShadowReceipt, CodecError>>> {
    Ok(store.get_cert(subject)?.map(|bytes| decode(&bytes)))
}

/// Check the receipt stored for a subject.
///
/// The same discipline as the parity and lineage readers: a decode failure or a
/// foreign scheme is a named failure, an absent receipt is not a failure, and a
/// recorded divergence is reported as unverifiable rather than dressed up as a
/// pass.
#[must_use]
pub fn check(store: &Store, subject: &str) -> CertStatus {
    let receipt = match get(store, subject) {
        Ok(Some(Ok(r))) => r,
        Ok(Some(Err(e))) => return CertStatus::Failed(format!("corrupt shadow receipt ({e})")),
        Ok(None) => return CertStatus::Absent,
        Err(e) => return CertStatus::Failed(format!("shadow receipt unreadable: {e}")),
    };
    if receipt.subject.as_str() != subject {
        return CertStatus::Failed(format!(
            "shadow receipt vouches for {}, not the requested {subject}",
            receipt.subject
        ));
    }
    if receipt.scheme != HASH_SCHEME {
        return CertStatus::Failed(format!(
            "shadow receipt made under foreign scheme {:?}; this build speaks {HASH_SCHEME:?}",
            receipt.scheme
        ));
    }
    if !receipt.agreed() {
        return CertStatus::Unverifiable(format!(
            "{CLAIM_SHADOW_PARSE_AGREED_NAME} recorded {} divergence(s) over {} file(s)",
            receipt.comparison.divergences, receipt.comparison.corpus_files
        ));
    }
    CertStatus::Verified(format!(
        "{CLAIM_SHADOW_PARSE_AGREED_NAME}@{} by {} over {} file(s)",
        receipt.scheme, receipt.compiler, receipt.comparison.corpus_files
    ))
}

/// Record a run's per-phase wall times under the comparison's subject.
///
/// The last-write-wins half. Two correct runs of the same comparison disagree
/// here and that is not an error, which is precisely why these readings are kept
/// out of the certificate.
///
/// # Errors
/// A filesystem error, or a subject the decision layer rejects as a locator.
pub fn put_timing(
    store: &Store,
    subject: &str,
    tallies: &BTreeMap<&'static str, PhaseTally>,
) -> io::Result<()> {
    let mut out = format!("{TIMING_FORMAT}\n");
    for (phase, tally) in tallies {
        // Nanoseconds as an integer, not the row's rounded milliseconds: the
        // stderr row is a display and may round, a stored reading has no reason
        // to lose precision on its way through a file.
        let _ = writeln!(
            out,
            "{phase}\t{}\t{}",
            tally.invocations,
            tally.wall.as_nanos()
        );
    }
    store.put_decision(TIMING_KIND, subject, out.as_bytes())
}

/// Read back a run's recorded per-phase wall times, as `(phase, invocations,
/// wall)` triples in phase-label order.
///
/// # Errors
/// A filesystem error, a subject the decision layer rejects, or bytes in an
/// unknown format.
pub fn get_timing(store: &Store, subject: &str) -> io::Result<Vec<(String, usize, Duration)>> {
    let Some(bytes) = store.get_decision(TIMING_KIND, subject)? else {
        return Ok(Vec::new());
    };
    let text = String::from_utf8(bytes)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
    let mut lines = text.lines();
    if lines.next() != Some(TIMING_FORMAT) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "shadow timing decision has an unknown format",
        ));
    }
    let mut out = Vec::new();
    for line in lines.filter(|l| !l.is_empty()) {
        let mut parts = line.split('\t');
        let bad = || io::Error::new(io::ErrorKind::InvalidData, "malformed shadow timing row");
        let phase = parts.next().ok_or_else(bad)?.to_string();
        let invocations = parts.next().ok_or_else(bad)?.parse().map_err(|_| bad())?;
        let nanos: u128 = parts.next().ok_or_else(bad)?.parse().map_err(|_| bad())?;
        let nanos = u64::try_from(nanos).map_err(|_| bad())?;
        out.push((phase, invocations, Duration::from_nanos(nanos)));
    }
    Ok(out)
}
