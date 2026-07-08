//! Per-phase compile timing, behind `--time-compile` / `PRISM_TIME_COMPILE`.
//!
//! When a [`TimingSink`] is installed on the [`Config`](super::Config), each
//! compiler phase emits one line-oriented, machine-diffable row to *stderr*. The
//! sink lives only on the config the CLI threads through a top-level compile;
//! every internal re-elaboration (`prelude_fn_names`, `off_platform_builtins`,
//! the identity/hash surfaces) builds its own [`Config::from_env`](super::Config::from_env),
//! which never installs a sink, so those helper compiles stay silent. All the
//! measuring work is gated on `Some(sink)`: with the flag off, [`timed`] and
//! [`timed_res`] reduce to a bare call of the wrapped closure, and no hash,
//! clock, or format cost is paid.
//!
//! The row schema, single-TAB separated, positions fixed:
//! ```text
//! phase<TAB>parse<TAB>2.1ms<TAB>in=src:1f2a8c9d<TAB>cold[<TAB>out=core:9b3e11f0][<TAB>k=v]...
//! ```
//! 1. the literal word `phase`;
//! 2. the phase name ([`Phase::label`]);
//! 3. wall time, milliseconds to one decimal;
//! 4. the input artifact key, the source content digest abbreviated for display;
//! 5. the cache status, always [`CacheStatus::Cold`] for now (no compile cache
//!    exists yet; the column is here so the format survives one arriving);
//! 6. an optional output artifact key, present only where a phase has a real,
//!    cheaply available artifact identity (the elaborated Core root, the emitted
//!    LLVM bitcode);
//! 7. trailing `k=v` counts, emitted only when real and already cheap at that phase.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// The literal first field, the anchor a reader greps for to find a timing row.
const ROW_TAG: &str = "phase";
// Width, in hex characters, of the abbreviated digest shown in an artifact key.
// Deliberately distinct from the 16-nibble `HASH_PREFIX_HEX` the content-address
// dumps use: a timing row is a glance-value display, not an identity.
const ABBREV_HEX: usize = 8;
// The artifact-kind prefix in field 4: every phase names the source it compiles.
const SRC_KIND: &str = "src";

/// The canonical pipeline-phase family. Each variant maps to one real stage of
/// the driver (`src/driver/front.rs` for the front end, `lower_opt` for the two
/// optimizer stages around effect lowering, the native path for codegen); the
/// label is the single spelling every row and test shares.
///
/// Lexing and parsing are one driver call (`parse`), so they are one honest
/// `parse` row rather than a faked split.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Phase {
    Parse,
    Resolve,
    Desugar,
    Typecheck,
    Elaborate,
    OptPre,
    LowerEffects,
    OptLate,
    EmitLlvm,
    CcLink,
    Eval,
}

impl Phase {
    /// The stable phase name, field 2 of the row.
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Parse => "parse",
            Self::Resolve => "resolve",
            Self::Desugar => "desugar",
            Self::Typecheck => "typecheck",
            Self::Elaborate => "elaborate",
            Self::OptPre => "opt.pre",
            Self::LowerEffects => "lower.effects",
            Self::OptLate => "opt.late",
            Self::EmitLlvm => "emit.llvm",
            Self::CcLink => "cc.link",
            Self::Eval => "eval",
        }
    }
}

/// The cache status column (field 5). The format reserves the spellings `cold`,
/// `hit`, `miss`, and `write`; a compile cache does not exist yet, so `Cold` is
/// the only constructed status and the enum grows a variant the day one arrives.
/// The column exists now so that arrival widens a value set, never the schema.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CacheStatus {
    Cold,
}

impl CacheStatus {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Cold => "cold",
        }
    }
}

/// The artifact kinds a row can name, in the `in=`/`out=` keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArtifactKind {
    /// The elaborated (pre-optimizer) Core root, a phase's compiled identity.
    Core,
    /// The emitted LLVM bitcode.
    Llvm,
}

impl ArtifactKind {
    const fn label(self) -> &'static str {
        match self {
            Self::Core => "core",
            Self::Llvm => "llvm",
        }
    }
}

/// The trailing `k=v` count keys. Only counts that are real and already cheap to
/// obtain at a phase are emitted; the family names the full vocabulary a reader
/// may encounter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CountKey {
    Defs,
    IrBytes,
}

impl CountKey {
    const fn label(self) -> &'static str {
        match self {
            Self::Defs => "defs",
            Self::IrBytes => "ir_bytes",
        }
    }
}

/// The optional tail of a row: an output artifact key and any count fields.
/// Built only when a sink is installed, so its (possibly hashing) construction is
/// never reached with the flag off.
#[derive(Default)]
pub(crate) struct RowExtras {
    out: Option<(ArtifactKind, String)>,
    counts: Vec<(CountKey, usize)>,
}

impl RowExtras {
    /// Attach the phase's output artifact key (`out=<kind>:<digest>`). `digest` is
    /// the full hex; the row abbreviates it for display.
    #[must_use]
    pub(crate) fn out(mut self, kind: ArtifactKind, digest: String) -> Self {
        self.out = Some((kind, digest));
        self
    }

    /// Attach a `k=v` count field.
    #[must_use]
    pub(crate) fn count(mut self, key: CountKey, value: usize) -> Self {
        self.counts.push((key, value));
        self
    }
}

// The mutable state a sink guards: the source digest (computed once, on the first
// phase that carries the source) and the set of phases already emitted (so a
// re-elaboration on the same compile does not double-print a phase).
#[derive(Debug, Default)]
struct Inner {
    src_digest: Option<String>,
    emitted: BTreeSet<&'static str>,
}

/// The per-compile timing sink, installed on the CLI's [`Config`](super::Config).
///
/// Cheap to clone (an `Arc`); every clone shares one state, so the source digest
/// and the de-duplication set are consistent across the handful of places a
/// config is cloned. Rows stream to stderr as phases complete, so a compile that
/// fails midway still reports the phases that ran.
#[derive(Clone, Debug, Default)]
pub struct TimingSink(Arc<Mutex<Inner>>);

impl TimingSink {
    /// A fresh sink with no source digest yet. The first timed phase to carry the
    /// source fills it in.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    // The abbreviated source key, computing (once) the digest from the first
    // non-empty source seen. Later phases pass an empty source and read the cached
    // digest.
    fn src_key(&self, src: &str) -> String {
        // Take an owned digest under the lock, then release it before formatting.
        let digest = {
            let mut inner = self
                .0
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if inner.src_digest.is_none() && !src.is_empty() {
                inner.src_digest = Some(blake3::hash(src.as_bytes()).to_hex().to_string());
            }
            inner.src_digest.clone().unwrap_or_default()
        };
        format!("{SRC_KIND}:{}", abbrev(&digest))
    }

    // Record one phase, unless it was already emitted on this compile. Streams the
    // row to stderr immediately.
    fn record(&self, phase: Phase, src: &str, dt: Duration, extras: &RowExtras) {
        // First sight of this phase? A re-elaboration on the same compile repeats
        // phases; the guard is released before any formatting or stderr write.
        let first = {
            let mut inner = self
                .0
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            inner.emitted.insert(phase.label())
        };
        if !first {
            return;
        }
        let mut row = String::new();
        let _ = write!(
            row,
            "{ROW_TAG}\t{}\t{}\tin={}\t{}",
            phase.label(),
            millis(dt),
            self.src_key(src),
            CacheStatus::Cold.label(),
        );
        if let Some((kind, digest)) = &extras.out {
            let _ = write!(row, "\tout={}:{}", kind.label(), abbrev(digest));
        }
        for (key, value) in &extras.counts {
            let _ = write!(row, "\t{}={value}", key.label());
        }
        eprintln!("{row}");
    }
}

// Field 3: wall time in milliseconds to one decimal place.
fn millis(dt: Duration) -> String {
    format!("{:.1}ms", dt.as_secs_f64() * 1000.0)
}

// The leading `ABBREV_HEX` nibbles of a digest, for display in an artifact key.
fn abbrev(digest: &str) -> &str {
    &digest[..digest.len().min(ABBREV_HEX)]
}

/// Time a fallible phase. With no sink this is exactly `f()`. With a sink, the
/// wall time of `f` alone is measured (the extras, which may hash, are built
/// afterward and never charged to the phase), then a row is emitted: the
/// `ok_extras`-derived tail on success, a bare row on failure.
pub(crate) fn timed_res<T, E>(
    timing: Option<&TimingSink>,
    phase: Phase,
    src: &str,
    f: impl FnOnce() -> Result<T, E>,
    ok_extras: impl FnOnce(&T) -> RowExtras,
) -> Result<T, E> {
    match timing {
        None => f(),
        Some(sink) => {
            let start = Instant::now();
            let result = f();
            let dt = start.elapsed();
            match &result {
                Ok(value) => sink.record(phase, src, dt, &ok_extras(value)),
                Err(_) => sink.record(phase, src, dt, &RowExtras::default()),
            }
            result
        }
    }
}

/// Time an infallible phase. As [`timed_res`], but for a closure that cannot fail
/// (the optimizer stages return a value, not a `Result`).
pub(crate) fn timed<T>(
    timing: Option<&TimingSink>,
    phase: Phase,
    src: &str,
    f: impl FnOnce() -> T,
    extras: impl FnOnce(&T) -> RowExtras,
) -> T {
    match timing {
        None => f(),
        Some(sink) => {
            let start = Instant::now();
            let value = f();
            let dt = start.elapsed();
            sink.record(phase, src, dt, &extras(&value));
            value
        }
    }
}

/// The `emit.llvm` row's tail: the size and content digest of the emitted LLVM
/// bitcode. Best-effort, since it runs only under the flag: a bitcode file that
/// cannot be read yields a bare tail rather than an error.
pub(crate) fn llvm_artifact(bitcode: &Path) -> RowExtras {
    std::fs::read(bitcode).map_or_else(
        |_| RowExtras::default(),
        |bytes| {
            RowExtras::default()
                .out(
                    ArtifactKind::Llvm,
                    blake3::hash(&bytes).to_hex().to_string(),
                )
                .count(CountKey::IrBytes, bytes.len())
        },
    )
}
