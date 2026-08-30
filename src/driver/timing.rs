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
//! 5. the cache status: `cold` when caching is disabled, otherwise `hit`,
//!    `miss`, or `write`;
//! 6. an optional output artifact key, present only where a phase has a real,
//!    cheaply available artifact identity (the elaborated Core root, the emitted
//!    LLVM bitcode);
//! 7. trailing `k=v` counts, emitted only when real and already cheap at that phase.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
#[cfg(feature = "native")]
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant};

use crate::core::work::{self, WorkCounts};

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
// The row schema names every compile phase; a wasm build constructs no LLVM/cc
// phase, so those variants are legitimately unbuilt there, not dead.
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
    /// The ownership finishing between the optimizer and codegen: reference-count
    /// insertion, the reuse pass, their verifications, and the typed-to-untyped
    /// erasure. One honest row, like `parse`, rather than a faked split.
    Rc,
    #[cfg(feature = "native")]
    EmitLlvm,
    #[cfg(feature = "native")]
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
            Self::Rc => "rc",
            #[cfg(feature = "native")]
            Self::EmitLlvm => "emit.llvm",
            #[cfg(feature = "native")]
            Self::CcLink => "cc.link",
            Self::Eval => "eval",
        }
    }
}

/// The cache decision attached to a phase timing row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CacheStatus {
    Cold,
    #[cfg(feature = "native")]
    Hit,
    #[cfg(feature = "native")]
    Miss,
    #[cfg(feature = "native")]
    Write,
}

impl CacheStatus {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Cold => "cold",
            #[cfg(feature = "native")]
            Self::Hit => "hit",
            #[cfg(feature = "native")]
            Self::Miss => "miss",
            #[cfg(feature = "native")]
            Self::Write => "write",
        }
    }
}

/// The artifact kinds a row can name, in the `in=`/`out=` keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArtifactKind {
    /// The elaborated (pre-optimizer) Core root, a phase's compiled identity.
    Core,
    /// The emitted LLVM bitcode.
    #[cfg(feature = "native")]
    Llvm,
    /// A linked native executable.
    #[cfg(feature = "native")]
    Native,
}

impl ArtifactKind {
    const fn label(self) -> &'static str {
        match self {
            Self::Core => "core",
            #[cfg(feature = "native")]
            Self::Llvm => "llvm",
            #[cfg(feature = "native")]
            Self::Native => "native",
        }
    }
}

/// The trailing `k=v` count keys. Only counts that are real and already cheap to
/// obtain at a phase are emitted; the family names the full vocabulary a reader
/// may encounter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CountKey {
    Defs,
    #[cfg(feature = "native")]
    IrBytes,
    #[cfg(feature = "native")]
    ArtifactBytes,
    #[cfg(feature = "native")]
    CcInvocations,
    #[cfg(feature = "native")]
    CcProbeInvocations,
    #[cfg(feature = "native")]
    CcProbeMs,
    #[cfg(feature = "native")]
    CcCompileInvocations,
    #[cfg(feature = "native")]
    CcCompileMs,
    /// How many bitcode modules LLVM lowered to objects inside Prism.
    #[cfg(feature = "native")]
    LlvmObjectEmissions,
    /// Summed in-process LLVM object-lowering time in integer milliseconds.
    #[cfg(feature = "native")]
    LlvmObjectMs,
    #[cfg(feature = "native")]
    CcLinkInvocations,
    #[cfg(feature = "native")]
    CcLinkMs,
    #[cfg(feature = "native")]
    RuntimeObjectHits,
    #[cfg(feature = "native")]
    RuntimeObjectMisses,
    /// How many per-SCC bitcode shards the sharded backend emitted.
    #[cfg(feature = "native")]
    SccShards,
    /// Core nodes this phase entered through the shared descent.
    CoreVisits,
    /// Core nodes this phase reconstructed through the shared descent.
    RebuiltNodes,
    /// The deepest descent observed so far in this compile. Unlike the two above
    /// it is a running whole-compile maximum, not a per-phase delta, because a
    /// maximum over a subrange is not a property anyone can act on.
    MaxDepth,
}

impl CountKey {
    const fn label(self) -> &'static str {
        match self {
            Self::Defs => "defs",
            #[cfg(feature = "native")]
            Self::IrBytes => "ir_bytes",
            #[cfg(feature = "native")]
            Self::ArtifactBytes => "artifact_bytes",
            #[cfg(feature = "native")]
            Self::CcInvocations => "cc_invocations",
            #[cfg(feature = "native")]
            Self::CcProbeInvocations => "cc_probe_invocations",
            #[cfg(feature = "native")]
            Self::CcProbeMs => "cc_probe_ms",
            #[cfg(feature = "native")]
            Self::CcCompileInvocations => "cc_compile_invocations",
            #[cfg(feature = "native")]
            Self::CcCompileMs => "cc_compile_ms",
            #[cfg(feature = "native")]
            Self::LlvmObjectEmissions => "llvm_object_emissions",
            #[cfg(feature = "native")]
            Self::LlvmObjectMs => "llvm_object_ms",
            #[cfg(feature = "native")]
            Self::CcLinkInvocations => "cc_link_invocations",
            #[cfg(feature = "native")]
            Self::CcLinkMs => "cc_link_ms",
            #[cfg(feature = "native")]
            Self::RuntimeObjectHits => "runtime_object_hits",
            #[cfg(feature = "native")]
            Self::RuntimeObjectMisses => "runtime_object_misses",
            #[cfg(feature = "native")]
            Self::SccShards => "scc_shards",
            Self::CoreVisits => "core_visits",
            Self::RebuiltNodes => "rebuilt_nodes",
            Self::MaxDepth => "max_depth",
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
    // The same structural work the count fields display, kept unformatted so the
    // sink can accumulate it. The row shows one invocation's delta; a tally wants
    // to add them up, and re-parsing the rendered field to do so would make the
    // display the source of truth.
    work: WorkCounts,
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

    /// Attach the structural work this phase did, as the difference between two
    /// whole-compile readings.
    ///
    /// A difference rather than a reset, so a phase that contains another phase
    /// reports its own work including the inner one's, which is what containment
    /// means. Zero visits are left off the row entirely: the front end descends no
    /// Core, and a row of zeros reads as a measurement when it is an absence.
    #[must_use]
    fn work(mut self, before: WorkCounts, after: WorkCounts) -> Self {
        self.work = WorkCounts {
            visits: after.visits.saturating_sub(before.visits),
            rebuilt: after.rebuilt.saturating_sub(before.rebuilt),
            // Not a delta: a maximum over a subrange is not a property anyone can
            // act on, so this stays the whole-compile reading.
            max_depth: after.max_depth,
        };
        if self.work.is_silent() {
            return self;
        }
        let clamp = |n: u64| usize::try_from(n).unwrap_or(usize::MAX);
        self.counts.extend([
            (CountKey::CoreVisits, clamp(self.work.visits)),
            (CountKey::RebuiltNodes, clamp(self.work.rebuilt)),
            (CountKey::MaxDepth, clamp(self.work.max_depth)),
        ]);
        self
    }

    #[cfg(feature = "native")]
    #[must_use]
    pub(crate) fn cc_link_stats(mut self, stats: super::native::CcLinkStats) -> Self {
        let duration_ms =
            |duration: Duration| usize::try_from(duration.as_millis()).unwrap_or(usize::MAX);
        self.counts.extend([
            (CountKey::CcInvocations, stats.invocations()),
            (CountKey::CcProbeInvocations, stats.probe_invocations),
            (CountKey::CcProbeMs, duration_ms(stats.probe_time)),
            (CountKey::CcCompileInvocations, stats.compile_invocations),
            (CountKey::CcCompileMs, duration_ms(stats.compile_time)),
            (CountKey::LlvmObjectEmissions, stats.llvm_object_emissions),
            (CountKey::LlvmObjectMs, duration_ms(stats.llvm_object_time)),
            (CountKey::CcLinkInvocations, stats.link_invocations),
            (CountKey::CcLinkMs, duration_ms(stats.link_time)),
            (CountKey::RuntimeObjectHits, stats.runtime_object_hits),
            (CountKey::RuntimeObjectMisses, stats.runtime_object_misses),
        ]);
        self
    }
}

/// Everything a phase accumulated across one whole compile.
///
/// A phase can run more than once (a re-elaboration repeats the front end), and
/// only the first run is printed, so this is the only place the repeats survive.
/// That difference is the point: the row answers "what did this phase look like",
/// the tally answers "how many times did it happen and to what total", and a
/// receipt that quoted the row for the second question would silently drop every
/// repeat.
#[derive(Clone, Copy, Debug, Default)]
pub struct PhaseTally {
    /// How many times the phase ran, printed or not.
    pub invocations: usize,
    /// Summed wall time over those runs. A reading of the machine, not a property
    /// of the compilation: unlike the work counts it will differ run to run.
    pub wall: Duration,
    /// Summed structural work over those runs, with `max_depth` kept as a
    /// maximum rather than a sum, since it already is one.
    pub work: WorkCounts,
}

impl PhaseTally {
    fn add(&mut self, dt: Duration, work: WorkCounts) {
        self.invocations += 1;
        self.wall += dt;
        self.work.visits += work.visits;
        self.work.rebuilt += work.rebuilt;
        self.work.max_depth = self.work.max_depth.max(work.max_depth);
    }
}

// The mutable state a sink guards: the source digest (computed once, on the first
// phase that carries the source), the set of phases already emitted (so a
// re-elaboration on the same compile does not double-print a phase), and the
// per-phase tallies, which unlike the emitted set keep counting past the first.
#[derive(Debug, Default)]
struct Inner {
    src_digest: Option<String>,
    emitted: BTreeSet<&'static str>,
    tallies: BTreeMap<&'static str, PhaseTally>,
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

    /// What each phase accumulated, keyed by the stable phase name the timing
    /// rows print in field 2 (`parse`, `opt.pre`, `rc`, and the rest).
    ///
    /// The structured read of what the rows only sample. A caller building a
    /// receipt takes this rather than parsing stderr, so the row schema stays a
    /// display and never becomes an interchange format.
    #[must_use]
    pub fn tallies(&self) -> BTreeMap<&'static str, PhaseTally> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .tallies
            .clone()
    }

    // The abbreviated source key, computing (once) the digest from the first
    // non-empty source seen. Later phases pass an empty source and read the cached
    // digest.
    fn src_key(&self, src: &str) -> String {
        // Take an owned digest under the lock, then release it before formatting.
        let digest = {
            let mut inner = self.0.lock().unwrap_or_else(PoisonError::into_inner);
            if inner.src_digest.is_none() && !src.is_empty() {
                inner.src_digest = Some(blake3::hash(src.as_bytes()).to_hex().to_string());
            }
            inner.src_digest.clone().unwrap_or_default()
        };
        format!("{SRC_KIND}:{}", abbrev(&digest))
    }

    // Record one phase, unless it was already emitted on this compile. Streams the
    // row to stderr immediately.
    fn record(
        &self,
        phase: Phase,
        src: &str,
        dt: Duration,
        status: CacheStatus,
        extras: &RowExtras,
    ) {
        // Tally first, then ask whether to print: every invocation counts, only the
        // first prints. A re-elaboration on the same compile repeats phases; the
        // guard is released before any formatting or stderr write.
        let first = {
            let mut inner = self.0.lock().unwrap_or_else(PoisonError::into_inner);
            inner
                .tallies
                .entry(phase.label())
                .or_default()
                .add(dt, extras.work);
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
            status.label(),
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
            let before = work::snapshot();
            let start = Instant::now();
            let result = f();
            let dt = start.elapsed();
            let after = work::snapshot();
            match &result {
                Ok(value) => sink.record(
                    phase,
                    src,
                    dt,
                    CacheStatus::Cold,
                    &ok_extras(value).work(before, after),
                ),
                Err(_) => sink.record(
                    phase,
                    src,
                    dt,
                    CacheStatus::Cold,
                    &RowExtras::default().work(before, after),
                ),
            }
            result
        }
    }
}

/// Time a fallible cache-aware phase with an explicit decision label.
#[cfg(feature = "native")]
pub(crate) fn timed_res_status<T, E>(
    timing: Option<&TimingSink>,
    phase: Phase,
    src: &str,
    status: CacheStatus,
    f: impl FnOnce() -> Result<T, E>,
    ok_extras: impl FnOnce(&T) -> RowExtras,
) -> Result<T, E> {
    match timing {
        None => f(),
        Some(sink) => {
            let before = work::snapshot();
            let start = Instant::now();
            let result = f();
            let dt = start.elapsed();
            let after = work::snapshot();
            match &result {
                Ok(value) => sink.record(
                    phase,
                    src,
                    dt,
                    status,
                    &ok_extras(value).work(before, after),
                ),
                Err(_) => sink.record(
                    phase,
                    src,
                    dt,
                    status,
                    &RowExtras::default().work(before, after),
                ),
            }
            result
        }
    }
}

/// Record a cache hit that skipped the phase entirely.
#[cfg(feature = "native")]
pub(crate) fn cache_hit(
    timing: Option<&TimingSink>,
    phase: Phase,
    src: &str,
    output_kind: ArtifactKind,
    output_digest: String,
) {
    if let Some(sink) = timing {
        sink.record(
            phase,
            src,
            Duration::ZERO,
            CacheStatus::Hit,
            &RowExtras::default().out(output_kind, output_digest),
        );
    }
}

/// The `emit.llvm` row's tail: the size and content digest of the emitted LLVM
/// bitcode. Best-effort, since it runs only under the flag: a bitcode file that
/// cannot be read yields a bare tail rather than an error.
#[cfg(feature = "native")]
pub(crate) fn native_artifact(binary: &Path) -> RowExtras {
    std::fs::read(binary).map_or_else(
        |_| RowExtras::default(),
        |bytes| {
            RowExtras::default()
                .out(
                    ArtifactKind::Native,
                    blake3::hash(&bytes).to_hex().to_string(),
                )
                .count(CountKey::ArtifactBytes, bytes.len())
        },
    )
}

#[cfg(feature = "native")]
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
