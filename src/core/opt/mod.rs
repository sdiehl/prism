//! The mid-level optimization tier's pass vocabulary and diagnostics.
//!
//! The pass implementations live in `core::typed` and transform witness-carrying
//! typed Core; the driver's stage runner owns their ordering, verification
//! boundaries, and the SCC fixed-point cache. This module holds what is shared
//! around them: the pass and stage enums, the level-to-pipeline expansion, the
//! `--passes` spec, the behavior-bearing pipeline fingerprint, per-pass tick
//! stats, Core Lint, and the per-pass dump sink. Each pass preserves observable
//! behavior (the parity oracle gates it) and runs above the interpreter/native
//! fork, so a rewrite lands identically on every backend.

use std::collections::BTreeSet;
use std::fmt::Write;
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::cbpv::Core;
use super::pretty::pp_core_pretty;
use crate::flags::DynFlags;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program};

mod lint;

const PASS_FINGERPRINT_SCHEMA: &[u8] = b"prism-core-pass-fingerprint-v1";

pub use lint::lint;

/// Optimization level: the knob that selects which passes run.
///
/// `O0` keeps only the mandatory representation passes (newtype erasure, which
/// both backends depend on). `O1`, the default, adds dictionary specialization
/// (pre-lowering), the gentle simplifier, the bounded inliner, and scalar CSE
/// (all late, after effect lowering, so they compose with the var/State fusion
/// rather than defeating it). `O2` runs a second inline/simplify iteration on top
/// of `O1`, so a body exposed as a call site only after the first inlining round
/// (a wrapper that inlined into another wrapper) still gets pasted in and cleaned
/// up. The extra round is idempotent once the program reaches a fixed point, so it
/// costs nothing on code the first round already settled.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OptLevel {
    O0,
    #[default]
    O1,
    O2,
}

impl OptLevel {
    /// Parse a `-O` level argument: the digit `0`, `1`, or `2` (the form the CLI
    /// `-O0`/`-O1`/`-O2` flags pass after stripping the prefix). `-O` with no
    /// digit is conventionally the highest level.
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "0" => Some(Self::O0),
            "1" => Some(Self::O1),
            "2" | "" => Some(Self::O2),
            _ => None,
        }
    }
}

/// A pass in the pipeline.
///
/// The ordered list a level expands to is data, built by [`pipeline`]; new
/// passes slot in here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CorePass {
    /// Whole-program stream fusion of pull-`Sequence` pipelines: collapse a
    /// recognized producer|>transformer|>consumer chain into one allocation-free
    /// loop (see `fuse`). Off by default; injected pre-lowering only when
    /// `DynFlags::fuse` is set, never listed by [`pipeline`].
    Fuse,
    /// Erase single-field `newtype` boxes. Mandatory at every level: it is a
    /// representation decision both backends consume, not an optimization.
    EraseNewtypes,
    /// Specialize constrained calls on known global dictionaries to direct calls.
    Specialize,
    /// The fixed-point gentle simplifier (case-of-known-constructor, trivial
    /// copy-propagation, dead-let elimination, const-fold, case-of-case,
    /// used-once-thunk inlining).
    Simplify,
    /// Inline single-call-site non-recursive functions.
    Inline,
    /// Common subexpression elimination of pure scalar `Prim`s.
    Cse,
}

impl CorePass {
    /// The pass's spelling in dumps, stats, and the `--passes` spec.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Fuse => "Fuse",
            Self::EraseNewtypes => "EraseNewtypes",
            Self::Specialize => "Specialize",
            Self::Simplify => "Simplify",
            Self::Inline => "Inline",
            Self::Cse => "Cse",
        }
    }

    /// The pass named by `s`, matching [`CorePass::name`] exactly. `None` for an
    /// unknown name.
    #[must_use]
    pub fn from_name(s: &str) -> Option<Self> {
        [
            Self::Fuse,
            Self::EraseNewtypes,
            Self::Specialize,
            Self::Simplify,
            Self::Inline,
            Self::Cse,
        ]
        .into_iter()
        .find(|p| p.name() == s)
    }

    /// Which stage of the pipeline this pass runs in.
    #[must_use]
    pub const fn stage(self) -> PassStage {
        match self {
            // Fusion must see the whole-program Core (the embedded stdlib is part of
            // the one program, which is what makes cross-module fusion free) and run
            // before effect lowering rewrites the shapes it matches on. Erasure is a
            // representation both backends consume; specialization needs the
            // pre-lowering dictionary shapes.
            Self::Fuse | Self::EraseNewtypes | Self::Specialize => PassStage::PreLowering,
            // The simplifier, inliner, and CSE must run after effect lowering:
            // pre-lowering they rewrite the Core shapes the var/State fusion
            // analysis matches on.
            Self::Simplify | Self::Inline | Self::Cse => PassStage::Late,
        }
    }

    /// Whether this pass transforms each definition independently and therefore
    /// admits an SCC-local durable query boundary.
    #[must_use]
    pub const fn is_scc_local(self) -> bool {
        matches!(self, Self::EraseNewtypes | Self::Simplify | Self::Cse)
    }
}

/// The point in compilation a pass runs, relative to effect lowering. Passes are
/// not freely reorderable across this boundary, so the pipeline is split by it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PassStage {
    /// Before effect lowering, in the front end.
    PreLowering,
    /// After effect lowering, on the lowered core (before reference counting).
    Late,
}

impl PassStage {
    /// The stage's spelling in the `--passes` spec (`pre`/`late`).
    const fn label(self) -> &'static str {
        match self {
            Self::PreLowering => "pre",
            Self::Late => "late",
        }
    }
}

/// An explicit ordered pass list per stage, the parsed `--passes` flag.
///
/// Overrides the `-O` level entirely: each section is exactly the passes named,
/// in order, with no level defaults filled in.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PassSpec {
    /// Pre-lowering passes, in run order.
    pub pre: Vec<CorePass>,
    /// Late (post-lowering) passes, in run order.
    pub late: Vec<CorePass>,
}

impl PassSpec {
    /// Parse a pass spec of the form `[pre:<names>][;late:<names>]`, where
    /// `<names>` is a comma-separated list of [`CorePass::name`] spellings. A bare
    /// comma-list with no `pre:`/`late:` marker is taken as the pre stage. An
    /// omitted section is empty (it is NOT defaulted to a level's passes), so the
    /// result lists exactly the passes named, in order.
    ///
    /// # Errors
    /// Returns a human-readable message when a name is unknown, a pass is placed
    /// in the wrong stage, the pre section orders `Specialize` before
    /// `EraseNewtypes`, or both sections are empty.
    pub fn parse(spec: &str) -> Result<Self, String> {
        let mut out = Self::default();
        for segment in spec.split(';').map(str::trim).filter(|s| !s.is_empty()) {
            let (stage, names) = split_section(segment);
            let target = match stage {
                PassStage::PreLowering => &mut out.pre,
                PassStage::Late => &mut out.late,
            };
            for name in names.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                let pass = CorePass::from_name(name).ok_or_else(|| unknown_pass(name))?;
                if pass.stage() != stage {
                    return Err(format!(
                        "{} runs in the {} stage",
                        pass.name(),
                        pass.stage().label()
                    ));
                }
                target.push(pass);
            }
        }
        let erase = out.pre.iter().position(|p| *p == CorePass::EraseNewtypes);
        let spec_pos = out.pre.iter().position(|p| *p == CorePass::Specialize);
        if let (Some(e), Some(s)) = (erase, spec_pos) {
            if s < e {
                return Err("EraseNewtypes must precede Specialize".into());
            }
        }
        if out.pre.is_empty() && out.late.is_empty() {
            return Err("pass specification is empty".into());
        }
        Ok(out)
    }
}

// Split one `;`-delimited segment into its stage and the comma-list of names. A
// `pre:`/`late:` marker selects the stage; a bare list (no marker) is the pre
// stage.
fn split_section(segment: &str) -> (PassStage, &str) {
    for (prefix, stage) in [("pre:", PassStage::PreLowering), ("late:", PassStage::Late)] {
        if let Some(rest) = segment.strip_prefix(prefix) {
            return (stage, rest);
        }
    }
    (PassStage::PreLowering, segment)
}

// An "unknown pass" message, suggesting the closest known name when one is near.
fn unknown_pass(name: &str) -> String {
    let suggestion = [
        CorePass::EraseNewtypes,
        CorePass::Specialize,
        CorePass::Simplify,
    ]
    .into_iter()
    .map(|p| (edit_distance(name, p.name()), p.name()))
    .filter(|(d, _)| *d <= 3)
    .min()
    .map(|(_, n)| n);
    suggestion.map_or_else(
        || format!("unknown pass `{name}`"),
        |n| format!("unknown pass `{name}` (did you mean `{n}`?)"),
    )
}

// Levenshtein distance, for the closest-name suggestion only.
fn edit_distance(a: &str, b: &str) -> usize {
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0; b.len() + 1];
    for (i, ca) in a.chars().enumerate() {
        cur[0] = i + 1;
        for (j, &cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            cur[j + 1] = (prev[j] + cost).min(prev[j + 1] + 1).min(cur[j] + 1);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

/// Per-pass tick counts (rewrites fired), in run order. Dumped under
/// `PRISM_OPT_STATS`.
#[derive(Clone, Debug, Default)]
pub struct PassStats {
    entries: Vec<(&'static str, u64)>,
}

impl PassStats {
    pub(crate) fn record(&mut self, pass: &'static str, ticks: u64) {
        self.entries.push((pass, ticks));
    }

    /// Total rewrites fired across all passes.
    #[must_use]
    pub fn total(&self) -> u64 {
        self.entries.iter().map(|(_, t)| t).sum()
    }

    /// Per-pass tick counts in run order.
    #[must_use]
    pub fn entries(&self) -> &[(&'static str, u64)] {
        &self.entries
    }

    pub(crate) fn report(&self) -> String {
        let mut s = String::from("core-opt ticks:\n");
        for (pass, ticks) in &self.entries {
            let _ = writeln!(s, "  {pass:<16} {ticks}");
        }
        let _ = writeln!(s, "  {:<16} {}", "total", self.total());
        s
    }
}

/// The ordered pass list for an opt level. Order matters: erase first (it
/// exposes inner values), then specialize.
#[must_use]
pub fn pipeline(level: OptLevel) -> Vec<CorePass> {
    // The list spans both stages; the driver runs the passes of one stage at a
    // time. The simplifier is a late (post-lowering) pass, so it composes with
    // the var/State fusion instead of defeating it.
    match level {
        OptLevel::O0 => vec![CorePass::EraseNewtypes],
        // O1 runs the inliner and CSE, sandwiched in simplifier runs: the first
        // cleans and exposes call sites, the inliner pastes single-call-site
        // bodies in, the second cleans
        // up the inlined code (wrappers vanish, case-of-known-constructor fires
        // across the inlined boundary), CSE shares the prims it exposed, the last
        // cleans up after CSE. The inliner's freshened binders are deterministic
        // (`%i{n}`), so this is safe at the default level's snapshots.
        OptLevel::O1 => vec![
            CorePass::EraseNewtypes,
            CorePass::Specialize,
            CorePass::Simplify,
            CorePass::Inline,
            CorePass::Simplify,
            CorePass::Cse,
            CorePass::Simplify,
        ],
        // O2 = O1 with stream fusion up front and a second inline/simplify round
        // before CSE. Fusion runs first (pre-lowering) so recognized pull-stream
        // pipelines collapse to loops before anything else shapes the Core; it is
        // default-on here only because its full battery (the ON/OFF differential
        // oracle, parity, Core Lint on fused output) is green, and `--no-fuse`
        // turns it back off. The second inline round: the first inlining can turn
        // a two-hop call chain into a single site that only the second round can
        // paste, so a wrapper that inlined into another wrapper is flattened here.
        // Both passes are fixed-point/idempotent, so the extra round is a no-op
        // once the program settles and never loops.
        OptLevel::O2 => vec![
            CorePass::Fuse,
            CorePass::EraseNewtypes,
            CorePass::Specialize,
            CorePass::Simplify,
            CorePass::Inline,
            CorePass::Simplify,
            CorePass::Inline,
            CorePass::Simplify,
            CorePass::Cse,
            CorePass::Simplify,
        ],
    }
}

/// Fingerprint the exact behavior-bearing pass sequence for one pipeline stage.
///
/// Diagnostic switches such as Core dumps and pass statistics are excluded;
/// disabled passes are removed, explicit pass specs override optimization levels,
/// and forced fusion is inserted exactly as [`effective_passes`] resolves it.
#[must_use]
pub fn pass_fingerprint(
    level: OptLevel,
    spec: Option<&PassSpec>,
    stage: PassStage,
    disabled: &[CorePass],
    flags: &DynFlags,
) -> String {
    let passes = effective_passes(level, spec, stage, disabled, flags);
    let mut hasher = blake3::Hasher::new();
    for field in std::iter::once(stage.label()).chain(passes.iter().map(|pass| pass.name())) {
        hasher.update(&(field.len() as u64).to_le_bytes());
        hasher.update(field.as_bytes());
    }
    hasher.update(PASS_FINGERPRINT_SCHEMA);
    hasher.finalize().to_hex().to_string()
}

/// Resolve an optimization level or explicit specification into the exact pass
/// sequence that changes Core at one stage.
#[must_use]
pub fn effective_passes(
    level: OptLevel,
    spec: Option<&PassSpec>,
    stage: PassStage,
    disabled: &[CorePass],
    flags: &DynFlags,
) -> Vec<CorePass> {
    let mut passes = spec.map_or_else(
        || {
            let mut selected = pipeline(level)
                .into_iter()
                .filter(|pass| pass.stage() == stage)
                .collect::<Vec<_>>();
            if flags.fuse && stage == PassStage::PreLowering && !selected.contains(&CorePass::Fuse)
            {
                selected.insert(0, CorePass::Fuse);
            }
            selected
        },
        |spec| match stage {
            PassStage::PreLowering => spec.pre.clone(),
            PassStage::Late => spec.late.clone(),
        },
    );
    passes.retain(|pass| !disabled.contains(pass));
    passes
}

// Each `run` that dumps gets a distinct id, so the several pipeline invocations a
// process makes (prelude compile, program compile, REPL turns) write to separate
// places instead of clobbering one another.
static DUMP_RUN: AtomicUsize = AtomicUsize::new(0);

// Claim the next dump-run ordinal. Every pipeline invocation takes one, dumping
// or not, so run numbering is stable across mixed-flag compiles in a process.
pub(crate) fn next_dump_run() -> usize {
    DUMP_RUN.fetch_add(1, Ordering::Relaxed)
}

// Render `core` to the `PRISM_DUMP_CORE` sink, labeled with the stage it follows.
// `stdout`/`stderr` stream a banner plus
// the block; any other value (or a bare flag) is a base directory under which a
// `run-N/` subdir holds one ordinal-prefixed file per stage, so directory order
// matches run order. Dump-only: the rendered form is for reading and diffing, not
// reloading.
pub(crate) fn dump_core(sink: &std::ffi::OsStr, run: usize, ord: usize, label: &str, core: &Core) {
    let text = pp_core_pretty(core);
    match sink.to_string_lossy().as_ref() {
        "stdout" => print!("=== core[run {run}]: {label} ===\n{text}\n"),
        "stderr" => eprint!("=== core[run {run}]: {label} ===\n{text}\n"),
        other => {
            let base = if matches!(other, "" | "1" | "on" | "true") {
                "target/core-dumps"
            } else {
                other
            };
            let safe: String = label
                .chars()
                .map(|c| if c.is_alphanumeric() { c } else { '_' })
                .collect();
            let dir = Path::new(base).join(format!("run-{run}"));
            if fs::create_dir_all(&dir).is_ok() {
                let _ = fs::write(dir.join(format!("{ord:02}-{safe}.core")), text);
            }
        }
    }
}

/// The constructor symbol of every `newtype` in the program (each a single-field
/// wrapper whose box this tier erases).
#[must_use]
pub fn newtype_ctors(prog: &Program<CorePhase>) -> BTreeSet<Sym> {
    prog.types
        .iter()
        .filter(|d| d.newtype)
        .filter_map(|d| d.ctors.first())
        .map(|c| Sym::from(&c.name))
        .collect()
}
