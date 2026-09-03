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
use prism_common::sym::Sym;
use prism_syntax::ast::{Core as CorePhase, Program};
use prism_syntax::error::suggest;

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    /// Higher-order specialization: clone a function on a constant callable
    /// argument that never varies across the recursion, turning the indirect
    /// force-and-apply into a direct call. Runs after `Specialize` so a callable
    /// threaded through a dictionary clone is already visible as a top-level call.
    HoSpecialize,
    /// Exact-size destination allocation: redirect a growable list-to-array
    /// builder chain to sized clones at call sites whose element count the
    /// summary domain proves exact. Runs after `HoSpecialize` so the
    /// devirtualized traversal clones whose counts the summaries track are
    /// already in place.
    ExactSize,
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
    /// Every pass, in declaration order. The one table the name lookup and the
    /// misspelling suggestion read, so a new variant reaches both.
    pub const ALL: [Self; 8] = [
        Self::Fuse,
        Self::EraseNewtypes,
        Self::Specialize,
        Self::HoSpecialize,
        Self::ExactSize,
        Self::Simplify,
        Self::Inline,
        Self::Cse,
    ];

    /// The pass's spelling in dumps, stats, and the `--passes` spec.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Fuse => "Fuse",
            Self::EraseNewtypes => "EraseNewtypes",
            Self::Specialize => "Specialize",
            Self::HoSpecialize => "HoSpecialize",
            Self::ExactSize => "ExactSize",
            Self::Simplify => "Simplify",
            Self::Inline => "Inline",
            Self::Cse => "Cse",
        }
    }

    /// The pass named by `s`, matching [`CorePass::name`] exactly. `None` for an
    /// unknown name.
    #[must_use]
    pub fn from_name(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|p| p.name() == s)
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
            Self::Fuse
            | Self::EraseNewtypes
            | Self::Specialize
            | Self::HoSpecialize
            | Self::ExactSize => PassStage::PreLowering,
            // The simplifier, inliner, and CSE must run after effect lowering:
            // pre-lowering they rewrite the Core shapes the var/State fusion
            // analysis matches on.
            Self::Simplify | Self::Inline | Self::Cse => PassStage::Late,
        }
    }

    /// Whether this pass transforms each definition independently and therefore
    /// admits an SCC-local durable query boundary. Such passes must preserve the
    /// input global-name set: regrouping keeps the original program order and
    /// rejects any added or dropped definition.
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassPipeline {
    pre: Vec<CorePass>,
    late: Vec<CorePass>,
}

/// Compatibility name for the original public API. Construction remains
/// validated because the alias exposes no fields.
pub type PassSpec = PassPipeline;

impl PassPipeline {
    /// Build one explicit staged pipeline.
    ///
    /// # Errors
    /// An empty pipeline, an off-stage pass, or an illegal specialization order.
    pub fn try_new(pre: Vec<CorePass>, late: Vec<CorePass>) -> Result<Self, String> {
        if pre
            .iter()
            .any(|pass| pass.stage() != PassStage::PreLowering)
        {
            return Err("pre pipeline contains a late-stage pass".into());
        }
        if late.iter().any(|pass| pass.stage() != PassStage::Late) {
            return Err("late pipeline contains a pre-lowering pass".into());
        }
        let erase = pre.iter().position(|p| *p == CorePass::EraseNewtypes);
        let specialize = pre.iter().position(|p| *p == CorePass::Specialize);
        if let (Some(e), Some(s)) = (erase, specialize) {
            if s < e {
                return Err("EraseNewtypes must precede Specialize".into());
            }
        }
        let higher_order = pre.iter().position(|p| *p == CorePass::HoSpecialize);
        if let (Some(s), Some(h)) = (specialize, higher_order) {
            if h < s {
                return Err("Specialize must precede HoSpecialize".into());
            }
        }
        if pre.is_empty() && late.is_empty() {
            return Err("pass specification is empty".into());
        }
        Ok(Self { pre, late })
    }

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
        let mut pre = Vec::new();
        let mut late = Vec::new();
        for segment in spec.split(';').map(str::trim).filter(|s| !s.is_empty()) {
            let (stage, names) = split_section(segment);
            let target = match stage {
                PassStage::PreLowering => &mut pre,
                PassStage::Late => &mut late,
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
        Self::try_new(pre, late)
    }

    /// Passes belonging to one verified stage.
    #[must_use]
    pub fn for_stage(&self, stage: PassStage) -> &[CorePass] {
        match stage {
            PassStage::PreLowering => &self.pre,
            PassStage::Late => &self.late,
        }
    }

    /// Pre-lowering passes, in run order.
    #[must_use]
    pub fn pre(&self) -> &[CorePass] {
        &self.pre
    }

    /// Late passes, in run order.
    #[must_use]
    pub fn late(&self) -> &[CorePass] {
        &self.late
    }

    fn without(&self, disabled: CorePass) -> Result<Self, String> {
        Self::try_new(
            self.pre
                .iter()
                .copied()
                .filter(|pass| *pass != disabled)
                .collect(),
            self.late
                .iter()
                .copied()
                .filter(|pass| *pass != disabled)
                .collect(),
        )
    }
}

/// A duplicate-free normalized set of disabled level-selected passes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PassSet(BTreeSet<CorePass>);

impl PassSet {
    #[must_use]
    pub const fn new() -> Self {
        Self(BTreeSet::new())
    }

    pub fn insert(&mut self, pass: CorePass) {
        self.0.insert(pass);
    }

    #[must_use]
    pub fn contains(&self, pass: CorePass) -> bool {
        self.0.contains(&pass)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = CorePass> + '_ {
        self.0.iter().copied()
    }
}

impl FromIterator<CorePass> for PassSet {
    fn from_iter<T: IntoIterator<Item = CorePass>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

/// The mutually exclusive ways to select an optimizer pipeline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OptimizationPlan {
    Level { level: OptLevel, disabled: PassSet },
    Explicit(PassPipeline),
}

impl Default for OptimizationPlan {
    fn default() -> Self {
        Self::Level {
            level: OptLevel::default(),
            disabled: PassSet::new(),
        }
    }
}

impl OptimizationPlan {
    #[must_use]
    pub const fn level(level: OptLevel, disabled: PassSet) -> Self {
        Self::Level { level, disabled }
    }

    #[must_use]
    pub const fn explicit(pipeline: PassPipeline) -> Self {
        Self::Explicit(pipeline)
    }

    /// Disable one pass. Explicit pipelines are normalized immediately; a
    /// request that would make them empty is rejected.
    ///
    /// # Errors
    /// Returns an error when disabling the pass would leave an explicit
    /// pipeline empty.
    pub fn disable(&mut self, pass: CorePass) -> Result<(), String> {
        match self {
            Self::Level { disabled, .. } => {
                disabled.insert(pass);
                Ok(())
            }
            Self::Explicit(pipeline) => {
                *pipeline = pipeline.without(pass)?;
                Ok(())
            }
        }
    }

    #[must_use]
    pub const fn selected_level(&self) -> Option<OptLevel> {
        match self {
            Self::Level { level, .. } => Some(*level),
            Self::Explicit(_) => None,
        }
    }

    #[must_use]
    pub const fn explicit_pipeline(&self) -> Option<&PassPipeline> {
        match self {
            Self::Explicit(pipeline) => Some(pipeline),
            Self::Level { .. } => None,
        }
    }

    #[must_use]
    pub const fn disabled(&self) -> Option<&PassSet> {
        match self {
            Self::Level { disabled, .. } => Some(disabled),
            Self::Explicit(_) => None,
        }
    }

    #[must_use]
    pub fn passes(&self, stage: PassStage, options: OptimizerOptions) -> Vec<CorePass> {
        match self {
            Self::Explicit(pipeline) => pipeline.for_stage(stage).to_vec(),
            Self::Level { level, disabled } => {
                let mut selected = pipeline(*level)
                    .into_iter()
                    .filter(|pass| pass.stage() == stage && !disabled.contains(*pass))
                    .collect::<Vec<_>>();
                if options.force_fuse
                    && stage == PassStage::PreLowering
                    && !disabled.contains(CorePass::Fuse)
                    && !selected.contains(&CorePass::Fuse)
                {
                    selected.insert(0, CorePass::Fuse);
                }
                selected
            }
        }
    }
}

/// The only behavior option observed while resolving optimizer passes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OptimizerOptions {
    pub force_fuse: bool,
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
    suggest::did_you_mean(name, CorePass::ALL.into_iter().map(CorePass::name)).map_or_else(
        || format!("unknown pass `{name}`"),
        |n| format!("unknown pass `{name}` (did you mean `{n}`?)"),
    )
}

/// Per-pass tick counts (rewrites fired), in run order. Dumped under
/// `PRISM_OPT_STATS`.
#[derive(Clone, Debug, Default)]
pub struct PassStats {
    entries: Vec<(&'static str, u64)>,
}

impl PassStats {
    pub fn record(&mut self, pass: &'static str, ticks: u64) {
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

    #[must_use]
    pub fn report(&self) -> String {
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
            CorePass::HoSpecialize,
            CorePass::ExactSize,
            CorePass::Simplify,
            CorePass::Inline,
            CorePass::Simplify,
            CorePass::Cse,
            CorePass::Simplify,
        ],
        // O2 = O1 with stream fusion up front and a second inline/simplify round
        // before CSE. Fusion runs first (pre-lowering) so recognized pull-stream
        // pipelines collapse to loops before anything else shapes the Core; it is
        // default-on here because its invisibility oracles are gated (a fuse-on
        // native build diffed against the interpreter in
        // `tests/native/fuse_parity.rs`, and the `-O2` versus `--no-fuse` leg of
        // the whole-corpus optimizer-equivalence sweep, which runs under Core
        // Lint), and `--no-fuse` takes it back out. The second inline round: the
        // first inlining can turn
        // a two-hop call chain into a single site that only the second round can
        // paste, so a wrapper that inlined into another wrapper is flattened here.
        // Both passes are fixed-point/idempotent, so the extra round is a no-op
        // once the program settles and never loops.
        OptLevel::O2 => vec![
            CorePass::Fuse,
            CorePass::EraseNewtypes,
            CorePass::Specialize,
            CorePass::HoSpecialize,
            CorePass::ExactSize,
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

/// Fingerprint a normalized optimization policy without exposing process-wide
/// flags or precedence inputs to the middle end.
#[must_use]
pub fn optimization_fingerprint(
    plan: &OptimizationPlan,
    stage: PassStage,
    options: OptimizerOptions,
) -> String {
    let passes = plan.passes(stage, options);
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
        |spec| spec.for_stage(stage).to_vec(),
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
pub fn next_dump_run() -> usize {
    DUMP_RUN.fetch_add(1, Ordering::Relaxed)
}

// Sink values that ask for a dump without naming a place, and the base directory
// they resolve to. An off spelling never reaches here: `DynFlags` resolves it to
// no sink at all.
const DUMP_HERE_SPELLINGS: [&str; 3] = ["1", "on", "true"];
const DUMP_DEFAULT_DIR: &str = "target/core-dumps";

// Render `core` to the `PRISM_DUMP_CORE` sink, labeled with the stage it follows.
// `stdout`/`stderr` stream a banner plus
// the block; a bare on spelling, or any other value, is a base directory under
// which a `run-N/` subdir holds one ordinal-prefixed file per stage, so directory
// order matches run order. Dump-only: the rendered form is for reading and
// diffing, not reloading.
pub fn dump_core(sink: &std::ffi::OsStr, run: usize, ord: usize, label: &str, core: &Core) {
    let text = pp_core_pretty(core);
    match sink.to_string_lossy().as_ref() {
        "stdout" => print!("=== core[run {run}]: {label} ===\n{text}\n"),
        "stderr" => eprint!("=== core[run {run}]: {label} ===\n{text}\n"),
        other => {
            let base = if DUMP_HERE_SPELLINGS.contains(&other) {
                DUMP_DEFAULT_DIR
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn staged_pipeline_rejects_wrong_stage_and_empty_construction() {
        assert!(PassPipeline::try_new(vec![CorePass::Inline], Vec::new()).is_err());
        assert!(PassPipeline::try_new(Vec::new(), vec![CorePass::Fuse]).is_err());
        assert!(PassPipeline::try_new(Vec::new(), Vec::new()).is_err());
    }

    #[test]
    fn explicit_and_level_plans_are_one_choice() {
        let explicit = PassPipeline::parse("pre:EraseNewtypes;late:Simplify").unwrap();
        let plan = OptimizationPlan::explicit(explicit);
        assert_eq!(plan.selected_level(), None);
        assert_eq!(
            plan.passes(PassStage::Late, OptimizerOptions::default()),
            vec![CorePass::Simplify]
        );
    }

    #[test]
    fn disabling_the_only_explicit_pass_is_rejected() {
        let mut plan = OptimizationPlan::explicit(PassPipeline::parse("late:Simplify").unwrap());
        assert!(plan.disable(CorePass::Simplify).is_err());
    }
}
