//! Mid-level Core-to-Core optimization tier.
//!
//! Each pass preserves observable behavior (the parity oracle gates it) and runs
//! above the interpreter/native fork, so a rewrite here lands identically on
//! every backend.
//!
//! `erase_newtypes`: a `newtype N = MkN(T)` is representationally identical to
//! `T`, so its one-field box is erased. Construction `MkN(v)` becomes `v`, and a
//! match `MkN(x) => body` becomes a plain rebind of `x` to the scrutinee (a
//! newtype is single-constructor, so its match is one irrefutable arm). The
//! surrounding logic, such as a derived `show` that prints `MkN(...)`, is
//! untouched, so only the representation changes, never the meaning.

use std::collections::BTreeSet;
use std::fmt::Write;

use super::cbpv::{Comp, Core, CoreFn, CorePat, Value};
use super::pretty::pp_core_pretty;
use super::traverse::Rewrite;
use crate::flags::DynFlags;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program};

mod cse;
mod fuse;
mod inline;
mod lint;
mod rename;
mod simplify;
mod specialize;
use cse::cse_counted;
use fuse::fuse_counted;
use inline::inline_counted;
pub use lint::lint;
use simplify::simplify_counted;
pub use specialize::specialize;
use specialize::specialize_counted;

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
    fn record(&mut self, pass: &'static str, ticks: u64) {
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

    fn report(&self) -> String {
        let mut s = String::from("core-opt ticks:\n");
        for (pass, ticks) in &self.entries {
            let _ = writeln!(s, "  {pass:<16} {ticks}");
        }
        let _ = writeln!(s, "  {:<16} {}", "total", self.total());
        s
    }
}

/// The optimization context: the program-derived newtype constructor set a pass
/// needs, and the tick counter. The inliner owns
/// its own deterministic per-compilation fresh-name counter.
struct OptCx {
    newtype_ctors: BTreeSet<Sym>,
    stats: PassStats,
}

/// The ordered pass list for an opt level. Order matters: erase first (it
/// exposes inner values), then specialize.
#[must_use]
pub fn pipeline(level: OptLevel) -> Vec<CorePass> {
    // The list spans both stages; `run` executes the passes of one stage at a
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

// Each `run` that dumps gets a distinct id, so the several pipeline invocations a
// process makes (prelude compile, program compile, REPL turns) write to separate
// places instead of clobbering one another.
static DUMP_RUN: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

// Render `core` to the `PRISM_DUMP_CORE` sink, labeled with the stage it follows.
// `stdout`/`stderr` stream a banner plus
// the block; any other value (or a bare flag) is a base directory under which a
// `run-N/` subdir holds one ordinal-prefixed file per stage, so directory order
// matches run order. Dump-only: the rendered form is for reading and diffing, not
// reloading.
fn dump_core(sink: &std::ffi::OsStr, run: usize, ord: usize, label: &str, core: &Core) {
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
            let dir = std::path::Path::new(base).join(format!("run-{run}"));
            if std::fs::create_dir_all(&dir).is_ok() {
                let _ = std::fs::write(dir.join(format!("{ord:02}-{safe}.core")), text);
            }
        }
    }
}

fn run_pass(pass: CorePass, core: &Core, cx: &mut OptCx) -> Core {
    let (out, ticks) = match pass {
        CorePass::Fuse => fuse_counted(core),
        CorePass::EraseNewtypes => erase_newtypes_counted(core, &cx.newtype_ctors),
        CorePass::Specialize => specialize_counted(core),
        CorePass::Simplify => simplify_counted(core),
        CorePass::Inline => inline_counted(core),
        CorePass::Cse => cse_counted(core),
    };
    cx.stats.record(pass.name(), ticks);
    out
}

/// Run the `stage` passes of the Core-to-Core pipeline for `level` over `core`.
///
/// The pipeline spans two stages around effect lowering ([`PassStage`]); this
/// runs only the passes of the requested stage, so the driver calls it twice (the
/// pre-lowering passes in the front end, the late passes on the lowered core).
/// `nt` is the program's newtype constructor set, needed by `EraseNewtypes` (pass
/// an empty set for a late run, which has no use for it). `disabled` is the set of
/// passes the caller turned off (the `--no-<pass>` flags plus `PRISM_NO_SPECIALIZE`,
/// resolved by the driver's `Config`). Runs Core Lint between passes under
/// `PRISM_CORE_LINT`, returns per-pass ticks, and dumps them under `PRISM_OPT_STATS`.
///
/// # Panics
/// Under `PRISM_CORE_LINT`, panics if a pass produces ill-formed Core (a
/// compiler bug), naming the pass responsible.
#[must_use]
pub fn run(
    core: &Core,
    nt: &BTreeSet<Sym>,
    level: OptLevel,
    stage: PassStage,
    disabled: &[CorePass],
    flags: &DynFlags,
) -> (Core, PassStats) {
    let mut passes: Vec<CorePass> = pipeline(level)
        .into_iter()
        .filter(|p| p.stage() == stage)
        .collect();
    // Stream fusion is default-on at `-O2` (listed by `pipeline` there, removable
    // with `--no-fuse` via `disabled`); the `PRISM_FUSE`/`--fuse` flag force-runs
    // it at the lower levels too, for experiments and the differential oracle.
    if flags.fuse && stage == PassStage::PreLowering && !passes.contains(&CorePass::Fuse) {
        passes.insert(0, CorePass::Fuse);
    }
    run_passes(core, nt, &passes, disabled, flags)
}

/// Run an explicit ordered list of `passes` over `core`, the `--passes` analogue
/// of [`run`].
///
/// `passes` is one stage's worth (the driver calls this twice, once per stage);
/// `nt` is the newtype constructor set `EraseNewtypes` needs (empty for a late
/// run); `disabled` is the caller's turned-off pass set. Uses the same lint/dump/
/// stats machinery and `PRISM_*` switches as [`run`].
///
/// # Panics
/// Under `PRISM_CORE_LINT`, panics if a pass produces ill-formed Core (a
/// compiler bug), naming the pass responsible.
#[must_use]
pub fn run_spec_stage(
    core: &Core,
    nt: &BTreeSet<Sym>,
    passes: &[CorePass],
    disabled: &[CorePass],
    flags: &DynFlags,
) -> (Core, PassStats) {
    run_passes(core, nt, passes, disabled, flags)
}

// The shared pass-running loop behind [`run`] and [`run_spec_stage`]: Core Lint
// between passes when `flags.core_lint`, dumps when `flags.dump_core` is set, the
// disabled-pass filter (the `--no-<pass>` flags plus `PRISM_NO_SPECIALIZE`), and
// per-pass ticks dumped when `flags.opt_stats`. Those three switches come from the
// threaded [`DynFlags`], not from the environment (see `crate::flags`).
fn run_passes(
    core: &Core,
    nt: &BTreeSet<Sym>,
    passes: &[CorePass],
    disabled: &[CorePass],
    flags: &DynFlags,
) -> (Core, PassStats) {
    let lint_on = flags.core_lint;
    // The effective pass vector: the requested passes minus every one the caller
    // disabled (the `--no-<pass>` flags and `PRISM_NO_SPECIALIZE`, resolved into
    // one list by the driver's `Config`). Filtering here applies whether the
    // passes came from a `-O` level or an explicit `--passes` list, and keeps
    // disabled passes out of the dump and per-pass stats below.
    let passes: Vec<CorePass> = passes
        .iter()
        .copied()
        .filter(|p| !disabled.contains(p))
        .collect();
    let mut cx = OptCx {
        newtype_ctors: nt.clone(),
        stats: PassStats::default(),
    };
    let check = |c: &Core, after: &str| {
        if lint_on {
            if let Err(errs) = lint(c) {
                panic!(
                    "PRISM_CORE_LINT: ill-formed Core after {after}:\n{}",
                    errs.join("\n")
                );
            }
        }
    };
    let dump_sink = flags.dump_core.clone();
    let dump_run = std::sync::atomic::AtomicUsize::fetch_add(
        &DUMP_RUN,
        1,
        std::sync::atomic::Ordering::Relaxed,
    );
    let mut ord = 0;
    if let Some(sink) = &dump_sink {
        dump_core(sink, dump_run, ord, "input", core);
        ord += 1;
    }
    check(core, "<input>");
    let mut cur = core.clone();
    for &pass in &passes {
        cur = run_pass(pass, &cur, &mut cx);
        check(&cur, pass.name());
        if let Some(sink) = &dump_sink {
            dump_core(sink, dump_run, ord, pass.name(), &cur);
            ord += 1;
        }
    }
    if flags.opt_stats {
        eprint!("{}", cx.stats.report());
    }
    (cur, cx.stats)
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

/// Erase every newtype box from `core` (see module docs). A no-op when the
/// program declares no newtypes.
#[must_use]
pub fn erase_newtypes(core: &Core, nt: &BTreeSet<Sym>) -> Core {
    erase_newtypes_counted(core, nt).0
}

// As `erase_newtypes`, also returning how many boxes were erased (the pass's
// tick count for telemetry).
fn erase_newtypes_counted(core: &Core, nt: &BTreeSet<Sym>) -> (Core, u64) {
    if nt.is_empty() {
        return (core.clone(), 0);
    }
    let mut e = Erase { nt, ticks: 0 };
    let fns = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            dict_arity: f.dict_arity,
            body: e.comp(&f.body, &()),
        })
        .collect();
    (Core { fns }, e.ticks)
}

struct Erase<'a> {
    nt: &'a BTreeSet<Sym>,
    ticks: u64,
}

fn is_newtype_match(arms: &[(CorePat, Comp)], nt: &BTreeSet<Sym>) -> bool {
    arms.len() == 1 && matches!(&arms[0].0, CorePat::Ctor(n, bs) if nt.contains(n) && bs.len() == 1)
}

impl Rewrite for Erase<'_> {
    type Ctx = ();

    fn comp(&mut self, c: &Comp, cx: &()) -> Comp {
        match c {
            // A newtype match is one irrefutable arm: rebind the matched value
            // (now the inner value) and run the body.
            Comp::Case(v, arms) if is_newtype_match(arms, self.nt) => {
                let CorePat::Ctor(_, binders) = &arms[0].0 else {
                    unreachable!("is_newtype_match")
                };
                self.ticks += 1;
                let binder = binders[0].unwrap_or_else(|| Sym::from("_"));
                Comp::Bind(
                    Box::new(Comp::Return(self.value(v, cx))),
                    binder,
                    Box::new(self.comp(&arms[0].1, cx)),
                )
            }
            _ => self.descend_comp(c, cx),
        }
    }

    fn value(&mut self, v: &Value, cx: &()) -> Value {
        match v {
            // The newtype box is its single field: drop the wrapper.
            Value::Ctor(name, _, fields) if self.nt.contains(name) && fields.len() == 1 => {
                self.ticks += 1;
                self.value(&fields[0], cx)
            }
            _ => self.descend_value(v, cx),
        }
    }
}
