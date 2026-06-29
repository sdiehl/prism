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

use super::cbpv::{Comp, Core, CoreFn, CorePat, Value};
use super::traverse::Rewrite;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program};

mod lint;
mod specialize;
pub use lint::lint;
pub use specialize::specialize;
use specialize::specialize_counted;

/// Optimization level: the knob that selects which passes run.
///
/// `O0` keeps only the mandatory representation passes (newtype erasure, which
/// both backends depend on); `O1`, the default, adds optimization.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OptLevel {
    O0,
    #[default]
    O1,
}

/// A pass in the pipeline (the GHC `CoreToDo` analogue).
///
/// The ordered list a level expands to is data, built by [`pipeline`]; new
/// passes slot in here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CorePass {
    /// Erase single-field `newtype` boxes. Mandatory at every level: it is a
    /// representation decision both backends consume, not an optimization.
    EraseNewtypes,
    /// Specialize constrained calls on known global dictionaries to direct calls.
    Specialize,
}

impl CorePass {
    const fn name(self) -> &'static str {
        match self {
            Self::EraseNewtypes => "EraseNewtypes",
            Self::Specialize => "Specialize",
        }
    }
}

/// Per-pass tick counts (rewrites fired), in run order. Dumped under
/// `PRISM_OPT_STATS`; the `-ddump-simpl-stats` analogue.
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
        use std::fmt::Write;
        let mut s = String::from("core-opt ticks:\n");
        for (pass, ticks) in &self.entries {
            let _ = writeln!(s, "  {pass:<16} {ticks}");
        }
        let _ = writeln!(s, "  {:<16} {}", "total", self.total());
        s
    }
}

/// The optimization context (the GHC `CoreM` analogue): the level, the
/// program-derived newtype constructor set a pass needs, and the tick counter.
/// A fresh-name supply (`Sym::fresh`) is added here when a clone-generating pass
/// first needs it.
struct OptCx {
    level: OptLevel,
    newtype_ctors: BTreeSet<Sym>,
    stats: PassStats,
}

/// The ordered pass list for an opt level (the GHC `getCoreToDo`). Order matters:
/// erase first (it exposes inner values), then specialize.
#[must_use]
pub fn pipeline(level: OptLevel) -> Vec<CorePass> {
    match level {
        OptLevel::O0 => vec![CorePass::EraseNewtypes],
        OptLevel::O1 => vec![CorePass::EraseNewtypes, CorePass::Specialize],
    }
}

fn run_pass(pass: CorePass, core: &Core, cx: &mut OptCx) -> Core {
    let (out, ticks) = match pass {
        CorePass::EraseNewtypes => erase_newtypes_counted(core, &cx.newtype_ctors),
        CorePass::Specialize => specialize_counted(core),
    };
    cx.stats.record(pass.name(), ticks);
    out
}

/// Run the Core-to-Core pipeline for `level` over `core`.
///
/// Folds the passes built by [`pipeline`], honoring two env opt-outs
/// (`PRISM_NO_SPECIALIZE` drops specialization for before/after measurement) and
/// running Core Lint between passes under `PRISM_CORE_LINT`. Per-pass ticks are
/// returned, and dumped to stderr under `PRISM_OPT_STATS`.
///
/// # Panics
/// Under `PRISM_CORE_LINT`, panics if a pass produces ill-formed Core (a
/// compiler bug), naming the pass responsible.
#[must_use]
pub fn run(core: &Core, prog: &Program<CorePhase>, level: OptLevel) -> (Core, PassStats) {
    let lint_on = std::env::var_os("PRISM_CORE_LINT").is_some();
    let no_spec = std::env::var_os("PRISM_NO_SPECIALIZE").is_some();
    let mut cx = OptCx {
        level,
        newtype_ctors: newtype_ctors(prog),
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
    check(core, "<input>");
    let mut cur = core.clone();
    for pass in pipeline(cx.level) {
        if pass == CorePass::Specialize && no_spec {
            continue;
        }
        cur = run_pass(pass, &cur, &mut cx);
        check(&cur, pass.name());
    }
    if std::env::var_os("PRISM_OPT_STATS").is_some() {
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
