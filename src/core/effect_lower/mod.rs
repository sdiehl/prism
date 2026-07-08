use std::collections::{BTreeMap, BTreeSet};

use super::cbpv::{reachable_fns, Core, CoreFn, ElaboratedCore, LoweredCore, Value};
use super::traverse::map_children as map_kids;
use crate::error::TypeError;
use crate::flags::{DynFlags, EffectTier};
use crate::fresh::Fresh;
use crate::names::{self, ENTRY_POINT};
use crate::sym::Sym;
use crate::syntax::ast::Grade;
use crate::types::CtorInfo;

/// Each effect op's declared resumption grade, keyed by its symbol.
///
/// Built by the checker ([`crate::tc::Checked::op_grades`]) and consumed by
/// `erase_var`: an op graded at most `One` can never resume more than once, so a
/// handler for it never disables var-erasure. An op absent here defaults to `Many`
/// at the consumer (a synthetic private effect keeps the prior behavior).
pub type OpGrades = BTreeMap<Sym, Grade>;

mod analysis;
mod checks;
mod diagnostics;
mod erase_control;
mod erase_var;
mod evidence;
mod flow;
mod handle;
mod monadic;
mod runtime;
mod state;
mod trampoline;
mod walk;

use analysis::{latent_map, monadic_set};
use checks::{check_convention_boundaries, raw_effects};
use diagnostics::{free_monad_warning, genuine_eff, DriftLog};
use runtime::{ebind_fn, qapply_fn, synth_ctor};
use walk::collect_ops;

pub use analysis::latent_ops;
pub use checks::residual_effects;
use walk::{contains_mask, each_subcomp, each_value, latent, thunks_in_comp, thunks_in_value};

// Compile algebraic effects to plain closures and data by a free-monad
// translation. A computation that may perform effects is reified into a value
// of the result type:
//
//   EPure(v)              a finished computation returning v
//   EOp(id, skip, arg, k) a suspended `do op(arg)` whose continuation is k
//
// `ebind` threads a continuation through this representation. Each `handle`
// becomes a recursive driver matching the result: EPure runs the return clause,
// EOp dispatches to the matching operation with `resume` bound to a closure that
// re-enters the driver. Since `k` is an ordinary reusable closure, resumptions
// are multishot.
//
// A handler is "open" when its body performs effects it does not itself catch.
// Its driver forwards the unhandled `EOp` outward with a continuation that
// re-enters this driver, so an outer handler discharges it and resumption flows
// back through here. Open drivers return Eff values and monadify their clauses.
// "Closed" drivers (the common case, including the parameter-passing `k(v)(s)`
// idiom) return bare values and are unchanged.
//
// When effectful code escapes first-class through a thunk, no static analysis
// can tell monadified callees apart at dynamic call sites, so lowering falls
// back to whole-program monadic mode. Every function, lambda, and thunk body is
// monadified, every handler is driven open-style, and `main` unwraps the final
// EPure, trapping on an op that reaches the top like the interpreter's
// unhandled-effect error.
//
// Mask is an explicit depth mirroring the interpreter's `skip` counter
// (`eval/mod.rs`). An in-flight `EOp` carries `skip`, the number of matching
// handlers it must still bypass. A mask driver increments `skip` on ops of its
// effect passing through it. A handler driver matches on `id` equality; when an
// op is its own but `skip > 0`, it forwards with `skip - 1`, consuming one level
// exactly as the interpreter decrements on a `Frame::Handle` crossing. Fresh ops
// start at `skip = 0`.

const PURE_TAG: usize = 0;
const OP_TAG: usize = 1;
// A third Eff ctor used only by the self-recursive driver: a clause that resumes
// in tail position yields `EResume(queue, value)` instead of re-entering a driver,
// so the driver drives the resumed continuation by tail-calling itself.
const RESUME_TAG: usize = 2;
const ERESUME: &str = "EResume";
// Type name carrying the free-monad result (its ctors are EPure/EOp/EResume).
const EFF: &str = "Eff";
const EPURE: &str = "EPure";
pub(crate) const EOP: &str = "EOp";
const EBIND: &str = "ebind";
// The queue-application driver: runs an `EOp`'s type-aligned continuation queue.
const QAPPLY: &str = "qApply";

// Behind `PRISM_CEK_SPIKE`: a reserved op id marking a reified `resume`. The CEK
// driver dispatches it specially, driving the captured continuation concatenated
// with the clause's post-resume work; a real op id is always non-negative.
const RESUME_OP_ID: i64 = -1;

// Trampoline (`PRISM_TRAMPOLINE`): a fourth Eff ctor reifying a deferred monadic
// hop. `EBounce(thunk)` is "run this thunk for the next Eff"; the `prism_drive`
// loop forces it in constant native stack, so the run-queue/answer-function
// recursion of a parameter-passing scheduler no longer grows the C stack.
const BOUNCE_TAG: usize = 3;
const EBOUNCE: &str = "EBounce";
const DRIVE: &str = "prism_drive";

// The result of `taq_uncons`: `TQNil` (empty queue) or `TQCons(head, tail)`. Its
// own small ADT so `qApply` can pattern-match the C primitive's return.
const TQ: &str = "TQ";
const TQNIL: &str = "TQNil";
const TQCONS: &str = "TQCons";
const TQNIL_TAG: usize = 0;
const TQCONS_TAG: usize = 1;

// Behind `PRISM_CEK_SPIKE`: the CEK loop's meta-continuation, a LIFO stack of
// pending answer-continuations (each a continuation queue). A resume pushes the
// clause's post-resume work; reaching `EPure` with a non-empty stack pops and
// applies it. Kept separate from an `EOp`'s own queue so nested parallel
// multishot resumptions never tangle (which `concat`-ing them into the queue did).
const MK: &str = "MK";
const MKNIL: &str = "MKNil";
const MKCONS: &str = "MKCons";
const MKNIL_TAG: usize = 0;
const MKCONS_TAG: usize = 1;

/// Whether `name` is one of the residual free-monad driver templates: `ebind`, a
/// per-handle driver (`{n}@handle`), or a mask driver (`{n}@mask`). Each entry to
/// one is a structural reduction turn the `prism_drive_step` counter tracks (so
/// codegen emits the bump at its head). The names are minted here, so the
/// predicate lives here. The erased-loop drivers (`{n}@loopdrv`) are direct,
/// constant-stack control flow, not the free-monad driver, so they are excluded.
#[cfg(feature = "native")]
#[must_use]
pub(crate) fn is_free_monad_driver(name: &str) -> bool {
    name == EBIND
        || name == QAPPLY
        || name.ends_with("@handle")
        || name.ends_with("@mask")
        || name.ends_with("@region")
}

// Step constructors for the state path's early-termination protocol: a fused
// producer threads `Step S` and stops when `stake` yields `SDone`.
const MORE_TAG: usize = 0;
const DONE_TAG: usize = 1;
// Type name carrying the early-termination step (its ctors are SMore/SDone).
const STEP: &str = "Step";
pub(super) const SMORE: &str = "SMore";
pub(super) const SDONE: &str = "SDone";

// Canonical `Step` constructors, shared by every lowering path that threads the
// early-termination protocol. Defined once so the tag values live in exactly one
// place (see `MORE_TAG`/`DONE_TAG`).
pub(super) fn smore(v: Value) -> Value {
    Value::Ctor(SMORE.into(), MORE_TAG, vec![v])
}

pub(super) fn sdone(v: Value) -> Value {
    Value::Ctor(SDONE.into(), DONE_TAG, vec![v])
}

// A latent op with the mask depth at which it is in flight: `depth` handlers of
// its effect must still be skipped. Replaces the old `op#d` string encoding.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct MaskOp {
    pub id: Sym,
    pub depth: u32,
}

// Per-function set of effect ops still latent in its body (used to decide which
// handlers are open).
type Latent = BTreeMap<Sym, BTreeSet<MaskOp>>;

// Evidence environment: the op id in scope mapped to the variable currently
// holding its active clause. Keyed by id so iteration is in ascending order,
// keeping evidence parameter order agreed between callers and callees.
type Env = BTreeMap<i64, Sym>;

// A lowered program: its functions, the constructor table (extended with the
// `EPure`/`EOp`/`Step` synthetics the free-monad and state paths introduce), and
// any free-monad fallback warning for the driver to surface.
pub(crate) type Lowered = (Core, BTreeMap<String, CtorInfo>, Option<String>);

// The public result of [`lower`]: like [`Lowered`] but with its whole-program
// term wrapped as `LoweredCore`, the stage tag native codegen requires. The
// internal `Lowered` stays a bare `Core` because the lowering helpers build and
// splice raw functions; only the seam that leaves the pass is stage-tagged.
pub type LowerResult = (LoweredCore, BTreeMap<String, CtorInfo>, Option<String>);

// How a `resume` application inside the clause body currently being monadified is
// reified. The three constant-stack backends each reify it differently, and at
// most one is ever active, so the mode is one enum rather than a bool per backend:
// two independent bools could in principle both be set, silently emitting two
// resume encodings, whereas the enum makes the choice mutually exclusive by
// construction. Saved and restored around each clause body (see `handle.rs`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ResumeMode {
    /// Not lowering a native/CEK clause: a resume application already yields an
    /// Eff value and is threaded as-is (the mutually-recursive driver path).
    Off,
    /// Native `{n}@region` loop: a resume yields `EResume(queue, value)`, which the
    /// loop drives by tail-calling itself on `qApply(queue, value)`.
    Native,
    /// CEK trampoline (experimental): a resume yields `EOp(RESUME_OP_ID, ...)`
    /// carrying its captured continuation queue, whose post-resume work the
    /// surrounding `ebind` snocs onto the op's queue.
    CekOp,
}

// The remaining flags are independent lowering modes (whole-program vs selective,
// early short-circuit, native effect driving), not a state machine, so they stay
// as separate booleans; the two resume-reification sub-states are unified in
// `resume` above.
#[allow(clippy::struct_excessive_bools)]
struct Lowerer {
    op_ids: BTreeMap<Sym, i64>,
    eff: BTreeSet<Sym>,
    full: bool,
    arities: BTreeMap<Sym, usize>,
    latent: Latent,
    flow: flow::ThunkFlow,
    resume_aliases: BTreeSet<Sym>,
    fresh: Fresh,
    generated: Vec<CoreFn>,
    // Set by the state path when a `stake`-style early-terminating handler is
    // present: producers then thread `Step S` and check it after each emit.
    early: bool,
    // Per fused op, how its `do op` site reconstructs the resume value with no
    // allocation: `Unit` (a write, result is unit) or `Acc` (a read, result is the
    // current accumulator). Populated by `fold_uniform`, read by `thread_st`.
    state_a: BTreeMap<Sym, state::AKind>,
    // Set by `fold_uniform` when a fold handler's answer is the producer value (a
    // get-style `return r => \s -> r`), not the accumulator (a writer `\a -> a`).
    // The threaded loop still carries the accumulator, so this mode is sound only
    // when the producer value coincides with it; the extra `thread_st` guards (a
    // non-state `return`, a producer result observed as a value) fall back rather
    // than miscompile when it does not.
    state_mode: bool,
    // Default on (opt out with `PRISM_NATIVE_EFFECTS=0`): drive eligible closed
    // handlers with a self-recursive `{n}@region` loop (a tail resume becomes a
    // queue plus `EResume`, and a function-answer state handler threads its state
    // in an accumulator) instead of a continuation thunk re-entering a mutually
    // recursive driver, so the resumed continuation is driven by a musttail
    // self-call and a parameter-passing loop runs in constant stack.
    native: bool,
    // How a `resume` in the clause body currently being monadified is reified
    // (`Native`/`CekOp`), or `Off` outside such a body. Saved/restored per clause.
    resume: ResumeMode,
    // Recorded when any handler is driven natively, so the `EResume` ctor is added
    // to the table only when it is actually used.
    used_resume: bool,
    // Behind `PRISM_CEK_SPIKE`: drive in-scope-resume full-mode handlers with the
    // CEK trampoline (constant stack) instead of the thunk-re-entrant driver.
    cek_spike: bool,
    // Whether the program uses `mask`. The CEK trampoline's skip/forward path is not
    // yet validated against masking, so a masked program keeps the proven driver.
    has_mask: bool,
    // Trampoline: defer every monadic hop that can grow the native stack into an
    // `EBounce` and drive the whole free-monad computation through one
    // `prism_drive` loop, so a deferred-resume (parameter-passing) scheduler runs
    // in constant native stack. A non-yielding fast path (see `trampoline.rs`)
    // leaves a hop that codegen already `musttail`s un-bounced, so a same-arity
    // tail loop keeps running natively; only a closure `App` and a cross-arity
    // `Call` bounce. Default on (opt out with `PRISM_TRAMPOLINE=0`): the rewrite
    // is behaviorally transparent (native-vs-interpreter parity holds byte-for-
    // byte either way) and the fast path keeps a same-arity tail loop native, so
    // it costs nothing where the stack could not grow. A whole-program rewrite of
    // the free-monad fallback only; the evidence/state fusion paths never reach it.
    trampoline: bool,
    // Per-lowering reporter for effect-lowering matcher drift. Scopes the once-per
    // -matcher stderr guard to this lowering (not a process-global static) and
    // reads `quiet` from `DynFlags`, so the diagnostic is a deterministic function
    // of (source, flags) even in a long-lived host.
    drift: DriftLog,
}

/// # Panics
/// Panics only if a program declares more than `i64::MAX` distinct effect ops.
///
/// # Errors
/// Returns [`TypeError::Ice`] if lowering reaches an internal inconsistency: an
/// op or effectful callee missing from the tables built during setup, or a
/// monadified tail that is not Eff-shaped (a compiler bug surfaced as an error
/// rather than a panic).
pub fn lower(
    core: &ElaboratedCore,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<LowerResult, TypeError> {
    let mut warning = None;
    let (c, ct, _) = lower_impl(core, ctors, flags, grades, &mut warning)?;
    Ok((LoweredCore(c), ct, warning))
}

/// No residual effects survive lowering: the program compiles to direct code.
pub const TIER_PURE: &str = "pure";
/// Evidence passing (the Identity answer): the fastest real effect lowering.
pub const TIER_EVIDENCE: &str = "evidence";
/// State fusion (the State answer): an accumulator threaded through producers.
pub const TIER_STATE_FUSION: &str = "state-fusion";
/// Free monad confined to a disjoint component, the rest still fused.
pub const TIER_LOCAL_PARTIAL: &str = "local-partial";
/// Only the effectful functions reify into the free monad; the rest stay native.
pub const TIER_SELECTIVE_FREE_MONAD: &str = "selective-free-monad";
/// Every function reifies into the free monad: the slowest, most general path.
pub const TIER_WHOLE_PROGRAM_FREE_MONAD: &str = "whole-program-free-monad";

/// The lowering tiers in cost order, cheapest first.
///
/// A program's tier moving to a later index is a performance regression; moving
/// to an earlier one is an improvement. `tests/perf_gate.rs`'s tier manifest
/// reads this ordering to tell a silent fusion-to-free-monad collapse (fail
/// loudly) from a genuine speedup (regenerate the golden). This array is the one
/// canonical list of the tier names `strategy` can return, so a new tier is added
/// here and nowhere else.
pub const EFFECT_TIERS: [&str; 6] = [
    TIER_PURE,
    TIER_EVIDENCE,
    TIER_STATE_FUSION,
    TIER_LOCAL_PARTIAL,
    TIER_SELECTIVE_FREE_MONAD,
    TIER_WHOLE_PROGRAM_FREE_MONAD,
];

/// The lowering strategy a program takes.
///
/// The single source of truth is `lower_impl` itself, so the classification can
/// never drift from the decision the compiler actually makes. One of the
/// [`EFFECT_TIERS`]: [`TIER_PURE`] (no effects survive), [`TIER_EVIDENCE`],
/// [`TIER_STATE_FUSION`], [`TIER_LOCAL_PARTIAL`] (free monad confined to a
/// component, rest fused), [`TIER_SELECTIVE_FREE_MONAD`], or
/// [`TIER_WHOLE_PROGRAM_FREE_MONAD`]. A perf snapshot pins this per program so a
/// fusion-to-free-monad regression is a reviewable diff.
///
/// # Errors
/// As [`lower`].
pub fn strategy(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> Result<&'static str, TypeError> {
    Ok(lower_impl(core, ctors, flags, grades, &mut None)?.2)
}

fn lower_impl(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
    warning: &mut Option<String>,
) -> Result<(Core, BTreeMap<String, CtorInfo>, &'static str), TypeError> {
    // Dead prelude code must not flip the program into monadic mode, so only
    // functions reachable from main are lowered (and kept) at all.
    let shaken;
    let core = if core.fns.iter().any(|f| f.name.as_str() == ENTRY_POINT) {
        let live = reachable_fns(core);
        shaken = Core {
            fns: core
                .fns
                .iter()
                .filter(|f| live.contains(&f.name))
                .cloned()
                .collect(),
        };
        &shaken
    } else {
        core
    };
    // The tier cap: `PRISM_EFFECT_TIER` names the lowest cascade rung this
    // compile may take, so a differential oracle can run one program on two
    // tiers and diff the outputs. `FreeMonad` skips the erasures and every
    // fusion rung below; `State` skips only evidence fusion; `Auto` is the full
    // ladder. Tier selection is a pure cost decision, never observable in
    // program output; `tests/tier_parity.rs` enforces that against the
    // interpreter.
    let tier = flags.effect_tier;
    // Erase escape-checked local `var` state to mutable cells before anything
    // else: a var-only program then has no residual effects and returns here,
    // and a var+effect program becomes a strictly smaller effect problem for the
    // strategies below (the var was forcing the free monad). Both erasures are
    // themselves fast tiers (a recognized shape lowers to direct control flow),
    // so the free-monad cap skips them: the var/loop handlers then reify like
    // any other effect, which is exactly the slow path being diffed.
    let (erased, used_step) = if tier == EffectTier::FreeMonad {
        (core.clone(), false)
    } else {
        let vars_gone = erase_var::erase_local_vars(core, grades);
        // Erase loop-control effects (break/continue/return) to direct control
        // flow next, so a recognized loop's control ops are gone before the
        // strategy cascade classifies the residual: a pure imperative loop then
        // classifies "pure" rather than reifying into the free monad.
        erase_control::erase_control(&vars_gone)
    };
    let core = &erased;
    // The `SMore`/`SDone` constructors the `return` erasure threads must be on the
    // constructor table for every return path below, including the `"pure"` one
    // (codegen must see them wherever the threaded body flows). Merge them into a
    // base table that shadows the input and feeds all paths.
    let base_ctors;
    let ctors = if used_step {
        let mut c = ctors.clone();
        c.insert(SMORE.into(), synth_ctor(STEP, MORE_TAG, 1));
        c.insert(SDONE.into(), synth_ctor(STEP, DONE_TAG, 1));
        base_ctors = c;
        &base_ctors
    } else {
        ctors
    };
    if !core.fns.iter().any(|f| raw_effects(&f.body)) {
        return Ok((core.clone(), ctors.clone(), TIER_PURE));
    }

    let mut op_set = BTreeSet::new();
    for f in &core.fns {
        collect_ops(&f.body, &mut op_set);
    }
    // Ids are assigned in alphabetical name order (a BTreeSet<Sym> orders by
    // intern id, which is first-seen, so sort by name explicitly to keep the
    // ev@<id> and trap order stable).
    let mut ops_sorted: Vec<Sym> = op_set.into_iter().collect();
    ops_sorted.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    let op_ids: BTreeMap<Sym, i64> = ops_sorted
        .into_iter()
        .enumerate()
        .map(|(i, n)| {
            i64::try_from(i)
                .map(|id| (n, id))
                .map_err(|_| TypeError::Ice {
                    msg: "more than i64::MAX effect ops".into(),
                })
        })
        .collect::<Result<_, _>>()?;

    let lat = latent_map(core);
    let (eff, full) = monadic_set(core, &lat);
    let thunk_flow = flow::analyze(core, &lat);
    let mut lo = Lowerer {
        op_ids,
        eff,
        full,
        arities: core.fns.iter().map(|f| (f.name, f.params.len())).collect(),
        latent: lat,
        flow: thunk_flow,
        resume_aliases: BTreeSet::new(),
        fresh: Fresh::new(),
        generated: Vec::new(),
        early: false,
        state_a: BTreeMap::new(),
        state_mode: false,
        native: flags.native_effects,
        used_resume: false,
        cek_spike: flags.cek_spike,
        has_mask: core.fns.iter().any(|f| contains_mask(&f.body)),
        resume: ResumeMode::Off,
        trampoline: flags.trampoline,
        drift: DriftLog::new(flags.quiet),
    };

    // The two fusion paths and the free-monad fallback are three answer-type
    // strategies for the same evidence translation, tried in order of how little
    // they reify: the evidence path is the Identity answer (a clause is a plain
    // thunk, `do op` is `force(ev)(args)`, resume is a direct return); the state
    // path is the State answer (a clause is a transformer `\(args, acc) -> acc'`,
    // producers thread an accumulator, and `stake` adds a `Step` short-circuit);
    // the free monad reifies the continuation when neither answer fits. They are
    // kept as separate passes deliberately: the Identity translation threads
    // values through ordinary CBPV bind, while the State translation threads an
    // explicit accumulator and splits consumer from producer, so the core `Bind`
    // and `do op` handling genuinely differs rather than sharing one traversal.
    // What they do share, the static eligibility prologue, is factored into
    // [`Lowerer::fusion_handles`].
    //
    // The evidence path subsumes the free monad whenever it applies: every
    // reachable handler tail-resumptive and every escaping effectful thunk
    // trackable to its force sites. It fully succeeds or returns None, falling
    // back here with no state to undo.
    if tier == EffectTier::Auto {
        if let Some(lowered) = lo.try_lower_ev(core) {
            return Ok((lowered, ctors.clone(), TIER_EVIDENCE));
        }
    }
    if tier != EffectTier::FreeMonad {
        if let Some(lowered) = lo.try_lower_state(core) {
            let mut ctors = ctors.clone();
            if lo.early {
                ctors.insert(SMORE.into(), synth_ctor(STEP, MORE_TAG, 1));
                ctors.insert(SDONE.into(), synth_ctor(STEP, DONE_TAG, 1));
            }
            return Ok((lowered, ctors, TIER_STATE_FUSION));
        }

        // Global fusion failed. Before paying the free monad for the whole program,
        // try to confine it: if the escaping effectful closure lives in a component
        // whose effects are disjoint from the rest, free-monad only that component
        // and keep the rest fused (local monadification). Bails to whole-program when
        // the split is not clean, so it never regresses a program that compiles today.
        if let Some((c, ct, w)) = lo.try_local(core, ctors)? {
            *warning = w;
            return Ok((c, ct, TIER_LOCAL_PARTIAL));
        }
    }

    // Neither fusion path applied and the escape is not confinable, so the
    // continuation is reified into the free monad (EOp cells), the slow path.
    // Hand the driver a warning naming the functions that lost fusion and why,
    // so the fallback is surfaced rather than taken silently. The latent fixpoint
    // does not enter thunk bodies, so a function whose only effect is a raw `do` in
    // an escaping closure has an empty latent set; add those capturing functions so
    // a program forced whole-program purely by such an escape still names a culprit.
    let mut lost = genuine_eff(&lo.latent);
    for f in &core.fns {
        let mut thunks = Vec::new();
        thunks_in_comp(&f.body, &mut thunks);
        if thunks.iter().any(|t| raw_effects(t)) {
            lost.insert(f.name);
        }
    }
    *warning = free_monad_warning(core, &lost, &lo.latent);

    let entries: BTreeSet<Sym> = if lo.eff.contains(&Sym::new(ENTRY_POINT)) {
        std::iter::once(Sym::from(ENTRY_POINT)).collect()
    } else {
        BTreeSet::new()
    };
    let refs: Vec<&CoreFn> = core.fns.iter().collect();
    let mut fns = lo.lower_set(&refs, &entries)?;
    // The appended drivers are closed by construction, so no hygiene pass is
    // needed. A per-handler driver takes `[res] ++ fvs` as parameters, where
    // `fvs` is `fv::comp_without` of its clause bodies (gathered in
    // `lower_handle`): every free term variable of the body is therefore a
    // parameter, and every other name in it is either one of its own `{n}@hint`
    // fresh binders (a digit-led namespace of their own, see `names::lowered`)
    // or a top-level name it calls (the recursive driver, `ebind`, the
    // `EOp`/`EPure` ctors, a program function). `ebind` and the mask drivers
    // bind only the fixed `names::*` set, whose `@` is unforgeable in source, and
    // the drivers reference one another only by `Call`, never by lexical nesting,
    // so a fixed binder can never capture another driver's free occurrence.
    fns.extend(std::mem::take(&mut lo.generated));
    fns.push(ebind_fn());
    fns.push(qapply_fn());
    let monadic: BTreeSet<Sym> = if lo.full {
        fns.iter().map(|f| f.name).collect()
    } else {
        lo.eff.clone()
    };
    let refs: Vec<&CoreFn> = fns.iter().collect();
    check_convention_boundaries(&fns, &refs, &monadic, lo.full, &entries)?;

    // Run the trampoline as a semantics-preserving rewrite AFTER the boundary
    // check has validated the (untrampolined) monadic structure: it defers every
    // monadic hop into an `EBounce` and inserts `prism_drive` at each Eff-inspect
    // site, so the unbounded tail-call chain runs in constant native stack.
    if lo.trampoline && lo.full {
        trampoline::trampolinize(&mut fns, &mut lo.fresh);
        fns.push(trampoline::prism_drive_fn());
    }

    let mut ctors = ctors.clone();
    ctors.insert(EPURE.into(), synth_ctor(EFF, PURE_TAG, 1));
    ctors.insert(EOP.into(), synth_ctor(EFF, OP_TAG, 4));
    ctors.insert(TQNIL.into(), synth_ctor(TQ, TQNIL_TAG, 0));
    ctors.insert(TQCONS.into(), synth_ctor(TQ, TQCONS_TAG, 2));
    if lo.used_resume {
        ctors.insert(ERESUME.into(), synth_ctor(EFF, RESUME_TAG, 2));
    }
    if lo.cek_spike {
        ctors.insert(MKNIL.into(), synth_ctor(MK, MKNIL_TAG, 0));
        ctors.insert(MKCONS.into(), synth_ctor(MK, MKCONS_TAG, 2));
    }
    if lo.trampoline && lo.full {
        ctors.insert(EBOUNCE.into(), synth_ctor(EFF, BOUNCE_TAG, 1));
    }

    let strat = if lo.full {
        TIER_WHOLE_PROGRAM_FREE_MONAD
    } else {
        TIER_SELECTIVE_FREE_MONAD
    };
    Ok((Core { fns }, ctors, strat))
}

impl Lowerer {
    // Every op reaching lowering was assigned an id by collect_ops. Aliasing
    // a missed op to id 0 would silently misroute handler dispatch.
    fn op_id(&self, op: Sym) -> Result<i64, TypeError> {
        self.op_ids.get(&op).copied().ok_or_else(|| TypeError::Ice {
            msg: format!("effect op `{op}` escaped collect_ops"),
        })
    }

    fn fresh(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }
}
