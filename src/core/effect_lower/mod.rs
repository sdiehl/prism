use std::collections::{BTreeMap, BTreeSet};

use super::cbpv::{reachable_fns, Comp, Core, CoreFn, HandleOp, Value};
use crate::error::TypeError;
use crate::fresh::Fresh;
use crate::names::{self, ENTRY_POINT};
use crate::sym::Sym;
use crate::types::CtorInfo;

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
mod walk;

use analysis::{latent_map, monadic_set};
use checks::{check_convention_boundaries, raw_effects};
use diagnostics::{free_monad_warning, genuine_eff};
use runtime::{ebind_fn, qapply_fn, synth_ctor};
use walk::collect_ops;

pub use analysis::latent_ops;
pub use checks::residual_effects;
use walk::{contains_mask, each_subcomp, each_value, latent, thunks_in_value};

// Compile algebraic effects to plain closures and data by a free-monad
// translation. A computation that may perform effects is reified into a value
// of the result type:
//
//   EPure(v)              a finished computation returning v
//   EOp(id, skip, arg, k) a suspended `do op(arg)` whose continuation is k
//
// `ebind` threads a continuation through this representation. Each `handle`
// becomes a recursive driver that pattern-matches the result: EPure runs the
// return clause, EOp dispatches to the matching operation with `resume` bound
// to a closure that re-enters the driver. Because `k` is an ordinary reusable
// closure, resumptions are multishot.
//
// A handler is "open" when its body performs effects it does not itself
// catch: the driver then forwards (re-emits) the unhandled `EOp` outward with
// a continuation that re-enters this driver, so an outer handler discharges it
// and resumption flows back through here. Open drivers return Eff values and
// their clauses are monadified. "Closed" drivers (the common case, including
// the parameter-passing `k(v)(s)` idiom) return bare values and are unchanged.
//
// When effectful code escapes first-class through a thunk, no static analysis
// can tell monadified callees apart at dynamic call sites, so lowering falls
// back to whole-program monadic mode: every function, lambda and thunk body is
// monadified, every handler is driven open-style, and `main` unwraps the final
// EPure, trapping on an op that reaches the top like the interpreter's
// unhandled-effect error.
//
// Mask is an explicit depth, mirroring the interpreter's `skip` counter
// (`eval/mod.rs`): an in-flight `EOp` carries `skip`, the number of matching
// handlers it must still bypass. A mask driver increments `skip` on ops of its
// effect passing through it. A handler driver matches purely on `id` equality;
// when an op is its own but `skip > 0`, it forwards with `skip - 1`, consuming
// one level, exactly as the interpreter decrements on a `Frame::Handle`
// crossing. Fresh ops start at `skip = 0`.

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

// The result of `taq_uncons`: `TQNil` (empty queue) or `TQCons(head, tail)`. Its
// own small ADT so `qApply` can pattern-match the C primitive's return.
const TQ: &str = "TQ";
const TQNIL: &str = "TQNil";
const TQCONS: &str = "TQCons";
const TQNIL_TAG: usize = 0;
const TQCONS_TAG: usize = 1;

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

// The flags are independent lowering modes (whole-program vs selective, early
// short-circuit, native effect driving and its two sub-states), not a state
// machine an enum would model, so they stay as separate booleans.
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
    // handlers with a self-recursive `{n}@region` loop -- a tail resume becomes a
    // queue plus `EResume`, a function-answer state handler threads its state in an
    // accumulator -- instead of a continuation thunk re-entering a mutually
    // recursive driver, so the resumed continuation is driven by a musttail
    // self-call and a parameter-passing loop runs in constant stack.
    native: bool,
    // Set while lowering a native clause body: a resume application then yields
    // `EResume(queue, value)` for the `{n}@region` loop to drive.
    native_resume: bool,
    // Recorded when any handler is driven natively, so the `EResume` ctor is added
    // to the table only when it is actually used.
    used_resume: bool,
}

/// # Panics
/// Panics only if a program declares more than `i64::MAX` distinct effect ops.
///
/// # Errors
/// Returns [`TypeError::Ice`] if lowering reaches an internal inconsistency: an
/// op or effectful callee missing from the tables built during setup, or a
/// monadified tail that is not Eff-shaped (a compiler bug surfaced as an error
/// rather than a panic).
pub fn lower(core: &Core, ctors: &BTreeMap<String, CtorInfo>) -> Result<Lowered, TypeError> {
    let mut warning = None;
    let (c, ct, _) = lower_impl(core, ctors, &mut warning)?;
    Ok((c, ct, warning))
}

/// The lowering strategy a program takes.
///
/// The single source of truth is [`lower_impl`] itself, so the classification can
/// never drift from the decision the compiler actually makes. One of: `pure` (no
/// effects survive), `evidence`, `state-fusion`, `local-partial` (free monad
/// confined to a component, rest fused), `whole-program-free-monad`, or
/// `selective-free-monad`. A perf snapshot pins this per program so a
/// fusion-to-free-monad regression is a reviewable diff.
///
/// # Errors
/// As [`lower`].
pub fn strategy(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<&'static str, TypeError> {
    Ok(lower_impl(core, ctors, &mut None)?.2)
}

fn lower_impl(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    warning: &mut Option<String>,
) -> Result<(Core, BTreeMap<String, CtorInfo>, &'static str), TypeError> {
    // Dead prelude code must not flip the program into monadic mode, so only
    // functions reachable from main are lowered (and kept) at all.
    let shaken;
    let core = if core.fns.iter().any(|f| f.name == ENTRY_POINT) {
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
    // Erase escape-checked local `var` state to mutable cells before anything
    // else: a var-only program then has no residual effects and returns here,
    // and a var+effect program becomes a strictly smaller effect problem for the
    // strategies below (the var was forcing the free monad).
    let erased = erase_var::erase_local_vars(core);
    // Erase loop-control effects (break/continue/return) to direct control flow
    // next, so a recognized loop's control ops are gone before the strategy
    // cascade classifies the residual: a pure imperative loop then classifies
    // "pure" rather than reifying into the free monad.
    let (erased, used_step) = erase_control::erase_control(&erased);
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
        return Ok((core.clone(), ctors.clone(), "pure"));
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
        native: std::env::var("PRISM_NATIVE_EFFECTS").map_or(true, |v| v != "0"),
        native_resume: false,
        used_resume: false,
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
    if let Some(lowered) = lo.try_lower_ev(core) {
        return Ok((lowered, ctors.clone(), "evidence"));
    }
    if let Some(lowered) = lo.try_lower_state(core) {
        let mut ctors = ctors.clone();
        if lo.early {
            ctors.insert(SMORE.into(), synth_ctor(STEP, MORE_TAG, 1));
            ctors.insert(SDONE.into(), synth_ctor(STEP, DONE_TAG, 1));
        }
        return Ok((lowered, ctors, "state-fusion"));
    }

    // Global fusion failed. Before paying the free monad for the whole program,
    // try to confine it: if the escaping effectful closure lives in a component
    // whose effects are disjoint from the rest, free-monad only that component
    // and keep the rest fused (local monadification). Bails to whole-program when
    // the split is not clean, so it never regresses a program that compiles today.
    if let Some((c, ct, w)) = lo.try_local(core, ctors)? {
        *warning = w;
        return Ok((c, ct, "local-partial"));
    }

    // Neither fusion path applied and the escape is not confinable, so the
    // continuation is reified into the free monad (EOp cells), the slow path.
    // Hand the driver a warning naming the functions that lost fusion and why,
    // so the fallback is surfaced rather than taken silently.
    *warning = free_monad_warning(core, &genuine_eff(&lo.latent), &lo.latent);

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

    let mut ctors = ctors.clone();
    ctors.insert(EPURE.into(), synth_ctor(EFF, PURE_TAG, 1));
    ctors.insert(EOP.into(), synth_ctor(EFF, OP_TAG, 4));
    ctors.insert(TQNIL.into(), synth_ctor(TQ, TQNIL_TAG, 0));
    ctors.insert(TQCONS.into(), synth_ctor(TQ, TQCONS_TAG, 2));
    if lo.used_resume {
        ctors.insert(ERESUME.into(), synth_ctor(EFF, RESUME_TAG, 2));
    }

    let strat = if lo.full {
        "whole-program-free-monad"
    } else {
        "selective-free-monad"
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

// Rebuild `c`, applying `g` to every immediate sub-computation and to every
// thunk body in immediate values: the single structural recursion the
// recognize-or-leave Core passes (`erase_var`, `erase_control`) share.
pub(super) fn map_kids<G: FnMut(&Comp) -> Comp>(c: &Comp, g: &mut G) -> Comp {
    let vals = |args: &[Value], g: &mut G| args.iter().map(|a| map_val(a, g)).collect();
    match c {
        Comp::Bind(m, x, n) => Comp::Bind(Box::new(g(m)), *x, Box::new(g(n))),
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(g(b))),
        Comp::App(f, args) => Comp::App(Box::new(g(f)), vals(args, g)),
        Comp::If(v, t, e) => Comp::If(map_val(v, g), Box::new(g(t)), Box::new(g(e))),
        Comp::Case(v, arms) => {
            let v = map_val(v, g);
            Comp::Case(v, arms.iter().map(|(p, b)| (p.clone(), g(b))).collect())
        }
        Comp::Mask(ops, b) => Comp::Mask(ops.clone(), Box::new(g(b))),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(g(body)),
            return_var: *return_var,
            return_body: return_body.as_ref().map(|rb| Box::new(g(rb))),
            ops: ops
                .iter()
                .map(|op| HandleOp {
                    name: op.name,
                    params: op.params.clone(),
                    resume: op.resume,
                    body: g(&op.body),
                })
                .collect(),
        },
        Comp::Return(v) => Comp::Return(map_val(v, g)),
        Comp::Force(v) => Comp::Force(map_val(v, g)),
        Comp::Print(v) => Comp::Print(map_val(v, g)),
        Comp::PrintF(v) => Comp::PrintF(map_val(v, g)),
        Comp::PrintS(v) => Comp::PrintS(map_val(v, g)),
        Comp::Error(v) => Comp::Error(map_val(v, g)),
        Comp::Srand(v) => Comp::Srand(map_val(v, g)),
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, map_val(v, g)),
        Comp::Dup(v) => Comp::Dup(map_val(v, g)),
        Comp::Drop(v) => Comp::Drop(map_val(v, g)),
        Comp::Prim(op, a, b) => Comp::Prim(*op, map_val(a, g), map_val(b, g)),
        Comp::Call(n, args) => Comp::Call(*n, vals(args, g)),
        Comp::Do(op, args) => Comp::Do(*op, vals(args, g)),
        Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, vals(args, g)),
        Comp::RefNew(v) => Comp::RefNew(map_val(v, g)),
        Comp::RefGet(v) => Comp::RefGet(map_val(v, g)),
        Comp::RefSet(a, b) => Comp::RefSet(map_val(a, g), map_val(b, g)),
        Comp::WithReuse { token, freed, body } => Comp::WithReuse {
            token: *token,
            freed: map_val(freed, g),
            body: Box::new(g(body)),
        },
        Comp::Reuse(tok, v) => Comp::Reuse(*tok, map_val(v, g)),
        Comp::PrintNl | Comp::ReadInt | Comp::ReadLine | Comp::Rand => c.clone(),
    }
}

pub(super) fn map_val<G: FnMut(&Comp) -> Comp>(v: &Value, g: &mut G) -> Value {
    match v {
        Value::Thunk(c) => Value::Thunk(Box::new(g(c))),
        Value::Ctor(n, t, fs) => Value::Ctor(*n, *t, fs.iter().map(|f| map_val(f, g)).collect()),
        Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| map_val(f, g)).collect()),
        _ => v.clone(),
    }
}
