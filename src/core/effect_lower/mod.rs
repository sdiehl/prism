use std::collections::{BTreeMap, BTreeSet};
use std::slice;

use super::builtins::Builtin;
use super::cbpv::{reachable_fns, Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use super::fv;
use crate::error::TypeError;
use crate::fresh::Fresh;
use crate::names::{self, ENTRY_POINT};
use crate::sym::Sym;
use crate::types::{CtorInfo, Type};

mod erase_control;
mod erase_var;
mod evidence;
mod flow;
mod state;

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

// A lowered program: its functions plus the constructor table (extended with the
// `EPure`/`EOp`/`Step` synthetics the free-monad and state paths introduce).
type Lowered = (Core, BTreeMap<String, CtorInfo>);

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
pub fn lower(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<(Core, BTreeMap<String, CtorInfo>), TypeError> {
    let (c, ct, _) = lower_impl(core, ctors)?;
    Ok((c, ct))
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
    Ok(lower_impl(core, ctors)?.2)
}

fn lower_impl(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
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
    if let Some((c, ct)) = lo.try_local(core, ctors)? {
        return Ok((c, ct, "local-partial"));
    }

    // Neither fusion path applied and the escape is not confinable, so the
    // continuation is reified into the free monad (EOp cells), the slow path.
    // Default-on warning (silenceable with `PRISM_QUIET`) names the functions
    // that lost fusion and why.
    warn_free_monad(core, &genuine_eff(&lo.latent), &lo.latent);

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

// Default-on diagnostic for the free-monad fallback. Falling off the fused
// evidence/state path is a real performance event (handlers reify into per-op
// `EOp` cells instead of fusing), so it is announced unless `PRISM_QUIET` is
// set. It names the monadified functions and the specific cause, so a hot
// pipeline can be steered back onto a fused path. It fires only here, in the
// fallback, so a fully fused program is silent (zero false positives).
// `monadified` is the set that actually reified into EOp cells: in whole-program
// mode the genuinely effectful functions, in local mode just the entangled
// component (so the warning names the few functions that lost fusion, not the
// whole program). Causes are reported only for those functions, so a fused
// pipeline sharing the program is never blamed.
fn warn_free_monad(core: &Core, monadified: &BTreeSet<Sym>, fl: &Latent) {
    if std::env::var_os("PRISM_QUIET").is_some() {
        return;
    }
    let mut names: Vec<&str> = monadified.iter().map(|s| s.as_str()).collect();
    names.sort_unstable();
    if names.is_empty() {
        return;
    }
    let causes = free_monad_causes(core, monadified, fl);
    let why = if causes.is_empty() {
        // No structural cause matched: a reachable handler is not tail-resumptive
        // (it captures or multiply-applies `resume`), so its continuation is reified.
        "a handler reifies its continuation (not tail-resumptive)".to_string()
    } else {
        causes.join("; ")
    };
    eprintln!(
        "warning: effect lowering fell off the fused path: {why}. {} function(s) now \
         reify into EOp cells per operation instead of fusing: {}. \
         Call effectful functions directly instead of through a first-class value, or \
         restructure the handler, to refuse. Silence with PRISM_QUIET.",
        names.len(),
        names.join(", ")
    );
}

// The genuinely effectful functions: those with a non-empty latent set. This is
// the natural per-function monadic set, before any whole-program inflation.
fn genuine_eff(fl: &Latent) -> BTreeSet<Sym> {
    fl.iter()
        .filter(|(_, s)| !s.is_empty())
        .map(|(n, _)| *n)
        .collect()
}

// The reasons a program fell to the free monad, each naming the offending
// function and the construct (an effectful closure at an apply site, a raw
// do/handle captured in a thunk, or an open handler whose resume escapes). Only
// the `monadified` functions are scanned, so a fused combinator in the same
// program (whose thunk legitimately performs effects) is not falsely blamed. The
// Core IR carries no source spans, so the function name is the locator.
fn free_monad_causes(core: &Core, monadified: &BTreeSet<Sym>, fl: &Latent) -> Vec<String> {
    let eff = genuine_eff(fl);
    let mut causes = Vec::new();
    for f in core.fns.iter().filter(|f| monadified.contains(&f.name)) {
        let mut thunks = Vec::new();
        thunks_in_comp(&f.body, &mut thunks);
        let captures_effect = thunks.iter().any(|body| {
            let mut heads = BTreeSet::new();
            all_calls(body, &mut heads);
            !heads.is_disjoint(&eff) || raw_effects(body)
        });
        if captures_effect {
            causes.push(format!(
                "`{}` captures an effectful computation in a first-class closure",
                f.name
            ));
        }
        if open_resume_escapes(&f.body, fl) {
            causes.push(format!("`{}` has a handler whose resume escapes", f.name));
        }
        if contains_mask(&f.body) {
            causes.push(format!("`{}` uses `mask`, which disables fusion", f.name));
        }
    }
    // An effect that reaches `main` unhandled is monadified to trap at the top
    // (the interpreter's unhandled-effect error), the same as today.
    if monadified.contains(&Sym::new(ENTRY_POINT))
        && fl
            .get(&Sym::new(ENTRY_POINT))
            .is_some_and(|s| !s.is_empty())
    {
        causes.push("an effect reaches `main` unhandled".to_string());
    }
    causes
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

    // A right-associative `id == k` cascade: for each op, when `scrut` equals
    // its id run the branch `make` produces, else fall through to the next. The
    // last falls through to `fallthrough`. Built back-to-front (each branch then
    // its test var) so the emitted tree and fresh-var order are exactly the
    // hand-rolled form. Drives all three dispatch sites (handler/forward/mask).
    fn build_op_chain(
        &mut self,
        scrut: &Value,
        ids: &[i64],
        mut make: impl FnMut(&mut Self, usize) -> Result<Comp, TypeError>,
        fallthrough: Comp,
    ) -> Result<Comp, TypeError> {
        let mut acc = fallthrough;
        for i in (0..ids.len()).rev() {
            let then = make(self, i)?;
            let t = self.fresh("t");
            acc = Comp::Bind(
                Box::new(Comp::Prim(CoreOp::Eq, scrut.clone(), Value::Int(ids[i]))),
                t,
                Box::new(Comp::If(Value::Var(t), Box::new(then), Box::new(acc))),
            );
        }
        Ok(acc)
    }

    // A handler is open when its body performs an effect it does not catch.
    // Whole-program mode drives every handler open-style for uniformity.
    fn is_open(&self, body: &Comp, ops: &[HandleOp]) -> bool {
        if self.full {
            return true;
        }
        let mut s = BTreeSet::new();
        latent(body, &self.latent, &mut s);
        for op in ops {
            s.remove(&MaskOp {
                id: op.name,
                depth: 0,
            });
        }
        !s.is_empty()
    }

    fn is_resume_app(&self, f: &Comp) -> bool {
        matches!(f, Comp::Force(Value::Var(v)) if self.resume_aliases.contains(v))
    }

    // Structural pass over the whole program: rewrite every `handle` into a
    // call to a generated driver, leaving non-effectful code untouched.
    fn lower_comp(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        Ok(match c {
            Comp::Handle { body, ops, .. } if self.is_open(body, ops) => {
                let e = self.fresh("e");
                let x = self.fresh("ex");
                Comp::Bind(
                    Box::new(self.lower_handle(c)?),
                    e,
                    Box::new(Comp::Case(
                        Value::Var(e),
                        vec![
                            (
                                ctor_pat(EPURE, slice::from_ref(&x)),
                                Comp::Return(Value::Var(x)),
                            ),
                            (
                                ctor_pat(
                                    EOP,
                                    &["_fi".into(), "_fs".into(), "_fa".into(), "_fk".into()],
                                ),
                                Comp::Error(Value::Str(
                                    "ICE: effect op escaped a closed handler".into(),
                                )),
                            ),
                        ],
                    )),
                )
            }
            Comp::Handle { .. } => self.handle_closed(c)?,
            // A mask reached outside monadic context has no escaping ops to
            // relabel, so it is the identity on its body.
            Comp::Mask(_, b) => self.lower_comp(b)?,
            Comp::Bind(m, x, n) => {
                if let Some(c) = self.try_lower_fn_answer(m, *x, n)? {
                    c
                } else {
                    Comp::Bind(
                        Box::new(self.lower_comp(m)?),
                        *x,
                        Box::new(self.lower_comp(n)?),
                    )
                }
            }
            Comp::If(v, t, e) => Comp::If(
                v.clone(),
                Box::new(self.lower_comp(t)?),
                Box::new(self.lower_comp(e)?),
            ),
            Comp::Case(v, arms) => Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Ok((p.clone(), self.lower_comp(b)?)))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.lower_comp(b)?)),
            Comp::App(f, args) => Comp::App(Box::new(self.lower_comp(f)?), args.clone()),
            other => other.clone(),
        })
    }

    // Monadic translation: produce a computation whose result is an Eff value.
    fn mon(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        Ok(match c {
            Comp::Return(v) => {
                let v = self.mon_value(v)?;
                epure(v)
            }
            Comp::Bind(m, x, n) => {
                // The elaborator routes a resume through `return k to tmp` before
                // applying it, so propagate the alias to keep recognizing it.
                if let Comp::Return(Value::Var(v)) = m.as_ref() {
                    if self.resume_aliases.contains(v) {
                        self.resume_aliases.insert(*x);
                    }
                }
                let mv = self.fresh("m");
                let f = Value::Thunk(Box::new(Comp::Lam(vec![*x], Box::new(self.mon(n)?))));
                Comp::Bind(
                    Box::new(self.mon(m)?),
                    mv,
                    Box::new(Comp::Call(EBIND.into(), vec![Value::Var(mv), f])),
                )
            }
            Comp::Do(op, args) => {
                let id = self.op_id(*op)?;
                let arg = match args.len() {
                    0 => Value::Unit,
                    1 => self.mon_value(&args[0])?,
                    _ => Value::Tuple(args.iter().map(|a| self.mon_value(a)).collect::<Result<
                        _,
                        TypeError,
                    >>(
                    )?),
                };
                // A fresh op's continuation queue is empty (Unit): `qApply(empty,
                // v) = EPure(v)`. `ebind` snocs onto it as the op propagates.
                Comp::Return(Value::Ctor(
                    EOP.into(),
                    OP_TAG,
                    vec![Value::Int(id), Value::Int(0), arg, Value::Unit],
                ))
            }
            Comp::If(v, t, e) => {
                Comp::If(v.clone(), Box::new(self.mon(t)?), Box::new(self.mon(e)?))
            }
            Comp::Case(v, arms) => Comp::Case(
                self.mon_value(v)?,
                arms.iter()
                    .map(|(p, b)| Ok((p.clone(), self.mon(b)?)))
                    .collect::<Result<_, TypeError>>()?,
            ),
            // Driving the resume natively: `resume` is bound to the op's
            // continuation queue, so applying it yields `EResume(queue, value)`,
            // which the `{n}@region` loop drives by tail-calling itself on
            // `qApply(queue, value)`. Eligibility guarantees this is in tail
            // position, so the `EResume` is the clause's result.
            Comp::App(f, args) if self.native_resume && self.is_resume_app(f) => {
                let Comp::Force(Value::Var(q)) = f.as_ref() else {
                    unreachable!("is_resume_app matched a non-Force(Var)")
                };
                let arg = match args.len() {
                    0 => Value::Unit,
                    1 => self.mon_value(&args[0])?,
                    _ => Value::Tuple(args.iter().map(|a| self.mon_value(a)).collect::<Result<
                        _,
                        TypeError,
                    >>(
                    )?),
                };
                Comp::Return(Value::Ctor(
                    ERESUME.into(),
                    RESUME_TAG,
                    vec![Value::Var(*q), arg],
                ))
            }
            // Applying the current resume already yields an Eff value (the
            // re-driven continuation), so thread it instead of EPure-wrapping.
            Comp::App(f, args) if self.is_resume_app(f) => Comp::App(f.clone(), args.clone()),
            // In whole-program mode every closure body is monadic, so any
            // dynamic application already yields an Eff value.
            Comp::App(f, args) if self.full => Comp::App(
                Box::new(self.mon_head(f)?),
                args.iter()
                    .map(|a| self.mon_value(a))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Comp::Mask(ops, body) => {
                let driver = self.mask_driver(ops)?;
                let v = self.fresh("m");
                Comp::Bind(
                    Box::new(self.mon(body)?),
                    v,
                    Box::new(Comp::Call(driver, vec![Value::Var(v)])),
                )
            }
            Comp::Handle { body, ops, .. } if self.is_open(body, ops) => self.lower_handle(c)?,
            Comp::Handle { .. } => {
                let v = self.fresh("h");
                Comp::Bind(
                    Box::new(self.handle_closed(c)?),
                    v,
                    Box::new(epure(Value::Var(v))),
                )
            }
            // A call to an effectful function already yields an Eff value. A
            // partial application (whole-program mode) yields a bare closure,
            // so lift it; the closure body is monadic once saturated.
            Comp::Call(g, args) if self.eff.contains(g) => {
                let args: Vec<Value> =
                    args.iter()
                        .map(|a| self.mon_value(a))
                        .collect::<Result<_, TypeError>>()?;
                let arity = self.arities.get(g).copied().ok_or_else(|| TypeError::Ice {
                    msg: format!("effectful call to unknown function `{g}`"),
                })?;
                let partial = self.full && args.len() < arity;
                let call = Comp::Call(*g, args);
                if partial {
                    let v = self.fresh("p");
                    Comp::Bind(Box::new(call), v, Box::new(epure(Value::Var(v))))
                } else {
                    call
                }
            }
            // Effect-free computations: run, then lift the result with EPure.
            Comp::Error(_) => c.clone(),
            _ => {
                let v = self.fresh("p");
                Comp::Bind(
                    Box::new(self.lower_comp(c)?),
                    v,
                    Box::new(epure(Value::Var(v))),
                )
            }
        })
    }

    // Whole-program mode rewrites every thunk so its body is monadic. Outside
    // that mode values pass through untouched.
    fn mon_value(&mut self, v: &Value) -> Result<Value, TypeError> {
        if !self.full {
            return Ok(v.clone());
        }
        Ok(match v {
            Value::Thunk(c) => Value::Thunk(Box::new(match c.as_ref() {
                Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.mon(b)?)),
                other => self.mon(other)?,
            })),
            Value::Ctor(n, t, fs) => Value::Ctor(
                *n,
                *t,
                fs.iter()
                    .map(|x| self.mon_value(x))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Value::Tuple(fs) => Value::Tuple(
                fs.iter()
                    .map(|x| self.mon_value(x))
                    .collect::<Result<_, TypeError>>()?,
            ),
            _ => v.clone(),
        })
    }

    fn mon_head(&mut self, f: &Comp) -> Result<Comp, TypeError> {
        Ok(match f {
            Comp::Force(v) => Comp::Force(self.mon_value(v)?),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.mon(b)?)),
            Comp::App(g, args) => Comp::App(
                Box::new(self.mon_head(g)?),
                args.iter()
                    .map(|a| self.mon_value(a))
                    .collect::<Result<_, TypeError>>()?,
            ),
            other => other.clone(),
        })
    }

    // An entry to a monadic region returns Eff; unwrap its final EPure to the
    // bare value its (direct-convention) caller expects, and trap on an op that
    // escaped every handler, naming it like the interpreter's unhandled-effect
    // error. `main` is the canonical entry (the runtime calls it); under local
    // monadification every component function a fused caller invokes is one too.
    fn unwrap_main(&mut self, body: Comp) -> Comp {
        let r = self.fresh("r");
        let x = self.fresh("x");
        let id = self.fresh("id");
        let ops: Vec<(Sym, i64)> = self.op_ids.iter().map(|(n, i)| (*n, *i)).collect();
        let mut trap = Comp::Error(Value::Str("unhandled effect".into()));
        for (name, opid) in ops.into_iter().rev() {
            let t = self.fresh("t");
            trap = Comp::Bind(
                Box::new(Comp::Prim(CoreOp::Eq, Value::Var(id), Value::Int(opid))),
                t,
                Box::new(Comp::If(
                    Value::Var(t),
                    Box::new(Comp::Error(Value::Str(format!(
                        "unhandled effect `{name}`"
                    )))),
                    Box::new(trap),
                )),
            );
        }
        Comp::Bind(
            Box::new(body),
            r,
            Box::new(Comp::Case(
                Value::Var(r),
                vec![
                    (
                        ctor_pat(EPURE, slice::from_ref(&x)),
                        Comp::Return(Value::Var(x)),
                    ),
                    (
                        ctor_pat(EOP, &[id, "_us".into(), "_ua".into(), "_uk".into()]),
                        trap,
                    ),
                ],
            )),
        )
    }

    // Lower a set of functions on the free-monad path: monadify the effectful
    // ones (`self.eff`), leave the rest direct, and unwrap each entry. Shared by
    // the whole-program fallback and the local-monadification region.
    fn lower_set(
        &mut self,
        fns: &[&CoreFn],
        entries: &BTreeSet<Sym>,
    ) -> Result<Vec<CoreFn>, TypeError> {
        fns.iter()
            .map(|f| {
                let body = if self.eff.contains(&f.name) {
                    self.mon(&f.body)?
                } else {
                    self.lower_comp(&f.body)?
                };
                // Trap an effect that escaped every handler whenever the function
                // is a monadic entry, not only in whole-program mode: an unhandled
                // effect would otherwise flow out as a bare `EOp`, silently
                // diverging from the interpreter, which raises `unhandled effect`.
                let body = if entries.contains(&f.name) && self.eff.contains(&f.name) {
                    self.unwrap_main(body)
                } else {
                    body
                };
                Ok(CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    body,
                })
            })
            .collect()
    }

    // The functions whose body lets an effectful closure escape untrackably, or
    // whose open handler's resume escapes: the seeds of the monadic region.
    fn escaping_set(&self, core: &Core) -> BTreeSet<Sym> {
        let mut s = flow::escaping_fns(core, &self.latent, &self.flow);
        for f in &core.fns {
            if open_resume_escapes(&f.body, &self.latent) {
                s.insert(f.name);
            }
        }
        s
    }

    // Local monadification. When an effectful closure escapes, confine the free
    // monad to the flow/effect-connected component that contains it and keep
    // everything else fused. Returns the fully lowered program when the split
    // is clean, or None to fall back to whole-program monadification (sound, no
    // regression). The cleanliness is structural: the component's effect ops are
    // disjoint from the rest (so no boundary call crosses a live effect), and no
    // thunk crosses the boundary as a call argument or entry result (so the two
    // calling conventions never meet on a first-class value); `monadic_region`
    // returns None otherwise.
    fn try_local(
        &mut self,
        core: &Core,
        base_ctors: &BTreeMap<String, CtorInfo>,
    ) -> Result<Option<Lowered>, TypeError> {
        let escaping = self.escaping_set(core);
        if escaping.is_empty() {
            return Ok(None);
        }
        let Some((region, entries)) = monadic_region(core, &self.latent, &escaping) else {
            return Ok(None);
        };
        // `main` must be fusable (in the rest) for the rest to fuse at all; if it
        // is in the region the rest-fusion guard rejects it anyway.
        if region.contains(&Sym::new(ENTRY_POINT)) {
            return Ok(None);
        }

        // Below here `self.eff`/`full`/`early`/`generated` are reconfigured for
        // the two sub-lowerings. Save them so any bail restores the whole-program
        // state `monadic_set` chose, which the fallback then uses unchanged.
        let saved_eff = std::mem::take(&mut self.eff);
        let saved_full = self.full;
        let restore = |me: &mut Self, eff: BTreeSet<Sym>, full: bool| {
            me.eff = eff;
            me.full = full;
            me.early = false;
            me.generated.clear();
        };

        // Fuse the rest. Evidence threading appends evidence for genuinely
        // effectful functions only, so reset `eff` from the whole-program
        // inflation `monadic_set` returned.
        let rest = Core {
            fns: core
                .fns
                .iter()
                .filter(|f| !region.contains(&f.name))
                .cloned()
                .collect(),
        };
        self.eff = genuine_eff(&self.latent);
        self.full = false;
        self.early = false;
        let (fused, early) = if let Some(c) = self.try_lower_ev(&rest) {
            (c, false)
        } else if let Some(c) = self.try_lower_state(&rest) {
            (c, self.early)
        } else {
            restore(self, saved_eff, saved_full);
            return Ok(None);
        };

        // Free-monad the region, full-style: a uniform monadic convention within
        // it so the escaping closure's dynamic applies all agree.
        self.eff.clone_from(&region);
        self.full = true;
        self.early = false;
        self.generated.clear();
        let region_fns: Vec<&CoreFn> = core
            .fns
            .iter()
            .filter(|f| region.contains(&f.name))
            .collect();
        let mon_fns = self.lower_set(&region_fns, &entries)?;

        let mut fns = fused.fns;
        fns.extend(mon_fns);
        let generated = std::mem::take(&mut self.generated);
        let mut full_style: BTreeSet<Sym> = region.clone();
        full_style.extend(generated.iter().map(|f| f.name));
        full_style.insert(EBIND.into());
        full_style.insert(QAPPLY.into());
        fns.extend(generated);
        fns.push(ebind_fn());
        fns.push(qapply_fn());

        // Boundary rail over the full-style region (functions, drivers, ebind).
        // The fused rest is a different convention and excluded. A failure here
        // means the split was not as clean as the static checks judged, so fall
        // back to whole-program monadification rather than miscompiling.
        let refs: Vec<&CoreFn> = fns.iter().collect();
        if check_convention_boundaries(&fns, &refs, &full_style, true, &entries).is_err() {
            restore(self, saved_eff, saved_full);
            return Ok(None);
        }

        warn_free_monad(core, &region, &self.latent);

        let mut ctors = base_ctors.clone();
        ctors.insert(EPURE.into(), synth_ctor(EFF, PURE_TAG, 1));
        ctors.insert(EOP.into(), synth_ctor(EFF, OP_TAG, 4));
        ctors.insert(TQNIL.into(), synth_ctor(TQ, TQNIL_TAG, 0));
        ctors.insert(TQCONS.into(), synth_ctor(TQ, TQCONS_TAG, 2));
        if early {
            ctors.insert(SMORE.into(), synth_ctor(STEP, MORE_TAG, 1));
            ctors.insert(SDONE.into(), synth_ctor(STEP, DONE_TAG, 1));
        }
        Ok(Some((Core { fns }, ctors)))
    }

    // Emit an op outward: `EOp(id, skip, arg, taq_snoc(Unit, resume))` -- a fresh
    // singleton queue holding `resume`, the continuation that re-enters the
    // forwarding driver. The empty queue is `Unit`.
    fn forward_eop(&mut self, id: Value, skip: Value, arg: Value, resume: Value) -> Comp {
        let q = self.fresh("q");
        Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::TaqSnoc,
                vec![Value::Unit, resume],
            )),
            q,
            Box::new(Comp::Return(Value::Ctor(
                EOP.into(),
                OP_TAG,
                vec![id, skip, arg, Value::Var(q)],
            ))),
        )
    }

    fn lower_handle(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = c
        else {
            return Ok(c.clone());
        };

        // Free variables of the handler arms become extra parameters threaded
        // through the driver and every resumption.
        let mut fvs = BTreeSet::new();
        if let Some(rb) = return_body {
            fvs.extend(fv::comp_without(rb, return_var.iter()));
        }
        for op in ops {
            let mut s = fv::comp_without(&op.body, &op.params);
            s.remove(&op.resume);
            fvs.extend(s);
        }
        // `Sym` orders by intern id. Sort the captured free vars by name so the
        // driver's parameter and resumption-argument order stays byte-stable.
        let mut fvs: Vec<Sym> = fvs.into_iter().collect();
        fvs.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        let open = self.is_open(body, ops);

        let driver = self.fresh("handle");
        let res = self.fresh("res");

        // EPure(x) => run return clause. Open drivers return Eff, so the return
        // body is monadified and a bare result is lifted with EPure.
        let x = self.fresh("x");
        let pure_body = match (return_var, return_body) {
            (Some(rv), Some(rb)) => {
                let rbody = if open {
                    self.mon(rb)?
                } else {
                    self.lower_comp(rb)?
                };
                Comp::Bind(Box::new(Comp::Return(Value::Var(x))), *rv, Box::new(rbody))
            }
            _ if open => epure(Value::Var(x)),
            _ => Comp::Return(Value::Var(x)),
        };
        let pure_arm = (ctor_pat(EPURE, &[x]), pure_body);

        // EOp(id, skip, arg, k) => dispatch on id
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");

        let mut resume_args = vec![Value::Var(names::RESUME_KONT.into())];
        resume_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        // resume = \v -> drive(qApply(Q, v), fvs): run the op's continuation queue
        // `k` on `v`, then re-drive the result through this handler.
        let resume_thunk = Value::Thunk(Box::new(Comp::Lam(
            vec![names::RESUME_VAL.into()],
            Box::new(Comp::Bind(
                Box::new(Comp::Call(
                    QAPPLY.into(),
                    vec![Value::Var(k), Value::Var(names::RESUME_VAL.into())],
                )),
                names::RESUME_KONT.into(),
                Box::new(Comp::Call(driver, resume_args)),
            )),
        )));

        // Unhandled op (id not ours): closed handlers cannot reach here, open
        // handlers forward by re-emitting the EOp with a singleton queue holding a
        // continuation that re-enters this driver, so an enclosing handler
        // discharges it.
        let mut dispatch = if open {
            self.forward_eop(
                Value::Var(id),
                Value::Var(skip),
                Value::Var(arg),
                resume_thunk.clone(),
            )
        } else {
            Comp::Error(Value::Str(
                "ICE: unhandled effect op in closed handler dispatch".into(),
            ))
        };
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let rt = &resume_thunk;
        dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let op = &ops[i];
                let mut handler = if open {
                    let saved = std::mem::take(&mut me.resume_aliases);
                    me.resume_aliases.insert(op.resume);
                    let h = me.mon(&op.body);
                    me.resume_aliases = saved;
                    h?
                } else {
                    me.lower_comp(&op.body)?
                };
                // bind operation parameters from arg (tuple-unpacked when n-ary)
                handler = bind_params(&op.params, arg, handler);
                // bind resume
                let handle = Comp::Bind(
                    Box::new(Comp::Return(rt.clone())),
                    op.resume,
                    Box::new(handler),
                );
                // A closed handler's own ops always arrive at skip 0 (a masked
                // op of its effect keeps the handler open, by `is_open`), so it
                // handles directly. An open handler may receive one masked past
                // it (skip > 0): forward with one fewer level and re-enter this
                // driver on resume, mirroring the interpreter decrementing `skip`
                // on a matching handler crossing.
                if !open {
                    return Ok(handle);
                }
                let sk1 = me.fresh("sk");
                let reemit =
                    me.forward_eop(Value::Var(id), Value::Var(sk1), Value::Var(arg), rt.clone());
                let forward = Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Sub, Value::Var(skip), Value::Int(1))),
                    sk1,
                    Box::new(reemit),
                );
                let z = me.fresh("z");
                Ok(Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Eq, Value::Var(skip), Value::Int(0))),
                    z,
                    Box::new(Comp::If(Value::Var(z), Box::new(handle), Box::new(forward))),
                ))
            },
            dispatch,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let body_case = Comp::Case(Value::Var(res), vec![pure_arm, op_arm]);

        // Closed by construction: the params are `res` (the driven result) plus
        // exactly `fvs`, the `fv::comp_without` of every clause body computed
        // above. Every other name in `body_case` is a `{n}@hint` fresh binder or
        // a top-level callee, so no free occurrence can escape (no hygiene check
        // needed; see the note at the driver-append site in `lower`).
        let mut params = vec![res];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: driver,
            params,
            body: body_case,
        });

        // call site: run the monadified body, then drive it
        let r0 = self.fresh("r0");
        let mut call_args = vec![Value::Var(r0)];
        call_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        Ok(Comp::Bind(
            Box::new(self.mon(body)?),
            r0,
            Box::new(Comp::Call(driver, call_args)),
        ))
    }

    // A closed handle is driven natively when opted in and every clause resumes
    // only in tail position: its continuation never needs a mutually-recursive
    // driver, so a single self-recursive loop drives it in constant stack.
    fn native_eligible(&self, c: &Comp) -> bool {
        if !self.native {
            return false;
        }
        let Comp::Handle { body, ops, .. } = c else {
            return false;
        };
        !self.is_open(body, ops) && resume_tail_only(ops)
    }

    fn handle_closed(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        if self.native_eligible(c) {
            self.lower_handle_native(c)
        } else {
            self.lower_handle(c)
        }
    }

    // The self-recursive driver for an eligible closed handle. Mirrors
    // `lower_handle`, but the per-op continuation is the `EOp` queue itself: a
    // tail resume becomes `EResume(queue, value)`, and the loop drives the resumed
    // continuation by tail-calling itself on `qApply(queue, value)`. Because the
    // re-entry is a self-call at fixed arity it compiles to a `musttail`, so a
    // resuming loop runs in constant stack. The clauses are separate top-level
    // functions (direct calls, no per-dispatch closure), and the loop returns the
    // bare handler answer, the same call-site contract as `lower_handle` closed.
    fn lower_handle_native(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = c
        else {
            return Ok(c.clone());
        };

        let mut fvs = BTreeSet::new();
        if let Some(rb) = return_body {
            fvs.extend(fv::comp_without(rb, return_var.iter()));
        }
        for op in ops {
            let mut s = fv::comp_without(&op.body, &op.params);
            s.remove(&op.resume);
            fvs.extend(s);
        }
        let mut fvs: Vec<Sym> = fvs.into_iter().collect();
        fvs.sort_by(|a, b| a.as_str().cmp(b.as_str()));

        self.used_resume = true;
        let loop_name = self.fresh("region");

        // One top-level function per op: clause(arg, resume, fvs...). `resume` is
        // the op's continuation queue, so a tail resume monadifies to
        // `EResume(resume, value)`.
        let mut clause_names = Vec::new();
        for op in ops {
            let cname = self.fresh("clause");
            let arg_p = self.fresh("arg");
            let resume_p = self.fresh("res");
            let saved = std::mem::take(&mut self.resume_aliases);
            self.resume_aliases.insert(op.resume);
            let saved_native = self.native_resume;
            self.native_resume = true;
            let mbody = self.mon(&op.body);
            self.native_resume = saved_native;
            self.resume_aliases = saved;
            let with_resume = Comp::Bind(
                Box::new(Comp::Return(Value::Var(resume_p))),
                op.resume,
                Box::new(mbody?),
            );
            let cbody = bind_params(&op.params, arg_p, with_resume);
            let mut params = vec![arg_p, resume_p];
            params.extend(fvs.iter().copied());
            self.generated.push(CoreFn {
                name: cname,
                params,
                body: cbody,
            });
            clause_names.push(cname);
        }

        // EPure(x) => the body finished: run the return clause for the answer.
        let x = self.fresh("x");
        let pure_body = match (return_var, return_body) {
            (Some(rv), Some(rb)) => Comp::Bind(
                Box::new(Comp::Return(Value::Var(x))),
                *rv,
                Box::new(self.lower_comp(rb)?),
            ),
            _ => Comp::Return(Value::Var(x)),
        };
        let pure_arm = (ctor_pat(EPURE, &[x]), pure_body);

        // EOp(id, skip, arg, k) => dispatch on id. A closed handler's ops always
        // arrive at skip 0 (a masked op keeps the handler open), so `skip` is
        // unused, matching the closed `lower_handle` dispatch.
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let fail = Comp::Error(Value::Str(
            "ICE: unhandled effect op in closed native handler".into(),
        ));
        let lname = loop_name;
        let fvs_ref = &fvs;
        let dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let cname = clause_names[i];
                let mut call_args = vec![Value::Var(arg), Value::Var(k)];
                call_args.extend(fvs_ref.iter().map(|v| Value::Var(*v)));
                let cr = me.fresh("cr");
                // case cr of
                //   EResume(q, v) => region(qApply(q, v), fvs)   -- drive the resume
                //   EOp(..)       => region(cr, fvs)             -- a re-performed op
                //   EPure(ans)    => ans                         -- finished, bare answer
                let q = me.fresh("q");
                let v = me.fresh("v");
                let qa = me.fresh("qa");
                let mut resume_args = vec![Value::Var(qa)];
                resume_args.extend(fvs_ref.iter().map(|w| Value::Var(*w)));
                let resume_arm = (
                    ctor_pat(ERESUME, &[q, v]),
                    Comp::Bind(
                        Box::new(Comp::Call(
                            QAPPLY.into(),
                            vec![Value::Var(q), Value::Var(v)],
                        )),
                        qa,
                        Box::new(Comp::Call(lname, resume_args)),
                    ),
                );
                let oi = me.fresh("id");
                let os = me.fresh("sk");
                let oa = me.fresh("arg");
                let ok = me.fresh("k");
                let mut redrive_args = vec![Value::Var(cr)];
                redrive_args.extend(fvs_ref.iter().map(|w| Value::Var(*w)));
                let op_redrive = (
                    ctor_pat(EOP, &[oi, os, oa, ok]),
                    Comp::Call(lname, redrive_args),
                );
                let ans = me.fresh("ans");
                let final_arm = (ctor_pat(EPURE, &[ans]), Comp::Return(Value::Var(ans)));
                let cased = Comp::Case(Value::Var(cr), vec![resume_arm, op_redrive, final_arm]);
                Ok(Comp::Bind(
                    Box::new(Comp::Call(cname, call_args)),
                    cr,
                    Box::new(cased),
                ))
            },
            fail,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let cur = self.fresh("cur");
        let loop_body = Comp::Case(Value::Var(cur), vec![pure_arm, op_arm]);
        let mut params = vec![cur];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: loop_name,
            params,
            body: loop_body,
        });

        // Call site: reify the body to an Eff value, then drive it; the loop
        // returns the bare answer (closed).
        let r0 = self.fresh("r0");
        let mut call_args = vec![Value::Var(r0)];
        call_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        Ok(Comp::Bind(
            Box::new(self.mon(body)?),
            r0,
            Box::new(Comp::Call(loop_name, call_args)),
        ))
    }

    // `let f = <closed function-answer handle> in f(arg)`: the handler's answer
    // type is a function `S -> A` threaded as a state accumulator (a
    // parameter-passing handler, e.g. `rd(u, r) => \s -> r(s)(s)`). Each clause
    // resumes once and applies the result to a new state, so the driver becomes a
    // single self-tail-recursive loop `region(cur, acc, fvs)` that threads the
    // state in `acc` and `musttail`s on the resumed continuation: a
    // parameter-passing loop then runs in constant stack with no per-operation
    // frame. The boundary application `f(arg)` is folded into the initial call, so
    // the loop returns the bare answer. Returns None unless the handle is closed,
    // every clause and the return clause have the state shape, and `f` is applied
    // exactly once in tail position, so any other program falls back to the proven
    // free monad. Gated: only when natively driving effects.
    fn try_lower_fn_answer(
        &mut self,
        m: &Comp,
        f: Sym,
        n: &Comp,
    ) -> Result<Option<Comp>, TypeError> {
        if !self.native {
            return Ok(None);
        }
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = m
        else {
            return Ok(None);
        };
        if ops.is_empty() || self.is_open(body, ops) || return_var.is_none() {
            return Ok(None);
        }
        // Pure shape check first, before any fresh-name or generated-function
        // mutation, so a non-match leaves the lowerer untouched for the fallback.
        let Some((ret_s, ret_body)) = state_return(return_body.as_deref()) else {
            return Ok(None);
        };
        let mut clauses = Vec::new();
        for op in ops {
            let Some(sc) = state_clause(op) else {
                return Ok(None);
            };
            clauses.push(sc);
        }
        if !fn_applied_once_tail(n, f) {
            return Ok(None);
        }

        // Captured free vars threaded through the loop and resumptions. The clause
        // and return lambda params, the op params and the resume are all bound
        // within their bodies, so they fall out of `comp_without` already.
        let mut fvs = BTreeSet::new();
        if let Some(rb) = return_body {
            fvs.extend(fv::comp_without(rb, return_var.iter()));
        }
        for op in ops {
            let mut s = fv::comp_without(&op.body, &op.params);
            s.remove(&op.resume);
            fvs.extend(s);
        }
        let mut fvs: Vec<Sym> = fvs.into_iter().collect();
        fvs.sort_by(|a, b| a.as_str().cmp(b.as_str()));

        let region = self.fresh("region");
        let acc = self.fresh("acc");

        // EPure(x) => run the return clause with the accumulator as its state, a
        // bare answer out.
        let x = self.fresh("x");
        let mut pbody = self.lower_comp(&ret_body)?;
        pbody = Comp::Bind(
            Box::new(Comp::Return(Value::Var(acc))),
            ret_s,
            Box::new(pbody),
        );
        let rv = return_var.expect("return_var checked present above");
        pbody = Comp::Bind(Box::new(Comp::Return(Value::Var(x))), rv, Box::new(pbody));
        let pure_arm = (ctor_pat(EPURE, &[x]), pbody);

        // EOp(id, skip, arg, k) => dispatch on id; skip is 0 for a closed
        // handler's own ops, as in the other closed dispatches.
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let fail = Comp::Error(Value::Str(
            "ICE: unhandled effect op in closed native handler".into(),
        ));
        let fvs_ref = &fvs;
        let clauses_ref = &clauses;
        let dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let sc = &clauses_ref[i];
                let op = &ops[i];
                // region(qApply(k, A), B, fvs): resume the continuation on `A`,
                // then thread `B` as the new accumulator.
                let qa = me.fresh("qa");
                let mut region_args = vec![Value::Var(qa), sc.b.clone()];
                region_args.extend(fvs_ref.iter().map(|w| Value::Var(*w)));
                let mut tail = Comp::Bind(
                    Box::new(Comp::Call(QAPPLY.into(), vec![Value::Var(k), sc.a.clone()])),
                    qa,
                    Box::new(Comp::Call(region, region_args)),
                );
                for (pm, px) in sc.prefix.iter().rev() {
                    let lm = me.lower_comp(pm)?;
                    tail = Comp::Bind(Box::new(lm), *px, Box::new(tail));
                }
                tail = Comp::Bind(
                    Box::new(Comp::Return(Value::Var(acc))),
                    sc.s,
                    Box::new(tail),
                );
                Ok(bind_params(&op.params, arg, tail))
            },
            fail,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let cur = self.fresh("cur");
        let loop_body = Comp::Case(Value::Var(cur), vec![pure_arm, op_arm]);
        let mut params = vec![cur, acc];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: region,
            params,
            body: loop_body,
        });

        // Call site: reify the handled computation, then drive it from `arg`. The
        // continuation `n` has its single `f(arg)` rewritten to the region call.
        let r0 = self.fresh("r0");
        let mut aliases = BTreeSet::new();
        aliases.insert(f);
        let driven = self
            .rewrite_fn_use(n, &aliases, region, r0, &fvs)?
            .ok_or_else(|| TypeError::Ice {
                msg: "function-answer use-site rewrite failed after shape check".into(),
            })?;
        Ok(Some(Comp::Bind(
            Box::new(self.mon(body)?),
            r0,
            Box::new(driven),
        )))
    }

    // Rewrite the continuation after `let f = <handle> in n` so the single tail
    // application `f(arg)` becomes `region(r0, arg, fvs)`, dropping the now-dead
    // `f` routing. Mirrors `fn_applied_once_tail`, which already verified the
    // shape, so the `None` arms are unreachable in practice.
    fn rewrite_fn_use(
        &mut self,
        n: &Comp,
        aliases: &BTreeSet<Sym>,
        region: Sym,
        r0: Sym,
        fvs: &[Sym],
    ) -> Result<Option<Comp>, TypeError> {
        match n {
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(v)) = f.as_ref() else {
                    return Ok(None);
                };
                if !aliases.contains(v) || args.len() != 1 {
                    return Ok(None);
                }
                let mut call_args = vec![Value::Var(r0), args[0].clone()];
                call_args.extend(fvs.iter().map(|w| Value::Var(*w)));
                Ok(Some(Comp::Call(region, call_args)))
            }
            Comp::Bind(m, x, rest) => {
                if let Comp::Return(Value::Var(v)) = m.as_ref() {
                    if aliases.contains(v) {
                        let mut a2 = aliases.clone();
                        a2.insert(*x);
                        return self.rewrite_fn_use(rest, &a2, region, r0, fvs);
                    }
                }
                if mentions(&fv::comp(m), aliases) {
                    return Ok(None);
                }
                let lm = self.lower_comp(m)?;
                Ok(self
                    .rewrite_fn_use(rest, aliases, region, r0, fvs)?
                    .map(|r| Comp::Bind(Box::new(lm), *x, Box::new(r))))
            }
            _ => Ok(None),
        }
    }

    // mask<Eff> becomes a driver that handles nothing: it adds N to the id of
    // every Eff op flowing through it, so the next driver of that effect
    // misses its equality match once and forwards with id - N.
    //
    // Closed top-level template: its binders are the fixed `names::*` @-set,
    // disjoint from program names, and it never nests another template's body, so
    // the fixed binders cannot capture. Closedness is structural, not checked.
    fn mask_driver(&mut self, ops: &[Sym]) -> Result<Sym, TypeError> {
        let driver = self.fresh("mask");
        // Queue binder for the re-emitted op (a `{n}@q` fresh name: unforgeable and
        // unique, so the template stays closed). The bump and forward arms are
        // mutually exclusive, so reusing one binder across both is sound.
        let qb = self.fresh("q");
        let resume = Value::Thunk(Box::new(Comp::Lam(
            vec![names::RESUME_VAL.into()],
            Box::new(Comp::Bind(
                Box::new(Comp::Call(
                    QAPPLY.into(),
                    vec![
                        Value::Var(names::CONT.into()),
                        Value::Var(names::RESUME_VAL.into()),
                    ],
                )),
                names::RESUME_KONT.into(),
                Box::new(Comp::Call(
                    driver,
                    vec![Value::Var(names::RESUME_KONT.into())],
                )),
            )),
        )));
        let reemit = |skipv: Value| {
            Comp::Bind(
                Box::new(Comp::StrBuiltin(
                    Builtin::TaqSnoc,
                    vec![Value::Unit, resume.clone()],
                )),
                qb,
                Box::new(Comp::Return(Value::Ctor(
                    EOP.into(),
                    OP_TAG,
                    vec![
                        Value::Var(names::OP_ID.into()),
                        skipv,
                        Value::Var(names::OP_ARG.into()),
                        Value::Var(qb),
                    ],
                ))),
            )
        };
        // An op of the masked effect gains one skip level, so the next matching
        // handler bypasses it once. Any other op passes through unchanged.
        let bump = Comp::Bind(
            Box::new(Comp::Prim(
                CoreOp::Add,
                Value::Var(names::OP_SKIP.into()),
                Value::Int(1),
            )),
            names::FWD_SKIP.into(),
            Box::new(reemit(Value::Var(names::FWD_SKIP.into()))),
        );
        let fwd = reemit(Value::Var(names::OP_SKIP.into()));
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(*op))
            .collect::<Result<_, _>>()?;
        let dispatch = self.build_op_chain(
            &Value::Var(names::OP_ID.into()),
            &ids,
            |_, _| Ok(bump.clone()),
            fwd,
        )?;
        let pure_arm = (
            ctor_pat(EPURE, &[names::COMPOSE.into()]),
            epure(Value::Var(names::COMPOSE.into())),
        );
        let op_arm = (
            ctor_pat(
                EOP,
                &[
                    names::OP_ID.into(),
                    names::OP_SKIP.into(),
                    names::OP_ARG.into(),
                    names::CONT.into(),
                ],
            ),
            dispatch,
        );
        self.generated.push(CoreFn {
            name: driver,
            params: vec![names::RET.into()],
            body: Comp::Case(Value::Var(names::RET.into()), vec![pure_arm, op_arm]),
        });
        Ok(driver)
    }
}

fn bind_params(params: &[Sym], arg: Sym, body: Comp) -> Comp {
    match params.len() {
        0 => body,
        1 => Comp::Bind(
            Box::new(Comp::Return(Value::Var(arg))),
            params[0],
            Box::new(body),
        ),
        _ => {
            let binders = params.iter().map(|p| Some(*p)).collect();
            Comp::Case(Value::Var(arg), vec![(CorePat::Tuple(binders), body)])
        }
    }
}

// Whether every clause of a handler uses `resume` only as the head of a
// tail-position application. Such a resume can be driven by the self-recursive
// `{n}@region` loop (a tail resume is the clause's result, so it becomes
// `EResume(queue, value)`); any other occurrence (captured by a lambda, passed as
// an argument, bound and reused, returned as a value) would leave the queue where
// the loop cannot drive it, so the handler stays on the free monad.
fn resume_tail_only(ops: &[HandleOp]) -> bool {
    ops.iter().all(|op| {
        let mut aliases = BTreeSet::new();
        aliases.insert(op.resume);
        clause_resume_tail(&op.body, &aliases, true)
    })
}

fn mentions(set: &fv::Set, aliases: &BTreeSet<Sym>) -> bool {
    aliases.iter().any(|a| set.contains(a))
}

// `tail` tracks whether `c`'s value is the clause result. A resume application is
// allowed only in tail position with arguments that do not themselves mention a
// resume alias. The elaborator routes resume through `return k to x`, so a bind of
// that shape grows the alias set (and is not itself a use). Any other occurrence
// of an alias disqualifies the clause.
fn clause_resume_tail(c: &Comp, aliases: &BTreeSet<Sym>, tail: bool) -> bool {
    match c {
        Comp::App(f, args) if matches!(f.as_ref(), Comp::Force(Value::Var(v)) if aliases.contains(v)) => {
            tail && args.iter().all(|a| !mentions(&fv::value(a), aliases))
        }
        Comp::Bind(m, x, n) => {
            let routing = matches!(m.as_ref(), Comp::Return(Value::Var(v)) if aliases.contains(v));
            let mut a2 = aliases.clone();
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    a2.insert(*x);
                }
            }
            (routing || clause_resume_tail(m, aliases, false)) && clause_resume_tail(n, &a2, tail)
        }
        Comp::If(v, t, e) => {
            !mentions(&fv::value(v), aliases)
                && clause_resume_tail(t, aliases, tail)
                && clause_resume_tail(e, aliases, tail)
        }
        Comp::Case(v, arms) => {
            !mentions(&fv::value(v), aliases)
                && arms
                    .iter()
                    .all(|(_, b)| clause_resume_tail(b, aliases, tail))
        }
        other => !mentions(&fv::comp(other), aliases),
    }
}

// A function-answer state clause `\s -> let t = resume(A) in t(B)`: the handler's
// answer type is a function `S -> A` threaded as a state accumulator. `A` is the
// value the continuation resumes with, `B` the value its result (the next answer
// function) is applied to, so the loop becomes `region(qApply(k, A), B, fvs)`: a
// self-tail-call that threads `B` as the new accumulator. `prefix` is the pure
// routing binds that define `A`/`B` from the lambda param, op params and free
// vars; they are re-emitted verbatim. None when the clause is not of that shape.
struct StateClause {
    s: Sym,
    prefix: Vec<(Comp, Sym)>,
    a: Value,
    b: Value,
}

fn state_clause(op: &HandleOp) -> Option<StateClause> {
    let Comp::Return(Value::Thunk(t)) = &op.body else {
        return None;
    };
    let Comp::Lam(ps, inner) = t.as_ref() else {
        return None;
    };
    let [s] = ps.as_slice() else {
        return None;
    };
    let mut aliases = BTreeSet::new();
    aliases.insert(op.resume);
    let mut prefix: Vec<(Comp, Sym)> = Vec::new();
    let mut cur: &Comp = inner;
    loop {
        let Comp::Bind(m, x, n) = cur else {
            return None;
        };
        // The resume application `resume(A)` (possibly wrapped in its own pure
        // routing let-chain) bound to `x`, whose continuation applies `x` to `B`.
        if let Some((mprefix, a)) = resume_app(m, &aliases) {
            let b = state_apply_tail(n, *x)?;
            if mentions(&fv::value(&b), &aliases) {
                return None;
            }
            prefix.extend(mprefix);
            return Some(StateClause {
                s: *s,
                prefix,
                a,
                b,
            });
        }
        // `return r to x`: routes the resume through an ANF binder; drop the bind
        // (the resume is the queue `k`, not a value in scope) and track the alias.
        if let Comp::Return(Value::Var(v)) = m.as_ref() {
            if aliases.contains(v) {
                aliases.insert(*x);
                cur = n;
                continue;
            }
        }
        // A pure routing bind that defines part of `A`/`B`: re-emitted as-is.
        // Anything effectful or that mentions the resume is rejected.
        if !matches!(m.as_ref(), Comp::Return(_) | Comp::Prim(..))
            || mentions(&fv::comp(m), &aliases)
        {
            return None;
        }
        prefix.push(((**m).clone(), *x));
        cur = n;
    }
}

// A resume application `resume(A)`, possibly preceded by its own pure routing
// let-chain (the ANF binds the elaborator threads `s`/params and the resume
// through). Returns the pure prefix binds to preserve (resume routing dropped)
// and the value `A` the continuation resumes with. None when `m` is not a resume
// application.
fn resume_app(m: &Comp, aliases: &BTreeSet<Sym>) -> Option<(Vec<(Comp, Sym)>, Value)> {
    let mut local = aliases.clone();
    let mut prefix: Vec<(Comp, Sym)> = Vec::new();
    let mut cur = m;
    loop {
        match cur {
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(r)) = f.as_ref() else {
                    return None;
                };
                if !local.contains(r) {
                    return None;
                }
                let [a] = args.as_slice() else {
                    return None;
                };
                if mentions(&fv::value(a), &local) {
                    return None;
                }
                return Some((prefix, a.clone()));
            }
            Comp::Bind(mm, y, nn) => {
                if let Comp::Return(Value::Var(v)) = mm.as_ref() {
                    if local.contains(v) {
                        local.insert(*y);
                        cur = nn;
                        continue;
                    }
                }
                if !matches!(mm.as_ref(), Comp::Return(_) | Comp::Prim(..))
                    || mentions(&fv::comp(mm), &local)
                {
                    return None;
                }
                prefix.push(((**mm).clone(), *y));
                cur = nn;
            }
            _ => return None,
        }
    }
}

// The tail of a state clause: the resume result `t` applied once to `B`, modulo
// `return t to x` routing. Returns `B`.
fn state_apply_tail(n: &Comp, t: Sym) -> Option<Value> {
    let mut aliases = BTreeSet::new();
    aliases.insert(t);
    let mut cur = n;
    loop {
        match cur {
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(v)) = f.as_ref() else {
                    return None;
                };
                if !aliases.contains(v) {
                    return None;
                }
                let [b] = args.as_slice() else {
                    return None;
                };
                if mentions(&fv::value(b), &aliases) {
                    return None;
                }
                return Some(b.clone());
            }
            Comp::Bind(m, x, rest) => {
                let Comp::Return(Value::Var(v)) = m.as_ref() else {
                    return None;
                };
                if !aliases.contains(v) {
                    return None;
                }
                aliases.insert(*x);
                cur = rest;
            }
            _ => return None,
        }
    }
}

// The return clause of a function-answer handler: `\s -> R`. Returns the lambda
// param and body, threaded with the accumulator at the loop's `EPure` arm.
fn state_return(return_body: Option<&Comp>) -> Option<(Sym, Comp)> {
    let Comp::Return(Value::Thunk(t)) = return_body? else {
        return None;
    };
    let Comp::Lam(ps, body) = t.as_ref() else {
        return None;
    };
    let [s] = ps.as_slice() else {
        return None;
    };
    Some((*s, (**body).clone()))
}

// Whether the continuation `n` after `let f = <handle> in n` applies `f` exactly
// once, as the head of a tail application with a single argument, modulo `return f
// to x` routing. A `f` used anywhere else (escaping as a value, applied twice)
// means the answer function cannot be folded into the region loop.
fn fn_applied_once_tail(n: &Comp, f: Sym) -> bool {
    let mut aliases = BTreeSet::new();
    aliases.insert(f);
    let mut cur = n;
    loop {
        match cur {
            Comp::App(fc, args) => {
                let Comp::Force(Value::Var(v)) = fc.as_ref() else {
                    return false;
                };
                return aliases.contains(v)
                    && args.len() == 1
                    && !mentions(&fv::value(&args[0]), &aliases);
            }
            Comp::Bind(m, x, rest) => {
                if let Comp::Return(Value::Var(v)) = m.as_ref() {
                    if aliases.contains(v) {
                        aliases.insert(*x);
                        cur = rest;
                        continue;
                    }
                }
                if mentions(&fv::comp(m), &aliases) {
                    return false;
                }
                cur = rest;
            }
            _ => return false,
        }
    }
}

fn epure(v: Value) -> Comp {
    Comp::Return(Value::Ctor(EPURE.into(), PURE_TAG, vec![v]))
}

// fn ebind(r, f) =
//   case r {
//     EPure(x)        => force(f)(x),
//     EOp(id,sk,a,q)  => EOp(id, sk, a, taq_snoc(q, f)),
//   }
//
// The Freer monad: binding a continuation onto a suspended op is one O(1) queue
// snoc -- no spine re-walk, no nested closure tree. `CONT` binds the op's queue
// (its 4th field); `f` (`EBIND_FN`) is the new Kleisli arrow.
//
// Closed top-level template: its binders (`names::OP_ID`/`OP_SKIP`/`OP_ARG`/
// `CONT`/`EBIND_FN`/`RESUME_KONT`) are fixed `@`-names, disjoint from program
// names. Templates refer to one another by `Call`, never by lexical nesting, so the
// fixed binders cannot capture across templates; do not emit one template's body
// inside another. Closedness is thus structural, not checked.
fn ebind_fn() -> CoreFn {
    let pure_arm = (
        ctor_pat(EPURE, &[names::COMPOSE.into()]),
        Comp::App(
            Box::new(Comp::Force(Value::Var(names::EBIND_FN.into()))),
            vec![Value::Var(names::COMPOSE.into())],
        ),
    );
    let q = Sym::from(names::RESUME_KONT);
    let op_arm = (
        ctor_pat(
            EOP,
            &[
                names::OP_ID.into(),
                names::OP_SKIP.into(),
                names::OP_ARG.into(),
                names::CONT.into(),
            ],
        ),
        Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::TaqSnoc,
                vec![
                    Value::Var(names::CONT.into()),
                    Value::Var(names::EBIND_FN.into()),
                ],
            )),
            q,
            Box::new(Comp::Return(Value::Ctor(
                EOP.into(),
                OP_TAG,
                vec![
                    Value::Var(names::OP_ID.into()),
                    Value::Var(names::OP_SKIP.into()),
                    Value::Var(names::OP_ARG.into()),
                    Value::Var(q),
                ],
            ))),
        ),
    );
    CoreFn {
        name: EBIND.into(),
        params: vec![names::RET.into(), names::EBIND_FN.into()],
        body: Comp::Case(Value::Var(names::RET.into()), vec![pure_arm, op_arm]),
    }
}

// fn qApply(q, v) =
//   case taq_uncons(q) {
//     TQNil          => EPure(v),
//     TQCons(g, qr)  => case force(g)(v) {
//       EPure(w)         => qApply(qr, w),                       -- musttail
//       EOp(id,sk,a,q2)  => EOp(id, sk, a, taq_concat(q2, qr)),  -- splice, O(1)
//     }
//   }
//
// Runs an op's continuation queue on a resumption value. Every arrow is dequeued
// once and concat never re-walks a passed prefix, so driving an n-snoc queue is
// O(n). The `EPure` self-call is in tail position (codegen `musttail` => O(1)
// native stack). Closed template (fixed `@`-binders), like `ebind`.
fn qapply_fn() -> CoreFn {
    let g = Sym::from(names::CONT); // head arrow
    let qr = Sym::from(names::RESUME_KONT); // tail queue
    let w = Sym::from(names::COMPOSE);
    let id = Sym::from(names::OP_ID);
    let sk = Sym::from(names::OP_SKIP);
    let a = Sym::from(names::OP_ARG);
    let q2 = Sym::from(names::FWD_SKIP);
    let spliced = Sym::from(names::RESUME_VAL);
    let v = Sym::from(names::RET);
    let qparam = Sym::from(names::EBIND_FN);
    let u = Sym::from(names::ERR);

    // case applied { EPure(w) => qApply(qr, w), EOp(..) => EOp(.., concat(q2, qr)) }
    let applied = Comp::App(Box::new(Comp::Force(Value::Var(g))), vec![Value::Var(v)]);
    let on_op = Comp::Bind(
        Box::new(Comp::StrBuiltin(
            Builtin::TaqConcat,
            vec![Value::Var(q2), Value::Var(qr)],
        )),
        spliced,
        Box::new(Comp::Return(Value::Ctor(
            EOP.into(),
            OP_TAG,
            vec![
                Value::Var(id),
                Value::Var(sk),
                Value::Var(a),
                Value::Var(spliced),
            ],
        ))),
    );
    let inner = Comp::Bind(
        Box::new(applied),
        Sym::from(names::STATE),
        Box::new(Comp::Case(
            Value::Var(Sym::from(names::STATE)),
            vec![
                (
                    ctor_pat(EPURE, &[w]),
                    Comp::Call(QAPPLY.into(), vec![Value::Var(qr), Value::Var(w)]),
                ),
                (ctor_pat(EOP, &[id, sk, a, q2]), on_op),
            ],
        )),
    );
    let cons_arm = (ctor_pat(TQCONS, &[g, qr]), inner);
    let nil_arm = (ctor_pat(TQNIL, &[]), epure(Value::Var(v)));
    CoreFn {
        name: QAPPLY.into(),
        params: vec![qparam, v],
        body: Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::TaqUncons,
                vec![Value::Var(qparam)],
            )),
            u,
            Box::new(Comp::Case(Value::Var(u), vec![nil_arm, cons_arm])),
        ),
    }
}

fn ctor_pat(name: &str, vars: &[Sym]) -> CorePat {
    CorePat::Ctor(Sym::from(name), vars.iter().map(|v| Some(*v)).collect())
}

fn synth_ctor(type_name: &str, tag: usize, n: usize) -> CtorInfo {
    CtorInfo {
        type_name: type_name.into(),
        params: vec![],
        args: vec![Type::Int; n],
        tag,
        fields: vec![],
    }
}

// Per-function set of effect ops still latent in its body, with the mask depth
// dropped: the op identities the call-graph fixpoint believes each function can
// still perform. Exposed for the driver's effect-engine reconciliation check.
#[must_use]
pub fn latent_ops(core: &Core) -> BTreeMap<Sym, BTreeSet<Sym>> {
    latent_map(core)
        .into_iter()
        .map(|(f, ops)| (f, ops.into_iter().map(|o| o.id).collect()))
        .collect()
}

fn latent_map(core: &Core) -> Latent {
    // The latent ops of each function are a least fixpoint over the call graph:
    // a function's set is the ops it performs directly plus those latent in its
    // callees. `least_fixpoint` grows each set monotonically to convergence, so
    // termination is structural (no iteration ceiling needed).
    let seed: Latent = core.fns.iter().map(|f| (f.name, BTreeSet::new())).collect();
    let bodies: BTreeMap<Sym, &Comp> = core.fns.iter().map(|f| (f.name, &f.body)).collect();
    crate::fixpoint::least_fixpoint(seed, |name, cur| {
        let mut s = BTreeSet::new();
        latent(bodies[name], cur, &mut s);
        s
    })
}

// Selective mode monadifies only functions that perform or propagate an
// effect. When effectful code escapes first-class through a thunk (a call to
// an effectful function, or a raw do/handle inside a closure body), dynamic
// call sites cannot tell conventions apart, so switch to whole-program mode and
// monadify everything. `try_local` first tries to confine that whole-program
// answer to the escaping component; this is its fallback. check_convention_boundaries
// enforces the resulting invariant after the rewrite.
fn monadic_set(core: &Core, fl: &Latent) -> (BTreeSet<Sym>, bool) {
    let eff: BTreeSet<Sym> = fl
        .iter()
        .filter(|(_, s)| !s.is_empty())
        .map(|(n, _)| *n)
        .collect();
    let mut thunks = Vec::new();
    for f in &core.fns {
        thunks_in_comp(&f.body, &mut thunks);
    }
    let escapes = thunks.iter().any(|body| {
        let mut heads = BTreeSet::new();
        all_calls(body, &mut heads);
        !heads.is_disjoint(&eff) || raw_effects(body)
    }) || core.fns.iter().any(|f| open_resume_escapes(&f.body, fl));
    if escapes {
        (core.fns.iter().map(|f| f.name).collect(), true)
    } else {
        (eff, false)
    }
}

// The monadic region for local monadification: the component of functions that
// must be free-monad lowered because an effectful closure escapes inside it,
// together with its entry functions (the ones a fused caller invokes, which need
// a bare-returning, unwrapped convention). Returns None when the split is not
// clean enough to keep the rest fused, so the caller falls back to whole-program.
//
// Built as the connected component of the escaping functions under two closures:
// downward over the call graph (every function an escaping one calls, so the
// closure that is applied dynamically and the data path it flows through are all
// monadic together), and over a shared effect op (a function that performs or
// handles an op the region performs joins it, so the handler that drives the
// region's `EOp` cells is inside it). The region is therefore downward-closed:
// it calls no function outside itself, so the only boundary is the rest calling
// in at entries. With its effect ops disjoint from the rest (checked below) and
// no first-class closure crossing at an entry, the two calling conventions never
// meet on a value, so the rest stays fused.
fn monadic_region(
    core: &Core,
    fl: &Latent,
    escaping: &BTreeSet<Sym>,
) -> Option<(BTreeSet<Sym>, BTreeSet<Sym>)> {
    let by_name: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();
    let footprint: BTreeMap<Sym, BTreeSet<Sym>> = core
        .fns
        .iter()
        .map(|f| {
            let mut ops = BTreeSet::new();
            collect_ops(&f.body, &mut ops);
            if let Some(s) = fl.get(&f.name) {
                ops.extend(s.iter().map(|m| m.id));
            }
            (f.name, ops)
        })
        .collect();
    // Closure-inert functions: no effect and no dynamic application anywhere in
    // their downward call-graph. A monadified closure can flow through one as
    // opaque data (it is never forced) and the function returns a bare value, so
    // it is convention-agnostic and stays shared in the fused rest rather than
    // being pulled into the region (which would falsely conflict whenever the
    // rest also calls it, e.g. a prelude helper like `length`). Greatest fixpoint:
    // start all-inert, drop any that applies a value, performs/propagates an
    // effect, or calls a non-inert function.
    let mut inert: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    loop {
        let mut changed = false;
        for f in &core.fns {
            if !inert.contains(&f.name) {
                continue;
            }
            let mut callees = BTreeSet::new();
            all_calls(&f.body, &mut callees);
            let disqualified = has_app(&f.body)
                || !footprint[&f.name].is_empty()
                || callees
                    .iter()
                    .any(|g| by_name.contains_key(g) && !inert.contains(g));
            if disqualified {
                inert.remove(&f.name);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut region: BTreeSet<Sym> = escaping.clone();
    loop {
        let mut changed = false;
        // Downward: every named, non-inert callee of a region function (the
        // dynamic-apply and data-flow reach of the escaping closure). Inert
        // callees stay shared in the rest.
        for name in region.clone() {
            if let Some(f) = by_name.get(&name) {
                let mut heads = BTreeSet::new();
                all_calls(&f.body, &mut heads);
                for g in heads {
                    if by_name.contains_key(&g) && !inert.contains(&g) {
                        changed |= region.insert(g);
                    }
                }
            }
        }
        // Over a shared effect op: anything performing or handling an op the
        // region touches (the handler that drives its EOp cells, a co-performer).
        let tainted: BTreeSet<Sym> = region
            .iter()
            .flat_map(|f| footprint[f].iter().copied())
            .collect();
        for f in &core.fns {
            if !footprint[&f.name].is_disjoint(&tainted) {
                changed |= region.insert(f.name);
            }
        }
        if !changed {
            break;
        }
    }
    let entry_point = Sym::new(ENTRY_POINT);
    // Disjoint effects: no rest function may touch an op the region does, else a
    // boundary call would cross a live effect with mismatched conventions.
    let region_ops: BTreeSet<Sym> = region
        .iter()
        .flat_map(|f| footprint[f].iter().copied())
        .collect();
    for f in core.fns.iter().filter(|f| !region.contains(&f.name)) {
        if !footprint[&f.name].is_disjoint(&region_ops) {
            return None;
        }
    }

    // Entries: region functions a non-region (fused) function calls, plus `main`
    // when it is in the region (the runtime is its caller).
    let mut entries = BTreeSet::new();
    for f in &core.fns {
        if region.contains(&f.name) {
            continue;
        }
        let mut heads = BTreeSet::new();
        all_calls(&f.body, &mut heads);
        entries.extend(heads.into_iter().filter(|g| region.contains(g)));
    }
    if region.contains(&entry_point) {
        entries.insert(entry_point);
    }
    // An entry also called from within the region would need two conventions
    // (bare for the fused caller, Eff for the region caller). `main` is never
    // called by program code, so it is exempt.
    for f in core.fns.iter().filter(|f| region.contains(&f.name)) {
        let mut heads = BTreeSet::new();
        all_calls(&f.body, &mut heads);
        if heads
            .iter()
            .any(|g| *g != entry_point && entries.contains(g))
        {
            return None;
        }
    }
    // A closure crossing the boundary as a call argument, or returned from an
    // entry, would mix conventions: the rest threads bare-returning thunks while
    // the region monadifies thunk bodies into Eff. Reject either.
    for f in &core.fns {
        let in_region = region.contains(&f.name);
        let mut crosses_thunk = false;
        for_each_call(&f.body, &mut |g, args| {
            if in_region != region.contains(&g) && args.iter().any(carries_thunk) {
                crosses_thunk = true;
            }
        });
        if crosses_thunk {
            return None;
        }
    }
    for e in entries.iter().filter(|e| **e != entry_point) {
        if let Some(f) = core.fns.iter().find(|f| f.name == *e) {
            // A closure returned to, or dynamically applied from, a fused caller
            // mixes conventions on a value the syntactic argument check (which
            // only sees literal thunks, not ones bound to a variable) cannot rule
            // out, so reject a higher-order entry outright.
            let params: BTreeSet<Sym> = f.params.iter().copied().collect();
            if tail_returns_thunk(&f.body) || applies_param(&f.body, &params) {
                return None;
            }
        }
    }
    Some((region, entries))
}

// Whether a computation dynamically applies any value (an `App` node anywhere,
// including inside a thunk it builds). A function with no `App` in its whole
// body never forces a closure, so a monadified closure can pass through it as
// opaque data without a convention clash.
fn has_app(c: &Comp) -> bool {
    if matches!(c, Comp::App(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            found |= has_app(t);
        }
    });
    each_subcomp(c, &mut |sc| found |= has_app(sc));
    found
}

// A value that carries a first-class closure (directly or nested in a
// constructor or tuple): the convention-sensitive shape at a region boundary.
fn carries_thunk(v: &Value) -> bool {
    match v {
        Value::Thunk(_) => true,
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(carries_thunk),
        _ => false,
    }
}

// Visit every `Call` head and its arguments, descending into thunk bodies.
fn for_each_call<'a>(c: &'a Comp, f: &mut impl FnMut(Sym, &'a [Value])) {
    if let Comp::Call(g, args) = c {
        f(*g, args);
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            for_each_call(t, f);
        }
    });
    each_subcomp(c, &mut |sc| for_each_call(sc, f));
}

// Whether a computation dynamically applies one of `params` (forcing it as a
// call head), tracking `let`-aliases of a param. A region entry that does this is
// higher-order over a value its fused caller supplies, whose convention the
// region cannot assume, so such entries are rejected.
fn applies_param(c: &Comp, params: &BTreeSet<Sym>) -> bool {
    match c {
        Comp::App(f, _) => {
            matches!(f.as_ref(), Comp::Force(Value::Var(p)) if params.contains(p))
                || applies_param(f, params)
        }
        Comp::Bind(m, x, n) => {
            if applies_param(m, params) {
                return true;
            }
            // `let x = p` makes x an alias of the param p.
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if params.contains(v) {
                    let mut p2 = params.clone();
                    p2.insert(*x);
                    return applies_param(n, &p2);
                }
            }
            applies_param(n, params)
        }
        Comp::If(_, t, e) => applies_param(t, params) || applies_param(e, params),
        Comp::Case(_, arms) => arms.iter().any(|(_, b)| applies_param(b, params)),
        Comp::Lam(_, b) | Comp::Mask(_, b) => applies_param(b, params),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            applies_param(body, params)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| applies_param(rb, params))
                || ops.iter().any(|op| applies_param(&op.body, params))
        }
        _ => false,
    }
}

// Whether a computation can return a closure at a tail (result) position, the
// value an entry hands back to its fused caller.
fn tail_returns_thunk(c: &Comp) -> bool {
    match c {
        Comp::Return(v) => carries_thunk(v),
        Comp::Bind(_, _, n) => tail_returns_thunk(n),
        Comp::If(_, t, e) => tail_returns_thunk(t) || tail_returns_thunk(e),
        Comp::Case(_, arms) => arms.iter().any(|(_, b)| tail_returns_thunk(b)),
        Comp::Mask(_, b) => tail_returns_thunk(b),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            tail_returns_thunk(body)
                || return_body
                    .as_ref()
                    .is_some_and(|rb| tail_returns_thunk(rb))
                || ops.iter().any(|op| tail_returns_thunk(&op.body))
        }
        _ => false,
    }
}

// An open handler whose resume escapes into a closure (the parameter-passing
// k(v)(s) idiom with a foreign effect passing through) has a function-typed
// answer that surfaces Eff values when forced later, so its applications need
// the uniform whole-program calling convention.
fn open_resume_escapes(c: &Comp, fl: &Latent) -> bool {
    if let Comp::Handle { body, ops, .. } = c {
        let mut s = BTreeSet::new();
        latent(body, fl, &mut s);
        for op in ops {
            s.remove(&MaskOp {
                id: op.name,
                depth: 0,
            });
        }
        if !s.is_empty() && ops.iter().any(|op| resume_in_thunk(&op.body, op.resume)) {
            return true;
        }
    }
    let mut found = false;
    each_subcomp(c, &mut |sc| found |= open_resume_escapes(sc, fl));
    found
}

fn resume_in_thunk(c: &Comp, resume: Sym) -> bool {
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            found |= fv::comp(t).contains(&resume);
        }
    });
    each_subcomp(c, &mut |sc| found |= resume_in_thunk(sc, resume));
    found
}

// Convention-boundary rail, run in both selective and whole-program mode. A
// monadic context must end in an Eff value at every tail: an EPure/EOp
// construction, a saturated call to a program function (itself Eff-tailed by
// induction or because it is the direct callee a monadic context EPure-wrapped),
// a dynamic application of a monadified closure, or a diverging Error. A function
// the rewrite should have monadified but did not shows up here as an ICE, exactly
// where the old whole-program uniformity used to make a missed boundary
// impossible, rather than as a miscompile at a distant dynamic call site.
//
// Whole-program mode (`full`): every function, generated driver, and thunk body
// is monadic, so all are checked, including under their lambda binders. Selective
// mode: only the `monadic` program functions are; their top-level tail is checked
// (their interior mixes monadic continuation thunks with direct data thunks, so a
// blanket thunk check would false-positive). `main` is exempt either way because
// `unwrap_main` strips its final EPure.
fn check_convention_boundaries(
    arity_fns: &[CoreFn],
    check: &[&CoreFn],
    monadic: &BTreeSet<Sym>,
    blanket: bool,
    exempt: &BTreeSet<Sym>,
) -> Result<(), TypeError> {
    let arities: BTreeMap<&str, usize> = arity_fns
        .iter()
        .map(|f| (f.name.as_str(), f.params.len()))
        .collect();
    for f in check {
        if !monadic.contains(&f.name) || exempt.contains(&f.name) {
            continue;
        }
        check_tails(f.name.as_str(), &f.body, &arities)?;
        if blanket {
            // A full-style monadic function monadifies every thunk body too, so
            // each (under its lambda binder) must also be Eff-tailed.
            let mut ts = Vec::new();
            thunks_in_comp(&f.body, &mut ts);
            for t in ts {
                let b = if let Comp::Lam(_, b) = t { b } else { t };
                check_tails(f.name.as_str(), b, &arities)?;
            }
        }
    }
    Ok(())
}

fn check_tails(fname: &str, c: &Comp, arities: &BTreeMap<&str, usize>) -> Result<(), TypeError> {
    match c {
        Comp::Bind(_, _, n) => check_tails(fname, n, arities)?,
        Comp::If(_, t, e) => {
            check_tails(fname, t, arities)?;
            check_tails(fname, e, arities)?;
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                check_tails(fname, b, arities)?;
            }
        }
        Comp::Return(Value::Ctor(n, ..)) if n == EPURE || n == EOP => {}
        Comp::Call(g, args) if g != ENTRY_POINT && arities.get(g.as_str()) == Some(&args.len()) => {
        }
        Comp::App(..) | Comp::Error(_) => {}
        other => {
            return Err(TypeError::Ice {
                msg: format!(
                    "monadification: `{fname}` tail is not Eff-shaped: {}",
                    other.kind()
                ),
            });
        }
    }
    Ok(())
}

// Invariant check: between selective and whole-program mode, lowering must
// eliminate every `do` and `handle`. A survivor is a compiler bug.
/// # Errors
/// Fails if any `do` or `handle` survives lowering.
pub fn residual_effects(core: &Core) -> Result<(), String> {
    for f in &core.fns {
        if raw_effects(&f.body) {
            return Err(format!("residual effect in `{}` after lowering", f.name));
        }
    }
    Ok(())
}

fn raw_effects(c: &Comp) -> bool {
    if matches!(c, Comp::Do(..) | Comp::Handle { .. } | Comp::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| found |= raw_effects_value(v));
    each_subcomp(c, &mut |sc| found |= raw_effects(sc));
    found
}

fn raw_effects_value(v: &Value) -> bool {
    match v {
        Value::Thunk(c) => raw_effects(c),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().any(raw_effects_value),
        _ => false,
    }
}

fn all_calls(c: &Comp, out: &mut BTreeSet<Sym>) {
    if let Comp::Call(g, _) = c {
        out.insert(*g);
    }
    each_subcomp(c, &mut |sc| all_calls(sc, out));
}

fn thunks_in_comp<'a>(c: &'a Comp, out: &mut Vec<&'a Comp>) {
    each_value(c, &mut |v| thunks_in_value(v, out));
    each_subcomp(c, &mut |sc| thunks_in_comp(sc, out));
}

fn thunks_in_value<'a>(v: &'a Value, out: &mut Vec<&'a Comp>) {
    match v {
        Value::Thunk(c) => {
            out.push(c);
            thunks_in_comp(c, out);
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            for f in fs {
                thunks_in_value(f, out);
            }
        }
        _ => {}
    }
}

fn each_value<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Value)) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        // Reuse nodes only arise after this pass; keep the traversal total. The
        // freed cell and the reuse constructor are the value positions.
        | Comp::WithReuse { freed: v, .. }
        | Comp::Reuse(_, v)
        // Ref ops arise from `erase_local_vars` at the top of `lower`, so the
        // analyses below must visit their values (e.g. a thunk a var holds whose
        // body still performs another effect).
        | Comp::RefNew(v)
        | Comp::RefGet(v)
        | Comp::If(v, ..)
        | Comp::Case(v, _) => f(v),
        Comp::Prim(_, a, b) | Comp::RefSet(a, b) => {
            f(a);
            f(b);
        }
        Comp::App(_, args)
        | Comp::Call(_, args)
        | Comp::Do(_, args)
        | Comp::StrBuiltin(_, args) => {
            for a in args {
                f(a);
            }
        }
        _ => {}
    }
}

fn each_subcomp<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Comp)) {
    match c {
        Comp::Bind(m, _, n) => {
            f(m);
            f(n);
        }
        Comp::Lam(_, b) | Comp::Mask(_, b) | Comp::WithReuse { body: b, .. } => f(b),
        Comp::App(g, _) => f(g),
        Comp::If(_, t, e) => {
            f(t);
            f(e);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                f(b);
            }
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            f(body);
            if let Some(rb) = return_body {
                f(rb);
            }
            for o in ops {
                f(&o.body);
            }
        }
        _ => {}
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

fn contains_mask(c: &Comp) -> bool {
    if matches!(c, Comp::Mask(..)) {
        return true;
    }
    let mut found = false;
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        found |= ts.iter().any(|t| contains_mask(t));
    });
    each_subcomp(c, &mut |sc| found |= contains_mask(sc));
    found
}

// Latent sets track mask depth in a `MaskOp { id, depth }`: depth d means d
// handlers of the op's effect must still be skipped. A handler removes its ops
// at depth 0 and peels one level off deeper ones; a mask pushes its ops one
// level down.
fn latent(c: &Comp, fl: &Latent, out: &mut BTreeSet<MaskOp>) {
    match c {
        Comp::Do(op, _) => {
            out.insert(MaskOp { id: *op, depth: 0 });
        }
        Comp::Call(g, _) => {
            if let Some(s) = fl.get(g) {
                out.extend(s.iter().copied());
            }
        }
        Comp::Bind(m, _, n) => {
            latent(m, fl, out);
            latent(n, fl, out);
        }
        Comp::If(_, t, e) => {
            latent(t, fl, out);
            latent(e, fl, out);
        }
        Comp::Case(_, arms) => {
            for (_, b) in arms {
                latent(b, fl, out);
            }
        }
        Comp::App(f, _) => latent(f, fl, out),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            let mut inner = BTreeSet::new();
            latent(body, fl, &mut inner);
            for op in ops {
                inner.remove(&MaskOp {
                    id: op.name,
                    depth: 0,
                });
            }
            out.extend(inner.into_iter().map(|l| {
                if ops.iter().any(|op| op.name == l.id) {
                    MaskOp {
                        id: l.id,
                        depth: l.depth - 1,
                    }
                } else {
                    l
                }
            }));
            if let Some(rb) = return_body {
                latent(rb, fl, out);
            }
            for op in ops {
                // A parameter-passing clause returns a transformer thunk that the
                // handler driver then applies, so the ops it re-performs (a
                // `stake`-style `\acc -> { do op(..); resume(..) }`) are latent
                // here, not hidden behind the thunk.
                match &op.body {
                    Comp::Return(Value::Thunk(t)) => {
                        let inner = if let Comp::Lam(_, b) = t.as_ref() {
                            b
                        } else {
                            t
                        };
                        latent(inner, fl, out);
                    }
                    _ => latent(&op.body, fl, out),
                }
            }
        }
        Comp::Mask(ops, body) => {
            let mut inner = BTreeSet::new();
            latent(body, fl, &mut inner);
            out.extend(inner.into_iter().map(|l| {
                if ops.contains(&l.id) {
                    MaskOp {
                        id: l.id,
                        depth: l.depth + 1,
                    }
                } else {
                    l
                }
            }));
        }
        _ => {}
    }
}

fn collect_ops(c: &Comp, out: &mut BTreeSet<Sym>) {
    match c {
        Comp::Do(op, _) => {
            out.insert(*op);
        }
        Comp::Handle { ops, .. } => {
            for op in ops {
                out.insert(op.name);
            }
        }
        Comp::Mask(ops, _) => out.extend(ops.iter().copied()),
        _ => {}
    }
    each_value(c, &mut |v| {
        let mut ts = Vec::new();
        thunks_in_value(v, &mut ts);
        for t in ts {
            collect_ops(t, out);
        }
    });
    each_subcomp(c, &mut |sc| collect_ops(sc, out));
}
