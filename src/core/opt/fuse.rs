//! Whole-program stream fusion for the pull `Sequence` substrate.
//!
//! A pull sequence is `(Unit) -> Step(a)` with
//! `Step(a) = SDone | SMore(a, (Unit) -> Step(a))`. Each pipeline stage allocates,
//! per element, one `SMore` cell and one tail closure; a `producer |> map |> filter
//! |> fold` chain pays for every intermediate. The inliner cannot remove this cost
//! because the combinators are recursive and multi-call-site, so producer and
//! consumer never share a body for case-of-known-constructor to cancel the `SMore`
//! against its own destruction.
//!
//! This pass fuses the `Step` hylomorphism directly on whole-program Core. It
//! recognizes a fusion seed (a self-recursive consumer whose recursion is driven by
//! matching the two `Step` constructors on a forced sequence, applied to a producer
//! expression built from known step-shaped combinators), drives the producer's step
//! body into the consumer's forcing site, pushes the consumer match through the
//! producer's `if`/`case` spine (case-of-case) until each branch meets the empty or
//! cons constructor directly so the construction and destruction cancel, and ties
//! the knot: driving reproduces the seed pipeline advanced by one element, so the
//! whole loop residualizes into one fresh top-level join function whose parameters
//! are the advancing state and the consumer's accumulators. The result is a single
//! loop with no `Step` cells.
//!
//! The knot is keyed by anti-unification (most-specific generalization) of the seed
//! pipeline against its one-step tail: positions that differ become join parameters
//! (ordered by first occurrence in a fixed producer-first traversal, so the join
//! signature is byte-stable), positions that coincide stay baked in. A
//! generalization whose recursion value references a variable bound inside the
//! driven body (a captured local) is refused (the classic most-specific-
//! generalization scope trap).
//!
//! Every misfire degrades to not fusing: a seed whose driving exceeds the unfold or
//! size budget, whose bodies perform any effect, or whose shape is unrecognized is
//! left exactly as written. The pass only ever ADDS a top-level function and
//! redirects one call, never a partial rewrite, so a fused pipeline is a lowering
//! tier in all but name and the ON/OFF differential oracle gates it.

use std::collections::{BTreeMap, BTreeSet};

use super::super::cbpv::{Comp, Core, CoreFn, CorePat, Value};
use super::super::fv;
use super::super::traverse::{Rewrite, Visit};
use super::rename;
use super::specialize::subst_comp;
use crate::names::{self, FRESH_FUSE};
use crate::sym::Sym;

// A seed whose symbolic driving takes more than this many reduction steps aborts
// to not-fusing: the configuration is not converging on the regular pipeline shape
// this cut recognizes.
const UNFOLD_BUDGET: u32 = 4000;
// A driven `Step` tree larger than this many nodes aborts to not-fusing: the
// residual is growing without the expected fold, so leave the source untouched.
const SIZE_BUDGET: usize = 20_000;
// The `Unit` witness applied to a forced sequence thunk (`s(())`).
const UNIT: Value = Value::Unit;

/// The two `Step` constructors of the sequence type in play, learned from the
/// consumer's match rather than hard-coded, so no combinator name is a cross-phase
/// contract: `done` is the nullary (empty) constructor, `more` the binary
/// (head, tail) one.
#[derive(Clone, Copy)]
struct StepCtors {
    done: Sym,
    more: Sym,
}

/// A pull-sequence pipeline as a tree: a combinator applied to its arguments, with
/// the single stream-typed argument recursively a nested pipeline. A producer has
/// no `Stream` argument; a transformer has exactly one.
#[derive(Clone, Debug)]
struct StreamExpr {
    comb: Sym,
    args: Vec<Arg>,
}

#[derive(Clone, Debug)]
enum Arg {
    /// An ordinary value argument (a bound, a mapper/predicate thunk, a count).
    Val(Value),
    /// The stream-typed argument: the inner pipeline this combinator consumes.
    Stream(Box<StreamExpr>),
}

/// A combinator's role in a pipeline: a producer forces no stream parameter, a
/// transformer forces exactly the parameter at the given index.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    Producer,
    Transformer(usize),
}

/// One compiled match arm: a pattern and its body (the shape `Comp::Case` carries).
type Arm = (CorePat, Comp);

/// One symbolic production step of a driven pipeline: the shape of `force(pipe)(())`
/// after the intermediate `Step` cells have been cancelled against the consumer's
/// match. Leaves carry the (already fused) head value and the pipeline advanced by
/// one element.
enum Step {
    /// The pipeline is exhausted (every stage reached the empty constructor).
    Done,
    /// The pipeline yields `head`, and its tail is `next`.
    Yield { head: Value, next: StreamExpr },
    /// A stage (a filter) consumed an element without yielding; continue at `next`
    /// without advancing the consumer.
    Skip { next: StreamExpr },
    /// A guard from the producer or a filtering stage.
    Branch {
        cond: Value,
        then: Box<Self>,
        els: Box<Self>,
    },
    /// A pure head computation (a mapper application reduced to a `Prim`/`Call`)
    /// scoped over the rest of the step.
    Let {
        var: Sym,
        comp: Comp,
        body: Box<Self>,
    },
}

/// The context threaded through recognition and driving: the program's functions by
/// name, a purity memo, and the deterministic fresh-name and join counters.
struct Cx<'a> {
    fns: BTreeMap<Sym, &'a CoreFn>,
    pure: BTreeMap<Sym, bool>,
    fresh: u32,
    joins: u32,
    /// Join functions produced this run, appended to the program at the end.
    emitted: Vec<CoreFn>,
}

/// Fuse every recognized pull-sequence pipeline in `core`, returning the rewritten
/// program and the number of seeds fused (the pass tick count for telemetry).
///
/// A no-op when no seed is recognized; every unrecognized or over-budget
/// configuration is left untouched (degrade to not fusing, never a partial
/// rewrite).
pub(crate) fn fuse_counted(core: &Core) -> (Core, u64) {
    let mut cx = Cx {
        fns: core.fns.iter().map(|f| (f.name, f)).collect(),
        pure: BTreeMap::new(),
        fresh: 0,
        joins: 0,
        emitted: Vec::new(),
    };
    // Rewrite each function body, redirecting any recognized seed call to a fresh
    // join. Bodies are processed in program order and the join counter is shared,
    // so names are deterministic. When a body actually fused, its now-dead upstream
    // pipeline (the combinator calls and mapper/predicate closures the redirected
    // consumer no longer reads) is removed by dead-let elimination, so the fused loop
    // stands alone instead of running beside a discarded allocation.
    let mut fns: Vec<CoreFn> = core
        .fns
        .iter()
        .map(|f| {
            let before = cx.joins;
            let mut body = rewrite_body(&f.body, &mut cx);
            if cx.joins > before {
                body = dead_let_elim(&body, &mut cx);
            }
            CoreFn {
                name: f.name,
                params: f.params.clone(),
                dict_arity: f.dict_arity,
                body,
            }
        })
        .collect();
    let ticks = u64::from(cx.joins);
    fns.append(&mut cx.emitted);
    (Core { fns }, ticks)
}

// Walk `body`, replacing every recognized seed call with a call to a freshly
// emitted join function. Tracks the enclosing let-bindings so a seed's sequence
// argument (a `Var` bound upstream to a combinator call) can be resolved.
fn rewrite_body(body: &Comp, cx: &mut Cx<'_>) -> Comp {
    let mut env: BTreeMap<Sym, Comp> = BTreeMap::new();
    rewrite_in(body, &mut env, cx)
}

fn rewrite_in(c: &Comp, env: &mut BTreeMap<Sym, Comp>, cx: &mut Cx<'_>) -> Comp {
    match c {
        Comp::Bind(a, x, k) => {
            let a2 = rewrite_in(a, env, cx);
            // Record the binding so a later seed can resolve `x` to its definition.
            env.insert(*x, (*a).as_ref().clone());
            let k2 = rewrite_in(k, env, cx);
            env.remove(x);
            // A seed in tail position of the bound computation is already handled by
            // the recursive `rewrite_in(a)`; here we additionally try the whole bind
            // head as a seed (a `Call` bound to `x`).
            Comp::Bind(Box::new(a2), *x, Box::new(k2))
        }
        Comp::Call(f, args) => try_fuse_call(*f, args, env, cx).unwrap_or_else(|| c.clone()),
        _ => descend_rewrite(c, env, cx),
    }
}

// Structural recursion for the non-seed-bearing cases, tracking no new bindings
// (only `Bind` introduces the let scope a seed needs).
fn descend_rewrite(c: &Comp, env: &mut BTreeMap<Sym, Comp>, cx: &mut Cx<'_>) -> Comp {
    struct R<'a, 'b> {
        env: &'a mut BTreeMap<Sym, Comp>,
        cx: &'a mut Cx<'b>,
    }
    impl Rewrite for R<'_, '_> {
        type Ctx = ();
        fn comp(&mut self, c: &Comp, (): &()) -> Comp {
            match c {
                Comp::Bind(..) | Comp::Call(..) => rewrite_in(c, self.env, self.cx),
                _ => self.descend_comp(c, &()),
            }
        }
    }
    R { env, cx }.descend_comp(c, &())
}

// Try to recognize and fuse `Call(f, args)` as a fusion seed. Returns the
// redirected call (to a fresh join) on success, `None` to leave it untouched.
fn try_fuse_call(
    f: Sym,
    args: &[Value],
    env: &BTreeMap<Sym, Comp>,
    cx: &mut Cx<'_>,
) -> Option<Comp> {
    let consumer = resolve_consumer(f, args, cx)?;
    // The sequence the consumer folds, resolved from the seed's sequence argument
    // through the enclosing let-bindings into a pipeline tree.
    let seed_stream = resolve_stream(&consumer.seq_arg, env, cx)?;
    // Purity gate: every combinator body and every baked closure in the driven
    // region must be effect-free (this cut fuses no effectful step).
    if !stream_pure(&seed_stream, cx) || !consumer.pure(cx) {
        return None;
    }
    build_join(&consumer, &seed_stream, cx)
}

// --- consumer recognition -------------------------------------------------------

/// A fold-shaped consumer resolved to its driving form: it forces its sequence
/// parameter, matches the two `Step` constructors, and tail-recurses on the cons
/// tail. Wrapper consumers (`sum = fold(s, 0, add)`) are peeled to the underlying
/// fold, carrying the wrapper's fixed arguments.
struct Consumer {
    ctors: StepCtors,
    /// The sequence argument at the seed call site (before let-resolution).
    seq_arg: Value,
    /// The accumulator arguments at the seed call site (non-sequence, non-closure
    /// state), paired with how each advances in the recursive call.
    accs: Vec<Acc>,
    /// The closure arguments baked into the fold (mappers/fold-functions), by the
    /// fold's parameter name, substituted into every body.
    baked: BTreeMap<Sym, Value>,
    /// The empty-arm body (the fold's result when the sequence is exhausted), over
    /// the accumulator parameters.
    done_body: Comp,
    /// The cons-arm body up to (not including) the self-call: the per-element
    /// action computing the next accumulators. Binds the element variable `elem`.
    step_body: Comp,
    /// The element binder introduced by the cons pattern.
    elem: Sym,
    /// The fold's own parameter names for the accumulators, in order.
    acc_params: Vec<Sym>,
    /// Every function name reachable in the consumer's driven region (for purity).
    fn_names: Vec<Sym>,
}

/// One accumulator: the fold parameter, its seed value, and its advance expression
/// (the corresponding self-call argument, over the parameters and the element).
struct Acc {
    seed: Value,
    advance: Value,
}

impl Consumer {
    fn pure(&self, cx: &mut Cx<'_>) -> bool {
        comp_pure(&self.done_body, cx)
            && comp_pure(&self.step_body, cx)
            && self.baked.values().all(|v| value_pure(v, cx))
            && self.fn_names.iter().all(|n| fn_pure(*n, cx))
    }
}

// Resolve the seed call head to a fold-shaped consumer, peeling wrapper functions
// (a body that is a single call to another consumer with the sequence threaded).
fn resolve_consumer(f: Sym, args: &[Value], cx: &mut Cx<'_>) -> Option<Consumer> {
    let def = cx.fns.get(&f).copied()?;
    if def.params.len() != args.len() {
        return None;
    }
    // A direct fold analyses the raw body (parameters intact, so its forcing site
    // names a parameter). A wrapper (`sum = fold(s, 0, add)`) needs the arguments
    // substituted to expose its single delegate call.
    if let Some(c) = fold_consumer(f, &def.params, args, &def.body, cx) {
        return Some(c);
    }
    let sub: BTreeMap<Sym, Value> = def
        .params
        .iter()
        .copied()
        .zip(args.iter().cloned())
        .collect();
    let body = normalize(&subst(&def.body, &sub, cx), cx)?;
    if let Comp::Call(g, wargs) = &body {
        if *g != f {
            return resolve_consumer(*g, wargs, cx);
        }
    }
    None
}

// Match the canonical fold shape on the (copy-propagated) raw body and extract its
// driving pieces, filling accumulator seeds from the seed call `args`. Returns
// `None` if the body is not a fold over one of its parameters.
fn fold_consumer(
    f: Sym,
    params: &[Sym],
    args: &[Value],
    raw_body: &Comp,
    cx: &mut Cx<'_>,
) -> Option<Consumer> {
    // Copy-propagate the elaboration's `return x to t` aliases so the forcing site,
    // match, and self-call read structurally, then expect
    // `Bind(force(seq)(()), st, Case st arms)`.
    let body = copy_prop(raw_body, cx);
    let (seq, st, arms) = match_force_case(&body)?;
    // `seq` must be one of the fold's own parameters (the sequence being folded).
    let seq_idx = params.iter().position(|p| *p == seq)?;
    let (ctors, done_body, elem, tail, step_body) = match_step_arms(st, arms)?;
    // The self-call in the cons arm: `Call(f, [tail, adv...])`, tail in the seq slot.
    let (callee, cargs) = tail_self_call(&step_body, f)?;
    if callee != f || cargs.len() != params.len() {
        return None;
    }
    if !matches!(&cargs[seq_idx], Value::Var(v) if *v == tail) {
        return None;
    }
    // Partition the non-sequence parameters into accumulators (advancing) and baked
    // closures (invariant). A parameter whose self-call argument is itself (`Var p`)
    // and whose seed argument is a thunk is baked; otherwise it is an accumulator.
    let mut accs = Vec::new();
    let mut baked = BTreeMap::new();
    let mut acc_params = Vec::new();
    for (i, p) in params.iter().enumerate() {
        if i == seq_idx {
            continue;
        }
        let advance = cargs[i].clone();
        let invariant = matches!(&advance, Value::Var(v) if v == p);
        if invariant && matches!(&args[i], Value::Thunk(_)) {
            baked.insert(*p, args[i].clone());
        } else {
            accs.push(Acc {
                seed: args[i].clone(),
                advance,
            });
            acc_params.push(*p);
        }
    }
    let mut fn_names = Vec::new();
    collect_calls(&done_body, &mut fn_names);
    collect_calls(&step_body, &mut fn_names);
    fn_names.retain(|n| *n != f);
    Some(Consumer {
        ctors,
        seq_arg: args[seq_idx].clone(),
        accs,
        baked,
        done_body,
        step_body: strip_self_call(&step_body, f),
        elem,
        acc_params,
        fn_names,
    })
}

// Peel leading pure `Bind(Return v, x, k)` lets (copy-propagated by `normalize`
// already, but a residual value let can remain), then match
// `Bind(App(Force(Var seq), [Unit]), st, Case(Var st, arms))`.
fn match_force_case(body: &Comp) -> Option<(Sym, Sym, &[Arm])> {
    if let Comp::Bind(a, st, k) = body {
        if let Comp::App(head, app_args) = a.as_ref() {
            if let Comp::Force(Value::Var(seq)) = head.as_ref() {
                if app_args.len() == 1 && is_unit(&app_args[0]) {
                    if let Comp::Case(Value::Var(sc), arms) = k.as_ref() {
                        if sc == st {
                            return Some((*seq, *st, arms));
                        }
                    }
                }
            }
        }
    }
    None
}

// Split the two-arm `Step` match into (ctors, done-body, elem, tail, cons-body).
fn match_step_arms(_st: Sym, arms: &[Arm]) -> Option<(StepCtors, Comp, Sym, Sym, Comp)> {
    if arms.len() != 2 {
        return None;
    }
    let mut done: Option<(Sym, Comp)> = None;
    let mut more: Option<(Sym, Sym, Sym, Comp)> = None;
    for (p, b) in arms {
        match p {
            CorePat::Ctor(c, bs) if bs.is_empty() => done = Some((*c, b.clone())),
            CorePat::Ctor(c, bs) if bs.len() == 2 => {
                let x = bs[0]?;
                let next = bs[1]?;
                more = Some((*c, x, next, b.clone()));
            }
            _ => return None,
        }
    }
    let (dc, db) = done?;
    let (mc, elem, tail, mb) = more?;
    Some((StepCtors { done: dc, more: mc }, db, elem, tail, mb))
}

// The tail self-call `Call(f, args)` reachable through the cons-arm's straight-line
// binds (the recursion is the last computation).
fn tail_self_call(body: &Comp, f: Sym) -> Option<(Sym, Vec<Value>)> {
    match body {
        Comp::Call(g, args) if *g == f => Some((*g, args.clone())),
        Comp::Bind(_, _, k) => tail_self_call(k, f),
        _ => None,
    }
}

// Replace the tail self-call with a `Return(Unit)` marker: the cons-arm body then
// holds exactly the per-element action (the accumulator computations) as a
// straight-line prefix, which the residualizer re-emits before the recursive join
// call.
fn strip_self_call(body: &Comp, f: Sym) -> Comp {
    match body {
        Comp::Call(g, _) if *g == f => Comp::Return(Value::Unit),
        Comp::Bind(a, x, k) => Comp::Bind(a.clone(), *x, Box::new(strip_self_call(k, f))),
        other => other.clone(),
    }
}

// --- stream resolution ----------------------------------------------------------

// Resolve a sequence argument (a value, usually a `Var` bound upstream to a
// combinator call) into a pipeline tree. Producers bottom the recursion.
fn resolve_stream(seq: &Value, env: &BTreeMap<Sym, Comp>, cx: &mut Cx<'_>) -> Option<StreamExpr> {
    let Value::Var(v) = seq else {
        return None;
    };
    let def = env.get(v)?.clone();
    resolve_stream_comp(&def, env, cx)
}

// Resolve a stream-valued computation to a pipeline tree. Elaboration nests a whole
// pipeline as one `Bind`-chain (the inner stages are `Bind(Call(comb, ..), t, ..)`
// leading to the outermost call), so copy-propagate to inline the value aliases,
// flatten the chain into the resolution environment, and resolve the trailing call.
fn resolve_stream_comp(
    def: &Comp,
    env: &BTreeMap<Sym, Comp>,
    cx: &mut Cx<'_>,
) -> Option<StreamExpr> {
    let def = copy_prop(def, cx);
    let mut local = env.clone();
    let mut cur = &def;
    while let Comp::Bind(a, x, k) = cur {
        local.insert(*x, (**a).clone());
        cur = k;
    }
    match cur {
        Comp::Call(k, a) => stream_of_call(*k, a, &local, cx),
        Comp::Return(Value::Var(w)) => resolve_stream(&Value::Var(*w), &local, cx),
        _ => None,
    }
}

// Chase let-aliases (`x = Return v`) to a ground value: a literal or a thunk. A
// producer bound or a mapper/predicate closure reaches its definition this way, so
// it is baked into the join as a value rather than a reference to a caller-local.
fn resolve_value(v: &Value, env: &BTreeMap<Sym, Comp>) -> Value {
    if let Value::Var(x) = v {
        if let Some(Comp::Return(inner)) = env.get(x) {
            return resolve_value(inner, env);
        }
    }
    v.clone()
}

fn stream_of_call(
    comb: Sym,
    cargs: &[Value],
    env: &BTreeMap<Sym, Comp>,
    cx: &mut Cx<'_>,
) -> Option<StreamExpr> {
    let stream_idx = match stream_role(comb, cx)? {
        Role::Producer => None,
        Role::Transformer(i) => Some(i),
    };
    let mut args = Vec::with_capacity(cargs.len());
    for (i, a) in cargs.iter().enumerate() {
        if Some(i) == stream_idx {
            args.push(Arg::Stream(Box::new(resolve_stream(a, env, cx)?)));
        } else {
            args.push(Arg::Val(resolve_value(a, env)));
        }
    }
    Some(StreamExpr { comb, args })
}

// The role of combinator `comb`: a producer (forces no parameter) or a transformer
// (forces exactly one). `None` when `comb` is unknown or forces more than one
// parameter (a binary combinator like `zip`), which this cut does not fuse.
fn stream_role(comb: Sym, cx: &mut Cx<'_>) -> Option<Role> {
    let def = cx.fns.get(&comb).copied()?;
    let params = def.params.clone();
    // Copy-propagate first: elaboration forces an alias (`return s to t; force t`),
    // so the raw body never names the parameter at the forcing site.
    let body = copy_prop(&def.body, cx);
    // The body is `Return(Thunk(Lam([_], step)))`; find which parameters are forced
    // and applied to unit inside the step.
    let forced = forced_params(&body, &params);
    match forced.len() {
        0 => Some(Role::Producer),
        1 => Some(Role::Transformer(forced[0])),
        _ => None,
    }
}

// The parameter indices that appear as `force(param)(())` anywhere in `body`.
fn forced_params(body: &Comp, params: &[Sym]) -> Vec<usize> {
    struct F<'a> {
        params: &'a [Sym],
        hits: Vec<usize>,
    }
    impl Visit for F<'_> {
        fn visit_comp(&mut self, c: &Comp) {
            if let Comp::App(head, args) = c {
                if let Comp::Force(Value::Var(v)) = head.as_ref() {
                    if args.len() == 1 && is_unit(&args[0]) {
                        if let Some(i) = self.params.iter().position(|p| p == v) {
                            if !self.hits.contains(&i) {
                                self.hits.push(i);
                            }
                        }
                    }
                }
            }
            self.descend_comp(c);
        }
    }
    let mut f = F {
        params,
        hits: Vec::new(),
    };
    f.visit_comp(body);
    f.hits
}

// --- purity ---------------------------------------------------------------------

fn stream_pure(s: &StreamExpr, cx: &mut Cx<'_>) -> bool {
    fn_pure(s.comb, cx)
        && s.args.iter().all(|a| match a {
            Arg::Val(v) => value_pure(v, cx),
            Arg::Stream(inner) => stream_pure(inner, cx),
        })
}

// A function is fusion-pure when no path through the call graph from its body reaches
// a direct effect node or an unknown call head. This is a reachability property, so a
// single optimistic-seed descent cannot memoize it soundly: under mutual recursion a
// co-recursive member can be finalized against an in-progress member's provisional
// verdict, committing a genuinely impure function as pure. We therefore condense the
// call graph into strongly connected components (Tarjan) and commit one shared verdict
// per component, and only once the whole component has fully resolved. A component is
// pure when every member is free of direct effects and unknown heads and every edge
// leaving the component targets an already-resolved pure function; edges inside the
// component are mutual recursion and never introduce impurity on their own. The
// drive-time `comp_pure` re-check below stays as defense in depth.
fn fn_pure(name: Sym, cx: &mut Cx<'_>) -> bool {
    if let Some(&p) = cx.pure.get(&name) {
        return p;
    }
    if !cx.fns.contains_key(&name) {
        // An unknown call head cannot be proven pure.
        cx.pure.insert(name, false);
        return false;
    }
    let mut walk = PurityWalk::default();
    walk.connect(name, cx);
    cx.pure.get(&name).copied().unwrap_or(false)
}

// A function body's own purity contribution: whether it directly performs an effect
// (or calls an unknown head), plus the known-head functions it calls. The call set is
// collected by descending the whole body (through thunks, lambdas, arguments, and
// arms) exactly as the purity check descends, so the reachability fixpoint the walk
// computes matches the one the recursive check would reach.
struct BodyInfo {
    self_bad: bool,
    callees: Vec<Sym>,
}

fn body_info(def: &CoreFn, fns: &BTreeMap<Sym, &CoreFn>) -> BodyInfo {
    struct Scan<'a, 'b> {
        fns: &'a BTreeMap<Sym, &'b CoreFn>,
        info: BodyInfo,
    }
    impl Visit for Scan<'_, '_> {
        fn visit_comp(&mut self, c: &Comp) {
            match c {
                Comp::Call(f, _) => {
                    if self.fns.contains_key(f) {
                        if !self.info.callees.contains(f) {
                            self.info.callees.push(*f);
                        }
                    } else {
                        self.info.self_bad = true;
                    }
                }
                Comp::Io(..)
                | Comp::Do(..)
                | Comp::Handle { .. }
                | Comp::Mask(..)
                | Comp::Error(_)
                | Comp::RefNew(_)
                | Comp::RefGet(_)
                | Comp::RefSet(..) => self.info.self_bad = true,
                _ => {}
            }
            self.descend_comp(c);
        }
    }
    let mut scan = Scan {
        fns,
        info: BodyInfo {
            self_bad: false,
            callees: Vec::new(),
        },
    };
    scan.visit_comp(&def.body);
    scan.info
}

// Scratch state for one strongly-connected-component purity walk (Tarjan). It lives
// for the duration of a single `fn_pure` memo miss; every node it pushes is popped and
// finalized into `cx.pure` before the walk returns, so the stack is empty on exit and
// no provisional index leaks to a later walk.
#[derive(Default)]
struct PurityWalk {
    index: BTreeMap<Sym, u32>,
    low: BTreeMap<Sym, u32>,
    stack: Vec<Sym>,
    on_stack: BTreeSet<Sym>,
    info: BTreeMap<Sym, BodyInfo>,
    counter: u32,
}

impl PurityWalk {
    fn connect(&mut self, v: Sym, cx: &mut Cx<'_>) {
        let info = match cx.fns.get(&v).copied() {
            Some(def) => body_info(def, &cx.fns),
            None => BodyInfo {
                self_bad: true,
                callees: Vec::new(),
            },
        };
        let idx = self.counter;
        self.counter += 1;
        self.index.insert(v, idx);
        self.low.insert(v, idx);
        self.stack.push(v);
        self.on_stack.insert(v);

        for &w in &info.callees {
            if cx.pure.contains_key(&w) {
                // A finalized successor: its verdict is consulted at pop time.
            } else if self.on_stack.contains(&w) {
                let lv = self.low[&v].min(self.index[&w]);
                self.low.insert(v, lv);
            } else {
                self.connect(w, cx);
                let lv = self.low[&v].min(self.low[&w]);
                self.low.insert(v, lv);
            }
        }
        self.info.insert(v, info);

        if self.low[&v] == self.index[&v] {
            let mut comp = Vec::new();
            loop {
                let x = self.stack.pop().expect("purity walk stack underflow");
                self.on_stack.remove(&x);
                comp.push(x);
                if x == v {
                    break;
                }
            }
            let members: BTreeSet<Sym> = comp.iter().copied().collect();
            let mut pure_scc = true;
            for x in &comp {
                let xi = &self.info[x];
                if xi.self_bad {
                    pure_scc = false;
                }
                for w in &xi.callees {
                    if members.contains(w) {
                        continue;
                    }
                    // An edge leaving the component targets an already-resolved
                    // function; anything but a finalized-pure target taints the
                    // whole component, so a missing verdict is never assumed pure.
                    if cx.pure.get(w) != Some(&true) {
                        pure_scc = false;
                    }
                }
            }
            for x in &comp {
                cx.pure.insert(*x, pure_scc);
            }
        }
    }
}

fn comp_pure(c: &Comp, cx: &mut Cx<'_>) -> bool {
    struct P<'a, 'b> {
        cx: &'a mut Cx<'b>,
        ok: bool,
    }
    impl Visit for P<'_, '_> {
        fn visit_comp(&mut self, c: &Comp) {
            if !self.ok {
                return;
            }
            match c {
                Comp::Call(f, _) => {
                    if fn_pure(*f, self.cx) {
                        self.descend_comp(c);
                    } else {
                        self.ok = false;
                    }
                }
                Comp::Return(_)
                | Comp::Bind(..)
                | Comp::Force(_)
                | Comp::Lam(..)
                | Comp::App(..)
                | Comp::If(..)
                | Comp::Prim(..)
                | Comp::Case(..)
                | Comp::FloatBuiltin(..)
                | Comp::Neg(..)
                | Comp::UnboxedProject(..)
                | Comp::StrBuiltin(..)
                | Comp::Dup(_)
                | Comp::Drop(_)
                | Comp::WithReuse { .. }
                | Comp::Reuse(..)
                | Comp::InitAt(..) => self.descend_comp(c),
                Comp::Io(..)
                | Comp::Do(..)
                | Comp::Handle { .. }
                | Comp::Mask(..)
                | Comp::Error(_)
                | Comp::RefNew(_)
                | Comp::RefGet(_)
                | Comp::RefSet(..) => self.ok = false,
            }
        }
    }
    let mut p = P { cx, ok: true };
    p.visit_comp(c);
    p.ok
}

fn value_pure(v: &Value, cx: &mut Cx<'_>) -> bool {
    match v {
        Value::Thunk(c) => comp_pure(c, cx),
        _ => true,
    }
}

// --- driving --------------------------------------------------------------------

// Drive one production step of pipeline `s`, with the stream-state variables kept
// symbolic. Returns the fused `Step` tree, or `None` on any unrecognized shape or
// budget overrun.
fn drive(s: &StreamExpr, ctors: StepCtors, cx: &mut Cx<'_>, budget: &mut u32) -> Option<Step> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let def = cx.fns.get(&s.comb).copied()?;
    match stream_role(s.comb, cx)? {
        Role::Producer => drive_producer(def, s, ctors, cx),
        Role::Transformer(i) => drive_transformer(def, s, i, ctors, cx, budget),
    }
}

// A producer: inline its step body with the (all-value) arguments and read the
// `Step` constructors it builds directly.
fn drive_producer(def: &CoreFn, s: &StreamExpr, ctors: StepCtors, cx: &mut Cx<'_>) -> Option<Step> {
    let sub = bind_args(def, s)?;
    let step = step_body_of(def, &sub, cx)?;
    reduce_leaf(&step, None, ctors, cx)
}

// A transformer: drive its inner stream, then push its match through the inner
// step's leaves (case-of-case), fusing away the intermediate constructor.
fn drive_transformer(
    def: &CoreFn,
    s: &StreamExpr,
    idx: usize,
    ctors: StepCtors,
    cx: &mut Cx<'_>,
    budget: &mut u32,
) -> Option<Step> {
    let Arg::Stream(inner) = &s.args[idx] else {
        return None;
    };
    let inner_step = drive(inner, ctors, cx, budget)?;
    // Inline the transformer's step body with its value arguments bound; the stream
    // parameter is left free (its forcing site is where the inner step plugs in).
    let sub = bind_value_args(def, s, idx);
    let step = step_body_of(def, &sub, cx)?;
    // `step` is `Bind(force(seqparam)(()), st, Case st arms)`; compose.
    let (_st, arms) = force_case_of(&step, def.params[idx])?;
    compose(&inner_step, &arms, s, idx, ctors, cx)
}

// Push the transformer's match `Case st arms` through the inner step's leaves.
fn compose(
    inner: &Step,
    arms: &[Arm],
    s: &StreamExpr,
    idx: usize,
    ctors: StepCtors,
    cx: &mut Cx<'_>,
) -> Option<Step> {
    match inner {
        Step::Done => arm_reduce(arms, ctors, &ArmInput::Done, cx),
        Step::Yield { head, next } => {
            arm_reduce(arms, ctors, &ArmInput::More(head.clone(), next.clone()), cx)
        }
        // The inner stage produced nothing this element: this stage also produces
        // nothing, advancing to itself over the inner tail.
        Step::Skip { next } => Some(Step::Skip {
            next: replace_stream(s, idx, next.clone()),
        }),
        Step::Branch { cond, then, els } => {
            let t = compose(then, arms, s, idx, ctors, cx)?;
            let e = compose(els, arms, s, idx, ctors, cx)?;
            Some(Step::Branch {
                cond: cond.clone(),
                then: Box::new(t),
                els: Box::new(e),
            })
        }
        Step::Let { var, comp, body } => {
            let b = compose(body, arms, s, idx, ctors, cx)?;
            Some(Step::Let {
                var: *var,
                comp: comp.clone(),
                body: Box::new(b),
            })
        }
    }
}

// What the inner step delivered to a transformer's match: the empty case, or a cons
// with a head value and a tail pipeline.
enum ArmInput {
    Done,
    More(Value, StreamExpr),
}

// Select and reduce the transformer's matching arm for the inner step's outcome,
// then reduce that arm body to this stage's `Step`.
fn arm_reduce(arms: &[Arm], ctors: StepCtors, input: &ArmInput, cx: &mut Cx<'_>) -> Option<Step> {
    for (p, b) in arms {
        match (p, input) {
            (CorePat::Ctor(c, bs), ArmInput::Done) if *c == ctors.done && bs.is_empty() => {
                return reduce_leaf(b, None, ctors, cx);
            }
            (CorePat::Ctor(c, bs), ArmInput::More(head, next)) if *c == ctors.more => {
                // Bind the arm's head/tail binders to the inner head and a marker
                // var standing for the inner tail pipeline.
                let x = bs[0]?;
                let nextb = bs[1]?;
                let marker = rename::next(&mut cx.fresh, FRESH_FUSE);
                let mut sub = BTreeMap::new();
                sub.insert(x, head.clone());
                sub.insert(nextb, Value::Var(marker));
                let body = subst(b, &sub, cx);
                let tl = (marker, next.clone());
                return reduce_leaf(&body, Some(&tl), ctors, cx);
            }
            _ => {}
        }
    }
    None
}

// Reduce a leaf computation (a producer step body, or a transformer arm after its
// head is substituted) into this stage's `Step`. `tail`, when present, binds the
// marker variable standing for the inner tail pipeline (transformer case), so an
// outgoing pipeline value `Call(comb, [.. marker ..])` resolves back to a
// `StreamExpr` instead of being emitted (and re-allocated) as a computation.
fn reduce_leaf(
    c: &Comp,
    tail: Option<&(Sym, StreamExpr)>,
    ctors: StepCtors,
    cx: &mut Cx<'_>,
) -> Option<Step> {
    let mut env: BTreeMap<Sym, StreamExpr> = BTreeMap::new();
    reduce_leaf_env(c, tail, ctors, &mut env, cx)
}

// The recursive worker: `env` maps the leaf's intermediate binders (producer
// self-tails and this stage's rebuilt tails) to their pipeline trees, so a
// constructed `SMore` tail resolves to a `StreamExpr` rather than a live `Call`.
fn reduce_leaf_env(
    c: &Comp,
    tail: Option<&(Sym, StreamExpr)>,
    ctors: StepCtors,
    env: &mut BTreeMap<Sym, StreamExpr>,
    cx: &mut Cx<'_>,
) -> Option<Step> {
    let c = normalize(c, cx)?;
    match &c {
        Comp::Return(Value::Ctor(cn, _, fields)) if *cn == ctors.done && fields.is_empty() => {
            Some(Step::Done)
        }
        Comp::Return(Value::Ctor(cn, _, fields)) if *cn == ctors.more && fields.len() == 2 => {
            let head = fields[0].clone();
            let next = resolve_tail_value(&fields[1], env)?;
            Some(Step::Yield { head, next })
        }
        Comp::If(cond, t, e) => {
            let then = reduce_leaf_env(t, tail, ctors, &mut env.clone(), cx)?;
            let els = reduce_leaf_env(e, tail, ctors, &mut env.clone(), cx)?;
            Some(Step::Branch {
                cond: cond.clone(),
                then: Box::new(then),
                els: Box::new(els),
            })
        }
        // A bare re-force of a tail pipeline (a filter's non-yielding branch): skip,
        // advancing over that tail.
        Comp::App(head, app_args) if app_args.len() == 1 && is_unit(&app_args[0]) => {
            let Comp::Force(Value::Var(t)) = head.as_ref() else {
                return None;
            };
            let next = env.get(t).cloned()?;
            Some(Step::Skip { next })
        }
        Comp::Bind(a, x, k) => {
            // A stream-tail binding `Call(K, kargs)` (K a stream combinator) names a
            // rebuilt tail; record it and continue without emitting a computation.
            if let Comp::Call(kf, kargs) = a.as_ref() {
                if is_stream_comb(*kf, cx) {
                    let se = stream_from_tailcall(*kf, kargs, tail, env, cx)?;
                    env.insert(*x, se);
                    return reduce_leaf_env(k, tail, ctors, env, cx);
                }
            }
            // Otherwise a pure head computation (a reduced mapper/predicate
            // application) scoped over the rest of the leaf.
            if comp_pure(a, cx) {
                let body = reduce_leaf_env(k, tail, ctors, env, cx)?;
                return Some(Step::Let {
                    var: *x,
                    comp: (**a).clone(),
                    body: Box::new(body),
                });
            }
            None
        }
        _ => None,
    }
}

// Resolve a constructed `SMore` tail value (always a bound variable in the shapes
// this cut recognizes) to its pipeline tree.
fn resolve_tail_value(v: &Value, env: &BTreeMap<Sym, StreamExpr>) -> Option<StreamExpr> {
    match v {
        Value::Var(t) => env.get(t).cloned(),
        _ => None,
    }
}

// Rebuild the pipeline tree for a tail `Call(K, kargs)`: a producer's advanced
// self-call (all value arguments) or a transformer over the inner tail (its stream
// slot is the marker variable, or a variable already bound in `env`).
fn stream_from_tailcall(
    k: Sym,
    kargs: &[Value],
    tail: Option<&(Sym, StreamExpr)>,
    env: &BTreeMap<Sym, StreamExpr>,
    cx: &mut Cx<'_>,
) -> Option<StreamExpr> {
    match stream_role(k, cx)? {
        Role::Producer => Some(StreamExpr {
            comb: k,
            args: kargs.iter().map(|v| Arg::Val(v.clone())).collect(),
        }),
        Role::Transformer(i) => {
            let mut args = Vec::with_capacity(kargs.len());
            for (j, v) in kargs.iter().enumerate() {
                if j == i {
                    let Value::Var(m) = v else {
                        return None;
                    };
                    let inner = match tail {
                        Some((mk, it)) if m == mk => it.clone(),
                        _ => env.get(m).cloned()?,
                    };
                    args.push(Arg::Stream(Box::new(inner)));
                } else {
                    args.push(Arg::Val(v.clone()));
                }
            }
            Some(StreamExpr { comb: k, args })
        }
    }
}

// A stream combinator returns a step thunk `\u. ...`; its body is
// `Return(Thunk(Lam([_], _)))`. Used to tell a stream-tail binding apart from a
// scalar head computation (a mapper call like `pdbl(x)`).
fn is_stream_comb(comb: Sym, cx: &Cx<'_>) -> bool {
    cx.fns.get(&comb).is_some_and(|def| {
        matches!(&def.body, Comp::Return(Value::Thunk(t))
            if matches!(t.as_ref(), Comp::Lam(ps, _) if ps.len() == 1))
    })
}

// Replace the stream argument of `s` with `inner`.
fn replace_stream(s: &StreamExpr, idx: usize, inner: StreamExpr) -> StreamExpr {
    let mut args = s.args.clone();
    args[idx] = Arg::Stream(Box::new(inner));
    StreamExpr { comb: s.comb, args }
}

// --- small helpers over Core ----------------------------------------------------

fn bind_args(def: &CoreFn, s: &StreamExpr) -> Option<BTreeMap<Sym, Value>> {
    if def.params.len() != s.args.len() {
        return None;
    }
    let mut sub = BTreeMap::new();
    for (p, a) in def.params.iter().zip(&s.args) {
        match a {
            Arg::Val(v) => {
                sub.insert(*p, v.clone());
            }
            Arg::Stream(_) => return None,
        }
    }
    Some(sub)
}

fn bind_value_args(def: &CoreFn, s: &StreamExpr, stream_idx: usize) -> BTreeMap<Sym, Value> {
    let mut sub = BTreeMap::new();
    for (i, (p, a)) in def.params.iter().zip(&s.args).enumerate() {
        if i == stream_idx {
            continue;
        }
        if let Arg::Val(v) = a {
            sub.insert(*p, v.clone());
        }
    }
    sub
}

// Inline a combinator body with `sub`, normalize, and extract its step body (the
// `\u. ...` under the returned thunk, with `u` bound to unit).
fn step_body_of(def: &CoreFn, sub: &BTreeMap<Sym, Value>, cx: &mut Cx<'_>) -> Option<Comp> {
    let body = normalize(&subst(&def.body, sub, cx), cx)?;
    if let Comp::Return(Value::Thunk(t)) = &body {
        if let Comp::Lam(ps, lam_body) = t.as_ref() {
            if ps.len() == 1 {
                let mut s2 = BTreeMap::new();
                s2.insert(ps[0], UNIT);
                // Copy-propagate the arm-internal aliases so the driven arms read
                // structurally (their tails and head computations name values, not
                // per-step `t` binders).
                let stepped = normalize(&subst(lam_body, &s2, cx), cx)?;
                return Some(copy_prop(&stepped, cx));
            }
        }
    }
    None
}

fn force_case_of(step: &Comp, seqparam: Sym) -> Option<(Sym, Vec<Arm>)> {
    if let Comp::Bind(a, st, k) = step {
        if let Comp::App(head, args) = a.as_ref() {
            if let Comp::Force(Value::Var(v)) = head.as_ref() {
                if *v == seqparam && args.len() == 1 && is_unit(&args[0]) {
                    if let Comp::Case(Value::Var(sc), arms) = k.as_ref() {
                        if sc == st {
                            return Some((*st, arms.clone()));
                        }
                    }
                }
            }
        }
    }
    None
}

const fn is_unit(v: &Value) -> bool {
    matches!(v, Value::Unit)
}

fn subst(c: &Comp, sub: &BTreeMap<Sym, Value>, cx: &mut Cx<'_>) -> Comp {
    subst_comp(c, sub, &mut cx.fresh, FRESH_FUSE)
}

fn collect_calls(c: &Comp, out: &mut Vec<Sym>) {
    super::super::cbpv::calls_in(c, out);
}

// Copy-propagate every trivial `Bind(Return v, x, k)` alias throughout `c`
// (recursively, under every binder), the cleanup elaboration's per-step `return x
// to t` sequencing leaves behind. Unlike `normalize` (head-only), this descends
// everywhere, so a self-call's arguments and a transformer's arms read structurally.
fn copy_prop(c: &Comp, cx: &mut Cx<'_>) -> Comp {
    CopyProp {
        counter: &mut cx.fresh,
    }
    .comp(c, &())
}

struct CopyProp<'a> {
    counter: &'a mut u32,
}

impl Rewrite for CopyProp<'_> {
    type Ctx = ();
    fn comp(&mut self, c: &Comp, (): &()) -> Comp {
        match c {
            Comp::Bind(a, x, k) => {
                let a2 = self.comp(a, &());
                match a2 {
                    // Inline a trivial value alias.
                    Comp::Return(v) => {
                        let mut sub = BTreeMap::new();
                        sub.insert(*x, v);
                        let k2 = subst_comp(k, &sub, self.counter, FRESH_FUSE);
                        self.comp(&k2, &())
                    }
                    // Re-associate `Bind(Bind(ia, iy, ib), x, k)` to
                    // `Bind(ia, iy, Bind(ib, x, k))` (monad associativity), so the
                    // whole computation is one flat bind spine. Elaboration nests an
                    // argument's own binds inside the outer bind; flattening lets the
                    // driver read each `Call`/`Prim` at the spine.
                    Comp::Bind(ia, iy, ib) => {
                        let inner = Comp::Bind(ib, *x, k.clone());
                        let reassoc = Comp::Bind(ia, iy, Box::new(inner));
                        self.comp(&reassoc, &())
                    }
                    other => Comp::Bind(Box::new(other), *x, Box::new(self.comp(k, &()))),
                }
            }
            _ => self.descend_comp(c, &()),
        }
    }
}

// Eliminate dead pure let-bindings from `c`: a `Bind(a, x, k)` whose bound variable
// `x` is unused in the rewritten continuation and whose `a` is effect-free is
// dropped. Applied only to a function that fused, to sweep away the upstream
// pipeline the redirected consumer no longer reads (leaving it would allocate and
// immediately free the intermediate stream). Bottom-up, so a binding that becomes
// dead only after an inner one is removed is caught in the same pass.
fn dead_let_elim(c: &Comp, cx: &mut Cx<'_>) -> Comp {
    Dce { cx }.comp(c, &())
}

struct Dce<'a, 'b> {
    cx: &'a mut Cx<'b>,
}

impl Rewrite for Dce<'_, '_> {
    type Ctx = ();
    fn comp(&mut self, c: &Comp, (): &()) -> Comp {
        match c {
            Comp::Bind(a, x, k) => {
                let a2 = self.comp(a, &());
                let k2 = self.comp(k, &());
                if !fv::comp(&k2).contains(x) && self.removable(&a2) {
                    k2
                } else {
                    Comp::Bind(Box::new(a2), *x, Box::new(k2))
                }
            }
            _ => self.descend_comp(c, &()),
        }
    }
}

impl Dce<'_, '_> {
    // A dead bound computation is removed only when it is obviously total, never
    // merely pure: dropping a diverging (even pure) computation would turn a
    // non-terminating program terminating, an observable change the determinism
    // contract forbids and the oracle (which would hang, not diff) could not catch.
    // The dead upstream pipeline is a bind-chain of `Return(_)` (a mapper/predicate
    // closure or a scalar bound) and lazy stream-combinator calls, every step `O(1)`
    // and total; a chain of total steps is total.
    fn removable(&self, a: &Comp) -> bool {
        match a {
            Comp::Return(_) => true,
            Comp::Call(f, _) => is_stream_comb(*f, self.cx),
            Comp::Bind(a, _, k) => self.removable(a) && self.removable(k),
            _ => false,
        }
    }
}

// --- normalization (bounded head reduction) -------------------------------------

// Reduce a computation by the fusion rules until its head is stuck: let-of-return,
// force-of-thunk, beta (applied lambda/forced-thunk-lambda), case-of-known-
// constructor, and if-of-known-boolean. Arithmetic is NOT folded, so a producer's
// advancing argument stays a symbolic `x + 1` rather than collapsing to a literal.
// Returns `None` on budget overrun.
fn normalize(c: &Comp, cx: &mut Cx<'_>) -> Option<Comp> {
    let mut steps = UNFOLD_BUDGET;
    normalize_go(c, cx, &mut steps)
}

fn normalize_go(c: &Comp, cx: &mut Cx<'_>, steps: &mut u32) -> Option<Comp> {
    if *steps == 0 {
        return None;
    }
    *steps -= 1;
    match c {
        Comp::Bind(a, x, k) => {
            let a = normalize_go(a, cx, steps)?;
            match a {
                Comp::Return(v) => {
                    let mut sub = BTreeMap::new();
                    sub.insert(*x, v);
                    let k2 = subst(k, &sub, cx);
                    normalize_go(&k2, cx, steps)
                }
                other => Some(Comp::Bind(Box::new(other), *x, k.clone())),
            }
        }
        Comp::Force(Value::Thunk(inner)) => normalize_go(inner, cx, steps),
        Comp::App(head, args) => {
            let head = normalize_go(head, cx, steps)?;
            match &head {
                Comp::Lam(ps, body) if ps.len() == args.len() => {
                    let sub: BTreeMap<Sym, Value> =
                        ps.iter().copied().zip(args.iter().cloned()).collect();
                    let b = subst(body, &sub, cx);
                    normalize_go(&b, cx, steps)
                }
                _ => Some(Comp::App(Box::new(head), args.clone())),
            }
        }
        Comp::If(Value::Bool(b), t, e) => {
            let branch = if *b { t } else { e };
            normalize_go(branch, cx, steps)
        }
        Comp::Case(scrut, arms) => {
            if let Value::Ctor(cn, _, fields) = scrut {
                for (p, b) in arms {
                    if let CorePat::Ctor(pc, bs) = p {
                        if pc == cn && bs.len() == fields.len() {
                            let mut sub = BTreeMap::new();
                            for (b, f) in bs.iter().zip(fields) {
                                if let Some(name) = b {
                                    sub.insert(*name, f.clone());
                                }
                            }
                            let body = subst(b, &sub, cx);
                            return normalize_go(&body, cx, steps);
                        }
                    }
                }
            }
            Some(c.clone())
        }
        _ => Some(c.clone()),
    }
}

// --- join emission --------------------------------------------------------------

// One advancing stream position: the fresh variable abstracting it, its path into
// the pipeline tree, and its initial (seed) value.
struct StreamParam {
    var: Sym,
    path: Vec<usize>,
    init: Value,
}

// Anti-unify the seed pipeline against its one-step tail, allocate join parameters
// for the differing (advancing) positions and the changing accumulators, drive the
// pipeline symbolically, and residualize into one fresh top-level join function.
// Returns the redirected call `Call(join, initialargs)`, or `None` to not fuse.
fn build_join(consumer: &Consumer, seed: &StreamExpr, cx: &mut Cx<'_>) -> Option<Comp> {
    // Abstract the scalar (non-closure) arguments to fresh variables, so the
    // producer's advance is driven symbolically (`x + 1`, not a folded literal).
    let (sym_seed, init) = abstract_stream(seed, cx);
    let mut budget = UNFOLD_BUDGET;
    let step = drive(&sym_seed, consumer.ctors, cx, &mut budget)?;
    if step_size(&step) > SIZE_BUDGET {
        return None;
    }
    // The one-step tail (identical across every yielding/skipping leaf): the knot.
    let tail = collect_tail(&step)?;
    // Classify each abstracted position: a differing one advances (a join
    // parameter), a coincident one is invariant (baked back to its seed value).
    let mut params: Vec<StreamParam> = Vec::new();
    let mut bakes: BTreeMap<Sym, Value> = BTreeMap::new();
    classify(
        &sym_seed,
        &tail,
        &init,
        &mut Vec::new(),
        &mut params,
        &mut bakes,
    )?;
    let join = Sym::new(&names::fused_join(cx.joins));
    let stream_paths: Vec<Vec<usize>> = params.iter().map(|p| p.path.clone()).collect();
    let body0 = {
        let mut r = Res {
            consumer,
            join,
            stream_paths: &stream_paths,
            cx,
        };
        r.residual(&step)?
    };
    // Bake invariant abstracted positions to their seed values.
    let body = subst(&body0, &bakes, cx);
    // Join parameters: advancing stream positions first (deterministic first-
    // occurrence order), then the consumer's accumulators.
    let mut jparams: Vec<Sym> = params.iter().map(|p| p.var).collect();
    jparams.extend(consumer.acc_params.iter().copied());
    // Scope safety: the residual must close over nothing but the join parameters. A
    // leaked local (the most-specific-generalization scope trap) aborts the seed.
    if !join_is_closed(&body, &jparams) {
        return None;
    }
    cx.emitted.push(CoreFn {
        name: join,
        params: jparams,
        dict_arity: 0,
        body,
    });
    cx.joins += 1;
    // The redirected initial call: seed values for the advancing positions, then the
    // accumulators' seed values.
    let mut initargs: Vec<Value> = params.iter().map(|p| p.init.clone()).collect();
    initargs.extend(consumer.accs.iter().map(|a| a.seed.clone()));
    Some(Comp::Call(join, initargs))
}

// Replace every scalar (non-thunk) value argument in the pipeline with a fresh
// variable, recording its seed value, in a fixed pre-order traversal (so parameter
// naming and order are byte-stable). Thunk arguments (mappers/predicates/fold
// functions) are left concrete so their applications inline during driving.
fn abstract_stream(s: &StreamExpr, cx: &mut Cx<'_>) -> (StreamExpr, BTreeMap<Sym, Value>) {
    let mut init = BTreeMap::new();
    let out = abstract_go(s, &mut init, cx);
    (out, init)
}

fn abstract_go(s: &StreamExpr, init: &mut BTreeMap<Sym, Value>, cx: &mut Cx<'_>) -> StreamExpr {
    let args = s
        .args
        .iter()
        .map(|a| match a {
            Arg::Val(Value::Thunk(t)) => Arg::Val(Value::Thunk(t.clone())),
            Arg::Val(v) => {
                let f = rename::next(&mut cx.fresh, FRESH_FUSE);
                init.insert(f, v.clone());
                Arg::Val(Value::Var(f))
            }
            Arg::Stream(inner) => Arg::Stream(Box::new(abstract_go(inner, init, cx))),
        })
        .collect();
    StreamExpr { comb: s.comb, args }
}

// Walk the abstracted seed and its one-step tail in parallel, sorting each
// abstracted position into an advancing parameter or a baked invariant.
fn classify(
    sym: &StreamExpr,
    tail: &StreamExpr,
    init: &BTreeMap<Sym, Value>,
    path: &mut Vec<usize>,
    params: &mut Vec<StreamParam>,
    bakes: &mut BTreeMap<Sym, Value>,
) -> Option<()> {
    if sym.comb != tail.comb || sym.args.len() != tail.args.len() {
        return None;
    }
    for (j, (sa, ta)) in sym.args.iter().zip(&tail.args).enumerate() {
        path.push(j);
        match (sa, ta) {
            (Arg::Val(Value::Var(fv)), Arg::Val(tv)) if init.contains_key(fv) => {
                // Invariant exactly when the tail threads the same variable through.
                if matches!(tv, Value::Var(w) if w == fv) {
                    bakes.insert(*fv, init[fv].clone());
                } else {
                    params.push(StreamParam {
                        var: *fv,
                        path: path.clone(),
                        init: init[fv].clone(),
                    });
                }
            }
            // A closure argument (mapper/predicate/fold function) is threaded
            // unchanged; alpha-renaming of its binder is irrelevant, so ignore it. A
            // non-closure non-abstracted value must not change.
            (Arg::Val(Value::Thunk(_)), Arg::Val(Value::Thunk(_))) => {}
            (Arg::Val(sv), Arg::Val(tv)) => {
                if !value_eq(sv, tv) {
                    return None;
                }
            }
            (Arg::Stream(si), Arg::Stream(ti)) => classify(si, ti, init, path, params, bakes)?,
            _ => return None,
        }
        path.pop();
    }
    Some(())
}

// Collect the one-step tail shared by every yielding/skipping leaf; `None` if the
// leaves disagree (an unexpected non-uniform advance) or the pipeline never
// recurses.
fn collect_tail(step: &Step) -> Option<StreamExpr> {
    let mut tails = Vec::new();
    gather_tails(step, &mut tails);
    let first: StreamExpr = (*tails.first()?).clone();
    if tails.iter().all(|t| stream_eq(t, &first)) {
        Some(first)
    } else {
        None
    }
}

fn gather_tails<'a>(step: &'a Step, out: &mut Vec<&'a StreamExpr>) {
    match step {
        Step::Done => {}
        Step::Yield { next, .. } | Step::Skip { next } => out.push(next),
        Step::Branch { then, els, .. } => {
            gather_tails(then, out);
            gather_tails(els, out);
        }
        Step::Let { body, .. } => gather_tails(body, out),
    }
}

// The residualizer: turns a driven `Step` tree into the join function body,
// emitting the consumer's per-element action at each yield and a self-call at every
// leaf.
struct Res<'a, 'b> {
    consumer: &'a Consumer,
    join: Sym,
    stream_paths: &'a [Vec<usize>],
    cx: &'a mut Cx<'b>,
}

impl Res<'_, '_> {
    fn residual(&mut self, step: &Step) -> Option<Comp> {
        match step {
            Step::Done => Some(subst(
                &self.consumer.done_body,
                &self.consumer.baked,
                self.cx,
            )),
            Step::Skip { next } => {
                let mut args = self.stream_rec_args(next)?;
                args.extend(self.consumer.acc_params.iter().map(|p| Value::Var(*p)));
                Some(Comp::Call(self.join, args))
            }
            Step::Yield { head, next } => {
                let mut rec_args = self.stream_rec_args(next)?;
                rec_args.extend(self.consumer.accs.iter().map(|a| a.advance.clone()));
                let call = Comp::Call(self.join, rec_args);
                let grafted = graft_return(&self.consumer.step_body, call)?;
                // Substitute the element and baked closures uniformly, then inline
                // the fold-function application the graft exposed.
                let mut sub = self.consumer.baked.clone();
                sub.insert(self.consumer.elem, head.clone());
                let done = subst(&grafted, &sub, self.cx);
                normalize(&done, self.cx)
            }
            Step::Branch { cond, then, els } => {
                let t = self.residual(then)?;
                let e = self.residual(els)?;
                Some(Comp::If(cond.clone(), Box::new(t), Box::new(e)))
            }
            Step::Let { var, comp, body } => {
                let b = self.residual(body)?;
                Some(Comp::Bind(Box::new(comp.clone()), *var, Box::new(b)))
            }
        }
    }

    // The advancing arguments for a recursive call: each stream parameter read from
    // the leaf's tail pipeline at its path.
    fn stream_rec_args(&self, next: &StreamExpr) -> Option<Vec<Value>> {
        self.stream_paths
            .iter()
            .map(|p| read_at_path(next, p))
            .collect()
    }
}

// Replace the trailing `Return(Unit)` marker (the stripped self-call) with `repl`.
fn graft_return(body: &Comp, repl: Comp) -> Option<Comp> {
    match body {
        Comp::Return(Value::Unit) => Some(repl),
        Comp::Bind(a, x, k) => Some(Comp::Bind(a.clone(), *x, Box::new(graft_return(k, repl)?))),
        _ => None,
    }
}

// Read the value at `path` (a sequence of argument indices descending through
// stream arguments, the last picking a value argument).
fn read_at_path(se: &StreamExpr, path: &[usize]) -> Option<Value> {
    let (last, rest) = path.split_last()?;
    let mut cur = se;
    for &i in rest {
        match cur.args.get(i)? {
            Arg::Stream(inner) => cur = inner,
            Arg::Val(_) => return None,
        }
    }
    match cur.args.get(*last)? {
        Arg::Val(v) => Some(v.clone()),
        Arg::Stream(_) => None,
    }
}

fn step_size(step: &Step) -> usize {
    match step {
        Step::Done | Step::Yield { .. } | Step::Skip { .. } => 1,
        Step::Branch { then, els, .. } => 1 + step_size(then) + step_size(els),
        Step::Let { body, .. } => 1 + step_size(body),
    }
}

// Structural equality of two pipeline tails, ignoring closure (thunk) arguments:
// mappers/predicates/fold functions are threaded unchanged, so an alpha-rename of a
// baked closure's binder must not make two otherwise-identical tails disagree.
fn stream_eq(a: &StreamExpr, b: &StreamExpr) -> bool {
    a.comb == b.comb
        && a.args.len() == b.args.len()
        && a.args.iter().zip(&b.args).all(|(x, y)| match (x, y) {
            (Arg::Stream(xi), Arg::Stream(yi)) => stream_eq(xi, yi),
            (Arg::Val(Value::Thunk(_)), Arg::Val(Value::Thunk(_))) => true,
            (Arg::Val(xv), Arg::Val(yv)) => value_eq(xv, yv),
            _ => false,
        })
}

fn value_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Float(x), Value::Float(y)) => x.to_bits() == y.to_bits(),
        (Value::Ctor(xn, xt, xs), Value::Ctor(yn, yt, ys)) => {
            xn == yn
                && xt == yt
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| value_eq(x, y))
        }
        (Value::Tuple(xs), Value::Tuple(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| value_eq(x, y))
        }
        _ => a == b,
    }
}

// The scope-safety gate on an emitted join: its body may close over nothing but
// its own parameters (top-level names and literals are not free variables). A
// violation means the most-specific generalization proposed a hole under a
// binder introduced during driving, the classic scope trap.
fn join_is_closed(body: &Comp, jparams: &[Sym]) -> bool {
    fv::comp(body).iter().all(|v| jparams.contains(v))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Defense-in-depth guard, tested directly because no curated pipeline can
    // reach it: a stream parameter's init is always a seed-level value in scope
    // at the call site, and every tail-advance value residualized into a join
    // body references only the abstracted stream variables (which become join
    // parameters) plus top-level functions and literals, never a binder
    // introduced during driving. The guard exists so that if a future combinator
    // shape breaks that invariant, the seed silently degrades to not-fusing
    // instead of emitting an open join (a miscompile).
    #[test]
    fn scope_guard_refuses_a_leaked_local() {
        let p = Sym::new("p0");
        let leaked = Sym::new("leaked");
        let closed = Comp::Return(Value::Var(p));
        assert!(join_is_closed(&closed, &[p]));
        let open = Comp::Return(Value::Var(leaked));
        assert!(!join_is_closed(&open, &[p]));
    }

    #[test]
    fn stream_equality_compares_float_bits() {
        let comb = Sym::new("producer");
        let a = StreamExpr {
            comb,
            args: vec![Arg::Val(Value::Float(0.0))],
        };
        let b = StreamExpr {
            comb,
            args: vec![Arg::Val(Value::Float(-0.0))],
        };
        assert!(!stream_eq(&a, &b));
    }

    #[test]
    fn classify_rejects_changed_non_abstracted_float_bits() {
        let comb = Sym::new("producer");
        let sym = StreamExpr {
            comb,
            args: vec![Arg::Val(Value::Float(0.0))],
        };
        let tail = StreamExpr {
            comb,
            args: vec![Arg::Val(Value::Float(-0.0))],
        };
        assert!(classify(
            &sym,
            &tail,
            &BTreeMap::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut BTreeMap::new(),
        )
        .is_none());
    }

    // Discovery starts at `a`: the old optimistic recursion breaker finalized
    // `b` as pure while `a` was provisionally true, then found `a`'s effect and
    // left the stale `b = true` memo behind. Both members must share the SCC's
    // impure verdict.
    #[test]
    fn mutual_recursion_cannot_hide_a_sibling_effect() {
        let a = Sym::new("a");
        let b = Sym::new("b");
        let functions = [
            CoreFn {
                name: a,
                params: Vec::new(),
                body: Comp::Bind(
                    Box::new(Comp::Call(b, Vec::new())),
                    Sym::new("from_b"),
                    Box::new(Comp::Error(Value::Int(0))),
                ),
                dict_arity: 0,
            },
            CoreFn {
                name: b,
                params: Vec::new(),
                body: Comp::Call(a, Vec::new()),
                dict_arity: 0,
            },
        ];
        let mut cx = Cx {
            fns: functions.iter().map(|f| (f.name, f)).collect(),
            pure: BTreeMap::new(),
            fresh: 0,
            joins: 0,
            emitted: Vec::new(),
        };

        assert!(!fn_pure(a, &mut cx));
        assert_eq!(cx.pure.get(&a), Some(&false));
        assert_eq!(cx.pure.get(&b), Some(&false));
    }

    #[test]
    fn pure_mutual_recursion_keeps_one_pure_scc_verdict() {
        let a = Sym::new("a");
        let b = Sym::new("b");
        let functions = [
            CoreFn {
                name: a,
                params: Vec::new(),
                body: Comp::Call(b, Vec::new()),
                dict_arity: 0,
            },
            CoreFn {
                name: b,
                params: Vec::new(),
                body: Comp::Call(a, Vec::new()),
                dict_arity: 0,
            },
        ];
        let mut cx = Cx {
            fns: functions.iter().map(|f| (f.name, f)).collect(),
            pure: BTreeMap::new(),
            fresh: 0,
            joins: 0,
            emitted: Vec::new(),
        };

        assert!(fn_pure(a, &mut cx));
        assert_eq!(cx.pure.get(&a), Some(&true));
        assert_eq!(cx.pure.get(&b), Some(&true));
    }
}
