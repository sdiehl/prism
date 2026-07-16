//! Whole-program stream fusion for typed Core (pre-lowering, O2 and forced
//! Fuse).
//!
//! Mirrors [`super::super::opt::fuse::fuse_counted`] rule-for-rule: recognize a
//! fusion seed (a self-recursive fold-shaped consumer applied to a pipeline of
//! known step-shaped combinators), drive one symbolic production step through
//! the pipeline (case-of-case cancelling every intermediate `Step` cell),
//! anti-unify the seed against its one-step tail to pick the advancing join
//! parameters, and residualize the knot into one fresh top-level join function,
//! redirecting the seed call. Every misfire (unrecognized shape, effectful
//! step, budget overrun, leaked local) degrades to not fusing, and the fresh
//! and join counters advance exactly as the legacy pass advances them, so the
//! erased output is byte-identical.
//!
//! The typed-specific steps are:
//! - Witness instantiation before inlining: a combinator or consumer body is
//!   instantiated at the call site's explicit scheme arguments (a pure type
//!   substitution that never touches term structure), so every driven piece
//!   carries concrete witnesses.
//! - Representation transparency: shape recognition peels
//!   [`TypedValueKind::Reinterpret`], [`TypedValueKind::LoweredRepr`], and
//!   [`TypedValueKind::NewtypeRepr`] wrappers, matching exactly what erasure
//!   exposes, while rewrites carry the original wrapped values forward
//!   unchanged.
//! - Constructed nodes carry verified sigs: rebuilt `Bind`/`If` nodes take the
//!   verifier's own sig-construction rules (result from the continuation, row
//!   from the canonical row union), and the join function's signature is the
//!   fully instantiated seed call-site signature, so the emitted loop verifies
//!   before erasure.

use std::collections::{BTreeMap, BTreeSet};

use crate::names::{self, FRESH_FUSE};
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;

use super::inline::calls_in;
use super::specialize_support::{
    free_comp_vars, next_fresh, substitute_terms, substitute_witnesses, Rewrite,
};
use super::verify::{substitute_core_type, union_rows};
use super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreType, TypedBinder, TypedComp, TypedCompKind,
    TypedCore, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind,
};

// A seed whose symbolic driving takes more than this many reduction steps aborts
// to not-fusing. Matches the legacy budget exactly.
const UNFOLD_BUDGET: u32 = 4000;
// A driven `Step` tree larger than this many nodes aborts to not-fusing.
// Matches the legacy budget exactly.
const SIZE_BUDGET: usize = 20_000;

/// Rewrite counts for typed stream fusion.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct FuseStats {
    ticks: u64,
}

impl FuseStats {
    /// Seeds fused (joins emitted).
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// The two `Step` constructors of the sequence type in play, learned from the
/// consumer's match rather than hard-coded: `done` is the nullary (empty)
/// constructor, `more` the binary (head, tail) one.
#[derive(Clone, Copy)]
struct StepCtors {
    done: Sym,
    more: Sym,
}

/// A pull-sequence pipeline as a tree: a combinator applied to its arguments,
/// with the single stream-typed argument recursively a nested pipeline. The
/// explicit instantiation from the resolved call travels with the node so a
/// rebuilt tail call keeps its witnesses.
#[derive(Clone, Debug)]
struct StreamExpr {
    comb: Sym,
    instantiation: Vec<CoreInstantiation>,
    args: Vec<Arg>,
}

#[derive(Clone, Debug)]
enum Arg {
    /// An ordinary value argument (a bound, a mapper/predicate thunk, a count).
    Val(TypedValue),
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

/// One compiled match arm: a pattern and its body (the shape
/// [`TypedCompKind::Case`] carries).
type Arm = (TypedPattern, TypedComp);

/// One symbolic production step of a driven pipeline: the shape of
/// `force(pipe)(())` after the intermediate `Step` cells have been cancelled
/// against the consumer's match.
enum Step {
    /// The pipeline is exhausted (every stage reached the empty constructor).
    Done,
    /// The pipeline yields `head`, and its tail is `next`.
    Yield { head: TypedValue, next: StreamExpr },
    /// A stage (a filter) consumed an element without yielding; continue at
    /// `next` without advancing the consumer.
    Skip { next: StreamExpr },
    /// A guard from the producer or a filtering stage.
    Branch {
        cond: TypedValue,
        then: Box<Self>,
        els: Box<Self>,
    },
    /// A pure head computation (a mapper application reduced to a
    /// `Prim`/`Call`) scoped over the rest of the step.
    Let {
        binder: TypedBinder,
        comp: Box<TypedComp>,
        body: Box<Self>,
    },
}

/// The context threaded through recognition and driving: the program's
/// functions by name, a purity memo, and the deterministic fresh-name and join
/// counters.
struct Cx {
    fns: BTreeMap<Sym, TypedCoreFn>,
    pure: BTreeMap<Sym, bool>,
    fresh: u32,
    joins: u32,
    /// Join functions produced this run, appended to the program at the end.
    emitted: Vec<TypedCoreFn>,
}

/// Fuse every recognized pull-sequence pipeline, preserving every witness.
///
/// A no-op when no seed is recognized; every unrecognized or over-budget
/// configuration is left untouched (degrade to not fusing, never a partial
/// rewrite).
pub(crate) fn fuse<P>(core: TypedCore<P>) -> (TypedCore<P>, FuseStats) {
    let mut cx = Cx {
        fns: core
            .fns
            .iter()
            .map(|function| (function.name, function.clone()))
            .collect(),
        pure: BTreeMap::new(),
        fresh: 0,
        joins: 0,
        emitted: Vec::new(),
    };
    // Rewrite each function body, redirecting any recognized seed call to a
    // fresh join. Bodies are processed in program order and the join counter is
    // shared, so names are deterministic. When a body actually fused, its
    // now-dead upstream pipeline is removed by dead-let elimination, so the
    // fused loop stands alone instead of running beside a discarded allocation.
    let mut fns: Vec<TypedCoreFn> = core
        .fns
        .into_iter()
        .map(|function| {
            let before = cx.joins;
            let mut body = rewrite_body(&function.body, &mut cx);
            if cx.joins > before {
                body = dead_let_elim(&body, &mut cx);
            }
            TypedCoreFn::new(
                function.name,
                function.params,
                body,
                function.sig,
                function.dict_arity,
            )
        })
        .collect();
    let ticks = u64::from(cx.joins);
    fns.append(&mut cx.emitted);
    (TypedCore::new(fns), FuseStats { ticks })
}

// A value looked through any representation-only wrapper: those erase away
// transparently, so shape recognition must see the represented value. Rewrites
// keep the original (wrapped) value.
fn peel(value: &TypedValue) -> &TypedValue {
    match &value.kind {
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => peel(inner),
        _ => value,
    }
}

// The variable a value names once representation wrappers are peeled.
fn as_var(value: &TypedValue) -> Option<Sym> {
    match &peel(value).kind {
        TypedValueKind::Var { name, .. } => Some(*name),
        _ => None,
    }
}

fn is_unit(value: &TypedValue) -> bool {
    matches!(&peel(value).kind, TypedValueKind::Unit)
}

const fn unit_value() -> TypedValue {
    TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit)
}

fn binder_var(binder: &TypedBinder) -> TypedValue {
    TypedValue::new(
        binder.ty().clone(),
        TypedValueKind::Var {
            name: binder.name(),
            instantiation: Vec::new(),
        },
    )
}

// The verified `Bind`/`If` sig-construction rule unions the children's rows.
// Everything this pass rebuilds already passed the purity gate, whose rows are
// closed after instantiation, so the union cannot fail on verifiable input;
// the fallback merely keeps the pass total.
fn union_effects(left: &EffRow, right: &EffRow) -> EffRow {
    union_rows(left, right).unwrap_or_else(|_| right.clone())
}

// Walk `body`, replacing every recognized seed call with a call to a freshly
// emitted join function. Tracks the enclosing let-bindings so a seed's sequence
// argument (a `Var` bound upstream to a combinator call) can be resolved.
fn rewrite_body(body: &TypedComp, cx: &mut Cx) -> TypedComp {
    let mut env: BTreeMap<Sym, TypedComp> = BTreeMap::new();
    rewrite_in(body, &mut env, cx)
}

fn rewrite_in(c: &TypedComp, env: &mut BTreeMap<Sym, TypedComp>, cx: &mut Cx) -> TypedComp {
    match c.kind() {
        TypedCompKind::Bind(first, binder, rest) => {
            let first2 = rewrite_in(first, env, cx);
            // Record the binding so a later seed can resolve it to its
            // definition.
            env.insert(binder.name(), first.as_ref().clone());
            let rest2 = rewrite_in(rest, env, cx);
            env.remove(&binder.name());
            TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Bind(Box::new(first2), binder.clone(), Box::new(rest2)),
            )
        }
        TypedCompKind::Call { .. } => try_fuse_call(c, env, cx).unwrap_or_else(|| c.clone()),
        _ => descend_rewrite(c, env, cx),
    }
}

// Structural recursion for the non-seed-bearing cases, tracking no new bindings
// (only `Bind` introduces the let scope a seed needs).
fn descend_rewrite(c: &TypedComp, env: &mut BTreeMap<Sym, TypedComp>, cx: &mut Cx) -> TypedComp {
    struct R<'a> {
        env: &'a mut BTreeMap<Sym, TypedComp>,
        cx: &'a mut Cx,
    }
    impl Rewrite for R<'_> {
        type Ctx = ();
        fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
            match c.kind() {
                TypedCompKind::Bind(..) | TypedCompKind::Call { .. } => {
                    rewrite_in(c, self.env, self.cx)
                }
                _ => self.descend_comp(c, &()),
            }
        }
    }
    R { env, cx }.descend_comp(c, &())
}

// Try to recognize and fuse a seed call. Returns the redirected call (to a
// fresh join) on success, `None` to leave it untouched.
fn try_fuse_call(
    call: &TypedComp,
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
) -> Option<TypedComp> {
    let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = call.kind()
    else {
        return None;
    };
    let consumer = resolve_consumer(*callee, instantiation, args, call.sig(), cx)?;
    // The sequence the consumer folds, resolved from the seed's sequence
    // argument through the enclosing let-bindings into a pipeline tree.
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
/// parameter, matches the two `Step` constructors, and tail-recurses on the
/// cons tail. Wrapper consumers (`sum = fold(s, 0, add)`) are peeled to the
/// underlying fold, carrying the wrapper's fixed arguments.
struct Consumer {
    ctors: StepCtors,
    /// The sequence argument at the seed call site (before let-resolution).
    seq_arg: TypedValue,
    /// The accumulator arguments at the seed call site (non-sequence,
    /// non-closure state), paired with how each advances in the recursive call.
    accs: Vec<Acc>,
    /// The closure arguments baked into the fold (mappers/fold-functions), by
    /// the fold's parameter name, substituted into every body.
    baked: BTreeMap<Sym, TypedValue>,
    /// The empty-arm body (the fold's result when the sequence is exhausted),
    /// over the accumulator parameters.
    done_body: TypedComp,
    /// The cons-arm body up to (not including) the self-call: the per-element
    /// action computing the next accumulators. Binds the element variable
    /// `elem`.
    step_body: TypedComp,
    /// The element binder introduced by the cons pattern.
    elem: Sym,
    /// The fold's own accumulator parameters, in order, with call-site
    /// instantiated types (they become the trailing join parameters).
    acc_params: Vec<TypedBinder>,
    /// Every function name reachable in the consumer's driven region (for
    /// purity).
    fn_names: Vec<Sym>,
    /// The fully instantiated seed call-site signature: the join function's
    /// declared body signature and the redirected call's witness.
    call_sig: CompSig,
}

/// One accumulator: its seed value at the call site and its advance expression
/// (the corresponding self-call argument, over the parameters and the element).
struct Acc {
    seed: TypedValue,
    advance: TypedValue,
}

impl Consumer {
    fn pure(&self, cx: &mut Cx) -> bool {
        comp_pure(&self.done_body, cx)
            && comp_pure(&self.step_body, cx)
            && self.baked.values().all(|v| value_pure(v, cx))
            && self.fn_names.iter().all(|n| fn_pure(*n, cx))
    }
}

// Resolve the seed call head to a fold-shaped consumer, peeling wrapper
// functions (a body that is a single call to another consumer with the
// sequence threaded). The declared scheme is instantiated at the call site's
// explicit arguments before any analysis, so every extracted piece carries
// concrete witnesses; the term structure the legacy pass matches is untouched.
fn resolve_consumer(
    f: Sym,
    instantiation: &[CoreInstantiation],
    args: &[TypedValue],
    call_sig: &CompSig,
    cx: &mut Cx,
) -> Option<Consumer> {
    let def = cx.fns.get(&f)?.clone();
    if def.params.len() != args.len() {
        return None;
    }
    let quantifiers = def.sig.quantifiers().to_vec();
    let inst_body = substitute_witnesses(&def.body, &quantifiers, instantiation);
    let inst_params: Vec<TypedBinder> = def
        .params
        .iter()
        .map(|binder| {
            TypedBinder::new(
                binder.name(),
                substitute_core_type(binder.ty(), &quantifiers, instantiation),
            )
        })
        .collect();
    // A direct fold analyses the raw body (parameters intact, so its forcing
    // site names a parameter). A wrapper (`sum = fold(s, 0, add)`) needs the
    // arguments substituted to expose its single delegate call.
    if let Some(consumer) = fold_consumer(f, &inst_params, args, &inst_body, call_sig, cx) {
        return Some(consumer);
    }
    let sub: BTreeMap<Sym, TypedValue> = inst_params
        .iter()
        .map(TypedBinder::name)
        .zip(args.iter().cloned())
        .collect();
    let body = normalize(&subst(&inst_body, &sub, cx), cx)?;
    if let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = body.kind()
    {
        if *callee != f {
            return resolve_consumer(*callee, instantiation, args, call_sig, cx);
        }
    }
    None
}

// Match the canonical fold shape on the (copy-propagated) raw body and extract
// its driving pieces, filling accumulator seeds from the seed call `args`.
// Returns `None` if the body is not a fold over one of its parameters.
fn fold_consumer(
    f: Sym,
    params: &[TypedBinder],
    args: &[TypedValue],
    raw_body: &TypedComp,
    call_sig: &CompSig,
    cx: &mut Cx,
) -> Option<Consumer> {
    // Copy-propagate the elaboration's `return x to t` aliases so the forcing
    // site, match, and self-call read structurally, then expect
    // `Bind(force(seq)(()), st, Case st arms)`.
    let body = copy_prop(raw_body, cx);
    let (seq, _st, arms) = match_force_case(&body)?;
    // `seq` must be one of the fold's own parameters (the sequence being
    // folded).
    let seq_idx = params.iter().position(|p| p.name() == seq)?;
    let (ctors, done_body, elem, tail, step_body) = match_step_arms(arms)?;
    // The self-call in the cons arm: `Call(f, [tail, adv...])`, tail in the seq
    // slot.
    let (callee, cargs) = tail_self_call(&step_body, f)?;
    if callee != f || cargs.len() != params.len() {
        return None;
    }
    if as_var(&cargs[seq_idx]) != Some(tail) {
        return None;
    }
    // Partition the non-sequence parameters into accumulators (advancing) and
    // baked closures (invariant). A parameter whose self-call argument is
    // itself and whose seed argument is a thunk is baked; otherwise it is an
    // accumulator.
    let mut accs = Vec::new();
    let mut baked = BTreeMap::new();
    let mut acc_params = Vec::new();
    for (i, p) in params.iter().enumerate() {
        if i == seq_idx {
            continue;
        }
        let advance = cargs[i].clone();
        let invariant = as_var(&advance) == Some(p.name());
        if invariant && matches!(&peel(&args[i]).kind, TypedValueKind::Thunk(_)) {
            baked.insert(p.name(), args[i].clone());
        } else {
            accs.push(Acc {
                seed: args[i].clone(),
                advance,
            });
            acc_params.push(p.clone());
        }
    }
    let mut fn_names = calls_in(&done_body);
    fn_names.extend(calls_in(&step_body));
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
        call_sig: call_sig.clone(),
    })
}

// Match `Bind(App(Force(Var seq), [Unit]), st, Case(Var st, arms))`.
fn match_force_case(body: &TypedComp) -> Option<(Sym, Sym, &[Arm])> {
    if let TypedCompKind::Bind(first, st, rest) = body.kind() {
        if let TypedCompKind::App {
            callee,
            instantiation: _,
            args,
        } = first.kind()
        {
            if let TypedCompKind::Force(head) = callee.kind() {
                if let Some(seq) = as_var(head) {
                    if args.len() == 1 && is_unit(&args[0]) {
                        if let TypedCompKind::Case(scrutinee, arms) = rest.kind() {
                            if as_var(scrutinee) == Some(st.name()) {
                                return Some((seq, st.name(), arms));
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

// Split the two-arm `Step` match into (ctors, done-body, elem, tail,
// cons-body).
fn match_step_arms(arms: &[Arm]) -> Option<(StepCtors, TypedComp, Sym, Sym, TypedComp)> {
    if arms.len() != 2 {
        return None;
    }
    let mut done: Option<(Sym, TypedComp)> = None;
    let mut more: Option<(Sym, Sym, Sym, TypedComp)> = None;
    for (pattern, body) in arms {
        match pattern {
            TypedPattern::Ctor { name, fields, .. } if fields.is_empty() => {
                done = Some((*name, body.clone()));
            }
            TypedPattern::Ctor { name, fields, .. } if fields.len() == 2 => {
                let head = fields[0].as_ref()?;
                let next = fields[1].as_ref()?;
                more = Some((*name, head.name(), next.name(), body.clone()));
            }
            _ => return None,
        }
    }
    let (dc, db) = done?;
    let (mc, elem, tail, mb) = more?;
    Some((StepCtors { done: dc, more: mc }, db, elem, tail, mb))
}

// The tail self-call reachable through the cons-arm's straight-line binds (the
// recursion is the last computation).
fn tail_self_call(body: &TypedComp, f: Sym) -> Option<(Sym, Vec<TypedValue>)> {
    match body.kind() {
        TypedCompKind::Call { callee, args, .. } if *callee == f => Some((*callee, args.clone())),
        TypedCompKind::Bind(_, _, rest) => tail_self_call(rest, f),
        _ => None,
    }
}

// Replace the tail self-call with a `Return(Unit)` marker: the cons-arm body
// then holds exactly the per-element action as a straight-line prefix, which
// the residualizer re-emits before the recursive join call. The marker's sig is
// a placeholder; `graft_return` replaces the node wholesale before the body
// reaches output, restoring the enclosing binds' stored sigs.
fn strip_self_call(body: &TypedComp, f: Sym) -> TypedComp {
    match body.kind() {
        TypedCompKind::Call { callee, .. } if *callee == f => TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
            TypedCompKind::Return(unit_value()),
        ),
        TypedCompKind::Bind(first, binder, rest) => TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Bind(
                first.clone(),
                binder.clone(),
                Box::new(strip_self_call(rest, f)),
            ),
        ),
        _ => body.clone(),
    }
}

// --- stream resolution ----------------------------------------------------------

// Resolve a sequence argument (a value, usually a `Var` bound upstream to a
// combinator call) into a pipeline tree. Producers bottom the recursion.
fn resolve_stream(
    seq: &TypedValue,
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
) -> Option<StreamExpr> {
    let v = as_var(seq)?;
    let def = env.get(&v)?.clone();
    resolve_stream_comp(&def, env, cx)
}

// Resolve a stream-valued computation to a pipeline tree. Elaboration nests a
// whole pipeline as one `Bind`-chain leading to the outermost call, so
// copy-propagate to inline the value aliases, flatten the chain into the
// resolution environment, and resolve the trailing call.
fn resolve_stream_comp(
    def: &TypedComp,
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
) -> Option<StreamExpr> {
    let def = copy_prop(def, cx);
    let mut local = env.clone();
    let mut cur = &def;
    while let TypedCompKind::Bind(first, binder, rest) = cur.kind() {
        local.insert(binder.name(), first.as_ref().clone());
        cur = rest;
    }
    match cur.kind() {
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } => stream_of_call(*callee, instantiation, args, &local, cx),
        TypedCompKind::Return(value) if as_var(value).is_some() => {
            resolve_stream(value, &local, cx)
        }
        _ => None,
    }
}

// Chase let-aliases (`x = Return v`) to a ground value: a literal or a thunk. A
// producer bound or a mapper/predicate closure reaches its definition this way,
// so it is baked into the join as a value rather than a reference to a
// caller-local.
fn resolve_value(v: &TypedValue, env: &BTreeMap<Sym, TypedComp>) -> TypedValue {
    if let Some(x) = as_var(v) {
        if let Some(TypedCompKind::Return(inner)) = env.get(&x).map(TypedComp::kind) {
            return resolve_value(inner, env);
        }
    }
    v.clone()
}

fn stream_of_call(
    comb: Sym,
    instantiation: &[CoreInstantiation],
    cargs: &[TypedValue],
    env: &BTreeMap<Sym, TypedComp>,
    cx: &mut Cx,
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
    Some(StreamExpr {
        comb,
        instantiation: instantiation.to_vec(),
        args,
    })
}

// The role of combinator `comb`: a producer (forces no parameter) or a
// transformer (forces exactly one). `None` when `comb` is unknown or forces
// more than one parameter (a binary combinator like `zip`), which this cut does
// not fuse.
fn stream_role(comb: Sym, cx: &mut Cx) -> Option<Role> {
    let (params, body_src) = {
        let def = cx.fns.get(&comb)?;
        (
            def.params.iter().map(TypedBinder::name).collect::<Vec<_>>(),
            def.body.clone(),
        )
    };
    // Copy-propagate first: elaboration forces an alias (`return s to t; force
    // t`), so the raw body never names the parameter at the forcing site.
    let body = copy_prop(&body_src, cx);
    let forced = forced_params(&body, &params);
    match forced.len() {
        0 => Some(Role::Producer),
        1 => Some(Role::Transformer(forced[0])),
        _ => None,
    }
}

// The parameter indices that appear as `force(param)(())` anywhere in `body`,
// in first-occurrence order.
fn forced_params(body: &TypedComp, params: &[Sym]) -> Vec<usize> {
    let mut hits = Vec::new();
    forced_comp(body, params, &mut hits);
    hits
}

fn forced_comp(c: &TypedComp, params: &[Sym], hits: &mut Vec<usize>) {
    if let TypedCompKind::App {
        callee,
        instantiation: _,
        args,
    } = c.kind()
    {
        if let TypedCompKind::Force(head) = callee.kind() {
            if args.len() == 1 && is_unit(&args[0]) {
                if let Some(name) = as_var(head) {
                    if let Some(i) = params.iter().position(|p| *p == name) {
                        if !hits.contains(&i) {
                            hits.push(i);
                        }
                    }
                }
            }
        }
    }
    match c.kind() {
        TypedCompKind::Return(v)
        | TypedCompKind::Force(v)
        | TypedCompKind::Error(v)
        | TypedCompKind::FloatBuiltin(_, v)
        | TypedCompKind::Neg(_, v)
        | TypedCompKind::UnboxedProject(v, _)
        | TypedCompKind::Dup(v)
        | TypedCompKind::Drop(v)
        | TypedCompKind::Reuse(_, v)
        | TypedCompKind::RefNew(v)
        | TypedCompKind::RefGet(v) => forced_value(v, params, hits),
        TypedCompKind::Prim(_, a, b)
        | TypedCompKind::RefSet(a, b)
        | TypedCompKind::InitAt(a, b) => {
            forced_value(a, params, hits);
            forced_value(b, params, hits);
        }
        TypedCompKind::Bind(a, _, k) => {
            forced_comp(a, params, hits);
            forced_comp(k, params, hits);
        }
        TypedCompKind::Lam(_, b) | TypedCompKind::Mask(_, b) => forced_comp(b, params, hits),
        TypedCompKind::App { callee, args, .. } => {
            forced_comp(callee, params, hits);
            for a in args {
                forced_value(a, params, hits);
            }
        }
        TypedCompKind::If(v, t, e) => {
            forced_value(v, params, hits);
            forced_comp(t, params, hits);
            forced_comp(e, params, hits);
        }
        TypedCompKind::Call { args, .. }
        | TypedCompKind::Io(_, args)
        | TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. } => {
            for a in args {
                forced_value(a, params, hits);
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            forced_value(scrutinee, params, hits);
            for (_, b) in arms {
                forced_comp(b, params, hits);
            }
        }
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            forced_comp(body, params, hits);
            if let Some(rb) = return_body {
                forced_comp(rb, params, hits);
            }
            for arm in ops.arms() {
                forced_comp(arm.body(), params, hits);
            }
        }
        TypedCompKind::WithReuse { freed, body, .. } => {
            forced_value(freed, params, hits);
            forced_comp(body, params, hits);
        }
    }
}

fn forced_value(v: &TypedValue, params: &[Sym], hits: &mut Vec<usize>) {
    match &v.kind {
        TypedValueKind::Thunk(body) => forced_comp(body, params, hits),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => forced_value(inner, params, hits),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for f in fields {
                forced_value(f, params, hits);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, f) in fields {
                forced_value(f, params, hits);
            }
        }
        _ => {}
    }
}

// --- purity ---------------------------------------------------------------------

fn stream_pure(s: &StreamExpr, cx: &mut Cx) -> bool {
    fn_pure(s.comb, cx)
        && s.args.iter().all(|a| match a {
            Arg::Val(v) => value_pure(v, cx),
            Arg::Stream(inner) => stream_pure(inner, cx),
        })
}

// A function is fusion-pure when no path through the call graph from its body
// reaches a direct effect node or an unknown call head. This is a reachability
// property, so an optimistic seed is not a sound recursion breaker: one member
// of a mutually recursive component can otherwise be finalized against a
// sibling's provisional `true` verdict. Condense the reachable graph into
// strongly connected components and commit one shared verdict only after the
// whole component has resolved.
fn fn_pure(name: Sym, cx: &mut Cx) -> bool {
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

// One function body's local contribution to the call-graph fixpoint.
struct BodyInfo {
    self_bad: bool,
    callees: Vec<Sym>,
}

fn body_info(def: &TypedCoreFn, fns: &BTreeMap<Sym, TypedCoreFn>) -> BodyInfo {
    let mut info = BodyInfo {
        self_bad: comp_has_direct_effect(def.body()),
        callees: Vec::new(),
    };
    for callee in calls_in(def.body()) {
        if fns.contains_key(&callee) {
            if !info.callees.contains(&callee) {
                info.callees.push(callee);
            }
        } else {
            info.self_bad = true;
        }
    }
    info
}

// Direct effects include effects suspended inside values. Calls themselves are
// handled as graph edges by `body_info`, so recursion cannot influence this
// local predicate.
fn comp_has_direct_effect(c: &TypedComp) -> bool {
    match c.kind() {
        TypedCompKind::Io(..)
        | TypedCompKind::Do { .. }
        | TypedCompKind::Handle { .. }
        | TypedCompKind::Mask(..)
        | TypedCompKind::Error(_)
        | TypedCompKind::RefNew(_)
        | TypedCompKind::RefGet(_)
        | TypedCompKind::RefSet(..) => true,
        TypedCompKind::Call { args, .. } | TypedCompKind::StrBuiltin { args, .. } => {
            args.iter().any(value_has_direct_effect)
        }
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::Reuse(_, value) => value_has_direct_effect(value),
        TypedCompKind::Bind(first, _, rest) => {
            comp_has_direct_effect(first) || comp_has_direct_effect(rest)
        }
        TypedCompKind::Lam(_, body) => comp_has_direct_effect(body),
        TypedCompKind::App { callee, args, .. } => {
            comp_has_direct_effect(callee) || args.iter().any(value_has_direct_effect)
        }
        TypedCompKind::If(value, yes, no) => {
            value_has_direct_effect(value)
                || comp_has_direct_effect(yes)
                || comp_has_direct_effect(no)
        }
        TypedCompKind::Prim(_, lhs, rhs) | TypedCompKind::InitAt(lhs, rhs) => {
            value_has_direct_effect(lhs) || value_has_direct_effect(rhs)
        }
        TypedCompKind::Case(scrutinee, arms) => {
            value_has_direct_effect(scrutinee)
                || arms.iter().any(|(_, body)| comp_has_direct_effect(body))
        }
        TypedCompKind::WithReuse { freed, body, .. } => {
            value_has_direct_effect(freed) || comp_has_direct_effect(body)
        }
    }
}

fn value_has_direct_effect(value: &TypedValue) -> bool {
    match &value.kind {
        TypedValueKind::Thunk(body) => comp_has_direct_effect(body),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => value_has_direct_effect(inner),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => fields.iter().any(value_has_direct_effect),
        TypedValueKind::UnboxedRecord(fields) => fields
            .iter()
            .any(|(_, field)| value_has_direct_effect(field)),
        TypedValueKind::Var { .. }
        | TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => false,
    }
}

// Scratch state for one Tarjan walk. Every discovered node is finalized into
// `cx.pure` before `fn_pure` returns; no provisional verdict escapes the walk.
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
    fn connect(&mut self, name: Sym, cx: &mut Cx) {
        let info = cx.fns.get(&name).map_or(
            BodyInfo {
                self_bad: true,
                callees: Vec::new(),
            },
            |def| body_info(def, &cx.fns),
        );
        let index = self.counter;
        self.counter += 1;
        self.index.insert(name, index);
        self.low.insert(name, index);
        self.stack.push(name);
        self.on_stack.insert(name);

        for &callee in &info.callees {
            if cx.pure.contains_key(&callee) {
                // A finalized successor: consult its verdict at component pop.
            } else if self.on_stack.contains(&callee) {
                self.low
                    .insert(name, self.low[&name].min(self.index[&callee]));
            } else {
                self.connect(callee, cx);
                self.low
                    .insert(name, self.low[&name].min(self.low[&callee]));
            }
        }
        self.info.insert(name, info);

        if self.low[&name] == self.index[&name] {
            let mut component = Vec::new();
            loop {
                let member = self.stack.pop().expect("purity walk stack underflow");
                self.on_stack.remove(&member);
                component.push(member);
                if member == name {
                    break;
                }
            }
            let members: BTreeSet<Sym> = component.iter().copied().collect();
            let pure = component.iter().all(|member| {
                let info = &self.info[member];
                !info.self_bad
                    && info.callees.iter().all(|callee| {
                        members.contains(callee) || cx.pure.get(callee) == Some(&true)
                    })
            });
            for member in component {
                cx.pure.insert(member, pure);
            }
        }
    }
}

fn comp_pure(c: &TypedComp, cx: &mut Cx) -> bool {
    match c.kind() {
        TypedCompKind::Io(..)
        | TypedCompKind::Do { .. }
        | TypedCompKind::Handle { .. }
        | TypedCompKind::Mask(..)
        | TypedCompKind::Error(_)
        | TypedCompKind::RefNew(_)
        | TypedCompKind::RefGet(_)
        | TypedCompKind::RefSet(..) => false,
        TypedCompKind::Call { callee, args, .. } => {
            fn_pure(*callee, cx) && args.iter().all(|a| value_thunks_pure(a, cx))
        }
        TypedCompKind::Return(v)
        | TypedCompKind::Force(v)
        | TypedCompKind::FloatBuiltin(_, v)
        | TypedCompKind::Neg(_, v)
        | TypedCompKind::UnboxedProject(v, _)
        | TypedCompKind::Dup(v)
        | TypedCompKind::Drop(v)
        | TypedCompKind::Reuse(_, v) => value_thunks_pure(v, cx),
        TypedCompKind::Bind(a, _, k) => comp_pure(a, cx) && comp_pure(k, cx),
        TypedCompKind::Lam(_, b) => comp_pure(b, cx),
        TypedCompKind::App { callee, args, .. } => {
            comp_pure(callee, cx) && args.iter().all(|a| value_thunks_pure(a, cx))
        }
        TypedCompKind::If(v, t, e) => {
            value_thunks_pure(v, cx) && comp_pure(t, cx) && comp_pure(e, cx)
        }
        // `init_at` writes a constructor into a cell no one else can observe
        // yet, exactly as a plain constructor writes into fresh `prism_alloc`
        // memory. The legacy pass counts both pure; only the allocator differs.
        TypedCompKind::Prim(_, a, b) | TypedCompKind::InitAt(a, b) => {
            value_thunks_pure(a, cx) && value_thunks_pure(b, cx)
        }
        TypedCompKind::Case(scrutinee, arms) => {
            value_thunks_pure(scrutinee, cx) && arms.iter().all(|(_, b)| comp_pure(b, cx))
        }
        TypedCompKind::StrBuiltin { args, .. } => args.iter().all(|a| value_thunks_pure(a, cx)),
        TypedCompKind::WithReuse { freed, body, .. } => {
            value_thunks_pure(freed, cx) && comp_pure(body, cx)
        }
    }
}

// Every thunk anywhere inside `v` has a pure body (the deep descent the legacy
// visitor performs inside computations).
fn value_thunks_pure(v: &TypedValue, cx: &mut Cx) -> bool {
    match &v.kind {
        TypedValueKind::Thunk(body) => comp_pure(body, cx),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => value_thunks_pure(inner, cx),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => fields.iter().all(|f| value_thunks_pure(f, cx)),
        TypedValueKind::UnboxedRecord(fields) => {
            fields.iter().all(|(_, f)| value_thunks_pure(f, cx))
        }
        _ => true,
    }
}

// The shallow value gate the legacy pass applies to baked closures and pipeline
// value arguments: a thunk's body must be pure; anything else passes.
fn value_pure(v: &TypedValue, cx: &mut Cx) -> bool {
    match &peel(v).kind {
        TypedValueKind::Thunk(body) => comp_pure(body, cx),
        _ => true,
    }
}

// --- driving --------------------------------------------------------------------

// Drive one production step of pipeline `s`, with the stream-state variables
// kept symbolic. Returns the fused `Step` tree, or `None` on any unrecognized
// shape or budget overrun.
fn drive(s: &StreamExpr, ctors: StepCtors, cx: &mut Cx, budget: &mut u32) -> Option<Step> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let def = cx.fns.get(&s.comb)?.clone();
    match stream_role(s.comb, cx)? {
        Role::Producer => drive_producer(&def, s, ctors, cx),
        Role::Transformer(i) => drive_transformer(&def, s, i, ctors, cx, budget),
    }
}

// A producer: inline its step body with the (all-value) arguments and read the
// `Step` constructors it builds directly.
fn drive_producer(
    def: &TypedCoreFn,
    s: &StreamExpr,
    ctors: StepCtors,
    cx: &mut Cx,
) -> Option<Step> {
    let sub = bind_args(def, s)?;
    let step = step_body_of(def, &s.instantiation, &sub, cx)?;
    reduce_leaf(&step, None, ctors, cx)
}

// A transformer: drive its inner stream, then push its match through the inner
// step's leaves (case-of-case), fusing away the intermediate constructor.
fn drive_transformer(
    def: &TypedCoreFn,
    s: &StreamExpr,
    idx: usize,
    ctors: StepCtors,
    cx: &mut Cx,
    budget: &mut u32,
) -> Option<Step> {
    let Arg::Stream(inner) = &s.args[idx] else {
        return None;
    };
    let inner_step = drive(inner, ctors, cx, budget)?;
    // Inline the transformer's step body with its value arguments bound; the
    // stream parameter is left free (its forcing site is where the inner step
    // plugs in).
    let sub = bind_value_args(def, s, idx);
    let step = step_body_of(def, &s.instantiation, &sub, cx)?;
    // `step` is `Bind(force(seqparam)(()), st, Case st arms)`; compose.
    let (_st, arms) = force_case_of(&step, def.params()[idx].name())?;
    compose(&inner_step, &arms, s, idx, ctors, cx)
}

// Push the transformer's match `Case st arms` through the inner step's leaves.
fn compose(
    inner: &Step,
    arms: &[Arm],
    s: &StreamExpr,
    idx: usize,
    ctors: StepCtors,
    cx: &mut Cx,
) -> Option<Step> {
    match inner {
        Step::Done => arm_reduce(arms, ctors, &ArmInput::Done, cx),
        Step::Yield { head, next } => arm_reduce(arms, ctors, &ArmInput::More(head, next), cx),
        // The inner stage produced nothing this element: this stage also
        // produces nothing, advancing to itself over the inner tail.
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
        Step::Let { binder, comp, body } => {
            let b = compose(body, arms, s, idx, ctors, cx)?;
            Some(Step::Let {
                binder: binder.clone(),
                comp: comp.clone(),
                body: Box::new(b),
            })
        }
    }
}

// What the inner step delivered to a transformer's match: the empty case, or a
// cons with a head value and a tail pipeline.
enum ArmInput<'a> {
    Done,
    More(&'a TypedValue, &'a StreamExpr),
}

// Select and reduce the transformer's matching arm for the inner step's
// outcome, then reduce that arm body to this stage's `Step`.
fn arm_reduce(arms: &[Arm], ctors: StepCtors, input: &ArmInput<'_>, cx: &mut Cx) -> Option<Step> {
    for (pattern, body) in arms {
        match (pattern, input) {
            (TypedPattern::Ctor { name, fields, .. }, ArmInput::Done)
                if *name == ctors.done && fields.is_empty() =>
            {
                return reduce_leaf(body, None, ctors, cx);
            }
            (TypedPattern::Ctor { name, fields, .. }, ArmInput::More(head, next))
                if *name == ctors.more =>
            {
                // Bind the arm's head/tail binders to the inner head and a
                // marker var standing for the inner tail pipeline.
                let head_binder = fields[0].as_ref()?;
                let tail_binder = fields[1].as_ref()?;
                let marker = next_fresh(&mut cx.fresh, FRESH_FUSE);
                let mut sub = BTreeMap::new();
                sub.insert(head_binder.name(), (*head).clone());
                sub.insert(
                    tail_binder.name(),
                    TypedValue::new(
                        tail_binder.ty().clone(),
                        TypedValueKind::Var {
                            name: marker,
                            instantiation: Vec::new(),
                        },
                    ),
                );
                let body = subst(body, &sub, cx);
                let tl = (marker, (*next).clone());
                return reduce_leaf(&body, Some(&tl), ctors, cx);
            }
            _ => {}
        }
    }
    None
}

// Reduce a leaf computation (a producer step body, or a transformer arm after
// its head is substituted) into this stage's `Step`. `tail`, when present,
// binds the marker variable standing for the inner tail pipeline, so an
// outgoing pipeline value resolves back to a `StreamExpr` instead of being
// emitted (and re-allocated) as a computation.
fn reduce_leaf(
    c: &TypedComp,
    tail: Option<&(Sym, StreamExpr)>,
    ctors: StepCtors,
    cx: &mut Cx,
) -> Option<Step> {
    let mut env: BTreeMap<Sym, StreamExpr> = BTreeMap::new();
    reduce_leaf_env(c, tail, ctors, &mut env, cx)
}

// The recursive worker: `env` maps the leaf's intermediate binders (producer
// self-tails and this stage's rebuilt tails) to their pipeline trees, so a
// constructed cons tail resolves to a `StreamExpr` rather than a live call.
fn reduce_leaf_env(
    c: &TypedComp,
    tail: Option<&(Sym, StreamExpr)>,
    ctors: StepCtors,
    env: &mut BTreeMap<Sym, StreamExpr>,
    cx: &mut Cx,
) -> Option<Step> {
    let c = normalize(c, cx)?;
    match c.kind() {
        TypedCompKind::Return(value) => match &peel(value).kind {
            TypedValueKind::Ctor { name, fields, .. }
                if *name == ctors.done && fields.is_empty() =>
            {
                Some(Step::Done)
            }
            TypedValueKind::Ctor { name, fields, .. }
                if *name == ctors.more && fields.len() == 2 =>
            {
                let head = fields[0].clone();
                let next = resolve_tail_value(&fields[1], env)?;
                Some(Step::Yield { head, next })
            }
            _ => None,
        },
        TypedCompKind::If(cond, yes, no) => {
            let then = reduce_leaf_env(yes, tail, ctors, &mut env.clone(), cx)?;
            let els = reduce_leaf_env(no, tail, ctors, &mut env.clone(), cx)?;
            Some(Step::Branch {
                cond: cond.clone(),
                then: Box::new(then),
                els: Box::new(els),
            })
        }
        // A bare re-force of a tail pipeline (a filter's non-yielding branch):
        // skip, advancing over that tail.
        TypedCompKind::App {
            callee,
            instantiation: _,
            args,
        } if args.len() == 1 && is_unit(&args[0]) => {
            let TypedCompKind::Force(head) = callee.kind() else {
                return None;
            };
            let t = as_var(head)?;
            let next = env.get(&t).cloned()?;
            Some(Step::Skip { next })
        }
        TypedCompKind::Bind(first, binder, rest) => {
            // A stream-tail binding (a call to a stream combinator) names a
            // rebuilt tail; record it and continue without emitting a
            // computation.
            if let TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } = first.kind()
            {
                if is_stream_comb(*callee, cx) {
                    let se = stream_from_tailcall(*callee, instantiation, args, tail, env, cx)?;
                    env.insert(binder.name(), se);
                    return reduce_leaf_env(rest, tail, ctors, env, cx);
                }
            }
            // Otherwise a pure head computation (a reduced mapper/predicate
            // application) scoped over the rest of the leaf.
            if comp_pure(first, cx) {
                let body = reduce_leaf_env(rest, tail, ctors, env, cx)?;
                return Some(Step::Let {
                    binder: binder.clone(),
                    comp: first.clone(),
                    body: Box::new(body),
                });
            }
            None
        }
        _ => None,
    }
}

// Resolve a constructed cons tail value (always a bound variable in the shapes
// this cut recognizes) to its pipeline tree.
fn resolve_tail_value(v: &TypedValue, env: &BTreeMap<Sym, StreamExpr>) -> Option<StreamExpr> {
    env.get(&as_var(v)?).cloned()
}

// Rebuild the pipeline tree for a tail call: a producer's advanced self-call
// (all value arguments) or a transformer over the inner tail (its stream slot
// is the marker variable, or a variable already bound in `env`).
fn stream_from_tailcall(
    k: Sym,
    kinst: &[CoreInstantiation],
    kargs: &[TypedValue],
    tail: Option<&(Sym, StreamExpr)>,
    env: &BTreeMap<Sym, StreamExpr>,
    cx: &mut Cx,
) -> Option<StreamExpr> {
    match stream_role(k, cx)? {
        Role::Producer => Some(StreamExpr {
            comb: k,
            instantiation: kinst.to_vec(),
            args: kargs.iter().map(|v| Arg::Val(v.clone())).collect(),
        }),
        Role::Transformer(i) => {
            let mut args = Vec::with_capacity(kargs.len());
            for (j, v) in kargs.iter().enumerate() {
                if j == i {
                    let m = as_var(v)?;
                    let inner = match tail {
                        Some((mk, it)) if m == *mk => it.clone(),
                        _ => env.get(&m).cloned()?,
                    };
                    args.push(Arg::Stream(Box::new(inner)));
                } else {
                    args.push(Arg::Val(v.clone()));
                }
            }
            Some(StreamExpr {
                comb: k,
                instantiation: kinst.to_vec(),
                args,
            })
        }
    }
}

// A stream combinator returns a step thunk `\u. ...`; its body is
// `Return(Thunk(Lam([_], _)))`. Used to tell a stream-tail binding apart from a
// scalar head computation (a mapper call).
fn is_stream_comb(comb: Sym, cx: &Cx) -> bool {
    cx.fns.get(&comb).is_some_and(|def| {
        if let TypedCompKind::Return(value) = def.body.kind() {
            if let TypedValueKind::Thunk(thunk) = &peel(value).kind {
                return matches!(thunk.kind(), TypedCompKind::Lam(params, _) if params.len() == 1);
            }
        }
        false
    })
}

// Replace the stream argument of `s` with `inner`.
fn replace_stream(s: &StreamExpr, idx: usize, inner: StreamExpr) -> StreamExpr {
    let mut args = s.args.clone();
    args[idx] = Arg::Stream(Box::new(inner));
    StreamExpr {
        comb: s.comb,
        instantiation: s.instantiation.clone(),
        args,
    }
}

// --- small helpers over typed Core ------------------------------------------------

fn bind_args(def: &TypedCoreFn, s: &StreamExpr) -> Option<BTreeMap<Sym, TypedValue>> {
    if def.params().len() != s.args.len() {
        return None;
    }
    let mut sub = BTreeMap::new();
    for (p, a) in def.params().iter().zip(&s.args) {
        match a {
            Arg::Val(v) => {
                sub.insert(p.name(), v.clone());
            }
            Arg::Stream(_) => return None,
        }
    }
    Some(sub)
}

fn bind_value_args(
    def: &TypedCoreFn,
    s: &StreamExpr,
    stream_idx: usize,
) -> BTreeMap<Sym, TypedValue> {
    let mut sub = BTreeMap::new();
    for (i, (p, a)) in def.params().iter().zip(&s.args).enumerate() {
        if i == stream_idx {
            continue;
        }
        if let Arg::Val(v) = a {
            sub.insert(p.name(), v.clone());
        }
    }
    sub
}

// Inline a combinator body with `sub` after instantiating its scheme at the
// pipeline call's explicit arguments, normalize, and extract its step body (the
// `\u. ...` under the returned thunk, with `u` bound to unit).
fn step_body_of(
    def: &TypedCoreFn,
    instantiation: &[CoreInstantiation],
    sub: &BTreeMap<Sym, TypedValue>,
    cx: &mut Cx,
) -> Option<TypedComp> {
    let inst_body = substitute_witnesses(&def.body, def.sig().quantifiers(), instantiation);
    let body = normalize(&subst(&inst_body, sub, cx), cx)?;
    if let TypedCompKind::Return(value) = body.kind() {
        if let TypedValueKind::Thunk(thunk) = &peel(value).kind {
            if let TypedCompKind::Lam(params, lam_body) = thunk.kind() {
                if params.len() == 1 {
                    let mut s2 = BTreeMap::new();
                    s2.insert(params[0].name(), unit_value());
                    // Copy-propagate the arm-internal aliases so the driven
                    // arms read structurally.
                    let stepped = normalize(&subst(lam_body, &s2, cx), cx)?;
                    return Some(copy_prop(&stepped, cx));
                }
            }
        }
    }
    None
}

fn force_case_of(step: &TypedComp, seqparam: Sym) -> Option<(Sym, Vec<Arm>)> {
    if let TypedCompKind::Bind(first, st, rest) = step.kind() {
        if let TypedCompKind::App {
            callee,
            instantiation: _,
            args,
        } = first.kind()
        {
            if let TypedCompKind::Force(head) = callee.kind() {
                if as_var(head) == Some(seqparam) && args.len() == 1 && is_unit(&args[0]) {
                    if let TypedCompKind::Case(scrutinee, arms) = rest.kind() {
                        if as_var(scrutinee) == Some(st.name()) {
                            return Some((st.name(), arms.clone()));
                        }
                    }
                }
            }
        }
    }
    None
}

fn subst(c: &TypedComp, sub: &BTreeMap<Sym, TypedValue>, cx: &mut Cx) -> TypedComp {
    substitute_terms(c, sub, &mut cx.fresh, FRESH_FUSE)
}

// Copy-propagate every trivial `Bind(Return v, x, k)` alias throughout `c`
// (recursively, under every binder), which elaboration's per-step `return x to
// t` sequencing leaves behind. Unlike `normalize` (head-only), this descends
// everywhere, so a self-call's arguments and a transformer's arms read
// structurally.
fn copy_prop(c: &TypedComp, cx: &mut Cx) -> TypedComp {
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
    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        match c.kind() {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, &());
                // Inline a trivial value alias.
                if let TypedCompKind::Return(value) = first.kind() {
                    let mut sub = BTreeMap::new();
                    sub.insert(binder.name(), value.clone());
                    let rest = substitute_terms(rest, &sub, self.counter, FRESH_FUSE);
                    return self.comp(&rest, &());
                }
                // Re-associate `Bind(Bind(ia, iy, ib), x, k)` to
                // `Bind(ia, iy, Bind(ib, x, k))` (monad associativity), so the
                // whole computation is one flat bind spine and the driver reads
                // each `Call`/`Prim` at the spine. The new inner bind takes the
                // verified sig-construction rule (the continuation's result
                // over the children's row union).
                if let TypedCompKind::Bind(inner_first, inner_binder, inner_rest) = first.kind() {
                    let inner = TypedComp::new(
                        CompSig::new(
                            rest.sig().result().clone(),
                            union_effects(inner_rest.sig().effects(), rest.sig().effects()),
                        ),
                        TypedCompKind::Bind(inner_rest.clone(), binder.clone(), rest.clone()),
                    );
                    let reassoc = TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Bind(
                            inner_first.clone(),
                            inner_binder.clone(),
                            Box::new(inner),
                        ),
                    );
                    return self.comp(&reassoc, &());
                }
                TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(first),
                        binder.clone(),
                        Box::new(self.comp(rest, &())),
                    ),
                )
            }
            _ => self.descend_comp(c, &()),
        }
    }
}

// Eliminate dead pure let-bindings from `c`: a `Bind(a, x, k)` whose bound
// variable `x` is unused in the rewritten continuation and whose `a` is
// effect-free is dropped. Applied only to a function that fused, to sweep away
// the upstream pipeline the redirected consumer no longer reads. Bottom-up, so
// a binding that becomes dead only after an inner one is removed is caught in
// the same pass.
fn dead_let_elim(c: &TypedComp, cx: &mut Cx) -> TypedComp {
    Dce { cx }.comp(c, &())
}

struct Dce<'a> {
    cx: &'a mut Cx,
}

impl Rewrite for Dce<'_> {
    type Ctx = ();
    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        match c.kind() {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, &());
                let rest = self.comp(rest, &());
                if !free_comp_vars(&rest).contains(&binder.name()) && self.removable(&first) {
                    rest
                } else {
                    TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Bind(Box::new(first), binder.clone(), Box::new(rest)),
                    )
                }
            }
            _ => self.descend_comp(c, &()),
        }
    }
}

impl Dce<'_> {
    // A dead bound computation is removed only when it is obviously total,
    // never merely pure: dropping a diverging (even pure) computation would
    // turn a non-terminating program terminating, an observable change the
    // determinism contract forbids. The dead upstream pipeline is a bind-chain
    // of `Return(_)` and lazy stream-combinator calls, every step `O(1)` and
    // total; a chain of total steps is total.
    fn removable(&self, a: &TypedComp) -> bool {
        match a.kind() {
            TypedCompKind::Return(_) => true,
            TypedCompKind::Call { callee, .. } => is_stream_comb(*callee, self.cx),
            TypedCompKind::Bind(first, _, rest) => self.removable(first) && self.removable(rest),
            _ => false,
        }
    }
}

// --- normalization (bounded head reduction) -------------------------------------

// Reduce a computation by the fusion rules until its head is stuck:
// let-of-return, force-of-thunk, beta (applied lambda/forced-thunk-lambda),
// case-of-known-constructor, and if-of-known-boolean. Arithmetic is NOT folded,
// so a producer's advancing argument stays a symbolic `x + 1` rather than
// collapsing to a literal. Returns `None` on budget overrun.
fn normalize(c: &TypedComp, cx: &mut Cx) -> Option<TypedComp> {
    let mut steps = UNFOLD_BUDGET;
    normalize_go(c, cx, &mut steps)
}

fn normalize_go(c: &TypedComp, cx: &mut Cx, steps: &mut u32) -> Option<TypedComp> {
    if *steps == 0 {
        return None;
    }
    *steps -= 1;
    match c.kind() {
        TypedCompKind::Bind(first, binder, rest) => {
            let first = normalize_go(first, cx, steps)?;
            if let TypedCompKind::Return(value) = first.kind() {
                let mut sub = BTreeMap::new();
                sub.insert(binder.name(), value.clone());
                let rest = subst(rest, &sub, cx);
                return normalize_go(&rest, cx, steps);
            }
            Some(TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Bind(Box::new(first), binder.clone(), rest.clone()),
            ))
        }
        TypedCompKind::Force(value) => match &peel(value).kind {
            TypedValueKind::Thunk(inner) => normalize_go(inner, cx, steps),
            _ => Some(c.clone()),
        },
        TypedCompKind::App {
            callee,
            instantiation,
            args,
        } => {
            let head = normalize_go(callee, cx, steps)?;
            if let TypedCompKind::Lam(params, body) = head.kind() {
                if params.len() == args.len() {
                    let sub: BTreeMap<Sym, TypedValue> = params
                        .iter()
                        .map(TypedBinder::name)
                        .zip(args.iter().cloned())
                        .collect();
                    let body = subst(body, &sub, cx);
                    return normalize_go(&body, cx, steps);
                }
            }
            Some(TypedComp::new(
                c.sig().clone(),
                TypedCompKind::App {
                    callee: Box::new(head),
                    instantiation: instantiation.clone(),
                    args: args.clone(),
                },
            ))
        }
        TypedCompKind::If(cond, yes, no) => match &peel(cond).kind {
            TypedValueKind::Bool(b) => {
                let branch = if *b { yes } else { no };
                normalize_go(branch, cx, steps)
            }
            _ => Some(c.clone()),
        },
        TypedCompKind::Case(scrutinee, arms) => {
            if let TypedValueKind::Ctor { name, fields, .. } = &peel(scrutinee).kind {
                for (pattern, body) in arms {
                    if let TypedPattern::Ctor {
                        name: pc,
                        fields: binders,
                        ..
                    } = pattern
                    {
                        if pc == name && binders.len() == fields.len() {
                            let mut sub = BTreeMap::new();
                            for (binder, field) in binders.iter().zip(fields) {
                                if let Some(binder) = binder {
                                    sub.insert(binder.name(), field.clone());
                                }
                            }
                            let body = subst(body, &sub, cx);
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

// One advancing stream position: the fresh variable abstracting it, its path
// into the pipeline tree, and its initial (seed) value.
struct StreamParam {
    var: Sym,
    path: Vec<usize>,
    init: TypedValue,
}

// Anti-unify the seed pipeline against its one-step tail, allocate join
// parameters for the differing (advancing) positions and the changing
// accumulators, drive the pipeline symbolically, and residualize into one fresh
// top-level join function. Returns the redirected call, or `None` to not fuse.
fn build_join(consumer: &Consumer, seed: &StreamExpr, cx: &mut Cx) -> Option<TypedComp> {
    // Abstract the scalar (non-closure) arguments to fresh variables, so the
    // producer's advance is driven symbolically (`x + 1`, not a folded
    // literal).
    let (sym_seed, init) = abstract_stream(seed, cx);
    let mut budget = UNFOLD_BUDGET;
    let step = drive(&sym_seed, consumer.ctors, cx, &mut budget)?;
    if step_size(&step) > SIZE_BUDGET {
        return None;
    }
    // The one-step tail (identical across every yielding/skipping leaf): the
    // knot.
    let tail = collect_tail(&step)?;
    // Classify each abstracted position: a differing one advances (a join
    // parameter), a coincident one is invariant (baked back to its seed value).
    let mut params: Vec<StreamParam> = Vec::new();
    let mut bakes: BTreeMap<Sym, TypedValue> = BTreeMap::new();
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
    // Join parameters: advancing stream positions first (deterministic
    // first-occurrence order), then the consumer's accumulators.
    let mut jparams: Vec<TypedBinder> = params
        .iter()
        .map(|p| TypedBinder::new(p.var, p.init.ty().clone()))
        .collect();
    jparams.extend(consumer.acc_params.iter().cloned());
    // Scope safety: the residual must close over nothing but the join
    // parameters. A leaked local (the most-specific-generalization scope trap)
    // aborts the seed.
    let jparam_names: Vec<Sym> = jparams.iter().map(TypedBinder::name).collect();
    if !join_is_closed(&body, &jparam_names) {
        return None;
    }
    let sig = CoreFnSig::new(
        Vec::new(),
        jparams.iter().map(|b| b.ty().clone()).collect(),
        consumer.call_sig.clone(),
    );
    cx.emitted
        .push(TypedCoreFn::new(join, jparams, body, sig, 0));
    cx.joins += 1;
    // The redirected initial call: seed values for the advancing positions,
    // then the accumulators' seed values.
    let mut initargs: Vec<TypedValue> = params.iter().map(|p| p.init.clone()).collect();
    initargs.extend(consumer.accs.iter().map(|a| a.seed.clone()));
    Some(TypedComp::new(
        consumer.call_sig.clone(),
        TypedCompKind::Call {
            callee: join,
            instantiation: Vec::new(),
            args: initargs,
        },
    ))
}

// Replace every scalar (non-thunk) value argument in the pipeline with a fresh
// variable, recording its seed value, in a fixed pre-order traversal (so
// parameter naming and order are byte-stable). Thunk arguments are left
// concrete so their applications inline during driving.
fn abstract_stream(s: &StreamExpr, cx: &mut Cx) -> (StreamExpr, BTreeMap<Sym, TypedValue>) {
    let mut init = BTreeMap::new();
    let out = abstract_go(s, &mut init, cx);
    (out, init)
}

fn abstract_go(s: &StreamExpr, init: &mut BTreeMap<Sym, TypedValue>, cx: &mut Cx) -> StreamExpr {
    let args = s
        .args
        .iter()
        .map(|a| match a {
            Arg::Val(v) if matches!(&peel(v).kind, TypedValueKind::Thunk(_)) => Arg::Val(v.clone()),
            Arg::Val(v) => {
                let f = next_fresh(&mut cx.fresh, FRESH_FUSE);
                init.insert(f, v.clone());
                Arg::Val(TypedValue::new(
                    v.ty().clone(),
                    TypedValueKind::Var {
                        name: f,
                        instantiation: Vec::new(),
                    },
                ))
            }
            Arg::Stream(inner) => Arg::Stream(Box::new(abstract_go(inner, init, cx))),
        })
        .collect();
    StreamExpr {
        comb: s.comb,
        instantiation: s.instantiation.clone(),
        args,
    }
}

// Walk the abstracted seed and its one-step tail in parallel, sorting each
// abstracted position into an advancing parameter or a baked invariant.
fn classify(
    sym: &StreamExpr,
    tail: &StreamExpr,
    init: &BTreeMap<Sym, TypedValue>,
    path: &mut Vec<usize>,
    params: &mut Vec<StreamParam>,
    bakes: &mut BTreeMap<Sym, TypedValue>,
) -> Option<()> {
    if sym.comb != tail.comb || sym.args.len() != tail.args.len() {
        return None;
    }
    for (j, (sa, ta)) in sym.args.iter().zip(&tail.args).enumerate() {
        path.push(j);
        match (sa, ta) {
            (Arg::Val(sv), Arg::Val(tv)) => {
                if let Some(fv) = as_var(sv).filter(|fv| init.contains_key(fv)) {
                    // Invariant exactly when the tail threads the same variable
                    // through.
                    if as_var(tv) == Some(fv) {
                        bakes.insert(fv, init[&fv].clone());
                    } else {
                        params.push(StreamParam {
                            var: fv,
                            path: path.clone(),
                            init: init[&fv].clone(),
                        });
                    }
                } else if matches!(&peel(sv).kind, TypedValueKind::Thunk(_))
                    && matches!(&peel(tv).kind, TypedValueKind::Thunk(_))
                {
                    // A closure argument is threaded unchanged; alpha-renaming
                    // of its binder is irrelevant, so ignore it.
                } else if !value_eq(sv, tv) {
                    // A non-closure non-abstracted value must not change.
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

// Collect the one-step tail shared by every yielding/skipping leaf; `None` if
// the leaves disagree (an unexpected non-uniform advance) or the pipeline never
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
// emitting the consumer's per-element action at each yield and a self-call at
// every leaf.
struct Res<'a> {
    consumer: &'a Consumer,
    join: Sym,
    stream_paths: &'a [Vec<usize>],
    cx: &'a mut Cx,
}

impl Res<'_> {
    fn residual(&mut self, step: &Step) -> Option<TypedComp> {
        match step {
            Step::Done => Some(subst(
                &self.consumer.done_body,
                &self.consumer.baked,
                self.cx,
            )),
            Step::Skip { next } => {
                let mut args = self.stream_rec_args(next)?;
                args.extend(self.consumer.acc_params.iter().map(binder_var));
                Some(self.join_call(args))
            }
            Step::Yield { head, next } => {
                let mut rec_args = self.stream_rec_args(next)?;
                rec_args.extend(self.consumer.accs.iter().map(|a| a.advance.clone()));
                let call = self.join_call(rec_args);
                let grafted = graft_return(&self.consumer.step_body, call)?;
                // Substitute the element and baked closures uniformly, then
                // inline the fold-function application the graft exposed.
                let mut sub = self.consumer.baked.clone();
                sub.insert(self.consumer.elem, head.clone());
                let done = subst(&grafted, &sub, self.cx);
                normalize(&done, self.cx)
            }
            Step::Branch { cond, then, els } => {
                let t = self.residual(then)?;
                let e = self.residual(els)?;
                let sig = CompSig::new(
                    t.sig().result().clone(),
                    union_effects(t.sig().effects(), e.sig().effects()),
                );
                Some(TypedComp::new(
                    sig,
                    TypedCompKind::If(cond.clone(), Box::new(t), Box::new(e)),
                ))
            }
            Step::Let { binder, comp, body } => {
                let b = self.residual(body)?;
                let sig = CompSig::new(
                    b.sig().result().clone(),
                    union_effects(comp.sig().effects(), b.sig().effects()),
                );
                Some(TypedComp::new(
                    sig,
                    TypedCompKind::Bind(comp.clone(), binder.clone(), Box::new(b)),
                ))
            }
        }
    }

    // The recursive join call, carrying the seed call-site sig (the join's
    // declared body signature, so the direct-call witness rule holds).
    fn join_call(&self, args: Vec<TypedValue>) -> TypedComp {
        TypedComp::new(
            self.consumer.call_sig.clone(),
            TypedCompKind::Call {
                callee: self.join,
                instantiation: Vec::new(),
                args,
            },
        )
    }

    // The advancing arguments for a recursive call: each stream parameter read
    // from the leaf's tail pipeline at its path.
    fn stream_rec_args(&self, next: &StreamExpr) -> Option<Vec<TypedValue>> {
        self.stream_paths
            .iter()
            .map(|p| read_at_path(next, p))
            .collect()
    }
}

// Replace the trailing `Return(Unit)` marker (the stripped self-call) with
// `repl`.
fn graft_return(body: &TypedComp, repl: TypedComp) -> Option<TypedComp> {
    match body.kind() {
        TypedCompKind::Return(value) if matches!(value.kind(), TypedValueKind::Unit) => Some(repl),
        TypedCompKind::Bind(first, binder, rest) => Some(TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Bind(
                first.clone(),
                binder.clone(),
                Box::new(graft_return(rest, repl)?),
            ),
        )),
        _ => None,
    }
}

// Read the value at `path` (a sequence of argument indices descending through
// stream arguments, the last picking a value argument).
fn read_at_path(se: &StreamExpr, path: &[usize]) -> Option<TypedValue> {
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

// Structural equality of two pipeline tails, ignoring closure (thunk)
// arguments: mappers/predicates/fold functions are threaded unchanged, so an
// alpha-rename of a baked closure's binder must not make two
// otherwise-identical tails disagree.
fn stream_eq(a: &StreamExpr, b: &StreamExpr) -> bool {
    a.comb == b.comb
        && a.args.len() == b.args.len()
        && a.args.iter().zip(&b.args).all(|(x, y)| match (x, y) {
            (Arg::Stream(xi), Arg::Stream(yi)) => stream_eq(xi, yi),
            (Arg::Val(xv), Arg::Val(yv)) => {
                (matches!(&peel(xv).kind, TypedValueKind::Thunk(_))
                    && matches!(&peel(yv).kind, TypedValueKind::Thunk(_)))
                    || value_eq(xv, yv)
            }
            _ => false,
        })
}

// Value equality as the erased legacy pass computes it: floats by bit pattern
// (recursively through constructors and tuples), representation wrappers
// invisible, and everything else by erased structural equality.
fn value_eq(a: &TypedValue, b: &TypedValue) -> bool {
    match (&peel(a).kind, &peel(b).kind) {
        (TypedValueKind::Float(x), TypedValueKind::Float(y)) => x.to_bits() == y.to_bits(),
        (
            TypedValueKind::Ctor {
                name: xn,
                tag: xt,
                fields: xs,
                ..
            },
            TypedValueKind::Ctor {
                name: yn,
                tag: yt,
                fields: ys,
                ..
            },
        ) => {
            xn == yn
                && xt == yt
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| value_eq(x, y))
        }
        (TypedValueKind::Tuple(xs), TypedValueKind::Tuple(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| value_eq(x, y))
        }
        _ => a.clone().erase() == b.clone().erase(),
    }
}

// The scope-safety gate on an emitted join: its body may close over nothing but
// its own parameters (top-level names and literals are not free variables). A
// violation means the most-specific generalization proposed a hole under a
// binder introduced during driving, the classic scope trap.
fn join_is_closed(body: &TypedComp, jparams: &[Sym]) -> bool {
    free_comp_vars(body).iter().all(|v| jparams.contains(v))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::core::opt::{run_spec_stage, CorePass, PassStage};
    use crate::core::CoreOp;
    use crate::flags::DynFlags;
    use crate::types::Type;

    use super::super::verify::{verify, ConstructorSig, VerifyEnv};
    use super::super::Elaborated;
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn int() -> CoreType {
        source(Type::Int)
    }

    fn pure_sig(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn step_ty() -> CoreType {
        source(Type::Con(sym("Step"), vec![Type::Int]))
    }

    // A pull sequence: a thunk of a one-argument step closure `(Unit) -> Step`.
    fn seq_ty() -> CoreType {
        CoreType::Thunk(Box::new(pure_sig(CoreType::Function(Box::new(
            CoreFnSig::new(Vec::new(), vec![source(Type::Unit)], pure_sig(step_ty())),
        )))))
    }

    fn mapper_ty() -> CoreType {
        CoreType::Thunk(Box::new(pure_sig(CoreType::Function(Box::new(
            CoreFnSig::new(Vec::new(), vec![int()], pure_sig(int())),
        )))))
    }

    fn var(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn lit(n: i64) -> TypedValue {
        TypedValue::new(int(), TypedValueKind::Int(n))
    }

    fn unit() -> TypedValue {
        TypedValue::new(source(Type::Unit), TypedValueKind::Unit)
    }

    fn ret(v: TypedValue) -> TypedComp {
        TypedComp::new(pure_sig(v.ty().clone()), TypedCompKind::Return(v))
    }

    // All fixture rows are `Empty`, so the verified `Bind` sig collapses to the
    // continuation's sig.
    fn bind(first: TypedComp, name: &str, ty: CoreType, rest: TypedComp) -> TypedComp {
        TypedComp::new(
            rest.sig().clone(),
            TypedCompKind::Bind(
                Box::new(first),
                TypedBinder::new(sym(name), ty),
                Box::new(rest),
            ),
        )
    }

    fn prim(op: CoreOp, result: CoreType, a: TypedValue, b: TypedValue) -> TypedComp {
        TypedComp::new(pure_sig(result), TypedCompKind::Prim(op, a, b))
    }

    fn call(f: &str, args: Vec<TypedValue>, result: CoreType) -> TypedComp {
        TypedComp::new(
            pure_sig(result),
            TypedCompKind::Call {
                callee: sym(f),
                instantiation: Vec::new(),
                args,
            },
        )
    }

    fn purity_cx(functions: Vec<TypedCoreFn>) -> Cx {
        Cx {
            fns: functions
                .into_iter()
                .map(|function| (function.name(), function))
                .collect(),
            pure: BTreeMap::new(),
            fresh: 0,
            joins: 0,
            emitted: Vec::new(),
        }
    }

    fn sdone() -> TypedValue {
        TypedValue::new(
            step_ty(),
            TypedValueKind::Ctor {
                name: sym("SDone"),
                tag: 0,
                instantiation: Vec::new(),
                fields: Vec::new(),
            },
        )
    }

    fn smore(head: TypedValue, tail: TypedValue) -> TypedValue {
        TypedValue::new(
            step_ty(),
            TypedValueKind::Ctor {
                name: sym("SMore"),
                tag: 1,
                instantiation: Vec::new(),
                fields: vec![head, tail],
            },
        )
    }

    // The step application `force(seq)(())`.
    fn force_app(seq: TypedValue) -> TypedComp {
        let fun = CoreFnSig::new(Vec::new(), vec![source(Type::Unit)], pure_sig(step_ty()));
        let force = TypedComp::new(
            pure_sig(CoreType::Function(Box::new(fun))),
            TypedCompKind::Force(seq),
        );
        TypedComp::new(
            pure_sig(step_ty()),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![unit()],
            },
        )
    }

    fn step_lam(step: TypedComp) -> TypedComp {
        let lam_sig = CoreFnSig::new(Vec::new(), vec![source(Type::Unit)], pure_sig(step_ty()));
        TypedComp::new(
            pure_sig(CoreType::Function(Box::new(lam_sig))),
            TypedCompKind::Lam(
                vec![TypedBinder::new(sym("u"), source(Type::Unit))],
                Box::new(step),
            ),
        )
    }

    fn done_pattern() -> TypedPattern {
        TypedPattern::Ctor {
            name: sym("SDone"),
            instantiation: Vec::new(),
            fields: Vec::new(),
        }
    }

    fn more_pattern(head: &str, tail: &str) -> TypedPattern {
        TypedPattern::Ctor {
            name: sym("SMore"),
            instantiation: Vec::new(),
            fields: vec![
                Some(TypedBinder::new(sym(head), int())),
                Some(TypedBinder::new(sym(tail), seq_ty())),
            ],
        }
    }

    // fn count(i, n) = return thunk \u.
    //   bind b = i <= n in
    //   if b then bind i2 = i + 1 in bind t = count(i2, n) in return SMore(i, t)
    //   else return SDone
    fn count_fn() -> TypedCoreFn {
        let yield_branch = bind(
            prim(CoreOp::Add, int(), var("i", int()), lit(1)),
            "i2",
            int(),
            bind(
                call("count", vec![var("i2", int()), var("n", int())], seq_ty()),
                "t",
                seq_ty(),
                ret(smore(var("i", int()), var("t", seq_ty()))),
            ),
        );
        let step = bind(
            prim(
                CoreOp::Le,
                source(Type::Bool),
                var("i", int()),
                var("n", int()),
            ),
            "b",
            source(Type::Bool),
            TypedComp::new(
                pure_sig(step_ty()),
                TypedCompKind::If(
                    var("b", source(Type::Bool)),
                    Box::new(yield_branch),
                    Box::new(ret(sdone())),
                ),
            ),
        );
        let body = ret(TypedValue::new(
            seq_ty(),
            TypedValueKind::Thunk(Box::new(step_lam(step))),
        ));
        TypedCoreFn::new(
            sym("count"),
            vec![
                TypedBinder::new(sym("i"), int()),
                TypedBinder::new(sym("n"), int()),
            ],
            body,
            CoreFnSig::new(Vec::new(), vec![int(), int()], pure_sig(seq_ty())),
            0,
        )
    }

    // fn map(f, s) = return thunk \u.
    //   bind st = force(s)(()) in
    //   case st of
    //     SDone => return SDone
    //     SMore(x, rest) =>
    //       bind y = force(f)(x) in bind t = map(f, rest) in return SMore(y, t)
    fn map_fn() -> TypedCoreFn {
        let apply_f = {
            let fun = CoreFnSig::new(Vec::new(), vec![int()], pure_sig(int()));
            let force = TypedComp::new(
                pure_sig(CoreType::Function(Box::new(fun))),
                TypedCompKind::Force(var("f", mapper_ty())),
            );
            TypedComp::new(
                pure_sig(int()),
                TypedCompKind::App {
                    callee: Box::new(force),
                    instantiation: Vec::new(),
                    args: vec![var("x", int())],
                },
            )
        };
        let more_body = bind(
            apply_f,
            "y",
            int(),
            bind(
                call(
                    "map",
                    vec![var("f", mapper_ty()), var("rest", seq_ty())],
                    seq_ty(),
                ),
                "t",
                seq_ty(),
                ret(smore(var("y", int()), var("t", seq_ty()))),
            ),
        );
        let case = TypedComp::new(
            pure_sig(step_ty()),
            TypedCompKind::Case(
                var("st", step_ty()),
                vec![
                    (done_pattern(), ret(sdone())),
                    (more_pattern("x", "rest"), more_body),
                ],
            ),
        );
        let step = bind(force_app(var("s", seq_ty())), "st", step_ty(), case);
        let body = ret(TypedValue::new(
            seq_ty(),
            TypedValueKind::Thunk(Box::new(step_lam(step))),
        ));
        TypedCoreFn::new(
            sym("map"),
            vec![
                TypedBinder::new(sym("f"), mapper_ty()),
                TypedBinder::new(sym("s"), seq_ty()),
            ],
            body,
            CoreFnSig::new(Vec::new(), vec![mapper_ty(), seq_ty()], pure_sig(seq_ty())),
            0,
        )
    }

    // fn total(s, acc) =
    //   bind st = force(s)(()) in
    //   case st of
    //     SDone => return acc
    //     SMore(x, rest) => bind acc2 = acc + x in total(rest, acc2)
    fn total_fn() -> TypedCoreFn {
        let more_body = bind(
            prim(CoreOp::Add, int(), var("acc", int()), var("x", int())),
            "acc2",
            int(),
            call(
                "total",
                vec![var("rest", seq_ty()), var("acc2", int())],
                int(),
            ),
        );
        let case = TypedComp::new(
            pure_sig(int()),
            TypedCompKind::Case(
                var("st", step_ty()),
                vec![
                    (done_pattern(), ret(var("acc", int()))),
                    (more_pattern("x", "rest"), more_body),
                ],
            ),
        );
        let body = bind(force_app(var("s", seq_ty())), "st", step_ty(), case);
        TypedCoreFn::new(
            sym("total"),
            vec![
                TypedBinder::new(sym("s"), seq_ty()),
                TypedBinder::new(sym("acc"), int()),
            ],
            body,
            CoreFnSig::new(Vec::new(), vec![seq_ty(), int()], pure_sig(int())),
            0,
        )
    }

    fn step_env() -> VerifyEnv {
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            sym("SDone"),
            ConstructorSig::new(Vec::new(), 0, Vec::new(), step_ty()),
        );
        env.insert_constructor(
            sym("SMore"),
            ConstructorSig::new(Vec::new(), 1, vec![int(), seq_ty()], step_ty()),
        );
        env
    }

    // Verify the fixture, run the legacy pass on its erasure and the typed pass
    // on the witnesses, verify the output, and demand byte-identical erased
    // trees and identical tick counts.
    fn assert_differential(
        functions: Vec<TypedCoreFn>,
        env: &VerifyEnv,
    ) -> (TypedCore<Elaborated>, u64) {
        let input = TypedCore::new(functions);
        if let Err(violations) = verify(&input, env) {
            panic!("input fixture is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let (expected, legacy_stats) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &[CorePass::Fuse],
            PassStage::PreLowering,
            &[],
            &DynFlags::default(),
        );
        let expected_ticks = legacy_stats.total();
        let (actual, stats) = fuse(input);
        if let Err(violations) = verify(&actual, env) {
            panic!("fused typed Core is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        assert_eq!(stats.ticks(), expected_ticks);
        (actual, expected_ticks)
    }

    // `total(count(3, 10), 0)`: the producer-fold seed fuses into one join
    // whose loop carries the advancing counter and the accumulator.
    #[test]
    fn producer_fold_pipeline_fuses_to_a_join() {
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            bind(
                call("count", vec![lit(3), lit(10)], seq_ty()),
                "s",
                seq_ty(),
                call("total", vec![var("s", seq_ty()), lit(0)], int()),
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let (actual, ticks) = assert_differential(vec![count_fn(), total_fn(), main], &step_env());
        assert_eq!(ticks, 1);
        let join = Sym::new(&names::fused_join(0));
        assert!(actual.functions().iter().any(|f| f.name() == join));
    }

    // `total(map(dbl, count(3, 10)), 0)`: the transformer composes with the
    // producer (case-of-case through the driven leaves) and the whole nested
    // pipeline still residualizes into a single join.
    #[test]
    fn mapped_pipeline_fuses_through_the_transformer() {
        let dbl = {
            let fun = CoreFnSig::new(Vec::new(), vec![int()], pure_sig(int()));
            let lam = TypedComp::new(
                pure_sig(CoreType::Function(Box::new(fun))),
                TypedCompKind::Lam(
                    vec![TypedBinder::new(sym("z"), int())],
                    Box::new(prim(CoreOp::Mul, int(), var("z", int()), lit(2))),
                ),
            );
            TypedValue::new(mapper_ty(), TypedValueKind::Thunk(Box::new(lam)))
        };
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            bind(
                call("count", vec![lit(3), lit(10)], seq_ty()),
                "s0",
                seq_ty(),
                bind(
                    ret(dbl),
                    "d",
                    mapper_ty(),
                    bind(
                        call(
                            "map",
                            vec![var("d", mapper_ty()), var("s0", seq_ty())],
                            seq_ty(),
                        ),
                        "s1",
                        seq_ty(),
                        call("total", vec![var("s1", seq_ty()), lit(0)], int()),
                    ),
                ),
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let (actual, ticks) =
            assert_differential(vec![count_fn(), map_fn(), total_fn(), main], &step_env());
        assert_eq!(ticks, 1);
        let join = Sym::new(&names::fused_join(0));
        assert!(actual.functions().iter().any(|f| f.name() == join));
    }

    // A consumer whose sequence argument is an opaque parameter (no upstream
    // binding to resolve) is left exactly as written on both sides.
    #[test]
    fn unresolved_stream_leaves_the_call_untouched() {
        let opaque = TypedCoreFn::new(
            sym("opaque"),
            vec![TypedBinder::new(sym("s"), seq_ty())],
            call("total", vec![var("s", seq_ty()), lit(0)], int()),
            CoreFnSig::new(Vec::new(), vec![seq_ty()], pure_sig(int())),
            0,
        );
        let (_, ticks) = assert_differential(vec![total_fn(), opaque], &step_env());
        assert_eq!(ticks, 0);
    }

    // A fold whose per-element action contains an effect node (the aborting
    // `Error` intrinsic) fails the purity gate and degrades to not fusing.
    #[test]
    fn impure_step_refuses_to_fuse() {
        let more_body = bind(
            TypedComp::new(pure_sig(int()), TypedCompKind::Error(lit(0))),
            "e",
            int(),
            bind(
                prim(CoreOp::Add, int(), var("acc", int()), var("x", int())),
                "acc2",
                int(),
                call(
                    "crashy",
                    vec![var("rest", seq_ty()), var("acc2", int())],
                    int(),
                ),
            ),
        );
        let case = TypedComp::new(
            pure_sig(int()),
            TypedCompKind::Case(
                var("st", step_ty()),
                vec![
                    (done_pattern(), ret(var("acc", int()))),
                    (more_pattern("x", "rest"), more_body),
                ],
            ),
        );
        let crashy = TypedCoreFn::new(
            sym("crashy"),
            vec![
                TypedBinder::new(sym("s"), seq_ty()),
                TypedBinder::new(sym("acc"), int()),
            ],
            bind(force_app(var("s", seq_ty())), "st", step_ty(), case),
            CoreFnSig::new(Vec::new(), vec![seq_ty(), int()], pure_sig(int())),
            0,
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            bind(
                call("count", vec![lit(3), lit(10)], seq_ty()),
                "s",
                seq_ty(),
                call("crashy", vec![var("s", seq_ty()), lit(0)], int()),
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let (_, ticks) = assert_differential(vec![count_fn(), crashy, main], &step_env());
        assert_eq!(ticks, 0);
    }

    #[test]
    fn peel_crosses_lowered_representation_boundaries() {
        let wrapped = super::super::effect_lower::test_lowered_repr(
            lit(7),
            CoreType::Lowered(super::super::LoweredType::Word),
        );
        assert!(matches!(&peel(&wrapped).kind, TypedValueKind::Int(7)));
    }

    #[test]
    fn lowered_representation_cannot_hide_an_effectful_thunk() {
        let effectful_sig = CompSig::new(int(), EffRow::singleton(sym("Crash")));
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(effectful_sig.clone())),
            TypedValueKind::Thunk(Box::new(TypedComp::new(
                effectful_sig,
                TypedCompKind::Error(lit(0)),
            ))),
        );
        let wrapped = super::super::effect_lower::test_lowered_repr(
            thunk,
            CoreType::Lowered(super::super::LoweredType::Word),
        );
        let mut cx = purity_cx(Vec::new());

        assert!(!value_thunks_pure(&wrapped, &mut cx));
    }

    // Discovery starts at `a`: the old optimistic recursion breaker finalized
    // `b` as pure while `a` was provisionally true, then found `a`'s effect and
    // left the stale `b = true` memo behind. Both members share the SCC verdict.
    #[test]
    fn mutual_recursion_cannot_hide_a_sibling_effect() {
        let a = TypedCoreFn::new(
            sym("a"),
            Vec::new(),
            bind(
                call("b", Vec::new(), int()),
                "from_b",
                int(),
                TypedComp::new(pure_sig(int()), TypedCompKind::Error(lit(0))),
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let b = TypedCoreFn::new(
            sym("b"),
            Vec::new(),
            call("a", Vec::new(), int()),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let mut cx = purity_cx(vec![a, b]);

        assert!(!fn_pure(sym("a"), &mut cx));
        assert_eq!(cx.pure.get(&sym("a")), Some(&false));
        assert_eq!(cx.pure.get(&sym("b")), Some(&false));
    }

    #[test]
    fn pure_mutual_recursion_keeps_one_pure_scc_verdict() {
        let a = TypedCoreFn::new(
            sym("a"),
            Vec::new(),
            call("b", Vec::new(), int()),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let b = TypedCoreFn::new(
            sym("b"),
            Vec::new(),
            call("a", Vec::new(), int()),
            CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
            0,
        );
        let mut cx = purity_cx(vec![a, b]);

        assert!(fn_pure(sym("a"), &mut cx));
        assert_eq!(cx.pure.get(&sym("a")), Some(&true));
        assert_eq!(cx.pure.get(&sym("b")), Some(&true));
    }

    // Defense-in-depth guard, tested directly because no curated pipeline can
    // reach it: every tail-advance value residualized into a join body
    // references only the abstracted stream variables plus top-level functions
    // and literals, never a binder introduced during driving. The guard exists
    // so that if a future combinator shape breaks that invariant, the seed
    // silently degrades to not-fusing instead of emitting an open join (a
    // miscompile).
    #[test]
    fn scope_guard_refuses_a_leaked_local() {
        let p = sym("p0");
        let leaked = sym("leaked");
        let closed = ret(var("p0", int()));
        assert!(join_is_closed(&closed, &[p]));
        let open = ret(var("leaked", int()));
        assert!(!join_is_closed(&open, &[p]));
        let _ = leaked;
    }

    #[test]
    fn stream_equality_compares_float_bits() {
        let comb = sym("producer");
        let float = |x: f64| TypedValue::new(source(Type::Float), TypedValueKind::Float(x));
        let a = StreamExpr {
            comb,
            instantiation: Vec::new(),
            args: vec![Arg::Val(float(0.0))],
        };
        let b = StreamExpr {
            comb,
            instantiation: Vec::new(),
            args: vec![Arg::Val(float(-0.0))],
        };
        assert!(!stream_eq(&a, &b));
    }

    #[test]
    fn classify_rejects_changed_non_abstracted_float_bits() {
        let comb = sym("producer");
        let float = |x: f64| TypedValue::new(source(Type::Float), TypedValueKind::Float(x));
        let sym_seed = StreamExpr {
            comb,
            instantiation: Vec::new(),
            args: vec![Arg::Val(float(0.0))],
        };
        let tail = StreamExpr {
            comb,
            instantiation: Vec::new(),
            args: vec![Arg::Val(float(-0.0))],
        };
        assert!(classify(
            &sym_seed,
            &tail,
            &BTreeMap::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut BTreeMap::new(),
        )
        .is_none());
    }
}
