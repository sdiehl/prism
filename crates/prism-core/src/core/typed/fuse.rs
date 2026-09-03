//! Whole-program stream fusion for typed Core (pre-lowering, O2 and forced
//! Fuse).
//!
//! The pass recognizes a fusion seed (a self-recursive fold-shaped consumer
//! applied to a pipeline of known step-shaped combinators), drives one symbolic
//! production step through the pipeline (case-of-case cancelling every
//! intermediate `Step` cell), anti-unifies the seed against its one-step tail
//! to pick the advancing join parameters, and residualizes the knot into one
//! fresh top-level join function, redirecting the seed call. Every misfire
//! (unrecognized shape, effectful step, budget overrun, leaked local) degrades
//! to not fusing.
//!
//! Typed Core adds:
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

use crate::types::ty::EffRow;
use crate::types::Type;
use prism_common::sym::Sym;
use prism_syntax::names::{self, FRESH_FUSE};

use super::effect_lower::union_effects;
use super::facts::peel;
use super::inline::calls_in;
use super::specialize_support::{
    free_comp_vars, next_fresh, substitute_terms, substitute_witnesses, Rewrite,
};
use super::traverse::Visit;
use super::verify::substitute_core_type;
use super::{
    on_core_stack, CompSig, CoreFnSig, CoreInstantiation, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCore, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind,
    UncheckedTypedCore,
};

mod cleanup;
mod plan;
mod recognize;

use cleanup::{copy_prop, dead_let_elim, subst};
use plan::build_join;
#[cfg(test)]
use plan::{classify, join_is_closed, stream_eq};
use recognize::{comp_pure, resolve_consumer, resolve_stream, stream_pure, stream_role, Consumer};
#[cfg(test)]
use recognize::{fn_pure, forced_params, value_pure, value_thunks_pure};

// A seed whose symbolic driving takes more than this many reduction steps aborts
// to not-fusing. Matches the legacy budget exactly.
const UNFOLD_BUDGET: u32 = 4000;
// A driven `Step` tree larger than this many nodes aborts to not-fusing.
// Matches the legacy budget exactly.
const SIZE_BUDGET: usize = 20_000;

/// Rewrite counts for typed stream fusion.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FuseStats {
    ticks: u64,
}

impl FuseStats {
    /// Seeds fused (joins emitted).
    pub const fn ticks(self) -> u64 {
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
#[must_use]
pub fn fuse<P>(core: TypedCore<P>) -> (UncheckedTypedCore<P>, FuseStats) {
    on_core_stack(|| fuse_on_core_stack(core))
}

fn fuse_on_core_stack<P>(core: TypedCore<P>) -> (UncheckedTypedCore<P>, FuseStats) {
    let source_functions = core.into_unchecked().into_functions();
    let mut cx = Cx {
        fns: source_functions
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
    let mut fns: Vec<TypedCoreFn> = source_functions
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
    (UncheckedTypedCore::new(fns), FuseStats { ticks })
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

#[cfg(test)]
mod tests;
