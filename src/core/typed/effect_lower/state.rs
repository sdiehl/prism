//! State fusion: the fold-uniformity gate.
//!
//! A fold consumer handles its operation by parameter passing, so its clause is
//! not tail-resumptive and the [evidence](super::evidence) engine cannot take it.
//! This engine instead compiles the chain to an explicit left fold, threading the
//! accumulator through every producer. What lands here is the gate that decides
//! whether a program is shaped for that at all; the threading itself follows.
//!
//! ## Neutral shape judgments and witness-preserving rewrites
//!
//! A helper belongs in the neutral shape layer exactly when it **answers a
//! question about the shape of a term**, because the shape of a term is what
//! erasure preserves.
//!
//! `is_fold`, `is_id_return`, `is_id_transformer`, and `is_state_transformer`
//! answer. They take no compiler state: they read a clause and its `ResumeUse`
//! and return a verdict. So they are called on an erased clone, as
//! [`super::erase_var`] does to classify multishot resumption through the
//! canonical [`CheckedHandler`](crate::core::CheckedHandler).
//!
//! [`strip_state`] cannot live in that layer because it returns a *rewritten
//! clause body*: an erased rewrite has dropped exactly the witnesses this tree
//! exists to carry. [`produces`] and [`value_coincident`] also stay here because
//! they ask about latent effects and thunk flow, which require the typed tree.
//!
//! Where a rewrite recomputes something a neutral predicate already knows, the
//! two are cross-checked: [`strip_state`] reports the kind it derived, and its
//! caller checks that against what `is_fold` reports for the same clause.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::effect_shape::{
    is_fold, is_id_return, is_id_transformer, is_state_transformer, FoldAKind,
};
use crate::names::{self, STATE_ACC};
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;

use super::super::specialize_support::free_comp_vars;
use super::super::specialize_support::free_value_vars;
use super::super::verify::VerifyEnv;
use super::super::TypedPattern;
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedHandleOp,
};
use super::diagnostics::DriftLog;
use super::erase_control::StepAt;
use super::evidence::OpIds;
use super::evidence::Retyped;
use super::flow::{self, Loc, Sig, ThunkFlow};
use super::latent::Latent;
use super::walk::{collect_ops, each_subcomp, each_subterm};
use super::{TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum EarlyExitMode {
    Continue,
    ShortCircuit,
}

impl EarlyExitMode {
    const fn short_circuits(self) -> bool {
        matches!(self, Self::ShortCircuit)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum StateAnswerMode {
    Accumulator,
    Producer,
}

fn bound_producer_result(
    answer: StateAnswerMode,
    tail: Option<FoldAKind>,
    accumulator: &TypedBinder,
    result: &CoreType,
) -> Option<TypedValue> {
    match tail {
        Some(FoldAKind::Acc) => Some(super::binder_var(accumulator)),
        Some(FoldAKind::Unit) => Some(super::unit_value()),
        None if answer == StateAnswerMode::Producer => None,
        None => {
            assert_eq!(
                result,
                &CoreType::Source(Type::Unit),
                "an accumulator-answer state plan can only bind an unclassified producer result \
                 when that result is Unit"
            );
            Some(super::unit_value())
        }
    }
}

/// What the gate decided: which operations stream, how each fold clause resumes,
/// the answer convention the threading needs, and what each read pins the
/// accumulator to.
///
/// Returning these facts keeps the analysis from having a hidden channel into
/// the rewrite, as the evidence prepass does.
#[derive(Debug)]
pub(super) struct FoldPlan {
    /// The operations streamed through fold, forward, control, and take handlers.
    pub(super) ops: BTreeSet<Sym>,
    /// Per fold clause, the value its tail resumes with.
    pub(super) kinds: BTreeMap<Sym, FoldAKind>,
    /// Whether the threaded loop's accumulator is the program's answer.
    pub(super) answer: StateAnswerMode,
    /// Whether any handler terminates the stream early.
    pub(super) early: EarlyExitMode,
    /// The type each operation whose fold clause resumes with the accumulator
    /// pins it to. Operations nothing reads do not appear.
    pins: BTreeMap<Sym, CoreType>,
}

impl FoldPlan {
    /// How a producer latent in `ops` types the accumulator it threads.
    ///
    /// The question is asked per producer rather than per program because a
    /// program may fuse several independent chains, and nothing ties their
    /// accumulators together: one may thread an `Int` while another threads a
    /// list. `None` when one producer's own operations pin its single threaded
    /// accumulator to two types, which no producer can satisfy.
    pub(super) fn accumulator_for(&self, ops: &BTreeSet<Sym>) -> Option<Accumulator> {
        let mut pinned: Option<&CoreType> = None;
        for ty in ops.iter().filter_map(|op| self.pins.get(op)) {
            match pinned {
                Some(existing) if existing != ty => return None,
                _ => pinned = Some(ty),
            }
        }
        Some(pinned.map_or(Accumulator::Free, |ty| Accumulator::Pinned(ty.clone())))
    }
}

/// Stable whole-program authorities shared by State recognition and threading.
/// A strategy may select only some operations, but it must keep the prepared
/// program's numbering and analyses at every gate and rewrite site.
pub(super) struct StateAnalysis<'a> {
    ids: &'a OpIds,
    latent: &'a Latent,
    flow: &'a ThunkFlow,
    env: &'a VerifyEnv,
}

impl<'a> StateAnalysis<'a> {
    pub(super) const fn new(
        ids: &'a OpIds,
        latent: &'a Latent,
        flow: &'a ThunkFlow,
        env: &'a VerifyEnv,
    ) -> Self {
        Self {
            ids,
            latent,
            flow,
            env,
        }
    }
}

/// How the threaded accumulator is typed, which decides whether a producer
/// gains a state type quantifier or a concrete state type.
///
/// The untyped pass never had to ask: it threads a `st@` parameter whose type
/// nothing records. Both answers are real in the corpus, so a port that assumes
/// either one alone is wrong, and the answer belongs to a producer rather than
/// to the program: independent chains thread their own accumulators at their
/// own types.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum Accumulator {
    /// No producer ever observes the accumulator, so every producer is
    /// parametric in it and gains a state type quantifier instantiated at each
    /// call site. This is what lets one stream producer feed two chains at two
    /// accumulator types in a single program (`ssum` folds into an `Int`,
    /// `scollect` into a list, and both force the same producer).
    Free,
    /// A read clause resumes with the accumulator itself, so the operation's
    /// declared result *is* the accumulator and pins its type. A producer that
    /// reads then observes the accumulator at that type (a `get` feeding
    /// `st@ + 1`), and a quantifier would make the body unverifiable.
    Pinned(CoreType),
}

/// The type each read operation pins the accumulator to: a fold clause that
/// resumes with the accumulator resumes with the operation's declared result, so
/// that result *is* the accumulator wherever the operation streams.
fn pins(kinds: &BTreeMap<Sym, FoldAKind>, env: &VerifyEnv) -> Option<BTreeMap<Sym, CoreType>> {
    kinds
        .iter()
        .filter(|(_, kind)| **kind == FoldAKind::Acc)
        .map(|(op, _)| Some((*op, env.operation(*op)?.result().clone())))
        .collect()
}

/// What a producer's signature gains when it is threaded, and in what order.
///
/// The order is a contract between three sites that are rewritten separately: a
/// producer's declaration, every call to it, and the accumulator's own type. It
/// is fixed here so they cannot disagree.
#[derive(Debug)]
pub(super) struct ProducerPlan {
    /// The ambient residual row, last in the quantifier list so an existing
    /// instantiation's positional arguments do not move.
    pub(super) ambient: Sym,
    /// The evidence this producer takes, one per fused operation in ascending
    /// operation-id order, which is the one order evidence is ever laid out in.
    pub(super) evidence: Vec<TypedBinder>,
    /// The trailing accumulator parameter, after the evidence.
    pub(super) accumulator: TypedBinder,
    /// The threaded scheme: the original quantifiers, then the state type when
    /// the accumulator is free, then the ambient row.
    pub(super) quantifiers: Vec<CoreQuantifier>,
    /// The one `Step` instantiation this producer threads under in an
    /// early-exit program, decided here with the accumulator so declaration,
    /// guards, patterns and evidence cannot disagree.
    pub(super) step: Option<StepAt>,
}

impl ProducerPlan {
    /// The threaded parameter list: the producer's own, then its evidence, then
    /// the accumulator.
    pub(super) fn params(&self, declared: &[TypedBinder]) -> Vec<TypedBinder> {
        let mut params = declared.to_vec();
        params.extend(self.evidence.iter().cloned());
        params.push(self.accumulator.clone());
        params
    }
}

/// Plan the signature of a producer latent in `ops`.
///
/// `None` when the accumulator cannot be typed, which is the one thing that can
/// fail here: everything else is derived.
fn plan_producer(
    f: &TypedCoreFn,
    ops: &BTreeSet<Sym>,
    plan: &FoldPlan,
    ids: &OpIds,
    fns: &[TypedCoreFn],
    latent: &Latent,
    env: &VerifyEnv,
) -> Option<ProducerPlan> {
    let numbered: Vec<i64> = {
        let mut numbered: Vec<i64> = ops.iter().map(|op| ids.id(*op)).collect::<Option<_>>()?;
        numbered.sort_unstable();
        numbered
    };
    let ambient = Sym::from(names::evidence_row(&numbered));

    let (accumulator, state, step) = accumulator_type(plan, ops, &numbered)?;

    let evidence: Vec<TypedBinder> = numbered
        .iter()
        .map(|id| {
            let op = ids.op(*id)?;
            let inst =
                lexical_instantiation(f.body(), op, fns, latent, LEXICAL_DEPTH).unwrap_or_default();
            Some(TypedBinder::new(
                Sym::from(names::ev(*id)),
                clause_type(op, &accumulator, &EffRow::Var(ambient), &inst, env)?,
            ))
        })
        .collect::<Option<_>>()?;

    let mut quantifiers = f.sig().quantifiers().to_vec();
    quantifiers.extend(state.map(CoreQuantifier::Type));
    quantifiers.push(CoreQuantifier::Row(ambient));

    Some(ProducerPlan {
        ambient,
        evidence,
        accumulator: TypedBinder::new(Sym::from(STATE_ACC), accumulator),
        quantifiers,
        step,
    })
}

/// How the accumulator threaded by a producer over `ops` is typed, and the state
/// quantifier it introduces when nothing observes it.
///
/// A free accumulator is one every producer is parametric in, so it needs a
/// quantifier that a producer's declaration and a caller's nested thunk type can
/// both name without sharing a counter. That is what deriving the name from the
/// operation ids buys, exactly as the ambient row does.
///
/// One home for the question, because the threading asks it at each perform site
/// and the signature planner asks it once per producer, and an evidence type that
/// disagreed with the accumulator it is applied to would typecheck nowhere.
fn accumulator_type(
    plan: &FoldPlan,
    ops: &BTreeSet<Sym>,
    numbered: &[i64],
) -> Option<(CoreType, Option<Sym>, Option<StepAt>)> {
    let (base, state) = match plan.accumulator_for(ops)? {
        Accumulator::Pinned(ty) => (ty, None),
        Accumulator::Free => {
            let name = Sym::from(names::state_type(numbered));
            (CoreType::Source(Type::Var(name)), Some(name))
        }
    };
    // In an early-exit program the threaded accumulator is `Step Base`
    // everywhere a producer declares or a thunk carries it. One home for the
    // wrap; the callers that need the base (instantiation sites) read it from
    // the returned Step.
    if plan.early.short_circuits() {
        let source = super::super::build::source_type(&base).ok()?;
        let at = StepAt::new(source.clone(), source);
        Some((at.ty(), state, Some(at)))
    } else {
        Some((base, state, None))
    }
}

/// How many forwarding calls a lexical edge is followed through before the
/// harvest gives up: producers that only wrap other producers are shallow, and
/// a recursive producer performs directly, so this bounds pathology, not the
/// corpus.
const LEXICAL_DEPTH: u8 = 8;

/// The instantiation `op` is used at along this lexical edge: a direct perform
/// inside `c`, or, when `c` only forwards to a producer, that producer's own
/// lexical instantiation carried back through the call's type arguments.
///
/// This is what makes evidence types a property of the edge rather than of the
/// program: a mapped stream's source and target clauses need not share a type
/// merely because they implement the same operation, and a wrapper with no
/// perform of its own still types its evidence by the producer it forces.
fn lexical_instantiation(
    c: &TypedComp,
    op: Sym,
    fns: &[TypedCoreFn],
    latent: &Latent,
    depth: u8,
) -> Option<Vec<CoreInstantiation>> {
    fn visit(c: &TypedComp, f: &mut impl FnMut(&TypedComp)) {
        f(c);
        each_subterm(c, &mut |sc| visit(sc, f));
    }
    if depth == 0 {
        return None;
    }
    if let Some(direct) = perform_instantiation(c, op) {
        if !direct.is_empty() {
            return Some(direct);
        }
    } else {
        // Two direct performs disagreeing inside one lexical slot: no single
        // clause can serve them.
        return None;
    }
    // No direct perform: follow the first call to a producer latent in the
    // operation, substituting the call's type arguments into that producer's
    // own lexical instantiation.
    let mut out: Option<Vec<CoreInstantiation>> = None;
    let mut walk = |sc: &TypedComp| {
        if out.is_some() {
            return;
        }
        if let TypedCompKind::Call {
            callee,
            instantiation,
            ..
        } = sc.kind()
        {
            let latent_in_op = latent
                .get(callee)
                .is_some_and(|set| set.iter().any(|m| m.id == op));
            if !latent_in_op {
                return;
            }
            let Some(target) = fns.iter().find(|f| f.name() == *callee) else {
                return;
            };
            let Some(inner) = lexical_instantiation(target.body(), op, fns, latent, depth - 1)
            else {
                return;
            };
            let quantifiers = target.sig().quantifiers();
            // A substitution that leaves the source language cannot name the
            // instantiation; the edge stays generic rather than inventing one.
            out = inner
                .into_iter()
                .map(|inst| match inst {
                    CoreInstantiation::Type(t) => {
                        let substituted = super::super::verify::substitute_core_type(
                            &CoreType::Source(t),
                            quantifiers,
                            instantiation,
                        );
                        super::super::build::source_type(&substituted)
                            .ok()
                            .map(CoreInstantiation::Type)
                    }
                    CoreInstantiation::Row(row) => Some(CoreInstantiation::Row(
                        super::super::verify::substitute_row(&row, quantifiers, instantiation),
                    )),
                })
                .collect::<Option<Vec<_>>>();
        }
    };
    visit(c, &mut walk);
    out.or(Some(Vec::new()))
}

/// The one instantiation `op` is performed at inside `c`, or `None` when it is
/// never performed or performed at two different instantiations, which one
/// shared clause cannot serve.
fn perform_instantiation(c: &TypedComp, op: Sym) -> Option<Vec<CoreInstantiation>> {
    fn walk(
        c: &TypedComp,
        op: Sym,
        found: &mut Option<Vec<CoreInstantiation>>,
        conflicted: &mut bool,
    ) {
        if let TypedCompKind::Do {
            operation,
            instantiation,
            ..
        } = c.kind()
        {
            if *operation == op {
                match found {
                    Some(existing) if existing != instantiation => *conflicted = true,
                    _ => *found = Some(instantiation.clone()),
                }
            }
        }
        each_subterm(c, &mut |sc| walk(sc, op, found, conflicted));
    }
    let mut found: Option<Vec<CoreInstantiation>> = None;
    let mut conflicted = false;
    walk(c, op, &mut found, &mut conflicted);
    if conflicted {
        return None;
    }
    Some(found.unwrap_or_default())
}

/// The type an escaping producer thunk has once it is threaded: its own
/// parameters, then one clause per fused operation it performs, then the
/// accumulator, returning the accumulator, with the state quantifier (when
/// nothing pins the accumulator) and the ambient row bound inside the thunk's
/// own type.
///
/// Bound inside rather than on the enclosing function because it is the force
/// site, in another function entirely, that instantiates them, and the two
/// sides can only agree on names derived from the operations themselves.
///
/// One home for the transform: the thunk value's rewrite and the declared type
/// of every parameter such a thunk is passed to must produce the same type, or
/// the callee's witness and its callers disagree.
/// The arguments the row carries for the effect named `name`, or empty when
/// the label is absent or bare.
fn label_args(row: &EffRow, name: Sym) -> Vec<Type> {
    let mut cur = row;
    loop {
        match cur {
            EffRow::Extend(label, rest) => {
                if label.name == name {
                    return label.args.clone();
                }
                cur = rest;
            }
            _ => return Vec::new(),
        }
    }
}

fn threaded_thunk_type(
    declared: &CoreType,
    ops: &BTreeSet<Sym>,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Option<CoreType> {
    let mut numbered: Vec<i64> = ops.iter().map(|op| ids.id(*op)).collect::<Option<_>>()?;
    numbered.sort_unstable();
    let (acc, state, _step) = accumulator_type(plan, ops, &numbered)?;
    let ambient = Sym::from(names::evidence_row(&numbered));
    let CoreType::Thunk(inner) = declared else {
        return None;
    };
    let CoreType::Function(fun) = inner.result() else {
        return None;
    };
    let mut params = fun.params().to_vec();
    for id in &numbered {
        let op = ids.op(*id)?;
        // The parameter's own pre-threading row names the instantiation: the
        // effect label it carries (`Emit(b)` in `() -> a ! {Emit(b) | e}`)
        // holds the operation's type arguments in the receiving function's own
        // scheme vocabulary. Declarations own their indices; every incoming
        // edge substitutes at use. No caller is consulted.
        // An absent label supplies no binding relationship. In particular, a
        // same-named outer quantifier is not evidence that it instantiates the
        // operation scheme; leave the clause generic rather than guessing.
        let inst: Vec<CoreInstantiation> = env
            .operation(op)
            .map(|sig| label_args(fun.body().effects(), sig.effect().name))
            .unwrap_or_default()
            .into_iter()
            .map(CoreInstantiation::Type)
            .collect();
        params.push(clause_type(op, &acc, &EffRow::Var(ambient), &inst, env)?);
    }
    params.push(acc.clone());
    let mut quantifiers = fun.quantifiers().to_vec();
    quantifiers.extend(state.map(CoreQuantifier::Type));
    quantifiers.push(CoreQuantifier::Row(ambient));
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            quantifiers,
            params,
            CompSig::new(acc, EffRow::Var(ambient)),
        ))),
        EffRow::Empty,
    ))))
}

/// The type of a fused operation's evidence: its clause, which takes the
/// operation's own arguments and the accumulator, and returns the next
/// accumulator.
///
/// Unlike an [evidence](super::evidence) clause, this is never padded with a
/// unit parameter when the operation is nullary: the accumulator is appended to
/// every clause, so a nullary operation's clause already takes one argument, and
/// a padded one would take an argument the perform site does not pass.
fn clause_type(
    op: Sym,
    accumulator: &CoreType,
    row: &EffRow,
    instantiation: &[CoreInstantiation],
    env: &VerifyEnv,
) -> Option<CoreType> {
    let sig = env.operation(op)?;
    // A polymorphic operation's clause is used at the perform sites'
    // instantiation, so its type is the scheme applied there where the sites
    // agree on one: an inner re-quantified scheme would shadow whatever the
    // enclosing signature binds, and the argument that actually arrives is the
    // handler's concrete clause. Where no single instantiation exists, the
    // generic scheme is kept rather than declining a program the executable
    // pass fuses; the ratchet reports what that costs.
    let (quantifiers, op_params) = super::super::verify::instantiate_fn(
        &CoreFnSig::new(
            sig.quantifiers().to_vec(),
            sig.params().to_vec(),
            CompSig::new(sig.result().clone(), EffRow::Empty),
        ),
        instantiation,
    )
    .map_or_else(
        |_| (sig.quantifiers().to_vec(), sig.params().to_vec()),
        |applied| (Vec::new(), applied.params().to_vec()),
    );
    let mut params = op_params;
    params.push(accumulator.clone());
    let clause = CoreFnSig::new(
        quantifiers,
        params,
        CompSig::new(accumulator.clone(), row.clone()),
    );
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(clause)),
        EffRow::Empty,
    ))))
}

/// Thread a whole fold-uniform program: every producer gains its evidence and
/// accumulator, and everything else is rewritten around them.
///
/// `None` wherever the typed state rung cannot preserve its fusion contract.
pub(super) fn thread_program(
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    analysis: &StateAnalysis<'_>,
    drift: &DriftLog,
    fresh: &mut crate::util::fresh::Fresh,
) -> Option<Vec<TypedCoreFn>> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
    } = analysis;
    // The canonical evidence name per fused operation. A forwarding handler
    // shadows one of these for its source; nothing else rebinds them.
    let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
    for op in &plan.ops {
        evs.insert(*op, Sym::from(names::ev(ids.id(*op)?)));
    }

    let mut threader = Threader {
        plan,
        ids,
        env,
        latent,
        flow,
        drift,
        retyped: Retyped::new(),
        evidence_types: BTreeMap::new(),
        signatures: BTreeMap::new(),
        step: None,
        row: EffRow::Empty,
        fresh,
    };
    // Signature prepass: every call site rebuilds from its callee's
    // transformed signature, so those signatures exist before any body does.
    for f in fns {
        let sigs = flow.param.get(&f.name())?;
        let mut param_tys: Vec<CoreType> = f.sig().params().to_vec();
        for (index, sig) in sigs.iter().enumerate() {
            let carried: BTreeSet<Sym> = sig
                .iter()
                .map(|m| m.id)
                .filter(|id| plan.ops.contains(id))
                .collect();
            if carried.is_empty() {
                continue;
            }
            let declared = param_tys.get(index)?;
            param_tys[index] = threaded_thunk_type(declared, &carried, plan, ids, env)?;
        }
        let ops = producer_ops(f, &plan.ops, latent);
        let new_sig = if ops.is_empty() {
            // A consumer: residual row, and a result that follows its returned
            // thunk when the flow says the result carries fused operations.
            let mut residual = f.sig().body().effects().clone();
            for op in &plan.ops {
                if let Some(operation) = env.operation(*op) {
                    residual = super::subtract::subtract_row(&residual, operation.effect().name);
                }
            }
            let ret_ops: BTreeSet<Sym> = flow
                .ret
                .get(&f.name())
                .map(|s| {
                    s.iter()
                        .map(|m| m.id)
                        .filter(|id| plan.ops.contains(id))
                        .collect()
                })
                .unwrap_or_default();
            let result = if ret_ops.is_empty() {
                f.sig().body().result().clone()
            } else {
                threaded_thunk_type(f.sig().body().result(), &ret_ops, plan, ids, env)?
            };
            CoreFnSig::new(
                f.sig().quantifiers().to_vec(),
                param_tys,
                CompSig::new(result, residual),
            )
        } else {
            let producer = plan_producer(f, &ops, plan, ids, fns, latent, env)?;
            let mut all = param_tys;
            all.extend(producer.evidence.iter().map(|b| b.ty().clone()));
            all.push(producer.accumulator.ty().clone());
            CoreFnSig::new(
                producer.quantifiers.clone(),
                all,
                CompSig::new(
                    producer.accumulator.ty().clone(),
                    EffRow::Var(producer.ambient),
                ),
            )
        };
        threader.signatures.insert(f.name(), new_sig);
    }

    let mut out = Vec::with_capacity(fns.len());
    for f in fns {
        let loc: Loc = f
            .params()
            .iter()
            .map(TypedBinder::name)
            .zip(flow.param.get(&f.name())?.iter().cloned())
            .collect();
        let ops = producer_ops(f, &plan.ops, latent);
        threader.evidence_types.clear();
        // Source binder names are lexical, so the retype map is
        // declaration-local: a widened `g` from one instance method must not
        // leak into the next method's differently-shaped `g`.
        threader.retyped = Retyped::new();
        // A thunk-valued parameter that performs a fused operation arrives
        // already threaded whoever receives it, producer or consumer: its
        // declared type is the threaded thunk type, and every read of that
        // parameter follows it.
        let sigs = flow.param.get(&f.name())?;
        let mut params = f.params().to_vec();
        for (index, sig) in sigs.iter().enumerate() {
            let carried: BTreeSet<Sym> = sig
                .iter()
                .map(|m| m.id)
                .filter(|id| plan.ops.contains(id))
                .collect();
            if carried.is_empty() {
                continue;
            }
            let declared = params.get(index)?;
            let widened = threaded_thunk_type(declared.ty(), &carried, plan, ids, env)?;
            threader.retyped.insert(declared.name(), widened.clone());
            params[index] = TypedBinder::new(declared.name(), widened);
        }
        let lowered = if ops.is_empty() {
            let body = threader.rewrite(f.body(), &loc, &evs)?;
            // A consumer's declared row is its original row with the discharged
            // effects subtracted, not whatever its rewritten tail locally
            // reports: the handle removed exactly those labels, and every call
            // site's expectation is computed from this signature.
            let mut residual = f.sig().body().effects().clone();
            for op in &plan.ops {
                if let Some(operation) = env.operation(*op) {
                    residual = super::subtract::subtract_row(&residual, operation.effect().name);
                }
            }
            let sig = CoreFnSig::new(
                f.sig().quantifiers().to_vec(),
                params.iter().map(|p| p.ty().clone()).collect(),
                CompSig::new(body.sig().result().clone(), residual),
            );
            TypedCoreFn::new(f.name(), params, body, sig, f.dict_arity())
        } else {
            let producer = plan_producer(f, &ops, plan, ids, fns, latent, env)?;
            let producer_evs: BTreeMap<Sym, Sym> = evs
                .iter()
                .filter(|(operation, _)| ops.contains(operation))
                .map(|(operation, evidence)| (*operation, *evidence))
                .collect();
            for binder in &producer.evidence {
                threader
                    .evidence_types
                    .insert(binder.name(), binder.ty().clone());
            }
            threader.row = EffRow::Var(producer.ambient);
            // A top-level producer in an early-exit program threads a stepped
            // accumulator, and its guards consume the same one Step decision a
            // handle scope would have published for it.
            threader.step.clone_from(&producer.step);
            let body = threader.thread_st(f.body(), &producer_evs, &loc, &producer.accumulator)?;
            threader.step = None;
            threader.row = EffRow::Empty;
            let params = producer.params(&params);
            // The declared row is the ambient variable, whatever the body's
            // final node locally says: the residual of a threaded producer
            // rides its ambient quantifier, and a caller instantiates it away.
            let sig = CoreFnSig::new(
                producer.quantifiers.clone(),
                params.iter().map(|p| p.ty().clone()).collect(),
                CompSig::new(body.sig().result().clone(), EffRow::Var(producer.ambient)),
            );
            TypedCoreFn::new(f.name(), params, body, sig, f.dict_arity())
        };
        out.push(lowered);
    }
    Some(out)
}

/// Rewrite a fold clause's tail `k(A)(B)` to `return B`, dropping the resume
/// binder, and report what the resume value was: unit for a write, the
/// accumulator for a read.
///
/// The neutral clause-shape predicates answer a question, and erasure preserves
/// everything they read; this returns a rewritten clause body, and an erased
/// rewrite has dropped exactly the witnesses the typed tree carries. The kind
/// computed here is therefore cross-checked against [`is_fold`] by the caller.
///
/// `None` when the clause is not state-tail-resumptive, when the resume value is
/// outside the admitted set, or when branches disagree on the kind.
fn strip_state(c: &TypedComp, aliases: &BTreeSet<Sym>, acc: Sym) -> Option<(TypedComp, FoldAKind)> {
    strip_state_go(c, aliases, acc, &BTreeMap::new())
}

/// `subst` accumulates the pure `return v to x` aliases seen so far, so a resume
/// argument that is itself an A-normal-form binder (`return s to t; k(t)(..)`)
/// resolves back to the accumulator before its kind is classified.
fn strip_state_go(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    acc: Sym,
    subst: &BTreeMap<Sym, TypedValue>,
) -> Option<(TypedComp, FoldAKind)> {
    match c.kind() {
        TypedCompKind::Bind(m, x, n) => {
            // Drop a rebinding of the resume (`return k to k'`).
            if let TypedCompKind::Return(v) = m.kind() {
                if super::as_var(v).is_some_and(|v| aliases.contains(&v)) {
                    let mut a2 = aliases.clone();
                    a2.insert(x.name());
                    return strip_state_go(n, &a2, acc, subst);
                }
            }
            // The double application: `m` computes the resumption `k(A)` and binds
            // it to `x`, and the tail `n` applies that to the new accumulator `B`.
            if let Some(a) = resume_arg(m, aliases, subst) {
                let kind = a_kind(&a, acc)?;
                let TypedCompKind::App { callee, args, .. } = n.kind() else {
                    return None;
                };
                if !matches!(callee.kind(), TypedCompKind::Force(k)
                    if super::as_var(k) == Some(x.name()))
                {
                    return None;
                }
                let [ns] = args.as_slice() else {
                    return None;
                };
                if !free_value_vars(ns).is_disjoint(aliases) {
                    return None;
                }
                return Some((
                    TypedComp::new(
                        CompSig::new(ns.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(ns.clone()),
                    ),
                    kind,
                ));
            }
            // A pure leading bind (the `f(acc, x)` block): keep it, record any
            // value alias for resolving the resume argument, and thread on.
            if !free_comp_vars(m).is_disjoint(aliases) {
                return None;
            }
            let mut subst2 = subst.clone();
            if let TypedCompKind::Return(v) = m.kind() {
                subst2.insert(x.name(), v.clone());
            }
            let (tail, kind) = strip_state_go(n, aliases, acc, &subst2)?;
            Some((
                TypedComp::new(
                    tail.sig().clone(),
                    TypedCompKind::Bind(m.clone(), x.clone(), Box::new(tail)),
                ),
                kind,
            ))
        }
        TypedCompKind::If(v, t, e) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let (tt, kt) = strip_state_go(t, aliases, acc, subst)?;
            let (te, ke) = strip_state_go(e, aliases, acc, subst)?;
            if kt != ke {
                return None;
            }
            Some((
                TypedComp::new(
                    tt.sig().clone(),
                    TypedCompKind::If(v.clone(), Box::new(tt), Box::new(te)),
                ),
                kt,
            ))
        }
        TypedCompKind::Case(v, arms) => {
            if !free_value_vars(v).is_disjoint(aliases) {
                return None;
            }
            let mut kind: Option<FoldAKind> = None;
            let mut out = Vec::with_capacity(arms.len());
            for (p, b) in arms {
                let (tb, kb) = strip_state_go(b, aliases, acc, subst)?;
                match kind {
                    Some(k) if k != kb => return None,
                    _ => kind = Some(kb),
                }
                out.push((p.clone(), tb));
            }
            let sig = out.first().map(|(_, b)| b.sig().clone())?;
            Some((
                TypedComp::new(sig, TypedCompKind::Case(v.clone(), out)),
                kind?,
            ))
        }
        _ => None,
    }
}

/// The argument of `g(n)` when a computation evaluates to a unary application
/// of `g` through A-normal-form binds, the seed resolved to its source value.
fn anf_app_arg(g: Sym, c: &TypedComp) -> Option<TypedValue> {
    let mut subst: BTreeMap<Sym, TypedValue> = BTreeMap::new();
    let mut cur = c;
    loop {
        match cur.kind() {
            TypedCompKind::Bind(m, x, n) => {
                let TypedCompKind::Return(v) = m.kind() else {
                    return None;
                };
                subst.insert(x.name(), v.clone());
                cur = n;
            }
            TypedCompKind::App { callee, args, .. } => {
                let TypedCompKind::Force(v) = callee.kind() else {
                    return None;
                };
                let name = super::as_var(v)?;
                let resolved = super::as_var(&resolve(
                    &super::binder_var(&TypedBinder::new(name, v.ty().clone())),
                    &subst,
                ))
                .unwrap_or(name);
                if resolved != g {
                    return None;
                }
                let [a] = args.as_slice() else {
                    return None;
                };
                return Some(resolve(a, &subst));
            }
            _ => return None,
        }
    }
}

/// Whether a computation's head rebinds a live resume alias.
fn is_alias_return(m: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    matches!(m.kind(), TypedCompKind::Return(v)
        if super::as_var(v).is_some_and(|v| aliases.contains(&v)))
}

/// Whether a computation evaluates to `resume(rv)` for one argument disjoint
/// from the aliases.
fn resume_call(c: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    resume_arg(c, aliases, &BTreeMap::new()).is_some()
}

/// Classify a resume value against the fold lambda's accumulator parameter.
fn a_kind(a: &TypedValue, acc: Sym) -> Option<FoldAKind> {
    match &super::peel(a).kind {
        TypedValueKind::Unit => Some(FoldAKind::Unit),
        TypedValueKind::Var { name, .. } if *name == acc => Some(FoldAKind::Acc),
        _ => None,
    }
}

/// The argument of `resume(rv)` when a computation evaluates to a unary
/// application of a resume alias, allowing leading pure binds and resume
/// rebindings. The argument must be disjoint from the aliases, since it is not
/// the resume itself.
fn resume_arg(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    subst: &BTreeMap<Sym, TypedValue>,
) -> Option<TypedValue> {
    match c.kind() {
        TypedCompKind::App { callee, args, .. } => {
            if !matches!(callee.kind(), TypedCompKind::Force(k)
                if super::as_var(k).is_some_and(|k| aliases.contains(&k)))
            {
                return None;
            }
            let [rv] = args.as_slice() else {
                return None;
            };
            free_value_vars(rv)
                .is_disjoint(aliases)
                .then(|| resolve(rv, subst))
        }
        TypedCompKind::Bind(m, x, n) => {
            if let TypedCompKind::Return(v) = m.kind() {
                if super::as_var(v).is_some_and(|v| aliases.contains(&v)) {
                    let mut a2 = aliases.clone();
                    a2.insert(x.name());
                    return resume_arg(n, &a2, subst);
                }
            }
            if !free_comp_vars(m).is_disjoint(aliases) {
                return None;
            }
            let mut s2 = subst.clone();
            if let TypedCompKind::Return(v) = m.kind() {
                s2.insert(x.name(), v.clone());
            }
            resume_arg(n, aliases, &s2)
        }
        _ => None,
    }
}

/// Resolve a value through the pure binds seen so far, so an A-normal-form
/// binder resolves back to what it was bound to.
fn resolve(v: &TypedValue, subst: &BTreeMap<Sym, TypedValue>) -> TypedValue {
    super::as_var(v)
        .and_then(|name| subst.get(&name))
        .map_or_else(|| v.clone(), Clone::clone)
}

/// The producer-side rewrite: walk a producer body and fold every operation head
/// into the active evidence, so the body becomes a computation returning the
/// accumulator.
pub(super) struct Threader<'a> {
    pub(super) plan: &'a FoldPlan,
    /// The whole program's operation numbering. A fused subset keeps its global
    /// holes; renumbering it locally would violate the canonical ABI after
    /// strategies compose.
    pub(super) ids: &'a OpIds,
    pub(super) env: &'a VerifyEnv,
    pub(super) latent: &'a Latent,
    pub(super) flow: &'a ThunkFlow,
    /// Where a clause that almost matches a recognized shape is reported. It is
    /// an observable side channel, so it is the caller's log, never a fresh one:
    /// a local log would silently swallow a warning.
    pub(super) drift: &'a DriftLog,
    /// The locals whose type the threading has changed: a binder holding an
    /// escaping producer thunk changes type when the thunk gains its evidence
    /// and accumulator, and every read of it must change with it.
    pub(super) retyped: Retyped,
    /// The evidence binders actually in scope, by name: a producer's own
    /// parameters, or the local binds a handle introduced. Fabricating a type
    /// a second time at a use site is how a witness drifts from its binder.
    pub(super) evidence_types: BTreeMap<Sym, CoreType>,
    /// Every function's transformed signature, computed before any body is
    /// rewritten: the authority a call site rebuilds its result and arguments
    /// from. Reading the pre-threading witness at a call, or retagging its
    /// leaves toward what a consumer expects, is how stale results survive.
    pub(super) signatures: BTreeMap<Sym, CoreFnSig>,
    /// The one `Step` instantiation live in the scope being threaded, decided
    /// where the early-exit protocol is entered (a handle in early mode, a
    /// take) and consumed by every guard, lift, unwrap, constructor and
    /// pattern inside that scope. One builder owns each representation fact;
    /// reconstructing `Step(acc, acc)` at a use site from whatever type is
    /// nearby is how the take witnesses drifted.
    pub(super) step: Option<StepAt>,
    /// The residual row where the threading currently runs: the producer's own
    /// ambient variable inside a producer, and the handle's residual at a
    /// handle site. Evidence types and call-site instantiations both read it,
    /// so the two cannot disagree about what row the discharged operations
    /// leave behind.
    pub(super) row: EffRow,
    /// The term counter, which fixes generated names and tick order.
    ///
    /// Borrowed from the cascade, never owned: all state, local and free-monad
    /// attempts share one supply, and an Option-shaped attempt may mint and then
    /// decline, leaving the counter advanced for whatever runs next. An engine
    /// with a private counter would rename the fallback's tree, including where
    /// a name is minted before an arm that can still decline.
    pub(super) fresh: &'a mut crate::util::fresh::Fresh,
}

/// Constant context for the `stake` lowering: the downstream evidence, the
/// operation, the active evidence map (for rewriting non-producer subterms),
/// the live resume aliases, and the take's own `Step` instantiation.
struct TakeSite<'a> {
    ev: &'a TypedBinder,
    op: Sym,
    evs: &'a BTreeMap<Sym, Sym>,
    aliases: &'a BTreeSet<Sym>,
    step: &'a StepAt,
}

impl Threader<'_> {
    /// Thread `c`, whose accumulator is currently named `st`. `evs` maps each
    /// fused operation to the evidence active for it here.
    pub(super) fn thread_st(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        Some(match c.kind() {
            // `let g = handle s(()) with <stake>; g(n)`: a parameter-passing
            // early-terminating handler, lowered via the `Step` protocol.
            TypedCompKind::Bind(m, g, rest) if self.take_seed(m, g.name(), rest).is_some() => {
                let seed = self.take_seed(m, g.name(), rest)?;
                self.thread_take(m, &seed, evs, loc, st)?
            }
            // Re-associate a let-bound compound computation so its inner
            // operations surface as flat producing binds: state threading is
            // associative, and without this a `do op` buried in a bound
            // computation is opaque to the per-operation threading.
            TypedCompKind::Bind(m, x, n) if matches!(m.kind(), TypedCompKind::Bind(..)) => {
                let TypedCompKind::Bind(a, y, b) = m.kind() else {
                    unreachable!("guarded above")
                };
                let flat = TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::Bind(
                        a.clone(),
                        y.clone(),
                        Box::new(TypedComp::new(
                            c.sig().clone(),
                            TypedCompKind::Bind(b.clone(), x.clone(), n.clone()),
                        )),
                    ),
                );
                self.thread_st(&flat, evs, loc, st)?
            }
            // A bind whose head performs an operation: thread the accumulator
            // through it and rebind. The head's result is bound only if the tail
            // still needs it: a read observes the pre-operation accumulator, a
            // write yields unit.
            TypedCompKind::Bind(m, x, n) if produces(m, loc, &ops, self.latent, self.flow) => {
                let st2 = TypedBinder::new(self.mint("st"), st.ty().clone());
                let tm = self.thread_st(m, evs, loc, st)?;
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, self.latent, self.flow));
                let tn = self.thread_st(n, evs, &loc2, &st2)?;
                let tn = if free_comp_vars(n).contains(&x.name()) {
                    // A read exposes the prior accumulator and a write exposes
                    // unit. A producing head outside those operation shapes has
                    // no value the threaded accumulator can recreate.
                    // Producer-answer plans decline; accumulator-answer plans
                    // admit only Unit, whose single inhabitant can be rebuilt,
                    // and assert that exclusion before doing so.
                    let bound = bound_producer_result(
                        self.plan.answer,
                        self.op_tail_kind(m, loc, evs),
                        st,
                        x.ty(),
                    )?;
                    TypedComp::new(
                        tn.sig().clone(),
                        TypedCompKind::Bind(
                            Box::new(TypedComp::new(
                                CompSig::new(bound.ty().clone(), EffRow::Empty),
                                TypedCompKind::Return(bound),
                            )),
                            x.clone(),
                            Box::new(tn),
                        ),
                    )
                } else {
                    tn
                };
                // In early mode the producer stops once a stake yields
                // `SDone`, guarding with the scope's one Step decision.
                let tn = match (self.plan.early.short_circuits(), self.step.clone()) {
                    (true, Some(step)) => self.step_guard(&step, &st2, tn),
                    _ => tn,
                };
                Self::bind(tm, st2, tn)
            }
            // Tail producer heads append the accumulator and return the new one.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } if evs.contains_key(operation) => {
                let ev = self.evidence(evs, *operation, st.ty())?;
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, evs))
                    .collect::<Option<_>>()?;
                a.push(super::binder_var(st));
                Self::apply_clause(&ev, instantiation, a, st)?
            }
            TypedCompKind::Return(_) => TypedComp::new(
                CompSig::new(st.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(super::binder_var(st)),
            ),
            TypedCompKind::If(v, t, e) => {
                let t2 = self.thread_st(t, evs, loc, st)?;
                let e2 = self.thread_st(e, evs, loc, st)?;
                TypedComp::new(
                    t2.sig().clone(),
                    TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
                )
            }
            // A pure head: the accumulator passes through it untouched. The
            // binder follows the head it binds, exactly as in [`Self::rewrite`]:
            // a head whose value the rewrite retyped retypes its binder and
            // every read after it.
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.rewrite(m, loc, evs)?;
                let x2 = if m2.sig().result() == x.ty() {
                    x.clone()
                } else {
                    self.retyped.insert(x.name(), m2.sig().result().clone());
                    TypedBinder::new(x.name(), m2.sig().result().clone())
                };
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, self.latent, self.flow));
                let n2 = self.thread_st(n, evs, &loc2, st)?;
                Self::bind(m2, x2, n2)
            }
            // A tail call to a producer: append this call site's evidence, in the
            // same ascending operation-id order the producer declares it in, and
            // the accumulator.
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } if produces(c, loc, &ops, self.latent, self.flow) => {
                let callee_ops: BTreeSet<Sym> = self
                    .latent
                    .get(callee)
                    .map(|s| {
                        s.iter()
                            .map(|m| m.id)
                            .filter(|id| ops.contains(id))
                            .collect()
                    })
                    .unwrap_or_default();
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, evs))
                    .collect::<Option<_>>()?;
                a.extend(self.evidence_args(evs, &callee_ops, st.ty())?);
                a.push(super::binder_var(st));
                // The callee's signature gained quantifiers when it was planned
                // as a producer, and every reference must instantiate them: the
                // state type at what the accumulator concretely is here, and the
                // ambient row at the residual this call runs under.
                let mut inst = instantiation.clone();
                let numbered = {
                    let mut v: Vec<i64> = callee_ops
                        .iter()
                        .map(|op| self.ids.id(*op))
                        .collect::<Option<_>>()?;
                    v.sort_unstable();
                    v
                };
                if accumulator_type(self.plan, &callee_ops, &numbered)?
                    .1
                    .is_some()
                {
                    // (three-tuple now; .1 is still the state quantifier)
                    // The state quantifier is the BASE accumulator: a stepped
                    // scope's callee wraps its own Step around the declared
                    // accumulator, so instantiating at the stepped type would
                    // wrap twice.
                    let base = match &self.step {
                        Some(step) => step.done.clone(),
                        None => super::super::build::source_type(st.ty()).ok()?,
                    };
                    inst.push(CoreInstantiation::Type(base));
                }
                inst.push(CoreInstantiation::Row(self.row.clone()));
                TypedComp::new(
                    CompSig::new(st.ty().clone(), self.row.clone()),
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation: inst,
                        args: a,
                    },
                )
            }
            TypedCompKind::Case(v, arms) => {
                let arms: Vec<_> = arms
                    .iter()
                    .map(|(p, b)| Some((p.clone(), self.thread_st(b, evs, loc, st)?)))
                    .collect::<Option<_>>()?;
                // The case's row is the residual it runs under, not whatever a
                // single arm's tail locally reports: an arm ending in a bare
                // return says Empty, and the verifier rightly expects the
                // enclosing residual.
                let result = arms.first().map(|(_, b)| b.sig().result().clone())?;
                TypedComp::new(
                    CompSig::new(result, self.row.clone()),
                    TypedCompKind::Case(v.clone(), arms),
                )
            }
            // A force of an escaping producer thunk: the thunk gained evidence
            // and accumulator parameters and rank-2 quantifiers when it was
            // rewritten, so the force site appends the matching arguments and
            // instantiates the quantifiers: the state type at what the
            // accumulator concretely is here, and the ambient row at the residual
            // this site runs in.
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } if produces(c, loc, &ops, self.latent, self.flow) => {
                let TypedCompKind::Force(v) = callee.kind() else {
                    return None;
                };
                let v2 = self.retyped.rebuild(v);
                let CoreType::Thunk(thunk) = v2.ty().clone() else {
                    return None;
                };
                let CoreType::Function(fun) = thunk.result() else {
                    return None;
                };
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, evs))
                    .collect::<Option<_>>()?;
                let carried: BTreeSet<Sym> = flow::value_sig(v, loc, self.latent)
                    .into_iter()
                    .map(|masked| masked.id)
                    .filter(|operation| ops.contains(operation))
                    .collect();
                a.extend(self.evidence_args(evs, &carried, st.ty())?);
                a.push(super::binder_var(st));
                let mut inst = instantiation.clone();
                for q in fun.quantifiers().iter().skip(instantiation.len()) {
                    match q {
                        CoreQuantifier::Type(_) => {
                            let base = match &self.step {
                                Some(step) => step.done.clone(),
                                None => super::super::build::source_type(st.ty()).ok()?,
                            };
                            inst.push(CoreInstantiation::Type(base));
                        }
                        CoreQuantifier::Row(_) => {
                            inst.push(CoreInstantiation::Row(self.row.clone()));
                        }
                    }
                }
                let force = TypedComp::new(thunk.as_ref().clone(), TypedCompKind::Force(v2));
                TypedComp::new(
                    // The forced producer discharges its operations, so the App
                    // leaves the ambient residual, not the callee's stale source
                    // row.
                    CompSig::new(st.ty().clone(), self.row.clone()),
                    TypedCompKind::App {
                        callee: Box::new(force),
                        instantiation: inst,
                        args: a,
                    },
                )
            }
            // A handle inside a producer is a re-emitting forwarder: it performs
            // the operation again, so it threads rather than consumes.
            TypedCompKind::Handle { .. } => self.thread_forward(c, evs, loc, st)?,
            // Take handles using the `Step` protocol and escaping producer thunks
            // carried by a pure head are not fused here.
            _ => return None,
        })
    }

    /// Thread a re-emitting forwarder (`smap`, `skeep`): a handler that is
    /// tail-resumptive but performs the operation again, so it fuses as a producer
    /// rather than a consumer.
    ///
    /// Its clause becomes the source's evidence, bound under a fresh name that
    /// shadows the operation while the handled body re-emits into the outer
    /// evidence with the accumulator threaded through. Producer, `smap`, `skeep`
    /// and fold then collapse into one loop.
    fn thread_forward(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            ops,
            return_binder,
            return_body,
        } = c.kind()
        else {
            return None;
        };
        let [clause] = ops.arms() else {
            return None;
        };
        // The forwarded body's final value passes straight through, so the return
        // clause must be the identity: anything else would have to observe a value
        // the threaded loop has already turned into an accumulator.
        let erased_return = return_body.as_deref().map(|b| b.clone().erase());
        if !evs.contains_key(&clause.name())
            || !is_id_return(
                return_binder.as_ref().map(TypedBinder::name),
                erased_return.as_ref(),
            )
        {
            return None;
        }
        let mut aliases = BTreeSet::new();
        aliases.insert(clause.resume().name());
        let stripped = super::evidence::strip_resume(clause.body(), &aliases, self.drift)?;

        // The final producer edge establishes the shadow's clause. Substitute
        // the edge's element and ambient tail through the body, keep every
        // outer lexical local at its binder witness, and wrap exactly those
        // whose type changes through the explicit Word bridge, which erases to
        // the same variable and is legal because this builder's output is
        // EffectLowered.
        let mut from: Vec<CoreQuantifier> = Vec::new();
        let mut to: Vec<CoreInstantiation> = Vec::new();
        if let Some(CoreType::Thunk(edge)) = forced_source_type(body) {
            if let CoreType::Function(edge_fn) = edge.result() {
                let effect = self.env.operation(clause.name())?.effect().name;
                let elems = label_args(edge_fn.body().effects(), effect);
                for (binder, elem) in clause.params().iter().zip(elems) {
                    if let CoreType::Source(Type::Var(name)) = binder.ty() {
                        from.push(CoreQuantifier::Type(*name));
                        to.push(CoreInstantiation::Type(elem));
                    }
                }
            }
        }
        if let Some(tail) = row_tail(clause.body().sig().effects()) {
            from.push(CoreQuantifier::Row(tail));
            to.push(CoreInstantiation::Row(self.row.clone()));
        }
        let stripped = if from.is_empty() {
            stripped
        } else {
            let candidates: BTreeSet<Sym> = free_comp_vars(&stripped)
                .into_iter()
                .filter(|name| loc.contains_key(name))
                .collect();
            let lexical = lexical_types(&stripped, &candidates)?;
            let substituted =
                super::super::specialize_support::substitute_witnesses(&stripped, &from, &to);
            let effect = self.env.operation(clause.name())?.effect().name;
            let mut bridges: BTreeMap<Sym, TypedValue> = BTreeMap::new();
            for (name, reference) in &lexical {
                // The bridge target is the edge type with the discharged
                // operation removed from its rows: the shadow re-emits into the
                // outer evidence, so the source clause no longer carries the
                // label the outer scope has already accounted for.
                let edge_ty = super::subtract::SubtractEffect { label: effect }.ty(
                    &super::super::verify::substitute_core_type(reference.ty(), &from, &to),
                );
                if edge_ty != *reference.ty() {
                    bridges.insert(
                        *name,
                        super::abi::try_word_bridge(reference.clone(), edge_ty)?,
                    );
                }
            }
            if bridges.is_empty() {
                substituted
            } else {
                let mut counter = 0u32;
                super::super::specialize_support::substitute_terms(
                    &substituted,
                    &bridges,
                    &mut counter,
                    "fwb",
                )
            }
        };
        let shadow_params: Vec<TypedBinder> = clause
            .params()
            .iter()
            .map(|binder| {
                TypedBinder::new(
                    binder.name(),
                    super::super::verify::substitute_core_type(binder.ty(), &from, &to),
                )
            })
            .collect();

        // The source's evidence: the clause's own body, threading the accumulator
        // into whatever the outer evidence is here.
        let acc = TypedBinder::new(self.mint("acc"), st.ty().clone());
        let ev_body = self.thread_st(&stripped, evs, loc, &acc)?;
        let mut ev_params = shadow_params;
        ev_params.push(acc);
        let lam = Self::lam(ev_params, ev_body);
        let inner = TypedBinder::new(
            self.mint("ev"),
            CoreType::Thunk(Box::new(lam.sig().clone())),
        );
        self.evidence_types.insert(inner.name(), inner.ty().clone());
        let thunk = TypedValue::new(inner.ty().clone(), TypedValueKind::Thunk(Box::new(lam)));

        // Shadow the forwarded operation's evidence with that fresh source
        // evidence while threading the handled body. Every other operation keeps
        // the evidence active here.
        let mut evs2 = evs.clone();
        evs2.insert(clause.name(), inner.name());
        let threaded = self.thread_st(body, &evs2, loc, st)?;
        Some(TypedComp::new(
            threaded.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(thunk.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(thunk),
                )),
                inner,
                Box::new(threaded),
            ),
        ))
    }

    /// Lower a control consumer (a `for`/print loop): tail-resumptive but not
    /// re-emitting, so its clause is a pure side effect over a unit state the
    /// producer threads unchanged, and its return clause runs on the final state.
    fn lower_consumer(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
    ) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            ops,
            return_binder,
            return_body,
        } = c.kind()
        else {
            return None;
        };
        let [clause] = ops.arms() else {
            return None;
        };
        let unit = CoreType::Source(Type::Unit);
        let saved_row = std::mem::replace(&mut self.row, c.sig().effects().clone());

        // Evidence: run the clause's side effects, then return the state.
        let mut aliases = BTreeSet::new();
        aliases.insert(clause.resume().name());
        let stripped = super::evidence::strip_resume(clause.body(), &aliases, self.drift)?;
        let st = TypedBinder::new(self.mint("st"), unit.clone());
        let rewritten = self.rewrite(&stripped, loc, evs)?;
        let d = TypedBinder::new(self.mint("d"), rewritten.sig().result().clone());
        let ev_inner = TypedComp::new(
            CompSig::new(unit.clone(), rewritten.sig().effects().clone()),
            TypedCompKind::Bind(
                Box::new(rewritten),
                d,
                Box::new(TypedComp::new(
                    CompSig::new(unit.clone(), EffRow::Empty),
                    TypedCompKind::Return(super::binder_var(&st)),
                )),
            ),
        );
        let mut ev_params = clause.params().to_vec();
        let step_at = StepAt::new(Type::Unit, Type::Unit);
        let ev_body = if self.plan.early.short_circuits() {
            self.step = Some(step_at.clone());
            let step = TypedBinder::new(self.mint("step"), step_at.ty());
            let body = self.step_map(&step_at, &step, st, ev_inner);
            ev_params.push(step);
            body
        } else {
            ev_params.push(st);
            ev_inner
        };
        let ev_lam = Self::lam(ev_params, ev_body);
        let ev = TypedBinder::new(
            *evs.get(&clause.name())?,
            CoreType::Thunk(Box::new(ev_lam.sig().clone())),
        );
        self.evidence_types.insert(ev.name(), ev.ty().clone());
        let ev_thunk = TypedValue::new(ev.ty().clone(), TypedValueKind::Thunk(Box::new(ev_lam)));

        // Seed unit, thread the producer, bind its result, run the return clause.
        let st0 = TypedBinder::new(
            self.mint("st"),
            if self.plan.early.short_circuits() {
                step_at.ty()
            } else {
                unit.clone()
            },
        );
        let threaded = self.thread_st(body, evs, loc, &st0)?;
        let fin = TypedBinder::new(self.mint("fin"), unit.clone());
        let rv = return_binder
            .clone()
            .unwrap_or_else(|| TypedBinder::new(self.mint("r"), unit.clone()));
        let rb = match return_body {
            Some(b) => self.rewrite(b, loc, evs)?,
            None => TypedComp::new(
                CompSig::new(rv.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(super::binder_var(&rv)),
            ),
        };
        let (seed, body_done) = if self.plan.early.short_circuits() {
            (
                step_at.smore(super::unit_value()),
                self.seed_unwrap(&step_at, threaded),
            )
        } else {
            (super::unit_value(), threaded)
        };
        let bind = |head: TypedComp, x: TypedBinder, tail: TypedComp| Self::bind(head, x, tail);
        let read_fin = TypedComp::new(
            CompSig::new(fin.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(super::binder_var(&fin)),
        );
        let after = bind(body_done, fin, bind(read_fin, rv, rb));
        self.row = saved_row;
        Some(bind(
            TypedComp::new(
                CompSig::new(ev_thunk.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(ev_thunk),
            ),
            ev,
            bind(
                TypedComp::new(
                    CompSig::new(seed.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(seed),
                ),
                st0,
                after,
            ),
        ))
    }

    /// Lower a fold handle: bind one state-transformer evidence per clause, then
    /// thread the handled body under them.
    ///
    /// The handle collapses to `\(acc0) -> <body threaded>`, a function from the
    /// initial accumulator to the final one, which the call site applies. Each
    /// clause becomes `\(args.., acc) -> acc'`, its own evidence, bound under the
    /// canonical `ev@<id>` name the producers already expect: one `State` handler
    /// contributes both `get` and `put`, and they thread the one accumulator.
    fn lower_fold(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
    ) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            ops: clauses,
            return_binder,
            return_body,
        } = c.kind()
        else {
            return None;
        };

        // The shared classifier's verdict for each clause, read off the erased
        // clone, so the ported rewrite below can be checked against it.
        let erased = clauses.clone().erase();
        let shared: Vec<Option<FoldAKind>> = erased
            .iter_with_use()
            .map(|(clause, ru)| is_fold(clause, ru))
            .collect();

        // The accumulator's type at this handle is written on the clause lambdas
        // themselves: each clause is `\(acc) -> ..` and its binder carries the
        // type the seed will arrive at. The minted state quantifier is never used
        // here; a handle is a concrete instantiation site, not a parametric one.
        // The handle's residual is the row the whole handle expression carries:
        // what remains once its operations are discharged, which is exactly the
        // row its evidence clauses run under and its producer calls instantiate.
        let saved_row = std::mem::replace(&mut self.row, c.sig().effects().clone());
        let mut handle_acc: Option<CoreType> = None;
        let mut ev_binds: Vec<(TypedBinder, TypedValue)> = Vec::with_capacity(clauses.arms().len());
        for (index, clause) in clauses.arms().iter().enumerate() {
            let TypedCompKind::Return(v) = clause.body().kind() else {
                return None;
            };
            let TypedValueKind::Thunk(t) = &super::peel(v).kind else {
                return None;
            };
            let TypedCompKind::Lam(ps, inner) = t.kind() else {
                return None;
            };
            let [acc] = ps.as_slice() else {
                return None;
            };
            // One handle threads one accumulator, so its clauses must agree on
            // the type; the gate's per-producer pin check already refused the
            // programs where they cannot.
            match &handle_acc {
                Some(ty) if ty != acc.ty() => return None,
                _ => handle_acc = Some(acc.ty().clone()),
            }
            let mut aliases = BTreeSet::new();
            aliases.insert(clause.resume().name());
            let (stripped, kind) = strip_state(inner, &aliases, acc.name())?;
            // The ported rewrite and the shared judgment must agree about what
            // this clause resumes with. They are different code over different
            // trees, so this is a real check, and it runs on every program rather
            // than on the clauses a fixture happens to cover.
            if shared.get(index).copied().flatten() != Some(kind) {
                return None;
            }
            let ev_body = self.rewrite(&stripped, loc, evs)?;
            let mut ev_params = clause.params().to_vec();
            // In early mode the state is `Step Acc`: the evidence folds inside
            // `SMore` and forwards `SDone` untouched, so a stake upstream can
            // stop the loop.
            let ev_body = if self.plan.early.short_circuits() {
                let source = super::super::build::source_type(acc.ty()).ok()?;
                let step_at = StepAt::new(source.clone(), source);
                self.step = Some(step_at.clone());
                let step = TypedBinder::new(self.mint("step"), step_at.ty());
                let body = self.step_map(&step_at, &step, acc.clone(), ev_body);
                ev_params.push(step);
                body
            } else {
                ev_params.push(acc.clone());
                ev_body
            };
            let lam = Self::lam(ev_params, ev_body);
            // The evidence binder is typed by the clause that actually inhabits
            // it: a handle is a concrete site, and its clause is the handler's
            // own monomorphic lambda, not the operation's scheme re-quantified.
            let ev = TypedBinder::new(
                *evs.get(&clause.name())?,
                CoreType::Thunk(Box::new(lam.sig().clone())),
            );
            self.evidence_types.insert(ev.name(), ev.ty().clone());
            let thunk = TypedValue::new(ev.ty().clone(), TypedValueKind::Thunk(Box::new(lam)));
            ev_binds.push((ev, thunk));
        }

        // `g = \(acc0) -> <body threaded from acc0>`, closing over the evidence.
        // In early mode the seed is wrapped `SMore(acc0)` and the threaded
        // loop's final `Step` is unwrapped back to the bare accumulator.
        let acc0 = TypedBinder::new(self.mint("acc"), handle_acc?);
        let g_body = if self.plan.early.short_circuits() {
            let source = super::super::build::source_type(acc0.ty()).ok()?;
            let step_at = StepAt::new(source.clone(), source);
            self.step = Some(step_at.clone());
            let st0 = TypedBinder::new(self.mint("st"), step_at.ty());
            let threaded = self.thread_st(body, evs, loc, &st0)?;
            let seeded = step_at.smore(super::binder_var(&acc0));
            let unwrapped = self.seed_unwrap(&step_at, threaded);
            TypedComp::new(
                unwrapped.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(seeded.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(seeded),
                    )),
                    st0,
                    Box::new(unwrapped),
                ),
            )
        } else {
            self.thread_st(body, evs, loc, &acc0)?
        };
        let g_body = self.apply_state_return(
            g_body,
            return_binder.as_ref(),
            return_body.as_deref(),
            loc,
            evs,
        )?;
        let g_lam = Self::lam(vec![acc0.clone()], g_body);
        // A thunk of a lambda is typed by the lambda's own signature; building
        // the type a second time by hand is how the two drift.
        let g_ty = CoreType::Thunk(Box::new(g_lam.sig().clone()));
        let mut out = TypedComp::new(
            CompSig::new(g_ty.clone(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                g_ty,
                TypedValueKind::Thunk(Box::new(g_lam)),
            )),
        );
        for (binder, thunk) in ev_binds.into_iter().rev() {
            let bound = TypedComp::new(
                CompSig::new(thunk.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(thunk),
            );
            out = Self::bind(bound, binder, out);
        }
        self.row = saved_row;
        Some(out)
    }

    /// Apply a fold's state-transformer return clause to the threaded body's
    /// final accumulator.
    ///
    /// The identity transformer is absorbed, because the threaded body already
    /// yields the accumulator. A get-style `\s -> body` binds both the producer
    /// value and the final state to that one accumulator: they coincide, which is
    /// exactly what [`value_coincident`] checked before any of this ran.
    fn apply_state_return(
        &mut self,
        threaded: TypedComp,
        return_binder: Option<&TypedBinder>,
        return_body: Option<&TypedComp>,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedComp> {
        let rb = return_body?;
        if is_id_transformer(&rb.clone().erase()) {
            return Some(threaded);
        }
        let TypedCompKind::Return(v) = rb.kind() else {
            return None;
        };
        let TypedValueKind::Thunk(t) = &super::peel(v).kind else {
            return None;
        };
        let TypedCompKind::Lam(ps, body) = t.kind() else {
            return None;
        };
        let [s] = ps.as_slice() else {
            return None;
        };
        let rbody = self.rewrite(body, loc, evs)?;
        let fin = TypedBinder::new(self.mint("fin"), threaded.sig().result().clone());
        let r = return_binder
            .cloned()
            .unwrap_or_else(|| TypedBinder::new(self.mint("r"), fin.ty().clone()));
        let read_fin = || {
            TypedComp::new(
                CompSig::new(fin.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(super::binder_var(&fin)),
            )
        };
        let inner = Self::bind(read_fin(), s.clone(), rbody);
        let middle = Self::bind(read_fin(), r, inner);
        Some(Self::bind(threaded, fin, middle))
    }

    /// The seed of `let g = handle s(()) with <stake>; g(n)`, or `None` when
    /// this bind is not that shape: the handle's single clause must be a take,
    /// and `g(n)` is matched through its A-normal-form binds with the seed
    /// resolved back to its source value.
    fn take_seed(&self, m: &TypedComp, g: Sym, rest: &TypedComp) -> Option<TypedValue> {
        let TypedCompKind::Handle { ops, .. } = m.kind() else {
            return None;
        };
        let [clause] = ops.arms() else {
            return None;
        };
        if !is_take(clause, self.latent) {
            return None;
        }
        anf_app_arg(g, rest)
    }

    /// Lower a `stake` via the `Step` protocol.
    ///
    /// The clause `\(cnt) -> if c then { do op(x); resume(next) } else <drop>`
    /// becomes the source's evidence over `Step (dstep, cnt)`: it pairs its
    /// counter with the downstream state, re-emits into the downstream evidence
    /// while resuming, and yields `SDone` when it drops the continuation. The
    /// handled body threads from the combined seed `SMore (st, n)`, and the
    /// consumer takes back the downstream step the loop carried.
    fn thread_take(
        &mut self,
        handle: &TypedComp,
        seed: &TypedValue,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let TypedCompKind::Handle { body, ops, .. } = handle.kind() else {
            return None;
        };
        let [clause] = ops.arms() else {
            return None;
        };
        let op = clause.name();
        let TypedCompKind::Return(v) = clause.body().kind() else {
            return None;
        };
        let TypedValueKind::Thunk(t) = &super::peel(v).kind else {
            return None;
        };
        let TypedCompKind::Lam(ps, inner) = t.kind() else {
            return None;
        };
        let [cnt] = ps.as_slice() else {
            return None;
        };
        let mut aliases = BTreeSet::new();
        aliases.insert(clause.resume().name());

        // The take's own step: its payload pairs the downstream step with the
        // counter, and both constructors carry the same pair.
        let pair_ty = Type::Tuple(vec![
            super::super::build::source_type(st.ty()).ok()?,
            super::super::build::source_type(cnt.ty()).ok()?,
        ]);
        let step = StepAt::new(pair_ty.clone(), pair_ty.clone());
        let downstream = self.evidence(evs, op, st.ty())?;

        // Evidence for the source: unpack the step, run the clause's leading
        // counter-test binds and branch, threading the resume side into the
        // downstream evidence and the drop side into `SDone`.
        let dstep = TypedBinder::new(self.mint("ds"), st.ty().clone());
        let take = TakeSite {
            ev: &downstream,
            op,
            evs,
            aliases: &aliases,
            step: &step,
        };
        let smore_body = self.take_clause(inner, &take, loc, &dstep, cnt)?;
        let tstep = TypedBinder::new(self.mint("ts"), step.ty());
        // The SDone payload is the outer take pair (downstream step, counter),
        // not the bare downstream step; both the pattern and the reconstructed
        // value carry it.
        let sd = TypedBinder::new(self.mint("sd"), CoreType::Source(pair_ty));
        let sd_val = step.sdone(super::binder_var(&sd));
        let evt_body = TypedComp::new(
            smore_body.sig().clone(),
            TypedCompKind::Case(
                super::binder_var(&tstep),
                vec![
                    self.step_pair_arm(&step, true, dstep.clone(), cnt.clone(), smore_body)?,
                    (
                        step.done_pattern(sd),
                        TypedComp::new(
                            CompSig::new(step.ty(), EffRow::Empty),
                            TypedCompKind::Return(sd_val),
                        ),
                    ),
                ],
            ),
        );
        let mut evt_params = clause.params().to_vec();
        evt_params.push(tstep);
        let evt_lam = Self::lam(evt_params, evt_body);
        let evt = TypedBinder::new(
            self.mint("ev"),
            CoreType::Thunk(Box::new(evt_lam.sig().clone())),
        );
        self.evidence_types.insert(evt.name(), evt.ty().clone());
        let evt_thunk = TypedValue::new(evt.ty().clone(), TypedValueKind::Thunk(Box::new(evt_lam)));

        // Thread the source from the combined seed with the take's evidence
        // shadowing its operation, then take back the downstream step the loop
        // carried: `SMore` or `SDone`, same payload.
        let seedvar = TypedBinder::new(self.mint("st"), step.ty());
        let combined = step.smore(TypedValue::new(
            CoreType::Source(Type::Tuple(vec![
                super::super::build::source_type(st.ty()).ok()?,
                super::super::build::source_type(seed.ty()).ok()?,
            ])),
            TypedValueKind::Tuple(vec![super::binder_var(st), seed.clone()]),
        ));
        let mut evs_src = evs.clone();
        evs_src.insert(op, evt.name());
        let saved_step = self.step.replace(step.clone());
        let threaded = self.thread_st(body, &evs_src, loc, &seedvar)?;
        self.step = saved_step;
        let fin = TypedBinder::new(self.mint("fin"), step.ty());
        let d1 = TypedBinder::new(self.mint("d"), st.ty().clone());
        let w1 = TypedBinder::new(self.mint("w"), cnt.ty().clone());
        let d2 = TypedBinder::new(self.mint("d"), st.ty().clone());
        let w2 = TypedBinder::new(self.mint("w"), cnt.ty().clone());
        let ret_d = |d: &TypedBinder| {
            TypedComp::new(
                CompSig::new(d.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(super::binder_var(d)),
            )
        };
        let extract = TypedComp::new(
            CompSig::new(st.ty().clone(), EffRow::Empty),
            TypedCompKind::Case(
                super::binder_var(&fin),
                vec![
                    self.step_pair_arm(&step, true, d1.clone(), w1, ret_d(&d1))?,
                    self.step_pair_arm(&step, false, d2.clone(), w2, ret_d(&d2))?,
                ],
            ),
        );
        let bind = |head: TypedComp, x: TypedBinder, tail: TypedComp| Self::bind(head, x, tail);
        let seeded = bind(
            TypedComp::new(
                CompSig::new(combined.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(combined),
            ),
            seedvar,
            bind(threaded, fin, extract),
        );
        Some(bind(
            TypedComp::new(
                CompSig::new(evt_thunk.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(evt_thunk),
            ),
            evt,
            seeded,
        ))
    }

    /// The `SMore` arm of a take's evidence: keep the clause's leading
    /// counter-testing binds, then transform the tail `if`: the resuming side
    /// folds the downstream evidence and continues, and the dropping side stops
    /// with `SDone` carrying the current downstream step and counter.
    fn take_clause(
        &mut self,
        c: &TypedComp,
        t: &TakeSite<'_>,
        loc: &Loc,
        dstep: &TypedBinder,
        cnt: &TypedBinder,
    ) -> Option<TypedComp> {
        Some(match c.kind() {
            TypedCompKind::Bind(m, x, n) => {
                let tail = self.take_clause(n, t, loc, dstep, cnt)?;
                TypedComp::new(
                    tail.sig().clone(),
                    TypedCompKind::Bind(m.clone(), x.clone(), Box::new(tail)),
                )
            }
            TypedCompKind::If(cond, b1, b2) => {
                let (resume_b, drop_b, invert) = if branch_resumes(b1, t.aliases) {
                    (b1, b2, false)
                } else {
                    (b2, b1, true)
                };
                let more = self.take_thread(resume_b, t, loc, dstep)?;
                let d = TypedBinder::new(self.mint("d"), drop_b.sig().result().clone());
                let stopped = t.step.sdone(TypedValue::new(
                    CoreType::Source(Type::Tuple(vec![
                        super::super::build::source_type(dstep.ty()).ok()?,
                        super::super::build::source_type(cnt.ty()).ok()?,
                    ])),
                    TypedValueKind::Tuple(vec![super::binder_var(dstep), super::binder_var(cnt)]),
                ));
                let dropped = TypedComp::new(
                    CompSig::new(t.step.ty(), EffRow::Empty),
                    TypedCompKind::Bind(
                        Box::new(self.rewrite(drop_b, loc, t.evs)?),
                        d,
                        Box::new(TypedComp::new(
                            CompSig::new(t.step.ty(), EffRow::Empty),
                            TypedCompKind::Return(stopped),
                        )),
                    ),
                );
                let (bt, be) = if invert {
                    (dropped, more)
                } else {
                    (more, dropped)
                };
                TypedComp::new(
                    bt.sig().clone(),
                    TypedCompKind::If(cond.clone(), Box::new(bt), Box::new(be)),
                )
            }
            _ => return None,
        })
    }

    /// Thread the resuming branch of a take clause into `SMore ((dstep'), next)`:
    /// each re-emit folds into the downstream evidence, advancing the downstream
    /// step, and the parameter-passing resume becomes the new step carrying the
    /// advanced downstream step and the next counter value.
    fn take_thread(
        &mut self,
        c: &TypedComp,
        t: &TakeSite<'_>,
        loc: &Loc,
        dstep: &TypedBinder,
    ) -> Option<TypedComp> {
        Some(match c.kind() {
            // Right-associate a bind-of-bind so a re-emit at the tail of a
            // sub-block surfaces as a head this pass can rewrite.
            TypedCompKind::Bind(m, x, n) if matches!(m.kind(), TypedCompKind::Bind(..)) => {
                let TypedCompKind::Bind(a, y, b) = m.kind() else {
                    unreachable!("guarded above")
                };
                let reassoc = TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::Bind(
                        a.clone(),
                        y.clone(),
                        Box::new(TypedComp::new(
                            c.sig().clone(),
                            TypedCompKind::Bind(b.clone(), x.clone(), n.clone()),
                        )),
                    ),
                );
                return self.take_thread(&reassoc, t, loc, dstep);
            }
            TypedCompKind::Bind(m, x, n) if is_alias_return(m, t.aliases) => {
                let mut a2 = t.aliases.clone();
                a2.insert(x.name());
                return self.take_thread(n, &TakeSite { aliases: &a2, ..*t }, loc, dstep);
            }
            // A re-emit: fold the downstream evidence, advancing the step.
            TypedCompKind::Bind(m, x, n) if matches!(m.kind(), TypedCompKind::Do { operation, .. } if *operation == t.op) =>
            {
                let TypedCompKind::Do {
                    args,
                    instantiation,
                    ..
                } = m.kind()
                else {
                    unreachable!("guarded above")
                };
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, t.evs))
                    .collect::<Option<_>>()?;
                a.push(super::binder_var(dstep));
                let ds2 = TypedBinder::new(self.mint("ds"), dstep.ty().clone());
                let CoreType::Thunk(thunk) = t.ev.ty() else {
                    return None;
                };
                let CoreType::Function(fun) = thunk.result() else {
                    return None;
                };
                // The forced clause may already be instantiated; keep the
                // source Do's arguments only when the clause is still
                // polymorphic, and derive the App body (result and residual
                // row) from that instantiated signature rather than an empty
                // row.
                let inst = if fun.quantifiers().is_empty() {
                    Vec::new()
                } else {
                    instantiation.clone()
                };
                let applied = super::super::verify::instantiate_fn(fun, &inst).ok()?;
                let call = TypedComp::new(
                    applied.body().clone(),
                    TypedCompKind::App {
                        callee: Box::new(TypedComp::new(
                            thunk.as_ref().clone(),
                            TypedCompKind::Force(super::binder_var(t.ev)),
                        )),
                        instantiation: inst,
                        args: a,
                    },
                );
                let mut cont = self.take_thread(n, t, loc, &ds2)?;
                if free_comp_vars(n).contains(&x.name()) {
                    cont = TypedComp::new(
                        cont.sig().clone(),
                        TypedCompKind::Bind(
                            Box::new(TypedComp::new(
                                CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
                                TypedCompKind::Return(super::unit_value()),
                            )),
                            x.clone(),
                            Box::new(cont),
                        ),
                    );
                }
                Self::bind(call, ds2, cont)
            }
            // The double application `k(())(next)`: stop with the carried step.
            TypedCompKind::Bind(m, kr, n) if resume_call(m, t.aliases) => {
                let TypedCompKind::App { callee, args, .. } = n.kind() else {
                    return None;
                };
                if !matches!(callee.kind(), TypedCompKind::Force(k)
                    if super::as_var(k) == Some(kr.name()))
                {
                    return None;
                }
                let [next] = args.as_slice() else {
                    return None;
                };
                if !free_value_vars(next).is_disjoint(t.aliases) {
                    return None;
                }
                let stepped = t.step.smore(TypedValue::new(
                    CoreType::Source(Type::Tuple(vec![
                        super::super::build::source_type(dstep.ty()).ok()?,
                        super::super::build::source_type(next.ty()).ok()?,
                    ])),
                    TypedValueKind::Tuple(vec![super::binder_var(dstep), next.clone()]),
                ));
                TypedComp::new(
                    CompSig::new(t.step.ty(), EffRow::Empty),
                    TypedCompKind::Return(stepped),
                )
            }
            TypedCompKind::Bind(m, x, n) if free_comp_vars(m).is_disjoint(t.aliases) => {
                let tail = self.take_thread(n, t, loc, dstep)?;
                TypedComp::new(
                    tail.sig().clone(),
                    TypedCompKind::Bind(m.clone(), x.clone(), Box::new(tail)),
                )
            }
            TypedCompKind::If(v, tb, e) if free_value_vars(v).is_disjoint(t.aliases) => {
                let t2 = self.take_thread(tb, t, loc, dstep)?;
                let e2 = self.take_thread(e, t, loc, dstep)?;
                TypedComp::new(
                    t2.sig().clone(),
                    TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
                )
            }
            _ => return None,
        })
    }

    /// `Ctor(p) => case p of (a, b) => body`: a step over a state pair, unpacked
    /// in two steps because codegen binds only flat `Var` subpatterns.
    ///
    /// `None` when either component's source type cannot be recovered: a helper
    /// may never invent a witness where extraction fails, so an unrecoverable
    /// pair declines the whole take rather than shipping a fiction.
    fn step_pair_arm(
        &mut self,
        step: &StepAt,
        more: bool,
        a: TypedBinder,
        b: TypedBinder,
        body: TypedComp,
    ) -> Option<(TypedPattern, TypedComp)> {
        let p = TypedBinder::new(
            self.mint("p"),
            CoreType::Source(Type::Tuple(vec![
                super::super::build::source_type(a.ty()).ok()?,
                super::super::build::source_type(b.ty()).ok()?,
            ])),
        );
        let inner = TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Case(
                super::binder_var(&p),
                vec![(TypedPattern::Tuple(vec![Some(a), Some(b)]), body)],
            ),
        );
        let pattern = if more {
            step.more_pattern(p)
        } else {
            step.done_pattern(p)
        };
        Some((pattern, inner))
    }

    /// `\(.., acc) -> body` lifted to operate on `Step Acc`: fold inside
    /// `SMore`, forward `SDone` untouched.
    fn step_map(
        &mut self,
        step: &StepAt,
        sv: &TypedBinder,
        acc: TypedBinder,
        body: TypedComp,
    ) -> TypedComp {
        let r = TypedBinder::new(self.mint("r"), body.sig().result().clone());
        let sd = TypedBinder::new(self.mint("sd"), acc.ty().clone());
        let folded = step.smore(super::binder_var(&r));
        let forwarded = step.sdone(super::binder_var(&sd));
        // The SMore arm folds the body, which now honestly reports the ambient
        // residual; the arm and the enclosing Case carry that row. The SDone arm
        // stays Empty, and the Case union derives the ambient from the SMore arm.
        let row = body.sig().effects().clone();
        TypedComp::new(
            CompSig::new(step.ty(), row.clone()),
            TypedCompKind::Case(
                super::binder_var(sv),
                vec![
                    (
                        step.more_pattern(acc),
                        TypedComp::new(
                            CompSig::new(step.ty(), row),
                            TypedCompKind::Bind(
                                Box::new(body),
                                r,
                                Box::new(TypedComp::new(
                                    CompSig::new(step.ty(), EffRow::Empty),
                                    TypedCompKind::Return(folded),
                                )),
                            ),
                        ),
                    ),
                    (
                        step.done_pattern(sd),
                        TypedComp::new(
                            CompSig::new(step.ty(), EffRow::Empty),
                            TypedCompKind::Return(forwarded),
                        ),
                    ),
                ],
            ),
        )
    }

    /// Stop the producer once a `stake` has yielded `SDone`, else run the rest.
    fn step_guard(&mut self, step: &StepAt, sv: &TypedBinder, cont: TypedComp) -> TypedComp {
        let m = TypedBinder::new(self.mint("_w"), CoreType::Source(step.done.clone()));
        let d = TypedBinder::new(self.mint("_w"), CoreType::Source(step.done.clone()));
        TypedComp::new(
            cont.sig().clone(),
            TypedCompKind::Case(
                super::binder_var(sv),
                vec![
                    (step.more_pattern(m), cont),
                    (
                        step.done_pattern(d),
                        TypedComp::new(
                            CompSig::new(sv.ty().clone(), EffRow::Empty),
                            TypedCompKind::Return(super::binder_var(sv)),
                        ),
                    ),
                ],
            ),
        )
    }

    /// Unwrap the final `Step` of a fused loop back to its bare payload.
    fn seed_unwrap(&mut self, step: &StepAt, threaded: TypedComp) -> TypedComp {
        let fin = TypedBinder::new(self.mint("fin"), step.ty());
        let a = TypedBinder::new(self.mint("a"), CoreType::Source(step.done.clone()));
        let b = TypedBinder::new(self.mint("a"), CoreType::Source(step.done.clone()));
        let ret = |x: &TypedBinder| {
            TypedComp::new(
                CompSig::new(x.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(super::binder_var(x)),
            )
        };
        let unwrap = TypedComp::new(
            CompSig::new(a.ty().clone(), EffRow::Empty),
            TypedCompKind::Case(
                super::binder_var(&fin),
                vec![
                    (step.more_pattern(a.clone()), ret(&a)),
                    (step.done_pattern(b.clone()), ret(&b)),
                ],
            ),
        );
        Self::bind(threaded, fin, unwrap)
    }

    /// Rewrite a value. An escaping producer thunk (a lambda whose body is latent
    /// in a fused operation) gains one `ev@<id>` parameter per fused operation
    /// plus the accumulator, its body is threaded, and its type changes with its
    /// parameters: the state quantifier when nothing pins the accumulator, then
    /// the ambient row, both bound inside the thunk's own type because it is the
    /// force site, in another function, that instantiates them.
    ///
    /// A pure thunk still has its body rewritten. Any other shape carrying a
    /// fused operation (a non-lambda thunk, or one buried in data) is rejected;
    /// the gate's escape analysis already declines those programs, so this is a
    /// belt-and-braces guard.
    fn rewrite_value(
        &mut self,
        v: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedValue> {
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        let carried: BTreeSet<Sym> = flow::value_sig(v, loc, self.latent)
            .into_iter()
            .map(|masked| masked.id)
            .filter(|operation| ops.contains(operation))
            .collect();
        Some(match &super::peel(v).kind {
            TypedValueKind::Thunk(c) => match c.kind() {
                TypedCompKind::Lam(ps, b) if body_folds(b, &ops, self.latent) => {
                    let CoreType::Function(source_fun) = c.sig().result() else {
                        return None;
                    };
                    let carried_evs: BTreeMap<Sym, Sym> = evs
                        .iter()
                        .filter(|(operation, _)| carried.contains(operation))
                        .map(|(operation, evidence)| (*operation, *evidence))
                        .collect();
                    let numbered = self.numbered(&carried_evs)?;
                    let (acc_ty, state, step) = accumulator_type(self.plan, &carried, &numbered)?;
                    let ambient = Sym::from(names::evidence_row(&numbered));
                    let st = TypedBinder::new(Sym::from(STATE_ACC), acc_ty.clone());

                    let mut loc2 = loc.clone();
                    for p in ps {
                        loc2.insert(p.name(), Sig::new());
                    }
                    let mut ps2 = ps.clone();
                    let mut evs2 = BTreeMap::new();
                    for (id, op) in self.ordered(&carried_evs)? {
                        // This lambda value owns its function scheme. Its
                        // declared effect label therefore supplies the clause
                        // arguments in that scheme's vocabulary; searching the
                        // body can instead find a forwarded callee's vocabulary
                        // (or no direct `Do` at all).
                        let inst: Vec<CoreInstantiation> = self
                            .env
                            .operation(op)
                            .map(|sig| label_args(source_fun.body().effects(), sig.effect().name))
                            .unwrap_or_default()
                            .into_iter()
                            .map(CoreInstantiation::Type)
                            .collect();
                        let binder = TypedBinder::new(
                            Sym::from(names::ev(id)),
                            clause_type(op, &acc_ty, &EffRow::Var(ambient), &inst, self.env)?,
                        );
                        evs2.insert(op, binder.name());
                        self.evidence_types
                            .insert(binder.name(), binder.ty().clone());
                        ps2.push(binder);
                    }
                    ps2.push(st.clone());
                    // The thunk's body runs under the ambient row its own type
                    // binds, and everything threaded inside it (evidence rows,
                    // call instantiations, the scope's one Step decision) must
                    // agree on that. Both pieces of context are restored even
                    // when the threading declines, so a `?` cannot leak them.
                    let saved_row = std::mem::replace(&mut self.row, EffRow::Var(ambient));
                    let saved_step = std::mem::replace(&mut self.step, step);
                    let threaded = self.thread_st(b, &evs2, &loc2, &st);
                    self.row = saved_row;
                    self.step = saved_step;
                    let body = threaded?;

                    // The thunk's own scheme remains in force after threading.
                    // State and the ambient residual are appended inside that
                    // scheme; replacing its quantifiers would make the value
                    // disagree with `threaded_thunk_type` at every direct call.
                    let mut quantifiers = source_fun.quantifiers().to_vec();
                    quantifiers.extend(state.map(CoreQuantifier::Type));
                    quantifiers.push(CoreQuantifier::Row(ambient));
                    let lam_sig = CoreFnSig::new(
                        quantifiers,
                        ps2.iter().map(|p| p.ty().clone()).collect(),
                        body.sig().clone(),
                    );
                    let lam = TypedComp::new(
                        CompSig::new(CoreType::Function(Box::new(lam_sig)), EffRow::Empty),
                        TypedCompKind::Lam(ps2, Box::new(body)),
                    );
                    TypedValue::new(
                        CoreType::Thunk(Box::new(lam.sig().clone())),
                        TypedValueKind::Thunk(Box::new(lam)),
                    )
                }
                TypedCompKind::Lam(ps, b) => {
                    let body = self.rewrite(b, loc, evs)?;
                    let lam = TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Lam(ps.clone(), Box::new(body)),
                    );
                    TypedValue::new(v.ty().clone(), TypedValueKind::Thunk(Box::new(lam)))
                }
                _ if body_folds(c, &ops, self.latent) => return None,
                _ => {
                    let body = self.rewrite(c, loc, evs)?;
                    TypedValue::new(v.ty().clone(), TypedValueKind::Thunk(Box::new(body)))
                }
            },
            _ => self.retyped.rebuild(v),
        })
    }

    /// The fused operations paired with their ids, in ascending id order.
    fn ordered(&self, evs: &BTreeMap<Sym, Sym>) -> Option<Vec<(i64, Sym)>> {
        let mut ordered: Vec<(i64, Sym)> = evs
            .keys()
            .map(|op| Some((self.ids.id(*op)?, *op)))
            .collect::<Option<_>>()?;
        ordered.sort_unstable();
        Some(ordered)
    }

    /// Rewrite a computation the accumulator does not thread through: it performs
    /// no fused operation, so only what it contains can need rewriting.
    fn rewrite(&mut self, c: &TypedComp, loc: &Loc, evs: &BTreeMap<Sym, Sym>) -> Option<TypedComp> {
        Some(match c.kind() {
            // A handle here is a consumer: a fold, or the control consumer that
            // is the take slice. A `do` would be an operation the threading
            // missed, and a mask cannot reach here at all, because the gate
            // declines any program containing one.
            TypedCompKind::Handle { ops, .. } => {
                let erased = ops.clone().erase();
                let single_control = matches!(
                    (ops.arms(), erased.iter_with_use().next()),
                    ([arm], Some((_, ru)))
                        if ru.tail && !folds_op(arm.body(), arm.name(), self.latent)
                );
                if single_control {
                    self.lower_consumer(c, evs, loc)?
                } else {
                    self.lower_fold(c, evs, loc)?
                }
            }
            TypedCompKind::Do { .. } | TypedCompKind::Mask(..) => return None,
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.rewrite(m, loc, evs)?;
                // A head whose value the rewrite retyped (an escaping producer
                // thunk gaining parameters) retypes its binder, and every read
                // of the binder after it.
                let x2 = if m2.sig().result() == x.ty() {
                    x.clone()
                } else {
                    self.retyped.insert(x.name(), m2.sig().result().clone());
                    TypedBinder::new(x.name(), m2.sig().result().clone())
                };
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, self.latent, self.flow));
                let n2 = self.rewrite(n, &loc2, evs)?;
                Self::bind(m2, x2, n2)
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.rewrite(t, loc, evs)?;
                let e2 = self.rewrite(e, loc, evs)?;
                TypedComp::new(
                    t2.sig().clone(),
                    TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
                )
            }
            TypedCompKind::Case(v, arms) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Case(
                    v.clone(),
                    arms.iter()
                        .map(|(p, b)| Some((p.clone(), self.rewrite(b, loc, evs)?)))
                        .collect::<Option<_>>()?,
                ),
            ),
            TypedCompKind::Return(v) => {
                let v2 = self.rewrite_value(v, loc, evs)?;
                TypedComp::new(
                    CompSig::new(v2.ty().clone(), c.sig().effects().clone()),
                    TypedCompKind::Return(v2),
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                // The callee's transformed signature is the authority for the
                // call's result and row; the pre-threading witness is stale
                // the moment the callee's returned thunk widened.
                let sig = self.signatures.get(callee).map_or_else(
                    || c.sig().clone(),
                    |new_sig| {
                        super::super::verify::instantiate_fn(new_sig, instantiation)
                            .unwrap_or_else(|_| new_sig.clone())
                            .body()
                            .clone()
                    },
                );
                TypedComp::new(
                    sig,
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation: instantiation.clone(),
                        args: args
                            .iter()
                            .map(|a| self.rewrite_value(a, loc, evs))
                            .collect::<Option<_>>()?,
                    },
                )
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                // The application's signature is derived from the rewritten
                // callee by the verifier's own rule: a Function result,
                // instantiated with the existing arguments, the result from the
                // applied body, and the effects the union of the callee
                // computation's with the applied body's. Copying the old
                // signature leaves a pre-transform row on an application whose
                // rewritten callable derives a narrower one, and the stale row
                // contaminates every parent.
                let callee2 = self.rewrite(callee, loc, evs)?;
                let CoreType::Function(fun) = callee2.sig().result() else {
                    return None;
                };
                let applied = super::super::verify::instantiate_fn(fun, instantiation).ok()?;
                // The exact, fallible union: a non-representable union of two
                // open tails is a State decline, never permission to drop one.
                let effects = super::super::verify::union_rows(
                    callee2.sig().effects(),
                    applied.body().effects(),
                )
                .ok()?;
                let sig = CompSig::new(applied.body().result().clone(), effects);
                TypedComp::new(
                    sig,
                    TypedCompKind::App {
                        callee: Box::new(callee2),
                        instantiation: instantiation.clone(),
                        args: args
                            .iter()
                            .map(|a| self.rewrite_value(a, loc, evs))
                            .collect::<Option<_>>()?,
                    },
                )
            }
            TypedCompKind::Force(v) => {
                let v2 = self.rewrite_value(v, loc, evs)?;
                let sig = match v2.ty() {
                    CoreType::Thunk(inner) => inner.as_ref().clone(),
                    _ => c.sig().clone(),
                };
                TypedComp::new(sig, TypedCompKind::Force(v2))
            }
            TypedCompKind::Lam(ps, b) => TypedComp::new(
                c.sig().clone(),
                TypedCompKind::Lam(ps.clone(), Box::new(self.rewrite(b, loc, evs)?)),
            ),
            // Anything else performs nothing and carries no value this pass can
            // retype, so it stands.
            _ if self.carries_producer(c, loc, evs) => return None,
            _ => c.clone(),
        })
    }

    /// Whether a computation carries a value this slice cannot retype: a thunk
    /// that performs a fused operation changes type when it gains its evidence
    /// and accumulator, and every binder and reference to it must change with it.
    fn carries_producer(&self, c: &TypedComp, loc: &Loc, evs: &BTreeMap<Sym, Sym>) -> bool {
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        let mut found = false;
        super::walk::each_value(c, &mut |v| {
            found |= flow::value_sig(v, loc, self.latent)
                .iter()
                .any(|m| ops.contains(&m.id));
        });
        found
    }

    /// The evidence a producer call passes, one per fused operation in ascending
    /// operation-id order, using the evidence active here.
    fn evidence_args(
        &self,
        evs: &BTreeMap<Sym, Sym>,
        operations: &BTreeSet<Sym>,
        acc: &CoreType,
    ) -> Option<Vec<TypedValue>> {
        let mut ordered: Vec<(i64, Sym)> = operations
            .iter()
            .map(|op| Some((self.ids.id(*op)?, *op)))
            .collect::<Option<_>>()?;
        ordered.sort_unstable();
        ordered
            .into_iter()
            .map(|(_, op)| Some(super::binder_var(&self.evidence(evs, op, acc)?)))
            .collect()
    }

    /// The evidence binder active for `op` here, which a forwarding handler may
    /// have shadowed.
    /// `acc` is the accumulator type where the evidence is used, which is always
    /// the current `st` binder's type: at the handle it is the clause lambda's
    /// own parameter type, and inside a producer it is whatever the producer's
    /// signature says. The minted state quantifier never appears here; it lives
    /// only on producer signatures and producer thunk types, where parametricity
    /// is real, and is instantiated away before any evidence is applied.
    fn evidence(&self, evs: &BTreeMap<Sym, Sym>, op: Sym, acc: &CoreType) -> Option<TypedBinder> {
        let name = *evs.get(&op)?;
        let ty = if let Some(ty) = self.evidence_types.get(&name) {
            ty.clone()
        } else {
            clause_type(op, acc, &self.row.clone(), &[], self.env)?
        };
        Some(TypedBinder::new(name, ty))
    }

    /// Apply an operation's clause to its arguments and the accumulator.
    fn apply_clause(
        ev: &TypedBinder,
        instantiation: &[CoreInstantiation],
        args: Vec<TypedValue>,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let CoreType::Thunk(thunk) = ev.ty() else {
            return None;
        };
        let force = TypedComp::new(
            thunk.as_ref().clone(),
            TypedCompKind::Force(super::binder_var(ev)),
        );
        let CoreType::Function(clause) = thunk.result() else {
            return None;
        };
        // The clause in scope may already be instantiated (a handle's concrete
        // clause, or a producer parameter built at the perform sites'
        // instantiation), in which case the perform's own type arguments have
        // nothing left to apply to. The application's instantiation matches the
        // clause that is actually forced, not the operation's declared scheme.
        let instantiation = if clause.quantifiers().is_empty() {
            Vec::new()
        } else {
            instantiation.to_vec()
        };
        Some(TypedComp::new(
            CompSig::new(st.ty().clone(), clause.body().effects().clone()),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation,
                args,
            },
        ))
    }

    fn numbered(&self, evs: &BTreeMap<Sym, Sym>) -> Option<Vec<i64>> {
        let mut v: Vec<i64> = evs
            .keys()
            .map(|op| self.ids.id(*op))
            .collect::<Option<_>>()?;
        v.sort_unstable();
        Some(v)
    }

    /// What a producing head's tail resumes with, which decides what its bound
    /// result reads: a read observes the pre-operation accumulator, a write unit.
    fn op_tail_kind(
        &self,
        m: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<FoldAKind> {
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        match m.kind() {
            TypedCompKind::Do { operation, .. } if evs.contains_key(operation) => {
                self.plan.kinds.get(operation).copied()
            }
            TypedCompKind::Bind(mm, x, n) if !produces(mm, loc, &ops, self.latent, self.flow) => {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(mm, loc, self.latent, self.flow));
                self.op_tail_kind(n, &loc2, evs)
            }
            _ => None,
        }
    }

    /// A bind typed as what a bind is: the tail's result under the union of
    /// head and tail rows. A bind that reports only its tail's row hides the
    /// head's effects from every parent, which the verifier now rightly
    /// rejects.
    fn bind(head: TypedComp, binder: TypedBinder, tail: TypedComp) -> TypedComp {
        let sig = CompSig::new(
            tail.sig().result().clone(),
            super::union_effects(head.sig().effects(), tail.sig().effects()),
        );
        TypedComp::new(
            sig,
            TypedCompKind::Bind(Box::new(head), binder, Box::new(tail)),
        )
    }

    /// A lambda computation typed as what a lambda is: a function from its
    /// parameters to its body's signature. Every evidence and handle lambda
    /// this engine builds goes through here, because a lambda whose signature
    /// is its body's result is a value the verifier rightly rejects.
    fn lam(params: Vec<TypedBinder>, body: TypedComp) -> TypedComp {
        let sig = CoreFnSig::new(
            Vec::new(),
            params.iter().map(|p| p.ty().clone()).collect(),
            body.sig().clone(),
        );
        TypedComp::new(
            CompSig::new(CoreType::Function(Box::new(sig)), EffRow::Empty),
            TypedCompKind::Lam(params, Box::new(body)),
        )
    }

    fn mint(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }
}

/// The pre-threading type of the thunk a handle body forces.
fn forced_source_type(c: &TypedComp) -> Option<CoreType> {
    match c.kind() {
        TypedCompKind::App { callee, .. } => match callee.kind() {
            TypedCompKind::Force(v) => Some(super::peel(v).ty().clone()),
            _ => None,
        },
        TypedCompKind::Bind(m, _, n) => forced_source_type(m).or_else(|| forced_source_type(n)),
        _ => None,
    }
}

/// The open tail at the end of a row, if any.
fn row_tail(row: &EffRow) -> Option<Sym> {
    match row {
        EffRow::Extend(_, rest) => row_tail(rest),
        EffRow::Var(name) => Some(*name),
        _ => None,
    }
}

/// One lexical type per free name in `wanted`, harvested from its `Var`
/// occurrences everywhere in `c`, tracking bound names so a `wanted` name
/// rebound under an inner binder is NOT recorded from its shadowed occurrence.
/// Every value form is descended (wrapper, aggregate field, thunk body) and
/// every binder that a name can be rebound at extends the bound set for the
/// scope it governs. `None` when a genuinely free occurrence carries two
/// different types, which one bridge cannot serve.
fn lexical_types(c: &TypedComp, wanted: &BTreeSet<Sym>) -> Option<BTreeMap<Sym, TypedValue>> {
    struct Collect<'a> {
        wanted: &'a BTreeSet<Sym>,
        out: BTreeMap<Sym, TypedValue>,
        ok: bool,
    }
    impl Collect<'_> {
        fn value(&mut self, v: &TypedValue, bound: &BTreeSet<Sym>) {
            // The bridge reuses the ACTUAL occurrence, instantiations and all,
            // so a name-keyed map is only sound when every free occurrence is
            // byte-identical; a same-typed occurrence at a different
            // instantiation declines the whole capture.
            if let TypedValueKind::Var { name, .. } = &v.kind {
                if self.wanted.contains(name) && !bound.contains(name) {
                    match self.out.get(name) {
                        Some(existing) if existing != v => self.ok = false,
                        _ => {
                            self.out.insert(*name, v.clone());
                        }
                    }
                    return;
                }
            }
            // Exhaustive by construction: a new value form must be added here or
            // this fails to compile.
            match &v.kind {
                TypedValueKind::Reinterpret(inner)
                | TypedValueKind::NewtypeRepr { value: inner, .. }
                | TypedValueKind::LoweredRepr { value: inner, .. } => self.value(inner, bound),
                TypedValueKind::Thunk(body) => self.comp(body, bound),
                TypedValueKind::Ctor { fields, .. }
                | TypedValueKind::Tuple(fields)
                | TypedValueKind::UnboxedTuple(fields) => {
                    for f in fields {
                        self.value(f, bound);
                    }
                }
                TypedValueKind::UnboxedRecord(fields) => {
                    for (_, f) in fields {
                        self.value(f, bound);
                    }
                }
                TypedValueKind::Var { .. }
                | TypedValueKind::Int(_)
                | TypedValueKind::I64(_)
                | TypedValueKind::U64(_)
                | TypedValueKind::Float(_)
                | TypedValueKind::Bool(_)
                | TypedValueKind::Unit
                | TypedValueKind::Str(_) => {}
            }
        }
        fn comp(&mut self, c: &TypedComp, bound: &BTreeSet<Sym>) {
            match c.kind() {
                TypedCompKind::Bind(m, x, n) => {
                    self.comp(m, bound);
                    let mut b2 = bound.clone();
                    b2.insert(x.name());
                    self.comp(n, &b2);
                }
                TypedCompKind::Lam(ps, body) => {
                    let mut b2 = bound.clone();
                    b2.extend(ps.iter().map(TypedBinder::name));
                    self.comp(body, &b2);
                }
                TypedCompKind::Case(v, arms) => {
                    self.value(v, bound);
                    for (pat, arm) in arms {
                        let mut b2 = bound.clone();
                        pattern_binders(pat, &mut b2);
                        self.comp(arm, &b2);
                    }
                }
                TypedCompKind::Handle {
                    body,
                    ops,
                    return_binder,
                    return_body,
                } => {
                    self.comp(body, bound);
                    for arm in ops.arms() {
                        let mut b2 = bound.clone();
                        b2.extend(arm.params().iter().map(TypedBinder::name));
                        b2.insert(arm.resume().name());
                        self.comp(arm.body(), &b2);
                    }
                    if let Some(rb) = return_body {
                        let mut b2 = bound.clone();
                        if let Some(binder) = return_binder {
                            b2.insert(binder.name());
                        }
                        self.comp(rb, &b2);
                    }
                }
                TypedCompKind::WithReuse { token, freed, body } => {
                    self.value(freed, bound);
                    let mut b2 = bound.clone();
                    b2.insert(token.name());
                    self.comp(body, &b2);
                }
                _ => {
                    super::walk::each_value(c, &mut |v| self.value(v, bound));
                    super::walk::each_subcomp(c, &mut |sc| self.comp(sc, bound));
                }
            }
        }
    }
    let mut collect = Collect {
        wanted,
        out: BTreeMap::new(),
        ok: true,
    };
    collect.comp(c, &BTreeSet::new());
    collect.ok.then_some(collect.out)
}

/// Every binder a pattern introduces.
fn pattern_binders(pat: &super::super::TypedPattern, out: &mut BTreeSet<Sym>) {
    use super::super::TypedPattern;
    match pat {
        TypedPattern::Var(b) => {
            out.insert(b.name());
        }
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            for f in fields.iter().flatten() {
                out.insert(f.name());
            }
        }
        TypedPattern::Wild => {}
    }
}

/// Whether a computation is latent in any fused operation, so a thunk built
/// from it is a producer the moment it is forced.
fn body_folds(c: &TypedComp, ops: &BTreeSet<Sym>, latent: &Latent) -> bool {
    let mut s = Sig::new();
    super::latent::latent(c, latent, &mut s);
    s.iter().any(|m| ops.contains(&m.id))
}

/// Whether running a computation performs any fused operation, so the
/// accumulator must be threaded through it: a `do op`, a call to an
/// operation-latent function, or a force of a thunk whose flow signature carries
/// a fused operation, in any executed position.
///
/// [`latent`](super::latent) cannot see a force of a thunk-valued variable, so
/// this augments it with the flow `loc`.
pub(super) fn produces(
    c: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    latent: &Latent,
    flow: &ThunkFlow,
) -> bool {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => ops.contains(operation),
        TypedCompKind::Call { callee, .. } => latent
            .get(callee)
            .is_some_and(|s| s.iter().any(|m| ops.contains(&m.id))),
        TypedCompKind::App { callee, .. } => {
            matches!(callee.kind(), TypedCompKind::Force(v)
                if flow::value_sig(v, loc, latent).iter().any(|m| ops.contains(&m.id)))
        }
        TypedCompKind::Bind(m, x, n) => {
            produces(m, loc, ops, latent, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, latent, flow));
                produces(n, &loc2, ops, latent, flow)
            }
        }
        TypedCompKind::If(_, t, e) => {
            produces(t, loc, ops, latent, flow) || produces(e, loc, ops, latent, flow)
        }
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .any(|(_, body)| produces(body, loc, ops, latent, flow)),
        TypedCompKind::Mask(_, body) => produces(body, loc, ops, latent, flow),
        _ => false,
    }
}

/// Whether a computation's result value coincides with the threaded accumulator,
/// so the state-mode loop (which yields the accumulator) yields the right answer.
///
/// True when the tail is a read (a read resumes with the accumulator, so it
/// returns the state) or a tail-call to a producer (compiled to return the
/// accumulator, checked transitively). A `return` of any value, a first-class
/// application, or a write tail is not coincident: the producer value differs
/// from the state.
///
/// This is the check the whole engine's correctness in
/// [`StateAnswerMode::Producer`] rests on, and it is why the state rung declines
/// below its own gate: it belongs with the threading rather than the gate,
/// because it reads what each clause resumes with.
fn value_coincident(
    c: &TypedComp,
    plan: &FoldPlan,
    fns: &[TypedCoreFn],
    latent: &Latent,
    flow: &ThunkFlow,
    visited: &mut BTreeSet<Sym>,
) -> bool {
    match c.kind() {
        TypedCompKind::Do { operation, .. } => plan.kinds.get(operation) == Some(&FoldAKind::Acc),
        TypedCompKind::Bind(_, _, n) => value_coincident(n, plan, fns, latent, flow, visited),
        TypedCompKind::If(_, t, e) => {
            value_coincident(t, plan, fns, latent, flow, visited)
                && value_coincident(e, plan, fns, latent, flow, visited)
        }
        TypedCompKind::Case(_, arms) => arms
            .iter()
            .all(|(_, body)| value_coincident(body, plan, fns, latent, flow, visited)),
        TypedCompKind::Mask(_, body) => value_coincident(body, plan, fns, latent, flow, visited),
        TypedCompKind::Call { callee, .. } if produces(c, &Loc::new(), &plan.ops, latent, flow) => {
            // A recursive cycle is coinductively fine: its non-recursive tails are
            // checked on first visit.
            if !visited.insert(*callee) {
                return true;
            }
            fns.iter()
                .find(|f| f.name() == *callee)
                .is_some_and(|f| value_coincident(f.body(), plan, fns, latent, flow, visited))
        }
        _ => false,
    }
}

/// Whether the threaded loop's answer is the one the program means, which is the
/// precondition the threading itself runs under.
///
/// In [`StateAnswerMode::Producer`] the loop yields the accumulator while the
/// answer is the producer's value, so the two must coincide: every fold handle's
/// body must be value-coincident. Otherwise this engine would return the state
/// where the program means the value, and the program falls back to a slower rung
/// that is correct.
///
/// This sits below the gate deliberately: it is the first thing
/// `try_lower_state` asks after fold-uniformity, and it asks nothing the gate
/// answered.
pub(super) fn threads(plan: &FoldPlan, fns: &[TypedCoreFn], analysis: &StateAnalysis<'_>) -> bool {
    let StateAnalysis {
        ids, latent, flow, ..
    } = analysis;
    if plan.ops.iter().any(|op| ids.id(*op).is_none()) {
        return false;
    }
    if plan.answer != StateAnswerMode::Producer {
        return true;
    }
    let Some(handles) = super::evidence::fusion_handles(fns, latent, flow) else {
        return false;
    };
    handles.iter().all(|h| {
        let TypedCompKind::Handle {
            body, ops: clauses, ..
        } = h.kind()
        else {
            return true;
        };
        let erased = clauses.clone().erase();
        let all_folds = !erased.arms().is_empty()
            && erased
                .iter_with_use()
                .all(|(c, ru)| is_fold(c, ru).is_some());
        !all_folds || value_coincident(body, plan, fns, latent, flow, &mut BTreeSet::new())
    })
}

/// The fused operations a function is latent in, which are the ones whose
/// accumulator it threads. Empty for a function that is not a producer.
fn producer_ops(f: &TypedCoreFn, ops: &BTreeSet<Sym>, latent: &Latent) -> BTreeSet<Sym> {
    latent
        .get(&f.name())
        .map(|s| {
            s.iter()
                .map(|m| m.id)
                .filter(|id| ops.contains(id))
                .collect()
        })
        .unwrap_or_default()
}

/// Decide whether the whole program streams a single operation set through
/// handlers this engine can fuse, or `None` to fall back.
///
/// `None` for a mask, an escaping effectful thunk the flow cannot track, an open
/// latent escape, no handles, an unhandled operation, or any handler that is not
/// a fold consumer with a state-transformer return clause, a re-emitting
/// forwarder, a control consumer, or a take. One handler may carry several fold
/// clauses over distinct operations, each threading the one shared accumulator.
pub(super) fn fold_uniform(fns: &[TypedCoreFn], analysis: &StateAnalysis<'_>) -> Option<FoldPlan> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
    } = analysis;
    let mut ops = BTreeSet::new();
    for f in fns {
        collect_ops(f.body(), &mut ops);
    }
    if ops.is_empty() {
        return None;
    }
    let handles = super::evidence::fusion_handles(fns, latent, flow)?;

    let mut kinds = BTreeMap::new();
    let mut answer = StateAnswerMode::Accumulator;
    let mut consumed: BTreeSet<Sym> = BTreeSet::new();
    let mut folds = 0u32;
    let mut takes = 0u32;

    for h in &handles {
        let TypedCompKind::Handle {
            ops: clauses,
            return_binder,
            return_body,
            ..
        } = h.kind()
        else {
            return None;
        };
        // One erased clone per handle, so every clause-shape question below is
        // answered from one neutral representation.
        let erased = clauses.clone().erase();
        let uses: Vec<_> = erased
            .iter_with_use()
            .map(|(c, ru)| (c.clone(), ru))
            .collect();

        if !uses.is_empty() && uses.iter().all(|(c, ru)| is_fold(c, *ru).is_some()) {
            // A fold's return clause is a state transformer. The identity
            // transformer is the writer special case; a get-style `\s -> r` is the
            // general one, applied to the final accumulator.
            let rb = return_body.as_deref().map(|b| b.clone().erase());
            if !rb.as_ref().is_some_and(is_state_transformer) {
                return None;
            }
            if !rb.as_ref().is_some_and(is_id_transformer) {
                answer = StateAnswerMode::Producer;
            }
            for (c, ru) in &uses {
                kinds.insert(c.name, is_fold(c, *ru)?);
                consumed.insert(c.name);
                folds += 1;
            }
            continue;
        }

        let ([arm], [(erased_arm, ru)]) = (clauses.arms(), uses.as_slice()) else {
            return None;
        };
        if is_take(arm, latent) {
            takes += 1;
        } else if ru.tail && folds_op(arm.body(), arm.name(), latent) {
            // A re-emitting forwarder threads the accumulator straight into the
            // outer evidence, so its return clause must pass the source's final
            // value through unchanged.
            let rv = return_binder.as_ref().map(TypedBinder::name);
            let rb = return_body.as_deref().map(|b| b.clone().erase());
            if !is_id_return(rv, rb.as_ref()) {
                return None;
            }
        } else if ru.tail {
            // A control consumer: tail-resumptive but not re-emitting, so its
            // clause is a side effect over a unit state the producer threads
            // unchanged. Any return clause is fine.
        } else {
            return None;
        }
        consumed.insert(erased_arm.name);
    }

    // Every streamed operation must be handled here, and something must consume.
    // A pure forwarding or control chain belongs to the evidence engine, which
    // runs first, so reaching here means a fold or a take.
    if consumed != ops || folds + takes == 0 {
        return None;
    }

    // An effectful thunk handed to a callee this engine will not thread would gain
    // parameters its un-threaded force site cannot supply. The evidence engine
    // threads such callees through the flow analysis; this one does not.
    let forcers = generic_forcers(fns);
    if fns.iter().any(|f| {
        let loc: Loc = f
            .params()
            .iter()
            .map(TypedBinder::name)
            .zip(flow.param[&f.name()].iter().cloned())
            .collect();
        state_escapes(f.body(), &loc, &ops, &forcers, latent, flow)
    }) {
        return None;
    }

    let plan = FoldPlan {
        pins: pins(&kinds, env)?,
        ops,
        kinds,
        answer,
        early: if takes > 0 {
            EarlyExitMode::ShortCircuit
        } else {
            EarlyExitMode::Continue
        },
    };

    // Every producer must have an expressible threaded signature, which is where
    // typing the one accumulator it threads is decided: chains that share no
    // producer are free to disagree on the accumulator, and do.
    for f in fns {
        let ops = producer_ops(f, &plan.ops, latent);
        if !ops.is_empty() {
            plan_producer(f, &ops, &plan, ids, fns, latent, env)?;
        }
    }

    Some(plan)
}

/// A `stake`-style early-terminating handler: a parameter-passing clause that
/// re-emits and resumes on one branch but drops the continuation on the other, so
/// the threaded state gains a `Step` wrapper the producer can stop on.
fn is_take(arm: &TypedHandleOp, latent: &Latent) -> bool {
    let TypedCompKind::Return(v) = arm.body().kind() else {
        return false;
    };
    let TypedValueKind::Thunk(t) = &super::peel(v).kind else {
        return false;
    };
    let TypedCompKind::Lam(ps, inner) = t.kind() else {
        return false;
    };
    if ps.len() != 1 {
        return false;
    }
    let Some((b1, b2)) = tail_if(inner) else {
        return false;
    };
    let aliases = BTreeSet::from([arm.resume().name()]);
    folds_op(inner, arm.name(), latent)
        && branch_resumes(b1, &aliases) != branch_resumes(b2, &aliases)
}

/// The branches of a take clause's tail `if`, skipping its leading counter-test
/// binds. `None` when the clause is not that shape.
fn tail_if(c: &TypedComp) -> Option<(&TypedComp, &TypedComp)> {
    match c.kind() {
        TypedCompKind::Bind(_, _, n) => tail_if(n),
        TypedCompKind::If(_, t, e) => Some((t, e)),
        _ => None,
    }
}

/// Whether a branch uses a resume alias, so it resumes rather than dropping it.
fn branch_resumes(c: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    !free_comp_vars(c).is_disjoint(aliases)
}

/// Whether a computation is latent in one operation, so it is a producer body.
fn folds_op(c: &TypedComp, op: Sym, latent: &Latent) -> bool {
    let mut s = Sig::new();
    super::latent::latent(c, latent, &mut s);
    s.iter().any(|m| m.id == op)
}

/// Functions that force a thunk-valued parameter outside any handle: generic loop
/// combinators that drive their thunk at a fixed arity. A fold consumer forces its
/// thunk inside a handle body, where the threading reaches it, so it is not one of
/// these. Handing one an effectful thunk is an un-threadable escape.
fn generic_forcers(fns: &[TypedCoreFn]) -> BTreeSet<Sym> {
    fns.iter()
        .filter(|f| {
            let ps: BTreeSet<Sym> = f.params().iter().map(TypedBinder::name).collect();
            forces_param_bare(f.body(), &ps, false)
        })
        .map(TypedCoreFn::name)
        .collect()
}

/// Whether `c` forces one of `params` (or an A-normal-form alias of one) while not
/// inside a handle body.
fn forces_param_bare(c: &TypedComp, params: &BTreeSet<Sym>, in_handle: bool) -> bool {
    match c.kind() {
        TypedCompKind::App { callee, .. } => {
            (!in_handle
                && matches!(callee.kind(), TypedCompKind::Force(v)
                    if super::as_var(v).is_some_and(|n| params.contains(&n))))
                || forces_param_bare(callee, params, in_handle)
        }
        TypedCompKind::Bind(m, x, n) => {
            if forces_param_bare(m, params, in_handle) {
                return true;
            }
            // Track `return p to x` so a forced alias resolves back to the param.
            if let TypedCompKind::Return(v) = m.kind() {
                if super::as_var(v).is_some_and(|n| params.contains(&n)) {
                    let mut ps = params.clone();
                    ps.insert(x.name());
                    return forces_param_bare(n, &ps, in_handle);
                }
            }
            forces_param_bare(n, params, in_handle)
        }
        // A handle drives any thunk forced in its body or clauses through the
        // consumer threading, so those forces are not bare.
        TypedCompKind::Handle {
            body,
            ops,
            return_body,
            ..
        } => {
            forces_param_bare(body, params, true)
                || ops
                    .arms()
                    .iter()
                    .any(|o| forces_param_bare(o.body(), params, true))
                || return_body
                    .as_deref()
                    .is_some_and(|rb| forces_param_bare(rb, params, true))
        }
        _ => {
            let mut found = false;
            each_subcomp(c, &mut |sc| {
                found |= forces_param_bare(sc, params, in_handle);
            });
            found
        }
    }
}

/// Whether the body hands an effectful thunk to a callee this engine will not
/// thread the force site of.
fn state_escapes(
    c: &TypedComp,
    loc: &Loc,
    ops: &BTreeSet<Sym>,
    forcers: &BTreeSet<Sym>,
    latent: &Latent,
    flow: &ThunkFlow,
) -> bool {
    match c.kind() {
        TypedCompKind::Call { callee, args, .. } => {
            forcers.contains(callee)
                && args.iter().any(|a| {
                    flow::value_sig(a, loc, latent)
                        .iter()
                        .any(|m| ops.contains(&m.id))
                })
        }
        TypedCompKind::Bind(m, x, n) => {
            state_escapes(m, loc, ops, forcers, latent, flow) || {
                let mut loc2 = loc.clone();
                loc2.insert(x.name(), flow::result_sig(m, loc, latent, flow));
                state_escapes(n, &loc2, ops, forcers, latent, flow)
            }
        }
        _ => {
            let mut found = false;
            each_subcomp(c, &mut |sc| {
                found |= state_escapes(sc, loc, ops, forcers, latent, flow);
            });
            found
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::types::ty::Label;
    use crate::types::Type;

    use super::super::super::verify::OperationSig;
    use super::*;

    fn env_with(ops: &[(&str, &str, Type)]) -> VerifyEnv {
        let mut env = VerifyEnv::new();
        for (op, effect, result) in ops {
            env.insert_operation(
                Sym::new(op),
                OperationSig::new(
                    Vec::new(),
                    Vec::new(),
                    CoreType::Source(result.clone()),
                    Label::bare(Sym::new(effect)),
                ),
            );
        }
        env
    }

    fn kinds(entries: &[(&str, FoldAKind)]) -> BTreeMap<Sym, FoldAKind> {
        entries.iter().map(|(op, k)| (Sym::new(op), *k)).collect()
    }

    fn plan_over(entries: &[(&str, FoldAKind)], env: &VerifyEnv) -> FoldPlan {
        let kinds = kinds(entries);
        FoldPlan {
            ops: kinds.keys().copied().collect(),
            pins: pins(&kinds, env).expect("every operation is declared"),
            kinds,
            answer: StateAnswerMode::Accumulator,
            early: EarlyExitMode::Continue,
        }
    }

    fn ops(names: &[&str]) -> BTreeSet<Sym> {
        names.iter().map(|n| Sym::new(n)).collect()
    }

    #[test]
    #[should_panic(
        expected = "an accumulator-answer state plan can only bind an unclassified producer result when that result is Unit"
    )]
    fn accumulator_answer_excludes_value_bearing_unclassified_producer_results() {
        let st = TypedBinder::new(Sym::from(STATE_ACC), CoreType::Source(Type::Int));
        let _ = bound_producer_result(
            StateAnswerMode::Accumulator,
            None,
            &st,
            &CoreType::Source(Type::Int),
        );
    }

    fn thunk_performing(op: Sym, instantiation: Type) -> TypedValue {
        let unit = CoreType::Source(Type::Unit);
        let body = TypedComp::new(
            CompSig::new(unit, EffRow::Empty),
            TypedCompKind::Do {
                operation: op,
                instantiation: vec![CoreInstantiation::Type(instantiation)],
                args: Vec::new(),
            },
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(body.sig().clone())),
            TypedValueKind::Thunk(Box::new(body)),
        )
    }

    // `stake_go` performs its re-emit inside the state-transformer thunk its
    // handler clause returns. That `Do` is still the producer declaration's
    // evidence instantiation; a sub-computation-only walk silently misses it.
    #[test]
    fn lexical_instantiation_finds_a_perform_inside_a_returned_thunk() {
        let op = Sym::new("emit");
        let element = Sym::new("element");
        let thunk = thunk_performing(op, Type::Var(element));
        let outer = TypedComp::new(
            CompSig::new(thunk.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(thunk),
        );

        assert_eq!(
            lexical_instantiation(&outer, op, &[], &Latent::new(), LEXICAL_DEPTH),
            Some(vec![CoreInstantiation::Type(Type::Var(element))])
        );
    }

    // Two escaping thunks performing the same operation at different types do
    // not admit one shared evidence clause. Traversing thunk bodies must retain
    // the existing conflict result rather than selecting whichever is visited
    // first.
    #[test]
    fn conflicting_thunk_performs_have_no_lexical_instantiation() {
        let op = Sym::new("emit");
        let first_value = thunk_performing(op, Type::Int);
        let second_value = thunk_performing(op, Type::Bool);
        let first = TypedComp::new(
            CompSig::new(first_value.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(first_value),
        );
        let second = TypedComp::new(
            CompSig::new(second_value.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(second_value),
        );
        let result = second.sig().clone();
        let first_result = first.sig().result().clone();
        let outer = TypedComp::new(
            result,
            TypedCompKind::Bind(
                Box::new(first),
                TypedBinder::new(Sym::new("ignored_thunk"), first_result),
                Box::new(second),
            ),
        );

        assert_eq!(
            lexical_instantiation(&outer, op, &[], &Latent::new(), LEXICAL_DEPTH),
            None
        );
    }

    // The operation declaration conventionally calls its parameter `a`, and a
    // producer may independently bind an unrelated result `a`. `stake_go` is
    // exactly this collision: its re-emitted payload is `b`. The actual `Do<b>`
    // inside the returned transformer, not either printed `a`, owns the clause.
    #[test]
    fn producer_evidence_uses_the_thunked_perform_not_a_colliding_name() {
        let declaration_a = Sym::new("a");
        let payload_b = Sym::new("b");
        let operation = Sym::new("emit");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                vec![CoreQuantifier::Type(declaration_a)],
                vec![CoreType::Source(Type::Var(declaration_a))],
                CoreType::Source(Type::Unit),
                Label {
                    name: Sym::new("Emit"),
                    args: vec![Type::Var(declaration_a)],
                },
            ),
        );
        let plan = plan_over(&[("emit", FoldAKind::Unit)], &env);
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let thunk = thunk_performing(operation, Type::Var(payload_b));
        let body = TypedComp::new(
            CompSig::new(thunk.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(thunk),
        );
        let producer = TypedCoreFn::new(
            Sym::new("collision_producer"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(
                vec![
                    CoreQuantifier::Type(declaration_a),
                    CoreQuantifier::Type(payload_b),
                ],
                Vec::new(),
                body.sig().clone(),
            ),
            0,
        );

        let planned = plan_producer(
            &producer,
            &plan.ops,
            &plan,
            &ids,
            std::slice::from_ref(&producer),
            &Latent::new(),
            &env,
        )
        .expect("the producer has one concrete evidence scheme");
        let CoreType::Thunk(evidence) = planned.evidence[0].ty() else {
            panic!("the producer receives thunked evidence");
        };
        let CoreType::Function(clause) = evidence.result() else {
            panic!("the evidence contains a clause function");
        };
        assert!(clause.quantifiers().is_empty());
        assert_eq!(
            clause.params()[0],
            CoreType::Source(Type::Var(payload_b)),
            "the actual payload b wins over the unrelated canonical a"
        );
    }

    // Forwarding through a polymorphic producer substitutes the complete
    // operation instantiation. Type and row arguments follow the same call
    // edge; retaining the callee's row variable would split one evidence scheme
    // into two vocabularies.
    #[test]
    fn forwarding_substitutes_mixed_type_and_row_operation_arguments() {
        let operation = Sym::new("mixed_emit");
        let target_name = Sym::new("mixed_target");
        let element = Sym::new("element");
        let residual = Sym::new("residual");
        let unit = CoreType::Source(Type::Unit);
        let target_body = TypedComp::new(
            CompSig::new(unit.clone(), EffRow::Var(residual)),
            TypedCompKind::Do {
                operation,
                instantiation: vec![
                    CoreInstantiation::Type(Type::Var(element)),
                    CoreInstantiation::Row(EffRow::Var(residual)),
                ],
                args: Vec::new(),
            },
        );
        let target = TypedCoreFn::new(
            target_name,
            Vec::new(),
            target_body.clone(),
            CoreFnSig::new(
                vec![CoreQuantifier::Type(element), CoreQuantifier::Row(residual)],
                Vec::new(),
                target_body.sig().clone(),
            ),
            0,
        );
        let concrete_row = EffRow::singleton(Sym::new("IO"));
        let call = TypedComp::new(
            CompSig::new(unit, concrete_row.clone()),
            TypedCompKind::Call {
                callee: target_name,
                instantiation: vec![
                    CoreInstantiation::Type(Type::Int),
                    CoreInstantiation::Row(concrete_row.clone()),
                ],
                args: Vec::new(),
            },
        );
        let functions = [target];
        let latent = super::super::latent::latent_map(&functions);

        assert_eq!(
            lexical_instantiation(&call, operation, &functions, &latent, LEXICAL_DEPTH),
            Some(vec![
                CoreInstantiation::Type(Type::Int),
                CoreInstantiation::Row(concrete_row),
            ])
        );
    }

    // A writer streams only writes, so nothing observes the accumulator and every
    // producer stays parametric in it. This is what lets one stream producer feed
    // two chains at two accumulator types in a single program.
    #[test]
    fn writes_alone_leave_the_accumulator_free() {
        let env = env_with(&[("tell", "Writer", Type::Unit)]);
        let plan = plan_over(&[("tell", FoldAKind::Unit)], &env);
        assert_eq!(
            plan.accumulator_for(&ops(&["tell"])),
            Some(Accumulator::Free)
        );
    }

    // An escaping producer thunk can already bind source quantifiers. State
    // threading appends its state and ambient binders inside that same thunk;
    // it must not replace the source scheme, or the rewritten value and every
    // direct call typed by the signature prepass disagree.
    #[test]
    fn a_quantified_escaping_thunk_keeps_its_source_scheme() {
        let env = env_with(&[("tell", "Writer", Type::Unit)]);
        let plan = plan_over(&[("tell", FoldAKind::Unit)], &env);
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let source_row = Sym::new("source_row");
        let unit = CoreType::Source(Type::Unit);
        let effects = EffRow::Extend(
            Label::bare(Sym::new("Writer")),
            Box::new(EffRow::Var(source_row)),
        );
        let parameter = TypedBinder::new(Sym::new("u"), unit.clone());
        let body = TypedComp::new(
            CompSig::new(unit.clone(), effects.clone()),
            TypedCompKind::Do {
                operation: Sym::new("tell"),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let source_sig = CoreFnSig::new(
            vec![CoreQuantifier::Row(source_row)],
            vec![unit.clone()],
            CompSig::new(unit, effects),
        );
        let lambda = TypedComp::new(
            CompSig::new(CoreType::Function(Box::new(source_sig)), EffRow::Empty),
            TypedCompKind::Lam(vec![parameter], Box::new(body)),
        );
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        );
        let operation = Sym::new("tell");
        let evs = BTreeMap::from([(operation, Sym::from(names::ev(0)))]);
        let flow = ThunkFlow {
            ret: BTreeMap::new(),
            param: BTreeMap::new(),
        };
        let mut fresh = crate::util::fresh::Fresh::new();
        let mut threader = Threader {
            plan: &plan,
            ids: &ids,
            env: &env,
            latent: &Latent::new(),
            flow: &flow,
            drift: &DriftLog::new(true),
            retyped: Retyped::new(),
            evidence_types: BTreeMap::new(),
            signatures: BTreeMap::new(),
            step: None,
            row: EffRow::Empty,
            fresh: &mut fresh,
        };

        let rewritten = threader
            .rewrite_value(&thunk, &Loc::new(), &evs)
            .expect("the quantified producer thunk threads");
        let expected = threaded_thunk_type(thunk.ty(), &plan.ops, &plan, &ids, &env)
            .expect("the signature prepass types the same thunk");

        assert_eq!(rewritten.ty(), &expected);
        let CoreType::Thunk(rewritten_thunk) = rewritten.ty() else {
            panic!("the rewritten value remains a thunk: {:?}", rewritten.ty());
        };
        let CoreType::Function(rewritten_fun) = rewritten_thunk.result() else {
            panic!("the thunk still contains a function: {rewritten_thunk:?}");
        };
        assert_eq!(
            rewritten_fun.quantifiers().first(),
            Some(&CoreQuantifier::Row(source_row)),
            "the source scheme precedes State's appended binders"
        );
    }

    // A forwarded thunk whose row no longer carries the effect has no declared
    // operation instantiation. Even a same-spelled quantifier on the thunk is a
    // distinct binder, so the evidence must retain the operation's generic
    // scheme rather than manufacture a dependency by name.
    #[test]
    fn an_unlabelled_forwarded_thunk_does_not_guess_from_a_same_spelled_binder() {
        let operation_element = Sym::new("shadowed_element");
        let thunk_element = Sym::fresh_named(operation_element);
        assert_eq!(operation_element.as_str(), thunk_element.as_str());
        assert_ne!(operation_element, thunk_element);

        let residual = Sym::new("e");
        let operation = Sym::new("emit");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                vec![CoreQuantifier::Type(operation_element)],
                vec![CoreType::Source(Type::Var(operation_element))],
                CoreType::Source(Type::Unit),
                Label {
                    name: Sym::new("Emit"),
                    args: vec![Type::Var(operation_element)],
                },
            ),
        );
        let plan = plan_over(&[("emit", FoldAKind::Unit)], &env);
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let unit = CoreType::Source(Type::Unit);
        let declared = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                vec![CoreQuantifier::Type(thunk_element)],
                vec![unit.clone()],
                CompSig::new(unit, EffRow::Var(residual)),
            ))),
            EffRow::Empty,
        )));

        let threaded = threaded_thunk_type(&declared, &plan.ops, &plan, &ids, &env)
            .expect("the forwarded thunk has a threaded type");
        let CoreType::Thunk(thunk) = threaded else {
            panic!("the result remains a thunk: {threaded:?}");
        };
        let CoreType::Function(function) = thunk.result() else {
            panic!("the thunk contains a function: {thunk:?}");
        };
        let CoreType::Thunk(evidence) = &function.params()[1] else {
            panic!(
                "the second parameter is evidence: {:?}",
                function.params()[1]
            );
        };
        let CoreType::Function(clause) = evidence.result() else {
            panic!("the evidence contains a clause: {evidence:?}");
        };
        assert_eq!(
            clause.quantifiers(),
            [CoreQuantifier::Type(operation_element)],
            "without a label the operation clause stays generic"
        );
        assert_eq!(
            clause.params()[0],
            CoreType::Source(Type::Var(operation_element)),
            "printed spelling cannot capture the operation binder"
        );
    }

    // Ordinary top-level instantiation must stop at the thunk's own rank. The
    // inner binder deliberately prints like the outer one, while its Emit label
    // makes the threaded evidence depend on the inner identity; instantiating
    // the outer scheme at Int must preserve both witnesses unchanged.
    #[test]
    fn top_level_instantiation_preserves_a_nested_same_spelled_thunk_scheme() {
        let outer_element = Sym::new("ranked_element");
        let inner_element = Sym::fresh_named(outer_element);
        assert_eq!(outer_element.as_str(), inner_element.as_str());
        assert_ne!(outer_element, inner_element);

        let operation_element = Sym::new("operation_element");
        let operation = Sym::new("ranked_emit");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                vec![CoreQuantifier::Type(operation_element)],
                vec![CoreType::Source(Type::Var(operation_element))],
                CoreType::Source(Type::Unit),
                Label {
                    name: Sym::new("RankedEmit"),
                    args: vec![Type::Var(operation_element)],
                },
            ),
        );
        let plan = plan_over(&[("ranked_emit", FoldAKind::Unit)], &env);
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let unit = CoreType::Source(Type::Unit);
        let declared = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                vec![CoreQuantifier::Type(inner_element)],
                vec![unit.clone()],
                CompSig::new(
                    unit,
                    EffRow::Extend(
                        Label {
                            name: Sym::new("RankedEmit"),
                            args: vec![Type::Var(inner_element)],
                        },
                        Box::new(EffRow::Empty),
                    ),
                ),
            ))),
            EffRow::Empty,
        )));
        let threaded = threaded_thunk_type(&declared, &plan.ops, &plan, &ids, &env)
            .expect("the nested thunk receives typed evidence");
        let top = CoreFnSig::new(
            vec![CoreQuantifier::Type(outer_element)],
            Vec::new(),
            CompSig::new(threaded, EffRow::Empty),
        );

        let applied = super::super::super::verify::instantiate_fn(
            &top,
            &[CoreInstantiation::Type(Type::Int)],
        )
        .expect("ordinary top-level instantiation is well-kinded");
        let CoreType::Thunk(thunk) = applied.body().result() else {
            panic!("the top-level result remains a thunk");
        };
        let CoreType::Function(function) = thunk.result() else {
            panic!("the thunk remains callable");
        };
        assert_eq!(
            function.quantifiers().first(),
            Some(&CoreQuantifier::Type(inner_element)),
            "outer instantiation cannot consume the nested binder"
        );
        let CoreType::Thunk(evidence) = &function.params()[1] else {
            panic!("the threaded second parameter is evidence");
        };
        let CoreType::Function(clause) = evidence.result() else {
            panic!("the evidence contains a clause function");
        };
        assert!(clause.quantifiers().is_empty());
        assert_eq!(
            clause.params()[0],
            CoreType::Source(Type::Var(inner_element)),
            "the clause remains dependent on the nested binder"
        );
    }

    // A read resumes with the accumulator itself, so the operation's declared
    // result is the accumulator and pins its type: a producer reading `get` then
    // observes it as an `Int`, which a quantifier would make unverifiable.
    // A candidate name rebound under an inner Lam must be harvested only at its
    // free occurrence, never the shadowed one: the free `x : Int` outside is
    // what the bridge would retype, and the inner `x : Bool` is a different
    // binder the collector must not confuse for it.
    #[test]
    fn lexical_collector_respects_inner_shadowing() {
        let int = CoreType::Source(Type::Int);
        let boolean = CoreType::Source(Type::Bool);
        let x_free = TypedValue::new(
            int.clone(),
            TypedValueKind::Var {
                name: Sym::new("x"),
                instantiation: Vec::new(),
            },
        );
        // `return x` where x : Int, then a thunk `\(x : Bool) -> return x`.
        let inner_lam = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    vec![boolean.clone()],
                    CompSig::new(boolean.clone(), EffRow::Empty),
                ))),
                EffRow::Empty,
            ),
            TypedCompKind::Lam(
                vec![TypedBinder::new(Sym::new("x"), boolean.clone())],
                Box::new(TypedComp::new(
                    CompSig::new(boolean.clone(), EffRow::Empty),
                    TypedCompKind::Return(TypedValue::new(
                        boolean,
                        TypedValueKind::Var {
                            name: Sym::new("x"),
                            instantiation: Vec::new(),
                        },
                    )),
                )),
            ),
        );
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(inner_lam.sig().clone())),
            TypedValueKind::Thunk(Box::new(inner_lam)),
        );
        let body = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(thunk.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(thunk),
                )),
                TypedBinder::new(Sym::new("_t"), CoreType::Source(Type::Unit)),
                Box::new(TypedComp::new(
                    CompSig::new(int.clone(), EffRow::Empty),
                    TypedCompKind::Return(x_free),
                )),
            ),
        );
        let mut wanted: BTreeSet<Sym> = BTreeSet::new();
        wanted.insert(Sym::new("x"));
        let types = lexical_types(&body, &wanted).expect("no genuine free conflict");
        // The free `x` is captured at its Int occurrence; the inner Bool `x`
        // under the lambda is shadowed and never recorded.
        assert_eq!(types.get(&Sym::new("x")).map(TypedValue::ty), Some(&int));
    }

    // Cover a candidate shadowed by a WithReuse token and a genuinely free
    // occurrence buried under an aggregate and a representation wrapper. The
    // collector must exclude the first and find the second.
    #[test]
    fn lexical_collector_excludes_reuse_token_and_finds_wrapped_free() {
        let int = CoreType::Source(Type::Int);
        let free_ref = TypedValue::new(
            int.clone(),
            TypedValueKind::Var {
                name: Sym::new("y"),
                instantiation: Vec::new(),
            },
        );
        // `y` free, buried under Tuple(.., Reinterpret(y)).
        let wrapped = TypedValue::new(
            CoreType::Source(Type::Tuple(vec![Type::Int])),
            TypedValueKind::Tuple(vec![TypedValue::new(
                int.clone(),
                TypedValueKind::Reinterpret(Box::new(free_ref)),
            )]),
        );
        // A WithReuse whose token is named `y`, shadowing any outer `y` in body.
        let shadow = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::WithReuse {
                token: TypedBinder::new(
                    Sym::new("y"),
                    CoreType::ReuseToken(Box::new(CoreType::Source(Type::Unit))),
                ),
                freed: TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit),
                body: Box::new(TypedComp::new(
                    CompSig::new(int.clone(), EffRow::Empty),
                    TypedCompKind::Return(TypedValue::new(
                        int.clone(),
                        TypedValueKind::Var {
                            name: Sym::new("y"),
                            instantiation: Vec::new(),
                        },
                    )),
                )),
            },
        );
        let body = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(shadow),
                TypedBinder::new(Sym::new("_t"), CoreType::Source(Type::Unit)),
                Box::new(TypedComp::new(
                    CompSig::new(int.clone(), EffRow::Empty),
                    TypedCompKind::Return(wrapped),
                )),
            ),
        );
        let mut wanted: BTreeSet<Sym> = BTreeSet::new();
        wanted.insert(Sym::new("y"));
        let types = lexical_types(&body, &wanted).expect("the free y is unambiguous");
        // Found under the wrapper at Int; the reuse-token-shadowed y is excluded,
        // so no ReuseToken type poisons the capture.
        assert_eq!(types.get(&Sym::new("y")).map(TypedValue::ty), Some(&int));
    }

    #[test]
    fn a_read_pins_the_accumulator_to_its_result() {
        let env = env_with(&[("get", "State", Type::Int), ("put", "State", Type::Unit)]);
        let plan = plan_over(&[("get", FoldAKind::Acc), ("put", FoldAKind::Unit)], &env);
        assert_eq!(
            plan.accumulator_for(&ops(&["get", "put"])),
            Some(Accumulator::Pinned(CoreType::Source(Type::Int)))
        );
    }

    // One producer threads one accumulator, so two reads it performs cannot pin
    // that accumulator to two types. The untyped pass has no types to check and
    // threads them together regardless; here it is a decline, not a miscompile.
    #[test]
    fn one_producer_reading_two_types_declines() {
        let env = env_with(&[("get", "State", Type::Int), ("peek", "Other", Type::Bool)]);
        let plan = plan_over(&[("get", FoldAKind::Acc), ("peek", FoldAKind::Acc)], &env);
        assert_eq!(plan.accumulator_for(&ops(&["get", "peek"])), None);
    }

    // A nullary producer, the shape a `get`/`put` state handler threads.
    fn producer(name: &str) -> TypedCoreFn {
        let unit = CoreType::Source(Type::Unit);
        TypedCoreFn::new(
            Sym::new(name),
            Vec::new(),
            TypedComp::new(
                CompSig::new(unit.clone(), EffRow::Empty),
                TypedCompKind::Return(TypedValue::new(unit.clone(), TypedValueKind::Unit)),
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(unit, EffRow::Empty)),
            0,
        )
    }

    // The order a producer's threaded parameters go in, which three separately
    // rewritten sites have to agree on: its declaration, its call sites, and the
    // accumulator's own type.
    #[test]
    fn a_producer_takes_its_evidence_then_the_accumulator() {
        let env = env_with(&[("get", "State", Type::Int), ("put", "State", Type::Unit)]);
        let plan = plan_over(&[("get", FoldAKind::Acc), ("put", FoldAKind::Unit)], &env);
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let f = producer("tick");
        let out = plan_producer(&f, &plan.ops, &plan, &ids, &[], &Latent::new(), &env)
            .expect("a plannable producer");

        // `get` sorts before `put`, so the evidence is `ev@0, ev@1`, and the
        // accumulator trails it, the canonical convention pinned by
        // `examples/eff_state.pr`: `fn tick(ev@0, ev@1, st@)`.
        let names: Vec<String> = out
            .params(f.params())
            .iter()
            .map(|p| p.name().as_str().to_string())
            .collect();
        assert_eq!(names, ["ev@0", "ev@1", "st@"]);

        // A read pins the accumulator, so it is concrete and adds no quantifier.
        assert_eq!(out.accumulator.ty(), &CoreType::Source(Type::Int));
        assert_eq!(out.quantifiers, [CoreQuantifier::Row(out.ambient)]);
    }

    // A nullary operation's clause is not padded with a unit parameter the way an
    // evidence clause is. The accumulator is appended to every clause, so a
    // nullary operation's clause already takes one argument, and padding it would
    // declare an argument the perform site does not pass.
    #[test]
    fn a_nullary_clause_takes_the_accumulator_alone() {
        let env = env_with(&[("get", "State", Type::Int)]);
        let plan = plan_over(&[("get", FoldAKind::Acc)], &env);
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let f = producer("tick");
        let out = plan_producer(&f, &plan.ops, &plan, &ids, &[], &Latent::new(), &env)
            .expect("a plannable producer");

        let CoreType::Thunk(thunk) = out.evidence[0].ty() else {
            panic!("evidence is a thunk: {:?}", out.evidence[0].ty());
        };
        let CoreType::Function(clause) = thunk.result() else {
            panic!("of a clause function: {:?}", thunk.result());
        };
        assert_eq!(clause.params(), [CoreType::Source(Type::Int)]);
        assert_eq!(clause.body().result(), &CoreType::Source(Type::Int));
    }

    // A read in tail position is the smallest thing the producer rewrite has to
    // get right: `get()` becomes `force(ev@0)(st@)`, an application of the
    // operation's clause to the accumulator alone, returning the next
    // accumulator. The evidence is forced, not called, and the accumulator is the
    // only argument because the operation is nullary.
    #[test]
    fn a_read_in_tail_position_forces_its_evidence_on_the_accumulator() {
        let env = env_with(&[("get", "State", Type::Int)]);
        let plan = plan_over(&[("get", FoldAKind::Acc)], &env);
        let int = CoreType::Source(Type::Int);
        let st = TypedBinder::new(Sym::from(STATE_ACC), int.clone());
        let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
        evs.insert(Sym::new("get"), Sym::from(names::ev(0)));
        let flow = ThunkFlow {
            ret: BTreeMap::new(),
            param: BTreeMap::new(),
        };
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let mut threader = Threader {
            plan: &plan,
            ids: &ids,
            env: &env,
            latent: &Latent::new(),
            flow: &flow,
            drift: &DriftLog::new(true),
            retyped: Retyped::new(),
            evidence_types: BTreeMap::new(),
            signatures: BTreeMap::new(),
            step: None,
            row: EffRow::Empty,
            fresh: &mut crate::util::fresh::Fresh::new(),
        };
        let read = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::Do {
                operation: Sym::new("get"),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );

        let out = threader
            .thread_st(&read, &evs, &Loc::new(), &st)
            .expect("a read threads");

        let TypedCompKind::App { callee, args, .. } = out.kind() else {
            panic!("a read becomes an application: {:?}", out.kind());
        };
        assert!(
            matches!(callee.kind(), TypedCompKind::Force(v) if super::super::as_var(v) == Some(Sym::from(names::ev(0)))),
            "of its forced evidence: {:?}",
            callee.kind()
        );
        assert_eq!(args.len(), 1, "to the accumulator alone");
        assert_eq!(super::super::as_var(&args[0]), Some(Sym::from(STATE_ACC)));
        assert_eq!(out.sig().result(), &int, "and it yields the accumulator");
    }

    // The `put` clause of a parameter-passing state handler, as a typed tree:
    // `\(_s) -> k(())(s2)`, whose inner body is `force(k)(()) to k'; force(k')(s2)`.
    fn write_clause(acc: Sym, resume: Sym, s2: &TypedBinder) -> TypedComp {
        let unit = CoreType::Source(Type::Unit);
        let int = CoreType::Source(Type::Int);
        let kont = TypedBinder::new(
            Sym::new("k'"),
            CoreType::Thunk(Box::new(CompSig::new(int.clone(), EffRow::Empty))),
        );
        let resumed = TypedComp::new(
            CompSig::new(kont.ty().clone(), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(TypedComp::new(
                    CompSig::new(kont.ty().clone(), EffRow::Empty),
                    TypedCompKind::Force(super::super::binder_var(&TypedBinder::new(
                        resume,
                        CoreType::Thunk(Box::new(CompSig::new(kont.ty().clone(), EffRow::Empty))),
                    ))),
                )),
                instantiation: Vec::new(),
                args: vec![TypedValue::new(unit, TypedValueKind::Unit)],
            },
        );
        let _ = acc;
        TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(resumed),
                kont.clone(),
                Box::new(TypedComp::new(
                    CompSig::new(int, EffRow::Empty),
                    TypedCompKind::App {
                        callee: Box::new(TypedComp::new(
                            CompSig::new(kont.ty().clone(), EffRow::Empty),
                            TypedCompKind::Force(super::super::binder_var(&kont)),
                        )),
                        instantiation: Vec::new(),
                        args: vec![super::super::binder_var(s2)],
                    },
                )),
            ),
        )
    }

    // Stripping a write clause: the double application `k(())(s2)` collapses to
    // `return s2`, the resume binder is gone, and the resume value was unit, so
    // the clause is a write.
    //
    // The kind is the cross-check that keeps this port honest. It is also what
    // the shared `is_fold` reports for the same clause, and the two are computed
    // by different code over different trees: this rewrite walks the typed tree,
    // and `is_fold` walks the erased one. They must agree, and agreeing on a
    // fixture is the weakest form of that; the caller checks it on every program.
    #[test]
    fn stripping_a_write_clause_leaves_the_new_accumulator() {
        let acc = Sym::new("s");
        let resume = Sym::new("k");
        let s2 = TypedBinder::new(Sym::new("s2"), CoreType::Source(Type::Int));
        let clause = write_clause(acc, resume, &s2);
        let mut aliases: BTreeSet<Sym> = BTreeSet::new();
        aliases.insert(resume);

        let (stripped, kind) = strip_state(&clause, &aliases, acc).expect("a write clause strips");

        assert_eq!(kind, FoldAKind::Unit, "resuming with unit is a write");
        let TypedCompKind::Return(v) = stripped.kind() else {
            panic!("the double application collapses to a return: {stripped:?}");
        };
        assert_eq!(
            super::super::as_var(v),
            Some(s2.name()),
            "of the new accumulator the clause resumed into"
        );
        assert!(
            free_comp_vars(&stripped).is_disjoint(&aliases),
            "and the resume binder is gone"
        );
    }

    // The same clause resuming with the accumulator rather than unit is a read,
    // which is what pins the accumulator's type.
    #[test]
    fn a_clause_resuming_with_the_accumulator_is_a_read() {
        let acc = Sym::new("s");
        assert_eq!(
            a_kind(
                &super::super::binder_var(&TypedBinder::new(acc, CoreType::Source(Type::Int))),
                acc
            ),
            Some(FoldAKind::Acc)
        );
        assert_eq!(
            a_kind(
                &TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit),
                acc
            ),
            Some(FoldAKind::Unit)
        );
        // Resuming with anything else is not a fold this engine admits.
        assert_eq!(
            a_kind(
                &super::super::binder_var(&TypedBinder::new(
                    Sym::new("other"),
                    CoreType::Source(Type::Int)
                )),
                acc
            ),
            None
        );
    }

    // A read whose result the tail reads: `let n = get() in return n` threads to
    // `force(ev@0)(st@) to {n}@st; return st@ to n; return {n}@st`.
    //
    // Two things are pinned. The bound `n` reads the accumulator that was live
    // *before* the read, because that is what a read resumes with, so it is `st@`
    // and not the freshly bound one. And the accumulator the tail returns is the
    // new one the read produced, so the two names are distinct: getting either
    // wrong yields a program that threads a stale state.
    #[test]
    fn a_read_binds_the_accumulator_that_was_live_before_it() {
        let env = env_with(&[("get", "State", Type::Int)]);
        let plan = plan_over(&[("get", FoldAKind::Acc)], &env);
        let int = CoreType::Source(Type::Int);
        let st = TypedBinder::new(Sym::from(STATE_ACC), int.clone());
        let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
        evs.insert(Sym::new("get"), Sym::from(names::ev(0)));
        let flow = ThunkFlow {
            ret: BTreeMap::new(),
            param: BTreeMap::new(),
        };
        let ids = OpIds::assign(&plan.ops).expect("ids");
        let mut threader = Threader {
            plan: &plan,
            ids: &ids,
            env: &env,
            latent: &Latent::new(),
            flow: &flow,
            drift: &DriftLog::new(true),
            retyped: Retyped::new(),
            evidence_types: BTreeMap::new(),
            signatures: BTreeMap::new(),
            step: None,
            row: EffRow::Empty,
            fresh: &mut crate::util::fresh::Fresh::new(),
        };
        let n = TypedBinder::new(Sym::new("n"), int.clone());
        let body = TypedComp::new(
            CompSig::new(int.clone(), EffRow::Empty),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(int.clone(), EffRow::Empty),
                    TypedCompKind::Do {
                        operation: Sym::new("get"),
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
                n.clone(),
                Box::new(TypedComp::new(
                    CompSig::new(int, EffRow::Empty),
                    TypedCompKind::Return(super::super::binder_var(&n)),
                )),
            ),
        );

        let out = threader
            .thread_st(&body, &evs, &Loc::new(), &st)
            .expect("a read and its use thread");

        // The outer bind names the accumulator the read produced.
        let TypedCompKind::Bind(head, st2, tail) = out.kind() else {
            panic!("a producing bind stays a bind: {:?}", out.kind());
        };
        assert!(matches!(head.kind(), TypedCompKind::App { .. }));
        assert_ne!(st2.name(), st.name(), "the new accumulator is a fresh name");

        // The tail binds `n` to the accumulator live before the read, then
        // returns the new one.
        let TypedCompKind::Bind(bound, x, rest) = tail.kind() else {
            panic!("the read's result is rebound: {:?}", tail.kind());
        };
        assert_eq!(x.name(), n.name());
        let TypedCompKind::Return(v) = bound.kind() else {
            panic!("from a return: {:?}", bound.kind());
        };
        assert_eq!(
            super::super::as_var(v),
            Some(st.name()),
            "of the accumulator live before the read"
        );
        let TypedCompKind::Return(v) = rest.kind() else {
            panic!("and the tail returns: {:?}", rest.kind());
        };
        assert_eq!(
            super::super::as_var(v),
            Some(st2.name()),
            "the accumulator the read produced"
        );
    }

    // The same two reads in one program, but split across producers that share no
    // operation: two independent chains, each threading its own accumulator at its
    // own type. Asking the question per program would decline this; asking it per
    // producer is what makes each chain answerable.
    #[test]
    fn independent_chains_pin_their_own_accumulators() {
        let env = env_with(&[("get", "State", Type::Int), ("peek", "Other", Type::Bool)]);
        let plan = plan_over(&[("get", FoldAKind::Acc), ("peek", FoldAKind::Acc)], &env);
        assert_eq!(
            plan.accumulator_for(&ops(&["get"])),
            Some(Accumulator::Pinned(CoreType::Source(Type::Int)))
        );
        assert_eq!(
            plan.accumulator_for(&ops(&["peek"])),
            Some(Accumulator::Pinned(CoreType::Source(Type::Bool)))
        );
    }
}
