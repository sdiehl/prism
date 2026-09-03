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
//! `erase_var` does to classify multishot resumption through the
//! canonical [`CheckedHandler`](crate::core::CheckedHandler).
//!
//! `strip_state` cannot live in that layer because it returns a *rewritten
//! clause body*: an erased rewrite has dropped exactly the witnesses this tree
//! exists to carry. [`produces`] and `value_coincident` also stay here because
//! they ask about latent effects and thunk flow, which require the typed tree.
//!
//! Where a rewrite recomputes something a neutral predicate already knows, the
//! two are cross-checked: `strip_state` reports the kind it derived, and its
//! caller checks that against what `is_fold` reports for the same clause.

use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use crate::core::effect_shape::{
    is_fold, is_id_return, is_id_transformer, is_state_transformer, FoldAKind,
};
use crate::types::ty::EffRow;
use crate::types::Type;
use prism_common::sym::Sym;
use prism_syntax::names::{self, STATE_ACC};

use super::super::build::source_type;
use super::super::specialize_support::{
    free_comp_vars, free_value_vars, substitute_terms, substitute_witnesses,
};
use super::super::verify::{
    instantiate_fn, substitute_core_type, substitute_row, union_rows, VerifyEnv,
};
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
pub enum EarlyExitMode {
    Continue,
    ShortCircuit,
}

impl EarlyExitMode {
    const fn short_circuits(self) -> bool {
        matches!(self, Self::ShortCircuit)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum StateAnswerMode {
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
        // Symmetric with the producer arm above: an accumulator-answer plan can
        // rebuild only `Unit`, whose single inhabitant the threaded accumulator
        // can recreate. A value-bearing non-`Unit` producer result has no such
        // reconstruction, so it declines the state rung (returns `None`, which
        // the caller `?`-propagates into the free-monad fallback) rather than
        // crashing. Tier selection stays unobservable: both answer modes fall
        // through on what they cannot rebuild.
        None => (result == &CoreType::Source(Type::Unit)).then(super::unit_value),
    }
}

/// What the gate decided: which operations stream, how each fold clause resumes,
/// the answer convention the threading needs, and what each read pins the
/// accumulator to.
///
/// Returning these facts keeps the analysis from having a hidden channel into
/// the rewrite, as the evidence prepass does.
#[derive(Debug)]
pub struct FoldPlan {
    /// The operations streamed through fold, forward, control, and take handlers.
    pub ops: BTreeSet<Sym>,
    /// Per fold clause, the value its tail resumes with.
    pub kinds: BTreeMap<Sym, FoldAKind>,
    /// Whether the threaded loop's accumulator is the program's answer.
    pub answer: StateAnswerMode,
    /// Whether any handler terminates the stream early.
    pub early: EarlyExitMode,
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
    #[must_use]
    pub fn accumulator_for(&self, ops: &BTreeSet<Sym>) -> Option<Accumulator> {
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
///
/// A strategy may select only some operations, but it must keep the prepared
/// program's numbering and analyses at every gate and rewrite site.
#[derive(Debug)]
pub struct StateAnalysis<'a> {
    ids: &'a OpIds,
    latent: &'a Latent,
    flow: &'a ThunkFlow,
    env: &'a VerifyEnv,
}

impl<'a> StateAnalysis<'a> {
    #[must_use]
    pub const fn new(
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
pub enum Accumulator {
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
pub struct ProducerPlan {
    /// The ambient residual row, last in the quantifier list so an existing
    /// instantiation's positional arguments do not move.
    pub ambient: Sym,
    /// The evidence this producer takes, one per fused operation in ascending
    /// operation-id order, which is the one order evidence is ever laid out in.
    pub evidence: Vec<TypedBinder>,
    /// The trailing accumulator parameter, after the evidence.
    pub accumulator: TypedBinder,
    /// The threaded scheme: the original quantifiers, then the state type when
    /// the accumulator is free, then the ambient row.
    pub quantifiers: Vec<CoreQuantifier>,
    /// The one `Step` instantiation this producer threads under in an
    /// early-exit program, decided here with the accumulator so declaration,
    /// guards, patterns and evidence cannot disagree.
    pub step: Option<StepAt>,
}

impl ProducerPlan {
    /// The threaded parameter list: the producer's own, then its evidence, then
    /// the accumulator.
    #[must_use]
    pub fn params(&self, declared: &[TypedBinder]) -> Vec<TypedBinder> {
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
        let source = source_type(&base).ok()?;
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
                        let substituted =
                            substitute_core_type(&CoreType::Source(t), quantifiers, instantiation);
                        source_type(&substituted).ok().map(CoreInstantiation::Type)
                    }
                    CoreInstantiation::Row(row) => Some(CoreInstantiation::Row(substitute_row(
                        &row,
                        quantifiers,
                        instantiation,
                    ))),
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
    let (quantifiers, op_params) = instantiate_fn(
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
mod program;
mod strip;
mod thread;
mod uniformity;

pub use program::thread_program;
#[cfg(test)]
use strip::strip_state;
#[cfg(test)]
use thread::{a_kind, Threader};
#[cfg(test)]
use uniformity::lexical_types;
pub use uniformity::{fold_uniform, produces, threads};

#[cfg(test)]
mod tests;
