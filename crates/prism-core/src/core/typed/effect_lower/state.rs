//! State fusion: the fold-uniformity gate.
//!
//! A fold consumer handles its operation by parameter passing, so its clause
//! carries an accumulator from one operation to the next rather than answering
//! each one in isolation. This engine compiles the chain to an explicit left
//! fold, threading that accumulator through every producer. What lands here is
//! the gate that decides whether a program is shaped for that at all; the
//! threading itself follows.
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

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::mem;
use std::slice;

use crate::core::effect_shape::{
    direct_kind, is_fold, is_id_transformer, is_state_transformer, passes_return, FoldAKind,
};
use crate::types::ty::EffRow;
use crate::types::Type;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names::{self, ENTRY_POINT, STATE_ACC};

use super::super::build::{lower_value_type, source_type};
use super::super::specialize_support::{
    free_comp_vars, free_value_vars, substitute_terms, substitute_witnesses, Rewrite,
};
use super::super::verify::{
    core_subtype, instantiate_constructor, instantiate_fn, instantiate_operation,
    rename_row_variable_in_row, rename_row_variable_in_type, substitute_core_type, substitute_row,
    union_rows, ConstructorSig, OperationSig, VerifyEnv,
};
use super::super::TypedPattern;
use super::super::{
    on_core_stack, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType,
    TypedHandleOp, TypedHandler,
};
use super::diagnostics::DriftLog;
use super::erase_control::StepAt;
use super::flow::{self, Loc, Sig, ThunkFlow};
use super::latent::Latent;
use super::ops::OpIds;
use super::walk::{collect_ops, each_subcomp, each_subterm};
use super::{TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind};
use retype::Retyped;

/// A clause's parameters: the operation's own, or one unit parameter when the
/// operation is nullary.
///
/// A clause is applied, and an application needs an argument, so the nullary
/// case takes the unit witness the perform site passes. The clause type and the
/// perform site must agree on this, so both read it here.
#[must_use]
pub fn clause_params(declared: &[CoreType]) -> Vec<CoreType> {
    if declared.is_empty() {
        vec![CoreType::Source(Type::Unit)]
    } else {
        declared.to_vec()
    }
}

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
    /// The threaded scope yields the accumulator and the scope's own value
    /// side by side, which is the ordinary state monad: the accumulator-only
    /// conventions above are the special cases where one of the two can be
    /// recovered from the other.
    Pair,
}

/// The pair a scope in [`StateAnswerMode::Pair`] yields: the accumulator, then
/// the value the scope would have returned.
///
/// Unboxed, so the product costs nothing where it stays inside a function and
/// follows the boxed boundary plan only where it escapes one.
pub(super) fn pair_type(accumulator: &CoreType, value: &CoreType) -> Option<CoreType> {
    Some(CoreType::Source(Type::UnboxedTuple(vec![
        source_type(accumulator).ok()?,
        source_type(value).ok()?,
    ])))
}

/// The pair a scope carries inside its step: the accumulator, then the value the
/// scope would have returned.
///
/// Boxed where [`pair_type`] is not, because a constructor field holds one
/// runtime word and an unboxed product is two.
pub(super) fn carried_pair(accumulator: &CoreType, value: &CoreType) -> Option<CoreType> {
    Some(CoreType::Source(Type::Tuple(vec![
        source_type(accumulator).ok()?,
        source_type(value).ok()?,
    ])))
}

/// `(accumulator, value)` at the type the two components carry, boxed to sit in
/// a constructor field.
pub(super) fn carried_value(accumulator: TypedValue, value: TypedValue) -> Option<TypedValue> {
    let ty = carried_pair(accumulator.ty(), value.ty())?;
    Some(TypedValue::new(
        ty,
        TypedValueKind::Tuple(vec![accumulator, value]),
    ))
}

/// What a scope yields where it carries its value and can also leave through an
/// abort: a scope that left has no value to carry, so the two ride together
/// under `SMore` and the abort's payload travels alone.
pub(super) fn carried_result(step: &StepAt, value: &CoreType) -> Option<CoreType> {
    let pair = carried_pair(&CoreType::Source(step.more.clone()), value)?;
    Some(StepAt::new(source_type(&pair).ok()?, step.done.clone()).ty())
}

/// What a state-channel scope over `accumulator` yields for a scope whose own
/// value has type `value`: the accumulator alone where the answer convention
/// can recover the value from it, the two side by side where it cannot.
///
/// `step` is the wrap already applied to `accumulator`. A take's two payloads
/// are the same accumulator, so the pair stays outside it; an abort's is a
/// payload of its own, and only `SMore` has room for the value.
pub(super) fn state_result(
    plan: &FoldPlan,
    accumulator: &CoreType,
    step: Option<&StepAt>,
    value: &CoreType,
) -> Result<CoreType, String> {
    if plan.answer != StateAnswerMode::Pair {
        return Ok(accumulator.clone());
    }
    let unspelled = || "a threaded value with no source spelling".to_owned();
    step.filter(|at| at.more != at.done)
        .map_or_else(
            || pair_type(accumulator, value),
            |at| carried_result(at, value),
        )
        .ok_or_else(unspelled)
}

/// The two components of a [`pair_type`] or a [`carried_pair`], or `None` for
/// any other type. One reader for both, because a boundary asks what the pair
/// holds without caring which side of a step it was carried on.
pub(super) fn pair_parts(ty: &CoreType) -> Option<(CoreType, CoreType)> {
    let CoreType::Source(Type::UnboxedTuple(fields) | Type::Tuple(fields)) = ty else {
        return None;
    };
    let [accumulator, value] = fields.as_slice() else {
        return None;
    };
    Some((carried_component(accumulator), carried_component(value)))
}

// The Core type a pair component was stored at. [`pair_type`] records each
// component through `source_type`, whose one non-identity case is the CBPV
// thunk/function encoding, so recovering a function component means going back
// through that encoding rather than re-wrapping the source shape it printed as.
fn carried_component(ty: &Type) -> CoreType {
    match ty {
        Type::Fun(..) | Type::Forall(..) | Type::RowForall(..) => lower_value_type(ty),
        _ => CoreType::Source(ty.clone()),
    }
}

/// `#(accumulator, value)` at the type the two components carry.
pub(super) fn pair_value(accumulator: TypedValue, value: TypedValue) -> Option<TypedValue> {
    let ty = pair_type(accumulator.ty(), value.ty())?;
    Some(TypedValue::new(
        ty,
        TypedValueKind::UnboxedTuple(vec![accumulator, value]),
    ))
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
        // A clause resuming with a value of its own hands that value back
        // through the pair its evidence answers with, so it is read there and
        // never rebuilt here.
        Some(FoldAKind::Value) => None,
        None if answer != StateAnswerMode::Accumulator => None,
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
/// the rewrite.
#[derive(Clone, Debug)]
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
    /// The operations whose clause never resumes.
    pub aborts: BTreeSet<Sym>,
    /// Per operation, the aborting operations its own clause can raise. A
    /// handler answers such an operation by leaving through a further-out
    /// abort, so performing it can abort as surely as performing the abort
    /// itself, and every perform site steps.
    pub taint: BTreeMap<Sym, BTreeSet<Sym>>,
    /// The operations threaded by value: nothing sharing a handler or a
    /// producer with them folds or takes, so no accumulator is needed.
    by_value: BTreeSet<Sym>,
    /// The aborts that share a channel with an accumulator. Such a scope threads
    /// a step whose done payload is the abort's, so the two travel together.
    folded_aborts: BTreeSet<Sym>,
    /// Per operation sharing a channel with one of those aborts, the abort it
    /// shares it with. The handler answering the abort steps every clause it
    /// has, so an operation beside that abort threads the step wherever it is
    /// carried, including through a producer that cannot reach the abort
    /// itself. Without this the same clause would be stepped at the handle and
    /// bare at the boundary.
    stepped: BTreeMap<Sym, Sym>,
    /// The operations raised to the value channel out of a component that
    /// threads state, because every clause of theirs resumes in tail position
    /// with a value of its own. They cross such a component without joining it,
    /// exactly as an abort does.
    folded_directs: BTreeSet<Sym>,
    /// The operations the entry point's own handler answers with the
    /// unhandled-effect fault. Its arms are at the operation's scheme, so their
    /// clauses stay generic where an elaborated arm's is instantiated.
    entry: BTreeSet<Sym>,
    /// Whether the widened clause and handler shapes are accepted. The gate
    /// that admitted the program and the threading that lowers it read the one
    /// flag, so they cannot disagree about what is in the language.
    pub widen: bool,
    /// Whether a clause needing its continuation as a value is reified here
    /// rather than declined. Under construction, so it is off unless asked
    /// for; the judgment reads it to decide whether such a clause has a class.
    pub reify: bool,
    /// The operations at least one handler reifies. Their performers answer
    /// with a cell rather than a value, so every site that touches one is on
    /// the reified channel.
    pub reified: BTreeSet<Sym>,
}

/// Which channel a producer's operations are threaded through.
///
/// Operations that share a handler or a producer share a channel, so the
/// channel is a property of a producer's whole operation set, never of one
/// operation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Channel {
    /// An accumulator is passed in and returned; the producer's own value is
    /// the accumulator or, for a transforming return clause, bound beside it.
    State,
    /// Only evidence is passed; the producer returns its own value, stepped
    /// over the abort payload when one of its operations can abort.
    Value,
    /// Nothing is passed: the producer answers with an effect cell, and the
    /// handle site drives the queue that cell carries. This is the channel of
    /// an operation whose clause needs the continuation as a value, where no
    /// parameter can stand for the rest of the performer.
    Reified,
}

impl FoldPlan {
    /// The plan the threader runs under once the reified operations have
    /// been answered with cells: the same decisions over the operations that
    /// remain, with nothing left to reify.
    #[must_use]
    pub fn threaded(&self) -> Self {
        Self {
            ops: &self.ops - &self.reified,
            reified: BTreeSet::new(),
            ..self.clone()
        }
    }

    /// The channel a producer latent in `ops` threads, or `None` when `ops`
    /// straddles the two, which a single signature cannot carry.
    ///
    /// The operations the two channels agree about are the ones that take no
    /// accumulator either way: an abort, which never resumes, and a clause that
    /// resumes in tail position with a value of its own, which leaves the state
    /// as it found it. A set mixing those with folded operations still threads
    /// state.
    #[must_use]
    pub fn channel(&self, ops: &BTreeSet<Sym>) -> Option<Channel> {
        // A reified operation answers through the queue, which no accumulator
        // and no evidence parameter reaches. It shares a channel only with
        // other reified operations, because a producer performing one already
        // answers with a cell and cannot also answer with a value.
        let reified = ops.iter().filter(|op| self.reified.contains(op)).count();
        if reified > 0 {
            return (reified == ops.len()).then_some(Channel::Reified);
        }
        let mut by_value = 0;
        let mut all_stateless = true;
        for op in ops.iter().filter(|op| self.by_value.contains(op)) {
            by_value += 1;
            all_stateless &= self.folded_aborts.contains(op) || self.folded_directs.contains(op);
        }
        if by_value == 0 {
            Some(Channel::State)
        } else if by_value == ops.len() {
            Some(Channel::Value)
        } else if all_stateless {
            Some(Channel::State)
        } else {
            None
        }
    }

    /// Whether a scope over `ops` threads an accumulator and can leave through
    /// an abort carried beside it, which is what makes the accumulator a step.
    #[must_use]
    pub fn folds_an_abort(&self, ops: &BTreeSet<Sym>) -> bool {
        ops.iter().any(|op| self.stepped.contains_key(op))
            && self.channel(ops) == Some(Channel::State)
    }

    /// Whether `op`'s clause takes only the operation's own arguments and
    /// answers a step: it never resumes, so there is no accumulator to hand it
    /// and nothing it could do with one.
    #[must_use]
    pub fn value_shaped(&self, op: Sym) -> bool {
        self.by_value.contains(&op)
    }

    /// Whether `op` is a stopping arm: an abort its own fold handler answers,
    /// which keeps the state channel's clause and takes the accumulator, but
    /// never resumes, so what it answers is the payload the fold stops with.
    #[must_use]
    pub fn stops(&self, op: Sym) -> bool {
        self.folded_aborts.contains(&op) && !self.by_value.contains(&op)
    }

    /// Whether `op`'s clause answers with the accumulator and a resumed value
    /// side by side, which is where its evidence result is a pair.
    #[must_use]
    pub fn paired(&self, op: Sym) -> bool {
        self.kinds.get(&op) == Some(&FoldAKind::Value)
    }

    /// The one aborting operation among `ops`: `Some(None)` when there is
    /// none, `None` when there are several, whose payloads one result type
    /// cannot carry.
    #[must_use]
    pub fn abort_in(&self, ops: &BTreeSet<Sym>) -> Option<Option<Sym>> {
        let mut found = BTreeSet::new();
        for op in ops {
            if self.aborts.contains(op) {
                found.insert(*op);
            }
            if let Some(raised) = self.taint.get(op) {
                found.extend(raised.iter().copied());
            }
            if let Some(beside) = self.stepped.get(op) {
                found.insert(*beside);
            }
        }
        let mut found = found.into_iter();
        let first = found.next();
        found.next().is_none().then_some(first)
    }

    /// Whether performing `op` can raise `abort`: it is the abort, or a
    /// handler's clause answers it by leaving through the abort.
    #[must_use]
    pub fn raises(&self, abort: Sym, op: Sym) -> bool {
        abort == op
            || self
                .taint
                .get(&op)
                .is_some_and(|through| through.contains(&abort))
    }

    /// The operations whose performance can raise `abort`: the operation
    /// itself, and every operation a handler's clause raises it through.
    #[must_use]
    pub fn raising(&self, abort: Sym) -> BTreeSet<Sym> {
        let mut out = BTreeSet::from([abort]);
        out.extend(
            self.taint
                .iter()
                .filter(|(_, raised)| raised.contains(&abort))
                .map(|(op, _)| *op),
        );
        out
    }

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
    /// Why this engine last declined, in the words the tier explainer shows.
    /// A decline is a shape the engine does not fit, so it is recorded rather
    /// than raised, and the cascade reads it back once the rung is passed over.
    declined: RefCell<Option<String>>,
    /// The operations `discharge_entry` handled at the entry point.
    entry: BTreeSet<Sym>,
    /// Whether the widened clause and handler shapes are accepted. The engine
    /// recognizes strictly more under it, so a program can move to this rung
    /// that the narrow reading sends to a costlier one.
    widen: bool,
    /// Whether a clause needing its continuation as a value is reified rather
    /// than declined.
    reify: bool,
}

impl<'a> StateAnalysis<'a> {
    #[must_use]
    pub const fn new(
        ids: &'a OpIds,
        latent: &'a Latent,
        flow: &'a ThunkFlow,
        env: &'a VerifyEnv,
        entry: BTreeSet<Sym>,
        widen: bool,
        reify: bool,
    ) -> Self {
        Self {
            ids,
            latent,
            flow,
            env,
            declined: RefCell::new(None),
            entry,
            widen,
            reify,
        }
    }

    /// Whether the widened shapes are accepted.
    #[must_use]
    pub const fn widen(&self) -> bool {
        self.widen
    }

    /// Whether a clause needing its continuation as a value is reified.
    #[must_use]
    pub const fn reify(&self) -> bool {
        self.reify
    }

    /// Record why the engine declines. The first note wins: an outer gate
    /// declining after an inner one has already said why keeps the inner word.
    pub(super) fn note(&self, why: impl Into<String>) {
        let mut slot = self.declined.borrow_mut();
        if slot.is_none() {
            *slot = Some(why.into());
        }
    }

    /// Decline with a recorded reason.
    pub(super) fn decline<T>(&self, why: impl Into<String>) -> Option<T> {
        self.note(why);
        None
    }

    /// The recorded reason, once the engine has declined.
    #[must_use]
    pub fn declined(&self) -> Option<String> {
        self.declined.borrow().clone()
    }

    /// The environment with every constructor field declared at its stored
    /// convention. A field the constructor spells as a carrier is widened as
    /// a store site widens the value it holds, so the store that builds it,
    /// the pattern that reads it back, and the scheme the verifier checks
    /// both against agree. A field that cannot be widened, a buried arrow at
    /// a bare row among them, keeps its declaration; a store there falls back
    /// to the value's own type and a read leaves the binder alone.
    #[must_use]
    fn widened_env(&self, plan: &FoldPlan) -> VerifyEnv {
        let mut env = self.env.clone();
        if !plan.widen {
            return env;
        }
        let widened: Vec<(Sym, ConstructorSig)> = self
            .env
            .constructors()
            .map(|(name, sig)| {
                let fields = sig
                    .fields()
                    .iter()
                    .map(|field| {
                        widen_stored(field, plan, self.ids, self.env)
                            .unwrap_or_else(|_| field.clone())
                    })
                    .collect();
                let sig = ConstructorSig::new(
                    sig.quantifiers().to_vec(),
                    sig.tag(),
                    fields,
                    sig.result().clone(),
                );
                (name, sig)
            })
            .collect();
        for (name, sig) in widened {
            env.insert_constructor(name, sig);
        }
        env
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
    /// The residual row the producer runs under: its declared row with the
    /// fused labels removed, ending in the ambient variable. The variable is
    /// the declared tail when the declaration already names it, otherwise a
    /// quantifier appended last so an existing instantiation's positional
    /// arguments do not move.
    pub row: EffRow,
    /// The evidence this producer takes, one per fused operation in ascending
    /// operation-id order, which is the one order evidence is ever laid out in.
    pub evidence: Vec<TypedBinder>,
    /// The trailing accumulator parameter, after the evidence; absent in the
    /// value channel.
    pub accumulator: Option<TypedBinder>,
    /// The threaded scheme: the original quantifiers, then the state type when
    /// the accumulator is free (or the done type when an operation aborts),
    /// then the ambient row when the declaration did not already bind it.
    pub quantifiers: Vec<CoreQuantifier>,
    /// The one `Step` instantiation this producer threads under in an
    /// early-exit program, decided here with the accumulator so declaration,
    /// guards, patterns and evidence cannot disagree.
    pub step: Option<StepAt>,
    /// The value channel's abort, when the producer's operations include one.
    pub abort: Abort,
    /// The threaded result type.
    pub result: CoreType,
}

impl ProducerPlan {
    /// The threaded parameter list: the producer's own, then its evidence, then
    /// the accumulator when there is one.
    #[must_use]
    pub fn params(&self, declared: &[TypedBinder]) -> Vec<TypedBinder> {
        let mut params = declared.to_vec();
        params.extend(self.evidence.iter().cloned());
        params.extend(self.accumulator.iter().cloned());
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
) -> Result<ProducerPlan, String> {
    let numbered: Vec<i64> = {
        let mut numbered: Vec<i64> = ops
            .iter()
            .map(|op| ids.id(*op))
            .collect::<Option<_>>()
            .ok_or("an operation without an id")?;
        numbered.sort_unstable();
        numbered
    };
    let ambient = Sym::from(names::evidence_row(&numbered));
    let row = EffRow::Var(ambient);
    // A producer whose declared tail is already its ambient carries that
    // quantifier in declared position and runs at its own residual; only an
    // unnamed one gains the ambient as an appended quantifier.
    let residual = residual_row(f.sig().body().effects(), &plan.ops, env);
    let named = matches!(residual.tail(), EffRow::Var(name) if *name == ambient);
    // Either way the producer runs at its declared residual: the labels the
    // declaration keeps stand ahead of the ambient, whether that ambient is
    // the declared tail or the appended quantifier.
    let row = if named {
        residual
    } else {
        union_rows(&residual, &row)
            .ok()
            .ok_or("a residual row and an ambient that do not union")?
    };
    // A producer whose body spells no single instantiation still declares the
    // effect's own arguments in its own row, and those fix the operation's
    // effect parameters: a function annotated `! {State(Solver)}` may perform
    // `put` only through generic helpers, so no perform site under it names
    // `Solver` and the lexical harvest comes back empty. One that names no
    // label either carries the evidence only through a parameter, and leaves
    // the effect's parameters to its callers: one quantifier per parameter,
    // which every edge instantiates from the row argument it hands over.
    let inst_of = |op: Sym| {
        let lexical =
            lexical_instantiation(f.body(), op, fns, latent, LEXICAL_DEPTH).unwrap_or_default();
        if !lexical.is_empty() || !plan.widen {
            return lexical;
        }
        let labelled = label_instantiation(f.sig().body().effects(), op, env);
        if labelled.is_empty() {
            synthesized_instantiation(op, plan, ids, env)
        } else {
            labelled
        }
    };
    let mut quantifiers = f.sig().quantifiers().to_vec();
    quantifiers.extend(
        synthesized_quantifiers(ops, inst_of)
            .into_iter()
            .map(CoreQuantifier::Type),
    );

    match plan.channel(ops).ok_or_else(|| no_channel(ops))? {
        Channel::State => {
            let threading = accumulator_type(plan, ops, &numbered)
                .ok_or_else(|| format!("no accumulator type for {}", op_list(ops)))?;
            let accumulator = threading.ty;
            let done = threading.step.as_ref().map(|at| &at.done);
            let evidence: Vec<TypedBinder> = numbered
                .iter()
                .map(|id| {
                    let op = ids.op(*id).ok_or("an operation without a name")?;
                    // An abort takes no accumulator and answers a step, so its
                    // clause is the value channel's even here.
                    let ty = if plan.value_shaped(op) {
                        value_clause_type(op, done, &row, &inst_of(op), env)
                    } else {
                        clause_type(
                            op,
                            &accumulator,
                            done.filter(|_| plan.stops(op)),
                            &row,
                            &inst_of(op),
                            env,
                            plan.paired(op),
                        )
                    }
                    .ok_or_else(|| no_clause_type(op))?;
                    Ok(TypedBinder::new(Sym::from(names::ev(*id)), ty))
                })
                .collect::<Result<_, String>>()?;
            quantifiers.extend(threading.state.map(CoreQuantifier::Type));
            quantifiers.extend(threading.done.map(CoreQuantifier::Type));
            if !named {
                quantifiers.push(CoreQuantifier::Row(ambient));
            }
            let result = state_result(
                plan,
                &accumulator,
                threading.step.as_ref(),
                f.sig().body().result(),
            )?;
            Ok(ProducerPlan {
                row,
                evidence,
                accumulator: Some(TypedBinder::new(Sym::from(STATE_ACC), accumulator)),
                quantifiers,
                step: threading.step,
                abort: None,
                result,
            })
        }
        // A reified producer answers with a cell, so it takes neither
        // evidence nor an accumulator. Building that signature is the reified
        // lowering's own job; nothing threads into it here.
        Channel::Reified => Err(format!(
            "a producer of {} whose operations are reified",
            op_list(ops)
        )),
        Channel::Value => {
            let abort = value_abort(plan, ops, &numbered)
                .ok_or_else(|| format!("several of {} abort", op_list(ops)))?;
            let evidence: Vec<TypedBinder> = numbered
                .iter()
                .map(|id| {
                    let op = ids.op(*id).ok_or("an operation without a name")?;
                    let done = abort
                        .as_ref()
                        .filter(|(a, _)| plan.raises(*a, op))
                        .map(|(_, d)| d);
                    let ty = value_clause_type(op, done, &row, &inst_of(op), env)
                        .ok_or_else(|| no_clause_type(op))?;
                    Ok(TypedBinder::new(Sym::from(names::ev(*id)), ty))
                })
                .collect::<Result<_, String>>()?;
            if let Some((_, Type::Var(done))) = &abort {
                quantifiers.push(CoreQuantifier::Type(*done));
            }
            if !named {
                quantifiers.push(CoreQuantifier::Row(ambient));
            }
            let result = value_result(f.sig().body().result(), abort.as_ref().map(|(_, d)| d))
                .ok_or("a stepped result that is not a source type")?;
            Ok(ProducerPlan {
                row,
                evidence,
                accumulator: None,
                quantifiers,
                step: None,
                abort,
                result,
            })
        }
    }
}

/// The value channel's abort of one scope, when its operations include one:
/// the aborting operation and the done type quantifier the scope's result is
/// stepped over.
pub type Abort = Option<(Sym, Type)>;

/// The abort of a producer over `ops`, its done type named from the operation
/// ids so a declaration and a caller's nested thunk type agree without sharing
/// a counter. `None` when several of the operations abort.
fn value_abort(plan: &FoldPlan, ops: &BTreeSet<Sym>, numbered: &[i64]) -> Option<Abort> {
    let abort = plan.abort_in(ops)?;
    Some(abort.map(|op| (op, Type::Var(Sym::from(names::done_type(numbered))))))
}

/// A value-threaded result: the declared one, stepped over `done` when the
/// scope can abort.
fn value_result(declared: &CoreType, done: Option<&Type>) -> Option<CoreType> {
    Some(match done {
        Some(done) => StepAt::new(source_type(declared).ok()?, done.clone()).ty(),
        None => declared.clone(),
    })
}

/// How a state-channel scope threads its accumulator: the type a producer
/// declares and a carrying thunk takes, the quantifiers that type introduces,
/// and the step instantiation live inside the scope.
pub(super) struct Threading {
    /// The accumulator's type, already wrapped where the scope steps.
    pub ty: CoreType,
    /// The accumulator quantifier, when no read pins the accumulator.
    pub state: Option<Sym>,
    /// The done quantifier, when the scope can abort.
    pub done: Option<Sym>,
    /// The step the accumulator is wrapped in, when the scope can stop before
    /// the stream does.
    pub step: Option<StepAt>,
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
fn accumulator_type(plan: &FoldPlan, ops: &BTreeSet<Sym>, numbered: &[i64]) -> Option<Threading> {
    let (base, state) = match plan.accumulator_for(ops)? {
        Accumulator::Pinned(ty) => (ty, None),
        Accumulator::Free => {
            let name = Sym::from(names::state_type(numbered));
            (CoreType::Source(Type::Var(name)), Some(name))
        }
    };
    // In an early-exit program the threaded accumulator is `Step Base`
    // everywhere a producer declares or a thunk carries it, and in a scope that
    // can abort it is `Step Base Done`: the same protocol, its done payload
    // read off the abort rather than off the accumulator. One home for the
    // wrap; the callers that need the base (instantiation sites) read it from
    // the returned Step.
    if plan.early.short_circuits() {
        let source = source_type(&base).ok()?;
        let at = StepAt::new(source.clone(), source);
        return Some(Threading {
            ty: at.ty(),
            state,
            done: None,
            step: Some(at),
        });
    }
    if plan.folds_an_abort(ops) {
        plan.abort_in(ops)??;
        let done = Sym::from(names::done_type(numbered));
        let at = StepAt::new(source_type(&base).ok()?, Type::Var(done));
        return Some(Threading {
            ty: at.ty(),
            state,
            done: Some(done),
            step: Some(at),
        });
    }
    Some(Threading {
        ty: base,
        state,
        done: None,
        step: None,
    })
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

/// The ids of the planned operations of `effect`, ascending: the vocabulary
/// an effect-parameter quantifier is named in, which a declaration and every
/// thunk type nested in it share.
fn effect_ids(effect: Sym, plan: &FoldPlan, ids: &OpIds, env: &VerifyEnv) -> Vec<i64> {
    let mut out: Vec<i64> = plan
        .ops
        .iter()
        .filter(|op| {
            env.operation(**op)
                .is_some_and(|sig| sig.effect().name == effect)
        })
        .filter_map(|op| ids.id(*op))
        .collect();
    out.sort_unstable();
    out
}

/// The instantiation `op`'s effect parameters take where nothing in view
/// fixes them: one quantifier per parameter of the effect, named from the
/// effect's planned operations. Empty for an effect without parameters,
/// which needed no fixing.
fn synthesized_instantiation(
    op: Sym,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Vec<CoreInstantiation> {
    let Some(sig) = env.operation(op) else {
        return Vec::new();
    };
    let numbered = effect_ids(sig.effect().name, plan, ids, env);
    (0..sig.effect().args.len())
        .map(|index| {
            CoreInstantiation::Type(Type::Var(Sym::from(names::effect_param(&numbered, index))))
        })
        .collect()
}

/// The synthesized effect-parameter quantifiers the clauses of `ops` are
/// built at, each once, in operation order: what the declaration binds.
fn synthesized_quantifiers(
    ops: &BTreeSet<Sym>,
    inst_of: impl Fn(Sym) -> Vec<CoreInstantiation>,
) -> Vec<Sym> {
    let mut out = Vec::new();
    for argument in ops.iter().flat_map(|op| inst_of(*op)) {
        if let CoreInstantiation::Type(Type::Var(name)) = argument {
            if names::is_effect_param(name.as_str()) && !out.contains(&name) {
                out.push(name);
            }
        }
    }
    out
}

/// The instantiation an operation's effect parameters take from a row that
/// names the effect: the label's own type arguments. One home, because a
/// producer's declaration and its rewrite must fix the same parameters.
pub(super) fn label_instantiation(
    row: &EffRow,
    op: Sym,
    env: &VerifyEnv,
) -> Vec<CoreInstantiation> {
    env.operation(op)
        .map(|sig| label_args(row, sig.effect().name))
        .unwrap_or_default()
        .into_iter()
        .map(CoreInstantiation::Type)
        .collect()
}

fn threaded_thunk_type(
    declared: &CoreType,
    ops: &BTreeSet<Sym>,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
    ambient: Option<&EffRow>,
    enclosing: Option<&EffRow>,
) -> Result<CoreType, String> {
    let mut numbered: Vec<i64> = ops
        .iter()
        .map(|op| ids.id(*op))
        .collect::<Option<_>>()
        .ok_or("an operation without an id")?;
    numbered.sort_unstable();
    let CoreType::Thunk(inner) = declared else {
        return Err("a carrying parameter that is not a thunk".into());
    };
    let CoreType::Function(fun) = inner.result() else {
        return Err("a carrying thunk that is not a function".into());
    };
    // The parameter's own pre-threading row names the instantiation: the
    // effect label it carries (`Emit(b)` in `() -> a ! {Emit(b) | e}`) holds
    // the operation's type arguments in the receiving function's own scheme
    // vocabulary. Declarations own their indices; every incoming edge
    // substitutes at use. No caller is consulted.
    // An absent label supplies no binding relationship of its own. A position
    // of a function declaration (`enclosing` is its row) then reads the
    // label that declaration spells, which fixes the parameters the same way
    // for the evidence the function hands the thunk, and failing that the
    // quantifier the declaration synthesizes for them. A stored position has
    // no declaration to consult, and its clause stays generic.
    let inst_of = |op: Sym| -> Vec<CoreInstantiation> {
        let own = label_instantiation(fun.body().effects(), op, env);
        let Some(enclosing) = enclosing.filter(|_| own.is_empty()) else {
            return own;
        };
        let outer = label_instantiation(enclosing, op, env);
        if outer.is_empty() {
            synthesized_instantiation(op, plan, ids, env)
        } else {
            outer
        }
    };
    let mut params = fun.params().to_vec();
    let mut quantifiers = fun.quantifiers().to_vec();
    let (result, row) = match plan.channel(ops).ok_or_else(|| no_channel(ops))? {
        Channel::State => {
            // The state channel runs a thunk at its own residual joined with
            // its receiver's row, as the value channel does. With no receiver
            // in view, an open residual runs at its own tail, the enclosing
            // scheme's quantifier, and a closed one binds a fresh ambient
            // inside the thunk's type for the force site to instantiate.
            let own = residual_row(fun.body().effects(), &plan.ops, env);
            let (row, fresh) = match ambient {
                Some(receiver) => (
                    union_rows(&own, receiver).unwrap_or_else(|_| own.clone()),
                    None,
                ),
                None if matches!(own.tail(), EffRow::Empty) => {
                    let ambient = Sym::from(names::evidence_row(&numbered));
                    (
                        union_rows(&own, &EffRow::Var(ambient))
                            .ok()
                            .ok_or("a residual row and a fresh ambient that do not union")?,
                        Some(ambient),
                    )
                }
                None => (own, None),
            };
            let threading = accumulator_type(plan, ops, &numbered)
                .ok_or_else(|| format!("no accumulator type for {}", op_list(ops)))?;
            let acc = threading.ty;
            let done = threading.step.as_ref().map(|at| &at.done);
            for id in &numbered {
                let op = ids.op(*id).ok_or("an operation without an id")?;
                params.push(
                    if plan.value_shaped(op) {
                        value_clause_type(op, done, &row, &inst_of(op), env)
                    } else {
                        clause_type(
                            op,
                            &acc,
                            done.filter(|_| plan.stops(op)),
                            &row,
                            &inst_of(op),
                            env,
                            plan.paired(op),
                        )
                    }
                    .ok_or_else(|| format!("no clause type for `{}`", op.as_str()))?,
                );
            }
            params.push(acc.clone());
            quantifiers.extend(threading.state.map(CoreQuantifier::Type));
            quantifiers.extend(threading.done.map(CoreQuantifier::Type));
            quantifiers.extend(fresh.map(CoreQuantifier::Row));
            (
                state_result(plan, &acc, threading.step.as_ref(), fun.body().result())?,
                row,
            )
        }
        Channel::Reified => {
            return Err(format!(
                "a carrying position holding {}, which are reified",
                op_list(ops)
            ))
        }
        Channel::Value => {
            // The value channel runs a parameter thunk at its own residual
            // joined with its receiver's row, where the evidence handed to it
            // runs, and a returned thunk at its own residual. A closed residual
            // there binds a fresh ambient inside the thunk's type, which the
            // force site instantiates.
            let own = residual_row(fun.body().effects(), &plan.ops, env);
            let (row, fresh) = match ambient {
                Some(receiver) => (
                    union_rows(&own, receiver).unwrap_or_else(|_| own.clone()),
                    None,
                ),
                None if matches!(own.tail(), EffRow::Empty) => {
                    let ambient = Sym::from(names::evidence_row(&numbered));
                    (
                        union_rows(&own, &EffRow::Var(ambient))
                            .ok()
                            .ok_or("a residual row and a fresh ambient that do not union")?,
                        Some(ambient),
                    )
                }
                None => (own, None),
            };
            let abort = value_abort(plan, ops, &numbered)
                .ok_or_else(|| format!("several of {} abort", op_list(ops)))?;
            for id in &numbered {
                let op = ids.op(*id).ok_or("an operation without an id")?;
                let done = abort
                    .as_ref()
                    .filter(|(a, _)| plan.raises(*a, op))
                    .map(|(_, d)| d);
                params.push(
                    value_clause_type(op, done, &row, &inst_of(op), env)
                        .ok_or_else(|| format!("no clause type for `{}`", op.as_str()))?,
                );
            }
            if let Some((_, Type::Var(done))) = &abort {
                quantifiers.push(CoreQuantifier::Type(*done));
            }
            quantifiers.extend(fresh.map(CoreQuantifier::Row));
            (
                value_result(fun.body().result(), abort.as_ref().map(|(_, d)| d))
                    .ok_or("a stepped thunk result that is not a source type")?,
                row,
            )
        }
    };
    Ok(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            quantifiers,
            params,
            CompSig::new(result, row),
        ))),
        EffRow::Empty,
    ))))
}

/// The ambient row a returned carrier binds on its function's own scheme.
///
/// A carrier whose own residual is closed says nothing about the row its force
/// site runs at, and the receiving parameter of a call it is handed to names
/// that row concretely. Binding the ambient on the function's scheme lets the
/// caller instantiate it exactly where it instantiates everything else; bound
/// inside the returned type instead, the value is polymorphic one rank too
/// high for any parameter to accept it, and every pipeline that hands a
/// returned stream to the next combinator declines.
///
/// `None` where the declaration already says the row: a carrier whose residual
/// ends in a variable is the same variable the caller instantiates, and the
/// state channel binds its ambient inside the thunk because its accumulator
/// travels with it.
pub(super) fn returned_ambient(
    declared: &CoreType,
    ops: &BTreeSet<Sym>,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Option<Sym> {
    if plan.channel(ops)? != Channel::Value {
        return None;
    }
    let CoreType::Thunk(inner) = declared else {
        return None;
    };
    let CoreType::Function(fun) = inner.result() else {
        return None;
    };
    let own = residual_row(fun.body().effects(), &plan.ops, env);
    if !matches!(own.tail(), EffRow::Empty) {
        return None;
    }
    let mut numbered: Vec<i64> = ops.iter().map(|op| ids.id(*op)).collect::<Option<_>>()?;
    numbered.sort_unstable();
    Some(Sym::from(names::evidence_row(&numbered)))
}

/// The fused value-channel operations a row names.
fn carried_ops(row: &EffRow, plan: &FoldPlan, env: &VerifyEnv) -> BTreeSet<Sym> {
    let named: BTreeSet<Sym> = row.labels().into_iter().map(|label| label.name).collect();
    plan.ops
        .iter()
        .copied()
        .filter(|op| {
            env.operation(*op)
                .is_some_and(|sig| named.contains(&sig.effect().name))
        })
        .collect()
}

/// `ty` widened to the convention its own row names, when it is a thunk of a
/// function whose row carries fused operations.
///
/// The thunk binds its own ambient row, so a value of this type is forced at
/// whatever row its force site runs: a carrier stored in data is built in one
/// scope and forced in another, and nothing at the store connects the two.
pub(super) fn widen_carrier(
    ty: &CoreType,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Result<CoreType, String> {
    if !plan.widen {
        return Ok(ty.clone());
    }
    let CoreType::Thunk(inner) = ty else {
        return Ok(ty.clone());
    };
    let CoreType::Function(fun) = inner.result() else {
        return Ok(ty.clone());
    };
    let carried = carried_ops(fun.body().effects(), plan, env);
    if carried.is_empty() {
        return Ok(ty.clone());
    }
    threaded_thunk_type(ty, &carried, plan, ids, env, None, None)
}

/// `declared` with every arrow buried inside it widened.
///
/// The flow follows a thunk from where it is built to where it is forced. One
/// stored in data leaves that path, and the pattern that recovers it invents no
/// signature, so the widening of its type is the only thing that says which
/// evidence its force site must hand it. The outermost arrow is left alone:
/// that one is the flow's answer, threaded by its caller where the flow says
/// the position carries.
pub(super) fn widen_buried(
    declared: &CoreType,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Result<CoreType, String> {
    if !plan.widen {
        return Ok(declared.clone());
    }
    Ok(match declared {
        CoreType::Source(ty) => CoreType::Source(widen_children(ty, plan, ids, env)?),
        CoreType::Thunk(inner) => CoreType::Thunk(Box::new(CompSig::new(
            widen_buried(inner.result(), plan, ids, env)?,
            inner.effects().clone(),
        ))),
        CoreType::Function(fun) => CoreType::Function(Box::new(CoreFnSig::new(
            fun.quantifiers().to_vec(),
            fun.params()
                .iter()
                .map(|p| widen_buried(p, plan, ids, env))
                .collect::<Result<Vec<_>, _>>()?,
            CompSig::new(
                widen_answer(fun.body().result(), plan, ids, env)?,
                fun.body().effects().clone(),
            ),
        ))),
        CoreType::Ref(inner) => CoreType::Ref(Box::new(widen_buried(inner, plan, ids, env)?)),
        CoreType::ReuseToken(inner) => {
            CoreType::ReuseToken(Box::new(widen_buried(inner, plan, ids, env)?))
        }
        CoreType::Lowered(_) => declared.clone(),
    })
}

/// What an arrow answers with, widened where it stands, its own arrow
/// included. A thunk answering with the next step's thunk hands that one
/// over as a value the flow never followed, exactly as a store does, so the
/// widening of its type is the whole of what its force site hands it.
fn widen_answer(
    result: &CoreType,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Result<CoreType, String> {
    widen_carrier(&widen_buried(result, plan, ids, env)?, plan, ids, env)
}

/// The fused operations a carrier type's own row names.
///
/// Empty for anything but a thunk of a function: nothing else is forced, so
/// nothing else takes evidence.
pub(super) fn carrier_ops(ty: &CoreType, plan: &FoldPlan, env: &VerifyEnv) -> BTreeSet<Sym> {
    let CoreType::Thunk(inner) = ty else {
        return BTreeSet::new();
    };
    let CoreType::Function(fun) = inner.result() else {
        return BTreeSet::new();
    };
    carried_ops(fun.body().effects(), plan, env)
}

/// The type a value stored in data has after widening: every arrow buried
/// inside it, and its own if that carries too.
pub(super) fn widen_stored(
    ty: &CoreType,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Result<CoreType, String> {
    widen_carrier(&widen_buried(ty, plan, ids, env)?, plan, ids, env)
}

/// A source type argument widened where it stands, arrow included.
///
/// A buried arrow whose row is a bare variable is refused rather than left
/// alone: only the instantiation says whether that row names a fused
/// operation, and widening changes the arrow's arity, so one declaration
/// cannot serve both a call that fuses and a call that does not.
pub(super) fn widen_argument(
    ty: &Type,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Result<Type, String> {
    if !plan.widen {
        return Ok(ty.clone());
    }
    let inner = widen_children(ty, plan, ids, env)?;
    let Type::Fun(_, row, _) = &inner else {
        return Ok(inner);
    };
    if carried_ops(row, plan, env).is_empty() {
        if matches!(row.tail(), EffRow::Var(_)) && !value_ops(plan).is_empty() {
            return Err("a carrier whose row is polymorphic".into());
        }
        return Ok(inner);
    }
    let widened = widen_carrier(&lower_value_type(&inner), plan, ids, env)?;
    source_type(&widened).map_err(|_| "a widened carrier with no source spelling".to_string())
}

// Every structural child of a source type, widened. Written without a
// catch-all so a new type variant has to be answered here rather than quietly
// hiding a carrier.
fn widen_children(
    ty: &Type,
    plan: &FoldPlan,
    ids: &OpIds,
    env: &VerifyEnv,
) -> Result<Type, String> {
    let each = |ts: &[Type]| -> Result<Vec<Type>, String> {
        ts.iter()
            .map(|t| widen_argument(t, plan, ids, env))
            .collect()
    };
    let one = |t: &Type| -> Result<Box<Type>, String> {
        Ok(Box::new(widen_argument(t, plan, ids, env)?))
    };
    Ok(match ty {
        Type::Con(name, args) => Type::Con(*name, each(args)?),
        Type::Tuple(args) => Type::Tuple(each(args)?),
        Type::UnboxedTuple(args) => Type::UnboxedTuple(each(args)?),
        Type::UnboxedRecord(fields) => Type::UnboxedRecord(
            fields
                .iter()
                .map(|(name, t)| Ok((*name, widen_argument(t, plan, ids, env)?)))
                .collect::<Result<Vec<_>, String>>()?,
        ),
        // A row argument is an effect, not a value position, so nothing it
        // holds is ever forced.
        Type::Fun(params, row, result) => Type::Fun(each(params)?, row.clone(), one(result)?),
        Type::App(head, arg) => Type::App(one(head)?, one(arg)?),
        Type::Forall(name, t) => Type::Forall(*name, one(t)?),
        Type::RowForall(name, t) => Type::RowForall(*name, one(t)?),
        Type::OrNull(t) => Type::OrNull(one(t)?),
        Type::Coeffect(t, row) => Type::Coeffect(one(t)?, row.clone()),
        Type::Row(_)
        | Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str
        | Type::Var(_)
        | Type::Exist(_)
        | Type::Nat(_) => ty.clone(),
    })
}

/// Whether a handler's return binder names a value of unit type, which is the
/// one case where a constant return clause and the identity agree.
pub(super) fn unit_source(binder: Option<&TypedBinder>) -> bool {
    matches!(
        binder.map(TypedBinder::ty),
        Some(CoreType::Source(Type::Unit))
    )
}

/// The operations of a scope, spelled for a decline reason.
pub(super) fn op_list(ops: &BTreeSet<Sym>) -> String {
    ops.iter()
        .map(|op| format!("`{}`", op.as_str()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// An operation whose clause the witness layout cannot type: it is undeclared,
/// or nothing here fixes the effect parameters its argument types mention.
fn no_clause_type(op: Sym) -> String {
    format!("no clause type for `{}`", op.as_str())
}

fn no_channel(ops: &BTreeSet<Sym>) -> String {
    format!("operations {} that share no channel", op_list(ops))
}

/// `row` with every occurrence of every fused operation's effect removed and
/// its tail kept: what a scope still performs once those operations are
/// carried as evidence. Evidence carries the operation however many times the
/// row spells its effect: the checker may spell a label twice for one
/// performance nested under one handler, and no copy is left for a handler
/// that the evidence has replaced.
pub(super) fn residual_row(row: &EffRow, ops: &BTreeSet<Sym>, env: &VerifyEnv) -> EffRow {
    let fused: BTreeSet<Sym> = ops
        .iter()
        .filter_map(|op| env.operation(*op))
        .map(|operation| operation.effect().name)
        .collect();
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !fused.contains(&label.name))
            .cloned(),
        row.tail().clone(),
    )
}

/// A threaded producer with an open declared row names its own ambient: the
/// declared tail is renamed to the evidence-row variable its operations
/// derive, in the signature, every witness and every instantiation. The
/// threaded row then has one tail, and a caller's instantiation of it merges
/// per label with the residual head instead of stacking a second copy.
pub(super) fn name_ambient(
    f: &TypedCoreFn,
    ops: &BTreeSet<Sym>,
    plan: &FoldPlan,
    ids: &OpIds,
) -> Option<TypedCoreFn> {
    if ops.is_empty() || plan.channel(ops)? == Channel::Reified {
        return Some(f.clone());
    }
    let EffRow::Var(old) = f.sig().body().effects().tail() else {
        return Some(f.clone());
    };
    let mut numbered: Vec<i64> = ops.iter().map(|op| ids.id(*op)).collect::<Option<_>>()?;
    numbered.sort_unstable();
    let mut rename = RenameRow {
        old: *old,
        fresh: Sym::from(names::evidence_row(&numbered)),
    };
    Some(rename.function(f, &()))
}

/// Rename one row variable throughout a function, binders included.
struct RenameRow {
    old: Sym,
    fresh: Sym,
}

impl RenameRow {
    fn row(&self, row: &EffRow) -> EffRow {
        rename_row_variable_in_row(row, self.old, self.fresh)
    }

    fn sig(&self, sig: &CompSig) -> CompSig {
        CompSig::new(self.ty(sig.result()), self.row(sig.effects()))
    }

    fn fun(&self, sig: &CoreFnSig) -> CoreFnSig {
        let quantifiers = sig
            .quantifiers()
            .iter()
            .map(|q| match q {
                CoreQuantifier::Row(name) if *name == self.old => CoreQuantifier::Row(self.fresh),
                q => q.clone(),
            })
            .collect();
        CoreFnSig::new(
            quantifiers,
            sig.params().iter().map(|p| self.ty(p)).collect(),
            self.sig(sig.body()),
        )
    }

    fn ty(&self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.sig(sig))),
            CoreType::Function(sig) => CoreType::Function(Box::new(self.fun(sig))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.ty(inner))),
            CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(self.ty(inner))),
            CoreType::Source(inner) => {
                CoreType::Source(rename_row_variable_in_type(inner, self.old, self.fresh))
            }
            CoreType::Lowered(LoweredType::Word) => ty.clone(),
            CoreType::Lowered(LoweredType::Eff(row)) => {
                CoreType::Lowered(LoweredType::Eff(self.row(row)))
            }
            CoreType::Lowered(LoweredType::Queue(row)) => {
                CoreType::Lowered(LoweredType::Queue(self.row(row)))
            }
            CoreType::Lowered(LoweredType::QueueView(row)) => {
                CoreType::Lowered(LoweredType::QueueView(self.row(row)))
            }
        }
    }
}

impl Rewrite for RenameRow {
    type Ctx = ();

    fn function(&mut self, function: &TypedCoreFn, cx: &Self::Ctx) -> TypedCoreFn {
        self.rewrite_function_from_hooks(function, cx)
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, (): &()) -> CoreFnSig {
        self.fun(sig)
    }

    fn comp_sig(&mut self, sig: &CompSig, (): &()) -> CompSig {
        self.sig(sig)
    }

    fn core_type(&mut self, ty: &CoreType, (): &()) -> CoreType {
        self.ty(ty)
    }

    fn instantiation(&mut self, instantiation: &CoreInstantiation, (): &()) -> CoreInstantiation {
        match instantiation {
            CoreInstantiation::Row(row) => CoreInstantiation::Row(self.row(row)),
            CoreInstantiation::Type(ty) => {
                CoreInstantiation::Type(rename_row_variable_in_type(ty, self.old, self.fresh))
            }
        }
    }
}

/// The type of a value-threaded operation's evidence: its clause, which takes
/// the operation's own arguments (one unit argument when it has none, as an
/// erased clause does) and returns the operation's result,
/// stepped over `done` when the operation aborts.
fn value_clause_type(
    op: Sym,
    done: Option<&Type>,
    row: &EffRow,
    instantiation: &[CoreInstantiation],
    env: &VerifyEnv,
) -> Option<CoreType> {
    let (quantifiers, op_params, result) = value_scheme(env.operation(op)?, instantiation)?;
    let clause = CoreFnSig::new(
        quantifiers,
        clause_params(&op_params),
        CompSig::new(value_result(&result, done)?, row.clone()),
    );
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(clause)),
        EffRow::Empty,
    ))))
}

/// A value clause's scheme at `instantiation`: the operation's parameters and
/// result with the effect's own parameters fixed by the label that names them
/// and the quantifiers its parameters mention fixed, and the rest still
/// bound. A quantifier only the result mentions belongs to a never-resuming
/// operation, whose clause hands back a payload and produces no value of that
/// type at all, while every perform site names its own; the one clause serves
/// them all by staying generic there. An effect parameter is never that, even
/// when only the result mentions it (`get() : s`): the label binds it wherever
/// the operation appears.
///
/// A quantifier of the operation's own that its parameters mention is fixed
/// by the perform or the clause, whose instantiation runs over the whole
/// quantifier list in order, exactly as the verifier reads it.
///
/// An absent label fixes no effect parameter, which is a scheme only when
/// nothing needed fixing.
fn value_scheme(
    sig: &OperationSig,
    instantiation: &[CoreInstantiation],
) -> Option<(Vec<CoreQuantifier>, Vec<CoreType>, CoreType)> {
    let quantifiers = sig.quantifiers();
    let kept = result_only(sig);
    let fixed = |q: &CoreQuantifier| !instantiation.is_empty() && effect_position(sig, q).is_some();
    let full: Vec<CoreInstantiation> = quantifiers
        .iter()
        .enumerate()
        .map(|(i, q)| match effect_position(sig, q) {
            Some(slot) if fixed(q) => instantiation.get(slot).cloned(),
            _ if kept.contains(&i) => Some(identity(q)),
            _ if instantiation.len() == quantifiers.len() => instantiation.get(i).cloned(),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let scheme = CoreFnSig::new(
        quantifiers.to_vec(),
        sig.params().to_vec(),
        CompSig::new(sig.result().clone(), EffRow::Empty),
    );
    let applied = instantiate_fn(&scheme, &full).ok()?;
    // A label whose argument is an outer variable spelled like the operation's
    // own quantifier fixes that quantifier all the same: the enclosing
    // signature binds it, so the clause is not generic there.
    let generic = quantifiers
        .iter()
        .enumerate()
        .filter(|(i, q)| kept.contains(i) && !fixed(q))
        .map(|(_, q)| q.clone())
        .collect();
    Some((
        generic,
        applied.params().to_vec(),
        applied.body().result().clone(),
    ))
}

/// The position of `q` among the parameters of the effect `sig` belongs to,
/// when it is one of them.
fn effect_position(sig: &OperationSig, q: &CoreQuantifier) -> Option<usize> {
    let CoreQuantifier::Type(v) = q else {
        return None;
    };
    sig.effect()
        .args
        .iter()
        .position(|arg| matches!(arg, Type::Var(w) if w == v))
}

/// The planned operations the value channel carries.
pub(super) fn value_ops(plan: &FoldPlan) -> BTreeSet<Sym> {
    plan.ops
        .iter()
        .copied()
        .filter(|op| plan.channel(&BTreeSet::from([*op])) == Some(Channel::Value))
        .collect()
}

/// The positions of the quantifiers no parameter of `sig` mentions.
fn result_only(sig: &OperationSig) -> Vec<usize> {
    sig.quantifiers()
        .iter()
        .enumerate()
        .filter(|(_, q)| {
            let probe = match q {
                CoreQuantifier::Type(_) => CoreInstantiation::Type(Type::Unit),
                CoreQuantifier::Row(_) => CoreInstantiation::Row(EffRow::Empty),
            };
            !sig.params().iter().any(|p| {
                substitute_core_type(p, slice::from_ref(*q), slice::from_ref(&probe)) != *p
            })
        })
        .map(|(i, _)| i)
        .collect()
}

const fn identity(q: &CoreQuantifier) -> CoreInstantiation {
    match q {
        CoreQuantifier::Type(v) => CoreInstantiation::Type(Type::Var(*v)),
        CoreQuantifier::Row(v) => CoreInstantiation::Row(EffRow::Var(*v)),
    }
}

/// The quantifiers an arm at the operation's own scheme leaves generic: those
/// it instantiates at their own variable, which nothing but the clause binds.
/// A variable the enclosing function binds is not that, however the scheme
/// spells its own: an effect parameter and the handler's quantifier over it
/// share a name.
pub(super) fn generic_quantifiers(
    sig: &OperationSig,
    instantiation: &[CoreInstantiation],
    bound: &[CoreQuantifier],
) -> Vec<CoreQuantifier> {
    sig.quantifiers()
        .iter()
        .zip(instantiation)
        .filter(|(q, given)| identity(q) == **given && !bound.contains(q))
        .map(|(q, _)| q.clone())
        .collect()
}

/// A program whose entry point handles the operations that reached it.
#[derive(Debug)]
pub struct EntryDischarge {
    /// The operations the entry point's handler answers.
    pub ops: BTreeSet<Sym>,
    /// The program with `main` wrapped in that handler.
    pub fns: Vec<TypedCoreFn>,
}

/// Handle every operation still latent at the entry point there.
///
/// An operation that reaches `main` unhandled is the runtime's unhandled-effect
/// fault, so the arm that discharges it answers with that fault, resuming so
/// the arm is a direct clause and the operation threads by value like any
/// other. `None` when nothing reaches the entry point.
#[must_use]
pub fn discharge_entry(
    fns: &[TypedCoreFn],
    latent: &Latent,
    env: &VerifyEnv,
) -> Option<EntryDischarge> {
    let entry = Sym::new(ENTRY_POINT);
    let ops: BTreeSet<Sym> = latent
        .get(&entry)?
        .iter()
        .filter(|m| m.depth == 0)
        .map(|m| m.id)
        .collect();
    if ops.is_empty() {
        return None;
    }
    let main = fns.iter().find(|f| f.name() == entry)?;
    let body = main.body();
    let outer = CompSig::new(
        body.sig().result().clone(),
        residual_row(body.sig().effects(), &ops, env),
    );
    let aborted = aborted_ops(fns);
    let mut fresh = Fresh::new();
    let mut arms = Vec::with_capacity(ops.len());
    for op in &ops {
        arms.push(fault_arm(
            *op,
            aborted.contains(op),
            &outer,
            env,
            &mut fresh,
        )?);
    }
    let handled = TypedComp::new(
        outer,
        TypedCompKind::Handle {
            body: Box::new(body.clone()),
            return_binder: None,
            return_body: None,
            finally_body: None,
            ops: TypedHandler::new(arms).ok()?,
        },
    );
    let wrapped = TypedCoreFn::new(
        main.name(),
        main.params().to_vec(),
        handled,
        main.sig().clone(),
        main.dict_arity(),
    );
    let fns = fns
        .iter()
        .map(|f| {
            if f.name() == entry {
                wrapped.clone()
            } else {
                f.clone()
            }
        })
        .collect();
    Some(EntryDischarge { ops, fns })
}

/// The operations some handler in the program answers without resuming. An
/// operation has one clause shape across the program, so the entry point's arm
/// for such an operation aborts as well.
fn aborted_ops(fns: &[TypedCoreFn]) -> BTreeSet<Sym> {
    fn visit(c: &TypedComp, out: &mut BTreeSet<Sym>) {
        if let TypedCompKind::Handle { ops, .. } = c.kind() {
            for arm in ops.arms() {
                if !free_comp_vars(arm.body()).contains(&arm.resume().name()) {
                    out.insert(arm.name());
                }
            }
        }
        each_subcomp(c, &mut |sub| visit(sub, out));
    }
    let mut out = BTreeSet::new();
    for f in fns {
        visit(f.body(), &mut out);
    }
    out
}

/// `op(params) resume k => let e = fault in k(e)`, or `op(params) => fault`
/// where the program aborts the operation: the arm that answers an operation
/// nothing handles with the unhandled-effect fault, at the operation's own
/// scheme so the one clause serves every perform site.
fn fault_arm(
    op: Sym,
    aborts: bool,
    outer: &CompSig,
    env: &VerifyEnv,
    fresh: &mut Fresh,
) -> Option<TypedHandleOp> {
    let sig = env.operation(op)?;
    let instantiation: Vec<CoreInstantiation> = sig.quantifiers().iter().map(identity).collect();
    let operation = instantiate_operation(sig, &instantiation).ok()?;
    let mut mint = |hint: &str| Sym::from(names::lowered(hint, fresh.bump()));
    let params = operation
        .params
        .iter()
        .map(|ty| TypedBinder::new(mint("fault_p"), ty.clone()))
        .collect();
    let resumed_sig = CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![operation.result.clone()],
            outer.clone(),
        ))),
        EffRow::Empty,
    );
    let resume = TypedBinder::new(
        mint("fault_k"),
        CoreType::Thunk(Box::new(resumed_sig.clone())),
    );
    let message = TypedValue::new(
        CoreType::Source(Type::Str),
        TypedValueKind::Str(format!("unhandled effect `{}`", op.as_str())),
    );
    if aborts {
        let body = TypedComp::new(outer.clone(), TypedCompKind::Error(message));
        return Some(TypedHandleOp::new(op, instantiation, params, resume, body));
    }
    let answer = TypedBinder::new(mint("fault_e"), operation.result.clone());
    let fault = TypedComp::new(
        CompSig::new(operation.result, EffRow::Empty),
        TypedCompKind::Error(message),
    );
    let resumed = TypedComp::new(
        outer.clone(),
        TypedCompKind::App {
            callee: Box::new(TypedComp::new(
                resumed_sig,
                TypedCompKind::Force(super::binder_var(&resume)),
            )),
            instantiation: Vec::new(),
            args: vec![super::binder_var(&answer)],
        },
    );
    let body = TypedComp::new(
        outer.clone(),
        TypedCompKind::Bind(Box::new(fault), answer, Box::new(resumed)),
    );
    Some(TypedHandleOp::new(op, instantiation, params, resume, body))
}

/// The type of a fused operation's evidence: its clause, which takes the
/// operation's own arguments and the accumulator, and returns the next
/// accumulator, or that accumulator paired with the value the clause resumes
/// with where the accumulator alone cannot stand for it.
///
/// Unlike a continuation-erased clause, this is never padded with a
/// unit parameter when the operation is nullary: the accumulator is appended to
/// every clause, so a nullary operation's clause already takes one argument, and
/// a padded one would take an argument the perform site does not pass.
fn clause_type(
    op: Sym,
    accumulator: &CoreType,
    stops: Option<&Type>,
    row: &EffRow,
    instantiation: &[CoreInstantiation],
    env: &VerifyEnv,
    paired: bool,
) -> Option<CoreType> {
    let sig = env.operation(op)?;
    let instantiation = &pinned(sig, instantiation, paired);
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
    // A stopping arm answers the payload its fold stops with. It takes the
    // accumulator like any other arm and never gives one back, so the step the
    // payload lands in is built at the perform site, which knows what that
    // scope carries.
    let result = match (stops, paired) {
        (Some(done), _) => CoreType::Source(done.clone()),
        (None, true) => pair_type(accumulator, &instantiate_result(sig, instantiation))?,
        (None, false) => accumulator.clone(),
    };
    let clause = CoreFnSig::new(quantifiers, params, CompSig::new(result, row.clone()));
    Some(CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(clause)),
        EffRow::Empty,
    ))))
}

/// The instantiation a clause's type is built at. An effect label pins the
/// effect's own type arguments and leaves an operation's own to the perform
/// sites, which a parameter's declared type cannot see. On this channel a
/// clause answers with the accumulator, so an operation's declared result is
/// no part of it, and a quantifier the clause never mentions is discharged
/// here rather than kept as a scheme no concrete clause could inhabit.
fn pinned(
    sig: &OperationSig,
    instantiation: &[CoreInstantiation],
    paired: bool,
) -> Vec<CoreInstantiation> {
    let quantifiers = sig.quantifiers();
    if instantiation.len() >= quantifiers.len() {
        return instantiation.to_vec();
    }
    let mut mentioned = BTreeSet::new();
    let declared = sig.params().iter().chain(paired.then(|| sig.result()));
    for ty in declared {
        let CoreType::Source(ty) = ty else {
            return instantiation.to_vec();
        };
        ty.free_ty_vars(&mut mentioned);
    }
    let mut pinned = instantiation.to_vec();
    for quantifier in &quantifiers[instantiation.len()..] {
        match quantifier {
            CoreQuantifier::Type(name) if !mentioned.contains(name) => {
                pinned.push(CoreInstantiation::Type(Type::Unit));
            }
            _ => return instantiation.to_vec(),
        }
    }
    pinned
}

/// An operation's declared result at the instantiation its perform sites agree
/// on, or its generic result where they do not: the same fallback
/// [`clause_type`] applies to the parameters, so the two halves of one clause
/// signature are never instantiated apart.
fn instantiate_result(sig: &OperationSig, instantiation: &[CoreInstantiation]) -> CoreType {
    instantiate_fn(
        &CoreFnSig::new(
            sig.quantifiers().to_vec(),
            sig.params().to_vec(),
            CompSig::new(sig.result().clone(), EffRow::Empty),
        ),
        instantiation,
    )
    .map_or_else(
        |_| sig.result().clone(),
        |applied| applied.body().result().clone(),
    )
}

/// Thread a whole fold-uniform program: every producer gains its evidence and
/// accumulator, and everything else is rewritten around them.
///
/// `None` wherever the typed state rung cannot preserve its fusion contract.
mod judgment;
mod mono;
mod program;
mod reify;
mod resume;
mod retype;
mod strip;
mod thread;
mod uniformity;

pub use judgment::{judge_handle, ClauseClass, HandleClass, HandleJudgment};
pub use mono::instantiate_carriers;

pub use program::{thread_program, Threaded};
#[cfg(test)]
use strip::strip_state;
#[cfg(test)]
use thread::{a_kind, Threader};
#[cfg(test)]
use uniformity::lexical_types;
pub use uniformity::{fold_uniform, produces, tail_kind, threads};

#[cfg(test)]
mod tests;
