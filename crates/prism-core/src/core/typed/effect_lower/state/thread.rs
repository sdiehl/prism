//! Accumulator-threading transformation and local escape checks.

mod rewrite;
mod value;

use super::super::checks::kind_name;
use super::super::union_effects;
use super::super::{
    abi::try_word_bridge, as_var, binder_var, peel, subtract::SubtractEffect, unit_value,
};
use super::judgment::{judge_handle, HandleClass, HandleJudgment};
use super::resume::strip_resume;
use super::strip::strip_state;
use super::uniformity::{
    body_folds, branch_resumes, forced_source_type, is_take, lexical_types, row_tail,
};
use super::{
    accumulator_type, bound_producer_result, carried_result, carried_value, carrier_ops,
    clause_type, core_subtype, flow, free_comp_vars, free_value_vars, instantiate_constructor,
    instantiate_fn, is_fold, is_id_transformer, label_args, label_instantiation, mem, names,
    on_core_stack, pair_parts, pair_type, pair_value, passes_return, produces, source_type,
    substitute_core_type, substitute_terms, substitute_witnesses, tail_kind, union_rows,
    value_clause_type, widen_argument, widen_buried, widen_stored, Abort, Accumulator, BTreeMap,
    BTreeSet, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, DriftLog, EffRow,
    FoldAKind, FoldPlan, Latent, Loc, OpIds, Retyped, Sig, StateAnswerMode, StepAt, Sym, ThunkFlow,
    Type, TypedBinder, TypedComp, TypedCompKind, TypedHandleOp, TypedPattern, TypedValue,
    TypedValueKind, VerifyEnv, STATE_ACC,
};
use super::{generic_quantifiers, residual_row, unit_source, value_scheme, Channel};
use crate::core::TypedHandler;

/// The step a threaded result carries its pair inside, or `None` where the pair
/// is the whole result. Read off the type rather than off the scope, because the
/// same helpers run on both sides of the step: inside it a result still steps,
/// past it the pair stands alone.
fn carried_step(ty: &CoreType) -> Option<StepAt> {
    let at = StepAt::of(ty)?;
    pair_parts(&CoreType::Source(at.more.clone())).map(|_| at)
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
                let name = as_var(v)?;
                let resolved = as_var(&resolve(
                    &binder_var(&TypedBinder::new(name, v.ty().clone())),
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

/// The accumulator binder and body of a clause written as a state transformer,
/// which is the shape every arm of a fold handler has.
fn transformer(body: &TypedComp) -> Option<(&TypedBinder, &TypedComp)> {
    let TypedCompKind::Return(v) = body.kind() else {
        return None;
    };
    let TypedValueKind::Thunk(t) = &peel(v).kind else {
        return None;
    };
    let TypedCompKind::Lam(ps, inner) = t.kind() else {
        return None;
    };
    let [acc] = ps.as_slice() else {
        return None;
    };
    Some((acc, inner))
}

/// Whether a computation's head rebinds a live resume alias.
fn is_alias_return(m: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    matches!(m.kind(), TypedCompKind::Return(v)
        if as_var(v).is_some_and(|v| aliases.contains(&v)))
}

/// Whether a computation evaluates to `resume(rv)` for one argument disjoint
/// from the aliases.
fn resume_call(c: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    resume_arg(c, aliases, &BTreeMap::new()).is_some()
}

/// Classify a resume value against the fold lambda's accumulator parameter.
///
/// The typed mirror of [`fold_argument`](crate::core::effect_shape), and
/// `paired` admits the same widened shape there: a resume value of the clause's
/// own, which travels beside the accumulator instead of being rebuilt from it.
pub(super) fn a_kind(a: &TypedValue, acc: Sym, paired: bool) -> Option<FoldAKind> {
    match &peel(a).kind {
        TypedValueKind::Unit => Some(FoldAKind::Unit),
        TypedValueKind::Var { name, .. } if *name == acc => Some(FoldAKind::Acc),
        _ => paired.then_some(FoldAKind::Value),
    }
}

/// The argument of `resume(rv)` when a computation evaluates to a unary
/// application of a resume alias, allowing leading pure binds and resume
/// rebindings. The argument must be disjoint from the aliases, since it is not
/// the resume itself.
pub(super) fn resume_arg(
    c: &TypedComp,
    aliases: &BTreeSet<Sym>,
    subst: &BTreeMap<Sym, TypedValue>,
) -> Option<TypedValue> {
    match c.kind() {
        TypedCompKind::App { callee, args, .. } => {
            if !matches!(callee.kind(), TypedCompKind::Force(k)
                if as_var(k).is_some_and(|k| aliases.contains(&k)))
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
                if as_var(v).is_some_and(|v| aliases.contains(&v)) {
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
    as_var(v)
        .and_then(|name| subst.get(&name))
        .map_or_else(|| v.clone(), Clone::clone)
}

/// The producer-side rewrite: walk a producer body and fold every operation head
/// into the active evidence, so the body becomes a computation returning the
/// accumulator.
#[derive(Debug)]
pub(super) struct Threader<'a> {
    pub plan: &'a FoldPlan,
    /// The whole program's operation numbering. A fused subset keeps its global
    /// holes; renumbering it locally would violate the canonical ABI after
    /// strategies compose.
    pub ids: &'a OpIds,
    pub env: &'a VerifyEnv,
    /// The environment as the program declared it, before every constructor
    /// field was widened to its stored convention: what a field is read back
    /// at is derived from what it was declared at, and only the declaration
    /// says which operations that position carries.
    pub declared: &'a VerifyEnv,
    pub latent: &'a Latent,
    pub flow: &'a ThunkFlow,
    /// Where a clause that almost matches a recognized shape is reported. It is
    /// an observable side channel, so it is the caller's log, never a fresh one:
    /// a local log would silently swallow a warning.
    pub drift: &'a DriftLog,
    /// The locals whose type the threading has changed: a binder holding an
    /// escaping producer thunk changes type when the thunk gains its evidence
    /// and accumulator, and every read of it must change with it.
    pub retyped: Retyped,
    /// The evidence binders actually in scope, by name: a producer's own
    /// parameters, or the local binds a handle introduced. Fabricating a type
    /// a second time at a use site is how a witness drifts from its binder.
    pub evidence_types: BTreeMap<Sym, CoreType>,
    /// Every function's transformed signature, computed before any body is
    /// rewritten: the authority a call site rebuilds its result and arguments
    /// from. Reading the pre-threading witness at a call, or retagging its
    /// leaves toward what a consumer expects, is how stale results survive.
    pub signatures: BTreeMap<Sym, CoreFnSig>,
    /// The parameter positions the reified rewrite reads as cells, by
    /// function. Such a position takes no threaded evidence: the cells
    /// behind it capture the evidence in scope where they were built, and
    /// no handler for a threaded operation stands between the building and
    /// the forcing, since a handle over cells is promoted.
    pub cells: BTreeMap<Sym, BTreeSet<usize>>,
    /// The operations the reified rewrite answered with cells before
    /// threading began: a position that still spells one of their labels
    /// holds a value the rewrite typed without it.
    pub reified: BTreeSet<Sym>,
    /// The one `Step` instantiation live in the scope being threaded, decided
    /// where the early-exit protocol is entered (a handle in early mode, a
    /// take) and consumed by every guard, lift, unwrap, constructor and
    /// pattern inside that scope. One builder owns each representation fact;
    /// reconstructing `Step(acc, acc)` at a use site from whatever type is
    /// nearby is how the take witnesses drifted.
    pub step: Option<StepAt>,
    /// The abort live in the scope being threaded by value: the operation
    /// whose clause never resumes, and the done type its payload has here.
    /// Decided where a value scope is entered (a handle site with an abort
    /// arm, a producer whose operations include one) and read by every guard,
    /// lift and evidence type inside that scope.
    pub abort: Abort,
    /// Whether the value being rewritten is the one its declaration returns,
    /// whose row the signature prepass fixed: a returned lambda binds the
    /// ambient that row names inside its own type. Cleared by the first value
    /// rewrite that reads it, so nothing nested inherits it.
    pub returning: bool,
    /// The ambient row the function being threaded binds on its own scheme for
    /// the carrier it returns, when it has one. A returned lambda binds the
    /// ambient its declared row names only where nothing outside it already
    /// does; binding it twice leaves the inner one shadowing a quantifier the
    /// caller has already instantiated.
    pub scheme_row: Option<Sym>,
    /// The residual row where the threading currently runs: the producer's own
    /// ambient variable inside a producer, and the handle's residual at a
    /// handle site. Evidence types and call-site instantiations both read it,
    /// so the two cannot disagree about what row the discharged operations
    /// leave behind.
    pub row: EffRow,
    /// The term counter, which fixes generated names and tick order.
    ///
    /// Borrowed from the cascade, never owned: all state, local and free-monad
    /// attempts share one supply, and an Option-shaped attempt may mint and then
    /// decline, leaving the counter advanced for whatever runs next. An engine
    /// with a private counter would rename the fallback's tree, including where
    /// a name is minted before an arm that can still decline.
    pub fresh: &'a mut prism_common::fresh::Fresh,
    /// The first reason the threading stopped, when it did: set by the
    /// innermost site that refused a shape, read by the driver that reports
    /// the drop, and cleared before each declaration is threaded.
    pub why: Option<String>,
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
    /// Refuse the shape being threaded, keeping the first reason given: an
    /// outer site that fails because an inner one did adds nothing to it.
    pub(super) fn bail<T>(&mut self, why: impl Into<String>) -> Option<T> {
        self.why.get_or_insert_with(|| why.into());
        None
    }

    /// Pass a threading's answer through, naming the innermost computation
    /// dropped with no reason recorded so the decline can say where.
    pub(super) fn dropped(&mut self, c: &TypedComp, out: Option<TypedComp>) -> Option<TypedComp> {
        if out.is_none() && self.why.is_none() {
            self.why = Some(format!(
                "a {} dropped without a reason ({})",
                kind_name(c.kind()),
                c.sig()
            ));
        }
        out
    }

    /// Whether a threaded scope yields the accumulator and the scope's own
    /// value side by side rather than the accumulator alone. The
    /// accumulator-only conventions are the cases where the value can be
    /// recovered from the accumulator; where it cannot, the two travel
    /// together, which is the ordinary state monad.
    fn pairs(&self) -> bool {
        self.plan.answer == StateAnswerMode::Pair
    }

    /// The step this scope's own value travels inside, where it both carries
    /// that value and can leave through an abort. A take's two payloads are the
    /// one accumulator, so its pair stays outside the step and this is `None`.
    fn carried(&self) -> Option<StepAt> {
        self.step
            .clone()
            .filter(|at| self.pairs() && at.more != at.done)
    }

    /// The done payload live here: the abort of an enclosing value scope, or
    /// the one a stepped state scope already carries. A take's step is not one
    /// of these, since its done payload is the accumulator itself.
    pub(super) fn live_done(&self) -> Option<Type> {
        if self.plan.early.short_circuits() {
            return None;
        }
        self.abort
            .as_ref()
            .map(|(_, done)| done.clone())
            .or_else(|| self.step.as_ref().map(|at| at.done.clone()))
    }

    /// What a handle's threaded body can perform: the operations it performs
    /// directly and through the thunks in scope, among those this scope holds
    /// evidence for, plus the handle's own. An abort answered further out is
    /// among them, since the accumulator has to travel past it, while the
    /// program's other operations are not, so they do not decide the step.
    fn body_ops(
        &self,
        body: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
        handler: &TypedHandler,
    ) -> BTreeSet<Sym> {
        let mut sig = flow::body_sig(body, self.latent);
        flow::performed(body, loc, self.latent, self.flow, &mut sig);
        sig.into_iter()
            .map(|masked| masked.id)
            .filter(|op| evs.contains_key(op))
            .chain(handler.arms().iter().map(TypedHandleOp::name))
            .collect()
    }

    /// The step a scope threading `acc` over `ops` runs under: the take
    /// protocol's, where the program stops early, or the abort's, where the
    /// scope can leave through one. `None` where the scope runs to its end.
    fn scope_step(&self, acc: &CoreType, ops: &BTreeSet<Sym>) -> Option<StepAt> {
        let source = source_type(acc).ok()?;
        if self.plan.early.short_circuits() {
            return Some(StepAt::new(source.clone(), source));
        }
        self.plan
            .folds_an_abort(ops)
            .then(|| Some(StepAt::new(source, self.live_done()?)))
            .flatten()
    }

    /// `return #(st, v)`, what a threaded scope yields when the two travel
    /// together.
    fn yield_pair(&mut self, st: &TypedBinder, v: TypedValue) -> Option<TypedComp> {
        let Some(at) = self.carried() else {
            let Some(pair) = pair_value(binder_var(st), v) else {
                return self.bail("a threaded value with no source spelling");
            };
            return Some(TypedComp::new(
                CompSig::new(pair.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(pair),
            ));
        };
        // The accumulator is stepped, so the pair goes inside `SMore` and a step
        // already done travels on with the payload it stopped with: there is no
        // value to put beside it.
        let acc = TypedBinder::new(self.mint("a"), CoreType::Source(at.more.clone()));
        let Some(pair) = carried_value(binder_var(&acc), v) else {
            return self.bail("a threaded value with no source spelling");
        };
        let out = StepAt::new(source_type(pair.ty()).ok()?, at.done.clone());
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(at.done.clone()));
        Some(TypedComp::new(
            CompSig::new(out.ty(), EffRow::Empty),
            TypedCompKind::Case(
                binder_var(st),
                vec![
                    (
                        at.more_pattern(acc),
                        Self::returning(out.smore(pair), out.ty()),
                    ),
                    (
                        at.done_pattern(d.clone()),
                        Self::returning(out.sdone(binder_var(&d)), out.ty()),
                    ),
                ],
            ),
        ))
    }

    /// The binders a pair-yielding `head` takes apart into: the accumulator
    /// under a fresh name, and the value under `name` when the tail reads it.
    fn pair_binders(
        &mut self,
        head: &TypedComp,
        name: Option<&TypedBinder>,
    ) -> Option<(TypedBinder, Option<TypedBinder>)> {
        let carried = carried_step(head.sig().result());
        let pair = carried.as_ref().map_or_else(
            || head.sig().result().clone(),
            |at| CoreType::Source(at.more.clone()),
        );
        let Some((acc, value)) = pair_parts(&pair) else {
            return self.bail("a threaded scope that did not carry its value");
        };
        // Where the pair rode inside a step, what the tail threads on is that
        // step over the bare accumulator, not the accumulator the pair held.
        let acc = match &carried {
            Some(at) => StepAt::new(source_type(&acc).ok()?, at.done.clone()).ty(),
            None => acc,
        };
        let acc = TypedBinder::new(self.mint("st"), acc);
        let val = name.map(|b| TypedBinder::new(b.name(), value));
        Some((acc, val))
    }

    /// Bind what `head` yields, take the pair apart, and run `tail` under the
    /// two binders [`Self::pair_binders`] produced.
    fn split_pair(
        &mut self,
        head: TypedComp,
        acc: TypedBinder,
        val: Option<TypedBinder>,
        tail: TypedComp,
    ) -> Option<TypedComp> {
        let p = TypedBinder::new(self.mint("pr"), head.sig().result().clone());
        let Some(at) = carried_step(head.sig().result()) else {
            let case = TypedComp::new(
                tail.sig().clone(),
                TypedCompKind::Case(
                    binder_var(&p),
                    vec![(TypedPattern::Tuple(vec![Some(acc), val]), tail)],
                ),
            );
            return Some(Self::bind(head, p, case));
        };
        // A stepped pair is taken apart in two: the step first, whose done side
        // carries the tail's own stop rather than the head's, then the pair
        // inside it, rewrapped as the step the tail threads on.
        let pr = TypedBinder::new(self.mint("pr"), CoreType::Source(at.more.clone()));
        let (bare, _) = pair_parts(&CoreType::Source(at.more.clone()))?;
        let a = TypedBinder::new(self.mint("a"), bare);
        let seat = StepAt::of(acc.ty())?;
        let out = StepAt::of(tail.sig().result())?;
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(at.done.clone()));
        let inner = Self::bind(
            Self::returning(seat.smore(binder_var(&a)), acc.ty().clone()),
            acc,
            tail,
        );
        let taken = TypedComp::new(
            inner.sig().clone(),
            TypedCompKind::Case(
                binder_var(&pr),
                vec![(TypedPattern::Tuple(vec![Some(a), val]), inner)],
            ),
        );
        let case = TypedComp::new(
            taken.sig().clone(),
            TypedCompKind::Case(
                binder_var(&p),
                vec![
                    (at.more_pattern(pr), taken),
                    (
                        at.done_pattern(d.clone()),
                        Self::returning(out.sdone(binder_var(&d)), out.ty()),
                    ),
                ],
            ),
        );
        Some(Self::bind(head, p, case))
    }

    /// What a threaded scope over `st` yields for a scope whose own value has
    /// type `value`.
    fn threaded_result(&mut self, st: &TypedBinder, value: &CoreType) -> Option<CoreType> {
        if !self.pairs() {
            return Some(st.ty().clone());
        }
        let spelled = self.carried().map_or_else(
            || pair_type(st.ty(), value),
            |at| carried_result(&at, value),
        );
        spelled.map_or_else(
            || self.bail("a producer result with no source spelling"),
            Some,
        )
    }

    /// Keep only the accumulator of what `head` yields, for a position whose
    /// convention is the accumulator alone: a fold clause's evidence, or a
    /// handle whose return clause is the identity transformer.
    fn drop_value(&mut self, head: TypedComp) -> Option<TypedComp> {
        if !self.pairs() {
            return Some(head);
        }
        let (acc, _) = self.pair_binders(&head, None)?;
        let read = TypedComp::new(
            CompSig::new(acc.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(binder_var(&acc)),
        );
        self.split_pair(head, acc, None, read)
    }

    /// A stopping arm performed inside a threaded scope. Its clause answers
    /// the payload its fold stops with rather than a step, because nothing
    /// resumes past it and the step the payload belongs in is the one this
    /// site threads, which is the site that knows what the scope carries.
    #[allow(clippy::too_many_arguments)]
    fn stop_do(
        &mut self,
        c: &TypedComp,
        operation: &Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let Some(step) = self.step.clone() else {
            return self.bail(format!(
                "`{}` stopping a scope that does not step",
                operation.as_str()
            ));
        };
        let ev = self.evidence(evs, *operation, st.ty())?;
        let mut a: Vec<TypedValue> = args
            .iter()
            .map(|arg| self.rewrite_value(arg, loc, evs))
            .collect::<Option<_>>()?;
        a.push(binder_var(st));
        let payload = CoreType::Source(step.done);
        let stopped = Self::apply_clause_at(&ev, instantiation, a, payload.clone())?;
        let threaded = self.threaded_result(st, c.sig().result())?;
        let Some(out) = StepAt::of(&threaded) else {
            return self.bail(format!(
                "`{}` stopping a scope whose accumulator is not stepped",
                operation.as_str()
            ));
        };
        let d = TypedBinder::new(self.mint("d"), payload);
        Some(Self::bind(
            stopped,
            d.clone(),
            Self::returning(out.sdone(binder_var(&d)), out.ty()),
        ))
    }

    /// A tail producer head that also carries its value: step the accumulator,
    /// then yield it beside what the operation resumes with, since the tail is
    /// where the scope's own value is decided.
    #[allow(clippy::too_many_arguments)]
    fn pair_do(
        &mut self,
        c: &TypedComp,
        operation: &Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let ev = self.evidence(evs, *operation, st.ty())?;
        let mut a: Vec<TypedValue> = args
            .iter()
            .map(|arg| self.rewrite_value(arg, loc, evs))
            .collect::<Option<_>>()?;
        a.push(binder_var(st));
        let paired = self.plan.paired(*operation);
        let stepped = Self::apply_clause(&ev, instantiation, a, st, paired)?;
        // A paired clause has already put the two together: its answer is this
        // scope's answer, and rebuilding the pair here would only take apart
        // what the evidence just built. Where the scope also steps, the two it
        // put together are outside that step and the scope's are inside it.
        if paired {
            if self.carried().is_some() {
                return self.bail(format!(
                    "`{}` answering a pair beside a scope that can abort",
                    operation.as_str()
                ));
            }
            return Some(stepped);
        }
        let resumed = match self.plan.kinds.get(operation) {
            Some(FoldAKind::Acc) => binder_var(st),
            Some(FoldAKind::Unit) => unit_value(),
            Some(FoldAKind::Value) => unreachable!("guarded above"),
            None if c.sig().result() == &CoreType::Source(Type::Unit) => unit_value(),
            None => {
                return self.bail(format!(
                    "`{}` in tail position resuming with a value the pair cannot carry",
                    operation.as_str()
                ))
            }
        };
        let st2 = TypedBinder::new(self.mint("st"), st.ty().clone());
        let yielded = match (self.plan.kinds.get(operation), self.carried()) {
            // A read resumes with the accumulator it received, which in a
            // stepped scope sits inside the step: the read is answered from
            // that step's payload, and a step already done goes on as it is.
            (Some(FoldAKind::Acc), Some(at)) => {
                let old = TypedBinder::new(self.mint("a"), CoreType::Source(at.more.clone()));
                let inner = self.yield_pair(&st2, binder_var(&old))?;
                let out = StepAt::of(inner.sig().result())?;
                let d = TypedBinder::new(self.mint("d"), CoreType::Source(at.done.clone()));
                TypedComp::new(
                    inner.sig().clone(),
                    TypedCompKind::Case(
                        binder_var(st),
                        vec![
                            (at.more_pattern(old), inner),
                            (
                                at.done_pattern(d.clone()),
                                Self::returning(out.sdone(binder_var(&d)), out.ty()),
                            ),
                        ],
                    ),
                )
            }
            _ => self.yield_pair(&st2, resumed)?,
        };
        Some(Self::bind(stepped, st2, yielded))
    }

    /// An abort performed where an accumulator is threaded: apply its value
    /// clause, keep going with the untouched accumulator where the operation
    /// resumed, and stop the scope where it did not.
    #[allow(clippy::too_many_arguments)]
    fn abort_do(
        &mut self,
        operation: &Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        value: &CoreType,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let Some(step) = self.step.clone() else {
            return self.bail("an abort performed where the scope cannot stop");
        };
        let ev = self.evidence(evs, *operation, st.ty())?;
        let mut a: Vec<TypedValue> = args
            .iter()
            .map(|arg| self.rewrite_value(arg, loc, evs))
            .collect::<Option<_>>()?;
        if a.is_empty() {
            a.push(unit_value());
        }
        let app = self.apply_value_clause(&ev, *operation, instantiation, a)?;
        let Some(raised) = StepAt::of(app.sig().result()) else {
            return self.bail("an abort whose clause does not answer a step");
        };
        let carried = self.carried().is_some();
        let resumed = TypedBinder::new(
            self.mint(if carried { "w" } else { "_w" }),
            CoreType::Source(raised.more.clone()),
        );
        // The resuming arm is this tail, so a scope carrying its value carries
        // what the operation resumed with. The scope that stops carries nothing
        // beside its payload, which is why the pair rides inside the step.
        let kept = if carried {
            if CoreType::Source(raised.more.clone()) != *value {
                return self.bail(format!(
                    "abort `{}` resuming with a value this scope does not carry",
                    operation.as_str()
                ));
            }
            self.yield_pair(st, binder_var(&resumed))?
        } else {
            Self::returning(binder_var(st), st.ty().clone())
        };
        let Some(out) = StepAt::of(kept.sig().result()) else {
            return self.bail("an abort in a scope whose accumulator is not stepped");
        };
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done));
        let left = Self::returning(out.sdone(binder_var(&d)), out.ty());
        let sv = TypedBinder::new(self.mint("sv"), app.sig().result().clone());
        let case = TypedComp::new(
            CompSig::new(
                kept.sig().result().clone(),
                union_effects(kept.sig().effects(), left.sig().effects()),
            ),
            TypedCompKind::Case(
                binder_var(&sv),
                vec![
                    (raised.more_pattern(resumed), kept),
                    (raised.done_pattern(d), left),
                ],
            ),
        );
        Some(Self::bind(app, sv, case))
    }

    /// Thread the accumulator through a bind whose head performs one of the
    /// fused operations, rebinding the head's value only where the tail reads
    /// it and guarding the tail where the scope can stop.
    fn thread_producing_bind(
        &mut self,
        m: &TypedComp,
        x: &TypedBinder,
        n: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let st2 = TypedBinder::new(self.mint("st"), st.ty().clone());
        let tm = self.thread_st(m, evs, loc, st)?;
        let mut loc2 = loc.clone();
        loc2.insert(
            x.name(),
            flow::result_sig_in(m, loc, self.latent, self.flow),
        );
        let tn = self.thread_st(n, evs, &loc2, &st2)?;
        let tn = if free_comp_vars(n).contains(&x.name()) {
            // A read exposes the prior accumulator and a write exposes unit. A
            // producing head outside those operation shapes has no value the
            // threaded accumulator can recreate. Producer-answer plans decline;
            // accumulator-answer plans admit only Unit, whose single inhabitant
            // can be rebuilt, and assert that exclusion before doing so.
            let Some(bound) =
                bound_producer_result(self.plan.answer, self.op_tail_kind(m, loc, evs), st, x.ty())
            else {
                return self.bail("a producing head whose value the accumulator cannot recreate");
            };
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
        // In a stepped scope the producer stops once the accumulator yields
        // `SDone`, guarding with the scope's one Step decision.
        let tn = match self.step.clone() {
            Some(step) => self.step_guard(&step, &st2, tn),
            None => tn,
        };
        Some(Self::bind(tm, st2, tn))
    }

    /// Thread the accumulator through a call to a function planned as a
    /// producer of the fused operations: pass the evidence its operations need
    /// and the accumulator itself, and instantiate the quantifiers the plan
    /// gave its signature at what this scope concretely threads.
    #[allow(clippy::too_many_arguments)]
    fn thread_producer_call(
        &mut self,
        c: &TypedComp,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        // One evidence argument per fused operation latent in the callee,
        // whatever channel each one takes, because that is the list its
        // signature declares. A scope threading an accumulator can reach a
        // producer that also carries a value-channel operation, and narrowing
        // to the operations this scope threads would drop that argument.
        let callee_ops: BTreeSet<Sym> = self
            .latent
            .get(&callee)
            .map(|s| {
                s.iter()
                    .map(|m| m.id)
                    .filter(|id| self.plan.ops.contains(id))
                    .collect()
            })
            .unwrap_or_default();
        let mut a: Vec<TypedValue> = args
            .iter()
            .map(|arg| self.rewrite_value(arg, loc, evs))
            .collect::<Option<_>>()?;
        a.extend(self.evidence_args(evs, &callee_ops, st.ty())?);
        // A producer of value-channel operations alone takes no accumulator
        // and answers with its own value, stepped over the abort's payload
        // when one of them aborts: the accumulator runs straight through it,
        // and a step already done is this scope's own.
        if self.plan.channel(&callee_ops) == Some(Channel::Value) {
            return self.thread_value_producer_call(callee, instantiation, a, st);
        }
        a.push(binder_var(st));
        // The callee's signature gained quantifiers when it was planned as a
        // producer, and every reference must instantiate them: the state type
        // at what the accumulator concretely is here, and the ambient row at
        // the residual this call runs under.
        let mut inst = instantiation.to_vec();
        let numbered = {
            let mut v: Vec<i64> = callee_ops
                .iter()
                .map(|op| self.ids.id(*op))
                .collect::<Option<_>>()?;
            v.sort_unstable();
            v
        };
        let sig = self.signatures.get(&callee).cloned();
        // An effect parameter the callee names no argument for is fixed here,
        // by the label the row argument this call hands over spells.
        for q in sig
            .iter()
            .flat_map(|sig| sig.quantifiers().iter().skip(instantiation.len()))
        {
            if let CoreQuantifier::Type(name) = q {
                if names::is_effect_param(name.as_str()) {
                    inst.push(CoreInstantiation::Type(
                        self.effect_param(*name, instantiation),
                    ));
                }
            }
        }
        let threading = accumulator_type(self.plan, &callee_ops, &numbered)?;
        if threading.state.is_some() {
            // The state quantifier is the BASE accumulator: a stepped scope's
            // callee wraps its own Step around the declared accumulator, so
            // instantiating at the stepped type would wrap twice.
            let base = match &self.step {
                Some(step) => step.more.clone(),
                None => source_type(st.ty()).ok()?,
            };
            inst.push(CoreInstantiation::Type(base));
        }
        if threading.done.is_some() {
            let Some(step) = &self.step else {
                return self.bail("an aborting producer called outside a stepped scope");
            };
            inst.push(CoreInstantiation::Type(step.done.clone()));
        }
        // A callee that named its declared tail as its ambient carries that
        // quantifier in declared position and gained no row: the slot the
        // caller wrote is instantiated at this scope's row joined with the
        // caller's residual argument. Any other callee gained the row last.
        let named = sig
            .as_ref()
            .and_then(|sig| {
                let EffRow::Var(tail) = sig.body().effects().tail() else {
                    return None;
                };
                sig.quantifiers()
                    .iter()
                    .position(|q| matches!(q, CoreQuantifier::Row(name) if name == tail))
            })
            .filter(|slot| *slot < instantiation.len());
        match (named, &sig) {
            (Some(slot), Some(sig)) => {
                let residual = self.residual_instantiation(&inst[slot..=slot]);
                inst[slot] =
                    CoreInstantiation::Row(self.widened(sig.body().effects(), &residual[0]));
            }
            _ => inst.push(CoreInstantiation::Row(sig.as_ref().map_or_else(
                || self.row.clone(),
                |sig| self.gained_row(sig.body().effects()),
            ))),
        }
        let applied = sig.as_ref().and_then(|sig| instantiate_fn(sig, &inst).ok());
        if let Some(applied) = applied {
            for (arg, want) in a.iter().zip(applied.params()).take(args.len()) {
                self.accepts(arg, want)?;
            }
        }
        let result = self.threaded_result(st, c.sig().result())?;
        Some(TypedComp::new(
            CompSig::new(result, self.row.clone()),
            TypedCompKind::Call {
                callee,
                instantiation: inst,
                args: a,
            },
        ))
    }

    /// A call to a producer of value-channel operations from a scope threading
    /// an accumulator: the call takes the value scope's arguments, and its
    /// answer, stepped where the callee can abort, is read into this scope.
    fn thread_value_producer_call(
        &mut self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: Vec<TypedValue>,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let sig = self.signatures.get(&callee)?.clone();
        let inst = self.producer_instantiation(&sig, instantiation)?;
        let answer = instantiate_fn(&sig, &inst).ok()?.body().result().clone();
        let call = TypedComp::new(
            CompSig::new(answer.clone(), self.row.clone()),
            TypedCompKind::Call {
                callee,
                instantiation: inst,
                args,
            },
        );
        let r = TypedBinder::new(self.mint("r"), answer.clone());
        let Some(raised) = StepAt::of(&answer) else {
            let kept = self.value_through(st, binder_var(&r))?;
            return Some(Self::bind(call, r, kept));
        };
        let Some(step) = self.step.clone() else {
            return self.bail("an aborting producer called outside a stepped scope");
        };
        let v = TypedBinder::new(self.mint("v"), CoreType::Source(raised.more.clone()));
        let kept = self.value_through(st, binder_var(&v))?;
        let Some(out) = StepAt::of(kept.sig().result()) else {
            return self.bail("an aborting producer called where the accumulator is not stepped");
        };
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done));
        let left = Self::returning(out.sdone(binder_var(&d)), out.ty());
        let case = TypedComp::new(
            CompSig::new(
                kept.sig().result().clone(),
                union_effects(kept.sig().effects(), left.sig().effects()),
            ),
            TypedCompKind::Case(
                binder_var(&r),
                vec![
                    (raised.more_pattern(v), kept),
                    (raised.done_pattern(d), left),
                ],
            ),
        );
        Some(Self::bind(call, r, case))
    }

    /// What a scope yields once a value-channel operation answered `v` and
    /// left the accumulator where it was.
    fn value_through(&mut self, st: &TypedBinder, v: TypedValue) -> Option<TypedComp> {
        if self.pairs() {
            self.yield_pair(st, v)
        } else {
            Some(Self::returning(binder_var(st), st.ty().clone()))
        }
    }

    /// Thread `c`, whose accumulator is currently named `st`. `evs` maps each
    /// fused operation to the evidence active for it here.
    pub(super) fn thread_st(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        // A bind spine is threaded a node at a time, so the recursion is as deep
        // as the program's longest sequence; grow stack segments inside it, the
        // same discipline the shared descent keeps.
        let out = on_core_stack(|| self.thread_st_on_core_stack(c, evs, loc, st));
        self.dropped(c, out)
    }

    fn thread_st_on_core_stack(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        // A value-channel operation that resumes takes no accumulator and
        // answers with its own value, so a scope threading state runs straight
        // through it. Only an abort among them decides anything here, since the
        // scope it leaves through is the one holding the accumulator.
        let ops: BTreeSet<Sym> = evs
            .keys()
            .copied()
            .filter(|op| !self.plan.value_shaped(*op) || self.plan.aborts.contains(op))
            .collect();
        // The value-channel operations this scope holds evidence for and does
        // not thread. A head or tail performing only those is the value
        // route's, where it stands: it takes the evidence its callees and
        // carriers declare and answers with its own value, and the
        // accumulator passes through it untouched.
        let valued: BTreeSet<Sym> = evs.keys().copied().filter(|op| !ops.contains(op)).collect();
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
            // A bind whose head performs an operation, where the head already
            // carries its own value beside the accumulator: the binder reads
            // that value straight off the pair, so no shape of head has to be
            // one the threading can rebuild a value for.
            TypedCompKind::Bind(m, x, n)
                if self.pairs() && produces(m, loc, &ops, self.latent, self.flow) =>
            {
                let tm = self.thread_st(m, evs, loc, st)?;
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    flow::result_sig_in(m, loc, self.latent, self.flow),
                );
                let reads = free_comp_vars(n).contains(&x.name());
                let (st2, val) = self.pair_binders(&tm, reads.then_some(x))?;
                if let Some(val) = &val {
                    if val.ty() != x.ty() {
                        self.retyped.insert(x.name(), val.ty().clone());
                    }
                }
                let tn = self.thread_st(n, evs, &loc2, &st2)?;
                self.split_pair(tm, st2, val, tn)?
            }
            // A bind whose head performs an operation: thread the accumulator
            // through it and rebind. The head's result is bound only if the tail
            // still needs it: a read observes the pre-operation accumulator, a
            // write yields unit.
            TypedCompKind::Bind(m, x, n) if produces(m, loc, &ops, self.latent, self.flow) => {
                self.thread_producing_bind(m, x, n, evs, loc, st)?
            }
            // An abort performed inside a threaded scope takes no accumulator:
            // it never resumes, so its clause answers a step whose done payload
            // is this scope's. The resuming arm is reachable only where another
            // handler answers the operation without leaving, and the
            // accumulator it left is still the one in hand.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } if evs.contains_key(operation)
                && ops.contains(operation)
                && self.plan.value_shaped(*operation) =>
            {
                self.abort_do(
                    operation,
                    instantiation,
                    args,
                    c.sig().result(),
                    evs,
                    loc,
                    st,
                )?
            }
            // A stopping arm: an abort its own fold answers. It takes the
            // accumulator like any other arm of that fold and never gives one
            // back, so its clause hands back the payload the fold stops with
            // and this site puts that payload into its own step.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } if evs.contains_key(operation) && self.plan.stops(*operation) => {
                self.stop_do(c, operation, instantiation, args, evs, loc, st)?
            }
            // A resuming value-channel operation in tail position answers with
            // its own value and leaves the accumulator where it was, so the
            // scope yields that accumulator, beside the value where the two
            // travel together.
            TypedCompKind::Do { operation, .. }
                if evs.contains_key(operation) && !ops.contains(operation) =>
            {
                let m = self.rewrite(c, loc, evs)?;
                let v = TypedBinder::new(self.mint("v"), m.sig().result().clone());
                let rest = if self.pairs() {
                    self.yield_pair(st, binder_var(&v))?
                } else {
                    Self::returning(binder_var(st), st.ty().clone())
                };
                Self::bind(m, v, rest)
            }
            // A tail producer head that also carries its value: step the
            // accumulator, then yield it beside what the operation resumes
            // with, since the tail is where the scope's own value is decided.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } if self.pairs() && evs.contains_key(operation) => {
                self.pair_do(c, operation, instantiation, args, evs, loc, st)?
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
                a.push(binder_var(st));
                Self::apply_clause(&ev, instantiation, a, st, self.plan.paired(*operation))?
            }
            TypedCompKind::Return(v) if self.pairs() => {
                let v2 = self.rewrite_value(v, loc, evs)?;
                self.yield_pair(st, v2)?
            }
            TypedCompKind::Return(_) => TypedComp::new(
                CompSig::new(st.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(binder_var(st)),
            ),
            TypedCompKind::If(v, t, e) => {
                // A branch's row is read off the threaded branches, as the
                // verifier reads it: one side may carry the fused evidence
                // where the other returns outright.
                let t2 = self.thread_st(t, evs, loc, st)?;
                let e2 = self.thread_st(e, evs, loc, st)?;
                let Ok(row) = union_rows(t2.sig().effects(), e2.sig().effects()) else {
                    return self.bail("branches threaded at rows with distinct open tails");
                };
                let sig = CompSig::new(t2.sig().result().clone(), row);
                TypedComp::new(
                    sig,
                    TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
                )
            }
            // A pure head: the accumulator passes through it untouched. The
            // binder follows the head it binds, exactly as in [`Self::rewrite`]:
            // a head whose value the rewrite retyped retypes its binder and
            // every read after it.
            TypedCompKind::Bind(m, x, n) => {
                let m2 = if produces(m, loc, &valued, self.latent, self.flow) {
                    self.thread_val(m, evs, loc, false)?
                } else {
                    self.rewrite_head(m, x, n, loc, evs)?
                };
                let x2 = if m2.sig().result() == x.ty() {
                    x.clone()
                } else {
                    self.retyped.insert(x.name(), m2.sig().result().clone());
                    TypedBinder::new(x.name(), m2.sig().result().clone())
                };
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    flow::result_sig_in(m, loc, self.latent, self.flow),
                );
                let n2 = self.thread_st(n, evs, &loc2, st)?;
                self.bound(m2, x2, n2)?
            }
            // A tail call to a producer: append this call site's evidence, in the
            // same ascending operation-id order the producer declares it in, and
            // the accumulator.
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } if produces(c, loc, &ops, self.latent, self.flow) => {
                self.thread_producer_call(c, *callee, instantiation, args, evs, loc, st)?
            }
            TypedCompKind::Case(v, arms) => {
                let arms: Vec<_> = arms
                    .iter()
                    .map(|(p, b)| self.arm(p, |this| this.thread_st(b, evs, loc, st)))
                    .collect::<Option<_>>()?;
                // The case's row is the residual it runs under, not whatever a
                // single arm's tail locally reports: an arm ending in a bare
                // return says Empty, and the verifier rightly expects the
                // enclosing residual.
                let result = arms.first().map(|(_, b)| b.sig().result().clone())?;
                TypedComp::new(
                    CompSig::new(result, self.row.clone()),
                    TypedCompKind::Case(self.scrutinee(v), arms),
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
                    return self.bail("a producing application whose callee is not a force");
                };
                let v2 = self.retyped.rebuild_through(v);
                let CoreType::Thunk(thunk) = v2.ty().clone() else {
                    return self.bail("a forced producer that is not a thunk");
                };
                let CoreType::Function(fun) = thunk.result() else {
                    return self.bail("a forced producer thunk that is not a function");
                };
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, evs))
                    .collect::<Option<_>>()?;
                // One evidence argument per fused operation the carrier
                // performs, whatever channel each one takes, because that is
                // the list its widened type declares: a stored carrier of a
                // value-channel operation beside the accumulator's takes
                // both, and narrowing to the operations this scope threads
                // would drop the first.
                let carried: BTreeSet<Sym> = flow::value_sig_in(v, loc, self.latent, self.flow)
                    .into_iter()
                    .map(|masked| masked.id)
                    .filter(|operation| self.plan.ops.contains(operation))
                    .collect();
                a.extend(self.evidence_args(evs, &carried, st.ty())?);
                a.push(binder_var(st));
                let mut inst = instantiation.clone();
                for q in fun.quantifiers().iter().skip(instantiation.len()) {
                    match q {
                        CoreQuantifier::Type(name) if names::is_effect_param(name.as_str()) => {
                            inst.push(CoreInstantiation::Type(
                                self.effect_param(*name, instantiation),
                            ));
                        }
                        // A carrier that aborts binds a done payload beside its
                        // accumulator, and only the name says which is which.
                        CoreQuantifier::Type(name) if names::is_done_type(name.as_str()) => {
                            let Some(step) = &self.step else {
                                return self
                                    .bail("an aborting carrier forced outside a stepped scope");
                            };
                            inst.push(CoreInstantiation::Type(step.done.clone()));
                        }
                        CoreQuantifier::Type(_) => {
                            let base = match &self.step {
                                Some(step) => step.more.clone(),
                                None => source_type(st.ty()).ok()?,
                            };
                            inst.push(CoreInstantiation::Type(base));
                        }
                        CoreQuantifier::Row(_) => {
                            inst.push(CoreInstantiation::Row(
                                self.gained_row(fun.body().effects()),
                            ));
                        }
                    }
                }
                if let Ok(applied) = instantiate_fn(fun, &inst) {
                    for (arg, want) in a.iter().zip(applied.params()).take(args.len()) {
                        self.accepts(arg, want)?;
                    }
                }
                let force = TypedComp::new(thunk.as_ref().clone(), TypedCompKind::Force(v2));
                let result = self.threaded_result(st, c.sig().result())?;
                TypedComp::new(
                    // The forced producer discharges its operations, so the App
                    // leaves the ambient residual, not the callee's stale source
                    // row.
                    CompSig::new(result, self.row.clone()),
                    TypedCompKind::App {
                        callee: Box::new(force),
                        instantiation: inst,
                        args: a,
                    },
                )
            }
            // A handle inside a producer either re-emits its operation, and so
            // threads rather than consumes it, or discharges it in tail
            // position, which the enclosing scope runs straight through.
            TypedCompKind::Handle { .. } => {
                if self.consumes(c) {
                    self.thread_consumer(c, evs, loc, st)?
                } else {
                    self.thread_forward(c, evs, loc, st)?
                }
            }
            // A tail performing only value-channel operations runs the value
            // route where it stands and yields its answer beside the
            // accumulator it never touched.
            _ if produces(c, loc, &valued, self.latent, self.flow) => {
                let m = self.thread_val(c, evs, loc, false)?;
                let v = TypedBinder::new(self.mint("v"), m.sig().result().clone());
                let rest = self.value_through(st, binder_var(&v))?;
                Self::bind(m, v, rest)
            }
            // A tail that performs none of the fused operations still decides
            // the scope's value, so a paired scope runs it and yields what it
            // answered beside the accumulator it never touched.
            _ if self.pairs() => {
                let m = self.rewrite(c, loc, evs)?;
                let v = TypedBinder::new(self.mint("v"), m.sig().result().clone());
                let yielded = self.yield_pair(st, binder_var(&v))?;
                Self::bind(m, v, yielded)
            }
            // Take handles using the `Step` protocol and escaping producer thunks
            // carried by a pure head are not fused here.
            _ => return self.bail(format!("a {} in a state scope", kind_name(c.kind()))),
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
            return self.bail("a forwarder with several arms");
        };
        // The forwarded body's final value passes straight through, so the return
        // clause must hand it on: anything else would have to observe a value the
        // threaded loop has already turned into an accumulator.
        let erased_return = return_body.as_deref().map(|b| b.clone().erase());
        if !evs.contains_key(&clause.name()) {
            return self.bail(format!(
                "a forwarder of `{}` without evidence in scope",
                clause.name().as_str()
            ));
        }
        if !passes_return(
            return_binder.as_ref().map(TypedBinder::name),
            erased_return.as_ref(),
            self.plan.widen && unit_source(return_binder.as_ref()),
        ) {
            return self.bail(format!(
                "a forwarder of `{}` whose return clause does not pass its value on",
                clause.name().as_str()
            ));
        }
        let mut aliases = BTreeSet::new();
        aliases.insert(clause.resume().name());
        // A forwarder resumes in tail position. A clause that does not is a
        // handler of another shape sitting where the threading expected one,
        // and it has no shadow clause to establish.
        let Some(stripped) = strip_resume(clause.body(), &aliases, self.drift) else {
            return self.bail(format!(
                "a handler of `{}` inside a producer whose clause is not a tail resumption",
                clause.name().as_str()
            ));
        };

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
            let substituted = substitute_witnesses(&stripped, &from, &to);
            let effect = self.env.operation(clause.name())?.effect().name;
            let mut bridges: BTreeMap<Sym, TypedValue> = BTreeMap::new();
            for (name, reference) in &lexical {
                // The bridge target is the edge type with the discharged
                // operation removed from its rows: the shadow re-emits into the
                // outer evidence, so the source clause no longer carries the
                // label the outer scope has already accounted for.
                let edge_ty = SubtractEffect { label: effect }.ty(&substitute_core_type(
                    reference.ty(),
                    &from,
                    &to,
                ));
                if edge_ty != *reference.ty() {
                    bridges.insert(*name, try_word_bridge(reference.clone(), edge_ty)?);
                }
            }
            if bridges.is_empty() {
                substituted
            } else {
                let mut counter = 0u32;
                substitute_terms(&substituted, &bridges, &mut counter, "fwb")
            }
        };
        let shadow_params: Vec<TypedBinder> = clause
            .params()
            .iter()
            .map(|binder| {
                TypedBinder::new(binder.name(), substitute_core_type(binder.ty(), &from, &to))
            })
            .collect();

        // The source's evidence: the clause's own body, threading the accumulator
        // into whatever the outer evidence is here.
        let acc = TypedBinder::new(self.mint("acc"), st.ty().clone());
        let ev_body = self.thread_st(&stripped, evs, loc, &acc)?;
        // A clause is a state transformer under every convention, so a paired
        // scope keeps only the accumulator at this boundary.
        let ev_body = self.drop_value(ev_body)?;
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

    /// Whether a handle discharges its operations in tail position without
    /// re-emitting them: a consumer, which threads nothing of its own.
    fn consumes(&self, c: &TypedComp) -> bool {
        self.plan.widen
            && matches!(
                judge_handle(c, self.latent, self.plan.widen, self.plan.reify),
                Ok(HandleJudgment {
                    class: HandleClass::Direct { abort: None },
                    ..
                })
            )
    }

    /// Thread a direct consumer inside a live scope. Such a clause is a fold
    /// clause that leaves the accumulator alone: it becomes evidence taking
    /// the accumulator like any other arm and handing it back beside whatever
    /// the clause resumes with, and the handled body goes on threading the
    /// very same accumulator, so the scope reads straight through the handle.
    fn thread_consumer(
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
        // The handled body decides this scope's value as much as any other
        // tail does, so the return clause must hand that value on rather than
        // observe one the threaded loop has already turned into state.
        let erased_return = return_body.as_deref().map(|b| b.clone().erase());
        if !passes_return(
            return_binder.as_ref().map(TypedBinder::name),
            erased_return.as_ref(),
            self.plan.widen && unit_source(return_binder.as_ref()),
        ) {
            return self.bail("a consumer whose return clause does not pass its value on");
        }
        let under = self.handle_evidence(evs, ops)?;
        // A clause is a value of the enclosing scope, so it answers with the
        // evidence that scope holds and not with its siblings'.
        let mut bound: Vec<(TypedBinder, TypedValue)> = Vec::new();
        for clause in ops.arms() {
            // An operation the value channel carries takes no accumulator here
            // either: its clause is the one every other value-channel site
            // calls.
            let lam = if self.plan.value_shaped(clause.name()) {
                self.direct_clause(clause, evs, loc, None)?
            } else {
                self.consumer_clause(clause, evs, loc, st)?
            };
            let ty = CoreType::Thunk(Box::new(lam.sig().clone()));
            let ev = TypedBinder::new(*under.get(&clause.name())?, ty.clone());
            self.evidence_types.insert(ev.name(), ty.clone());
            let thunk = TypedValue::new(ty, TypedValueKind::Thunk(Box::new(lam)));
            bound.push((ev, thunk));
        }
        let threaded = self.thread_st(body, &under, loc, st)?;
        Some(bound.into_iter().rev().fold(threaded, |rest, (ev, thunk)| {
            Self::bind(Self::returning(thunk, ev.ty().clone()), ev, rest)
        }))
    }

    /// One clause of a direct consumer, as the evidence its perform sites
    /// call: the operation's own parameters and the accumulator, then the
    /// clause's body threaded through that accumulator, which leaves what it
    /// resumes with exactly where the convention keeps the scope's value.
    fn consumer_clause(
        &mut self,
        clause: &TypedHandleOp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let aliases = BTreeSet::from([clause.resume().name()]);
        let stripped = strip_resume(clause.body(), &aliases, self.drift)?;
        // The performer binds the operation's declared result, so a clause of
        // a unit-valued operation answers with unit whatever its body left
        // behind.
        let unit = CoreType::Source(Type::Unit);
        let declared = value_scheme(self.env.operation(clause.name())?, clause.instantiation())?.2;
        let stripped = if declared == unit && stripped.sig().result() != &unit {
            let v = TypedBinder::new(self.mint("v"), stripped.sig().result().clone());
            Self::bind(stripped, v, Self::returning(unit_value(), unit))
        } else {
            stripped
        };
        let acc = TypedBinder::new(self.mint("acc"), st.ty().clone());
        let body = self.thread_st(&stripped, evs, loc, &acc)?;
        // A clause takes the accumulator appended to the operation's own
        // parameters, and a nullary operation's clause is not padded: the
        // accumulator is the argument its perform sites pass.
        let mut params = clause.params().to_vec();
        params.push(acc);
        let generic = if self.plan.entry.contains(&clause.name()) {
            generic_quantifiers(
                self.env.operation(clause.name())?,
                clause.instantiation(),
                &[],
            )
        } else {
            Vec::new()
        };
        Some(Self::lam_quantified(generic, params, body))
    }

    /// Lower a control consumer (a `for`/print loop): tail-resumptive but not
    /// re-emitting, so each clause is a pure side effect over a unit state the
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
        if ops.arms().is_empty() {
            return self.bail("a consuming handler with no arms");
        }
        // The state a consumer threads is unit: it exists only so the clauses
        // sit on the same edge the producer's do. An operation read elsewhere
        // in the program pins that state to its own result, and this handler
        // has no seed to offer at that type.
        let threaded: BTreeSet<Sym> = ops
            .arms()
            .iter()
            .map(TypedHandleOp::name)
            .filter(|op| !self.plan.value_shaped(*op))
            .collect();
        if let Some(Accumulator::Pinned(ty)) = self.plan.accumulator_for(&threaded) {
            if ty != CoreType::Source(Type::Unit) {
                return self
                    .bail("a consuming handler of an operation another scope reads for its state");
            }
        }
        let unit = CoreType::Source(Type::Unit);
        let row = self.handle_row(c)?;
        let saved_row = mem::replace(&mut self.row, row);
        let saved_evidence = self.evidence_types.clone();
        let under = self.handle_evidence(evs, ops)?;
        let saved_step = self.step.clone();
        // The step the unit state runs under: the take protocol's, or the
        // abort's live around this handle, whose payload every clause forwards
        // and this handle re-raises where the abort escapes it.
        let body_ops = self.body_ops(body, loc, evs, ops);
        let step_at = self.scope_step(&unit, &body_ops);
        let escapes = !self.plan.early.short_circuits() && self.passes_abort(c, loc);
        if escapes && step_at.is_none() {
            return self.bail("a consumer passing an abort outside a stepped scope");
        }
        if escapes && self.pairs() {
            return self.bail("a consumer passing an abort beside a paired scope");
        }

        // Evidence: one lambda per arm, each running its clause's side effects
        // and then returning the state. The arms of a consumer read and write
        // nothing between them, because the state they share is unit, so they
        // bind independently in clause order.
        let mut bound: Vec<(TypedBinder, TypedValue)> = Vec::new();
        for clause in ops.arms() {
            // An operation the value channel carries takes no accumulator: its
            // clause is the one every other value-channel site calls, and the
            // state this handler threads runs past it untouched.
            let ev_lam = if self.plan.value_shaped(clause.name()) {
                self.direct_clause(clause, evs, loc, None)?
            } else {
                let aliases = BTreeSet::from([clause.resume().name()]);
                let stripped = strip_resume(clause.body(), &aliases, self.drift)?;
                let st = TypedBinder::new(self.mint("st"), unit.clone());
                let mut ev_params = clause.params().to_vec();
                // A clause that leaves through the abort live here runs as a
                // value scope: its own answer is a step, and the state passes
                // on inside `SMore` only where that answer did not leave.
                let leaves = escapes && self.clause_leaves(clause, loc);
                let ev_body = if let Some(at) = step_at.as_ref().filter(|_| leaves) {
                    let threaded = self.thread_val(&stripped, evs, loc, true)?;
                    let Some(got) = StepAt::of(threaded.sig().result()) else {
                        return self.bail("a leaving clause whose answer is not a step");
                    };
                    let sv = TypedBinder::new(self.mint("sv"), got.ty());
                    let w = TypedBinder::new(self.mint("w"), CoreType::Source(got.more.clone()));
                    let d = TypedBinder::new(self.mint("d"), CoreType::Source(got.done.clone()));
                    let passed = TypedComp::new(
                        CompSig::new(at.ty(), EffRow::Empty),
                        TypedCompKind::Case(
                            binder_var(&sv),
                            vec![
                                (
                                    got.more_pattern(w),
                                    Self::returning(at.smore(binder_var(&st)), at.ty()),
                                ),
                                (
                                    got.done_pattern(d.clone()),
                                    Self::returning(at.sdone(binder_var(&d)), at.ty()),
                                ),
                            ],
                        ),
                    );
                    let ev_inner = Self::bind(threaded, sv, passed);
                    let step = TypedBinder::new(self.mint("step"), at.ty());
                    let sd = TypedBinder::new(self.mint("sd"), CoreType::Source(at.done.clone()));
                    let body = TypedComp::new(
                        ev_inner.sig().clone(),
                        TypedCompKind::Case(
                            binder_var(&step),
                            vec![
                                (at.more_pattern(st), ev_inner),
                                (
                                    at.done_pattern(sd.clone()),
                                    Self::returning(at.sdone(binder_var(&sd)), at.ty()),
                                ),
                            ],
                        ),
                    );
                    ev_params.push(step);
                    body
                } else if let Some(at) = &step_at {
                    let ev_inner = self.consumer_effects(&stripped, &st, loc, evs)?;
                    let step = TypedBinder::new(self.mint("step"), at.ty());
                    let body = self.step_fold(at, &step, st, ev_inner);
                    ev_params.push(step);
                    body
                } else {
                    let ev_inner = self.consumer_effects(&stripped, &st, loc, evs)?;
                    ev_params.push(st);
                    ev_inner
                };
                Self::lam(ev_params, ev_body)
            };
            let ev = TypedBinder::new(
                *under.get(&clause.name())?,
                CoreType::Thunk(Box::new(ev_lam.sig().clone())),
            );
            self.evidence_types.insert(ev.name(), ev.ty().clone());
            let thunk = TypedValue::new(ev.ty().clone(), TypedValueKind::Thunk(Box::new(ev_lam)));
            bound.push((ev, thunk));
        }
        if let Some(at) = &step_at {
            self.step = Some(at.clone());
        }

        // Seed unit, thread the producer, bind its result, run the return clause.
        let st0 = TypedBinder::new(
            self.mint("st"),
            step_at.as_ref().map_or_else(|| unit.clone(), StepAt::ty),
        );
        let threaded = self.thread_st(body, &under, loc, &st0)?;
        let fin = TypedBinder::new(self.mint("fin"), unit.clone());
        let rv = if let Some(b) = return_binder {
            b.clone()
        } else {
            let ty = if self.pairs() {
                pair_parts(threaded.sig().result())?.1
            } else {
                unit
            };
            TypedBinder::new(self.mint("r"), ty)
        };
        let rb = match return_body {
            Some(b) => self.rewrite(b, loc, evs)?,
            None => TypedComp::new(
                CompSig::new(rv.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(binder_var(&rv)),
            ),
        };
        let seed = step_at
            .as_ref()
            .map_or_else(unit_value, |at| at.smore(unit_value()));
        let bind = |head: TypedComp, x: TypedBinder, tail: TypedComp| Self::bind(head, x, tail);
        let read_fin = TypedComp::new(
            CompSig::new(fin.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(binder_var(&fin)),
        );
        // A consumer threads a unit state, so under the paired convention the
        // value the return clause runs on is the pair's second component
        // rather than that unit.
        let after = match &step_at {
            Some(at) if escapes => self.consumer_reraise(at, threaded, rv, rb)?,
            _ if self.pairs() => {
                let body_done = self.consumer_unwrap(step_at.as_ref(), threaded);
                let (acc, value) = self.pair_binders(&body_done, Some(&rv))?;
                self.split_pair(body_done, acc, value, rb)?
            }
            _ => {
                let body_done = self.consumer_unwrap(step_at.as_ref(), threaded);
                bind(body_done, fin, bind(read_fin, rv, rb))
            }
        };
        self.evidence_types = saved_evidence;
        self.row = saved_row;
        // A take's step is the plan's and stays live for the tail that
        // consumes it; an abort's step is this handle's own.
        if !self.plan.early.short_circuits() {
            self.step = saved_step;
        }
        let inner = bind(
            TypedComp::new(
                CompSig::new(seed.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(seed),
            ),
            st0,
            after,
        );
        Some(bound.into_iter().rev().fold(inner, |tail, (ev, thunk)| {
            bind(
                TypedComp::new(
                    CompSig::new(thunk.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(thunk),
                ),
                ev,
                tail,
            )
        }))
    }

    /// A consumer clause's side effects, then the unit state it was handed.
    fn consumer_effects(
        &mut self,
        stripped: &TypedComp,
        st: &TypedBinder,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedComp> {
        let rewritten = self.rewrite(stripped, loc, evs)?;
        let d = TypedBinder::new(self.mint("d"), rewritten.sig().result().clone());
        Some(TypedComp::new(
            CompSig::new(st.ty().clone(), rewritten.sig().effects().clone()),
            TypedCompKind::Bind(
                Box::new(rewritten),
                d,
                Box::new(TypedComp::new(
                    CompSig::new(st.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(binder_var(st)),
                )),
            ),
        ))
    }

    /// Unwrap a consumer's final unit state: bare where the scope runs to its
    /// end, out of `SMore` where it steps. A take's `SDone` is its own answer;
    /// an abort's cannot arrive at a handle that stops every operation raising
    /// it, and that arm is an error.
    fn consumer_unwrap(&mut self, step: Option<&StepAt>, threaded: TypedComp) -> TypedComp {
        let Some(step) = step else {
            return threaded;
        };
        if step.more == step.done {
            return self.seed_unwrap(step, threaded);
        }
        let fin = TypedBinder::new(self.mint("fin"), step.ty());
        let a = TypedBinder::new(self.mint("a"), CoreType::Source(step.more.clone()));
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done.clone()));
        let unreached = TypedComp::new(
            CompSig::new(a.ty().clone(), EffRow::Empty),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str("ICE: an abort reached the handler that stops it".into()),
            )),
        );
        let unwrap = TypedComp::new(
            CompSig::new(a.ty().clone(), EffRow::Empty),
            TypedCompKind::Case(
                binder_var(&fin),
                vec![
                    (
                        step.more_pattern(a.clone()),
                        Self::returning(binder_var(&a), a.ty().clone()),
                    ),
                    (step.done_pattern(d), unreached),
                ],
            ),
        );
        Self::bind(threaded, fin, unwrap)
    }

    /// Answer a consumer the abort escapes: the return clause runs on a body
    /// that ran to its end and its answer steps beside the abort re-raised.
    fn consumer_reraise(
        &mut self,
        step: &StepAt,
        threaded: TypedComp,
        rv: TypedBinder,
        rb: TypedComp,
    ) -> Option<TypedComp> {
        let fin = TypedBinder::new(self.mint("fin"), step.ty());
        let a = TypedBinder::new(self.mint("a"), CoreType::Source(step.more.clone()));
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done.clone()));
        let out = StepAt::new(source_type(rb.sig().result()).ok()?, step.done.clone());
        let r = TypedBinder::new(self.mint("r"), rb.sig().result().clone());
        let row = rb.sig().effects().clone();
        let more = Self::bind(
            Self::returning(binder_var(&a), rv.ty().clone()),
            rv,
            Self::bind(
                rb,
                r.clone(),
                Self::returning(out.smore(binder_var(&r)), out.ty()),
            ),
        );
        let raised = Self::returning(out.sdone(binder_var(&d)), out.ty());
        let answer = TypedComp::new(
            CompSig::new(out.ty(), row),
            TypedCompKind::Case(
                binder_var(&fin),
                vec![(step.more_pattern(a), more), (step.done_pattern(d), raised)],
            ),
        );
        Some(Self::bind(threaded, fin, answer))
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
        halt: Option<Sym>,
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
            .map(|(clause, ru)| is_fold(clause, ru, self.plan.widen))
            .collect();

        // The accumulator's type at this handle is written on the clause lambdas
        // themselves: each clause is `\(acc) -> ..` and its binder carries the
        // type the seed will arrive at. The minted state quantifier is never used
        // here; a handle is a concrete instantiation site, not a parametric one.
        // The handle's residual is the row the whole handle expression carries:
        // what remains once its operations are discharged. Joined with the
        // enclosing scope's row, it is the row its evidence clauses run under
        // and its producer calls instantiate.
        let row = self.handle_row(c)?;
        let saved_row = mem::replace(&mut self.row, row);
        let saved_evidence = self.evidence_types.clone();
        let under = self.handle_evidence(evs, clauses)?;
        let body_ops = self.body_ops(body, loc, evs, clauses);
        let saved_step = self.step.clone();
        // A stopping arm answers the handle, so the step's done payload is what
        // its transformer returns and this site is where that payload lands.
        let answer_ty = match halt {
            Some(op) => Some(
                clauses
                    .arms()
                    .iter()
                    .find(|arm| arm.name() == op)
                    .and_then(|arm| transformer(arm.body()))
                    .and_then(|(_, inner)| source_type(inner.sig().result()).ok())?,
            ),
            // A producer beside an abort threads the step wherever it is
            // carried, so a scope no abort reaches still forces stepped
            // producers. Their done payload is never built, and the handle's
            // own answer stands in for it: the payload arm then returns it
            // exactly as a stopping arm's would.
            None if self.plan.folds_an_abort(&body_ops)
                && self.live_done().is_none()
                && !self.plan.early.short_circuits() =>
            {
                let (_, inner) = return_body.as_deref().and_then(transformer)?;
                Some(source_type(inner.sig().result()).ok()?)
            }
            None => None,
        };
        let mut handle_acc: Option<CoreType> = None;
        let mut ev_binds: Vec<(TypedBinder, TypedValue)> = Vec::with_capacity(clauses.arms().len());
        for (index, clause) in clauses.arms().iter().enumerate() {
            let (acc, inner) = transformer(clause.body())?;
            // One handle threads one accumulator, so its clauses must agree on
            // the type; the gate's per-producer pin check already refused the
            // programs where they cannot.
            match &handle_acc {
                Some(ty) if ty != acc.ty() => return None,
                _ => handle_acc = Some(acc.ty().clone()),
            }
            let ends = halt == Some(clause.name());
            let ev_body = if ends {
                self.rewrite(inner, loc, evs)?
            } else {
                let mut aliases = BTreeSet::new();
                aliases.insert(clause.resume().name());
                let (stripped, kind) = strip_state(inner, &aliases, acc.name(), self.plan.widen)?;
                // The ported rewrite and the shared judgment must agree about
                // what this clause resumes with. They are different code over
                // different trees, so this is a real check, and it runs on every
                // program rather than on the clauses a fixture happens to cover.
                if shared.get(index).copied().flatten() != Some(kind) {
                    return None;
                }
                self.rewrite(&stripped, loc, evs)?
            };
            let mut ev_params = clause.params().to_vec();
            // In a stepped scope the state is `Step Acc`: the evidence folds
            // inside `SMore` and forwards `SDone` untouched, so a stake or an
            // abort upstream can stop the loop.
            let at = match &answer_ty {
                Some(done) => Some(StepAt::new(source_type(acc.ty()).ok()?, done.clone())),
                None => self.scope_step(acc.ty(), &body_ops),
            };
            let ev_body = if let Some(at) = at {
                self.step = Some(at.clone());
                let carrier = TypedBinder::new(self.mint("step"), at.ty());
                let body = if ends {
                    self.step_stop(&at, &carrier, acc.clone(), ev_body)
                } else {
                    self.step_fold(&at, &carrier, acc.clone(), ev_body)
                };
                ev_params.push(carrier);
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
                *under.get(&clause.name())?,
                CoreType::Thunk(Box::new(lam.sig().clone())),
            );
            self.evidence_types.insert(ev.name(), ev.ty().clone());
            let thunk = TypedValue::new(ev.ty().clone(), TypedValueKind::Thunk(Box::new(lam)));
            ev_binds.push((ev, thunk));
        }

        // `g = \(acc0) -> <body threaded from acc0>`, closing over the evidence.
        // In a stepped scope the seed is wrapped `SMore(acc0)`; where the loop
        // only stops early the final `Step` is unwrapped back to the bare
        // accumulator, and where it can abort it stays stepped, because the
        // payload has nowhere to go until the handler that answers it.
        let acc0 = TypedBinder::new(self.mint("acc"), handle_acc?);
        let scope = match &answer_ty {
            Some(done) => Some(StepAt::new(source_type(acc0.ty()).ok()?, done.clone())),
            None => self.scope_step(acc0.ty(), &body_ops),
        };
        // A step whose two payloads coincide is read as a take's, whose pair
        // travels outside the step, while the producers forced here were
        // threaded with the pair inside it.
        if halt.is_none() && self.pairs() && scope.as_ref().is_some_and(|at| at.more == at.done) {
            return self.bail("a fold beside an abort whose answer is its own accumulator");
        }
        let g_body = if let Some(step_at) = scope.clone() {
            self.step = Some(step_at.clone());
            let st0 = TypedBinder::new(self.mint("st"), step_at.ty());
            let threaded = self.thread_st(body, &under, loc, &st0)?;
            let seeded = step_at.smore(binder_var(&acc0));
            let inner = if step_at.more == step_at.done {
                self.seed_unwrap(&step_at, threaded)
            } else {
                threaded
            };
            TypedComp::new(
                inner.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(seeded.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(seeded),
                    )),
                    st0,
                    Box::new(inner),
                ),
            )
        } else {
            self.thread_st(body, &under, loc, &acc0)?
        };
        let aborting = scope.filter(|at| at.more != at.done);
        let g_body = match &aborting {
            None => self.apply_state_return(
                g_body,
                return_binder.as_ref(),
                return_body.as_deref(),
                loc,
                evs,
            )?,
            Some(step_at) => {
                let answered = self.stepped_return(
                    g_body,
                    step_at,
                    answer_ty.is_some(),
                    (return_binder.as_ref(), return_body.as_deref()),
                    loc,
                    evs,
                )?;
                // The step this handle answers is its own; an enclosing take's
                // is the plan's and stays live for the tail that consumes it.
                self.step = saved_step;
                answered
            }
        };
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
        self.evidence_types = saved_evidence;
        self.row = saved_row;
        Some(out)
    }

    /// Apply a fold's return clause under a `Step`, keeping the abort's payload
    /// on the outside.
    ///
    /// The scope leaves through an operation this handle does not answer, so its
    /// result is still a step: the accumulator arm runs the transformer and
    /// steps again at whatever the transformer answers, and the payload arm
    /// re-raises untouched.
    fn stepped_return(
        &mut self,
        threaded: TypedComp,
        step: &StepAt,
        answers: bool,
        ret: (Option<&TypedBinder>, Option<&TypedComp>),
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedComp> {
        // The threaded body says what its `SMore` holds: the accumulator, or the
        // accumulator beside the value where the scope carries both. Either way
        // the return clause runs past the step, on what the step held.
        let at = carried_step(threaded.sig().result()).unwrap_or_else(|| step.clone());
        let fin = TypedBinder::new(self.mint("fin"), at.ty());
        let a = TypedBinder::new(self.mint("a"), CoreType::Source(at.more.clone()));
        let bare = Self::returning(binder_var(&a), a.ty().clone());
        let answered = self.apply_state_return(bare, ret.0, ret.1, loc, evs)?;
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done.clone()));
        let row = answered.sig().effects().clone();
        // A stopping arm's payload is the handle's answer, so it is returned as
        // it stands; an abort this handle does not answer is re-raised, and the
        // answer steps beside it.
        let (more, raised, result) = if answers {
            let answer = answered.sig().result().clone();
            (
                answered,
                Self::returning(binder_var(&d), answer.clone()),
                answer,
            )
        } else {
            let out = StepAt::new(
                source_type(answered.sig().result()).ok()?,
                step.done.clone(),
            );
            let r = TypedBinder::new(self.mint("r"), answered.sig().result().clone());
            (
                Self::bind(
                    answered,
                    r.clone(),
                    Self::returning(out.smore(binder_var(&r)), out.ty()),
                ),
                Self::returning(out.sdone(binder_var(&d)), out.ty()),
                out.ty(),
            )
        };
        let answer = TypedComp::new(
            CompSig::new(result, row),
            TypedCompKind::Case(
                binder_var(&fin),
                vec![(at.more_pattern(a), more), (at.done_pattern(d), raised)],
            ),
        );
        Some(Self::bind(threaded, fin, answer))
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
            return self.drop_value(threaded);
        }
        let TypedCompKind::Return(v) = rb.kind() else {
            return None;
        };
        let TypedValueKind::Thunk(t) = &peel(v).kind else {
            return None;
        };
        let TypedCompKind::Lam(ps, body) = t.kind() else {
            return None;
        };
        let [s] = ps.as_slice() else {
            return None;
        };
        let rbody = self.rewrite(body, loc, evs)?;
        if self.pairs() {
            // The scope carried both, so the transformer's state parameter and
            // the handle's value binder are the pair's two components instead
            // of one accumulator standing for both.
            let named = return_binder.cloned();
            let (fin, value) = self.pair_binders(&threaded, named.as_ref())?;
            let read_fin = TypedComp::new(
                CompSig::new(fin.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(binder_var(&fin)),
            );
            let inner = Self::bind(read_fin, s.clone(), rbody);
            return self.split_pair(threaded, fin, value, inner);
        }
        let fin = TypedBinder::new(self.mint("fin"), threaded.sig().result().clone());
        let r = return_binder
            .cloned()
            .unwrap_or_else(|| TypedBinder::new(self.mint("r"), fin.ty().clone()));
        let read_fin = || {
            TypedComp::new(
                CompSig::new(fin.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(binder_var(&fin)),
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
        let TypedValueKind::Thunk(t) = &peel(v).kind else {
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
            source_type(st.ty()).ok()?,
            source_type(cnt.ty()).ok()?,
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
        let sd_val = step.sdone(binder_var(&sd));
        let evt_body = TypedComp::new(
            smore_body.sig().clone(),
            TypedCompKind::Case(
                binder_var(&tstep),
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
                source_type(st.ty()).ok()?,
                source_type(seed.ty()).ok()?,
            ])),
            TypedValueKind::Tuple(vec![binder_var(st), seed.clone()]),
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
                TypedCompKind::Return(binder_var(d)),
            )
        };
        let extract = TypedComp::new(
            CompSig::new(st.ty().clone(), EffRow::Empty),
            TypedCompKind::Case(
                binder_var(&fin),
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
                        source_type(dstep.ty()).ok()?,
                        source_type(cnt.ty()).ok()?,
                    ])),
                    TypedValueKind::Tuple(vec![binder_var(dstep), binder_var(cnt)]),
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
                a.push(binder_var(dstep));
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
                let applied = instantiate_fn(fun, &inst).ok()?;
                let call = TypedComp::new(
                    applied.body().clone(),
                    TypedCompKind::App {
                        callee: Box::new(TypedComp::new(
                            thunk.as_ref().clone(),
                            TypedCompKind::Force(binder_var(t.ev)),
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
                                TypedCompKind::Return(unit_value()),
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
                    if as_var(k) == Some(kr.name()))
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
                        source_type(dstep.ty()).ok()?,
                        source_type(next.ty()).ok()?,
                    ])),
                    TypedValueKind::Tuple(vec![binder_var(dstep), next.clone()]),
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
                source_type(a.ty()).ok()?,
                source_type(b.ty()).ok()?,
            ])),
        );
        let inner = TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Case(
                binder_var(&p),
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

    /// [`Self::step_fold`] for a clause that ends the fold rather than
    /// continuing it: the body computes the payload the fold stops with, and a
    /// carrier that already stopped forwards the payload it holds. No step is
    /// rebuilt, because the perform site puts this payload into the step it is
    /// itself threading, which is the one that knows what the scope carries.
    fn step_stop(
        &mut self,
        step: &StepAt,
        sv: &TypedBinder,
        acc: TypedBinder,
        body: TypedComp,
    ) -> TypedComp {
        let out = CoreType::Source(step.done.clone());
        let sd = TypedBinder::new(self.mint("sd"), out.clone());
        let row = body.sig().effects().clone();
        TypedComp::new(
            CompSig::new(out.clone(), row),
            TypedCompKind::Case(
                binder_var(sv),
                vec![
                    (step.more_pattern(acc), body),
                    (
                        step.done_pattern(sd.clone()),
                        TypedComp::new(
                            CompSig::new(out, EffRow::Empty),
                            TypedCompKind::Return(binder_var(&sd)),
                        ),
                    ),
                ],
            ),
        )
    }

    /// `\(.., acc) -> body` lifted to operate on `Step Acc`: fold inside
    /// `SMore`, forward `SDone` untouched.
    fn step_fold(
        &mut self,
        step: &StepAt,
        sv: &TypedBinder,
        acc: TypedBinder,
        body: TypedComp,
    ) -> TypedComp {
        let r = TypedBinder::new(self.mint("r"), body.sig().result().clone());
        let sd = TypedBinder::new(self.mint("sd"), CoreType::Source(step.done.clone()));
        let folded = step.smore(binder_var(&r));
        let forwarded = step.sdone(binder_var(&sd));
        // The SMore arm folds the body, which now honestly reports the ambient
        // residual; the arm and the enclosing Case carry that row. The SDone arm
        // stays Empty, and the Case union derives the ambient from the SMore arm.
        let row = body.sig().effects().clone();
        TypedComp::new(
            CompSig::new(step.ty(), row.clone()),
            TypedCompKind::Case(
                binder_var(sv),
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

    /// Stop the producer once the accumulator has yielded `SDone`, else run the
    /// rest. The step's two payloads are the same type only for a take; an
    /// abort carries its own, so each arm reads the one its constructor holds.
    fn step_guard(&mut self, step: &StepAt, sv: &TypedBinder, cont: TypedComp) -> TypedComp {
        let m = TypedBinder::new(self.mint("_w"), CoreType::Source(step.more.clone()));
        let d = TypedBinder::new(self.mint("_w"), CoreType::Source(step.done.clone()));
        TypedComp::new(
            cont.sig().clone(),
            TypedCompKind::Case(
                binder_var(sv),
                vec![
                    (step.more_pattern(m), cont),
                    (
                        step.done_pattern(d),
                        TypedComp::new(
                            CompSig::new(sv.ty().clone(), EffRow::Empty),
                            TypedCompKind::Return(binder_var(sv)),
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
                TypedCompKind::Return(binder_var(x)),
            )
        };
        let unwrap = TypedComp::new(
            CompSig::new(a.ty().clone(), EffRow::Empty),
            TypedCompKind::Case(
                binder_var(&fin),
                vec![
                    (step.more_pattern(a.clone()), ret(&a)),
                    (step.done_pattern(b.clone()), ret(&b)),
                ],
            ),
        );
        Self::bind(threaded, fin, unwrap)
    }
}

/// The row a thunk type's body runs under, when `ty` is a thunk of a function.
pub(super) fn thunk_row(ty: &CoreType) -> Option<&EffRow> {
    let CoreType::Thunk(sig) = ty else {
        return None;
    };
    let CoreType::Function(fun) = sig.result() else {
        return None;
    };
    Some(fun.body().effects())
}
