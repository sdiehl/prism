//! Accumulator-threading transformation and local escape checks.

mod rewrite;

use super::super::{
    abi::try_word_bridge, as_var, binder_var, evidence::strip_resume, peel,
    subtract::SubtractEffect, unit_value,
};
use super::strip::strip_state;
use super::uniformity::{
    body_folds, branch_resumes, folds_op, forced_source_type, is_take, lexical_types, row_tail,
};
use super::{
    accumulator_type, bound_producer_result, clause_type, flow, free_comp_vars, free_value_vars,
    instantiate_fn, is_fold, is_id_return, is_id_transformer, label_args, mem, names, produces,
    source_type, substitute_core_type, substitute_terms, substitute_witnesses, union_rows,
    BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, DriftLog,
    EffRow, FoldAKind, FoldPlan, Latent, Loc, OpIds, Retyped, Sig, StepAt, Sym, ThunkFlow, Type,
    TypedBinder, TypedComp, TypedCompKind, TypedPattern, TypedValue, TypedValueKind, VerifyEnv,
    STATE_ACC,
};

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
pub(super) fn a_kind(a: &TypedValue, acc: Sym) -> Option<FoldAKind> {
    match &peel(a).kind {
        TypedValueKind::Unit => Some(FoldAKind::Unit),
        TypedValueKind::Var { name, .. } if *name == acc => Some(FoldAKind::Acc),
        _ => None,
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
    /// The one `Step` instantiation live in the scope being threaded, decided
    /// where the early-exit protocol is entered (a handle in early mode, a
    /// take) and consumed by every guard, lift, unwrap, constructor and
    /// pattern inside that scope. One builder owns each representation fact;
    /// reconstructing `Step(acc, acc)` at a use site from whatever type is
    /// nearby is how the take witnesses drifted.
    pub step: Option<StepAt>,
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
                a.push(binder_var(st));
                Self::apply_clause(&ev, instantiation, a, st)?
            }
            TypedCompKind::Return(_) => TypedComp::new(
                CompSig::new(st.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(binder_var(st)),
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
                a.push(binder_var(st));
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
                        None => source_type(st.ty()).ok()?,
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
                a.push(binder_var(st));
                let mut inst = instantiation.clone();
                for q in fun.quantifiers().iter().skip(instantiation.len()) {
                    match q {
                        CoreQuantifier::Type(_) => {
                            let base = match &self.step {
                                Some(step) => step.done.clone(),
                                None => source_type(st.ty()).ok()?,
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
        let stripped = strip_resume(clause.body(), &aliases, self.drift)?;

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
        let saved_row = mem::replace(&mut self.row, c.sig().effects().clone());

        // Evidence: run the clause's side effects, then return the state.
        let mut aliases = BTreeSet::new();
        aliases.insert(clause.resume().name());
        let stripped = strip_resume(clause.body(), &aliases, self.drift)?;
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
                    TypedCompKind::Return(binder_var(&st)),
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
                TypedCompKind::Return(binder_var(&rv)),
            ),
        };
        let (seed, body_done) = if self.plan.early.short_circuits() {
            (
                step_at.smore(unit_value()),
                self.seed_unwrap(&step_at, threaded),
            )
        } else {
            (unit_value(), threaded)
        };
        let bind = |head: TypedComp, x: TypedBinder, tail: TypedComp| Self::bind(head, x, tail);
        let read_fin = TypedComp::new(
            CompSig::new(fin.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(binder_var(&fin)),
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
        let saved_row = mem::replace(&mut self.row, c.sig().effects().clone());
        let mut handle_acc: Option<CoreType> = None;
        let mut ev_binds: Vec<(TypedBinder, TypedValue)> = Vec::with_capacity(clauses.arms().len());
        for (index, clause) in clauses.arms().iter().enumerate() {
            let TypedCompKind::Return(v) = clause.body().kind() else {
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
                let source = source_type(acc.ty()).ok()?;
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
            let source = source_type(acc0.ty()).ok()?;
            let step_at = StepAt::new(source.clone(), source);
            self.step = Some(step_at.clone());
            let st0 = TypedBinder::new(self.mint("st"), step_at.ty());
            let threaded = self.thread_st(body, evs, loc, &st0)?;
            let seeded = step_at.smore(binder_var(&acc0));
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

    /// Stop the producer once a `stake` has yielded `SDone`, else run the rest.
    fn step_guard(&mut self, step: &StepAt, sv: &TypedBinder, cont: TypedComp) -> TypedComp {
        let m = TypedBinder::new(self.mint("_w"), CoreType::Source(step.done.clone()));
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
