//! Rewriting outside the active accumulator-threading path.

use super::super::super::{binder_var, peel, union_effects, walk};
use super::{
    accumulator_type, body_folds, clause_type, flow, folds_op, instantiate_fn, label_args, mem,
    names, produces, union_rows, BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreInstantiation,
    CoreQuantifier, CoreType, EffRow, FoldAKind, Loc, Sig, Sym, Threader, TypedBinder, TypedComp,
    TypedCompKind, TypedValue, TypedValueKind, STATE_ACC,
};

impl Threader<'_> {
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
    pub(in super::super) fn rewrite_value(
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
        Some(match &peel(v).kind {
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
                    let saved_row = mem::replace(&mut self.row, EffRow::Var(ambient));
                    let saved_step = mem::replace(&mut self.step, step);
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
    pub(super) fn ordered(&self, evs: &BTreeMap<Sym, Sym>) -> Option<Vec<(i64, Sym)>> {
        let mut ordered: Vec<(i64, Sym)> = evs
            .keys()
            .map(|op| Some((self.ids.id(*op)?, *op)))
            .collect::<Option<_>>()?;
        ordered.sort_unstable();
        Some(ordered)
    }

    /// Rewrite a computation the accumulator does not thread through: it performs
    /// no fused operation, so only what it contains can need rewriting.
    pub(in super::super) fn rewrite(
        &mut self,
        c: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedComp> {
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
                        instantiate_fn(new_sig, instantiation)
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
                let applied = instantiate_fn(fun, instantiation).ok()?;
                // The exact, fallible union: a non-representable union of two
                // open tails is a State decline, never permission to drop one.
                let effects = union_rows(callee2.sig().effects(), applied.body().effects()).ok()?;
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
    pub(super) fn carries_producer(
        &self,
        c: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> bool {
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        let mut found = false;
        walk::each_value(c, &mut |v| {
            found |= flow::value_sig(v, loc, self.latent)
                .iter()
                .any(|m| ops.contains(&m.id));
        });
        found
    }

    /// The evidence a producer call passes, one per fused operation in ascending
    /// operation-id order, using the evidence active here.
    pub(super) fn evidence_args(
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
            .map(|(_, op)| Some(binder_var(&self.evidence(evs, op, acc)?)))
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
    pub(super) fn evidence(
        &self,
        evs: &BTreeMap<Sym, Sym>,
        op: Sym,
        acc: &CoreType,
    ) -> Option<TypedBinder> {
        let name = *evs.get(&op)?;
        let ty = if let Some(ty) = self.evidence_types.get(&name) {
            ty.clone()
        } else {
            clause_type(op, acc, &self.row.clone(), &[], self.env)?
        };
        Some(TypedBinder::new(name, ty))
    }

    /// Apply an operation's clause to its arguments and the accumulator.
    pub(super) fn apply_clause(
        ev: &TypedBinder,
        instantiation: &[CoreInstantiation],
        args: Vec<TypedValue>,
        st: &TypedBinder,
    ) -> Option<TypedComp> {
        let CoreType::Thunk(thunk) = ev.ty() else {
            return None;
        };
        let force = TypedComp::new(thunk.as_ref().clone(), TypedCompKind::Force(binder_var(ev)));
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

    pub(super) fn numbered(&self, evs: &BTreeMap<Sym, Sym>) -> Option<Vec<i64>> {
        let mut v: Vec<i64> = evs
            .keys()
            .map(|op| self.ids.id(*op))
            .collect::<Option<_>>()?;
        v.sort_unstable();
        Some(v)
    }

    /// What a producing head's tail resumes with, which decides what its bound
    /// result reads: a read observes the pre-operation accumulator, a write unit.
    pub(super) fn op_tail_kind(
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
    pub(super) fn bind(head: TypedComp, binder: TypedBinder, tail: TypedComp) -> TypedComp {
        let sig = CompSig::new(
            tail.sig().result().clone(),
            union_effects(head.sig().effects(), tail.sig().effects()),
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
    pub(super) fn lam(params: Vec<TypedBinder>, body: TypedComp) -> TypedComp {
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

    pub(super) fn mint(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }
}
