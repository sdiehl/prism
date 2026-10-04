//! Threading through the value channel: producers pass evidence and return
//! their own value, stepped over the abort payload where an abort can reach.
//!
//! A direct clause is a bare function of the operation's arguments. An abort
//! clause returns `SDone(payload)` and nothing else, so every producing bind
//! whose head can abort is guarded by a case that passes the payload upward,
//! and the handle site unwraps the step: `SMore` runs the return clause,
//! `SDone` runs the abort arm with its parameters bound from the payload.

use super::super::super::checks::kind_name;
use super::super::super::subtract::subtract_row;
use crate::core::{TypedHandleOp, TypedHandler};

use super::super::super::super::specialize_support::free_comp_vars;
use super::super::super::{union_effects, union_rows};
use super::super::resume::strip_resume;
use super::super::{value_abort, value_clause_type, value_scheme, Abort};
use super::{
    binder_var, flow, generic_quantifiers, instantiate_fn, label_args, mem, names, on_core_stack,
    passes_return, produces, residual_row, source_type, unit_source, unit_value, BTreeMap,
    BTreeSet, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, EffRow, Loc, StepAt,
    Sym, Threader, Type, TypedBinder, TypedComp, TypedCompKind, TypedPattern, TypedValue,
    TypedValueKind,
};

/// An abort's payload: its parameters tupled, one alone, or unit.
fn payload_type(params: &[TypedBinder]) -> Option<Type> {
    let tys: Vec<Type> = params
        .iter()
        .map(|p| source_type(p.ty()).ok())
        .collect::<Option<_>>()?;
    Some(match tys.as_slice() {
        [] => Type::Unit,
        [ty] => ty.clone(),
        _ => Type::Tuple(tys),
    })
}

fn payload_value(params: &[TypedBinder]) -> Option<TypedValue> {
    Some(match params {
        [] => unit_value(),
        [p] => binder_var(p),
        _ => TypedValue::new(
            CoreType::Source(payload_type(params)?),
            TypedValueKind::Tuple(params.iter().map(binder_var).collect()),
        ),
    })
}

impl Threader<'_> {
    /// Thread `c` by value. `early` when this scope answers with a `Step`: its
    /// operations include the live abort, so a tail value is `SMore` and an
    /// aborting head's payload is passed upward.
    pub(in super::super) fn thread_val(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        early: bool,
    ) -> Option<TypedComp> {
        // A bind spine is threaded a node at a time, so the recursion is as deep
        // as the program's longest sequence; grow stack segments inside it, the
        // same discipline the shared descent keeps.
        let out = on_core_stack(|| self.thread_val_on_core_stack(c, evs, loc, early));
        self.dropped(c, out)
    }

    fn thread_val_on_core_stack(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        early: bool,
    ) -> Option<TypedComp> {
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        Some(match c.kind() {
            // Re-associate a let-bound compound computation so its inner
            // operations surface as flat producing binds.
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
                self.thread_val(&flat, evs, loc, early)?
            }
            // A bind whose head performs an operation. A head that can abort
            // answers with a step, unwrapped here: its value continues, its
            // payload is this scope's answer.
            TypedCompKind::Bind(m, x, n)
                if produces(m, loc, &ops, self.latent, self.flow) || self.can_abort(m, loc) =>
            {
                let head_early = self.can_abort(m, loc);
                if head_early && !early {
                    return self.bail("an aborting head in a scope that does not step");
                }
                let tm = self.thread_val(m, evs, loc, head_early)?;
                // A head answering a transformer defers its abort to the
                // application that runs it: the step is the applied body's,
                // so the binder follows the retyped thunk and the tail steps
                // on its own.
                let deferred = head_early
                    && self
                        .deferred_step(x.ty())
                        .is_some_and(|ty| tm.sig().result() == &ty);
                let head_early = head_early && !deferred;
                // A binder follows its head before the tail reads it: a head
                // answering with a widened thunk retypes every force after.
                let x2 = if head_early {
                    x.clone()
                } else {
                    self.follow(x, tm.sig().result())
                };
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    flow::result_sig_in(m, loc, self.latent, self.flow),
                );
                let tn = self.thread_val(n, evs, &loc2, early)?;
                if head_early {
                    let step = StepAt::new(source_type(x.ty()).ok()?, self.done()?);
                    if tm.sig().result() != &step.ty() {
                        return self.bail(format!(
                            "an aborting head whose result is not this scope's step ({} at {})",
                            tm.sig().result(),
                            step.ty()
                        ));
                    }
                    let sv = TypedBinder::new(self.mint("sv"), step.ty());
                    let guard = self.value_guard(&step, &sv, x2, tn)?;
                    Self::bind(tm, sv, guard)
                } else {
                    Self::bind(tm, x2, tn)
                }
            }
            // A perform is a call of its evidence. An abort's evidence already
            // answers with a step; a direct one is lifted when the scope steps.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } if evs.contains_key(operation) => {
                // A clause on this channel holds no accumulator, so an
                // operation the scope threads as state has nothing here to
                // answer it with: a direct clause performing one does not
                // leave the state as it found it, and is not direct after all.
                if !self.plan.value_shaped(*operation) {
                    return self.bail(format!(
                        "a direct clause performing `{}`, which this scope threads as state",
                        operation.as_str()
                    ));
                }
                let Some(aborts) = self.head_aborts(&BTreeSet::from([*operation])) else {
                    return self.bail(format!(
                        "`{}` aborting with an operation this scope cannot answer",
                        operation.as_str()
                    ));
                };
                let ev = self.value_evidence(evs, *operation)?;
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, evs))
                    .collect::<Option<_>>()?;
                if a.is_empty() {
                    a.push(unit_value());
                }
                let app = self.apply_value_clause(&ev, *operation, instantiation, a)?;
                self.lift(app, early, aborts)?
            }
            TypedCompKind::Return(v) => {
                let v2 = self.rewrite_value(v, loc, evs)?;
                if early {
                    let step = StepAt::new(source_type(v2.ty()).ok()?, self.done()?);
                    Self::returning(step.smore(v2), step.ty())
                } else {
                    let ty = v2.ty().clone();
                    Self::returning(v2, ty)
                }
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.thread_val(t, evs, loc, early)?;
                let e2 = self.thread_val(e, evs, loc, early)?;
                let sig = CompSig::new(
                    t2.sig().result().clone(),
                    union_effects(t2.sig().effects(), e2.sig().effects()),
                );
                TypedComp::new(
                    sig,
                    TypedCompKind::If(v.clone(), Box::new(t2), Box::new(e2)),
                )
            }
            // A pure head passes through; its binder follows the head it binds.
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.rewrite_head(m, x, n, loc, evs)?;
                let x2 = self.follow(x, m2.sig().result());
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    flow::result_sig_in(m, loc, self.latent, self.flow),
                );
                let n2 = self.thread_val(n, evs, &loc2, early)?;
                Self::bind(m2, x2, n2)
            }
            // A tail call to a producer: append this site's evidence in the
            // producer's own order, instantiate the done type when the callee
            // can abort, and the ambient row at this site's residual.
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
                let Some(aborts) = self.head_aborts(&callee_ops) else {
                    return self.bail(format!(
                        "a call to `{}`, which aborts with an operation this scope cannot answer",
                        callee.as_str()
                    ));
                };
                let (inst, applied) = {
                    let new_sig = self.signatures.get(callee)?;
                    let inst = self.producer_instantiation(new_sig, instantiation)?;
                    let applied = instantiate_fn(new_sig, &inst).ok()?;
                    (inst, applied)
                };
                let mut a = self.call_args(args, Some(&applied), Some(*callee), loc, evs)?;
                a.extend(self.value_evidence_args(evs, &callee_ops)?);
                let call = TypedComp::new(
                    applied.body().clone(),
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation: inst,
                        args: a,
                    },
                );
                self.lift(call, early, aborts)?
            }
            TypedCompKind::Case(v, arms) => {
                let arms: Vec<_> = arms
                    .iter()
                    .map(|(p, b)| self.arm(p, |this| this.thread_val(b, evs, loc, early)))
                    .collect::<Option<_>>()?;
                let result = arms.first().map(|(_, b)| b.sig().result().clone())?;
                let effects = arms.iter().fold(EffRow::Empty, |acc, (_, b)| {
                    union_effects(&acc, b.sig().effects())
                });
                TypedComp::new(
                    CompSig::new(result, effects),
                    TypedCompKind::Case(self.scrutinee(v), arms),
                )
            }
            // A force of an escaping producer thunk, which gained evidence
            // parameters and rank-2 quantifiers when it was rewritten.
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } if produces(c, loc, &ops, self.latent, self.flow) => {
                let TypedCompKind::Force(v) = callee.kind() else {
                    return None;
                };
                let v2 = self.retyped.rebuild_through(v);
                let CoreType::Thunk(thunk) = v2.ty().clone() else {
                    return None;
                };
                let CoreType::Function(fun) = thunk.result() else {
                    return None;
                };
                let carried: BTreeSet<Sym> = flow::value_sig_in(v, loc, self.latent, self.flow)
                    .into_iter()
                    .map(|masked| masked.id)
                    .filter(|operation| ops.contains(operation))
                    .collect();
                let Some(aborts) = self.head_aborts(&carried) else {
                    return self.bail(
                        "a forced thunk aborting with an operation this scope cannot answer",
                    );
                };
                let inst = self.producer_instantiation(fun, instantiation)?;
                let applied = instantiate_fn(fun, &inst).ok()?;
                let mut a = self.call_args(args, Some(&applied), None, loc, evs)?;
                a.extend(self.value_evidence_args(evs, &carried)?);
                let force = TypedComp::new(thunk.as_ref().clone(), TypedCompKind::Force(v2));
                let app = TypedComp::new(
                    applied.body().clone(),
                    TypedCompKind::App {
                        callee: Box::new(force),
                        instantiation: inst,
                        args: a,
                    },
                );
                self.lift(app, early, aborts)?
            }
            // A handle whose clauses do not answer this scope's abort hands the
            // payload onward, so its answer already steps and nothing lifts it.
            TypedCompKind::Handle { .. } if self.passes_abort(c, loc) => {
                self.rewrite(c, loc, evs)?
            }
            // A tail that performs nothing fused yields its own value.
            _ if !produces(c, loc, &ops, self.latent, self.flow) => {
                let c2 = self.rewrite(c, loc, evs)?;
                self.lift(c2, early, false)?
            }
            // A handle inside a value-threaded scope is not fused yet.
            _ => return self.bail(format!("a {} in a value scope", kind_name(c.kind()))),
        })
    }

    /// Lower a handler of direct and abort clauses at its handle site: each
    /// clause becomes a bound evidence thunk, the body is threaded under this
    /// handle's abort, and the answer runs the return clause on the body's
    /// value or the abort arm on the payload.
    pub(super) fn lower_direct(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        abort: Option<Sym>,
    ) -> Option<TypedComp> {
        let row = self.handle_row(c)?;
        let saved_row = mem::replace(&mut self.row, row);
        // Evidence is named by operation, so this handle's clauses shadow the
        // scope's same-named evidence for exactly the extent they are bound
        // around; past the handle, the scope's evidence is in force again.
        let saved_evidence = self.evidence_types.clone();
        let out = self.lower_direct_in(c, evs, loc, abort);
        self.evidence_types = saved_evidence;
        self.row = saved_row;
        out
    }

    fn lower_direct_in(
        &mut self,
        c: &TypedComp,
        evs: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        abort: Option<Sym>,
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
        let abort_arm = abort.and_then(|op| clauses.arms().iter().find(|arm| arm.name() == op));
        // An operation another handler aborts is stepped wherever it is
        // performed, because the producer that performs it has one evidence
        // type. A handler that resumes it answers that step: its clause returns
        // `SMore` and this site unwraps, where a `SDone` cannot arrive because
        // no clause bound here makes one.
        // An operation whose clause here leaves through the abort live around
        // this handle is not merely stepped: its step is the enclosing one and
        // this site hands the payload on rather than unwrapping it. Another
        // handler's clause leaving through that abort steps the operation
        // everywhere, but a clause here that stays answers the step itself.
        let resumed: Vec<Sym> = if self.plan.widen && abort_arm.is_none() {
            clauses
                .arms()
                .iter()
                .filter(|arm| {
                    self.plan.aborts.contains(&arm.name())
                        || self.plan.taint.contains_key(&arm.name())
                })
                .filter(|arm| !self.clause_leaves(arm, loc))
                .map(TypedHandleOp::name)
                .collect()
        } else {
            Vec::new()
        };
        let resumed = match resumed.as_slice() {
            [] => None,
            [op] => Some(*op),
            ops => {
                let named: Vec<String> =
                    ops.iter().map(|op| format!("`{}`", op.as_str())).collect();
                return self.bail(format!(
                    "a handler resuming {}, which abort elsewhere",
                    named.join(", ")
                ));
            }
        };
        let own: BTreeSet<Sym> = clauses.arms().iter().map(TypedHandleOp::name).collect();
        // An abort this handle does not answer stays live in its body: the
        // handle discharges the operations it names and hands the payload on,
        // so the body still steps and the answer re-raises what it carries.
        let inherited = self
            .abort
            .clone()
            .filter(|(op, _)| self.plan.widen && !own.contains(op));
        // A resumed operation's step carries the payload live here, where an
        // abort is inherited; otherwise the one its own abort names, which is
        // this handle's answer.
        let done = match (abort_arm, resumed) {
            (Some(arm), _) => Some(payload_type(arm.params())?),
            (None, Some(_)) => Some(match &inherited {
                Some((_, live)) => live.clone(),
                None => source_type(c.sig().result()).ok()?,
            }),
            (None, None) => None,
        };
        // A clause is a value of the enclosing scope, so it sees that scope's
        // evidence and not its siblings'.
        let outer: BTreeMap<Sym, Sym> = evs
            .iter()
            .filter(|(op, _)| !own.contains(op))
            .map(|(op, ev)| (*op, *ev))
            .collect();
        let under = self.handle_evidence(evs, clauses)?;
        let mut bound = Vec::new();
        for clause in clauses.arms() {
            let lam = if Some(clause.name()) == abort {
                self.abort_clause(clause, done.as_ref()?)
            } else if Some(clause.name()) == resumed {
                self.direct_clause(clause, &outer, loc, done.as_ref())
            } else {
                self.direct_clause(clause, &outer, loc, None)
            };
            let lam = lam?;
            let ty = CoreType::Thunk(Box::new(lam.sig().clone()));
            let ev = TypedBinder::new(*under.get(&clause.name())?, ty.clone());
            self.evidence_types.insert(ev.name(), ty.clone());
            bound.push((
                ev,
                TypedValue::new(ty, TypedValueKind::Thunk(Box::new(lam))),
            ));
        }

        // The step a resumed operation answers with is the one its own abort
        // names, which is the operation itself when its clause aborts and the
        // operation it raises through when a handler's does. Inside another
        // abort's scope that step must be the enclosing one, so the answer
        // unwraps what the clause resumed and hands an abort's payload on.
        let stepped = resumed
            .and_then(|op| self.plan.abort_in(&BTreeSet::from([op])))
            .flatten();
        let own_step = stepped.zip(done.clone());
        if let Some(live) = inherited
            .as_ref()
            .filter(|live| resumed.is_some() && own_step.as_ref() != Some(live))
        {
            return self.bail(format!(
                "a handler resuming an abort inside another abort's scope ({} inside `{}` at {:?})",
                own_step.as_ref().map_or_else(
                    || "no step".to_string(),
                    |(op, done)| format!("`{}` at {done:?}", op.as_str())
                ),
                live.0.as_str(),
                live.1
            ));
        }
        let live = abort.zip(done).or(own_step).or_else(|| inherited.clone());
        let passes =
            abort_arm.is_none() && (resumed.is_none() || inherited.is_some()) && live.is_some();
        let early = live.is_some();
        let saved_abort = mem::replace(&mut self.abort, live);
        let threaded = self.thread_val(body, &under, loc, early);
        self.abort = saved_abort;
        let threaded = threaded?;

        // The answer runs in the enclosing scope, where it performs nothing
        // fused yet.
        let outer_ops: BTreeSet<Sym> = outer.keys().copied().collect();
        let rv = return_binder.as_ref().map_or_else(
            || TypedBinder::new(self.mint("r"), body.sig().result().clone()),
            Clone::clone,
        );
        let rb = match return_body {
            // The return clause runs outside the handle, so an operation it
            // performs is the enclosing scope's to thread, and the accumulator
            // that scope threads has already been consumed by the body.
            Some(b) if produces(b, loc, &outer_ops, self.latent, self.flow) => {
                return self
                    .bail("a return clause that performs an operation the enclosing scope threads")
            }
            Some(b) => self.rewrite(b, loc, &outer)?,
            None => Self::returning(binder_var(&rv), rv.ty().clone()),
        };
        let out = match abort_arm {
            None if passes => {
                let step = StepAt::of(threaded.sig().result())?;
                let sv = TypedBinder::new(self.mint("sv"), step.ty());
                let more = self.lift(rb, true, false)?;
                let guard = self.value_guard(&step, &sv, rv, more)?;
                Self::bind(threaded, sv, guard)
            }
            None if resumed.is_some() => {
                let step = StepAt::of(threaded.sig().result())?;
                let fin = TypedBinder::new(self.mint("fin"), step.ty());
                let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done.clone()));
                let unreached = Self::returning(binder_var(&d), c.sig().result().clone());
                let answer = TypedComp::new(
                    CompSig::new(c.sig().result().clone(), rb.sig().effects().clone()),
                    TypedCompKind::Case(
                        binder_var(&fin),
                        vec![
                            (step.more_pattern(rv), rb),
                            (step.done_pattern(d), unreached),
                        ],
                    ),
                );
                Self::bind(threaded, fin, answer)
            }
            None => Self::bind(threaded, rv, rb),
            Some(arm) => {
                if produces(arm.body(), loc, &outer_ops, self.latent, self.flow) {
                    return self.bail(
                        "an abort arm that performs an operation the enclosing scope threads",
                    );
                }
                let on_done = self.rewrite(arm.body(), loc, &outer)?;
                let step = StepAt::of(threaded.sig().result())?;
                let fin = TypedBinder::new(self.mint("fin"), step.ty());
                let (pattern, on_done) = self.payload_arm(&step, arm.params(), on_done);
                let answer = TypedComp::new(
                    CompSig::new(
                        c.sig().result().clone(),
                        union_effects(rb.sig().effects(), on_done.sig().effects()),
                    ),
                    TypedCompKind::Case(
                        binder_var(&fin),
                        vec![(step.more_pattern(rv), rb), (pattern, on_done)],
                    ),
                );
                Self::bind(threaded, fin, answer)
            }
        };
        Some(bound.into_iter().rev().fold(out, |acc, (ev, thunk)| {
            Self::bind(Self::returning(thunk, ev.ty().clone()), ev, acc)
        }))
    }

    /// Lower a re-emitting forwarder on the value channel: a handler whose one
    /// tail-resumptive clause performs the same operation again, so the handle
    /// discharges nothing and its answer is the handled body's own value.
    ///
    /// The clause becomes evidence bound under a fresh name that shadows the
    /// operation for the extent of the handled body, exactly as the state
    /// channel does, except that a value clause takes only the operation's
    /// arguments: there is no accumulator to thread beside them.
    pub(super) fn value_forward(
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
            return self.bail("a forwarder with several arms");
        };
        if !evs.contains_key(&clause.name()) {
            return self.bail(format!(
                "a forwarder of `{}` without evidence in scope",
                clause.name().as_str()
            ));
        }
        // The forwarded body's final value is the handle's answer, so the
        // return clause must hand it on untouched.
        let erased_return = return_body.as_deref().map(|b| b.clone().erase());
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
        let aliases = BTreeSet::from([clause.resume().name()]);
        let stripped = strip_resume(clause.body(), &aliases, self.drift)?;
        // The clause re-emits into the evidence this scope already holds for
        // the operation, so it threads under the unshadowed map. A clause
        // that leaves through the abort live here answers with its step, as
        // any stepped clause of the operation does.
        let aborts = self.can_abort(&stripped, loc);
        let ev_body = self.thread_val(&stripped, evs, loc, aborts)?;
        let params = self.clause_binders(clause.params());
        let lam = Self::lam(params, ev_body);
        let inner = TypedBinder::new(
            self.mint("ev"),
            CoreType::Thunk(Box::new(lam.sig().clone())),
        );
        self.evidence_types.insert(inner.name(), inner.ty().clone());
        let thunk = TypedValue::new(inner.ty().clone(), TypedValueKind::Thunk(Box::new(lam)));
        let mut evs2 = evs.clone();
        evs2.insert(clause.name(), inner.name());
        // An abort this handle does not name stays live in the body, whose
        // answer already steps; the identity return passes that step on.
        let early = self.passes_abort(c, loc);
        let threaded = self.thread_val(body, &evs2, loc, early)?;
        let ty = inner.ty().clone();
        Some(Self::bind(Self::returning(thunk, ty), inner, threaded))
    }

    /// A direct clause behind the operation's parameters: its body with the
    /// resume stripped, threaded through the enclosing scope's evidence when it
    /// performs a fused operation there. A clause is a bare function, so it
    /// cannot answer the enclosing scope's abort.
    pub(super) fn direct_clause(
        &mut self,
        clause: &TypedHandleOp,
        outer: &BTreeMap<Sym, Sym>,
        loc: &Loc,
        done: Option<&Type>,
    ) -> Option<TypedComp> {
        let aliases = BTreeSet::from([clause.resume().name()]);
        let stripped = strip_resume(clause.body(), &aliases, self.drift)?;
        // The performer binds the operation's declared result, so a unit-valued
        // operation whose clause resumes with something else resumes with a
        // value no perform site can read: an earlier rewrite of the clause's own
        // control flow left it dead. Bind it and answer with unit, which the
        // operation's type says is the whole answer.
        let unit = CoreType::Source(Type::Unit);
        let declared = value_scheme(self.env.operation(clause.name())?, clause.instantiation())?.2;
        let stripped = if declared == unit && stripped.sig().result() != &unit {
            let v = TypedBinder::new(self.mint("v"), stripped.sig().result().clone());
            Self::bind(stripped, v, Self::returning(unit_value(), unit))
        } else {
            stripped
        };
        let outer_ops: BTreeSet<Sym> = outer.keys().copied().collect();
        // A clause that leaves through a further-out abort answers with that
        // scope's step, so it threads early and every perform site of the
        // operation guards, exactly as a perform site of the abort does.
        let aborts = self.can_abort(&stripped, loc);
        if aborts && !self.plan.widen {
            return self.bail(format!(
                "a clause of `{}` whose body aborts",
                clause.name().as_str()
            ));
        }
        let body = if produces(&stripped, loc, &outer_ops, self.latent, self.flow) || aborts {
            self.thread_val(&stripped, outer, loc, aborts)?
        } else {
            self.rewrite(&stripped, loc, outer)?
        };
        // An operation stepped by another handler's abort is stepped here too:
        // the answer this clause resumes with is the step's `SMore`.
        let done = if aborts { None } else { done };
        let body = match done {
            Some(done) => {
                let step = StepAt::new(source_type(body.sig().result()).ok()?, done.clone());
                let v = TypedBinder::new(self.mint("v"), body.sig().result().clone());
                let more = Self::returning(step.smore(binder_var(&v)), step.ty());
                Self::bind(body, v, more)
            }
            None => body,
        };
        let params = self.clause_binders(clause.params());
        // An arm the entry point's own handler carries is at the operation's
        // scheme, so its clause stays generic where an elaborated arm's is
        // instantiated and every perform site applies it at its own arguments.
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

    /// `\(params) -> return SDone(payload)`: an abort clause hands its
    /// arguments to the handle site and nothing else.
    fn abort_clause(&mut self, clause: &TypedHandleOp, done: &Type) -> Option<TypedComp> {
        let sig = self.env.operation(clause.name())?;
        let (quantifiers, _, result) = value_scheme(sig, clause.instantiation())?;
        let step = StepAt::new(source_type(&result).ok()?, done.clone());
        let payload = payload_value(clause.params())?;
        let params = self.clause_binders(clause.params());
        let body = Self::returning(step.sdone(payload), step.ty());
        Some(Self::lam_quantified(quantifiers, params, body))
    }

    /// The done arm of a handle site: the abort arm's parameters bound from
    /// the payload.
    fn payload_arm(
        &mut self,
        step: &StepAt,
        params: &[TypedBinder],
        body: TypedComp,
    ) -> (TypedPattern, TypedComp) {
        match params {
            [] => {
                let w = TypedBinder::new(self.mint("_w"), CoreType::Source(Type::Unit));
                (step.done_pattern(w), body)
            }
            [p] => (step.done_pattern(p.clone()), body),
            _ => {
                let t = TypedBinder::new(self.mint("t"), CoreType::Source(step.done.clone()));
                let fields = params.iter().cloned().map(Some).collect();
                let unpack = TypedComp::new(
                    body.sig().clone(),
                    TypedCompKind::Case(binder_var(&t), vec![(TypedPattern::Tuple(fields), body)]),
                );
                (step.done_pattern(t), unpack)
            }
        }
    }

    /// `case sv of SMore(x) => tn | SDone(d) => return SDone(d)`: the head's
    /// value continues, its payload becomes this scope's answer.
    fn value_guard(
        &mut self,
        step: &StepAt,
        sv: &TypedBinder,
        x: TypedBinder,
        tn: TypedComp,
    ) -> Option<TypedComp> {
        let scope = StepAt::of(tn.sig().result())?;
        let d = TypedBinder::new(self.mint("d"), CoreType::Source(step.done.clone()));
        let reraise = Self::returning(scope.sdone(binder_var(&d)), scope.ty());
        Some(TypedComp::new(
            tn.sig().clone(),
            TypedCompKind::Case(
                binder_var(sv),
                vec![(step.more_pattern(x), tn), (step.done_pattern(d), reraise)],
            ),
        ))
    }

    /// Lift a head into the scope's step convention: a head that cannot abort,
    /// in a scope that can, has its value wrapped as `SMore`.
    fn lift(&mut self, c: TypedComp, early: bool, aborts: bool) -> Option<TypedComp> {
        if !early || aborts {
            return Some(c);
        }
        // A head whose answer already steps over this scope's done payload
        // forwards the abort itself, so its value is not wrapped again.
        if StepAt::of(c.sig().result()).is_some_and(|at| Some(&at.done) == self.done().as_ref()) {
            return Some(c);
        }
        let step = StepAt::new(source_type(c.sig().result()).ok()?, self.done()?);
        let v = TypedBinder::new(self.mint("v"), c.sig().result().clone());
        let more = Self::returning(step.smore(binder_var(&v)), step.ty());
        Some(Self::bind(c, v, more))
    }

    /// Whether running `c` can perform the abort live in this scope, either by
    /// performing it or by handing it through a handle that does not answer it.
    fn can_abort(&self, c: &TypedComp, loc: &Loc) -> bool {
        self.abort.as_ref().is_some_and(|(op, _)| {
            let raising = self.escaping_row(c, self.plan.raising(*op));
            produces(c, loc, &raising, self.latent, self.flow)
        }) || self.passes_abort(c, loc)
    }

    /// The operations among `ops` that can leave `c`: a computation performs
    /// nothing outside its row, so an operation it handles inside is not one
    /// its callers see, however latent the callee is in it. A row with an
    /// open tail may still hide any of them.
    fn escaping_row(&self, c: &TypedComp, ops: BTreeSet<Sym>) -> BTreeSet<Sym> {
        let row = c.sig().effects();
        if !matches!(row.tail(), EffRow::Empty) {
            return ops;
        }
        let labels = row.label_names();
        ops.into_iter()
            .filter(|op| {
                self.env
                    .operation(*op)
                    .is_none_or(|sig| labels.contains(&sig.effect().name))
            })
            .collect()
    }

    /// Whether a handle hands this scope's abort onward: its body performs an
    /// operation that raises the abort and this handle does not stop it. A
    /// handle stops an operation only by naming it in a clause that does not
    /// itself leave through the abort; a clause that does answers by aborting,
    /// so the abort escapes the handle and its answer is a step.
    pub(super) fn passes_abort(&self, c: &TypedComp, loc: &Loc) -> bool {
        let TypedCompKind::Handle {
            body, ops: clauses, ..
        } = c.kind()
        else {
            return false;
        };
        self.plan.widen
            && self.abort.as_ref().is_some_and(|(abort, _)| {
                let escaping: BTreeSet<Sym> = self
                    .plan
                    .raising(*abort)
                    .into_iter()
                    .filter(|op| {
                        clauses
                            .arms()
                            .iter()
                            .find(|arm| arm.name() == *op)
                            .is_none_or(|arm| self.clause_leaves(arm, loc))
                    })
                    .collect();
                let escaping = self.escaping_row(body, escaping);
                !escaping.is_empty() && produces(body, loc, &escaping, self.latent, self.flow)
            })
    }

    /// Whether a clause's body leaves through the abort live here. Its resume
    /// stripped, the body is a plain computation of the enclosing scope, so
    /// it leaves exactly where a head of that scope would; a body that never
    /// resumes is that computation already, and one that cannot be stripped
    /// is not read at all and is taken to leave.
    pub(super) fn clause_leaves(&self, clause: &TypedHandleOp, loc: &Loc) -> bool {
        let resume = clause.resume().name();
        if !free_comp_vars(clause.body()).contains(&resume) {
            return self.can_abort(clause.body(), loc);
        }
        strip_resume(clause.body(), &BTreeSet::from([resume]), self.drift)
            .is_none_or(|stripped| self.can_abort(&stripped, loc))
    }

    /// Whether a head over `ops` aborts with this scope's abort (`Some(true)`),
    /// cannot abort (`Some(false)`), or aborts with another operation, whose
    /// payload this scope's result cannot carry (`None`).
    pub(super) fn head_aborts(&self, ops: &BTreeSet<Sym>) -> Option<bool> {
        self.plan
            .abort_in(ops)?
            .map_or(Some(false), |op| match &self.abort {
                Some((live, _)) if *live == op => Some(true),
                _ => None,
            })
    }

    /// The done type live in this scope.
    pub(super) fn done(&self) -> Option<Type> {
        self.abort.as_ref().map(|(_, done)| done.clone())
    }

    /// The type a transformer-valued head answers when its abort is deferred
    /// to the application: the same function, its body stepped.
    fn deferred_step(&self, ty: &CoreType) -> Option<CoreType> {
        let CoreType::Thunk(thunk) = ty else {
            return None;
        };
        let CoreType::Function(fun) = thunk.result() else {
            return None;
        };
        let step = StepAt::new(source_type(fun.body().result()).ok()?, self.done()?);
        let stepped = CoreFnSig::new(
            fun.quantifiers().to_vec(),
            fun.params().to_vec(),
            CompSig::new(step.ty(), fun.body().effects().clone()),
        );
        Some(CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(stepped)),
            thunk.effects().clone(),
        ))))
    }

    /// A binder follows the head it binds: a head the rewrite retyped retypes
    /// its binder and every read after it.
    fn follow(&mut self, x: &TypedBinder, ty: &CoreType) -> TypedBinder {
        if ty == x.ty() {
            x.clone()
        } else {
            self.retyped.insert(x.name(), ty.clone());
            TypedBinder::new(x.name(), ty.clone())
        }
    }

    /// A clause's binders: the operation's own, or one unit binder when the
    /// operation is nullary, since a clause is applied.
    pub(super) fn clause_binders(&mut self, params: &[TypedBinder]) -> Vec<TypedBinder> {
        if params.is_empty() {
            vec![TypedBinder::new(
                self.mint("_w"),
                CoreType::Source(Type::Unit),
            )]
        } else {
            params.to_vec()
        }
    }

    pub(super) fn value_evidence(&self, evs: &BTreeMap<Sym, Sym>, op: Sym) -> Option<TypedBinder> {
        let name = *evs.get(&op)?;
        let ty = if let Some(ty) = self.evidence_types.get(&name) {
            ty.clone()
        } else {
            let done = self
                .abort
                .as_ref()
                .filter(|(a, _)| self.plan.raises(*a, op))
                .map(|(_, d)| d);
            value_clause_type(op, done, &self.row, &[], self.env)?
        };
        Some(TypedBinder::new(name, ty))
    }

    fn value_evidence_args(
        &self,
        evs: &BTreeMap<Sym, Sym>,
        operations: &BTreeSet<Sym>,
    ) -> Option<Vec<TypedValue>> {
        let mut ordered: Vec<(i64, Sym)> = operations
            .iter()
            .map(|op| Some((self.ids.id(*op)?, *op)))
            .collect::<Option<_>>()?;
        ordered.sort_unstable();
        ordered
            .into_iter()
            .map(|(_, op)| Some(binder_var(&self.value_evidence(evs, op)?)))
            .collect()
    }

    /// Apply a value clause; the result is the clause's own, instantiated
    /// where the clause is still generic, at the perform's own arguments for
    /// exactly those quantifiers.
    pub(super) fn apply_value_clause(
        &self,
        ev: &TypedBinder,
        op: Sym,
        instantiation: &[CoreInstantiation],
        args: Vec<TypedValue>,
    ) -> Option<TypedComp> {
        let CoreType::Thunk(thunk) = ev.ty() else {
            return None;
        };
        let force = TypedComp::new(thunk.as_ref().clone(), TypedCompKind::Force(binder_var(ev)));
        let CoreType::Function(clause) = thunk.result() else {
            return None;
        };
        let (instantiation, body) = if clause.quantifiers().is_empty() {
            (Vec::new(), clause.body().clone())
        } else {
            // The clause stayed generic in exactly the scheme quantifiers it
            // still names; the perform site's arguments for those are its own.
            let scheme = self.env.operation(op)?.quantifiers();
            let kept: Vec<CoreInstantiation> = clause
                .quantifiers()
                .iter()
                .map(|q| {
                    let slot = scheme.iter().position(|p| p == q)?;
                    instantiation.get(slot).cloned()
                })
                .collect::<Option<_>>()?;
            let applied = instantiate_fn(clause, &kept).ok()?;
            (kept, applied.body().clone())
        };
        Some(TypedComp::new(
            body,
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation,
                args,
            },
        ))
    }

    /// The instantiation of a threaded producer at this site: the original
    /// arguments, then the done type when the callee aborts, and the ambient
    /// row at this site's residual joined with whatever the caller already
    /// passed for it, whether that variable was appended to the callee's
    /// scheme or is the declared tail the callee renamed. The evidence handed
    /// over runs at this site's row, so the callee's ambient must admit it
    /// even where the elaborator instantiated the tail minimally.
    pub(super) fn producer_instantiation(
        &self,
        sig: &CoreFnSig,
        instantiation: &[CoreInstantiation],
    ) -> Option<Vec<CoreInstantiation>> {
        let mut inst = self.residual_instantiation(instantiation);
        for q in sig.quantifiers().iter().skip(instantiation.len()) {
            inst.push(match q {
                CoreQuantifier::Type(name) if names::is_effect_param(name.as_str()) => {
                    CoreInstantiation::Type(self.effect_param(*name, instantiation))
                }
                CoreQuantifier::Type(_) => CoreInstantiation::Type(self.live_done()?),
                CoreQuantifier::Row(_) => {
                    CoreInstantiation::Row(self.gained_row(sig.body().effects()))
                }
            });
        }
        if let EffRow::Var(tail) = sig.body().effects().tail() {
            let slot = sig
                .quantifiers()
                .iter()
                .position(|q| matches!(q, CoreQuantifier::Row(name) if name == tail));
            if let Some(slot) = slot.filter(|slot| *slot < instantiation.len()) {
                inst[slot] =
                    CoreInstantiation::Row(self.widened(sig.body().effects(), &inst[slot]));
            }
        }
        Some(inst)
    }

    /// The row a handle's body runs at: the handle expression's residual
    /// joined with the enclosing scope's row. The evidence in scope came from
    /// handles further out and runs at their rows, and a producer called under
    /// this handle receives that evidence, so its ambient row must admit them.
    /// A nested handle never narrows the row its scope established.
    pub(super) fn handle_row(&mut self, c: &TypedComp) -> Option<EffRow> {
        let residual = residual_row(c.sig().effects(), &self.plan.ops, self.env);
        match union_rows(&residual, &self.row) {
            Ok(row) => Some(row),
            Err(why) => self.bail(format!(
                "a handle at a row its scope's row does not join ({why})"
            )),
        }
    }

    /// The evidence map a handle's body threads under: each clause's
    /// operation bound to the evidence this handle provides for it. That is
    /// the canonical `ev@<id>` the producers expect, unless the scope already
    /// binds evidence under that name: a handle's binders join the one
    /// sequence its function lowers to, so reusing a name the scope holds
    /// would capture every later reference the scope makes to its own
    /// evidence, and such a handle binds a fresh name instead.
    ///
    /// A handle whose operation the scope carries no evidence for is the
    /// origin of that operation's evidence: nothing outside it performs the
    /// operation, so no enclosing binder answers it. It takes the canonical
    /// name, which is exactly what a producer called under it expects.
    pub(super) fn handle_evidence(
        &mut self,
        evs: &BTreeMap<Sym, Sym>,
        clauses: &TypedHandler,
    ) -> Option<BTreeMap<Sym, Sym>> {
        let mut out = evs.clone();
        for clause in clauses.arms() {
            let canonical = if let Some(canonical) = evs.get(&clause.name()).copied() {
                canonical
            } else {
                let id = self
                    .plan
                    .widen
                    .then(|| self.ids.id(clause.name()))
                    .flatten();
                let Some(name) = id.map(|id| Sym::from(prism_syntax::names::ev(id))) else {
                    return self.bail(format!(
                        "a handle of `{}`, for which this scope holds no evidence",
                        clause.name().as_str()
                    ));
                };
                out.insert(clause.name(), name);
                name
            };
            if self.evidence_types.contains_key(&canonical) {
                out.insert(clause.name(), self.mint("ev"));
            }
        }
        Some(out)
    }

    /// A row argument for the tail of `position` joined with this site's row:
    /// the union of the position at that argument with the site's row, less
    /// the labels the position spells before its tail, so a label the
    /// position already names is not counted twice. The site's row alone
    /// when the open tails disagree.
    pub(super) fn widened(&self, position: &EffRow, argument: &CoreInstantiation) -> EffRow {
        let CoreInstantiation::Row(row) = argument else {
            return self.row.clone();
        };
        // The argument is an ordinary row and may spell labels of its own before
        // its tail, so the position's labels extend that row rather than standing
        // over it whole; a canonical row is built over a terminal tail.
        let full = EffRow::canonical(
            position.labels().into_iter().chain(row.labels()).cloned(),
            row.tail().clone(),
        );
        let joined = union_rows(&full, &self.row).unwrap_or_else(|_| self.row.clone());
        position
            .labels()
            .into_iter()
            .fold(joined, |row, label| subtract_row(&row, label.name))
    }

    /// The row a quantifier the threading appended stands for at this site:
    /// the site's row less the labels `position` spells before its tail. A
    /// producer's row keeps its declared residual labels ahead of the
    /// ambient, and instantiating the ambient at the whole site row would
    /// spell each of them twice.
    pub(super) fn gained_row(&self, position: &EffRow) -> EffRow {
        position
            .labels()
            .into_iter()
            .fold(self.row.clone(), |row, label| {
                subtract_row(&row, label.name)
            })
    }

    /// The type a synthesized effect-parameter quantifier stands for at this
    /// site: the argument a row this edge instantiates spells for the effect
    /// at that position, and the quantifier itself when none does, so a
    /// generic caller hands its own through.
    pub(super) fn effect_param(&self, name: Sym, instantiation: &[CoreInstantiation]) -> Type {
        let effect = names::effect_param_slot(name.as_str()).and_then(|(id, index)| {
            let op = self.ids.op(id)?;
            Some((self.env.operation(op)?.effect().name, index))
        });
        effect
            .and_then(|(effect, index)| {
                instantiation.iter().find_map(|argument| match argument {
                    CoreInstantiation::Row(row) => label_args(row, effect).get(index).cloned(),
                    CoreInstantiation::Type(_) => None,
                })
            })
            .unwrap_or(Type::Var(name))
    }

    /// The evidence a value-threaded escaping thunk gains at `row`, and the
    /// abort its body threads under.
    pub(super) fn value_thunk_params(
        &mut self,
        source_fun: &CoreFnSig,
        carried_evs: &BTreeMap<Sym, Sym>,
        numbered: &[i64],
        row: &EffRow,
    ) -> Option<(Vec<TypedBinder>, BTreeMap<Sym, Sym>, Abort)> {
        let carried: BTreeSet<Sym> = carried_evs.keys().copied().collect();
        let abort = value_abort(self.plan, &carried, numbered)?;
        let mut params = Vec::new();
        let mut evs2 = BTreeMap::new();
        for (id, op) in self.ordered(carried_evs)? {
            let inst = self.label_inst(source_fun, op);
            let done = abort
                .as_ref()
                .filter(|(a, _)| self.plan.raises(*a, op))
                .map(|(_, d)| d);
            let binder = TypedBinder::new(
                Sym::from(prism_syntax::names::ev(id)),
                value_clause_type(op, done, row, &inst, self.env)?,
            );
            evs2.insert(op, binder.name());
            self.evidence_types
                .insert(binder.name(), binder.ty().clone());
            params.push(binder);
        }
        Some((params, evs2, abort))
    }

    pub(super) const fn returning(v: TypedValue, ty: CoreType) -> TypedComp {
        TypedComp::new(CompSig::new(ty, EffRow::Empty), TypedCompKind::Return(v))
    }

    pub(super) fn lam_quantified(
        quantifiers: Vec<CoreQuantifier>,
        params: Vec<TypedBinder>,
        body: TypedComp,
    ) -> TypedComp {
        let sig = CoreFnSig::new(
            quantifiers,
            params.iter().map(|p| p.ty().clone()).collect(),
            body.sig().clone(),
        );
        TypedComp::new(
            CompSig::new(CoreType::Function(Box::new(sig)), EffRow::Empty),
            TypedCompKind::Lam(params, Box::new(body)),
        )
    }
}
