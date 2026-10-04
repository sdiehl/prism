//! Rewriting outside the active accumulator-threading path.

use super::super::super::super::traverse::{free_comp_vars, free_value_vars};
use super::super::super::abi;
use super::super::super::checks::kind_name;
use super::super::super::{binder_var, peel, union_effects, walk};
use super::super::judgment::{judge_handle, HandleClass};
use super::super::program::stripped_type;
use super::super::reify::residual_type;
use super::super::retype::{graft_arrow, innermost};
use super::super::{op_list, Channel};
use super::{
    accumulator_type, body_folds, carrier_ops, clause_type, core_subtype, flow,
    instantiate_constructor, instantiate_fn, label_instantiation, mem, names, on_core_stack,
    residual_row, tail_kind, thunk_row, union_rows, unit_value, value_clause_type, widen_argument,
    widen_buried, widen_stored, BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreInstantiation,
    CoreQuantifier, CoreType, EffRow, FoldAKind, Loc, Sig, Sym, Threader, Type, TypedBinder,
    TypedComp, TypedCompKind, TypedPattern, TypedValue, TypedValueKind, STATE_ACC,
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
    /// A rewritten call's instantiation: every row argument loses one
    /// occurrence of each fused label, exactly as every threaded signature's
    /// rows did, so a row the caller once passed for a thunk that performed
    /// the operation now describes the thunk that carries its evidence.
    pub(in super::super) fn residual_instantiation(
        &self,
        instantiation: &[CoreInstantiation],
    ) -> Vec<CoreInstantiation> {
        instantiation
            .iter()
            .map(|argument| match argument {
                CoreInstantiation::Row(row) => {
                    CoreInstantiation::Row(residual_row(row, &self.plan.ops, self.env))
                }
                argument @ CoreInstantiation::Type(_) => argument.clone(),
            })
            .collect()
    }

    /// A call's instantiation with the row tailing every fused position of the
    /// callee joined with this scope's row: the thunks the callee receives or
    /// returns run their evidence here, so the tail that types them must admit
    /// this row even where the elaborator instantiated it minimally. A fused
    /// position is a thunk parameter or result the flow carries a fused
    /// operation through.
    pub(in super::super) fn fused_instantiation(
        &self,
        callee: Sym,
        sig: &CoreFnSig,
        instantiation: &[CoreInstantiation],
    ) -> Vec<CoreInstantiation> {
        let mut inst = self.residual_instantiation(instantiation);
        let carries =
            |s: Option<&Sig>| s.is_some_and(|s| s.iter().any(|m| self.plan.ops.contains(&m.id)));
        let mut positions: Vec<&CoreType> = Vec::new();
        if carries(self.flow.ret.get(&callee)) {
            positions.push(sig.body().result());
        }
        if let Some(params) = self.flow.param.get(&callee) {
            positions.extend(
                sig.params()
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| carries(params.get(*i)))
                    .map(|(_, ty)| ty),
            );
        }
        for ty in positions {
            let Some(row) = thunk_row(ty) else {
                continue;
            };
            let EffRow::Var(tail) = row.tail() else {
                continue;
            };
            let slot = sig
                .quantifiers()
                .iter()
                .position(|q| matches!(q, CoreQuantifier::Row(name) if name == tail));
            if let Some(slot) = slot.filter(|slot| *slot < inst.len()) {
                inst[slot] = CoreInstantiation::Row(self.widened(row, &inst[slot]));
            }
        }
        inst
    }

    /// `instantiation` extended to the quantifiers the threading added, or
    /// `None` when it already covers them or the scope cannot say what they
    /// stand for. The added ones come last and in one order, so filling them is
    /// positional: a type is the payload this scope's aborts carry, a row is
    /// the residual the call runs under.
    fn gained_instantiation(
        &self,
        sig: &CoreFnSig,
        instantiation: &[CoreInstantiation],
    ) -> Option<Vec<CoreInstantiation>> {
        let gained = sig.quantifiers().get(instantiation.len()..)?;
        if gained.is_empty() {
            return None;
        }
        let mut inst = instantiation.to_vec();
        for q in gained {
            inst.push(match q {
                CoreQuantifier::Type(name) if names::is_effect_param(name.as_str()) => {
                    CoreInstantiation::Type(self.effect_param(*name, instantiation))
                }
                CoreQuantifier::Type(_) => CoreInstantiation::Type(self.done()?),
                CoreQuantifier::Row(_) => {
                    CoreInstantiation::Row(self.gained_row(sig.body().effects()))
                }
            });
        }
        Some(inst)
    }

    /// A bind's head rewritten with its receiver in view. A lambda the head
    /// returns and the tail hands straight to calls with known signatures
    /// runs at the row those calls' parameters expect, exactly as it would
    /// were it written in argument position; one the tail reads any other
    /// way, or hands to receivers that disagree, is rewritten without one.
    pub(in super::super) fn rewrite_head(
        &mut self,
        m: &TypedComp,
        x: &TypedBinder,
        n: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedComp> {
        let TypedCompKind::Return(v) = m.kind() else {
            return self.rewrite(m, loc, evs);
        };
        let lambda = matches!(&peel(innermost(v)).kind, TypedValueKind::Thunk(c) if matches!(c.kind(), TypedCompKind::Lam(..)));
        let expected = lambda.then(|| self.receiver_row(x, n)).flatten();
        let stored = expected.as_ref().is_some_and(|receiver| receiver.stored);
        // A carrier bound for a store is read at the row its position
        // declares, so the operations it must accept come from that position
        // rather than from the flow, which never followed it into the data. A
        // lambda performing none of them still takes their evidence: the force
        // site hands it what the position promised, used or not.
        let forced = expected
            .as_ref()
            .map(|receiver| receiver.carried.clone())
            .unwrap_or_default();
        let returning = mem::replace(&mut self.returning, stored);
        let v2 = self.rewrite_value_forced(v, loc, evs, expected.as_ref().map(|r| &r.row), &forced);
        self.returning = returning;
        let v2 = v2?;
        Some(TypedComp::new(
            CompSig::new(v2.ty().clone(), m.sig().effects().clone()),
            TypedCompKind::Return(v2),
        ))
    }

    /// The row every receiver of `binder` in `n` expects of it, when `n`
    /// reads the binder only as a direct argument of calls whose callees'
    /// signatures are known, or only as a carrier stored in data, and those
    /// positions agree.
    fn receiver_row(&self, binder: &TypedBinder, n: &TypedComp) -> Option<Receiver> {
        let mut rows = Vec::new();
        self.receivers(binder, n, &mut rows);
        let mut rows = rows.into_iter();
        let first = rows.next()??;
        rows.all(|row| row.as_ref() == Some(&first))
            .then_some(first)
    }

    /// One entry per read of `binder` in `c`: the receiving parameter's row
    /// for a direct call argument, the widened row for a carrier stored in
    /// data, `None` for any other read.
    fn receivers(&self, binder: &TypedBinder, c: &TypedComp, out: &mut Vec<Option<Receiver>>) {
        let name = binder.name();
        let reads = |v: &TypedValue| free_value_vars(v).contains(&name);
        match c.kind() {
            TypedCompKind::Bind(m, x, n) => {
                // A binder returned as is names the same value: its alias's
                // receivers are its own.
                let alias = matches!(m.kind(), TypedCompKind::Return(v)
                    if self.wrapped(v).is_none()
                        && matches!(&peel(v).kind, TypedValueKind::Var { name: read, .. } if *read == name));
                if alias {
                    self.receivers(x, n, out);
                } else {
                    self.receivers(binder, m, out);
                }
                if x.name() != name {
                    self.receivers(binder, n, out);
                }
            }
            TypedCompKind::If(v, t, e) => {
                out.extend(reads(v).then_some(None));
                self.receivers(binder, t, out);
                self.receivers(binder, e, out);
            }
            TypedCompKind::Case(v, arms) => {
                out.extend(reads(v).then_some(None));
                for (_, b) in arms {
                    self.receivers(binder, b, out);
                }
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                let applied = self.signatures.get(callee).and_then(|sig| {
                    let inst = self.fused_instantiation(*callee, sig, instantiation);
                    instantiate_fn(sig, &inst).ok()
                });
                for (i, a) in args.iter().enumerate() {
                    if !reads(a) {
                        continue;
                    }
                    // A read under a lowered bridge is handed to the parameter
                    // as directly as a bare one: the bridge follows the
                    // lambda it carries.
                    let direct = matches!(&peel(innermost(a)).kind, TypedValueKind::Var { name: read, .. } if *read == name);
                    out.push(
                        direct
                            .then(|| {
                                let param = applied.as_ref()?.params().get(i)?;
                                Some(Receiver::call(
                                    thunk_row(param)?.clone(),
                                    self.param_carried(*callee, i),
                                ))
                            })
                            .flatten(),
                    );
                }
            }
            // A lambda the scope returns reads the binder where its body
            // does: a resumption handed on to a call inside the clause's
            // lambda has that call's parameter as its receiver.
            TypedCompKind::Return(v) if reads(v) => match &peel(v).kind {
                TypedValueKind::Thunk(c) => match c.kind() {
                    TypedCompKind::Lam(ps, b) if ps.iter().all(|p| p.name() != name) => {
                        self.receivers(binder, b, out);
                    }
                    _ => out.push(None),
                },
                _ if is_data(v) || self.wrapped(v).is_some() => {
                    let declared = self
                        .stored_position(v, name)
                        .unwrap_or_else(|| binder.ty().clone());
                    let carried = carrier_ops(&declared, self.plan, self.env);
                    out.push(
                        self.stored_row(&declared)
                            .map(|row| Receiver::stored(row, carried)),
                    );
                }
                _ => out.push(None),
            },
            _ => out.extend(free_comp_vars(c).contains(&name).then_some(None)),
        }
    }

    /// The fused operations the flow saw a callee's parameter perform: the
    /// ones the parameter was widened to take evidence for, so what an
    /// argument standing there takes, performed or not.
    fn param_carried(&self, callee: Sym, i: usize) -> BTreeSet<Sym> {
        if self
            .cells
            .get(&callee)
            .is_some_and(|positions| positions.contains(&i))
        {
            return BTreeSet::new();
        }
        self.flow
            .param
            .get(&callee)
            .and_then(|params| params.get(i))
            .map(|sig| {
                sig.iter()
                    .map(|masked| masked.id)
                    .filter(|op| self.plan.ops.contains(op))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The type the position holding `name` in a stored value declares.
    ///
    /// A constructor's scheme is the authority over the type its argument
    /// happens to have where it was built: carriers stored in one field are
    /// read back at one type however their builders were spelled, and only the
    /// scheme says which. A tuple declares nothing beyond its components, so
    /// there the value's own type is already the answer.
    fn stored_position(&self, v: &TypedValue, name: Sym) -> Option<CoreType> {
        if let Some((ctor, instantiation, inner)) = self.wrapped(v) {
            let holds = matches!(&peel(inner).kind, TypedValueKind::Var { name: read, .. } if *read == name);
            return if holds {
                self.field_types(ctor, instantiation)?.pop().flatten()
            } else {
                self.stored_position(inner, name)
            };
        }
        let TypedValueKind::Ctor {
            name: ctor,
            instantiation,
            fields,
            ..
        } = &peel(v).kind
        else {
            return None;
        };
        let holds = |f: &TypedValue| matches!(&peel(f).kind, TypedValueKind::Var { name: read, .. } if *read == name);
        match fields.iter().position(holds) {
            Some(index) => self.field_types(*ctor, instantiation)?.remove(index),
            None => fields
                .iter()
                .find(|f| free_value_vars(f).contains(&name))
                .and_then(|f| self.stored_position(f, name)),
        }
    }

    /// A newtype coercion that wraps its operand, as the constructor, its
    /// instantiation, and the operand: the coercion whose type is the
    /// constructor's result. The other direction reads the field back.
    fn wrapped<'v>(
        &self,
        v: &'v TypedValue,
    ) -> Option<(Sym, &'v [CoreInstantiation], &'v TypedValue)> {
        let TypedValueKind::NewtypeRepr {
            constructor,
            instantiation,
            value,
        } = &v.kind
        else {
            return None;
        };
        let declared = self.declared.constructor(*constructor)?;
        let mono = instantiate_constructor(declared, instantiation).ok()?;
        (mono.result == *v.ty()).then_some((*constructor, instantiation.as_slice(), value))
    }

    /// What each field of a constructor declares, from the constructor's own
    /// scheme as the program declared it, instantiated at the arguments the
    /// value stands at as the program spelled them. A field is answered at
    /// its declared type, which is what says which operations the position
    /// carries; its stored convention is the widening of that, applied once
    /// by whoever reads the answer, and the pattern that reads a field back
    /// and the store that builds it agree on it. A field the scheme declares
    /// as a type argument is answered unwidened like any other: widened
    /// here, its row would no longer name what it carries, and the store
    /// would read a carrier as a value that takes no evidence.
    ///
    /// A field is left without an answer when its type cannot be widened, a
    /// buried arrow at a bare row among them: the store falls back to the
    /// value's own type there, as the read side leaves the binder alone.
    fn field_types(
        &self,
        ctor: Sym,
        instantiation: &[CoreInstantiation],
    ) -> Option<Vec<Option<CoreType>>> {
        let declared = self.declared.constructor(ctor)?;
        let read = instantiate_constructor(declared, instantiation).ok()?;
        Some(
            read.fields
                .into_iter()
                .map(|field| {
                    widen_stored(&field, self.plan, self.ids, self.env)
                        .is_ok()
                        .then_some(field)
                })
                .collect(),
        )
    }

    /// The row a carrier stored in data runs at: the one its widened position
    /// declares. A store is not a call, so no callee names the convention; the
    /// widening of the carrier's own type is the whole of it, and the force
    /// site reads the carrier back under exactly that.
    fn stored_row(&self, ty: &CoreType) -> Option<EffRow> {
        let target = widen_stored(ty, self.plan, self.ids, self.env).ok()?;
        if target == *ty {
            return None;
        }
        let CoreType::Thunk(inner) = &target else {
            return None;
        };
        let CoreType::Function(function) = inner.result() else {
            return None;
        };
        Some(function.body().effects().clone())
    }

    pub(in super::super) fn rewrite_value(
        &mut self,
        v: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedValue> {
        self.rewrite_value_to(v, loc, evs, None)
    }

    /// Rewrite a call's arguments against the callee's widened parameters.
    ///
    /// The callee's own parameter is the authority for what an argument must
    /// be, and the two can genuinely disagree: a carrier stored at a position
    /// whose row names a label carries a clause for that label, while a
    /// receiver whose row is a bare variable names none and keeps the generic
    /// clause. Neither side is wrong on its own, so the disagreement is a
    /// decline of this program rather than Core the verifier will reject.
    pub(in super::super) fn call_args(
        &mut self,
        args: &[TypedValue],
        applied: Option<&CoreFnSig>,
        callee: Option<Sym>,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<Vec<TypedValue>> {
        let mut out = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            let want = applied.and_then(|applied| applied.params().get(i)).cloned();
            let forced = callee.map_or_else(BTreeSet::new, |callee| self.param_carried(callee, i));
            let a =
                self.rewrite_value_forced(a, loc, evs, want.as_ref().and_then(thunk_row), &forced)?;
            if let Some(want) = &want {
                self.accepts(&a, want)?;
            }
            out.push(a);
        }
        Some(out)
    }

    /// The half of [`call_args`](Self::call_args) that only judges, for the
    /// sites that settle the callee's instantiation after rewriting the
    /// arguments.
    pub(in super::super) fn accepts(&mut self, a: &TypedValue, want: &CoreType) -> Option<()> {
        if core_subtype(a.ty(), want) {
            return Some(());
        }
        self.bail(format!(
            "an argument the callee's parameter does not accept ({} at {})",
            a.ty(),
            want
        ))
    }

    /// [`rewrite_value`](Self::rewrite_value) with the row a receiver expects
    /// of an escaping thunk in view: the receiving parameter's, when the value
    /// is an argument of a call whose callee's signature is known.
    pub(in super::super) fn rewrite_value_to(
        &mut self,
        v: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
        expected: Option<&EffRow>,
    ) -> Option<TypedValue> {
        self.rewrite_value_forced(v, loc, evs, expected, &BTreeSet::new())
    }

    /// [`rewrite_value_to`](Self::rewrite_value_to) with the carried operations
    /// settled in advance rather than read off the flow.
    ///
    /// A stored carrier is one the flow never followed, so the flow has no
    /// answer for it and the widened type of its position is the whole of the
    /// convention. That includes a lambda performing nothing at all: it still
    /// takes the evidence parameter its position declares, and simply never
    /// uses it.
    fn rewrite_value_forced(
        &mut self,
        v: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
        expected: Option<&EffRow>,
        forced: &BTreeSet<Sym>,
    ) -> Option<TypedValue> {
        // A lambda under a lowered bridge is threaded where it stands and
        // bridged again onto the target its new arrow spells: the bridge
        // changes what the closure answers with, never what it is applied to.
        if let TypedValueKind::LoweredRepr { value, proof } = &v.kind {
            let value2 = self.rewrite_value_forced(value, loc, evs, expected, forced)?;
            let target = graft_arrow(v.ty(), innermost(value).ty(), innermost(&value2).ty());
            if !proof.validates(value2.ty(), &target) {
                return self.bail("a threaded lambda the lowered bridge does not carry");
            }
            return Some(TypedValue::new(
                target,
                TypedValueKind::LoweredRepr {
                    value: Box::new(value2),
                    proof: proof.clone(),
                },
            ));
        }
        let ops: BTreeSet<Sym> = evs.keys().copied().collect();
        let returning = mem::take(&mut self.returning);
        // What the lambda performs, and what its receiver's position
        // promises evidence for whether or not it is performed.
        let carried: BTreeSet<Sym> = flow::value_sig_in(v, loc, self.latent, self.flow)
            .into_iter()
            .map(|masked| masked.id)
            .chain(forced.iter().copied())
            .filter(|operation| ops.contains(operation))
            .collect();
        Some(match &peel(v).kind {
            TypedValueKind::Thunk(c) => match c.kind() {
                TypedCompKind::Lam(ps, b) if !carried.is_empty() => {
                    let CoreType::Function(source_fun) = c.sig().result() else {
                        return self.bail("a lambda whose type is not a function");
                    };
                    let carried_evs: BTreeMap<Sym, Sym> = evs
                        .iter()
                        .filter(|(operation, _)| carried.contains(operation))
                        .map(|(operation, evidence)| (*operation, *evidence))
                        .collect();
                    let numbered = self.numbered(&carried_evs)?;
                    let ambient = Sym::from(names::evidence_row(&numbered));

                    let mut loc2 = loc.clone();
                    for p in ps {
                        loc2.insert(p.name(), Sig::new());
                    }
                    let mut ps2 = ps.clone();
                    // The thunk's own scheme remains in force after threading.
                    // State (or the done type) and the ambient residual are
                    // appended inside that scheme; replacing its quantifiers
                    // would make the value disagree with `threaded_thunk_type`
                    // at every direct call.
                    let mut quantifiers = source_fun.quantifiers().to_vec();
                    // The thunk's body runs under the row its own type
                    // declares (the ambient variable the state channel binds
                    // inside it, the expected residual on the value channel),
                    // and everything threaded inside it (evidence rows, call
                    // instantiations, the scope's one Step decision) must
                    // agree on that. Every piece of context is restored even
                    // when the threading declines, so a `?` cannot leak it;
                    // the evidence types in particular, because the thunk's
                    // own evidence binders shadow the scope's by name.
                    let saved_evidence = self.evidence_types.clone();
                    // The thunk's body sees the scope's whole evidence map
                    // with the thunk's own binders on top: a thunk nested
                    // inside performs what it performs whether or not this
                    // scope holds the evidence, and names its own parameter
                    // by the operation's id.
                    let threaded = (|| match self.plan.channel(&carried)? {
                        // A reified operation crosses no thunk parameter: the
                        // cell its performer answers with is what carries it.
                        Channel::Reified => None,
                        Channel::State
                            if abi::answers_with_effect_cell(source_fun.body().result()) =>
                        {
                            self.bail("a cells thunk carrying a state accumulator")
                        }
                        Channel::State => {
                            // The thunk runs at the row its receiver expects,
                            // or at its own residual joined with the enclosing
                            // scope's when no receiver is in view, as on the
                            // value channel. The value a declaration returns
                            // binds the ambient its declared result row ends
                            // in when that ambient is the thunk's own.
                            let own =
                                residual_row(source_fun.body().effects(), &self.plan.ops, self.env);
                            let (row, fresh) = match expected {
                                Some(row) => (
                                    row.clone(),
                                    returning
                                        .then_some(ambient)
                                        .filter(|ambient| {
                                            matches!(row.tail(), EffRow::Var(tail) if tail == ambient)
                                        })
                                        .filter(|ambient| self.scheme_row != Some(*ambient)),
                                ),
                                None => (union_rows(&self.row, &own).ok()?, None),
                            };
                            let threading = accumulator_type(self.plan, &carried, &numbered)?;
                            let acc_ty = threading.ty;
                            let done = threading.step.as_ref().map(|at| &at.done);
                            let st = TypedBinder::new(Sym::from(STATE_ACC), acc_ty.clone());
                            let mut evs2 = evs.clone();
                            for (id, op) in self.ordered(&carried_evs)? {
                                let inst = self.label_inst(source_fun, op);
                                let ty = if self.plan.value_shaped(op) {
                                    value_clause_type(op, done, &row, &inst, self.env)?
                                } else {
                                    clause_type(
                                        op,
                                        &acc_ty,
                                        done.filter(|_| self.plan.stops(op)),
                                        &row,
                                        &inst,
                                        self.env,
                                        self.plan.paired(op),
                                    )?
                                };
                                let binder = TypedBinder::new(Sym::from(names::ev(id)), ty);
                                evs2.insert(op, binder.name());
                                self.evidence_types
                                    .insert(binder.name(), binder.ty().clone());
                                ps2.push(binder);
                            }
                            ps2.push(st.clone());
                            quantifiers.extend(threading.state.map(CoreQuantifier::Type));
                            quantifiers.extend(threading.done.map(CoreQuantifier::Type));
                            let saved_row = mem::replace(&mut self.row, row.clone());
                            let saved_step = mem::replace(&mut self.step, threading.step);
                            let threaded = self.thread_st(b, &evs2, &loc2, &st);
                            self.row = saved_row;
                            self.step = saved_step;
                            quantifiers.extend(fresh.map(CoreQuantifier::Row));
                            // The lambda runs at the row its evidence binds,
                            // whether or not its body performs anything
                            // through it: a stored carrier is read back at
                            // that row, and a body performing nothing still
                            // has to meet it.
                            let threaded = threaded?;
                            let Ok(row) = union_rows(threaded.sig().effects(), &row) else {
                                return self
                                    .bail("a threaded lambda whose body runs at another ambient");
                            };
                            Some((threaded, Some(row)))
                        }
                        Channel::Value => {
                            // The thunk runs at the row its receiver expects,
                            // or at its own residual joined with the enclosing
                            // scope's when no receiver is in view. The value a
                            // declaration returns runs at its declared result
                            // row, and binds the ambient that row ends in when
                            // the ambient is the thunk's own.
                            //
                            // A lambda answering with an effect cell is forced
                            // by a driver with nothing in hand, wherever it
                            // ends up: it reads the evidence of the scope that
                            // built it, so it runs at the row its cells were
                            // spelled at, which is that scope's row when it
                            // reads that scope's evidence, whatever its
                            // receiver's position spells; the analysis
                            // credits that scope with what it performs.
                            let cells = abi::answers_with_effect_cell(source_fun.body().result());
                            let own =
                                residual_row(source_fun.body().effects(), &self.plan.ops, self.env);
                            let (row, fresh) = if let Some(row) = expected.filter(|_| !cells) {
                                let binds = returning
                                    .then_some(ambient)
                                    .filter(|ambient| {
                                        matches!(row.tail(), EffRow::Var(tail) if tail == ambient)
                                    })
                                    .filter(|ambient| self.scheme_row != Some(*ambient));
                                (row.clone(), binds)
                            } else if cells {
                                (own, None)
                            } else {
                                (union_rows(&self.row, &own).ok()?, None)
                            };
                            // A receiving parameter hands evidence only for
                            // the operations it forces the lambda to carry.
                            // The rest the lambda performs are answered by the
                            // evidence in scope: the receiver forces it under
                            // the handlers this scope runs under, and an
                            // abort among them leaves through this scope's. A
                            // lambda handed back to a caller carries its own,
                            // since the caller's scope is not this one. A
                            // cells lambda carries none.
                            if cells && !forced.is_empty() {
                                return self.bail("a cells thunk at a position handing evidence");
                            }
                            let handed: BTreeMap<Sym, Sym> = carried_evs
                                .iter()
                                .filter(|(operation, _)| {
                                    !cells
                                        && (expected.is_none()
                                            || returning
                                            || forced.contains(operation))
                                })
                                .map(|(operation, evidence)| (*operation, *evidence))
                                .collect();
                            let numbered = self.numbered(&handed)?;
                            let (evidence, own, abort) =
                                self.value_thunk_params(source_fun, &handed, &numbered, &row)?;
                            let abort = abort.or_else(|| {
                                self.abort.clone().filter(|(operation, _)| {
                                    carried.contains(operation) && !handed.contains_key(operation)
                                })
                            });
                            let mut evs2 = evs.clone();
                            evs2.extend(own);
                            ps2.extend(evidence);
                            if let Some((_, Type::Var(done))) = &abort {
                                quantifiers.push(CoreQuantifier::Type(*done));
                            }
                            quantifiers.extend(fresh.map(CoreQuantifier::Row));
                            let saved_row = mem::replace(&mut self.row, row.clone());
                            let saved_abort = mem::replace(&mut self.abort, abort.clone());
                            let threaded = self.thread_val(b, &evs2, &loc2, abort.is_some());
                            self.row = saved_row;
                            self.abort = saved_abort;
                            Some((threaded?, Some(row)))
                        }
                    })();
                    self.evidence_types = saved_evidence;
                    let (body, lam_row) = threaded?;
                    let lam_row = lam_row.unwrap_or_else(|| body.sig().effects().clone());
                    let lam_sig = CoreFnSig::new(
                        quantifiers,
                        ps2.iter().map(|p| p.ty().clone()).collect(),
                        CompSig::new(body.sig().result().clone(), lam_row),
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
                // A lambda carrying nothing keeps its scheme, less the value
                // labels no handler is left for, and follows its body's result,
                // which a thunk it returns may have widened.
                TypedCompKind::Lam(ps, b) => {
                    let declared = CoreType::Thunk(Box::new(c.sig().clone()));
                    let declared = match widen_buried(&declared, self.plan, self.ids, self.env) {
                        Ok(declared) => declared,
                        Err(why) => return self.bail(why),
                    };
                    let CoreType::Thunk(stripped) = stripped_type(&declared, self.plan, self.env)
                    else {
                        return self.bail("a lambda whose stripped type is not a thunk");
                    };
                    let CoreType::Function(fun) = stripped.result() else {
                        return self.bail("a lambda whose stripped type is not a function");
                    };
                    // The body runs at the row the lambda declares, which may
                    // be narrower than the scope's: a call inside it is
                    // widened to that row and no further.
                    let saved_row = mem::replace(&mut self.row, fun.body().effects().clone());
                    let body = self.rewrite(b, loc, evs);
                    self.row = saved_row;
                    let body = body?;
                    let sig = CoreFnSig::new(
                        fun.quantifiers().to_vec(),
                        fun.params().to_vec(),
                        CompSig::new(body.sig().result().clone(), fun.body().effects().clone()),
                    );
                    let lam = TypedComp::new(
                        CompSig::new(
                            CoreType::Function(Box::new(sig)),
                            stripped.effects().clone(),
                        ),
                        TypedCompKind::Lam(ps.clone(), Box::new(body)),
                    );
                    TypedValue::new(
                        CoreType::Thunk(Box::new(lam.sig().clone())),
                        TypedValueKind::Thunk(Box::new(lam)),
                    )
                }
                _ if body_folds(c, &ops, self.latent) => {
                    return self.bail("a thunk that is not a lambda and whose body folds")
                }
                _ => {
                    let body = self.rewrite(c, loc, evs)?;
                    TypedValue::new(v.ty().clone(), TypedValueKind::Thunk(Box::new(body)))
                }
            },
            _ => self.rewrite_data(v, loc, evs)?,
        })
    }

    /// A value that is not a thunk, with every carrier it stores widened.
    ///
    /// Descent stops at anything but a product: a carrier reaches a force site
    /// only by being taken apart again, and every shape that can hold one and
    /// be taken apart is here.
    fn rewrite_data(
        &mut self,
        v: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedValue> {
        if !self.plan.widen {
            return Some(self.retyped.rebuild_through(v));
        }
        let stored = |this: &mut Self, fields: &[TypedValue]| {
            fields
                .iter()
                .map(|f| this.rewrite_stored(f, loc, evs, None))
                .collect::<Option<Vec<_>>>()
        };
        let kind = match &v.kind {
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => {
                let declared = self.field_types(*name, instantiation).unwrap_or_default();
                let widened = self.widened_instantiation(instantiation)?;
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| {
                        let at = declared.get(i).and_then(Option::as_ref);
                        self.rewrite_stored(f, loc, evs, at)
                    })
                    .collect::<Option<Vec<_>>>()?;
                TypedValueKind::Ctor {
                    name: *name,
                    tag: *tag,
                    instantiation: widened,
                    fields,
                }
            }
            TypedValueKind::Tuple(fields) => TypedValueKind::Tuple(stored(self, fields)?),
            TypedValueKind::UnboxedTuple(fields) => {
                TypedValueKind::UnboxedTuple(stored(self, fields)?)
            }
            TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, f)| Some((*name, self.rewrite_stored(f, loc, evs, None)?)))
                    .collect::<Option<Vec<_>>>()?,
            ),
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => return self.rewrite_newtype(v, *constructor, instantiation, value, loc, evs),
            _ => return Some(self.retyped.rebuild_through(v)),
        };
        match widen_stored(v.ty(), self.plan, self.ids, self.env) {
            Ok(ty) => Some(TypedValue::new(ty, kind)),
            Err(why) => self.bail(why),
        }
    }

    /// A newtype coercion, at the convention the constructor's one field is
    /// stored at.
    ///
    /// The field's scheme is the authority on both sides. Wrapping stores the
    /// operand as a constructor stores a field, so it is built to the widened
    /// field type. Unwrapping reads the field back at that same type, which
    /// the outer type of the coercion now spells; the operand is data and
    /// stands as its binder was retyped. A field that cannot be widened leaves
    /// the coercion as it was.
    fn rewrite_newtype(
        &mut self,
        v: &TypedValue,
        constructor: Sym,
        instantiation: &[CoreInstantiation],
        value: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedValue> {
        let Some(field) = self
            .field_types(constructor, instantiation)
            .and_then(|mut fields| fields.pop().flatten())
        else {
            return Some(self.retyped.rebuild_through(v));
        };
        let wrapping = self.wrapped(v).is_some();
        let widened = self.widened_instantiation(instantiation)?;
        let (value2, ty) = if wrapping {
            let value2 = self.rewrite_stored(value, loc, evs, Some(&field))?;
            let ty = match widen_stored(v.ty(), self.plan, self.ids, self.env) {
                Ok(ty) => ty,
                Err(why) => return self.bail(why),
            };
            (value2, ty)
        } else {
            let ty = match widen_stored(&field, self.plan, self.ids, self.env) {
                Ok(ty) => ty,
                Err(why) => return self.bail(why),
            };
            (self.retyped.rebuild_through(value), ty)
        };
        Some(TypedValue::new(
            ty,
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation: widened,
                value: Box::new(value2),
            },
        ))
    }

    /// A value stored in data, built to the widened type its position now has.
    ///
    /// Nothing threaded this position: the flow does not follow a thunk into a
    /// constructor, so the widening of the field's type is the whole of the
    /// convention and the value must be built to meet it. A carrier that is not
    /// a lambda has no body to thread, and declines rather than storing a value
    /// the force site would hand evidence it never took.
    fn rewrite_stored(
        &mut self,
        v: &TypedValue,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
        declared: Option<&CoreType>,
    ) -> Option<TypedValue> {
        let declared = declared.unwrap_or_else(|| v.ty());
        let target = match widen_stored(declared, self.plan, self.ids, self.env) {
            Ok(target) => target,
            Err(why) => return self.bail(why),
        };
        // A position still spelling a reified label holds a value the reified
        // rewrite typed without it: cells already, and nothing to thread.
        if target == *v.ty() || residual_type(&target, &self.reified, self.env) == *v.ty() {
            return self.rewrite_value(v, loc, evs);
        }
        // A carrier bound by a let was already rewritten where its binder was,
        // in this same convention; the store reads it at the type it now has.
        let rebuilt = self.retyped.rebuild_through(v);
        if *rebuilt.ty() == target {
            return Some(rebuilt);
        }
        let lambda = matches!(&peel(v).kind, TypedValueKind::Thunk(c)
            if matches!(c.kind(), TypedCompKind::Lam(..)));
        if !lambda {
            return self.bail("a stored carrier that is not a lambda");
        }
        let CoreType::Thunk(inner) = &target else {
            return self.bail("a widened carrier that is not a thunk");
        };
        let CoreType::Function(function) = inner.result() else {
            return self.bail("a widened carrier that is not a function");
        };
        let row = function.body().effects().clone();
        let forced = carrier_ops(declared, self.plan, self.env);
        let returning = mem::replace(&mut self.returning, true);
        let stored = self.rewrite_value_forced(v, loc, evs, Some(&row), &forced);
        self.returning = returning;
        let stored = stored?;
        if *stored.ty() == target {
            return Some(stored);
        }
        self.bail("a stored carrier the widening and the rewrite disagree on")
    }

    /// An instantiation whose type arguments are widened where they stand: a
    /// scheme argument naming a carrier names the widened one everywhere the
    /// constructor's fields do.
    fn widened_instantiation(
        &mut self,
        instantiation: &[CoreInstantiation],
    ) -> Option<Vec<CoreInstantiation>> {
        instantiation
            .iter()
            .map(|argument| match argument {
                CoreInstantiation::Type(ty) => {
                    match widen_argument(ty, self.plan, self.ids, self.env) {
                        Ok(ty) => Some(CoreInstantiation::Type(ty)),
                        Err(why) => self.bail(why),
                    }
                }
                argument @ CoreInstantiation::Row(_) => Some(argument.clone()),
            })
            .collect()
    }

    /// One match arm, threaded with its binders shadowing the enclosing scope.
    ///
    /// A name an arm binds is not the name an outer scope retyped, even when
    /// the two are spelled alike: the arm's binder has whatever type its
    /// scrutinee's constructor stored, and reading it at an outer local's
    /// threaded type would hand the verifier a witness for a different value.
    /// The shadowing lasts the arm and no longer.
    pub(in super::super) fn arm<R>(
        &mut self,
        p: &TypedPattern,
        body: impl FnOnce(&mut Self) -> Option<R>,
    ) -> Option<(TypedPattern, R)> {
        let mut saved = Vec::new();
        let mut p = p.clone();
        if self.plan.widen {
            self.widen_pattern(&mut p);
            let mut shadow = |this: &mut Self, b: &TypedBinder| {
                saved.push((b.name(), this.retyped.remove(b.name())));
            };
            match &p {
                TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
                    for b in fields.iter().flatten() {
                        shadow(self, b);
                    }
                }
                TypedPattern::Var(b) => shadow(self, b),
                TypedPattern::Wild => {}
            }
            self.record(&p);
        }
        let out = body(self);
        for (name, previous) in saved {
            self.retyped.restore(name, previous);
        }
        Some((p, out?))
    }

    /// A constructor pattern matched at the arguments the widened scrutinee
    /// now carries, with its field binders retyped from the constructor's own
    /// scheme. The scheme is the authority: a field the constructor spells
    /// itself is declared at its stored convention, and one it declares as an
    /// argument moves exactly as far as that argument did.
    fn widen_pattern(&self, p: &mut TypedPattern) {
        let TypedPattern::Ctor {
            name,
            instantiation,
            fields,
        } = p
        else {
            return;
        };
        let mut widened = instantiation.clone();
        for argument in &mut widened {
            let CoreInstantiation::Type(ty) = argument else {
                continue;
            };
            if let Ok(target) = widen_argument(ty, self.plan, self.ids, self.env) {
                *ty = target;
            }
        }
        let Some(declared) = self.env.constructor(*name) else {
            return;
        };
        let Ok(mono) = instantiate_constructor(declared, &widened) else {
            return;
        };
        for (index, binder) in fields.iter_mut().enumerate() {
            let (Some(binder), Some(ty)) = (binder.as_mut(), mono.fields.get(index)) else {
                continue;
            };
            *binder = TypedBinder::new(binder.name(), ty.clone());
        }
        *instantiation = widened;
    }

    /// Every binder a pattern introduces, at the type it now has, so that reads
    /// of it inside the arm rebuild there.
    fn record(&mut self, p: &TypedPattern) {
        let mut bound: Vec<TypedBinder> = Vec::new();
        match p {
            TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
                bound.extend(fields.iter().flatten().cloned());
            }
            TypedPattern::Var(b) => bound.push(b.clone()),
            TypedPattern::Wild => {}
        }
        for b in bound {
            self.retyped.insert(b.name(), b.ty().clone());
        }
    }

    /// A scrutinee read at whatever type its binder now has.
    pub(in super::super) fn scrutinee(&self, v: &TypedValue) -> TypedValue {
        if !self.plan.widen {
            return v.clone();
        }
        self.retyped.rebuild_through(v)
    }

    /// The fused operations paired with their ids, in ascending id order.
    /// The instantiation a lambda value's own effect label supplies for `op`.
    /// The lambda owns its function scheme, so its declared label names the
    /// clause arguments in that scheme's vocabulary; searching the body could
    /// instead find a forwarded callee's vocabulary, or no direct `Do` at all.
    pub(super) fn label_inst(&self, source_fun: &CoreFnSig, op: Sym) -> Vec<CoreInstantiation> {
        label_instantiation(source_fun.body().effects(), op, self.env)
    }

    pub(super) fn ordered(&self, evs: &BTreeMap<Sym, Sym>) -> Option<Vec<(i64, Sym)>> {
        let mut ordered: Vec<(i64, Sym)> = evs
            .keys()
            .map(|op| Some((self.ids.id(*op)?, *op)))
            .collect::<Option<_>>()?;
        ordered.sort_unstable();
        Some(ordered)
    }

    /// Rewrite a consumer body whose returned thunk the signature prepass
    /// threaded: the value the body ultimately returns is threaded to that
    /// declared row, which may bind the thunk's ambient inside its own type.
    pub(in super::super) fn rewrite_tail(
        &mut self,
        c: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
        row: &EffRow,
        forced: &BTreeSet<Sym>,
    ) -> Option<TypedComp> {
        Some(match c.kind() {
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.rewrite_head(m, x, n, loc, evs)?;
                let x2 = self.rebound(x, &m2);
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    flow::result_sig_in(m, loc, self.latent, self.flow),
                );
                let n2 = self.rewrite_tail(n, &loc2, evs, row, forced)?;
                Self::bind(m2, x2, n2)
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.rewrite_tail(t, loc, evs, row, forced)?;
                let e2 = self.rewrite_tail(e, loc, evs, row, forced)?;
                Self::branch(v, t2, e2)
            }
            TypedCompKind::Case(v, arms) => {
                let arms = arms
                    .iter()
                    .map(|(p, b)| self.arm(p, |this| this.rewrite_tail(b, loc, evs, row, forced)))
                    .collect::<Option<_>>()?;
                Self::cases(c, &self.scrutinee(v), arms)
            }
            // Every lambda the declaration returns takes the evidence its
            // declared result carries, used or not: a caller forces whichever
            // one it received with the same arguments.
            TypedCompKind::Return(v) => {
                self.returning = true;
                let v2 = self.rewrite_value_forced(v, loc, evs, Some(row), forced);
                self.returning = false;
                let v2 = v2?;
                TypedComp::new(
                    CompSig::new(v2.ty().clone(), c.sig().effects().clone()),
                    TypedCompKind::Return(v2),
                )
            }
            _ => self.rewrite(c, loc, evs)?,
        })
    }

    /// The binder of a head whose value the rewrite retyped (an escaping
    /// producer thunk gaining parameters) follows it, and so does every read
    /// of the binder after it.
    fn rebound(&mut self, x: &TypedBinder, head: &TypedComp) -> TypedBinder {
        if head.sig().result() == x.ty() {
            return x.clone();
        }
        self.retyped.insert(x.name(), head.sig().result().clone());
        TypedBinder::new(x.name(), head.sig().result().clone())
    }

    /// A branch's row is derived from its arms, as the verifier derives it: an
    /// arm whose fused call lost a label no longer contributes that label, and
    /// the pre-threading row would still name it.
    fn branch(v: &TypedValue, t: TypedComp, e: TypedComp) -> TypedComp {
        let result = Self::settled([&t, &e]).unwrap_or_else(|| t.sig().result().clone());
        let sig = CompSig::new(
            result.clone(),
            union_effects(t.sig().effects(), e.sig().effects()),
        );
        let t = Self::diverging_at(t, &result);
        let e = Self::diverging_at(e, &result);
        TypedComp::new(sig, TypedCompKind::If(v.clone(), Box::new(t), Box::new(e)))
    }

    fn cases(c: &TypedComp, v: &TypedValue, arms: Vec<(TypedPattern, TypedComp)>) -> TypedComp {
        let effects = arms.iter().fold(EffRow::Empty, |row, (_, b)| {
            union_effects(&row, b.sig().effects())
        });
        let result = Self::settled(arms.iter().map(|(_, b)| b)).unwrap_or_else(|| {
            arms.first().map_or_else(
                || c.sig().result().clone(),
                |(_, b)| b.sig().result().clone(),
            )
        });
        let arms = arms
            .into_iter()
            .map(|(p, b)| (p, Self::diverging_at(b, &result)))
            .collect();
        TypedComp::new(
            CompSig::new(result, effects),
            TypedCompKind::Case(v.clone(), arms),
        )
    }

    /// The result the branches that answer agree on, when any of them does:
    /// a branch that only raises answers at whatever type its siblings do.
    fn settled<'a>(branches: impl IntoIterator<Item = &'a TypedComp>) -> Option<CoreType> {
        branches
            .into_iter()
            .find(|b| !Self::diverges(b))
            .map(|b| b.sig().result().clone())
    }

    fn diverges(c: &TypedComp) -> bool {
        match c.kind() {
            TypedCompKind::Error(_) => true,
            TypedCompKind::Bind(_, _, n) => Self::diverges(n),
            _ => false,
        }
    }

    /// A branch that raises, read at the type the branches beside it settled
    /// on: the verifier reads a raise at any type, but the branches must agree.
    fn diverging_at(c: TypedComp, result: &CoreType) -> TypedComp {
        if !Self::diverges(&c) || c.sig().result() == result {
            return c;
        }
        let sig = CompSig::new(result.clone(), c.sig().effects().clone());
        match c.kind() {
            TypedCompKind::Bind(m, x, n) => TypedComp::new(
                sig,
                TypedCompKind::Bind(
                    m.clone(),
                    x.clone(),
                    Box::new(Self::diverging_at((**n).clone(), result)),
                ),
            ),
            TypedCompKind::Error(v) => TypedComp::new(sig, TypedCompKind::Error(v.clone())),
            _ => c,
        }
    }

    /// Rewrite a computation the accumulator does not thread through: it performs
    /// no fused operation, so only what it contains can need rewriting.
    pub(in super::super) fn rewrite(
        &mut self,
        c: &TypedComp,
        loc: &Loc,
        evs: &BTreeMap<Sym, Sym>,
    ) -> Option<TypedComp> {
        // A bind spine is rewritten a node at a time, so the recursion is as deep
        // as the program's longest sequence; grow stack segments inside it, the
        // same discipline the shared descent keeps.
        let out = on_core_stack(|| self.rewrite_on_core_stack(c, loc, evs));
        self.dropped(c, out)
    }

    fn rewrite_on_core_stack(
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
            TypedCompKind::Handle { .. } => {
                let judged = match judge_handle(c, self.latent, self.plan.widen, self.plan.reify) {
                    Ok(judged) => judged,
                    Err(why) => return self.bail(why),
                };
                let handled: BTreeSet<Sym> = judged.arms.iter().map(|(op, _)| *op).collect();
                let Some(channel) = self.plan.channel(&handled) else {
                    return self.bail(format!(
                        "a handle over operations {} that share no channel",
                        op_list(&handled)
                    ));
                };
                match (judged.class, channel) {
                    (HandleClass::Fold { abort, .. }, Channel::State) => {
                        self.lower_fold(c, evs, loc, abort)?
                    }
                    (HandleClass::Direct { abort: None }, Channel::State) => {
                        self.lower_consumer(c, evs, loc)?
                    }
                    (HandleClass::Direct { abort }, Channel::Value) => {
                        self.lower_direct(c, evs, loc, abort)?
                    }
                    (HandleClass::Forward, Channel::Value) => self.value_forward(c, evs, loc)?,
                    (class, channel) => {
                        let class = match class {
                            HandleClass::Fold { .. } => "fold",
                            HandleClass::Take => "take",
                            HandleClass::Forward => "forwarding",
                            HandleClass::Direct { abort: None } => "direct",
                            HandleClass::Direct { .. } => "aborting",
                            HandleClass::Reified => "reifying",
                        };
                        let channel = match channel {
                            Channel::State => "state",
                            Channel::Value => "value",
                            Channel::Reified => "reified",
                        };
                        return self.bail(format!("a {class} handler on the {channel} channel"));
                    }
                }
            }
            // A perform outside the threading path is still a call of its
            // evidence, but only where the operation wanted no accumulator in
            // the first place: a value-channel clause takes the operation's own
            // arguments and nothing else. A state-channel operation reaching
            // here is one the threading missed, and answering it without an
            // accumulator would build a call its own clause does not accept. An
            // abort is refused for the neighbouring reason: its answer is a
            // step, and there is no step at this position to lift it into.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } if evs.contains_key(operation)
                && self.plan.value_shaped(*operation)
                && self.head_aborts(&BTreeSet::from([*operation])) == Some(false) =>
            {
                let ev = self.value_evidence(evs, *operation)?;
                let mut a: Vec<TypedValue> = args
                    .iter()
                    .map(|arg| self.rewrite_value(arg, loc, evs))
                    .collect::<Option<_>>()?;
                if a.is_empty() {
                    a.push(unit_value());
                }
                self.apply_value_clause(&ev, *operation, instantiation, a)?
            }
            TypedCompKind::Do { operation, .. } => {
                return self.bail(format!("`{}` performed by a consumer", operation.as_str()))
            }
            TypedCompKind::Mask(..) => return self.bail("a mask"),
            TypedCompKind::Bind(m, x, n) => {
                let m2 = self.rewrite_head(m, x, n, loc, evs)?;
                let x2 = self.rebound(x, &m2);
                let mut loc2 = loc.clone();
                loc2.insert(
                    x.name(),
                    flow::result_sig_in(m, loc, self.latent, self.flow),
                );
                let n2 = self.rewrite(n, &loc2, evs)?;
                Self::bind(m2, x2, n2)
            }
            TypedCompKind::If(v, t, e) => {
                let t2 = self.rewrite(t, loc, evs)?;
                let e2 = self.rewrite(e, loc, evs)?;
                Self::branch(v, t2, e2)
            }
            TypedCompKind::Case(v, arms) => {
                let arms = arms
                    .iter()
                    .map(|(p, b)| self.arm(p, |this| this.rewrite(b, loc, evs)))
                    .collect::<Option<_>>()?;
                Self::cases(c, &self.scrutinee(v), arms)
            }
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
                let instantiation = self.signatures.get(callee).map_or_else(
                    || self.residual_instantiation(instantiation),
                    |new_sig| self.fused_instantiation(*callee, new_sig, instantiation),
                );
                // A callee planned as a producer gained quantifiers its callers
                // never wrote: the payload it can abort with and the row it runs
                // under. Every reference instantiates them, this one included,
                // whether or not the call sits where the scope produces.
                let instantiation = self
                    .signatures
                    .get(callee)
                    .cloned()
                    .and_then(|new_sig| self.gained_instantiation(&new_sig, &instantiation))
                    .unwrap_or(instantiation);
                let applied = self.signatures.get(callee).map(|new_sig| {
                    instantiate_fn(new_sig, &instantiation).unwrap_or_else(|_| new_sig.clone())
                });
                let sig = applied
                    .as_ref()
                    .map_or_else(|| c.sig().clone(), |applied| applied.body().clone());
                let args = self.call_args(args, applied.as_ref(), Some(*callee), loc, evs)?;
                TypedComp::new(
                    sig,
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation,
                        args,
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
                    return self.bail("an application whose callee is not a function");
                };
                let instantiation = self.residual_instantiation(instantiation);
                let Ok(applied) = instantiate_fn(fun, &instantiation) else {
                    return self.bail("an application whose callee does not instantiate");
                };
                // The exact, fallible union: a non-representable union of two
                // open tails is a State decline, never permission to drop one.
                let Ok(effects) = union_rows(callee2.sig().effects(), applied.body().effects())
                else {
                    return self.bail("an application whose rows do not union");
                };
                let sig = CompSig::new(applied.body().result().clone(), effects);
                let args = self.call_args(args, Some(&applied), None, loc, evs)?;
                TypedComp::new(
                    sig,
                    TypedCompKind::App {
                        callee: Box::new(callee2),
                        instantiation,
                        args,
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
            _ if self.carries_producer(c, loc, evs) => {
                return self.bail(format!(
                    "a {} carrying a producer thunk",
                    kind_name(c.kind())
                ))
            }
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
            found |= flow::value_sig_in(v, loc, self.latent, self.flow)
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
        } else if self.plan.value_shaped(op) {
            // An abort threaded beside the accumulator keeps the value
            // channel's clause, so its type is built the value channel's way.
            value_clause_type(op, self.live_done().as_ref(), &self.row, &[], self.env)?
        } else {
            clause_type(
                op,
                acc,
                self.live_done().filter(|_| self.plan.stops(op)).as_ref(),
                &self.row.clone(),
                &[],
                self.env,
                self.plan.paired(op),
            )?
        };
        Some(TypedBinder::new(name, ty))
    }

    /// Apply an operation's clause to its arguments and the accumulator.
    pub(super) fn apply_clause(
        ev: &TypedBinder,
        instantiation: &[CoreInstantiation],
        args: Vec<TypedValue>,
        st: &TypedBinder,
        paired: bool,
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
        // An unpaired clause answers with the accumulator it was handed, which
        // is what the threading names it by. A paired one answers with the pair
        // its own signature declares, read from that signature at this site's
        // instantiation rather than rebuilt here.
        let result = if paired {
            let applied = if clause.quantifiers().is_empty() {
                clause.as_ref().clone()
            } else {
                instantiate_fn(clause, &instantiation).ok()?
            };
            applied.body().result().clone()
        } else {
            st.ty().clone()
        };
        Some(TypedComp::new(
            CompSig::new(result, clause.body().effects().clone()),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation,
                args,
            },
        ))
    }

    /// [`Self::apply_clause`] where the caller already knows what the clause
    /// answers: a stopping arm's is the payload its fold stops with, which the
    /// scope names rather than reads back off the accumulator.
    pub(super) fn apply_clause_at(
        ev: &TypedBinder,
        instantiation: &[CoreInstantiation],
        args: Vec<TypedValue>,
        result: CoreType,
    ) -> Option<TypedComp> {
        let CoreType::Thunk(thunk) = ev.ty() else {
            return None;
        };
        let force = TypedComp::new(thunk.as_ref().clone(), TypedCompKind::Force(binder_var(ev)));
        let CoreType::Function(clause) = thunk.result() else {
            return None;
        };
        let instantiation = if clause.quantifiers().is_empty() {
            Vec::new()
        } else {
            instantiation.to_vec()
        };
        Some(TypedComp::new(
            CompSig::new(result, clause.body().effects().clone()),
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
        tail_kind(m, loc, &ops, &self.plan.kinds, self.latent, self.flow)
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

    /// [`Self::bind`] under the rule that makes its union well formed. Two
    /// distinct open tails have no union: a bind reaching for one is a call to
    /// a consumer that kept its own declared residual beside this scope's
    /// ambient. The scope refuses it here rather than building a term whose row
    /// only a widening could type and leaving a later guard to notice.
    pub(super) fn bound(
        &mut self,
        head: TypedComp,
        binder: TypedBinder,
        tail: TypedComp,
    ) -> Option<TypedComp> {
        if let (EffRow::Var(ambient), EffRow::Var(other)) =
            (head.sig().effects().tail(), tail.sig().effects().tail())
        {
            if ambient != other {
                return self
                    .bail("a consumer called where its residual row is not this scope's ambient");
            }
        }
        Some(Self::bind(head, binder, tail))
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

/// What one read of a let-bound carrier expects of it: the row, and whether
/// the read is a store into data rather than a call argument. A stored carrier
/// binds the ambient its widened row ends in, exactly as a returned one does.
#[derive(Clone, PartialEq, Eq)]
pub(super) struct Receiver {
    row: EffRow,
    stored: bool,
    carried: BTreeSet<Sym>,
}

impl Receiver {
    const fn call(row: EffRow, carried: BTreeSet<Sym>) -> Self {
        Self {
            row,
            stored: false,
            carried,
        }
    }

    const fn stored(row: EffRow, carried: BTreeSet<Sym>) -> Self {
        Self {
            row,
            stored: true,
            carried,
        }
    }
}

/// Whether this value is a product a carrier can be stored in.
fn is_data(v: &TypedValue) -> bool {
    matches!(
        &peel(v).kind,
        TypedValueKind::Ctor { .. }
            | TypedValueKind::Tuple(_)
            | TypedValueKind::UnboxedTuple(_)
            | TypedValueKind::UnboxedRecord(_)
    )
}
