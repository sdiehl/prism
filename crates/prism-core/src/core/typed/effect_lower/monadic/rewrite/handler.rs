//! Handler capture analysis and free-monad driver construction.

use super::{
    abi, forced_var, free_comp_vars, free_value_vars, function_applied_once_tail, names,
    state_clause, state_return, union_effects, walk, BTreeSet, Builtin, CompSig, CoreFnSig, CoreOp,
    CoreType, EffRow, Effects, FnAnswerLowering, FreeMonadDriver, Monadic, Refusal,
    ResumeRepresentation, Site, Sym, Type, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
    TypedValue, TypedValueKind, EBIND,
};

impl<'a> Monadic<'a> {
    pub(super) fn handler_is_open(&self, comp: &TypedComp) -> bool {
        match (self.region_plan, self.effects()) {
            (Some(plan), Some(effects)) => plan.handler_is_open(comp, effects, &self.thunk_sigs),
            _ => true,
        }
    }

    /// The two effect maps a planning question needs, when this builder was
    /// configured with a region to consult.
    fn effects(&self) -> Option<Effects<'a>> {
        Some(Effects {
            latent: self.latent?,
            flow: self.flow?,
        })
    }

    fn rewrite_function_answer_use(
        &mut self,
        comp: &TypedComp,
        aliases: &BTreeSet<Sym>,
        region: Sym,
        initial: &TypedBinder,
        captures: &[TypedBinder],
    ) -> Option<TypedComp> {
        match comp.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = forced_var(callee)?;
                let [argument] = args.as_slice() else {
                    return None;
                };
                if !instantiation.is_empty() || !aliases.contains(&callee) {
                    return None;
                }
                let mut call_args = vec![
                    Self::var(initial.name(), initial.ty().clone()),
                    self.value(argument)?,
                ];
                call_args.extend(
                    captures
                        .iter()
                        .map(|capture| Self::var(capture.name(), capture.ty().clone())),
                );
                self.call(region, call_args)
            }
            TypedCompKind::Bind(head, binder, tail) => {
                if let TypedCompKind::Return(value) = head.kind() {
                    if let TypedValueKind::Var {
                        name,
                        instantiation,
                    } = &value.kind
                    {
                        if instantiation.is_empty() && aliases.contains(name) {
                            let mut extended = aliases.clone();
                            extended.insert(binder.name());
                            return self.rewrite_function_answer_use(
                                tail, &extended, region, initial, captures,
                            );
                        }
                    }
                }
                if !free_comp_vars(head).is_disjoint(aliases) {
                    return None;
                }
                let lowered = self.direct(head)?;
                let rest = self.with_source_binders(std::slice::from_ref(binder), |this| {
                    this.rewrite_function_answer_use(tail, aliases, region, initial, captures)
                })?;
                Some(TypedComp::new(
                    rest.sig().clone(),
                    TypedCompKind::Bind(Box::new(lowered), binder.clone(), Box::new(rest)),
                ))
            }
            _ => None,
        }
    }

    pub(super) fn try_handle_native_function_answer(
        &mut self,
        comp: &TypedComp,
        function: &TypedBinder,
        continuation: &TypedComp,
    ) -> Option<FnAnswerLowering> {
        // A cleanup clause has no lowered form, so a handler carrying one
        // declines here and stays on the interpreted path.
        let TypedCompKind::Handle {
            body,
            return_binder: Some(return_binder),
            return_body,
            finally_body: None,
            ops,
        } = comp.kind()
        else {
            return Some(FnAnswerLowering::Declined);
        };
        let (Some(plan), Some(effects)) = (self.region_plan, self.effects()) else {
            return Some(FnAnswerLowering::Declined);
        };
        if !plan.native_closed(comp, effects, &self.thunk_sigs, self.native_enabled)
            || function.ty() != comp.sig().result()
        {
            return Some(FnAnswerLowering::Declined);
        }
        let Some((return_state, return_tail)) = state_return(return_body.as_deref()) else {
            return Some(FnAnswerLowering::Declined);
        };
        let Some(clauses) = ops
            .arms()
            .iter()
            .map(state_clause)
            .collect::<Option<Vec<_>>>()
        else {
            return Some(FnAnswerLowering::Declined);
        };
        if !function_applied_once_tail(continuation, function.name())
            || clauses.iter().any(|clause| {
                clause.state.ty() != return_state.ty()
                    || clause.next_state.ty() != return_state.ty()
            })
        {
            return Some(FnAnswerLowering::Declined);
        }

        let captures = self.handler_captures(comp)?;
        let region = self.mint_driver(FreeMonadDriver::Region);
        let accumulator = TypedBinder::new(self.mint("acc"), return_state.ty().clone());
        let mut region_params = vec![abi::eff(self.row.clone()), accumulator.ty().clone()];
        region_params.extend(captures.iter().map(|capture| capture.ty().clone()));
        let region_signature = CoreFnSig::new(
            self.quantifiers.clone(),
            region_params,
            CompSig::new(return_tail.sig().result().clone(), self.row.clone()),
        );
        self.generated_signatures
            .insert(region, region_signature.clone());

        let pure_value = TypedBinder::new(self.mint("x"), abi::word());
        let mut pure_scope = captures.clone();
        pure_scope.push(return_binder.clone());
        pure_scope.push(return_state.clone());
        let return_tail =
            self.with_source_binders(&pure_scope, |this| this.direct(&return_tail))?;
        let bind_state = TypedComp::new(
            return_tail.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(accumulator.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(Self::var(accumulator.name(), accumulator.ty().clone())),
                )),
                return_state,
                Box::new(return_tail),
            ),
        );
        let pure_body = TypedComp::new(
            bind_state.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(return_binder.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(abi::lowered_repr(
                        Self::var(pure_value.name(), pure_value.ty().clone()),
                        return_binder.ty().clone(),
                    )),
                )),
                return_binder.clone(),
                Box::new(bind_state),
            ),
        );
        let pure_arm = (abi::epure_pattern(self.row.clone(), pure_value), pure_body);

        let id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
        let skip = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
        let argument = TypedBinder::new(self.mint("arg"), abi::word());
        let queue = TypedBinder::new(self.mint("k"), abi::queue(self.row.clone()));
        let mut dispatch = TypedComp::new(
            region_signature.body().clone(),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str("ICE: unhandled effect op in closed native handler".into()),
            )),
        );
        for ((operation, clause), operation_id) in ops
            .arms()
            .iter()
            .zip(clauses.iter())
            .zip(
                ops.arms()
                    .iter()
                    .map(|operation| self.ops.id(operation.name())),
            )
            .rev()
        {
            let operation_id = operation_id?;
            let applied = TypedBinder::new(self.mint("qa"), abi::eff(self.row.clone()));
            let mut scope = captures.clone();
            scope.extend(operation.params().iter().cloned());
            scope.push(clause.state.clone());
            scope.extend(clause.prefix.iter().map(|(_, binder)| binder.clone()));
            let branch = self.with_source_binders(&scope, |this| {
                let qapply = abi::qapply(
                    Self::var(queue.name(), queue.ty().clone()),
                    this.word(&clause.resumed)?,
                    this.row.clone(),
                );
                let mut region_args = vec![
                    Self::var(applied.name(), applied.ty().clone()),
                    this.value(&clause.next_state)?,
                ];
                region_args.extend(
                    captures
                        .iter()
                        .map(|capture| Self::var(capture.name(), capture.ty().clone())),
                );
                let redrive = this.call(region, region_args)?;
                let mut branch = TypedComp::new(
                    redrive.sig().clone(),
                    TypedCompKind::Bind(Box::new(qapply), applied.clone(), Box::new(redrive)),
                );
                for (prefix, binder) in clause.prefix.iter().rev() {
                    let prefix = this.direct(prefix)?;
                    branch = TypedComp::new(
                        branch.sig().clone(),
                        TypedCompKind::Bind(Box::new(prefix), binder.clone(), Box::new(branch)),
                    );
                }
                let bind_state = TypedComp::new(
                    branch.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(TypedComp::new(
                            CompSig::new(accumulator.ty().clone(), EffRow::Empty),
                            TypedCompKind::Return(Self::var(
                                accumulator.name(),
                                accumulator.ty().clone(),
                            )),
                        )),
                        clause.state.clone(),
                        Box::new(branch),
                    ),
                );
                Self::bind_operation_params(operation.params(), &argument, bind_state)
            })?;
            let matched = TypedBinder::new(self.mint("t"), CoreType::Source(Type::Bool));
            let is_operation = TypedComp::new(
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
                TypedCompKind::Prim(
                    CoreOp::Eq,
                    Self::var(id.name(), id.ty().clone()),
                    TypedValue::new(
                        CoreType::Source(Type::Int),
                        TypedValueKind::Int(operation_id),
                    ),
                ),
            );
            let selected = TypedComp::new(
                dispatch.sig().clone(),
                TypedCompKind::If(
                    Self::var(matched.name(), matched.ty().clone()),
                    Box::new(branch),
                    Box::new(dispatch),
                ),
            );
            dispatch = TypedComp::new(
                selected.sig().clone(),
                TypedCompKind::Bind(Box::new(is_operation), matched, Box::new(selected)),
            );
        }
        let operation_arm = (
            abi::eop_pattern(self.row.clone(), id, skip, argument, queue),
            dispatch,
        );
        let current = TypedBinder::new(self.mint("cur"), abi::eff(self.row.clone()));
        let region_body = TypedComp::new(
            region_signature.body().clone(),
            TypedCompKind::Case(
                Self::var(current.name(), current.ty().clone()),
                vec![pure_arm, operation_arm],
            ),
        );
        let mut parameters = vec![current, accumulator];
        parameters.extend(captures.iter().cloned());
        self.generated.push(TypedCoreFn::new(
            region,
            parameters,
            region_body,
            region_signature,
            0,
        ));

        let initial = TypedBinder::new(self.mint("r0"), abi::eff(self.row.clone()));
        let aliases = BTreeSet::from([function.name()]);
        let driven =
            self.rewrite_function_answer_use(continuation, &aliases, region, &initial, &captures)?;
        let body = self.comp(body)?;
        Some(FnAnswerLowering::Lowered(Box::new(TypedComp::new(
            driven.sig().clone(),
            TypedCompKind::Bind(Box::new(body), initial, Box::new(driven)),
        ))))
    }

    /// Whether any immediate value position of a computation writes material
    /// the region owns: a thunk it lowered, or a capture of the continuation a
    /// handler clause resumes through.
    pub(super) fn holds_monadic_thunk(&self, comp: &TypedComp) -> bool {
        let mut found = false;
        walk::each_value(comp, &mut |value| {
            found = found || self.produces_monadic_thunk(value) || self.captures_resume(value);
        });
        found
    }

    /// Refuse when a value the rewrite is about to copy verbatim closes over
    /// the continuation a handler clause resumes through.
    fn check_verbatim_capture(&mut self, value: &TypedValue) -> Option<()> {
        if self.captures_resume(value) {
            return self.refuse(Refusal::ThunkBoundary, Self::value_site(value));
        }
        Some(())
    }

    /// Whether a value written into direct code closes over the continuation a
    /// handler clause resumes through.
    ///
    /// A resume alias stands for the monadic continuation the handler driver
    /// threads, so a direct value holding one stores a binder of the region's
    /// own shape where the direct convention describes a source function. The
    /// flow solution cannot report this: a continuation performs whatever the
    /// action it resumes performs, which no latent set of the clause names, so
    /// the builder is the only place that knows the value crossed the boundary.
    fn captures_resume(&self, value: &TypedValue) -> bool {
        !self.resume_aliases.is_empty() && !free_value_vars(value).is_disjoint(&self.resume_aliases)
    }

    /// Whether any of these names is a binder the transform reified into a
    /// runtime word. Every use of one reads back as `Lowered(Word)`, so a
    /// source-typed mention of it that no crossing reaches contradicts the
    /// binder in scope. A binder already written at the word representation is
    /// not one of them: nothing about it moved.
    pub(super) fn reads_reified_binder(&self, names: &BTreeSet<Sym>) -> bool {
        !self.word_binders.is_empty()
            && names.iter().any(|name| {
                self.word_binders
                    .get(name)
                    .is_some_and(|ty| ty != &abi::word())
            })
    }

    /// A value handed to direct code unchanged.
    ///
    /// A reference standing on its own crosses back through the word
    /// representation here, which is the whole of what a residual argument
    /// needs. A mention buried anywhere else, inside a thunk the region leaves
    /// at the direct convention or under a constructor, has no crossing to
    /// stand in: the copy is verbatim, so it would read the reified binder at
    /// its source type where the word is what is in scope. The rewrite that
    /// would fix such a mention is a rewrite of the direct body, which is
    /// exactly what confinement promises not to do, so the region refuses and
    /// the whole-program lowering below it takes the declaration instead.
    pub(super) fn verbatim(&mut self, value: &TypedValue) -> Option<TypedValue> {
        self.check_verbatim_capture(value)?;
        // The crossing is written for an uninstantiated reference, which is
        // what a local ever is; a reference carrying witnesses falls through to
        // the check below rather than being copied without one.
        if let TypedValueKind::Var { instantiation, .. } = &value.kind {
            if instantiation.is_empty() {
                return Some(self.word_reference(value));
            }
        }
        if self.reads_reified_binder(&free_value_vars(value)) {
            return self.refuse(Refusal::WordCapture, Self::value_site(value));
        }
        Some(value.clone())
    }

    /// A value produced by a direct-convention computation. The identity unless
    /// it is a thunk the region owns, which is rewritten here and then retagged
    /// back to its source type so that no enclosing node's signature moves.
    pub(super) fn direct_value(&mut self, value: &TypedValue) -> Option<TypedValue> {
        if !self.produces_monadic_thunk(value) {
            return self.verbatim(value);
        }
        self.check_verbatim_capture(value)?;
        // The suspended body performs what it performs regardless of the row
        // its builder sits at, so the monadic material inside it is written
        // under the suspension row and the direct rewrite around it keeps the
        // declaration's own. The retag below restores the source type, so the
        // choice stays private to the thunk.
        let outer = std::mem::replace(&mut self.row, self.suspension_row.clone());
        let rewritten = self.value(value);
        self.row = outer;
        Self::retag_runtime_word(rewritten?, value.ty().clone())
    }

    // An argument of a residual App/Call/Force. A thunk the region owns is
    // built at the monadic convention, exactly as in a returned position;
    // everything else only crosses the word representation described below.
    pub(super) fn direct_argument(&mut self, argument: &TypedValue) -> Option<TypedValue> {
        if self.produces_monadic_thunk(argument) {
            return self.direct_value(argument);
        }
        self.verbatim(argument)
    }

    // A source binder the monadic transform reified into a Word continuation
    // parameter reads back as `Lowered(Word)`; a residual App/Call/Force that
    // still references it must cross back through the word representation, or the
    // reference type contradicts the word-typed binder. Non-word references pass
    // through untouched. Row/representation-only, so erased Core is unchanged.
    fn word_reference(&self, argument: &TypedValue) -> TypedValue {
        if let TypedValueKind::Var {
            name,
            instantiation,
        } = &argument.kind
        {
            if instantiation.is_empty() && self.word_binders.contains_key(name) {
                return abi::lowered_repr(Self::var(*name, abi::word()), argument.ty().clone());
            }
        }
        argument.clone()
    }

    // Re-instantiating a direct row-polymorphic callee at the monadic answer
    // row substitutes through its higher-order parameters too. Keep direct
    // values structurally unchanged, but retag their exact runtime-word
    // representation to the instantiated parameter witness.
    pub(super) fn direct_argument_at(
        &mut self,
        argument: &TypedValue,
        expected: &CoreType,
    ) -> Option<TypedValue> {
        let argument = self.direct_argument(argument)?;
        Self::retag_runtime_word(argument, expected.clone())
    }

    fn handler_captures(&self, comp: &TypedComp) -> Option<Vec<TypedBinder>> {
        let TypedCompKind::Handle {
            return_binder,
            return_body,
            ops,
            ..
        } = comp.kind()
        else {
            return None;
        };
        let mut free = BTreeSet::new();
        if let (Some(binder), Some(return_body)) = (return_binder, return_body) {
            let mut return_free = free_comp_vars(return_body);
            return_free.remove(&binder.name());
            free.extend(return_free);
        }
        for operation in ops.arms() {
            let mut operation_free = free_comp_vars(operation.body());
            for parameter in operation.params() {
                operation_free.remove(&parameter.name());
            }
            operation_free.remove(&operation.resume().name());
            free.extend(operation_free);
        }
        let mut free: Vec<Sym> = free.into_iter().collect();
        free.sort_by(|left, right| left.as_str().cmp(right.as_str()));
        free.into_iter()
            .map(|name| Some(TypedBinder::new(name, self.locals.get(&name)?.clone())))
            .collect()
    }

    pub(super) fn native_eligible(&self, comp: &TypedComp) -> bool {
        let TypedCompKind::Handle {
            return_binder,
            return_body,
            ..
        } = comp.kind()
        else {
            return false;
        };
        if return_binder.is_some() != return_body.is_some() {
            return false;
        }
        let (Some(plan), Some(effects)) = (self.region_plan, self.effects()) else {
            return false;
        };
        plan.native_eligible(comp, effects, &self.thunk_sigs, self.native_enabled)
    }

    pub(super) fn handle_native(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            finally_body: None,
            ops,
        } = comp.kind()
        else {
            return None;
        };
        if return_binder.is_some() != return_body.is_some() || ops.arms().is_empty() {
            return None;
        }
        let result_ty = comp.sig().result().clone();
        let captures = self.handler_captures(comp)?;
        let region = self.mint_driver(FreeMonadDriver::Region);
        let mut region_params = vec![abi::eff(self.row.clone())];
        region_params.extend(captures.iter().map(|capture| capture.ty().clone()));
        let region_signature = CoreFnSig::new(
            self.quantifiers.clone(),
            region_params,
            CompSig::new(result_ty.clone(), self.row.clone()),
        );
        self.generated_signatures
            .insert(region, region_signature.clone());

        let mut clauses = Vec::with_capacity(ops.arms().len());
        for operation in ops.arms() {
            let clause = self.mint("clause");
            let argument = TypedBinder::new(self.mint("arg"), abi::word());
            let resume = TypedBinder::new(self.mint("res"), abi::queue(self.row.clone()));
            let mut scope = captures.clone();
            scope.extend(operation.params().iter().cloned());
            let handled = self.with_source_binders(&scope, |this| {
                this.with_resume_representation(ResumeRepresentation::Queue, |this| {
                    this.with_resume_alias(operation.resume().name(), |this| {
                        this.comp(operation.body())
                    })
                })
            })?;
            let resume_bound = TypedBinder::new(operation.resume().name(), resume.ty().clone());
            let handled = TypedComp::new(
                handled.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(resume.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(Self::var(resume.name(), resume.ty().clone())),
                    )),
                    resume_bound,
                    Box::new(handled),
                ),
            );
            let handled = Self::bind_operation_params(operation.params(), &argument, handled)?;
            let mut parameters = vec![argument, resume];
            parameters.extend(captures.iter().cloned());
            let signature = CoreFnSig::new(
                self.quantifiers.clone(),
                parameters
                    .iter()
                    .map(|parameter| parameter.ty().clone())
                    .collect(),
                handled.sig().clone(),
            );
            self.generated_signatures.insert(clause, signature.clone());
            self.generated
                .push(TypedCoreFn::new(clause, parameters, handled, signature, 0));
            clauses.push(clause);
        }

        let pure_value = TypedBinder::new(self.mint("x"), abi::word());
        let pure_body = if let (Some(binder), Some(return_body)) = (return_binder, return_body) {
            let mut scope = captures.clone();
            scope.push(binder.clone());
            let lowered = self.with_source_binders(&scope, |this| this.direct(return_body))?;
            let unpacked = abi::lowered_repr(
                Self::var(pure_value.name(), pure_value.ty().clone()),
                binder.ty().clone(),
            );
            TypedComp::new(
                lowered.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(binder.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(unpacked),
                    )),
                    binder.clone(),
                    Box::new(lowered),
                ),
            )
        } else {
            TypedComp::new(
                CompSig::new(result_ty.clone(), EffRow::Empty),
                TypedCompKind::Return(abi::lowered_repr(
                    Self::var(pure_value.name(), pure_value.ty().clone()),
                    result_ty.clone(),
                )),
            )
        };
        let pure_arm = (abi::epure_pattern(self.row.clone(), pure_value), pure_body);

        let id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
        let skip = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
        let argument = TypedBinder::new(self.mint("arg"), abi::word());
        let queue = TypedBinder::new(self.mint("k"), abi::queue(self.row.clone()));
        let mut dispatch = TypedComp::new(
            CompSig::new(result_ty.clone(), self.row.clone()),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str("ICE: unhandled effect op in closed native handler".into()),
            )),
        );
        for (operation, clause) in ops.arms().iter().zip(clauses).rev() {
            let mut clause_args = vec![
                Self::var(argument.name(), argument.ty().clone()),
                Self::var(queue.name(), queue.ty().clone()),
            ];
            clause_args.extend(
                captures
                    .iter()
                    .map(|capture| Self::var(capture.name(), capture.ty().clone())),
            );
            let clause_call = self.call(clause, clause_args)?;
            let clause_result = TypedBinder::new(self.mint("cr"), abi::eff(self.row.clone()));

            let resumed_queue = TypedBinder::new(self.mint("q"), abi::queue(self.row.clone()));
            let resumed_value = TypedBinder::new(self.mint("v"), abi::word());
            let applied = TypedBinder::new(self.mint("qa"), abi::eff(self.row.clone()));
            let qapply = abi::qapply(
                Self::var(resumed_queue.name(), resumed_queue.ty().clone()),
                Self::var(resumed_value.name(), resumed_value.ty().clone()),
                self.row.clone(),
            );
            let mut region_args = vec![Self::var(applied.name(), applied.ty().clone())];
            region_args.extend(
                captures
                    .iter()
                    .map(|capture| Self::var(capture.name(), capture.ty().clone())),
            );
            let redrive = self.call(region, region_args)?;
            let resume_arm = (
                abi::eresume_pattern(self.row.clone(), resumed_queue, resumed_value),
                TypedComp::new(
                    redrive.sig().clone(),
                    TypedCompKind::Bind(Box::new(qapply), applied, Box::new(redrive)),
                ),
            );

            let escaped_id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
            let escaped_skip = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
            let escaped_argument = TypedBinder::new(self.mint("arg"), abi::word());
            let escaped_queue = TypedBinder::new(self.mint("k"), abi::queue(self.row.clone()));
            let escaped_arm = (
                abi::eop_pattern(
                    self.row.clone(),
                    escaped_id,
                    escaped_skip,
                    escaped_argument,
                    escaped_queue,
                ),
                TypedComp::new(
                    CompSig::new(result_ty.clone(), self.row.clone()),
                    TypedCompKind::Error(TypedValue::new(
                        CoreType::Source(Type::Str),
                        TypedValueKind::Str(
                            "ICE: effect op escaped a closed native handler clause".into(),
                        ),
                    )),
                ),
            );
            let answer = TypedBinder::new(self.mint("ans"), abi::word());
            let answer_arm = (
                abi::epure_pattern(self.row.clone(), answer.clone()),
                TypedComp::new(
                    CompSig::new(result_ty.clone(), EffRow::Empty),
                    TypedCompKind::Return(abi::lowered_repr(
                        Self::var(answer.name(), answer.ty().clone()),
                        result_ty.clone(),
                    )),
                ),
            );
            let inspected = TypedComp::new(
                CompSig::new(result_ty.clone(), self.row.clone()),
                TypedCompKind::Case(
                    Self::var(clause_result.name(), clause_result.ty().clone()),
                    vec![resume_arm, escaped_arm, answer_arm],
                ),
            );
            let branch = TypedComp::new(
                inspected.sig().clone(),
                TypedCompKind::Bind(Box::new(clause_call), clause_result, Box::new(inspected)),
            );
            let matched = TypedBinder::new(self.mint("t"), CoreType::Source(Type::Bool));
            let is_operation = TypedComp::new(
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
                TypedCompKind::Prim(
                    CoreOp::Eq,
                    Self::var(id.name(), id.ty().clone()),
                    TypedValue::new(
                        CoreType::Source(Type::Int),
                        TypedValueKind::Int(self.ops.id(operation.name())?),
                    ),
                ),
            );
            let selected = TypedComp::new(
                dispatch.sig().clone(),
                TypedCompKind::If(
                    Self::var(matched.name(), matched.ty().clone()),
                    Box::new(branch),
                    Box::new(dispatch),
                ),
            );
            dispatch = TypedComp::new(
                selected.sig().clone(),
                TypedCompKind::Bind(Box::new(is_operation), matched, Box::new(selected)),
            );
        }
        let op_arm = (
            abi::eop_pattern(self.row.clone(), id, skip, argument, queue),
            dispatch,
        );
        let current = TypedBinder::new(self.mint("cur"), abi::eff(self.row.clone()));
        let region_body = TypedComp::new(
            CompSig::new(result_ty, self.row.clone()),
            TypedCompKind::Case(
                Self::var(current.name(), current.ty().clone()),
                vec![pure_arm, op_arm],
            ),
        );
        let mut parameters = vec![current];
        parameters.extend(captures.iter().cloned());
        self.generated.push(TypedCoreFn::new(
            region,
            parameters,
            region_body,
            region_signature,
            0,
        ));

        let initial = TypedBinder::new(self.mint("r0"), abi::eff(self.row.clone()));
        let body = self.comp(body)?;
        let mut region_args = vec![Self::var(initial.name(), initial.ty().clone())];
        region_args.extend(
            captures
                .iter()
                .map(|capture| self.value(&Self::var(capture.name(), capture.ty().clone())))
                .collect::<Option<Vec<_>>>()?,
        );
        let call = self.call(region, region_args)?;
        Some(TypedComp::new(
            call.sig().clone(),
            TypedCompKind::Bind(Box::new(body), initial, Box::new(call)),
        ))
    }

    /// Re-enter the driver in place of a clause's tail resumption.
    ///
    /// A closed driver answers at the source convention, so it is not an effect
    /// computation and nothing downstream can defer a call to it. A reified
    /// resumption there is a closure the clause immediately forces, and the
    /// forced call is not in tail position of the driver, so every hop costs a
    /// native frame and a program whose hops are heap objects runs out of stack
    /// anyway. Applying the queue and calling the driver directly is the same
    /// computation at the same arity in tail position, which is a native loop.
    ///
    /// The rewrite holds exactly where the clause resumes in tail position and
    /// nowhere else, so it recognizes that shape as it goes and answers `None`
    /// for any other, leaving the reified continuation to carry it.
    fn resume_tail_loop(
        &mut self,
        comp: &TypedComp,
        aliases: &BTreeSet<Sym>,
        tail: bool,
        queue: &TypedBinder,
        driver: Sym,
        captures: &[TypedBinder],
    ) -> Option<TypedComp> {
        let verbatim = || {
            free_comp_vars(comp)
                .is_disjoint(aliases)
                .then(|| comp.clone())
        };
        match comp.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                if !forced_repr_var(callee).is_some_and(|name| aliases.contains(&name)) {
                    return verbatim();
                }
                let [argument] = args.as_slice() else {
                    return None;
                };
                if !tail
                    || !instantiation.is_empty()
                    || !free_value_vars(argument).is_disjoint(aliases)
                {
                    return None;
                }
                let resumed =
                    TypedBinder::new(Sym::from(names::RESUME_KONT), abi::eff(self.row.clone()));
                let applied = abi::qapply(
                    Self::var(queue.name(), queue.ty().clone()),
                    abi::lowered_repr(argument.clone(), abi::word()),
                    self.row.clone(),
                );
                let mut redrive_args = vec![Self::var(resumed.name(), resumed.ty().clone())];
                redrive_args.extend(
                    captures
                        .iter()
                        .map(|capture| Self::var(capture.name(), capture.ty().clone())),
                );
                let redrive = self.call(driver, redrive_args)?;
                Some(TypedComp::new(
                    redrive.sig().clone(),
                    TypedCompKind::Bind(Box::new(applied), resumed, Box::new(redrive)),
                ))
            }
            TypedCompKind::Bind(head, binder, body) => {
                let routing = match head.kind() {
                    TypedCompKind::Return(value) => {
                        repr_var(value).is_some_and(|name| aliases.contains(&name))
                    }
                    _ => false,
                };
                if routing {
                    // The name being rebound no longer exists once the clause
                    // resumes by re-entry, so the binding goes with it and the
                    // new name joins the aliases the tail is read against.
                    let mut extended = aliases.clone();
                    extended.insert(binder.name());
                    return self.resume_tail_loop(body, &extended, tail, queue, driver, captures);
                }
                let head = self.resume_tail_loop(head, aliases, false, queue, driver, captures)?;
                let body = self.resume_tail_loop(body, aliases, tail, queue, driver, captures)?;
                Some(TypedComp::new(
                    CompSig::new(
                        body.sig().result().clone(),
                        union_effects(head.sig().effects(), body.sig().effects()),
                    ),
                    TypedCompKind::Bind(Box::new(head), binder.clone(), Box::new(body)),
                ))
            }
            TypedCompKind::If(condition, yes, no) => {
                if !free_value_vars(condition).is_disjoint(aliases) {
                    return None;
                }
                let yes = self.resume_tail_loop(yes, aliases, tail, queue, driver, captures)?;
                let no = self.resume_tail_loop(no, aliases, tail, queue, driver, captures)?;
                Some(TypedComp::new(
                    CompSig::new(
                        yes.sig().result().clone(),
                        union_effects(yes.sig().effects(), no.sig().effects()),
                    ),
                    TypedCompKind::If(condition.clone(), Box::new(yes), Box::new(no)),
                ))
            }
            TypedCompKind::Case(scrutinee, arms) => {
                if !free_value_vars(scrutinee).is_disjoint(aliases) {
                    return None;
                }
                let mut effects = EffRow::Empty;
                let mut rewritten = Vec::with_capacity(arms.len());
                for (pattern, body) in arms {
                    let body =
                        self.resume_tail_loop(body, aliases, tail, queue, driver, captures)?;
                    effects = union_effects(&effects, body.sig().effects());
                    rewritten.push((pattern.clone(), body));
                }
                let result = rewritten.first()?.1.sig().result().clone();
                Some(TypedComp::new(
                    CompSig::new(result, effects),
                    TypedCompKind::Case(scrutinee.clone(), rewritten),
                ))
            }
            _ => verbatim(),
        }
    }

    /// The driver's pure arm: the body's value has arrived, so the return
    /// clause runs on it where the handler has one and the value is answered
    /// as it stands where it does not. The value reaches the arm at the word
    /// representation the effect cell carries, so the clause's binder is bound
    /// to it unpacked at the source type the clause was written against.
    fn driver_pure_body(
        &mut self,
        comp: &TypedComp,
        captures: &[TypedBinder],
        open: bool,
        driver_result: &CoreType,
        pure_value: &TypedBinder,
    ) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            return_binder,
            return_body,
            ..
        } = comp.kind()
        else {
            return None;
        };
        Some(
            if let (Some(binder), Some(return_body)) = (return_binder, return_body) {
                let mut scope = captures.to_vec();
                scope.push(binder.clone());
                let lowered = self.with_source_binders(&scope, |this| {
                    if open {
                        this.comp(return_body)
                    } else {
                        this.direct(return_body)
                    }
                })?;
                let unpacked = abi::lowered_repr(
                    Self::var(pure_value.name(), pure_value.ty().clone()),
                    binder.ty().clone(),
                );
                TypedComp::new(
                    lowered.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(TypedComp::new(
                            CompSig::new(binder.ty().clone(), EffRow::Empty),
                            TypedCompKind::Return(unpacked),
                        )),
                        binder.clone(),
                        Box::new(lowered),
                    ),
                )
            } else if open {
                abi::epure(
                    Self::var(pure_value.name(), pure_value.ty().clone()),
                    self.row.clone(),
                )
            } else {
                TypedComp::new(
                    CompSig::new(driver_result.clone(), EffRow::Empty),
                    TypedCompKind::Return(abi::lowered_repr(
                        Self::var(pure_value.name(), pure_value.ty().clone()),
                        driver_result.clone(),
                    )),
                )
            },
        )
    }

    pub(super) fn handle(&mut self, comp: &TypedComp, open: bool) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            finally_body: None,
            ops,
        } = comp.kind()
        else {
            return None;
        };
        if return_binder.is_some() != return_body.is_some() || ops.arms().is_empty() {
            return None;
        }
        // A driver that forwards answers in the effect type, so its clause
        // reaches the resumption through the monadic plumbing rather than in
        // its own tail, and the hop is a closure call no backend can make a
        // native tail call. Confined that is a frame per hop; widening reaches
        // the scope whose driver bounces the hop instead. Termination is not
        // the lowering's to decide, so the scope that cannot run the loop
        // refuses it rather than compiling one that runs out of stack.
        if open && !self.whole_style() {
            if let Some(operation) = ops.arms().iter().find(|operation| {
                resumes_in_tail(
                    operation.body(),
                    &BTreeSet::from([operation.resume().name()]),
                )
            }) {
                return self.refuse(Refusal::ForwardingResume, Site::Name(operation.name()));
            }
        }
        let captures = self.handler_captures(comp)?;

        let driver = self.mint_driver(FreeMonadDriver::Handle);
        let result = TypedBinder::new(self.mint("res"), abi::eff(self.row.clone()));
        let mut driver_params = vec![result.ty().clone()];
        driver_params.extend(captures.iter().map(|capture| capture.ty().clone()));
        let driver_result = if open {
            abi::eff(self.row.clone())
        } else {
            comp.sig().result().clone()
        };
        let driver_signature = CoreFnSig::new(
            self.quantifiers.clone(),
            driver_params,
            CompSig::new(driver_result.clone(), self.row.clone()),
        );
        self.generated_signatures
            .insert(driver, driver_signature.clone());

        let pure_value = TypedBinder::new(self.mint("x"), abi::word());
        let pure_body =
            self.driver_pure_body(comp, &captures, open, &driver_result, &pure_value)?;
        let pure_arm = (abi::epure_pattern(self.row.clone(), pure_value), pure_body);

        let id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
        let skip = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
        let argument = TypedBinder::new(self.mint("arg"), abi::word());
        let queue = TypedBinder::new(self.mint("k"), abi::queue(self.row.clone()));
        // In a program with a cleanup clause the operation's word is the
        // argument beside its pending cleanups: forwarding passes the pair on
        // untouched, and only a clause that catches it opens it.
        let pending = self.cleanups.then(|| {
            (
                TypedBinder::new(self.mint("arg"), abi::word()),
                TypedBinder::new(self.mint("pend"), abi::word()),
            )
        });
        let carried = pending
            .as_ref()
            .map_or_else(|| argument.clone(), |(packed, _)| packed.clone());

        let resume_value = TypedBinder::new(Sym::from(names::RESUME_VAL), abi::word());
        let resumed = TypedBinder::new(Sym::from(names::RESUME_KONT), abi::eff(self.row.clone()));
        let applied = abi::qapply(
            Self::var(queue.name(), queue.ty().clone()),
            Self::var(resume_value.name(), resume_value.ty().clone()),
            self.row.clone(),
        );
        let mut redrive_args = vec![Self::var(resumed.name(), resumed.ty().clone())];
        redrive_args.extend(
            captures
                .iter()
                .map(|capture| Self::var(capture.name(), capture.ty().clone())),
        );
        let redrive = self.call(driver, redrive_args)?;
        let resume_body = TypedComp::new(
            redrive.sig().clone(),
            TypedCompKind::Bind(Box::new(applied), resumed, Box::new(redrive)),
        );
        let resume_lambda = Self::lam(vec![resume_value], resume_body);
        let resume = TypedValue::new(
            CoreType::Thunk(Box::new(resume_lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(resume_lambda)),
        );

        let mut dispatch = if open {
            self.forward_eop(
                Self::var(id.name(), id.ty().clone()),
                Self::var(skip.name(), skip.ty().clone()),
                Self::var(carried.name(), carried.ty().clone()),
                resume.clone(),
            )
        } else {
            self.closed_dispatch_error(driver_result)
        };
        for operation in ops.arms().iter().rev() {
            let mut scope = captures.clone();
            scope.extend(operation.params().iter().cloned());
            let mut handled = self.with_source_binders(&scope, |this| {
                if open {
                    this.with_resume_alias(operation.resume().name(), |this| {
                        this.comp(operation.body())
                    })
                } else {
                    this.direct(operation.body())
                }
            })?;
            let mut reified = true;
            if !open {
                if let Some(looped) = self.resume_tail_loop(
                    &handled,
                    &BTreeSet::from([operation.resume().name()]),
                    true,
                    &queue,
                    driver,
                    &captures,
                ) {
                    handled = looped;
                    reified = false;
                }
            }
            handled = Self::bind_operation_params(operation.params(), &argument, handled)?;
            if open || reified {
                let bound_resume = if open {
                    resume.clone()
                } else {
                    abi::lowered_repr(
                        abi::lowered_repr(resume.clone(), abi::word()),
                        operation.resume().ty().clone(),
                    )
                };
                handled = TypedComp::new(
                    handled.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(TypedComp::new(
                            CompSig::new(bound_resume.ty().clone(), EffRow::Empty),
                            TypedCompKind::Return(bound_resume),
                        )),
                        if open {
                            TypedBinder::new(operation.resume().name(), resume.ty().clone())
                        } else {
                            operation.resume().clone()
                        },
                        Box::new(handled),
                    ),
                );
            }

            if let Some((_, cleanups)) = &pending {
                handled = self.run_pending(handled, cleanups)?;
            }

            let selected = if open {
                let decremented = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
                let forwarded = self.forward_eop(
                    Self::var(id.name(), id.ty().clone()),
                    Self::var(decremented.name(), decremented.ty().clone()),
                    Self::var(carried.name(), carried.ty().clone()),
                    resume.clone(),
                );
                let subtract = TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                    TypedCompKind::Prim(
                        CoreOp::Sub,
                        Self::var(skip.name(), skip.ty().clone()),
                        TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
                    ),
                );
                let forward = TypedComp::new(
                    forwarded.sig().clone(),
                    TypedCompKind::Bind(Box::new(subtract), decremented, Box::new(forwarded)),
                );
                let zero = TypedBinder::new(self.mint("z"), CoreType::Source(Type::Bool));
                let is_zero = TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
                    TypedCompKind::Prim(
                        CoreOp::Eq,
                        Self::var(skip.name(), skip.ty().clone()),
                        TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(0)),
                    ),
                );
                let selected_signature = CompSig::new(
                    handled.sig().result().clone(),
                    union_effects(handled.sig().effects(), forward.sig().effects()),
                );
                let selected = TypedComp::new(
                    selected_signature,
                    TypedCompKind::If(
                        Self::var(zero.name(), zero.ty().clone()),
                        Box::new(handled),
                        Box::new(forward),
                    ),
                );
                TypedComp::new(
                    selected.sig().clone(),
                    TypedCompKind::Bind(Box::new(is_zero), zero, Box::new(selected)),
                )
            } else {
                handled
            };

            // Every clause folds into this one dispatch, and a branch of it can
            // carry only one result type. A closed handler keeps its answers at
            // the source convention, where a clause whose answer never performs
            // holds an empty row inside the answered function type and a
            // performing sibling holds the ambient one: the checker unified
            // those at the source, but they are two Core types here and no
            // branch can hold both. Whole-program lowering answers with a cell
            // from every clause and never has the question, so refusing the
            // confined region costs speed and not meaning.
            if !open && selected.sig().result() != dispatch.sig().result() {
                return self.refuse(Refusal::HandlerArms, Site::Function);
            }

            let matched = TypedBinder::new(self.mint("t"), CoreType::Source(Type::Bool));
            let is_operation = TypedComp::new(
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
                TypedCompKind::Prim(
                    CoreOp::Eq,
                    Self::var(id.name(), id.ty().clone()),
                    TypedValue::new(
                        CoreType::Source(Type::Int),
                        TypedValueKind::Int(self.ops.id(operation.name())?),
                    ),
                ),
            );
            let branch_signature = CompSig::new(
                selected.sig().result().clone(),
                union_effects(selected.sig().effects(), dispatch.sig().effects()),
            );
            let branch = TypedComp::new(
                branch_signature,
                TypedCompKind::If(
                    Self::var(matched.name(), matched.ty().clone()),
                    Box::new(selected),
                    Box::new(dispatch),
                ),
            );
            dispatch = TypedComp::new(
                branch.sig().clone(),
                TypedCompKind::Bind(Box::new(is_operation), matched, Box::new(branch)),
            );
        }

        if let Some((_, cleanups)) = &pending {
            dispatch = TypedComp::new(
                dispatch.sig().clone(),
                TypedCompKind::Case(
                    abi::lowered_repr(
                        Self::var(carried.name(), carried.ty().clone()),
                        abi::pending(),
                    ),
                    vec![(abi::pend_pattern(argument, cleanups.clone()), dispatch)],
                ),
            );
        }
        let op_arm = (
            abi::eop_pattern(self.row.clone(), id, skip, carried, queue),
            dispatch,
        );
        let driver_body_signature = CompSig::new(
            driver_signature.body().result().clone(),
            union_effects(pure_arm.1.sig().effects(), op_arm.1.sig().effects()),
        );
        let driver_body = TypedComp::new(
            driver_body_signature,
            TypedCompKind::Case(
                Self::var(result.name(), result.ty().clone()),
                vec![pure_arm, op_arm],
            ),
        );
        let mut generated_params = vec![result];
        generated_params.extend(captures.iter().cloned());
        self.generated.push(TypedCoreFn::new(
            driver,
            generated_params,
            driver_body,
            driver_signature,
            0,
        ));

        let initial = TypedBinder::new(self.mint("r0"), abi::eff(self.row.clone()));
        let body = self.comp(body)?;
        let mut driver_args = vec![Self::var(initial.name(), initial.ty().clone())];
        driver_args.extend(
            captures
                .iter()
                .map(|capture| self.value(&Self::var(capture.name(), capture.ty().clone())))
                .collect::<Option<Vec<_>>>()?,
        );
        let driver_call = self.call(driver, driver_args)?;
        Some(TypedComp::new(
            driver_call.sig().clone(),
            TypedCompKind::Bind(Box::new(body), initial, Box::new(driver_call)),
        ))
    }

    /// Bind a cell's answer to `parameter` and continue with `tail` through
    /// the monadic bind, so an operation the head performs carries the tail in
    /// its queue.
    fn ebind_then(
        &mut self,
        head: TypedComp,
        parameter: TypedBinder,
        tail: TypedComp,
    ) -> TypedComp {
        let result = TypedBinder::new(self.mint("m"), abi::eff(self.row.clone()));
        let lambda = Self::lam(vec![parameter], tail);
        let continuation = TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        );
        let call = TypedComp::new(
            CompSig::new(abi::eff(self.row.clone()), self.row.clone()),
            TypedCompKind::Call {
                callee: Sym::from(EBIND),
                instantiation: abi::row_instantiation(self.row.clone()),
                args: vec![Self::var(result.name(), result.ty().clone()), continuation],
            },
        );
        TypedComp::new(
            call.sig().clone(),
            TypedCompKind::Bind(Box::new(head), result, Box::new(call)),
        )
    }

    /// A catching clause's answer, after the cleanups its operation left
    /// pending. Each pending cleanup answers with the value it was given, so
    /// the queue applied to the clause's answer runs them innermost first and
    /// hands the answer back; one whose resumption the clause took is disarmed
    /// and passes it straight on.
    fn run_pending(&mut self, handled: TypedComp, cleanups: &TypedBinder) -> Option<TypedComp> {
        let answer = TypedBinder::new(self.mint("x"), abi::word());
        let pending = abi::unpack_queue_word(
            Self::var(cleanups.name(), cleanups.ty().clone()),
            self.row.clone(),
        )?;
        let run = abi::qapply(
            pending,
            Self::var(answer.name(), answer.ty().clone()),
            self.row.clone(),
        );
        Some(self.ebind_then(handled, answer, run))
    }

    /// The cleanup body, then `value` as the answer.
    fn cleanup_then(
        &mut self,
        cleanup: &TypedComp,
        captures: &[TypedBinder],
        value: &TypedBinder,
    ) -> Option<TypedComp> {
        let lowered = self.with_source_binders(captures, |this| this.comp(cleanup))?;
        let ignored = TypedBinder::new(self.mint("u"), abi::word());
        let answer = abi::epure(
            Self::var(value.name(), value.ty().clone()),
            self.row.clone(),
        );
        Some(self.ebind_then(lowered, ignored, answer))
    }

    /// A handler with a `finally` clause, as the handler without it inside a
    /// bracket driver that runs the clause when the handler is left.
    ///
    /// The bracket handles no operation. On the pure arm the handler's answer
    /// is complete, so the cleanup runs and the answer passes on. An operation
    /// leaving the handler is forwarded with one armed cell: the resumption the
    /// bracket forwards disarms it, and the operation carries, beside its
    /// argument, a pending entry that runs the cleanup while the cell is still
    /// armed. The handler that catches the operation runs its pending entries
    /// once its clause is done, so a clause that drops the continuation leaves
    /// through every cleanup it crossed, innermost first, and one that resumed
    /// leaves none to run. The handler's own clauses catch inside the bracket,
    /// so their answers reach the pure arm like any other.
    pub(super) fn bracket(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            finally_body: Some(cleanup),
            ops,
        } = comp.kind()
        else {
            return None;
        };
        if return_binder.is_some() != return_body.is_some() {
            return None;
        }
        let inner = if !ops.arms().is_empty() {
            let handler = TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Handle {
                    body: body.clone(),
                    return_binder: return_binder.clone(),
                    return_body: return_body.clone(),
                    finally_body: None,
                    ops: ops.clone(),
                },
            );
            self.handle(&handler, true)?
        } else if let (Some(binder), Some(return_body)) = (return_binder, return_body) {
            self.comp(&TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Bind(body.clone(), binder.clone(), return_body.clone()),
            ))?
        } else {
            self.comp(body)?
        };

        let mut free: Vec<Sym> = free_comp_vars(cleanup).into_iter().collect();
        free.sort_by(|left, right| left.as_str().cmp(right.as_str()));
        let captures = free
            .into_iter()
            .map(|name| Some(TypedBinder::new(name, self.locals.get(&name)?.clone())))
            .collect::<Option<Vec<_>>>()?;

        let driver = self.mint_driver(FreeMonadDriver::Handle);
        let result = TypedBinder::new(self.mint("res"), abi::eff(self.row.clone()));
        let mut driver_params = vec![result.ty().clone()];
        driver_params.extend(captures.iter().map(|capture| capture.ty().clone()));
        let driver_signature = CoreFnSig::new(
            self.quantifiers.clone(),
            driver_params,
            CompSig::new(abi::eff(self.row.clone()), self.row.clone()),
        );
        self.generated_signatures
            .insert(driver, driver_signature.clone());
        let capture_args = || -> Vec<TypedValue> {
            captures
                .iter()
                .map(|capture| Self::var(capture.name(), capture.ty().clone()))
                .collect::<Vec<_>>()
        };

        let pure_value = TypedBinder::new(self.mint("x"), abi::word());
        let pure_body = self.cleanup_then(cleanup, &captures, &pure_value)?;
        let pure_arm = (abi::epure_pattern(self.row.clone(), pure_value), pure_body);

        let id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
        let skip = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
        let carried = TypedBinder::new(self.mint("arg"), abi::word());
        let queue = TypedBinder::new(self.mint("k"), abi::queue(self.row.clone()));
        let argument = TypedBinder::new(self.mint("arg"), abi::word());
        let pending = TypedBinder::new(self.mint("pend"), abi::word());
        let armed = TypedBinder::new(
            self.mint("armed"),
            CoreType::Ref(Box::new(CoreType::Source(Type::Bool))),
        );
        let armed_var = || Self::var(armed.name(), armed.ty().clone());
        let bool_value =
            |value| TypedValue::new(CoreType::Source(Type::Bool), TypedValueKind::Bool(value));

        // The resumption the bracket forwards: taking it disarms the entry.
        let resume_value = TypedBinder::new(Sym::from(names::RESUME_VAL), abi::word());
        let resumed = TypedBinder::new(Sym::from(names::RESUME_KONT), abi::eff(self.row.clone()));
        let applied = abi::qapply(
            Self::var(queue.name(), queue.ty().clone()),
            Self::var(resume_value.name(), resume_value.ty().clone()),
            self.row.clone(),
        );
        let mut redrive_args = vec![Self::var(resumed.name(), resumed.ty().clone())];
        redrive_args.extend(capture_args());
        let redrive = self.call(driver, redrive_args)?;
        let resume_body = TypedComp::new(
            redrive.sig().clone(),
            TypedCompKind::Bind(Box::new(applied), resumed, Box::new(redrive)),
        );
        let disarm = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::Empty),
            TypedCompKind::RefSet(armed_var(), bool_value(false)),
        );
        let disarmed = TypedBinder::new(self.mint("u"), CoreType::Source(Type::Unit));
        let resume_body = TypedComp::new(
            resume_body.sig().clone(),
            TypedCompKind::Bind(Box::new(disarm), disarmed, Box::new(resume_body)),
        );
        let resume_lambda = Self::lam(vec![resume_value], resume_body);
        let resume = TypedValue::new(
            CoreType::Thunk(Box::new(resume_lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(resume_lambda)),
        );

        // The pending entry: the cleanup while still armed, then its input.
        let passed = TypedBinder::new(self.mint("x"), abi::word());
        let run = self.cleanup_then(cleanup, &captures, &passed)?;
        let skipped = abi::epure(
            Self::var(passed.name(), passed.ty().clone()),
            self.row.clone(),
        );
        let still = TypedBinder::new(self.mint("b"), CoreType::Source(Type::Bool));
        let read = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            TypedCompKind::RefGet(armed_var()),
        );
        let chosen = TypedComp::new(
            CompSig::new(
                abi::eff(self.row.clone()),
                union_effects(run.sig().effects(), skipped.sig().effects()),
            ),
            TypedCompKind::If(
                Self::var(still.name(), still.ty().clone()),
                Box::new(run),
                Box::new(skipped),
            ),
        );
        let entry_body = TypedComp::new(
            chosen.sig().clone(),
            TypedCompKind::Bind(Box::new(read), still, Box::new(chosen)),
        );
        let entry_lambda = Self::lam(vec![passed], entry_body);
        let entry = TypedValue::new(
            CoreType::Thunk(Box::new(entry_lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(entry_lambda)),
        );

        let extended = TypedBinder::new(self.mint("pend"), abi::queue(self.row.clone()));
        let snoc = TypedComp::new(
            CompSig::new(abi::queue(self.row.clone()), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::TaqSnoc,
                instantiation: abi::row_instantiation(self.row.clone()),
                args: vec![
                    abi::unpack_queue_word(
                        Self::var(pending.name(), pending.ty().clone()),
                        self.row.clone(),
                    )?,
                    entry,
                ],
            },
        );
        let forwarded = self.forward_eop(
            Self::var(id.name(), id.ty().clone()),
            Self::var(skip.name(), skip.ty().clone()),
            abi::pend(
                Self::var(argument.name(), argument.ty().clone()),
                abi::pack_queue_word(Self::var(extended.name(), extended.ty().clone()))?,
            ),
            resume,
        );
        let forwarded = TypedComp::new(
            forwarded.sig().clone(),
            TypedCompKind::Bind(Box::new(snoc), extended, Box::new(forwarded)),
        );
        let opened = TypedComp::new(
            forwarded.sig().clone(),
            TypedCompKind::Case(
                abi::lowered_repr(
                    Self::var(carried.name(), carried.ty().clone()),
                    abi::pending(),
                ),
                vec![(abi::pend_pattern(argument, pending), forwarded)],
            ),
        );
        let arm = TypedComp::new(
            CompSig::new(armed.ty().clone(), EffRow::Empty),
            TypedCompKind::RefNew(bool_value(true)),
        );
        let op_body = TypedComp::new(
            opened.sig().clone(),
            TypedCompKind::Bind(Box::new(arm), armed.clone(), Box::new(opened)),
        );
        let op_arm = (
            abi::eop_pattern(self.row.clone(), id, skip, carried, queue),
            op_body,
        );

        let driver_body = TypedComp::new(
            CompSig::new(
                abi::eff(self.row.clone()),
                union_effects(pure_arm.1.sig().effects(), op_arm.1.sig().effects()),
            ),
            TypedCompKind::Case(
                Self::var(result.name(), result.ty().clone()),
                vec![pure_arm, op_arm],
            ),
        );
        let mut generated_params = vec![result];
        generated_params.extend(captures.iter().cloned());
        self.generated.push(TypedCoreFn::new(
            driver,
            generated_params,
            driver_body,
            driver_signature,
            0,
        ));

        let initial = TypedBinder::new(self.mint("r0"), abi::eff(self.row.clone()));
        let mut driver_args = vec![Self::var(initial.name(), initial.ty().clone())];
        driver_args.extend(
            captures
                .iter()
                .map(|capture| self.value(&Self::var(capture.name(), capture.ty().clone())))
                .collect::<Option<Vec<_>>>()?,
        );
        let driver_call = self.call(driver, driver_args)?;
        Some(TypedComp::new(
            driver_call.sig().clone(),
            TypedCompKind::Bind(Box::new(inner), initial, Box::new(driver_call)),
        ))
    }
}

/// The variable a value names, through the representation bridges the lowering
/// crosses to reach the reified thunk's word convention. A clause reads its own
/// resume across one of those, so a bare variable is not what the tree holds.
fn repr_var(value: &TypedValue) -> Option<Sym> {
    let mut value = value;
    while let TypedValueKind::LoweredRepr { value: inner, .. } = &value.kind {
        value = inner;
    }
    let TypedValueKind::Var {
        name,
        instantiation,
    } = &value.kind
    else {
        return None;
    };
    instantiation.is_empty().then_some(*name)
}

/// Whether a clause resumes in tail position.
///
/// That is the shape which turns a handled loop into a driver loop: the hop
/// answers by re-entering the driver and nothing of the clause is left to come
/// back to. A resumption anywhere else has work waiting after it, so it holds a
/// frame at every scope alike and none of them runs it unbounded.
fn resumes_in_tail(comp: &TypedComp, aliases: &BTreeSet<Sym>) -> bool {
    match comp.kind() {
        TypedCompKind::App { callee, .. } => {
            forced_var(callee).is_some_and(|name| aliases.contains(&name))
        }
        TypedCompKind::Bind(head, binder, body) => {
            // Naming is administrative here: the clause is in normal form, so
            // the resumption it applies has been rebound at least once by the
            // time the application reads it, and following the rebinding is
            // what makes the tail legible.
            let mut aliases = aliases.clone();
            match head.kind() {
                TypedCompKind::Return(value)
                    if repr_var(value).is_some_and(|name| aliases.contains(&name)) =>
                {
                    aliases.insert(binder.name());
                }
                _ => {
                    aliases.remove(&binder.name());
                }
            }
            resumes_in_tail(body, &aliases)
        }
        TypedCompKind::If(_, yes, no) => {
            resumes_in_tail(yes, aliases) || resumes_in_tail(no, aliases)
        }
        TypedCompKind::Case(_, arms) => arms.iter().any(|(_, body)| resumes_in_tail(body, aliases)),
        _ => false,
    }
}

fn forced_repr_var(comp: &TypedComp) -> Option<Sym> {
    let TypedCompKind::Force(value) = comp.kind() else {
        return None;
    };
    repr_var(value)
}
