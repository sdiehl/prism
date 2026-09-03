//! Witness-preserving free-monad rewrite engine.

use super::{
    abi, answered_thunk, flow, forced_var, free_comp_vars, free_value_vars,
    function_applied_once_tail, instantiate_fn, lowered_representation_conversion, names, plan,
    state_clause, state_return, union_effects, walk, BTreeMap, BTreeSet, Builtin, CompSig,
    CoreFnSig, CoreInstantiation, CoreOp, CoreQuantifier, CoreType, Decline, EffRow, Effects,
    FnAnswerLowering, FreeMonadDriver, Fresh, Monadic, MonadicScope, OpIds, Refusal, Region,
    ResumeRepresentation, Shadowed, Site, Sym, Type, TypedBinder, TypedComp, TypedCompKind,
    TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue, TypedValueKind, EBIND,
};

mod handler;

impl<'a> Monadic<'a> {
    pub fn new(
        ops: &'a OpIds,
        fresh: &'a mut Fresh,
        row: EffRow,
        calls: &'a BTreeMap<Sym, CoreFnSig>,
    ) -> Self {
        Self {
            ops,
            fresh,
            suspension_row: row.clone(),
            row,
            calls,
            generated: Vec::new(),
            generated_signatures: BTreeMap::new(),
            quantifiers: Vec::new(),
            locals: BTreeMap::new(),
            thunk_sigs: BTreeMap::new(),
            word_binders: BTreeMap::new(),
            resume_aliases: BTreeSet::new(),
            resume_representation: ResumeRepresentation::Continuation,
            region_plan: None,
            refusal: None,
            latent: None,
            flow: None,
            native_enabled: false,
        }
    }

    /// Set the row for a declaration whose own convention is the monadic one,
    /// where everything it suspends shares that row.
    pub(super) fn set_row(&mut self, row: EffRow) {
        self.suspension_row = row.clone();
        self.row = row;
    }

    /// Set the rows for a declaration the rewrite leaves at the direct
    /// convention while it may still build a computation the region owns.
    pub(super) fn set_direct_row(&mut self, row: EffRow, suspension_row: EffRow) {
        self.row = row;
        self.suspension_row = suspension_row;
    }

    pub(super) fn call_instantiation(
        &self,
        signature: &CoreFnSig,
        source: &[CoreInstantiation],
    ) -> Option<Vec<CoreInstantiation>> {
        let ambient = Sym::from(names::FREE_MONAD_ROW);
        if signature.quantifiers().len() == source.len() {
            // A direct row-polymorphic callee retains its source answer-row
            // quantifier, while its caller may already use the phase-private
            // free-monad row. Re-instantiate that one tail at the call boundary
            // so the declaration's parameter, result and body witnesses cross
            // together. Instantiations erase, and no parent row widens.
            if self.row.tail() != &EffRow::Var(ambient) {
                return Some(source.to_vec());
            }
            let EffRow::Var(tail) = signature.body().effects().tail() else {
                return Some(source.to_vec());
            };
            let Some(index) = signature
                .quantifiers()
                .iter()
                .position(|quantifier| quantifier == &CoreQuantifier::Row(*tail))
            else {
                return Some(source.to_vec());
            };
            let mut instantiation = source.to_vec();
            let argument = self.ambient_call_row(signature)?;
            let Some(CoreInstantiation::Row(row)) = instantiation.get_mut(index) else {
                return None;
            };
            *row = argument;
            return Some(instantiation);
        }
        if signature.quantifiers().len() != source.len() + 1
            || signature.quantifiers().last() != Some(&CoreQuantifier::Row(ambient))
        {
            return None;
        }
        let mut instantiation = source.to_vec();
        instantiation.push(CoreInstantiation::Row(self.ambient_call_row(signature)?));
        Some(instantiation)
    }

    fn ambient_call_row(&self, signature: &CoreFnSig) -> Option<EffRow> {
        let required = signature.body().effects().labels();
        let current = self.row.labels();
        if required.iter().any(|label| !current.contains(label)) {
            return None;
        }
        Some(EffRow::canonical(
            current
                .into_iter()
                .filter(|label| !required.contains(label))
                .cloned(),
            self.row.tail().clone(),
        ))
    }

    pub(super) const fn configure_region(&mut self, region: &Region<'a>) {
        self.region_plan = Some(region.plan);
        self.latent = Some(region.latent);
        self.flow = Some(region.flow);
        self.native_enabled = region.native_enabled;
    }

    /// Whether a value stands for a computation this region lowers at the
    /// monadic convention, asked against the signatures currently in scope.
    ///
    /// False outside a configured confined region: whole-style lowering has no
    /// second convention to confuse this one with, having put every declaration
    /// it rewrites into the monadic one, and asking there would answer for
    /// thunks the flow solution was never consulted about.
    fn monadic_thunk(&self, value: &TypedValue) -> bool {
        let (Some(latent), Some(_)) = (self.latent, self.flow) else {
            return false;
        };
        plan::thunk_is_monadic(value, &self.thunk_sigs, latent)
    }

    /// [`monadic_thunk`](Self::monadic_thunk) restricted to a thunk written
    /// here rather than a variable holding one. Only a literal is the producer's
    /// to rewrite; a variable already carries whatever convention its binding
    /// site chose, and re-deriving one for it would rewrite the same thunk twice.
    fn produces_monadic_thunk(&self, value: &TypedValue) -> bool {
        walk::is_thunk(value) && self.monadic_thunk(value)
    }

    /// Whether a handler answers with a transformer this region rewrites at the
    /// monadic convention: a clause, or the return clause, hands back a thunk
    /// over a lambda that performs, for the code around the handle to apply.
    ///
    /// Such an answer leaves the driver as an ordinary value word, and nothing
    /// downstream can read the convention back off it. A transformer that does
    /// not perform is not in question: every arm builds it at the direct
    /// convention, so applying it directly is right, which is why this asks the
    /// thunk rather than the shape.
    fn answers_monadic_transformer(&self, comp: &TypedComp) -> bool {
        let TypedCompKind::Handle {
            return_body, ops, ..
        } = comp.kind()
        else {
            return false;
        };
        let answered = return_body
            .as_deref()
            .into_iter()
            .chain(ops.arms().iter().map(TypedHandleOp::body));
        answered
            .filter_map(answered_thunk)
            .any(|(thunk, _, _)| self.produces_monadic_thunk(thunk))
    }

    /// Whether a callee position forces a thunk this region lowered at the
    /// monadic convention. Such a force answers with an `Eff` cell, so it must
    /// be applied through the monadic head path and never through the direct
    /// one, which would apply the free-monad cell as if it were the suspended
    /// source function.
    fn forces_monadic_thunk(&self, comp: &TypedComp) -> bool {
        let TypedCompKind::Force(value) = comp.kind() else {
            return false;
        };
        self.monadic_thunk(value)
    }

    /// The signature of the thunk a computation returns, in the current scope.
    /// Empty outside a configured confined region, where no thunk is tracked.
    fn result_sig(&self, comp: &TypedComp) -> flow::Sig {
        match (self.latent, self.flow) {
            (Some(latent), Some(flow)) => flow::result_sig(comp, &self.thunk_sigs, latent, flow),
            _ => flow::Sig::new(),
        }
    }

    /// Record what forcing the computation bound to `name` can still perform,
    /// for the scope the binder covers. An empty signature is left unrecorded so
    /// that an absent entry and a pure one are the same answer; the binder's
    /// enclosing scope guard has already removed any shadowed entry.
    fn note_thunk_sig(&mut self, name: Sym, signature: flow::Sig) {
        if !signature.is_empty() {
            self.thunk_sigs.insert(name, signature);
        }
    }

    /// Suspend a computation at the monadic convention: the body goes through
    /// the monadic builder and the thunk's type follows the body it now holds,
    /// which is what makes the change of convention visible to the verifier
    /// rather than a silent reinterpretation of the same `Thunk(_)` word.
    fn build_monadic_thunk(&mut self, body: &TypedComp) -> Option<TypedValue> {
        let lowered = match body.kind() {
            TypedCompKind::Lam(params, inner) => Self::lam_with(
                Self::lam_quantifiers(body),
                params.clone(),
                self.with_source_binders(params, |this| this.comp(inner))?,
            ),
            _ => self.comp(body)?,
        };
        Some(TypedValue::new(
            CoreType::Thunk(Box::new(lowered.sig().clone())),
            TypedValueKind::Thunk(Box::new(lowered)),
        ))
    }

    fn mint(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }

    // Driver templates are named by the effect ABI, which owns both the spelling
    // and the predicate native codegen counts structural reduction steps with.
    // Spelling one here would let a rename drift the two apart silently.
    fn mint_driver(&mut self, driver: FreeMonadDriver) -> Sym {
        Sym::from(driver.mint(self.fresh.bump()))
    }

    pub(super) const fn var(name: Sym, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name,
                instantiation: Vec::new(),
            },
        )
    }

    pub(super) fn lam(params: Vec<TypedBinder>, body: TypedComp) -> TypedComp {
        Self::lam_with(Vec::new(), params, body)
    }

    // Rebuild a lambda that keeps its source quantifiers. A generated
    // word/continuation lambda is monomorphic and passes an empty list, but a
    // re-lowered source lambda (a polymorphic dictionary field) must retain its
    // `forall`, or a bound type variable in its body escapes its binder.
    fn lam_with(
        quantifiers: Vec<CoreQuantifier>,
        params: Vec<TypedBinder>,
        body: TypedComp,
    ) -> TypedComp {
        let signature = CoreFnSig::new(
            quantifiers,
            params.iter().map(|param| param.ty().clone()).collect(),
            body.sig().clone(),
        );
        TypedComp::new(
            CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
            TypedCompKind::Lam(params, Box::new(body)),
        )
    }

    // The source quantifiers of a lambda computation, read from its function
    // result type, or empty when the shape is not a function.
    fn lam_quantifiers(comp: &TypedComp) -> Vec<CoreQuantifier> {
        match comp.sig().result() {
            CoreType::Function(sig) => sig.quantifiers().to_vec(),
            _ => Vec::new(),
        }
    }

    fn monadic_thunk_type(&self, ty: &CoreType) -> Option<CoreType> {
        let CoreType::Thunk(suspension) = ty else {
            return None;
        };
        let CoreType::Function(function) = suspension.result() else {
            return None;
        };
        Some(CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                function.quantifiers().to_vec(),
                function.params().to_vec(),
                CompSig::new(abi::eff(self.row.clone()), self.row.clone()),
            ))),
            suspension.effects().clone(),
        ))))
    }

    fn ambient_direct_thunk_type(&self, ty: &CoreType) -> Option<CoreType> {
        let CoreType::Thunk(suspension) = ty else {
            return None;
        };
        let CoreType::Function(function) = suspension.result() else {
            return None;
        };
        Some(CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                function.quantifiers().to_vec(),
                function.params().to_vec(),
                CompSig::new(function.body().result().clone(), self.row.clone()),
            ))),
            suspension.effects().clone(),
        ))))
    }

    /// Cross a source container boundary without pretending that its source
    /// type can name the phase-private `Eff` result. Both witnesses are native
    /// value words; the two explicit ABI edges retain that representation fact
    /// while making the calling-convention change visible to the verifier.
    fn retag_runtime_word(value: TypedValue, expected: CoreType) -> Option<TypedValue> {
        if value.ty() == &expected {
            return Some(value);
        }
        if !lowered_representation_conversion(value.ty(), &abi::word())
            || !lowered_representation_conversion(&abi::word(), &expected)
        {
            return None;
        }
        Some(abi::lowered_repr(
            abi::lowered_repr(value, abi::word()),
            expected,
        ))
    }

    /// Rewrite a value, then re-establish the witness its enclosing declaration
    /// owns. Whole-style lowering can change a closure's answer convention, but
    /// source constructor schemes, tuple fields and function parameters cannot
    /// name phase-private `Eff`; the explicit word bridge records that the
    /// representation crossing is nevertheless exact.
    fn value_at(&mut self, value: &TypedValue, expected: &CoreType) -> Option<TypedValue> {
        let transformed = self.value(value)?;
        Self::retag_runtime_word(transformed, expected.clone())
    }

    /// Refuse when a callee's thunk-valued slot is driven at the monadic
    /// convention and the argument standing in it was left at the direct one.
    ///
    /// A slot's convention is the join over every call site, and a thunk carries
    /// no convention in its type, so a callee reached with a computation the
    /// region owns at one site and a plain one at another leaves the plain site
    /// nothing to hand over: there is no coercion to insert, only a forcer that
    /// would drive a source function as if it were an effect cell.
    fn check_monadic_arguments(&mut self, callee: Sym, args: &[TypedValue]) -> Option<()> {
        let Some(slots) = self
            .region_plan
            .filter(|plan| plan.scope == MonadicScope::Selective)
            .and_then(|plan| plan.monadic_params.get(&callee))
        else {
            return Some(());
        };
        for argument in slots.iter().filter_map(|index| args.get(*index)) {
            if !self.monadic_thunk(argument) {
                return self.refuse(Refusal::ThunkBoundary, Self::value_site(argument));
            }
        }
        Some(())
    }

    fn whole_style(&self) -> bool {
        self.region_plan
            .is_none_or(|plan| plan.scope == MonadicScope::WholeProgram)
    }

    /// Run `f` with source-typed binders in lexical scope. A binder may shadow
    /// an enclosing monadic `Word` binder with the same erased name; generated
    /// drivers use this when a captured word is unpacked at the call boundary
    /// and becomes an ordinary source-typed parameter inside the driver.
    fn with_source_binders<T>(
        &mut self,
        binders: &[TypedBinder],
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let saved: Vec<Shadowed> = binders
            .iter()
            .map(|binder| Shadowed {
                name: binder.name(),
                local: self.locals.insert(binder.name(), binder.ty().clone()),
                word: self.word_binders.remove(&binder.name()),
                resume: self.resume_aliases.remove(&binder.name()),
                // A fresh binder carries no signature until its binding site
                // records one. Dropping the shadowed entry is what keeps a
                // pattern variable that reuses an outer thunk's name from
                // inheriting the outer thunk's convention.
                signature: self.thunk_sigs.remove(&binder.name()),
            })
            .collect();
        let result = f(self);
        for Shadowed {
            name,
            local,
            word,
            resume,
            signature,
        } in saved.into_iter().rev()
        {
            match local {
                Some(ty) => {
                    self.locals.insert(name, ty);
                }
                None => {
                    self.locals.remove(&name);
                }
            }
            if let Some(ty) = word {
                self.word_binders.insert(name, ty);
            } else {
                self.word_binders.remove(&name);
            }
            if resume {
                self.resume_aliases.insert(name);
            } else {
                self.resume_aliases.remove(&name);
            }
            match signature {
                Some(signature) => {
                    self.thunk_sigs.insert(name, signature);
                }
                None => {
                    self.thunk_sigs.remove(&name);
                }
            }
        }
        result
    }

    fn with_word_binder<T>(
        &mut self,
        binder: &TypedBinder,
        resume_alias: bool,
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let old_local = self.locals.insert(binder.name(), binder.ty().clone());
        let old_word = self.word_binders.insert(binder.name(), binder.ty().clone());
        let old_resume = self.resume_aliases.remove(&binder.name());
        let old_signature = self.thunk_sigs.remove(&binder.name());
        if resume_alias {
            self.resume_aliases.insert(binder.name());
        }
        let result = f(self);
        match old_local {
            Some(ty) => {
                self.locals.insert(binder.name(), ty);
            }
            None => {
                self.locals.remove(&binder.name());
            }
        }
        match old_word {
            Some(ty) => {
                self.word_binders.insert(binder.name(), ty);
            }
            None => {
                self.word_binders.remove(&binder.name());
            }
        }
        if old_resume {
            self.resume_aliases.insert(binder.name());
        } else {
            self.resume_aliases.remove(&binder.name());
        }
        match old_signature {
            Some(signature) => {
                self.thunk_sigs.insert(binder.name(), signature);
            }
            None => {
                self.thunk_sigs.remove(&binder.name());
            }
        }
        result
    }

    fn with_resume_alias<T>(
        &mut self,
        name: Sym,
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let old = self.resume_aliases.insert(name);
        let result = f(self);
        if !old {
            self.resume_aliases.remove(&name);
        }
        result
    }

    fn with_resume_representation<T>(
        &mut self,
        representation: ResumeRepresentation,
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let old = std::mem::replace(&mut self.resume_representation, representation);
        let result = f(self);
        self.resume_representation = old;
        result
    }

    fn pattern_binders(pattern: &TypedPattern) -> Vec<TypedBinder> {
        match pattern {
            TypedPattern::Wild => Vec::new(),
            TypedPattern::Var(binder) => vec![binder.clone()],
            TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
                fields.iter().flatten().cloned().collect()
            }
        }
    }

    fn word(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let value = self.value(value)?;
        if !lowered_representation_conversion(value.ty(), &abi::word()) {
            return None;
        }
        Some(abi::lowered_repr(value, abi::word()))
    }

    fn packed_word(&mut self, args: &[TypedValue]) -> Option<TypedValue> {
        let value = match args {
            [] => TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit),
            [argument] => self.value(argument)?,
            _ => {
                let fields = args
                    .iter()
                    .map(|argument| self.value(argument))
                    .collect::<Option<Vec<_>>>()?;
                TypedValue::new(
                    CoreType::Source(Type::Tuple(
                        fields
                            .iter()
                            .map(|field| match field.ty() {
                                CoreType::Source(ty) => Some(ty.clone()),
                                _ => None,
                            })
                            .collect::<Option<_>>()?,
                    )),
                    TypedValueKind::Tuple(fields),
                )
            }
        };
        if !lowered_representation_conversion(value.ty(), &abi::word()) {
            return None;
        }
        Some(abi::lowered_repr(value, abi::word()))
    }

    fn lift(&mut self, direct: TypedComp) -> Option<TypedComp> {
        let result = TypedBinder::new(self.mint("p"), direct.sig().result().clone());
        let tail = abi::epure(
            self.word(&Self::var(result.name(), result.ty().clone()))?,
            self.row.clone(),
        );
        Some(TypedComp::new(
            // The lifted node runs in the ambient monadic row like every other
            // node, not the source residue the un-lowered `direct` still carries;
            // a stale source row variable here fails the `ebind` continuation's
            // ambient-row expectation. Row-only, erased Core unchanged.
            CompSig::new(tail.sig().result().clone(), self.row.clone()),
            TypedCompKind::Bind(Box::new(direct), result, Box::new(tail)),
        ))
    }

    pub(super) fn value(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let ty = value.ty().clone();
        Some(match &value.kind {
            TypedValueKind::Var {
                name,
                instantiation,
            } if self.resume_aliases.contains(name) => {
                if !instantiation.is_empty() {
                    return None;
                }
                let word = if self.word_binders.contains_key(name) {
                    Self::var(*name, abi::word())
                } else {
                    match self.resume_representation {
                        ResumeRepresentation::Continuation => abi::lowered_repr(
                            Self::var(*name, abi::kont(self.row.clone())),
                            abi::word(),
                        ),
                        ResumeRepresentation::Queue => {
                            abi::pack_queue_word(Self::var(*name, abi::queue(self.row.clone())))?
                        }
                    }
                };
                abi::lowered_repr(word, ty)
            }
            TypedValueKind::Var {
                name,
                instantiation,
            } if self.word_binders.contains_key(name) => {
                if !instantiation.is_empty() || self.word_binders.get(name) != Some(&ty) {
                    return None;
                }
                abi::lowered_repr(Self::var(*name, abi::word()), ty)
            }
            TypedValueKind::Var { .. }
            | TypedValueKind::Unit
            | TypedValueKind::Int(_)
            | TypedValueKind::I64(_)
            | TypedValueKind::U64(_)
            | TypedValueKind::Bool(_)
            | TypedValueKind::Float(_)
            | TypedValueKind::Str(_)
            | TypedValueKind::UnboxedTuple(_)
            | TypedValueKind::UnboxedRecord(_) => value.clone(),
            TypedValueKind::Reinterpret(inner) => {
                let transformed = self.value(inner)?;
                if transformed.ty() == inner.ty() {
                    TypedValue::new(ty, TypedValueKind::Reinterpret(Box::new(transformed)))
                } else {
                    transformed
                }
            }
            TypedValueKind::LoweredRepr { value, proof } => TypedValue::new(
                ty,
                TypedValueKind::LoweredRepr {
                    value: Box::new(self.value(value)?),
                    proof: proof.clone(),
                },
            ),
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValue::new(
                ty,
                TypedValueKind::NewtypeRepr {
                    constructor: *constructor,
                    instantiation: instantiation.clone(),
                    value: Box::new(self.value_at(value, value.ty())?),
                },
            ),
            TypedValueKind::Thunk(body) => {
                // A confined region rewrites only the thunks whose forcing can
                // still perform an operation. The rest keep the convention they
                // were written at, so what a non-capturing program erases to is
                // exactly what it erased to before the region existed.
                if !self.whole_style() && !self.monadic_thunk(value) {
                    return self.verbatim(value);
                }
                self.build_monadic_thunk(body)?
            }
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValue::new(
                ty,
                TypedValueKind::Ctor {
                    name: *name,
                    tag: *tag,
                    instantiation: instantiation.clone(),
                    fields: fields
                        .iter()
                        .map(|field| self.value_at(field, field.ty()))
                        .collect::<Option<_>>()?,
                },
            ),
            TypedValueKind::Tuple(fields) => TypedValue::new(
                ty,
                TypedValueKind::Tuple(
                    fields
                        .iter()
                        .map(|field| self.value_at(field, field.ty()))
                        .collect::<Option<_>>()?,
                ),
            ),
        })
    }

    /// Translate the closed structural core of the free-monad transform.
    /// Unsupported dynamic applications, handlers, and masks decline here and
    /// are added by the driver/handler layers rather than guessed locally.
    #[allow(clippy::too_many_lines)] // One arm per computation form; the exhaustive match is the point.
    pub fn comp(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        Some(match comp.kind() {
            TypedCompKind::Return(value) => abi::epure(self.word(value)?, self.row.clone()),
            TypedCompKind::Bind(head, binder, tail) => {
                let resume_alias = matches!(
                    head.kind(),
                    TypedCompKind::Return(TypedValue {
                        kind: TypedValueKind::Var { name, instantiation },
                        ..
                    }) if instantiation.is_empty() && self.resume_aliases.contains(name)
                );
                let result = TypedBinder::new(self.mint("m"), abi::eff(self.row.clone()));
                let bound = self.result_sig(head);
                let monadic_tail = self.with_word_binder(binder, resume_alias, |this| {
                    this.note_thunk_sig(binder.name(), bound);
                    this.comp(tail)
                })?;
                let monadic_head = self.comp(head)?;
                let parameter = TypedBinder::new(binder.name(), abi::word());
                let lambda = Self::lam(vec![parameter], monadic_tail);
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
                    TypedCompKind::Bind(Box::new(monadic_head), result, Box::new(call)),
                )
            }
            TypedCompKind::Do {
                operation,
                instantiation: _,
                args,
            } => {
                let id = self.ops.id(*operation)?;
                abi::eop(
                    TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(id)),
                    TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(0)),
                    self.packed_word(args)?,
                    abi::empty_queue(self.row.clone()),
                    self.row.clone(),
                )
            }
            TypedCompKind::If(condition, yes, no) => {
                let yes = self.comp(yes)?;
                let no = self.comp(no)?;
                let signature = CompSig::new(
                    yes.sig().result().clone(),
                    union_effects(yes.sig().effects(), no.sig().effects()),
                );
                TypedComp::new(
                    signature,
                    TypedCompKind::If(self.value(condition)?, Box::new(yes), Box::new(no)),
                )
            }
            TypedCompKind::Case(scrutinee, arms) => {
                let arms: Vec<(TypedPattern, TypedComp)> = arms
                    .iter()
                    .map(|(pattern, body)| {
                        let binders = Self::pattern_binders(pattern);
                        Some((
                            pattern.clone(),
                            self.with_source_binders(&binders, |this| this.comp(body))?,
                        ))
                    })
                    .collect::<Option<_>>()?;
                let first = arms.first()?.1.sig();
                let effects = arms
                    .iter()
                    .skip(1)
                    .fold(first.effects().clone(), |effects, (_, body)| {
                        union_effects(&effects, body.sig().effects())
                    });
                let signature = CompSig::new(first.result().clone(), effects);
                TypedComp::new(signature, TypedCompKind::Case(self.value(scrutinee)?, arms))
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                if self.resume_representation == ResumeRepresentation::Queue {
                    if let Some(queue) = self.resume_queue(callee) {
                        if !instantiation.is_empty() {
                            return None;
                        }
                        return Some(abi::eresume(
                            queue,
                            self.packed_word(args)?,
                            self.row.clone(),
                        ));
                    }
                }
                // A confined member applies most callees directly and lifts the
                // answer. Forcing a thunk the region owns is the exception: that
                // force answers with an `Eff` cell, which only the head path can
                // apply.
                if !self.whole_style()
                    && self.resume_head(callee).is_none()
                    && !self.forces_monadic_thunk(callee)
                {
                    let direct = self.direct(comp)?;
                    return self.lift(direct);
                }
                let resume = self.resume_head(callee);
                let (callee, args) = if let Some(callee) = resume {
                    if !instantiation.is_empty() {
                        return None;
                    }
                    (callee, vec![self.packed_word(args)?])
                } else {
                    let callee = self.head(callee)?;
                    let CoreType::Function(signature) = callee.sig().result() else {
                        return None;
                    };
                    let signature = instantiate_fn(signature, instantiation).ok()?;
                    if signature.params().len() != args.len() {
                        return None;
                    }
                    let args = args
                        .iter()
                        .zip(signature.params())
                        .map(|(argument, expected)| self.value_at(argument, expected))
                        .collect::<Option<_>>()?;
                    (callee, args)
                };
                TypedComp::new(
                    CompSig::new(abi::eff(self.row.clone()), self.row.clone()),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation: instantiation.clone(),
                        args,
                    },
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                self.check_monadic_arguments(*callee, args)?;
                let signature = self
                    .generated_signatures
                    .get(callee)
                    .or_else(|| self.calls.get(callee))?;
                let instantiation = self.call_instantiation(signature, instantiation)?;
                let signature = instantiate_fn(signature, &instantiation).ok()?;
                if signature.params().len() != args.len() {
                    return None;
                }
                let args = args
                    .iter()
                    .zip(signature.params())
                    .map(|(argument, expected)| self.value_at(argument, expected))
                    .collect::<Option<_>>()?;
                let call = TypedComp::new(
                    signature.body().clone(),
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation,
                        args,
                    },
                );
                if signature.body().result() == &abi::eff(self.row.clone()) {
                    call
                } else {
                    self.lift(call)?
                }
            }
            TypedCompKind::Prim(operation, left, right) => {
                let left = self.value(left)?;
                let right = self.value(right)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Prim(*operation, left, right),
                ))?
            }
            TypedCompKind::Io(operation, args) => {
                let args = args
                    .iter()
                    .map(|argument| self.value(argument))
                    .collect::<Option<_>>()?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Io(*operation, args),
                ))?
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => {
                let args = args
                    .iter()
                    .map(|argument| self.value(argument))
                    .collect::<Option<_>>()?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::StrBuiltin {
                        op: *op,
                        instantiation: instantiation.clone(),
                        args,
                    },
                ))?
            }
            TypedCompKind::FloatBuiltin(operation, value) => {
                let value = self.value(value)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::FloatBuiltin(*operation, value),
                ))?
            }
            TypedCompKind::Neg(lane, value) => {
                let value = self.value(value)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Neg(*lane, value),
                ))?
            }
            TypedCompKind::UnboxedProject(value, index) => {
                let value = self.value(value)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::UnboxedProject(value, *index),
                ))?
            }
            TypedCompKind::Error(value) => TypedComp::new(
                CompSig::new(abi::eff(self.row.clone()), self.row.clone()),
                TypedCompKind::Error(self.value(value)?),
            ),
            TypedCompKind::Mask(operations, body) => {
                let driver = self.mask_driver(operations)?;
                let result = TypedBinder::new(self.mint("m"), abi::eff(self.row.clone()));
                let body = self.comp(body)?;
                let call =
                    self.call(driver, vec![Self::var(result.name(), result.ty().clone())])?;
                TypedComp::new(
                    call.sig().clone(),
                    TypedCompKind::Bind(Box::new(body), result, Box::new(call)),
                )
            }
            TypedCompKind::Handle { .. } if self.native_eligible(comp) => {
                let result = TypedBinder::new(self.mint("h"), comp.sig().result().clone());
                let handled = self.handle_native(comp)?;
                let lifted = abi::epure(
                    self.word(&Self::var(result.name(), result.ty().clone()))?,
                    self.row.clone(),
                );
                TypedComp::new(
                    // The bind's row is the union of the handled head and the
                    // pure `epure` tail, not the tail's empty row: a handler
                    // nested inside an effectful function carries that function's
                    // ambient row through the head, and storing `{}` fails the
                    // verifier's union rule. Row-only, erased Core unchanged.
                    CompSig::new(
                        lifted.sig().result().clone(),
                        union_effects(handled.sig().effects(), lifted.sig().effects()),
                    ),
                    TypedCompKind::Bind(Box::new(handled), result, Box::new(lifted)),
                )
            }
            TypedCompKind::Handle { .. } if self.handler_is_open(comp) => {
                // A transformer a clause answers with is rewritten at the
                // monadic convention when it performs, while the answer itself
                // leaves the driver as an ordinary value word. Nothing can read the
                // convention back off that word: the source type names a
                // function, the monadic bind erases the binder to a word, and
                // the driver's own pure arm answers with a transformer built at
                // the direct convention, so the two arms could not agree even if
                // the use site could ask. Applying such an answer directly would
                // consume an effect cell as a result, which is a wrong value
                // rather than a crash, so the confined region is refused and the
                // whole-program lowering, where every answer is a cell, takes
                // the program.
                if !self.whole_style() && self.answers_monadic_transformer(comp) {
                    return self.refuse(Refusal::HandlerAnswer, Site::Function);
                }
                self.handle(comp, true)?
            }
            TypedCompKind::Handle { .. } => {
                let result = TypedBinder::new(self.mint("h"), comp.sig().result().clone());
                let handled = self.handle(comp, false)?;
                let lifted = abi::epure(
                    self.word(&Self::var(result.name(), result.ty().clone()))?,
                    self.row.clone(),
                );
                TypedComp::new(
                    // The bind's row is the union of the handled head and the
                    // pure `epure` tail, not the tail's empty row: a handler
                    // nested inside an effectful function carries that function's
                    // ambient row through the head, and storing `{}` fails the
                    // verifier's union rule. Row-only, erased Core unchanged.
                    CompSig::new(
                        lifted.sig().result().clone(),
                        union_effects(handled.sig().effects(), lifted.sig().effects()),
                    ),
                    TypedCompKind::Bind(Box::new(handled), result, Box::new(lifted)),
                )
            }
            // Arena preparation runs before tier selection, so forced
            // whole-program lowering sees the pure `InitAt` nodes it
            // introduces. Sequence them into the monadic body like the other
            // direct runtime nodes while retaining their exact cell and
            // constructor witnesses.
            TypedCompKind::InitAt(cell, constructor) => {
                let cell = self.value(cell)?;
                let constructor = self.value(constructor)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::InitAt(cell, constructor),
                ))?
            }
            // Variable cells survive erasure as direct runtime nodes; sequence
            // them into the monadic body exactly like `Prim`/`Io` so a program
            // whose var loop landed on the free-monad convention still lowers.
            TypedCompKind::RefNew(value) => {
                let value = self.value(value)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::RefNew(value),
                ))?
            }
            TypedCompKind::RefGet(value) => {
                let value = self.value(value)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::RefGet(value),
                ))?
            }
            TypedCompKind::RefSet(cell, value) => {
                let cell = self.value(cell)?;
                let value = self.value(value)?;
                self.lift(TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::RefSet(cell, value),
                ))?
            }
            _ => return None,
        })
    }

    fn head(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        Some(match comp.kind() {
            TypedCompKind::Force(value) => {
                let mut value = self.value(value)?;
                if let Some(monadic) = self.monadic_thunk_type(value.ty()) {
                    value = Self::retag_runtime_word(value, monadic)?;
                }
                let CoreType::Thunk(signature) = value.ty().clone() else {
                    return None;
                };
                let CoreType::Function(function) = signature.result() else {
                    return None;
                };
                if function.body().result() != &abi::eff(self.row.clone()) {
                    return None;
                }
                TypedComp::new(*signature, TypedCompKind::Force(value))
            }
            TypedCompKind::Lam(params, body) => Self::lam_with(
                Self::lam_quantifiers(comp),
                params.clone(),
                self.with_source_binders(params, |this| this.comp(body))?,
            ),
            _ => return None,
        })
    }

    fn direct_app_callee(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        let TypedCompKind::Force(value) = comp.kind() else {
            return self.direct(comp);
        };
        // The callee of a direct application must answer with the suspended
        // source function. A thunk the region owns answers with an `Eff` cell
        // instead, and the caller has to route the application through the
        // monadic head path; declining is how that caller learns.
        if self.monadic_thunk(value) {
            return self.refuse(Refusal::DirectForce, Self::value_site(value));
        }
        let value = self.direct_argument(value)?;
        let ty = self.ambient_direct_thunk_type(value.ty())?;
        let value = Self::retag_runtime_word(value, ty)?;
        let CoreType::Thunk(signature) = value.ty().clone() else {
            return None;
        };
        Some(TypedComp::new(*signature, TypedCompKind::Force(value)))
    }

    fn resume_head(&self, comp: &TypedComp) -> Option<TypedComp> {
        let name = self.resume_var(comp)?;
        let resume = if self.word_binders.contains_key(&name) {
            abi::lowered_repr(Self::var(name, abi::word()), abi::kont(self.row.clone()))
        } else {
            Self::var(name, abi::kont(self.row.clone()))
        };
        // `abi::kont` builds a thunk type by construction, so the non-thunk
        // arm is unreachable on valid input. Decline (return `None`, which the
        // caller `?`-propagates) rather than crash if it is ever hit, so an
        // imperfect invariant downgrades the tier instead of surfacing as a
        // compiler crash. The `debug_assert!` keeps it loud in development.
        let CoreType::Thunk(signature) = resume.ty().clone() else {
            debug_assert!(false, "the resume ABI is expected to be a thunk");
            return None;
        };
        Some(TypedComp::new(*signature, TypedCompKind::Force(resume)))
    }

    fn resume_queue(&self, comp: &TypedComp) -> Option<TypedValue> {
        let name = self.resume_var(comp)?;
        Some(if self.word_binders.contains_key(&name) {
            abi::unpack_queue_word(Self::var(name, abi::word()), self.row.clone())?
        } else {
            Self::var(name, abi::queue(self.row.clone()))
        })
    }

    fn resume_var(&self, comp: &TypedComp) -> Option<Sym> {
        let TypedCompKind::Force(value) = comp.kind() else {
            return None;
        };
        let TypedValueKind::Var {
            name,
            instantiation,
        } = &value.kind
        else {
            return None;
        };
        (instantiation.is_empty() && self.resume_aliases.contains(name)).then_some(*name)
    }

    fn call(&self, callee: Sym, args: Vec<TypedValue>) -> Option<TypedComp> {
        let declaration = self
            .generated_signatures
            .get(&callee)
            .or_else(|| self.calls.get(&callee))?;
        let instantiation: Vec<CoreInstantiation> = declaration
            .quantifiers()
            .iter()
            .map(|quantifier| match quantifier {
                CoreQuantifier::Type(name) => CoreInstantiation::Type(Type::Var(*name)),
                CoreQuantifier::Row(name) => CoreInstantiation::Row(EffRow::Var(*name)),
            })
            .collect();
        let signature = instantiate_fn(declaration, &instantiation).ok()?;
        if signature.params().len() != args.len() {
            return None;
        }
        Some(TypedComp::new(
            signature.body().clone(),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            },
        ))
    }

    fn forward_eop(
        &mut self,
        id: TypedValue,
        skip: TypedValue,
        argument: TypedValue,
        resume: TypedValue,
    ) -> TypedComp {
        let queue = TypedBinder::new(self.mint("q"), abi::queue(self.row.clone()));
        let snoc = TypedComp::new(
            CompSig::new(abi::queue(self.row.clone()), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::TaqSnoc,
                instantiation: abi::row_instantiation(self.row.clone()),
                args: vec![abi::empty_queue(self.row.clone()), resume],
            },
        );
        let emitted = abi::eop(
            id,
            skip,
            argument,
            Self::var(queue.name(), queue.ty().clone()),
            self.row.clone(),
        );
        TypedComp::new(
            emitted.sig().clone(),
            TypedCompKind::Bind(Box::new(snoc), queue, Box::new(emitted)),
        )
    }

    fn closed_dispatch_error(&self, result: CoreType) -> TypedComp {
        TypedComp::new(
            CompSig::new(result, self.row.clone()),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str("ICE: unhandled effect op in closed handler dispatch".into()),
            )),
        )
    }

    fn bind_operation_params(
        parameters: &[TypedBinder],
        argument: &TypedBinder,
        mut body: TypedComp,
    ) -> Option<TypedComp> {
        match parameters {
            [] => {}
            [parameter] => {
                let unpacked = abi::lowered_repr(
                    Self::var(argument.name(), argument.ty().clone()),
                    parameter.ty().clone(),
                );
                body = TypedComp::new(
                    body.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(TypedComp::new(
                            CompSig::new(parameter.ty().clone(), EffRow::Empty),
                            TypedCompKind::Return(unpacked),
                        )),
                        parameter.clone(),
                        Box::new(body),
                    ),
                );
            }
            parameters => {
                let tuple_ty = CoreType::Source(Type::Tuple(
                    parameters
                        .iter()
                        .map(|parameter| match parameter.ty() {
                            CoreType::Source(ty) => Some(ty.clone()),
                            _ => None,
                        })
                        .collect::<Option<_>>()?,
                ));
                let unpacked =
                    abi::lowered_repr(Self::var(argument.name(), argument.ty().clone()), tuple_ty);
                body = TypedComp::new(
                    body.sig().clone(),
                    TypedCompKind::Case(
                        unpacked,
                        vec![(
                            TypedPattern::Tuple(parameters.iter().cloned().map(Some).collect()),
                            body,
                        )],
                    ),
                );
            }
        }
        Some(body)
    }

    fn mask_driver(&mut self, operations: &[Sym]) -> Option<Sym> {
        let driver = self.mint_driver(FreeMonadDriver::Mask);
        let driver_signature = CoreFnSig::new(
            self.quantifiers.clone(),
            vec![abi::eff(self.row.clone())],
            CompSig::new(abi::eff(self.row.clone()), self.row.clone()),
        );
        self.generated_signatures
            .insert(driver, driver_signature.clone());

        let queue = TypedBinder::new(self.mint("q"), abi::queue(self.row.clone()));
        let resume_value = TypedBinder::new(Sym::from(names::RESUME_VAL), abi::word());
        let resumed = TypedBinder::new(Sym::from(names::RESUME_KONT), abi::eff(self.row.clone()));
        let applied = abi::qapply(
            Self::var(Sym::from(names::CONT), abi::queue(self.row.clone())),
            Self::var(resume_value.name(), resume_value.ty().clone()),
            self.row.clone(),
        );
        let redrive = self.call(
            driver,
            vec![Self::var(resumed.name(), resumed.ty().clone())],
        )?;
        let resume_body = TypedComp::new(
            redrive.sig().clone(),
            TypedCompKind::Bind(Box::new(applied), resumed, Box::new(redrive)),
        );
        let resume_lambda = Self::lam(vec![resume_value], resume_body);
        let resume = TypedValue::new(
            abi::kont(self.row.clone()),
            TypedValueKind::Thunk(Box::new(resume_lambda)),
        );

        let reemit = |skip: TypedValue| {
            let snoc = TypedComp::new(
                CompSig::new(abi::queue(self.row.clone()), EffRow::Empty),
                TypedCompKind::StrBuiltin {
                    op: Builtin::TaqSnoc,
                    instantiation: abi::row_instantiation(self.row.clone()),
                    args: vec![abi::empty_queue(self.row.clone()), resume.clone()],
                },
            );
            let emitted = abi::eop(
                Self::var(Sym::from(names::OP_ID), CoreType::Source(Type::Int)),
                skip,
                Self::var(Sym::from(names::OP_ARG), abi::word()),
                Self::var(queue.name(), queue.ty().clone()),
                self.row.clone(),
            );
            TypedComp::new(
                emitted.sig().clone(),
                TypedCompKind::Bind(Box::new(snoc), queue.clone(), Box::new(emitted)),
            )
        };

        let bumped = TypedBinder::new(Sym::from(names::FWD_SKIP), CoreType::Source(Type::Int));
        let bump = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Prim(
                CoreOp::Add,
                Self::var(Sym::from(names::OP_SKIP), CoreType::Source(Type::Int)),
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
            ),
        );
        let bumped_body = reemit(Self::var(bumped.name(), bumped.ty().clone()));
        let bumped_body = TypedComp::new(
            bumped_body.sig().clone(),
            TypedCompKind::Bind(Box::new(bump), bumped, Box::new(bumped_body)),
        );
        let mut dispatch = reemit(Self::var(
            Sym::from(names::OP_SKIP),
            CoreType::Source(Type::Int),
        ));
        for operation in operations.iter().rev() {
            let matched = TypedBinder::new(self.mint("t"), CoreType::Source(Type::Bool));
            let is_operation = TypedComp::new(
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
                TypedCompKind::Prim(
                    CoreOp::Eq,
                    Self::var(Sym::from(names::OP_ID), CoreType::Source(Type::Int)),
                    TypedValue::new(
                        CoreType::Source(Type::Int),
                        TypedValueKind::Int(self.ops.id(*operation)?),
                    ),
                ),
            );
            let selected = TypedComp::new(
                dispatch.sig().clone(),
                TypedCompKind::If(
                    Self::var(matched.name(), matched.ty().clone()),
                    Box::new(bumped_body.clone()),
                    Box::new(dispatch),
                ),
            );
            dispatch = TypedComp::new(
                selected.sig().clone(),
                TypedCompKind::Bind(Box::new(is_operation), matched, Box::new(selected)),
            );
        }

        let returned = TypedBinder::new(Sym::from(names::RET), abi::eff(self.row.clone()));
        let pure_value = TypedBinder::new(Sym::from(names::COMPOSE), abi::word());
        let pure_arm = (
            abi::epure_pattern(self.row.clone(), pure_value.clone()),
            abi::epure(
                Self::var(pure_value.name(), pure_value.ty().clone()),
                self.row.clone(),
            ),
        );
        let op_arm = (
            abi::eop_pattern(
                self.row.clone(),
                TypedBinder::new(Sym::from(names::OP_ID), CoreType::Source(Type::Int)),
                TypedBinder::new(Sym::from(names::OP_SKIP), CoreType::Source(Type::Int)),
                TypedBinder::new(Sym::from(names::OP_ARG), abi::word()),
                TypedBinder::new(Sym::from(names::CONT), abi::queue(self.row.clone())),
            ),
            dispatch,
        );
        let body = TypedComp::new(
            pure_arm.1.sig().clone(),
            TypedCompKind::Case(
                Self::var(returned.name(), returned.ty().clone()),
                vec![pure_arm, op_arm],
            ),
        );
        self.generated.push(TypedCoreFn::new(
            driver,
            vec![returned],
            body,
            driver_signature,
            0,
        ));
        Some(driver)
    }

    pub(super) fn unwrap_entry(&mut self, body: TypedComp, result_ty: CoreType) -> TypedComp {
        let result = TypedBinder::new(self.mint("r"), abi::eff(self.row.clone()));
        let value = TypedBinder::new(self.mint("x"), abi::word());
        let pure_arm = (
            abi::epure_pattern(self.row.clone(), value.clone()),
            TypedComp::new(
                CompSig::new(result_ty.clone(), EffRow::Empty),
                TypedCompKind::Return(abi::lowered_repr(
                    Self::var(value.name(), value.ty().clone()),
                    result_ty.clone(),
                )),
            ),
        );

        let id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
        let mut trap = TypedComp::new(
            CompSig::new(result_ty.clone(), EffRow::Empty),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str("unhandled effect".into()),
            )),
        );
        let entries: Vec<(Sym, i64)> = self.ops.iter().collect();
        for (name, operation_id) in entries.into_iter().rev() {
            let matched = TypedBinder::new(self.mint("t"), CoreType::Source(Type::Bool));
            let comparison = TypedComp::new(
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
            let named = TypedComp::new(
                CompSig::new(result_ty.clone(), EffRow::Empty),
                TypedCompKind::Error(TypedValue::new(
                    CoreType::Source(Type::Str),
                    TypedValueKind::Str(format!("unhandled effect `{name}`")),
                )),
            );
            let selected = TypedComp::new(
                trap.sig().clone(),
                TypedCompKind::If(
                    Self::var(matched.name(), matched.ty().clone()),
                    Box::new(named),
                    Box::new(trap),
                ),
            );
            trap = TypedComp::new(
                selected.sig().clone(),
                TypedCompKind::Bind(Box::new(comparison), matched, Box::new(selected)),
            );
        }
        let ignored_skip = TypedBinder::new(Sym::from("_us"), CoreType::Source(Type::Int));
        let ignored_argument = TypedBinder::new(Sym::from("_ua"), abi::word());
        let ignored_queue = TypedBinder::new(Sym::from("_uk"), abi::queue(self.row.clone()));
        let op_arm = (
            abi::eop_pattern(
                self.row.clone(),
                id,
                ignored_skip,
                ignored_argument,
                ignored_queue,
            ),
            trap,
        );
        let inspected = TypedComp::new(
            CompSig::new(result_ty.clone(), EffRow::Empty),
            TypedCompKind::Case(
                Self::var(result.name(), result.ty().clone()),
                vec![pure_arm, op_arm],
            ),
        );
        TypedComp::new(
            CompSig::new(result_ty, body.sig().effects().clone()),
            TypedCompKind::Bind(Box::new(body), result, Box::new(inspected)),
        )
    }

    pub(super) fn direct(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        Some(match comp.kind() {
            // A thunk the region owns must be built by the monadic builder even
            // where the code producing it stays direct, or the closure stored
            // here and the cell every force of it expects disagree. Nothing
            // else about the node changes: the value keeps its source type, so
            // this arm is the identity on a program that produces no such thunk.
            TypedCompKind::Return(value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Return(self.direct_value(value)?),
            ),
            TypedCompKind::Bind(head, binder, body) => {
                match self.try_handle_native_function_answer(head, binder, body)? {
                    FnAnswerLowering::Lowered(native) => *native,
                    FnAnswerLowering::Declined => {
                        let bound = self.result_sig(head);
                        let head = self.direct(head)?;
                        let body =
                            self.with_source_binders(std::slice::from_ref(binder), |this| {
                                this.note_thunk_sig(binder.name(), bound);
                                this.direct(body)
                            })?;
                        TypedComp::new(
                            // A bind's row is the union of its head and tail, not
                            // the tail alone: a residual bind whose head calls a
                            // latent-effectful function (`map` applying `f`)
                            // carries that effect, and dropping it fails the
                            // verifier's own union rule. Row-only, so erased Core
                            // is unchanged.
                            CompSig::new(
                                body.sig().result().clone(),
                                union_effects(head.sig().effects(), body.sig().effects()),
                            ),
                            TypedCompKind::Bind(Box::new(head), binder.clone(), Box::new(body)),
                        )
                    }
                }
            }
            TypedCompKind::If(condition, yes, no) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::If(
                    self.verbatim(condition)?,
                    Box::new(self.direct(yes)?),
                    Box::new(self.direct(no)?),
                ),
            ),
            TypedCompKind::Case(scrutinee, arms) => {
                let scrutinee = self.verbatim(scrutinee)?;
                let arms: Vec<(TypedPattern, TypedComp)> = arms
                    .iter()
                    .map(|(pattern, body)| {
                        let binders = Self::pattern_binders(pattern);
                        Some((
                            pattern.clone(),
                            self.with_source_binders(&binders, |this| this.direct(body))?,
                        ))
                    })
                    .collect::<Option<_>>()?;
                // A case's row is the union of its arms, recomputed after
                // lowering, not the pre-lowering row: an arm whose body forces
                // a residual-effectful function widens past the stored row, and
                // keeping the stale row fails the verifier's own union rule.
                // The result type is unchanged, so this is row-only and erased
                // Core is identical.
                let effects = arms.iter().fold(EffRow::Empty, |effects, (_, body)| {
                    union_effects(&effects, body.sig().effects())
                });
                TypedComp::new(
                    CompSig::new(comp.sig().result().clone(), effects),
                    TypedCompKind::Case(scrutinee, arms),
                )
            }
            TypedCompKind::Lam(parameters, body) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Lam(
                    parameters.clone(),
                    Box::new(self.with_source_binders(parameters, |this| this.direct(body))?),
                ),
            ),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = self.direct_app_callee(callee)?;
                let CoreType::Function(declaration) = callee.sig().result() else {
                    return None;
                };
                let signature = instantiate_fn(declaration, instantiation).ok()?;
                if signature.params().len() != args.len() {
                    return None;
                }
                let effects = union_effects(callee.sig().effects(), signature.body().effects());
                TypedComp::new(
                    CompSig::new(signature.body().result().clone(), effects),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation: instantiation.clone(),
                        args: args
                            .iter()
                            .map(|a| self.direct_argument(a))
                            .collect::<Option<_>>()?,
                    },
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                self.check_monadic_arguments(*callee, args)?;
                let declaration = self
                    .generated_signatures
                    .get(callee)
                    .or_else(|| self.calls.get(callee))?;
                let instantiation = self.call_instantiation(declaration, instantiation)?;
                let signature = instantiate_fn(declaration, &instantiation).ok()?;
                if signature.params().len() != args.len() {
                    return None;
                }
                let args = args
                    .iter()
                    .zip(signature.params())
                    .map(|(argument, expected)| self.direct_argument_at(argument, expected))
                    .collect::<Option<_>>()?;
                TypedComp::new(
                    signature.body().clone(),
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation,
                        args,
                    },
                )
            }
            TypedCompKind::Mask(_, body) => self.direct(body)?,
            TypedCompKind::Handle { .. } if self.native_eligible(comp) => {
                self.handle_native(comp)?
            }
            TypedCompKind::Handle { .. } if !self.handler_is_open(comp) => {
                self.handle(comp, false)?
            }
            TypedCompKind::Handle { .. } => return None,
            TypedCompKind::Force(value) => {
                // Forcing a thunk the region owns answers with an `Eff` cell,
                // not the source result this position expects. Membership is
                // meant to have pulled the forcer into the region already;
                // declining here refuses the plan rather than emitting the two
                // conventions spliced together.
                if self.monadic_thunk(value) {
                    return self.refuse(Refusal::DirectForce, Self::value_site(value));
                }
                TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Force(self.direct_argument(value)?),
                )
            }
            _ => {
                // Every remaining form copies its values verbatim, which is
                // sound only while none of them holds a thunk the region owns:
                // a copy would store the source-convention closure where every
                // force of it expects an `Eff` cell.
                if self.holds_monadic_thunk(comp) {
                    return self.refuse(Refusal::DirectHolds, Site::Function);
                }
                // The same copy is sound only while none of those values reads
                // a binder the region reified into a word: there is no crossing
                // inside a verbatim copy, so the reference would keep its
                // source type where the word is in scope.
                if self.reads_reified_binder(&free_comp_vars(comp)) {
                    return self.refuse(Refusal::WordCapture, Site::Function);
                }
                comp.clone()
            }
        })
    }

    /// Record why an attempt is refused, and decline. The first
    /// refusal wins: it is the innermost one, and every decline above it is
    /// only this one unwinding.
    const fn refuse<T>(&mut self, reason: Refusal, site: Site) -> Option<T> {
        if self.refusal.is_none() {
            self.refusal = Some((reason, site));
        }
        None
    }

    /// The refusal this builder recorded, attributed to the declaration being
    /// lowered when it stopped. A decline with nothing recorded is a form the
    /// builder has no rewrite for at all, which is a refusal of its own kind
    /// rather than an unexplained one.
    pub(super) const fn declined(&self, function: Sym) -> Decline {
        let (reason, site) = match self.refusal {
            Some(recorded) => recorded,
            None => (Refusal::UnsupportedForm, Site::Function),
        };
        Decline::new(reason, function, site)
    }

    /// The site a refusal names when it turns on forcing a value: the binder,
    /// when the value is one, and the enclosing function otherwise.
    const fn value_site(value: &TypedValue) -> Site {
        match value.kind() {
            TypedValueKind::Var { name, .. } => Site::Name(*name),
            _ => Site::Function,
        }
    }
}
