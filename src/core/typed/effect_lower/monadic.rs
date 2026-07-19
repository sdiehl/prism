//! Typed free-monad translation.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::builtins::Builtin;
use crate::core::cbpv::CoreOp;
use crate::names;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;
use crate::util::fresh::Fresh;

use super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::verify::{instantiate_fn, lowered_representation_conversion};
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue, TypedValueKind,
};
use super::abi;
use super::analysis::{MonadicRegionPlan, MonadicScope};
use super::evidence::OpIds;
use super::latent::Latent;
use super::residual::Rows;
use super::union_effects;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ResumeRepresentation {
    Continuation,
    Queue,
}

#[derive(Clone)]
struct StateClause {
    state: TypedBinder,
    prefix: Vec<(TypedComp, TypedBinder)>,
    resumed: TypedValue,
    next_state: TypedValue,
}

enum FnAnswerLowering {
    Declined,
    Lowered(Box<TypedComp>),
}

fn forced_var(comp: &TypedComp) -> Option<Sym> {
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
    instantiation.is_empty().then_some(*name)
}

fn state_return(return_body: Option<&TypedComp>) -> Option<(TypedBinder, TypedComp)> {
    let TypedCompKind::Return(value) = return_body?.kind() else {
        return None;
    };
    let TypedValueKind::Thunk(lambda) = &value.kind else {
        return None;
    };
    let TypedCompKind::Lam(parameters, body) = lambda.kind() else {
        return None;
    };
    let [state] = parameters.as_slice() else {
        return None;
    };
    Some((state.clone(), (**body).clone()))
}

fn state_apply_tail(comp: &TypedComp, result: Sym) -> Option<TypedValue> {
    let mut aliases = BTreeSet::from([result]);
    let mut current = comp;
    loop {
        match current.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = forced_var(callee)?;
                let [argument] = args.as_slice() else {
                    return None;
                };
                return (instantiation.is_empty()
                    && aliases.contains(&callee)
                    && free_value_vars(argument).is_disjoint(&aliases))
                .then(|| argument.clone());
            }
            TypedCompKind::Bind(head, binder, tail) => {
                let TypedCompKind::Return(value) = head.kind() else {
                    return None;
                };
                let TypedValueKind::Var {
                    name,
                    instantiation,
                } = &value.kind
                else {
                    return None;
                };
                if !instantiation.is_empty() || !aliases.contains(name) {
                    return None;
                }
                aliases.insert(binder.name());
                current = tail;
            }
            _ => return None,
        }
    }
}

fn resume_app(
    comp: &TypedComp,
    aliases: &BTreeSet<Sym>,
) -> Option<(Vec<(TypedComp, TypedBinder)>, TypedValue)> {
    let mut local = aliases.clone();
    let mut prefix = Vec::new();
    let mut current = comp;
    loop {
        match current.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = forced_var(callee)?;
                let [argument] = args.as_slice() else {
                    return None;
                };
                return (instantiation.is_empty()
                    && local.contains(&callee)
                    && free_value_vars(argument).is_disjoint(&local))
                .then(|| (prefix, argument.clone()));
            }
            TypedCompKind::Bind(head, binder, tail) => {
                if let TypedCompKind::Return(value) = head.kind() {
                    if let TypedValueKind::Var {
                        name,
                        instantiation,
                    } = &value.kind
                    {
                        if instantiation.is_empty() && local.contains(name) {
                            local.insert(binder.name());
                            current = tail;
                            continue;
                        }
                    }
                }
                if !matches!(
                    head.kind(),
                    TypedCompKind::Return(_) | TypedCompKind::Prim(..)
                ) || !free_comp_vars(head).is_disjoint(&local)
                {
                    return None;
                }
                prefix.push(((**head).clone(), binder.clone()));
                current = tail;
            }
            _ => return None,
        }
    }
}

fn state_clause(operation: &TypedHandleOp) -> Option<StateClause> {
    let TypedCompKind::Return(value) = operation.body().kind() else {
        return None;
    };
    let TypedValueKind::Thunk(lambda) = &value.kind else {
        return None;
    };
    let TypedCompKind::Lam(parameters, body) = lambda.kind() else {
        return None;
    };
    let [state] = parameters.as_slice() else {
        return None;
    };
    let mut aliases = BTreeSet::from([operation.resume().name()]);
    let mut prefix = Vec::new();
    let mut current = body.as_ref();
    loop {
        let TypedCompKind::Bind(head, binder, tail) = current.kind() else {
            return None;
        };
        if let Some((resume_prefix, resumed)) = resume_app(head, &aliases) {
            let next_state = state_apply_tail(tail, binder.name())?;
            prefix.extend(resume_prefix);
            let escaped = !free_value_vars(&resumed).is_disjoint(&aliases)
                || !free_value_vars(&next_state).is_disjoint(&aliases)
                || prefix
                    .iter()
                    .any(|(head, _)| !free_comp_vars(head).is_disjoint(&aliases));
            if escaped {
                return None;
            }
            return Some(StateClause {
                state: state.clone(),
                prefix,
                resumed,
                next_state,
            });
        }
        if let TypedCompKind::Return(value) = head.kind() {
            if let TypedValueKind::Var {
                name,
                instantiation,
            } = &value.kind
            {
                if instantiation.is_empty() && aliases.contains(name) {
                    aliases.insert(binder.name());
                    current = tail;
                    continue;
                }
            }
        }
        if !matches!(
            head.kind(),
            TypedCompKind::Return(_) | TypedCompKind::Prim(..)
        ) || !free_comp_vars(head).is_disjoint(&aliases)
        {
            return None;
        }
        prefix.push(((**head).clone(), binder.clone()));
        current = tail;
    }
}

fn function_applied_once_tail(comp: &TypedComp, function: Sym) -> bool {
    let mut aliases = BTreeSet::from([function]);
    let mut current = comp;
    loop {
        match current.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let Some(callee) = forced_var(callee) else {
                    return false;
                };
                return instantiation.is_empty()
                    && aliases.contains(&callee)
                    && args.len() == 1
                    && free_value_vars(&args[0]).is_disjoint(&aliases);
            }
            TypedCompKind::Bind(head, binder, tail) => {
                if let TypedCompKind::Return(value) = head.kind() {
                    if let TypedValueKind::Var {
                        name,
                        instantiation,
                    } = &value.kind
                    {
                        if instantiation.is_empty() && aliases.contains(name) {
                            aliases.insert(binder.name());
                            current = tail;
                            continue;
                        }
                    }
                }
                if !free_comp_vars(head).is_disjoint(&aliases) {
                    return false;
                }
                current = tail;
            }
            _ => return false,
        }
    }
}

/// Translate computations into the row-indexed effect runtime while retaining
/// the source type of every value stored in its existential word slots.
pub(super) struct Monadic<'a> {
    ops: &'a OpIds,
    fresh: &'a mut Fresh,
    row: EffRow,
    calls: &'a BTreeMap<Sym, CoreFnSig>,
    generated: Vec<TypedCoreFn>,
    generated_signatures: BTreeMap<Sym, CoreFnSig>,
    quantifiers: Vec<CoreQuantifier>,
    locals: BTreeMap<Sym, CoreType>,
    word_binders: BTreeMap<Sym, CoreType>,
    resume_aliases: BTreeSet<Sym>,
    resume_representation: ResumeRepresentation,
    region_plan: Option<&'a MonadicRegionPlan>,
    latent: Option<&'a Latent>,
    native_enabled: bool,
    whole_values: bool,
}

impl<'a> Monadic<'a> {
    pub(super) const fn new(
        ops: &'a OpIds,
        fresh: &'a mut Fresh,
        row: EffRow,
        calls: &'a BTreeMap<Sym, CoreFnSig>,
    ) -> Self {
        Self {
            ops,
            fresh,
            row,
            calls,
            generated: Vec::new(),
            generated_signatures: BTreeMap::new(),
            quantifiers: Vec::new(),
            locals: BTreeMap::new(),
            word_binders: BTreeMap::new(),
            resume_aliases: BTreeSet::new(),
            resume_representation: ResumeRepresentation::Continuation,
            region_plan: None,
            latent: None,
            native_enabled: false,
            whole_values: false,
        }
    }

    fn set_row(&mut self, row: EffRow) {
        self.row = row;
    }

    const fn use_whole_value_convention(&mut self) {
        self.whole_values = true;
    }

    fn call_instantiation(
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

    const fn configure_region(
        &mut self,
        plan: &'a MonadicRegionPlan,
        latent: &'a Latent,
        native_enabled: bool,
    ) {
        self.region_plan = Some(plan);
        self.latent = Some(latent);
        self.native_enabled = native_enabled;
    }

    fn mint(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }

    const fn var(name: Sym, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name,
                instantiation: Vec::new(),
            },
        )
    }

    fn lam(params: Vec<TypedBinder>, body: TypedComp) -> TypedComp {
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
        let saved: Vec<(Sym, Option<CoreType>, Option<CoreType>, bool)> = binders
            .iter()
            .map(|binder| {
                (
                    binder.name(),
                    self.locals.insert(binder.name(), binder.ty().clone()),
                    self.word_binders.remove(&binder.name()),
                    self.resume_aliases.remove(&binder.name()),
                )
            })
            .collect();
        let result = f(self);
        for (name, local, word, resume) in saved.into_iter().rev() {
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

    fn value(&mut self, value: &TypedValue) -> Option<TypedValue> {
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
                if !self.whole_style() {
                    return Some(value.clone());
                }
                let body = match body.kind() {
                    TypedCompKind::Lam(params, inner) => Self::lam_with(
                        Self::lam_quantifiers(body),
                        params.clone(),
                        self.with_source_binders(params, |this| this.comp(inner))?,
                    ),
                    _ => self.comp(body)?,
                };
                TypedValue::new(
                    CoreType::Thunk(Box::new(body.sig().clone())),
                    TypedValueKind::Thunk(Box::new(body)),
                )
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
    pub(super) fn comp(&mut self, comp: &TypedComp) -> Option<TypedComp> {
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
                let monadic_tail =
                    self.with_word_binder(binder, resume_alias, |this| this.comp(tail))?;
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
                        callee: Sym::from("ebind"),
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
                if !self.whole_style() && self.resume_head(callee).is_none() {
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
        let value = self.direct_argument(value);
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
        let CoreType::Thunk(signature) = resume.ty().clone() else {
            unreachable!("the resume ABI is a thunk")
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
        let driver = self.mint("mask");
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

    fn unwrap_entry(&mut self, body: TypedComp, result_ty: CoreType) -> TypedComp {
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

    fn handler_is_open(&self, comp: &TypedComp) -> bool {
        match (self.region_plan, self.latent) {
            (Some(plan), Some(latent)) => plan.handler_is_open(comp, latent),
            _ => true,
        }
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

    fn try_handle_native_function_answer(
        &mut self,
        comp: &TypedComp,
        function: &TypedBinder,
        continuation: &TypedComp,
    ) -> Option<FnAnswerLowering> {
        let TypedCompKind::Handle {
            body,
            return_binder: Some(return_binder),
            return_body,
            ops,
        } = comp.kind()
        else {
            return Some(FnAnswerLowering::Declined);
        };
        let (Some(plan), Some(latent)) = (self.region_plan, self.latent) else {
            return Some(FnAnswerLowering::Declined);
        };
        if !plan.native_closed(comp, latent, self.native_enabled)
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
        let region = self.mint("region");
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

    fn direct(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        Some(match comp.kind() {
            TypedCompKind::Bind(head, binder, body) => {
                match self.try_handle_native_function_answer(head, binder, body)? {
                    FnAnswerLowering::Lowered(native) => *native,
                    FnAnswerLowering::Declined => {
                        let head = self.direct(head)?;
                        let body = self
                            .with_source_binders(std::slice::from_ref(binder), |this| {
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
                    condition.clone(),
                    Box::new(self.direct(yes)?),
                    Box::new(self.direct(no)?),
                ),
            ),
            TypedCompKind::Case(scrutinee, arms) => {
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
                    TypedCompKind::Case(scrutinee.clone(), arms),
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
                        args: args.iter().map(|a| self.direct_argument(a)).collect(),
                    },
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
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
            TypedCompKind::Force(value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Force(self.direct_argument(value)),
            ),
            _ => comp.clone(),
        })
    }

    // A source binder the monadic transform reified into a Word continuation
    // parameter reads back as `Lowered(Word)`; a residual App/Call/Force that
    // still references it must cross back through the word representation, or the
    // reference type contradicts the word-typed binder. Non-word references pass
    // through untouched. Row/representation-only, so erased Core is unchanged.
    fn direct_argument(&self, argument: &TypedValue) -> TypedValue {
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
    fn direct_argument_at(&self, argument: &TypedValue, expected: &CoreType) -> Option<TypedValue> {
        Self::retag_runtime_word(self.direct_argument(argument), expected.clone())
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

    fn native_eligible(&self, comp: &TypedComp) -> bool {
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
        let (Some(plan), Some(latent)) = (self.region_plan, self.latent) else {
            return false;
        };
        plan.native_eligible(comp, latent, self.native_enabled)
    }

    fn handle_native(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
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
        let region = self.mint("region");
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

    fn handle(&mut self, comp: &TypedComp, open: bool) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } = comp.kind()
        else {
            return None;
        };
        if return_binder.is_some() != return_body.is_some() || ops.arms().is_empty() {
            return None;
        }
        let captures = self.handler_captures(comp)?;

        let driver = self.mint("handle");
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
        let pure_body = if let (Some(binder), Some(return_body)) = (return_binder, return_body) {
            let mut scope = captures.clone();
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
        };
        let pure_arm = (abi::epure_pattern(self.row.clone(), pure_value), pure_body);

        let id = TypedBinder::new(self.mint("id"), CoreType::Source(Type::Int));
        let skip = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
        let argument = TypedBinder::new(self.mint("arg"), abi::word());
        let queue = TypedBinder::new(self.mint("k"), abi::queue(self.row.clone()));

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
                Self::var(argument.name(), argument.ty().clone()),
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
            handled = Self::bind_operation_params(operation.params(), &argument, handled)?;
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

            let selected = if open {
                let decremented = TypedBinder::new(self.mint("sk"), CoreType::Source(Type::Int));
                let forwarded = self.forward_eop(
                    Self::var(id.name(), id.ty().clone()),
                    Self::var(decremented.name(), decremented.ty().clone()),
                    Self::var(argument.name(), argument.ty().clone()),
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

        let op_arm = (
            abi::eop_pattern(self.row.clone(), id, skip, argument, queue),
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
}

fn monadic_quantifiers(function: &TypedCoreFn, row: &EffRow) -> Vec<CoreQuantifier> {
    let mut quantifiers = function.sig().quantifiers().to_vec();
    if let EffRow::Var(ambient) = row.tail() {
        if !quantifiers.contains(&CoreQuantifier::Row(*ambient)) {
            quantifiers.push(CoreQuantifier::Row(*ambient));
        }
    }
    quantifiers
}

/// Put every function in one monadic calling convention. Each declaration's
/// row retains the direct effects that remain after source operations are
/// reified; call instantiation aligns the callee with its current caller.
pub(super) fn lower_whole<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
) -> Option<Vec<TypedCoreFn>> {
    let signatures: BTreeMap<Sym, CoreFnSig> = functions
        .iter()
        .map(|function| {
            let row = rows.row(function.name())?;
            Some((
                function.name(),
                CoreFnSig::new(
                    monadic_quantifiers(function, &row),
                    function.sig().params().to_vec(),
                    CompSig::new(abi::eff(row.clone()), row),
                ),
            ))
        })
        .collect::<Option<_>>()?;
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    monadic.use_whole_value_convention();
    let mut lowered = Vec::with_capacity(functions.len());
    for function in functions {
        let row = rows.row(function.name())?;
        monadic.set_row(row.clone());
        monadic.quantifiers = monadic_quantifiers(function, &row);
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        // A resume alias belongs to one handler's dynamic scope; it must not
        // leak into the next function, or a plain source binder that happens to
        // share the continuation's name (a map's key `k` beside a handler's
        // `resume k`) is mistyped as the reified continuation. `lower_region`
        // already clears this per member; whole-program lowering must match.
        monadic.resume_aliases.clear();
        let body = monadic.comp(function.body())?;
        let entry = function.name().as_str() == ENTRY_POINT;
        let body = if entry {
            monadic.unwrap_entry(body, function.sig().body().result().clone())
        } else {
            body
        };
        let signature = if entry {
            CoreFnSig::new(
                monadic_quantifiers(function, &row),
                function.sig().params().to_vec(),
                CompSig::new(function.sig().body().result().clone(), row.clone()),
            )
        } else {
            signatures.get(&function.name())?.clone()
        };
        lowered.push(TypedCoreFn::new(
            function.name(),
            function.params().to_vec(),
            body,
            signature,
            function.dict_arity(),
        ));
    }
    lowered.append(&mut monadic.generated);
    Some(lowered)
}

/// Lower one clean `LocalPartial` component in the whole-style convention while
/// retaining direct signatures for the fused rest's inert callees. Region
/// entries unwrap their `Eff` result for the direct caller across the split.
pub(super) fn lower_region<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    region: &BTreeSet<Sym>,
    entries: &BTreeSet<Sym>,
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
) -> Result<Vec<TypedCoreFn>, String> {
    let planned_rows: BTreeMap<Sym, EffRow> = functions
        .iter()
        .filter(|function| region.contains(&function.name()))
        .map(|function| {
            rows.row(function.name())
                .map(|row| (function.name(), row))
                .ok_or_else(|| {
                    format!(
                        "LocalPartial member `{}` has no residual-row plan",
                        function.name()
                    )
                })
        })
        .collect::<Result<_, _>>()?;
    if let Some(missing) = region.iter().find(|name| !planned_rows.contains_key(name)) {
        return Err(format!(
            "LocalPartial plan names missing declaration `{missing}`"
        ));
    }
    let signatures: BTreeMap<Sym, CoreFnSig> = functions
        .iter()
        .map(|function| {
            let signature = if region.contains(&function.name()) {
                let row = planned_rows.get(&function.name()).ok_or_else(|| {
                    format!(
                        "LocalPartial member `{}` lost its residual-row plan",
                        function.name()
                    )
                })?;
                CoreFnSig::new(
                    monadic_quantifiers(function, row),
                    function.sig().params().to_vec(),
                    CompSig::new(abi::eff(row.clone()), row.clone()),
                )
            } else {
                function.sig().clone()
            };
            Ok((function.name(), signature))
        })
        .collect::<Result<_, String>>()?;
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    monadic.use_whole_value_convention();
    let mut lowered = Vec::with_capacity(region.len());
    for function in functions
        .iter()
        .filter(|function| region.contains(&function.name()))
    {
        let row = planned_rows.get(&function.name()).ok_or_else(|| {
            format!(
                "LocalPartial member `{}` lost its prepared row",
                function.name()
            )
        })?;
        monadic.set_row(row.clone());
        monadic.quantifiers = monadic_quantifiers(function, row);
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        monadic.resume_aliases.clear();
        let body = monadic.comp(function.body()).ok_or_else(|| {
            format!(
                "LocalPartial member `{}` failed after its region plan committed",
                function.name()
            )
        })?;
        let entry = entries.contains(&function.name());
        let body = if entry {
            monadic.unwrap_entry(body, function.sig().body().result().clone())
        } else {
            body
        };
        let signature = if entry {
            CoreFnSig::new(
                monadic_quantifiers(function, row),
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    body.sig().effects().clone(),
                ),
            )
        } else {
            signatures.get(&function.name()).cloned().ok_or_else(|| {
                format!(
                    "LocalPartial member `{}` lost its prepared signature",
                    function.name()
                )
            })?
        };
        lowered.push(TypedCoreFn::new(
            function.name(),
            function.params().to_vec(),
            body,
            signature,
            function.dict_arity(),
        ));
    }
    lowered.append(&mut monadic.generated);
    Ok(lowered)
}

/// Lower only declarations selected by a pre-rewrite region plan. Functions
/// outside the region keep their source convention and are traversed only to
/// discharge closed handlers; region entries unwrap their `Eff` result for the
/// direct caller named by the plan.
pub(super) fn lower_selective<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
    plan: &MonadicRegionPlan,
    latent: &Latent,
    native_enabled: bool,
) -> Option<Vec<TypedCoreFn>> {
    if plan.scope != MonadicScope::Selective {
        return None;
    }
    let signatures: BTreeMap<Sym, CoreFnSig> = functions
        .iter()
        .map(|function| {
            let signature = if plan.members.contains(&function.name()) {
                let row = rows.row(function.name())?;
                CoreFnSig::new(
                    monadic_quantifiers(function, &row),
                    function.sig().params().to_vec(),
                    CompSig::new(abi::eff(row.clone()), row),
                )
            } else {
                function.sig().clone()
            };
            Some((function.name(), signature))
        })
        .collect::<Option<_>>()?;
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    monadic.configure_region(plan, latent, native_enabled);
    let mut lowered = Vec::with_capacity(functions.len());
    for function in functions {
        let member = plan.members.contains(&function.name());
        if member {
            let row = rows.row(function.name())?;
            monadic.set_row(row.clone());
            monadic.quantifiers = monadic_quantifiers(function, &row);
        } else {
            monadic.set_row(function.sig().body().effects().clone());
            monadic.quantifiers = function.sig().quantifiers().to_vec();
        }
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        monadic.resume_aliases.clear();
        let entry = plan.entries.contains(&function.name());
        let body = if member {
            let body = monadic.comp(function.body())?;
            if entry {
                monadic.unwrap_entry(body, function.sig().body().result().clone())
            } else {
                body
            }
        } else {
            monadic.direct(function.body())?
        };
        let signature = if member && !entry {
            signatures.get(&function.name())?.clone()
        } else {
            CoreFnSig::new(
                if member {
                    monadic_quantifiers(function, &rows.row(function.name())?)
                } else {
                    function.sig().quantifiers().to_vec()
                },
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    body.sig().effects().clone(),
                ),
            )
        };
        monadic
            .generated_signatures
            .insert(function.name(), signature.clone());
        lowered.push(TypedCoreFn::new(
            function.name(),
            function.params().to_vec(),
            body,
            signature,
            function.dict_arity(),
        ));
    }
    lowered.append(&mut monadic.generated);
    Some(lowered)
}

#[cfg(test)]
mod tests {
    use super::super::super::{
        CoreFnSig, EffectLowered, Elaborated, TypedCore, TypedCoreFn, TypedHandleOp, TypedHandler,
    };
    use super::*;
    use crate::core::cbpv::{Comp, CoreOp, CorePat, Value};
    use crate::core::typed::verify::{verify, VerifyEnv};

    struct MissingRows;

    impl Rows for MissingRows {
        fn row(&self, _function: Sym) -> Option<EffRow> {
            None
        }
    }

    #[test]
    fn call_instantiation_rewrites_only_the_answer_row_quantifier() {
        let unrelated = Sym::from("unrelated");
        let answer = Sym::from("answer");
        let signature = CoreFnSig::new(
            vec![CoreQuantifier::Row(unrelated), CoreQuantifier::Row(answer)],
            Vec::new(),
            CompSig::new(
                CoreType::Source(Type::Int),
                EffRow::canonical([crate::types::ty::Label::bare("Need")], EffRow::Var(answer)),
            ),
        );
        let source = vec![
            CoreInstantiation::Row(EffRow::canonical(
                [crate::types::ty::Label::bare("Left")],
                EffRow::Var(Sym::from("outer")),
            )),
            CoreInstantiation::Row(EffRow::canonical(
                [crate::types::ty::Label::bare("Old")],
                EffRow::Var(Sym::from("source")),
            )),
        ];
        let expected_answer = EffRow::canonical(
            [crate::types::ty::Label::bare("Keep")],
            EffRow::Var(Sym::from(names::FREE_MONAD_ROW)),
        );
        let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
        let calls = BTreeMap::new();
        let mut fresh = Fresh::new();
        let mut monadic = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls);
        monadic.set_row(EffRow::canonical(
            [
                crate::types::ty::Label::bare("Keep"),
                crate::types::ty::Label::bare("Need"),
            ],
            EffRow::Var(Sym::from(names::FREE_MONAD_ROW)),
        ));
        let rewritten = monadic
            .call_instantiation(&signature, &source)
            .expect("ambient call instantiation");
        assert_eq!(rewritten[0], source[0], "unrelated row stays unchanged");
        assert_eq!(
            rewritten[1],
            CoreInstantiation::Row(expected_answer),
            "only the declaration answer row becomes ambient"
        );

        monadic.set_row(EffRow::canonical(
            [
                crate::types::ty::Label::bare("Keep"),
                crate::types::ty::Label::bare("Need"),
            ],
            EffRow::Var(Sym::from("ordinary")),
        ));
        assert_eq!(
            monadic.call_instantiation(&signature, &source),
            Some(source),
            "outside the free-monad ambient the source instantiation is unchanged"
        );
    }

    #[test]
    fn direct_call_retags_higher_order_arguments_at_the_answer_row() {
        let callee = Sym::from("apply");
        let function = Sym::from("f");
        let answer = Sym::from("answer");
        let source = Sym::from("source");
        let ambient = Sym::from(names::FREE_MONAD_ROW);
        let callable = |row| {
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    vec![CoreType::Source(Type::Unit)],
                    CompSig::new(CoreType::Source(Type::Int), row),
                ))),
                EffRow::Empty,
            )))
        };
        let declaration = CoreFnSig::new(
            vec![CoreQuantifier::Row(answer)],
            vec![callable(EffRow::Var(answer))],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Var(answer)),
        );
        let source_instantiation = vec![CoreInstantiation::Row(EffRow::Var(source))];
        let source_signature =
            instantiate_fn(&declaration, &source_instantiation).expect("source signature");
        let source_argument = TypedValue::new(
            callable(EffRow::Var(source)),
            TypedValueKind::Var {
                name: function,
                instantiation: Vec::new(),
            },
        );
        let call = TypedComp::new(
            source_signature.body().clone(),
            TypedCompKind::Call {
                callee,
                instantiation: source_instantiation,
                args: vec![source_argument],
            },
        );
        let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
        let calls = BTreeMap::from([(callee, declaration.clone())]);
        let mut fresh = Fresh::new();
        let mut monadic = Monadic::new(&ops, &mut fresh, EffRow::Var(ambient), &calls);

        let rewritten = monadic.direct(&call).expect("direct call");
        let TypedCompKind::Call {
            instantiation,
            args,
            ..
        } = rewritten.kind()
        else {
            panic!("direct call stays a call");
        };
        let signature = instantiate_fn(&declaration, instantiation).expect("rewritten signature");
        assert_eq!(args[0].ty(), &signature.params()[0]);
        assert_eq!(rewritten.clone().erase(), call.erase());
    }

    #[test]
    fn local_region_rejects_an_incomplete_plan_before_minting_names() {
        let name = Sym::from("member");
        let body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(0),
            )),
        );
        let function = TypedCoreFn::new(
            name,
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        let ops = OpIds::assign(&BTreeSet::new()).expect("the empty operation plan is valid");
        let mut fresh = Fresh::new();
        let error = lower_region(
            &[function],
            &BTreeSet::from([name]),
            &BTreeSet::new(),
            &ops,
            &mut fresh,
            &MissingRows,
        )
        .expect_err("a committed LocalPartial plan requires every residual row");
        assert!(error.contains("has no residual-row plan"));
        assert_eq!(fresh.bump(), 0, "planning failures cannot consume names");
    }

    fn source_int_thunk() -> TypedValue {
        let body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )),
        );
        let function = CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone());
        let lambda = TypedComp::new(
            CompSig::new(CoreType::Function(Box::new(function)), EffRow::Empty),
            TypedCompKind::Lam(Vec::new(), Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        )
    }

    #[test]
    fn bind_and_operation_translate_exactly_and_verify() {
        let operation = Sym::from("Ask.ask");
        let mut operation_set = std::collections::BTreeSet::new();
        operation_set.insert(operation);
        let ops = OpIds::assign(&operation_set).expect("one operation has an id");
        let x = TypedBinder::new(Sym::from("x"), CoreType::Source(Type::Int));
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(41),
                )],
            },
        );
        let returned = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Return(Monadic::var(x.name(), x.ty().clone())),
        );
        let source = TypedComp::new(
            returned.sig().clone(),
            TypedCompKind::Bind(Box::new(performed), x.clone(), Box::new(returned)),
        );
        let mut fresh = Fresh::new();
        let calls = BTreeMap::new();
        let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
            .comp(&source)
            .expect("closed structural translation");
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let core = TypedCore::<EffectLowered>::new(vec![main, abi::ebind_fn(), abi::qapply_fn()]);
        assert_eq!(verify(&core, &env), Ok(()));

        let m = Sym::from(names::lowered("m", 0));
        assert_eq!(
            body.erase(),
            Comp::Bind(
                Box::new(Comp::Return(Value::Ctor(
                    Sym::from("EOp"),
                    1,
                    vec![Value::Int(0), Value::Int(0), Value::Int(41), Value::Unit],
                ))),
                m,
                Box::new(Comp::Call(
                    Sym::from("ebind"),
                    vec![
                        Value::Var(m),
                        Value::Thunk(Box::new(Comp::Lam(
                            vec![x.name()],
                            Box::new(Comp::Return(Value::Ctor(
                                Sym::from("EPure"),
                                0,
                                vec![Value::Var(x.name())],
                            ))),
                        ))),
                    ],
                )),
            )
        );
    }

    #[test]
    fn tuple_fields_keep_their_declared_thunk_witness() {
        let thunk = source_int_thunk();
        let function_type = Type::Fun(Vec::new(), EffRow::Empty, Box::new(Type::Int));
        let tuple = TypedValue::new(
            CoreType::Source(Type::Tuple(vec![function_type.clone()])),
            TypedValueKind::Tuple(vec![thunk.clone()]),
        );
        let unboxed = TypedValue::new(
            CoreType::Source(Type::UnboxedTuple(vec![function_type])),
            TypedValueKind::UnboxedTuple(vec![thunk]),
        );
        let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
        let calls = BTreeMap::new();
        let mut fresh = Fresh::new();
        let mut monadic = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls);
        let transformed = monadic.value(&tuple).expect("tuple transforms");
        assert_eq!(monadic.value(&unboxed), Some(unboxed));

        let body = TypedComp::new(
            CompSig::new(tuple.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(transformed),
        );
        let function = TypedCoreFn::new(
            Sym::from("tuple_fixture"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(&TypedCore::<EffectLowered>::new(vec![function]), &env),
            Ok(())
        );
    }

    #[test]
    fn a_region_call_retags_a_monadified_thunk_to_its_parameter() {
        let thunk = source_int_thunk();
        let callee_name = Sym::from("consume");
        let callee_signature = CoreFnSig::new(
            Vec::new(),
            vec![thunk.ty().clone()],
            CompSig::new(abi::eff(EffRow::Empty), EffRow::Empty),
        );
        let calls = BTreeMap::from([(callee_name, callee_signature.clone())]);
        let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
        let source_call = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Call {
                callee: callee_name,
                instantiation: Vec::new(),
                args: vec![thunk],
            },
        );
        let mut fresh = Fresh::new();
        let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
            .comp(&source_call)
            .expect("region call transforms");

        let parameter = TypedBinder::new(Sym::from("action"), callee_signature.params()[0].clone());
        let callee_body = abi::epure(
            abi::lowered_repr(
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(0)),
                abi::word(),
            ),
            EffRow::Empty,
        );
        let consumer = TypedCoreFn::new(
            callee_name,
            vec![parameter],
            callee_body,
            callee_signature,
            0,
        );
        let invocation = TypedCoreFn::new(
            Sym::from("caller"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(
                &TypedCore::<EffectLowered>::new(vec![consumer, invocation]),
                &env,
            ),
            Ok(())
        );
    }

    #[test]
    fn dynamic_lambda_application_uses_the_monadic_convention() {
        let ops = OpIds::assign(&std::collections::BTreeSet::new()).expect("empty op table");
        let x = TypedBinder::new(Sym::from("x"), CoreType::Source(Type::Int));
        let returned = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Return(Monadic::var(x.name(), x.ty().clone())),
        );
        let lambda = Monadic::lam(vec![x.clone()], returned);
        let source = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(lambda),
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(7),
                )],
            },
        );
        let mut fresh = Fresh::new();
        let calls = BTreeMap::new();
        let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
            .comp(&source)
            .expect("dynamic application translates");
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(&TypedCore::<EffectLowered>::new(vec![main]), &env),
            Ok(())
        );
        assert_eq!(
            body.erase(),
            Comp::App(
                Box::new(Comp::Lam(
                    vec![x.name()],
                    Box::new(Comp::Return(Value::Ctor(
                        Sym::from("EPure"),
                        0,
                        vec![Value::Var(x.name())],
                    ))),
                )),
                vec![Value::Int(7)],
            )
        );
    }

    #[test]
    fn whole_program_direct_calls_share_the_monadic_signature() {
        let ops = OpIds::assign(&std::collections::BTreeSet::new()).expect("empty op table");
        let x = TypedBinder::new(Sym::from("x"), CoreType::Source(Type::Int));
        let id_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Return(Monadic::var(x.name(), x.ty().clone())),
        );
        let id = TypedCoreFn::new(
            Sym::from("id"),
            vec![x.clone()],
            id_body.clone(),
            CoreFnSig::new(Vec::new(), vec![x.ty().clone()], id_body.sig().clone()),
            0,
        );
        let main_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Call {
                callee: id.name(),
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(7),
                )],
            },
        );
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            main_body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), main_body.sig().clone()),
            0,
        );
        let mut fresh = Fresh::new();
        let lowered = lower_whole(&[id, main], &ops, &mut fresh, &EffRow::Empty)
            .expect("whole-program convention closes direct calls");
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(&TypedCore::<EffectLowered>::new(lowered.clone()), &env),
            Ok(())
        );
        assert_eq!(
            lowered
                .into_iter()
                .map(|function| function.erase().body)
                .collect::<Vec<_>>(),
            vec![
                Comp::Return(Value::Ctor(
                    Sym::from("EPure"),
                    0,
                    vec![Value::Var(x.name())],
                )),
                Comp::Bind(
                    Box::new(Comp::Call(Sym::from("id"), vec![Value::Int(7)])),
                    Sym::from(names::lowered("r", 0)),
                    Box::new(Comp::Case(
                        Value::Var(Sym::from(names::lowered("r", 0))),
                        vec![
                            (
                                CorePat::Ctor(
                                    Sym::from("EPure"),
                                    vec![Some(Sym::from(names::lowered("x", 1)))],
                                ),
                                Comp::Return(Value::Var(Sym::from(names::lowered("x", 1)))),
                            ),
                            (
                                CorePat::Ctor(
                                    Sym::from("EOp"),
                                    vec![
                                        Some(Sym::from(names::lowered("id", 2))),
                                        Some(Sym::from("_us")),
                                        Some(Sym::from("_ua")),
                                        Some(Sym::from("_uk")),
                                    ],
                                ),
                                Comp::Error(Value::Str("unhandled effect".into())),
                            ),
                        ],
                    )),
                ),
            ]
        );
    }

    #[test]
    fn a_direct_primitive_is_lifted_once_and_exactly() {
        let ops = OpIds::assign(&std::collections::BTreeSet::new()).expect("empty op table");
        let source = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Prim(
                CoreOp::Add,
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(2)),
            ),
        );
        let calls = BTreeMap::new();
        let mut fresh = Fresh::new();
        let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
            .comp(&source)
            .expect("primitive lifts");
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
            0,
        );
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(&TypedCore::<EffectLowered>::new(vec![main]), &env),
            Ok(())
        );
        let p = Sym::from(names::lowered("p", 0));
        assert_eq!(
            body.erase(),
            Comp::Bind(
                Box::new(Comp::Prim(CoreOp::Add, Value::Int(1), Value::Int(2))),
                p,
                Box::new(Comp::Return(Value::Ctor(
                    Sym::from("EPure"),
                    0,
                    vec![Value::Var(p)],
                ))),
            )
        );
    }

    #[test]
    fn a_captured_open_nary_handler_erases_exactly_to_the_executable_driver() {
        let operation = Sym::from("Ask.ask");
        let escaping = Sym::from("Leak.leak");
        let mut operation_set = std::collections::BTreeSet::new();
        operation_set.insert(operation);
        operation_set.insert(escaping);
        let ops = OpIds::assign(&operation_set).expect("two operations have ids");
        let captured_a = TypedBinder::new(Sym::from("a_offset"), CoreType::Source(Type::Int));
        let captured_z = TypedBinder::new(Sym::from("z_offset"), CoreType::Source(Type::Int));
        let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
        let extra = TypedBinder::new(Sym::from("unused_extra"), CoreType::Source(Type::Int));
        let resume_signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Int)],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        );
        let resume = TypedBinder::new(
            Sym::from("resume"),
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(resume_signature)),
                EffRow::Empty,
            ))),
        );
        let clause_result = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Prim(
                CoreOp::Add,
                Monadic::var(parameter.name(), parameter.ty().clone()),
                Monadic::var(captured_a.name(), captured_a.ty().clone()),
            ),
        );
        let escaped = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
            TypedCompKind::Do {
                operation: escaping,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let clause_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Leak")),
            TypedCompKind::Bind(
                Box::new(escaped),
                TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
                Box::new(clause_result),
            ),
        );
        let clause = TypedHandleOp::new(
            operation,
            Vec::new(),
            vec![parameter, extra],
            resume,
            clause_body,
        );
        let clauses = TypedHandler::new(vec![clause]).expect("one unique clause");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: vec![
                    TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
                    TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(9)),
                ],
            },
        );
        let handle_comp = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Handle {
                body: Box::new(performed),
                return_binder: Some(TypedBinder::new(
                    Sym::from("answer"),
                    CoreType::Source(Type::Int),
                )),
                return_body: Some(Box::new(TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                    TypedCompKind::Prim(
                        CoreOp::Add,
                        Monadic::var(Sym::from("answer"), CoreType::Source(Type::Int)),
                        Monadic::var(captured_z.name(), captured_z.ty().clone()),
                    ),
                ))),
                ops: clauses,
            },
        );
        let source_body = TypedComp::new(
            handle_comp.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                    TypedCompKind::Return(TypedValue::new(
                        CoreType::Source(Type::Int),
                        TypedValueKind::Int(40),
                    )),
                )),
                captured_z,
                Box::new(TypedComp::new(
                    handle_comp.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(TypedComp::new(
                            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                            TypedCompKind::Return(TypedValue::new(
                                CoreType::Source(Type::Int),
                                TypedValueKind::Int(2),
                            )),
                        )),
                        captured_a,
                        Box::new(handle_comp),
                    ),
                )),
            ),
        );
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            source_body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), source_body.sig().clone()),
            0,
        );
        let source = TypedCore::<Elaborated>::new(vec![main]);
        let mut fresh = Fresh::new();
        let mut lowered = lower_whole(&source.fns, &ops, &mut fresh, &EffRow::Empty)
            .expect("open handler translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_routed_resume_application_erases_exactly_and_verifies() {
        let operation = Sym::from("Ask.ask");
        let escaping = Sym::from("Leak.leak");
        let operation_set = BTreeSet::from([operation, escaping]);
        let ops = OpIds::assign(&operation_set).expect("two operations have ids");
        let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
        let resume_signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Int)],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        );
        let resume = TypedBinder::new(
            Sym::from("resume"),
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(resume_signature.clone())),
                EffRow::Empty,
            ))),
        );
        let routed = TypedBinder::new(Sym::from("routed_resume"), resume.ty().clone());
        let route = TypedComp::new(
            CompSig::new(resume.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(Monadic::var(resume.name(), resume.ty().clone())),
        );
        let force = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(resume_signature)),
                EffRow::Empty,
            ),
            TypedCompKind::Force(Monadic::var(routed.name(), routed.ty().clone())),
        );
        let apply = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![Monadic::var(parameter.name(), parameter.ty().clone())],
            },
        );
        let routed_body = TypedComp::new(
            apply.sig().clone(),
            TypedCompKind::Bind(Box::new(route), routed, Box::new(apply)),
        );
        let escaped = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
            TypedCompKind::Do {
                operation: escaping,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let clause_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Leak")),
            TypedCompKind::Bind(
                Box::new(escaped),
                TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
                Box::new(routed_body),
            ),
        );
        let clauses = TypedHandler::new(vec![TypedHandleOp::new(
            operation,
            Vec::new(),
            vec![parameter],
            resume,
            clause_body,
        )])
        .expect("one unique clause");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(7),
                )],
            },
        );
        let handled = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Handle {
                body: Box::new(performed),
                return_binder: None,
                return_body: None,
                ops: clauses,
            },
        );
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            handled.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), handled.sig().clone()),
            0,
        );
        let source = TypedCore::<Elaborated>::new(vec![main]);
        let mut fresh = Fresh::new();
        let mut lowered = lower_whole(&source.fns, &ops, &mut fresh, &EffRow::Empty)
            .expect("routed resume application translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_mask_driver_erases_exactly_and_verifies() {
        let operation = Sym::from("Ask.ask");
        let operation_set = BTreeSet::from([operation]);
        let ops = OpIds::assign(&operation_set).expect("one operation has an id");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(7),
                )],
            },
        );
        let masked = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Mask(vec![operation], Box::new(performed)),
        );
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            masked.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), masked.sig().clone()),
            0,
        );
        let source = TypedCore::<Elaborated>::new(vec![main]);
        let mut fresh = Fresh::new();
        let mut lowered = lower_whole(&source.fns, &ops, &mut fresh, &EffRow::Empty)
            .expect("mask driver translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_selective_closed_handler_keeps_the_direct_convention_exactly() {
        let operation = Sym::from("Ask.ask");
        let operation_set = BTreeSet::from([operation]);
        let ops = OpIds::assign(&operation_set).expect("one operation has an id");
        let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
        let resume_signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Int)],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        );
        let resume = TypedBinder::new(
            Sym::from("resume"),
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(resume_signature)),
                EffRow::Empty,
            ))),
        );
        let clause_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Return(Monadic::var(parameter.name(), parameter.ty().clone())),
        );
        let clauses = TypedHandler::new(vec![TypedHandleOp::new(
            operation,
            Vec::new(),
            vec![parameter],
            resume,
            clause_body,
        )])
        .expect("one unique clause");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(7),
                )],
            },
        );
        let handled = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Handle {
                body: Box::new(performed),
                return_binder: None,
                return_body: None,
                ops: clauses,
            },
        );
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            handled.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), handled.sig().clone()),
            0,
        );
        let source = TypedCore::<Elaborated>::new(vec![main]);
        let latent = super::super::latent::latent_map(&source.fns);
        let flow = super::super::flow::analyze(&source.fns, &latent);
        let plan = super::super::analysis::plan(&source.fns, &latent, &flow);
        assert_eq!(plan.scope, MonadicScope::Selective);

        let mut fresh = Fresh::new();
        let mut lowered = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &plan,
            &latent,
            false,
        )
        .expect("selective closed handler translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_closed_tail_resume_and_return_clause_use_the_native_region_exactly() {
        let operation = Sym::from("Ask.ask");
        let operation_set = BTreeSet::from([operation]);
        let ops = OpIds::assign(&operation_set).expect("one operation has an id");
        let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
        let resume_signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Int)],
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        );
        let resume = TypedBinder::new(
            Sym::from("resume"),
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(resume_signature.clone())),
                EffRow::Empty,
            ))),
        );
        let force = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(resume_signature)),
                EffRow::Empty,
            ),
            TypedCompKind::Force(Monadic::var(resume.name(), resume.ty().clone())),
        );
        let clause_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![Monadic::var(parameter.name(), parameter.ty().clone())],
            },
        );
        let clauses = TypedHandler::new(vec![TypedHandleOp::new(
            operation,
            Vec::new(),
            vec![parameter],
            resume,
            clause_body,
        )])
        .expect("one unique clause");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: vec![TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(7),
                )],
            },
        );
        let return_binder = TypedBinder::new(Sym::from("answer"), CoreType::Source(Type::Int));
        let return_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Prim(
                CoreOp::Add,
                Monadic::var(return_binder.name(), return_binder.ty().clone()),
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
            ),
        );
        let handled = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
            TypedCompKind::Handle {
                body: Box::new(performed),
                return_binder: Some(return_binder),
                return_body: Some(Box::new(return_body)),
                ops: clauses,
            },
        );
        let main = TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            handled.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), handled.sig().clone()),
            0,
        );
        let source = TypedCore::<Elaborated>::new(vec![main]);
        let latent = super::super::latent::latent_map(&source.fns);
        let flow = super::super::flow::analyze(&source.fns, &latent);
        let plan = super::super::analysis::plan(&source.fns, &latent, &flow);
        let mut fresh = Fresh::new();
        let mut lowered = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &plan,
            &latent,
            true,
        )
        .expect("native selective handler translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_generic_capture_is_scoped_by_the_generated_driver_scheme() {
        let operation = Sym::from("Ask.ask");
        let escaping = Sym::from("Leak.leak");
        let mut operation_set = std::collections::BTreeSet::new();
        operation_set.insert(operation);
        operation_set.insert(escaping);
        let ops = OpIds::assign(&operation_set).expect("two operations have ids");

        let a = Sym::from("a");
        let captured = TypedBinder::new(Sym::from("captured"), CoreType::Source(Type::Var(a)));
        let resume_signature = CoreFnSig::new(
            Vec::new(),
            vec![CoreType::Source(Type::Var(a))],
            CompSig::new(CoreType::Source(Type::Var(a)), EffRow::Empty),
        );
        let resume = TypedBinder::new(
            Sym::from("resume"),
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(resume_signature)),
                EffRow::Empty,
            ))),
        );
        let escaped = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
            TypedCompKind::Do {
                operation: escaping,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let clause_result = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Var(a)), EffRow::Empty),
            TypedCompKind::Return(Monadic::var(captured.name(), captured.ty().clone())),
        );
        let clause_body = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Var(a)), EffRow::singleton("Leak")),
            TypedCompKind::Bind(
                Box::new(escaped),
                TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
                Box::new(clause_result),
            ),
        );
        let clauses = TypedHandler::new(vec![TypedHandleOp::new(
            operation,
            Vec::new(),
            Vec::new(),
            resume,
            clause_body,
        )])
        .expect("one unique clause");
        let performed = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Var(a)), EffRow::singleton("Ask")),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let handle = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Var(a)), EffRow::Empty),
            TypedCompKind::Handle {
                body: Box::new(performed),
                return_binder: None,
                return_body: None,
                ops: clauses,
            },
        );
        let run = TypedCoreFn::new(
            Sym::from("run"),
            vec![captured.clone()],
            handle.clone(),
            CoreFnSig::new(
                vec![CoreQuantifier::Type(a)],
                vec![captured.ty().clone()],
                handle.sig().clone(),
            ),
            0,
        );

        let mut fresh = Fresh::new();
        let mut lowered = lower_whole(&[run], &ops, &mut fresh, &EffRow::Empty)
            .expect("generic captured handler translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(&TypedCore::<EffectLowered>::new(lowered), &env),
            Ok(())
        );
    }
}
