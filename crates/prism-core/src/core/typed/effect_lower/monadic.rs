//! Typed free-monad translation.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::builtins::Builtin;
use crate::core::cbpv::CoreOp;
use crate::core::effect_abi::{FreeMonadDriver, EBIND};
use crate::types::ty::EffRow;
use crate::types::Type;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;
use prism_syntax::names::ENTRY_POINT;

use super::super::specialize_support::{free_comp_vars, free_value_vars};
use super::super::verify::{instantiate_fn, lowered_representation_conversion};
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCoreFn, TypedHandleOp, TypedPattern, TypedValue, TypedValueKind,
};
use super::abi;
use super::analysis::{Effects, MonadicRegionPlan, MonadicScope};
use super::decline::{Decline, Refusal, Site};
use super::evidence::OpIds;
use super::flow::{self, ThunkFlow};
use super::latent::Latent;
use super::plan;
use super::residual::Rows;
use super::union_effects;
use super::walk;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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

/// The thunk a clause answers with, when its body has the parameter-passing
/// shape: a thunk over a lambda that the code around the handle applies once the
/// handle has returned. It is the one answer whose value is a computation rather
/// than a result, which is why the state path and the refusal below both ask for
/// it here rather than each re-reading the shape.
fn answered_thunk(body: &TypedComp) -> Option<(&TypedValue, &[TypedBinder], &TypedComp)> {
    let TypedCompKind::Return(value) = body.kind() else {
        return None;
    };
    let TypedValueKind::Thunk(lambda) = &value.kind else {
        return None;
    };
    let TypedCompKind::Lam(parameters, body) = lambda.kind() else {
        return None;
    };
    Some((value, parameters, body))
}

/// [`answered_thunk`](answered_thunk) without the value, for the state path,
/// which asks about the transformer's shape and never about its convention.
fn answered_lambda(body: &TypedComp) -> Option<(&[TypedBinder], &TypedComp)> {
    let (_, parameters, body) = answered_thunk(body)?;
    Some((parameters, body))
}

fn state_return(return_body: Option<&TypedComp>) -> Option<(TypedBinder, TypedComp)> {
    let (parameters, body) = answered_lambda(return_body?)?;
    let [state] = parameters else {
        return None;
    };
    Some((state.clone(), body.clone()))
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
    let (parameters, body) = answered_lambda(operation.body())?;
    let [state] = parameters else {
        return None;
    };
    let mut aliases = BTreeSet::from([operation.resume().name()]);
    let mut prefix = Vec::new();
    let mut current = body;
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

/// What a binder displaced when it entered scope, restored when it leaves.
struct Shadowed {
    name: Sym,
    local: Option<CoreType>,
    word: Option<CoreType>,
    resume: bool,
    signature: Option<flow::Sig>,
}

/// The confined-region facts a selective lowering consults: which declarations
/// share the free-monad convention, what each function can still perform, and
/// which suspended computations the region owns.
#[derive(Debug)]
pub struct Region<'a> {
    pub plan: &'a MonadicRegionPlan,
    pub latent: &'a Latent,
    pub flow: &'a ThunkFlow,
    pub native_enabled: bool,
}

/// Translate computations into the row-indexed effect runtime while retaining
/// the source type of every value stored in its existential word slots.
#[derive(Debug)]
pub struct Monadic<'a> {
    ops: &'a OpIds,
    fresh: &'a mut Fresh,
    row: EffRow,
    /// The row the monadic convention uses for a computation this declaration
    /// suspends. Equal to `row` wherever the declaration is itself monadic;
    /// outside a confined region it is the declaration's residual row instead,
    /// because a thunk the region owns performs what its own body performs and
    /// not what the declaration building it performs, while `row` has to stay
    /// the source row so the direct rewrite around it is left alone.
    suspension_row: EffRow,
    calls: &'a BTreeMap<Sym, CoreFnSig>,
    generated: Vec<TypedCoreFn>,
    generated_signatures: BTreeMap<Sym, CoreFnSig>,
    quantifiers: Vec<CoreQuantifier>,
    locals: BTreeMap<Sym, CoreType>,
    /// What forcing each thunk-valued binder in lexical scope can still
    /// perform, threaded beside `locals` because the convention a thunk was
    /// built at is not recoverable from its type: a monadic thunk and a direct
    /// one share the shape `Thunk(_)`, so the rewrite has to remember.
    thunk_sigs: flow::Loc,
    word_binders: BTreeMap<Sym, CoreType>,
    resume_aliases: BTreeSet<Sym>,
    resume_representation: ResumeRepresentation,
    region_plan: Option<&'a MonadicRegionPlan>,
    /// Why a confined attempt was refused, if one was. Carried rather than
    /// discarded so the plan artifact and the fallback warning can say why the
    /// program is paying for the wider region.
    refusal: Option<(Refusal, Site)>,
    latent: Option<&'a Latent>,
    flow: Option<&'a ThunkFlow>,
    native_enabled: bool,
}

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
    fn set_row(&mut self, row: EffRow) {
        self.suspension_row = row.clone();
        self.row = row;
    }

    /// Set the rows for a declaration the rewrite leaves at the direct
    /// convention while it may still build a computation the region owns.
    fn set_direct_row(&mut self, row: EffRow, suspension_row: EffRow) {
        self.row = row;
        self.suspension_row = suspension_row;
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

    const fn configure_region(&mut self, region: &Region<'a>) {
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

    fn direct(&mut self, comp: &TypedComp) -> Option<TypedComp> {
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

    /// Record why a confined attempt is refused, and decline. The first
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
    /// confined builder has no rewrite for at all, which is a refusal of its
    /// own kind rather than an unexplained one.
    const fn declined(&self, function: Sym) -> Decline {
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

    /// Whether any immediate value position of a computation writes material
    /// the region owns: a thunk it lowered, or a capture of the continuation a
    /// handler clause resumes through.
    fn holds_monadic_thunk(&self, comp: &TypedComp) -> bool {
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
    fn reads_reified_binder(&self, names: &BTreeSet<Sym>) -> bool {
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
    fn verbatim(&mut self, value: &TypedValue) -> Option<TypedValue> {
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
    fn direct_value(&mut self, value: &TypedValue) -> Option<TypedValue> {
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
    fn direct_argument(&mut self, argument: &TypedValue) -> Option<TypedValue> {
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
    fn direct_argument_at(
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
        let (Some(plan), Some(effects)) = (self.region_plan, self.effects()) else {
            return false;
        };
        plan.native_eligible(comp, effects, &self.thunk_sigs, self.native_enabled)
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

/// Put every function in one monadic calling convention.
///
/// Each declaration's row retains the direct effects that remain after source
/// operations are reified; call instantiation aligns the callee with its
/// current caller.
pub fn lower_whole<R: Rows + ?Sized>(
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
        // Thunk signatures are per-declaration for the same reason: they are
        // keyed by binder name, and two declarations share names freely.
        monadic.thunk_sigs.clear();
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
/// retaining direct signatures for the fused rest's inert callees.
///
/// Region entries unwrap their `Eff` result for the direct caller across the
/// split.
///
/// # Errors
/// A message when a region member has no planned row, or when its body has no
/// monadic rewrite.
pub fn lower_region<R: Rows + ?Sized>(
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
        monadic.thunk_sigs.clear();
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

/// Lower only declarations selected by a pre-rewrite region plan.
///
/// Functions outside the region keep their source convention and are traversed
/// only to discharge closed handlers; region entries unwrap their `Eff` result
/// for the direct caller named by the plan.
///
/// A refusal is returned rather than dropped: the caller answers it by widening
/// the plan, and what it answered is what the plan artifact and the fallback
/// warning report.
///
/// # Errors
/// The [`Decline`] the region recorded: the shape it has no confined rewrite
/// for, and where it met it.
///
/// # Panics
/// Panics if the plan is not a confined one. Which scope a plan carries is the
/// caller's to dispatch on, so a whole-program plan arriving here is a bug in
/// the cascade rather than a program the region refused.
pub fn lower_selective<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
    region: &Region<'_>,
) -> Result<Vec<TypedCoreFn>, Decline> {
    let plan = region.plan;
    assert_eq!(
        plan.scope,
        MonadicScope::Selective,
        "confined lowering needs a confined plan"
    );
    let mut signatures: BTreeMap<Sym, CoreFnSig> = BTreeMap::new();
    for function in functions {
        let signature = if plan.members.contains(&function.name()) {
            let row = rows
                .row(function.name())
                .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?;
            CoreFnSig::new(
                monadic_quantifiers(function, &row),
                function.sig().params().to_vec(),
                CompSig::new(abi::eff(row.clone()), row),
            )
        } else {
            function.sig().clone()
        };
        signatures.insert(function.name(), signature);
    }
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    monadic.configure_region(region);
    let mut lowered = Vec::with_capacity(functions.len());
    for function in functions {
        let member = plan.members.contains(&function.name());
        let missing_row = || Decline::whole(Refusal::MissingRow, function.name());
        if member {
            let row = rows.row(function.name()).ok_or_else(missing_row)?;
            monadic.set_row(row.clone());
            monadic.quantifiers = monadic_quantifiers(function, &row);
        } else {
            // A declaration outside the region keeps its source row, but the
            // computations it suspends for the region reify what its residual
            // plan says the declaration's whole body performs, thunks included.
            // Those labels sit over the declaration's own tail rather than the
            // region's: only a member quantifies the phase-private row, so a
            // suspension built here has to stay inside the rows the direct
            // declaration already binds.
            let source = function.sig().body().effects().clone();
            let residual = rows.row(function.name()).ok_or_else(missing_row)?;
            monadic.set_direct_row(
                source.clone(),
                EffRow::canonical(
                    residual.labels().into_iter().cloned(),
                    source.tail().clone(),
                ),
            );
            monadic.quantifiers = function.sig().quantifiers().to_vec();
        }
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        monadic.resume_aliases.clear();
        // Seed the scope from the interprocedural solution: what flowed into
        // each thunk-valued parameter is what forcing that parameter performs,
        // and reading it from the same place the plan did is what keeps the
        // membership decision and the rewrite from disagreeing.
        monadic.thunk_sigs = flow::param_loc(function, region.flow);
        let entry = plan.entries.contains(&function.name());
        let rewritten = if member {
            monadic.comp(function.body())
        } else {
            monadic.direct(function.body())
        };
        let Some(body) = rewritten else {
            return Err(monadic.declined(function.name()));
        };
        let body = if member && entry {
            monadic.unwrap_entry(body, function.sig().body().result().clone())
        } else {
            body
        };
        let signature = if member && !entry {
            signatures
                .get(&function.name())
                .ok_or_else(missing_row)?
                .clone()
        } else if member {
            CoreFnSig::new(
                monadic_quantifiers(
                    function,
                    &rows.row(function.name()).ok_or_else(missing_row)?,
                ),
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    body.sig().effects().clone(),
                ),
            )
        } else {
            CoreFnSig::new(
                function.sig().quantifiers().to_vec(),
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    // A declaration outside the region may only ever *widen*: the
                    // rewrite can add a residual effect, and the verifier admits a
                    // body row that is a subrow of the declaration, so a body whose
                    // recomputed row is narrower than the source row must not pull
                    // the declaration down with it. Narrowing here breaks every
                    // call node already emitted against the wider row, and the
                    // first of those is the declaration's own recursive call,
                    // rewritten before this signature exists.
                    union_effects(function.sig().body().effects(), body.sig().effects()),
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
    Ok(lowered)
}

#[cfg(test)]
mod tests {
    use super::super::super::{
        CoreFnSig, EffectLowered, Elaborated, TypedCore, TypedCoreFn, TypedHandleOp, TypedHandler,
    };
    use super::super::fixtures;
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
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let latent = effects.latent();
        let plan = super::super::analysis::plan(&source.fns, &effects, false);
        assert_eq!(plan.scope, MonadicScope::Selective);

        let mut fresh = Fresh::new();
        let mut lowered = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &Region {
                plan: &plan,
                latent,
                flow: effects.flow(),
                native_enabled: false,
            },
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
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let latent = effects.latent();
        let plan = super::super::analysis::plan(&source.fns, &effects, false);
        let mut fresh = Fresh::new();
        let mut lowered = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &Region {
                plan: &plan,
                latent,
                flow: effects.flow(),
                native_enabled: true,
            },
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

    #[test]
    fn a_confined_region_translates_and_leaves_no_raw_effects() {
        let ops = OpIds::assign(&BTreeSet::from([Sym::from(fixtures::ASK_OP)]))
            .expect("one operation has an id");
        let functions = fixtures::capturing_program();
        let source = TypedCore::<Elaborated>::new(functions);
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let plan = super::super::analysis::plan(&source.fns, &effects, false);
        assert_eq!(plan.scope, MonadicScope::Selective);
        assert!(
            !plan.members.contains(&Sym::from(ENTRY_POINT)),
            "the capturer stays outside the region"
        );

        let mut fresh = Fresh::new();
        let mut lowered = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &Region {
                plan: &plan,
                latent: effects.latent(),
                flow: effects.flow(),
                native_enabled: false,
            },
        )
        .expect("the confined region translates");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_region_reaching_through_an_island_handler_translates_and_verifies() {
        // The forwarder forces what it is handed from inside a handler for an
        // unrelated operation, so the operation the computation performs is in
        // no row the forwarder's own body discharges. The thunk is still built
        // at the monadic convention, and the bind inside it still suspends at
        // the row its body performs, which is the pairing the verifier checks.
        let ops = OpIds::assign(&BTreeSet::from([
            Sym::from(fixtures::ASK_OP),
            Sym::from(fixtures::LEAK_OP),
        ]))
        .expect("both operations have ids");
        let source = TypedCore::<Elaborated>::new(fixtures::island_program());
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let plan = super::super::analysis::plan(&source.fns, &effects, false);
        assert_eq!(plan.scope, MonadicScope::Selective);
        assert!(plan.members.contains(&Sym::from(fixtures::RUN)));

        let mut fresh = Fresh::new();
        let mut lowered = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &Region {
                plan: &plan,
                latent: effects.latent(),
                flow: effects.flow(),
                native_enabled: true,
            },
        )
        .expect("the region reaches through the island handler");
        lowered.push(abi::ebind_fn());
        lowered.push(abi::qapply_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(lowered);
        assert_eq!(verify(&typed, &env), Ok(()));
        crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
    }

    #[test]
    fn a_clause_handing_its_continuation_to_direct_code_declines_the_region() {
        // The clause suspends a resume application and passes it to a
        // declaration outside the region, which is the shape a clause takes
        // when something else decides how often to resume. The region reifies
        // that continuation, so the suspension holds a binder of the region's
        // own shape where the direct convention describes a source function. A
        // continuation performs whatever the computation it resumes performs,
        // so no flow fact reports this and the builder is the only place that
        // can see the value cross the boundary.
        let refusal = refusal_of(
            fixtures::resume_capturing_program(),
            &confined(&[fixtures::BUMP, fixtures::HELPER]),
        );
        assert_eq!(
            refusal,
            Decline::whole(Refusal::ThunkBoundary, Sym::from(fixtures::HELPER)),
        );
    }

    #[test]
    fn a_direct_thunk_reading_a_reified_binder_declines_the_region() {
        // The member binds what the operation answers, which the transform
        // reifies into a word parameter of the continuation, and hands a
        // suspension reading that binder to a declaration outside the region.
        // The suspension performs nothing, so it stays at the direct
        // convention and is copied verbatim: no crossing reaches the reference
        // inside it, and the copy would read the binder at its source type
        // where the word is what is in scope.
        let refusal = refusal_of(
            fixtures::word_capturing_program(),
            &confined(&[fixtures::HELPER]),
        );
        assert_eq!(
            refusal,
            Decline::whole(Refusal::WordCapture, Sym::from(fixtures::HELPER)),
        );
    }

    #[test]
    fn a_performing_handler_answering_with_a_transformer_declines_the_region() {
        // The clause answers with a lambda for the code around the handle to
        // apply, and that lambda still performs, so the region rewrites it at
        // the monadic convention. The answer leaves the driver as an ordinary
        // value word: the source type names a function, the monadic bind erases
        // the binder holding it, and the driver's pure arm answers with a
        // transformer built at the direct convention, so no use site can read
        // back which convention it holds. Applying it directly would consume an
        // effect cell as a result, which is a wrong value rather than a crash.
        let refusal = refusal_of(
            fixtures::transformer_answer_program(),
            &confined(&[fixtures::BUMP, fixtures::HELPER]),
        );
        assert_eq!(
            refusal,
            Decline::whole(Refusal::HandlerAnswer, Sym::from(fixtures::HELPER)),
        );
    }

    #[test]
    fn a_region_missing_a_forcer_declines_instead_of_mixing_conventions() {
        let ops = OpIds::assign(&BTreeSet::from([Sym::from(fixtures::ASK_OP)]))
            .expect("one operation has an id");
        let functions = fixtures::capturing_program();
        let source = TypedCore::<Elaborated>::new(functions);
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let mut plan = super::super::analysis::plan(&source.fns, &effects, false);
        // Hand-narrow the region to drop the forwarder. Nothing in the planner
        // produces this shape; the point is that if anything ever did, the
        // builder refuses to emit direct code that forces a monadic thunk
        // rather than emitting a program whose two halves disagree.
        assert!(plan.members.remove(&Sym::from(fixtures::RUN)));
        plan.monadic_params.remove(&Sym::from(fixtures::RUN));

        let mut fresh = Fresh::new();
        let refusal = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &Region {
                plan: &plan,
                latent: effects.latent(),
                flow: effects.flow(),
                native_enabled: false,
            },
        )
        .expect_err("forcing a monadic thunk from direct code declines the region");
        assert_eq!(
            refusal,
            Decline::new(
                Refusal::DirectForce,
                Sym::from(fixtures::RUN),
                Site::Name(Sym::from("action")),
            ),
            "the refusal names the forwarder and the parameter it forces"
        );
    }

    /// A region confined to exactly these declarations. The refusals below turn
    /// on shapes no planner produces, so the plan is written rather than
    /// derived from the program it is applied to.
    fn confined(members: &[&str]) -> MonadicRegionPlan {
        let members: BTreeSet<Sym> = members.iter().copied().map(Sym::from).collect();
        MonadicRegionPlan {
            genuine_effects: members.clone(),
            members,
            entries: BTreeSet::new(),
            monadic_params: BTreeMap::new(),
            scope: MonadicScope::Selective,
        }
    }

    /// Run the confined builder over a hand-written program and region, and
    /// report the refusal it recorded.
    fn refusal_of(functions: Vec<TypedCoreFn>, plan: &MonadicRegionPlan) -> Decline {
        let ops = OpIds::assign(&BTreeSet::from([
            Sym::from(fixtures::ASK_OP),
            Sym::from(fixtures::LEAK_OP),
        ]))
        .expect("both operations have ids");
        let source = TypedCore::<Elaborated>::new(functions);
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let mut fresh = Fresh::new();
        lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &EffRow::Empty,
            &Region {
                plan,
                latent: effects.latent(),
                flow: effects.flow(),
                native_enabled: false,
            },
        )
        .expect_err("the confined builder refuses this program")
    }

    #[test]
    fn a_cell_holding_a_computation_the_region_owns_declines_the_region() {
        // Storing the suspension in a reference is a form the rewrite copies
        // verbatim, so copying it would leave the source-convention closure
        // where every force of it expects an effect cell.
        let stashed = fixtures::nullary_thunk(fixtures::call(
            fixtures::BUMP,
            Vec::new(),
            fixtures::asking(),
        ));
        let stash = TypedComp::new(
            CompSig::new(CoreType::Ref(Box::new(stashed.ty().clone())), EffRow::Empty),
            TypedCompKind::RefNew(stashed),
        );
        let refusal = refusal_of(
            vec![
                fixtures::named(fixtures::BUMP, Vec::new(), fixtures::performed()),
                fixtures::named(fixtures::HELPER, Vec::new(), stash),
            ],
            &confined(&[fixtures::BUMP]),
        );
        assert_eq!(
            refusal,
            Decline::whole(Refusal::DirectHolds, Sym::from(fixtures::HELPER)),
        );
    }

    #[test]
    fn a_form_the_confined_builder_cannot_rewrite_declines_the_region() {
        // An open handler is not a convention crossing at all: the confined
        // builder simply has no rewrite for one, and the whole-program builder
        // is the one that handles it.
        let leaking = fixtures::handling_ask(
            fixtures::call(fixtures::BUMP, Vec::new(), fixtures::asking()),
            true,
        );
        let refusal = refusal_of(
            vec![
                fixtures::named(fixtures::BUMP, Vec::new(), fixtures::performed()),
                fixtures::named(fixtures::HELPER, Vec::new(), leaking),
            ],
            &confined(&[fixtures::BUMP]),
        );
        assert_eq!(
            refusal,
            Decline::whole(Refusal::UnsupportedForm, Sym::from(fixtures::HELPER)),
        );
    }

    #[test]
    fn a_member_with_no_residual_row_declines_before_minting_names() {
        let ops = OpIds::assign(&BTreeSet::from([Sym::from(fixtures::ASK_OP)]))
            .expect("one operation has an id");
        let source = TypedCore::<Elaborated>::new(fixtures::capturing_program());
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let plan = super::super::analysis::plan(&source.fns, &effects, false);
        let mut fresh = Fresh::new();
        let refusal = lower_selective(
            &source.fns,
            &ops,
            &mut fresh,
            &MissingRows,
            &Region {
                plan: &plan,
                latent: effects.latent(),
                flow: effects.flow(),
                native_enabled: false,
            },
        )
        .expect_err("a member needs a residual row for its monadic signature");
        assert_eq!(
            refusal,
            Decline::whole(Refusal::MissingRow, Sym::from(fixtures::BUMP)),
        );
        assert_eq!(fresh.bump(), 0, "planning failures cannot consume names");
    }

    #[test]
    fn a_slot_reached_at_two_conventions_declines_the_region() {
        // The forwarder's slot is driven at the monadic convention because one
        // call site fills it with a computation that performs. A second site
        // fills the same slot with one that only declares the row and performs
        // nothing, which the flow solution leaves at the direct convention. A
        // thunk carries no convention in its type, so there is nothing to
        // retag and no coercion to insert: the region declines.
        let quiet = fixtures::nullary_thunk(TypedComp::new(
            CompSig::new(fixtures::int(), fixtures::asking()),
            TypedCompKind::Return(TypedValue::new(
                fixtures::int(),
                TypedValueKind::Int(0.into()),
            )),
        ));
        let mut functions = fixtures::capturing_program();
        functions.push(fixtures::named(
            fixtures::HELPER,
            Vec::new(),
            fixtures::call(fixtures::RUN, vec![quiet], fixtures::asking()),
        ));
        let source = TypedCore::<Elaborated>::new(functions);
        let effects = super::super::EffectPlan::analyze(&source.fns);
        let plan = super::super::analysis::plan(&source.fns, &effects, false);
        assert_eq!(
            plan.monadic_params.get(&Sym::from(fixtures::RUN)),
            Some(&BTreeSet::from([0])),
            "the performing call site is what makes the slot monadic",
        );
        let refusal = refusal_of(source.fns, &plan);
        assert_eq!(
            refusal,
            Decline::whole(Refusal::ThunkBoundary, Sym::from(fixtures::HELPER)),
        );
    }
}
