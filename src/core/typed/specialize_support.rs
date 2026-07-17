//! Private traversal substrate for witness-preserving dictionary specialization.
//!
//! This module deliberately contains no specialization policy. It supplies the
//! structural operations the typed pass needs while keeping their order locked
//! to the legacy pass: partial witness substitution, term-variable substitution,
//! free-variable collection, and deterministic binder freshening.

use std::collections::{BTreeMap, BTreeSet};

use crate::names;
use crate::sym::Sym;

use super::verify::{
    substitute_core_type, substitute_fn_sig, substitute_label, substitute_row, substitute_sig,
    substitute_type,
};
use super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCore, TypedCoreFn, TypedForward, TypedHandleOp, TypedHandler, TypedPattern,
    TypedValue, TypedValueKind,
};

/// One structural typed-Core rewrite.
///
/// The default descent is the exhaustive node inventory for private typed
/// passes. Implementors override only the nodes or witness leaves they change.
/// Binder-sensitive rewrites override the corresponding computation forms so
/// their context extension stays explicit.
pub(super) trait Rewrite {
    type Ctx;

    fn core_type(&mut self, ty: &CoreType, _cx: &Self::Ctx) -> CoreType {
        ty.clone()
    }

    fn comp_sig(&mut self, sig: &CompSig, _cx: &Self::Ctx) -> CompSig {
        sig.clone()
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, _cx: &Self::Ctx) -> CoreFnSig {
        sig.clone()
    }

    fn instantiation(
        &mut self,
        instantiation: &CoreInstantiation,
        _cx: &Self::Ctx,
    ) -> CoreInstantiation {
        instantiation.clone()
    }

    fn forward(&mut self, forward: &TypedForward, _cx: &Self::Ctx) -> TypedForward {
        forward.clone()
    }

    fn binder(&mut self, binder: &TypedBinder, cx: &Self::Ctx) -> TypedBinder {
        TypedBinder::new(binder.name, self.core_type(&binder.ty, cx))
    }

    fn pattern(&mut self, pattern: &TypedPattern, cx: &Self::Ctx) -> TypedPattern {
        match pattern {
            TypedPattern::Wild => TypedPattern::Wild,
            TypedPattern::Var(binder) => TypedPattern::Var(self.binder(binder, cx)),
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => TypedPattern::Ctor {
                name: *name,
                instantiation: self.instantiations(instantiation, cx),
                fields: fields
                    .iter()
                    .map(|binder| binder.as_ref().map(|binder| self.binder(binder, cx)))
                    .collect(),
            },
            TypedPattern::Tuple(fields) => TypedPattern::Tuple(
                fields
                    .iter()
                    .map(|binder| binder.as_ref().map(|binder| self.binder(binder, cx)))
                    .collect(),
            ),
        }
    }

    fn value(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        self.descend_value(value, cx)
    }

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        self.descend_comp(comp, cx)
    }

    fn function(&mut self, function: &TypedCoreFn, cx: &Self::Ctx) -> TypedCoreFn {
        TypedCoreFn::new(
            function.name,
            function
                .params
                .iter()
                .map(|binder| self.binder(binder, cx))
                .collect(),
            self.comp(&function.body, cx),
            self.fn_sig(&function.sig, cx),
            function.dict_arity,
        )
    }

    fn core<P>(&mut self, core: &TypedCore<P>, cx: &Self::Ctx) -> TypedCore<P> {
        TypedCore::new(
            core.fns
                .iter()
                .map(|function| self.function(function, cx))
                .collect(),
        )
    }

    fn instantiations(
        &mut self,
        instantiations: &[CoreInstantiation],
        cx: &Self::Ctx,
    ) -> Vec<CoreInstantiation> {
        instantiations
            .iter()
            .map(|instantiation| self.instantiation(instantiation, cx))
            .collect()
    }

    #[allow(clippy::too_many_lines)]
    fn descend_value(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        let kind = match &value.kind {
            TypedValueKind::Var {
                name,
                instantiation,
            } => TypedValueKind::Var {
                name: *name,
                instantiation: self.instantiations(instantiation, cx),
            },
            TypedValueKind::Int(value) => TypedValueKind::Int(*value),
            TypedValueKind::I64(value) => TypedValueKind::I64(*value),
            TypedValueKind::U64(value) => TypedValueKind::U64(*value),
            TypedValueKind::Float(value) => TypedValueKind::Float(*value),
            TypedValueKind::Bool(value) => TypedValueKind::Bool(*value),
            TypedValueKind::Unit => TypedValueKind::Unit,
            TypedValueKind::Str(value) => TypedValueKind::Str(value.clone()),
            TypedValueKind::Reinterpret(value) => {
                TypedValueKind::Reinterpret(Box::new(self.value(value, cx)))
            }
            TypedValueKind::LoweredRepr { value, proof } => TypedValueKind::LoweredRepr {
                value: Box::new(self.value(value, cx)),
                proof: proof.clone(),
            },
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValueKind::NewtypeRepr {
                constructor: *constructor,
                instantiation: self.instantiations(instantiation, cx),
                value: Box::new(self.value(value, cx)),
            },
            TypedValueKind::Thunk(body) => TypedValueKind::Thunk(Box::new(self.comp(body, cx))),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValueKind::Ctor {
                name: *name,
                tag: *tag,
                instantiation: self.instantiations(instantiation, cx),
                fields: fields.iter().map(|field| self.value(field, cx)).collect(),
            },
            TypedValueKind::Tuple(fields) => {
                TypedValueKind::Tuple(fields.iter().map(|field| self.value(field, cx)).collect())
            }
            TypedValueKind::UnboxedTuple(fields) => TypedValueKind::UnboxedTuple(
                fields.iter().map(|field| self.value(field, cx)).collect(),
            ),
            TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, field)| (*name, self.value(field, cx)))
                    .collect(),
            ),
        };
        TypedValue::new(self.core_type(&value.ty, cx), kind)
    }

    #[allow(clippy::too_many_lines)]
    fn descend_comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        let kind = match &comp.kind {
            TypedCompKind::Return(value) => TypedCompKind::Return(self.value(value, cx)),
            TypedCompKind::Bind(first, binder, rest) => TypedCompKind::Bind(
                Box::new(self.comp(first, cx)),
                self.binder(binder, cx),
                Box::new(self.comp(rest, cx)),
            ),
            TypedCompKind::Force(value) => TypedCompKind::Force(self.value(value, cx)),
            TypedCompKind::Lam(params, body) => TypedCompKind::Lam(
                params
                    .iter()
                    .map(|binder| self.binder(binder, cx))
                    .collect(),
                Box::new(self.comp(body, cx)),
            ),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => TypedCompKind::App {
                callee: Box::new(self.comp(callee, cx)),
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::If(condition, yes, no) => TypedCompKind::If(
                self.value(condition, cx),
                Box::new(self.comp(yes, cx)),
                Box::new(self.comp(no, cx)),
            ),
            TypedCompKind::Prim(op, lhs, rhs) => {
                TypedCompKind::Prim(*op, self.value(lhs, cx), self.value(rhs, cx))
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => TypedCompKind::Call {
                callee: *callee,
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::Io(op, args) => {
                TypedCompKind::Io(*op, args.iter().map(|arg| self.value(arg, cx)).collect())
            }
            TypedCompKind::Error(value) => TypedCompKind::Error(self.value(value, cx)),
            TypedCompKind::Case(scrutinee, arms) => TypedCompKind::Case(
                self.value(scrutinee, cx),
                arms.iter()
                    .map(|(pattern, body)| (self.pattern(pattern, cx), self.comp(body, cx)))
                    .collect(),
            ),
            TypedCompKind::FloatBuiltin(op, value) => {
                TypedCompKind::FloatBuiltin(*op, self.value(value, cx))
            }
            TypedCompKind::Neg(lane, value) => TypedCompKind::Neg(*lane, self.value(value, cx)),
            TypedCompKind::UnboxedProject(value, field) => {
                TypedCompKind::UnboxedProject(self.value(value, cx), *field)
            }
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => TypedCompKind::Do {
                operation: *operation,
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => TypedCompKind::Handle {
                body: Box::new(self.comp(body, cx)),
                return_binder: return_binder.as_ref().map(|binder| self.binder(binder, cx)),
                return_body: return_body
                    .as_ref()
                    .map(|body| Box::new(self.comp(body, cx))),
                ops: TypedHandler {
                    arms: ops
                        .arms
                        .iter()
                        .map(|arm| TypedHandleOp {
                            name: arm.name,
                            instantiation: self.instantiations(&arm.instantiation, cx),
                            params: arm
                                .params
                                .iter()
                                .map(|binder| self.binder(binder, cx))
                                .collect(),
                            resume: self.binder(&arm.resume, cx),
                            body: self.comp(&arm.body, cx),
                        })
                        .collect(),
                    forwarded: ops
                        .forwarded
                        .iter()
                        .map(|forward| self.forward(forward, cx))
                        .collect(),
                },
            },
            TypedCompKind::Mask(effects, body) => {
                TypedCompKind::Mask(effects.clone(), Box::new(self.comp(body, cx)))
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedCompKind::StrBuiltin {
                op: *op,
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::Dup(value) => TypedCompKind::Dup(self.value(value, cx)),
            TypedCompKind::Drop(value) => TypedCompKind::Drop(self.value(value, cx)),
            TypedCompKind::WithReuse { token, freed, body } => TypedCompKind::WithReuse {
                token: self.binder(token, cx),
                freed: self.value(freed, cx),
                body: Box::new(self.comp(body, cx)),
            },
            TypedCompKind::Reuse(token, value) => {
                TypedCompKind::Reuse(self.binder(token, cx), self.value(value, cx))
            }
            TypedCompKind::RefNew(value) => TypedCompKind::RefNew(self.value(value, cx)),
            TypedCompKind::RefGet(value) => TypedCompKind::RefGet(self.value(value, cx)),
            TypedCompKind::RefSet(cell, value) => {
                TypedCompKind::RefSet(self.value(cell, cx), self.value(value, cx))
            }
            TypedCompKind::InitAt(cell, ctor) => {
                TypedCompKind::InitAt(self.value(cell, cx), self.value(ctor, cx))
            }
        };
        TypedComp::new(self.comp_sig(&comp.sig, cx), kind)
    }
}

/// Substitute any supplied prefix of a quantifier list through every typed-Core
/// witness. Unmatched quantifiers remain rigid, which lets specialization apply
/// only the concrete instance arguments it knows.
pub(super) fn substitute_witnesses(
    comp: &TypedComp,
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> TypedComp {
    TypeSubstitution {
        quantifiers,
        arguments,
    }
    .comp(comp, &())
}

/// Instantiate a known prefix of a function's own quantifiers, retaining and
/// capture-avoiding any unsupplied suffix.
#[cfg(test)]
pub(super) fn instantiate_fn_prefix(
    signature: &CoreFnSig,
    arguments: &[CoreInstantiation],
) -> CoreFnSig {
    let supplied = arguments.len();
    debug_assert!(
        supplied <= signature.quantifiers.len(),
        "a specialization prefix cannot exceed its function scheme"
    );
    let remaining = CoreFnSig::new(
        signature.quantifiers[supplied..].to_vec(),
        signature.params.clone(),
        signature.body.clone(),
    );
    substitute_fn_sig(
        &remaining,
        &signature.quantifiers[..supplied],
        &arguments[..supplied],
    )
}

struct TypeSubstitution<'a> {
    quantifiers: &'a [CoreQuantifier],
    arguments: &'a [CoreInstantiation],
}

impl Rewrite for TypeSubstitution<'_> {
    type Ctx = ();

    fn core_type(&mut self, ty: &CoreType, _cx: &Self::Ctx) -> CoreType {
        substitute_core_type(ty, self.quantifiers, self.arguments)
    }

    fn comp_sig(&mut self, sig: &CompSig, _cx: &Self::Ctx) -> CompSig {
        substitute_sig(sig, self.quantifiers, self.arguments)
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, _cx: &Self::Ctx) -> CoreFnSig {
        substitute_fn_sig(sig, self.quantifiers, self.arguments)
    }

    fn instantiation(
        &mut self,
        instantiation: &CoreInstantiation,
        _cx: &Self::Ctx,
    ) -> CoreInstantiation {
        match instantiation {
            CoreInstantiation::Type(ty) => {
                CoreInstantiation::Type(substitute_type(ty, self.quantifiers, self.arguments))
            }
            CoreInstantiation::Row(row) => {
                CoreInstantiation::Row(substitute_row(row, self.quantifiers, self.arguments))
            }
        }
    }

    fn forward(&mut self, forward: &TypedForward, _cx: &Self::Ctx) -> TypedForward {
        TypedForward::new(
            forward.operation,
            substitute_label(&forward.effect, self.quantifiers, self.arguments),
        )
    }
}

/// Capture-avoiding substitution of typed local variables by typed values.
pub(super) fn substitute_terms(
    comp: &TypedComp,
    substitution: &BTreeMap<Sym, TypedValue>,
    counter: &mut u32,
    prefix: &'static str,
) -> TypedComp {
    TermSubstitution { counter, prefix }.comp(
        comp,
        &TermContext {
            values: substitution.clone(),
            renames: BTreeMap::new(),
        },
    )
}

struct TermSubstitution<'a> {
    counter: &'a mut u32,
    prefix: &'static str,
}

#[derive(Clone)]
struct TermContext {
    values: BTreeMap<Sym, TypedValue>,
    renames: BTreeMap<Sym, Sym>,
}

impl TermSubstitution<'_> {
    fn enter(
        &mut self,
        substitution: &TermContext,
        bound: &[(Sym, CoreType)],
    ) -> (BTreeMap<Sym, Sym>, TermContext) {
        let mut next = substitution.clone();
        for (binder, _) in bound {
            next.values.remove(binder);
            next.renames.remove(binder);
        }
        let danger: BTreeSet<_> = next.values.values().flat_map(free_value_vars).collect();
        let mut renames = BTreeMap::new();
        for (binder, _) in bound {
            if danger.contains(binder) {
                let fresh = next_fresh(self.counter, self.prefix);
                next.renames.insert(*binder, fresh);
                renames.insert(*binder, fresh);
            }
        }
        (renames, next)
    }

    fn renamed_binder(binder: &TypedBinder, renames: &BTreeMap<Sym, Sym>) -> TypedBinder {
        TypedBinder::new(
            renames.get(&binder.name).copied().unwrap_or(binder.name),
            binder.ty.clone(),
        )
    }

    fn enter_binders(
        &mut self,
        substitution: &TermContext,
        binders: &[TypedBinder],
    ) -> (Vec<TypedBinder>, TermContext) {
        let binders_with_types: Vec<_> = binders
            .iter()
            .map(|binder| (binder.name, binder.ty.clone()))
            .collect();
        let (renames, next) = self.enter(substitution, &binders_with_types);
        (
            binders
                .iter()
                .map(|binder| Self::renamed_binder(binder, &renames))
                .collect(),
            next,
        )
    }

    fn enter_pattern(
        &mut self,
        substitution: &TermContext,
        pattern: &TypedPattern,
    ) -> (TypedPattern, TermContext) {
        let binders = pattern_typed_binders(pattern);
        let (renames, next) = self.enter(substitution, &binders);
        let pattern = match pattern {
            TypedPattern::Wild => TypedPattern::Wild,
            TypedPattern::Var(binder) => TypedPattern::Var(Self::renamed_binder(binder, &renames)),
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => TypedPattern::Ctor {
                name: *name,
                instantiation: instantiation.clone(),
                fields: fields
                    .iter()
                    .map(|binder| {
                        binder
                            .as_ref()
                            .map(|binder| Self::renamed_binder(binder, &renames))
                    })
                    .collect(),
            },
            TypedPattern::Tuple(fields) => TypedPattern::Tuple(
                fields
                    .iter()
                    .map(|binder| {
                        binder
                            .as_ref()
                            .map(|binder| Self::renamed_binder(binder, &renames))
                    })
                    .collect(),
            ),
        };
        (pattern, next)
    }
}

impl Rewrite for TermSubstitution<'_> {
    type Ctx = TermContext;

    fn value(&mut self, value: &TypedValue, substitution: &Self::Ctx) -> TypedValue {
        if let TypedValueKind::Var {
            name,
            instantiation,
        } = &value.kind
        {
            if let Some(replacement) = substitution.values.get(name) {
                return replacement.clone();
            }
            if let Some(fresh) = substitution.renames.get(name) {
                return TypedValue::new(
                    value.ty.clone(),
                    TypedValueKind::Var {
                        name: *fresh,
                        instantiation: instantiation.clone(),
                    },
                );
            }
        }
        self.descend_value(value, substitution)
    }

    fn comp(&mut self, comp: &TypedComp, substitution: &Self::Ctx) -> TypedComp {
        match &comp.kind {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, substitution);
                let (renames, next) = self.enter(substitution, &[(binder.name, binder.ty.clone())]);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(
                        Box::new(first),
                        Self::renamed_binder(binder, &renames),
                        Box::new(self.comp(rest, &next)),
                    ),
                )
            }
            TypedCompKind::Lam(params, body) => {
                let (params, next) = self.enter_binders(substitution, params);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Lam(params, Box::new(self.comp(body, &next))),
                )
            }
            TypedCompKind::Case(scrutinee, arms) => TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Case(
                    self.value(scrutinee, substitution),
                    arms.iter()
                        .map(|(pattern, body)| {
                            let (pattern, next) = self.enter_pattern(substitution, pattern);
                            (pattern, self.comp(body, &next))
                        })
                        .collect(),
                ),
            ),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                let body = Box::new(self.comp(body, substitution));
                let (return_binder, return_body) = match return_binder {
                    Some(binder) => {
                        let (renames, next) =
                            self.enter(substitution, &[(binder.name, binder.ty.clone())]);
                        (
                            Some(Self::renamed_binder(binder, &renames)),
                            return_body
                                .as_ref()
                                .map(|body| Box::new(self.comp(body, &next))),
                        )
                    }
                    None => (
                        None,
                        return_body
                            .as_ref()
                            .map(|body| Box::new(self.comp(body, substitution))),
                    ),
                };
                let arms = ops
                    .arms
                    .iter()
                    .map(|arm| {
                        let mut bound: Vec<_> = arm
                            .params
                            .iter()
                            .map(|binder| (binder.name, binder.ty.clone()))
                            .collect();
                        bound.push((arm.resume.name, arm.resume.ty.clone()));
                        let (renames, next) = self.enter(substitution, &bound);
                        TypedHandleOp {
                            name: arm.name,
                            instantiation: arm.instantiation.clone(),
                            params: arm
                                .params
                                .iter()
                                .map(|binder| Self::renamed_binder(binder, &renames))
                                .collect(),
                            resume: Self::renamed_binder(&arm.resume, &renames),
                            body: self.comp(&arm.body, &next),
                        }
                    })
                    .collect();
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Handle {
                        body,
                        return_binder,
                        return_body,
                        ops: TypedHandler {
                            arms,
                            forwarded: ops.forwarded.clone(),
                        },
                    },
                )
            }
            TypedCompKind::WithReuse { token, freed, body } => {
                let freed = self.value(freed, substitution);
                let (renames, next) = self.enter(substitution, &[(token.name, token.ty.clone())]);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::WithReuse {
                        token: Self::renamed_binder(token, &renames),
                        freed,
                        body: Box::new(self.comp(body, &next)),
                    },
                )
            }
            _ => self.descend_comp(comp, substitution),
        }
    }
}

/// Free local/global term references in a typed computation.
pub(super) fn free_comp_vars(comp: &TypedComp) -> BTreeSet<Sym> {
    let mut free = BTreeSet::new();
    collect_comp_vars(comp, &mut Vec::new(), &mut free);
    free
}

/// Free local/global term references in a typed value, including thunk bodies.
pub(super) fn free_value_vars(value: &TypedValue) -> BTreeSet<Sym> {
    let mut free = BTreeSet::new();
    collect_value_vars(value, &mut Vec::new(), &mut free);
    free
}

fn collect_ref(name: Sym, bound: &[Sym], free: &mut BTreeSet<Sym>) {
    if !bound.contains(&name) {
        free.insert(name);
    }
}

fn under(
    bound: &mut Vec<Sym>,
    names: impl IntoIterator<Item = Sym>,
    body: &TypedComp,
    free: &mut BTreeSet<Sym>,
) {
    let old_len = bound.len();
    bound.extend(names);
    collect_comp_vars(body, bound, free);
    bound.truncate(old_len);
}

fn collect_value_vars(value: &TypedValue, bound: &mut Vec<Sym>, free: &mut BTreeSet<Sym>) {
    match &value.kind {
        TypedValueKind::Var { name, .. } => collect_ref(*name, bound, free),
        TypedValueKind::Reinterpret(value)
        | TypedValueKind::LoweredRepr { value, proof: _ }
        | TypedValueKind::NewtypeRepr { value, .. } => {
            collect_value_vars(value, bound, free);
        }
        TypedValueKind::Thunk(body) => collect_comp_vars(body, bound, free),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                collect_value_vars(field, bound, free);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                collect_value_vars(field, bound, free);
            }
        }
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => {}
    }
}

#[allow(clippy::too_many_lines)]
fn collect_comp_vars(comp: &TypedComp, bound: &mut Vec<Sym>, free: &mut BTreeSet<Sym>) {
    match &comp.kind {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => collect_value_vars(value, bound, free),
        TypedCompKind::Reuse(token, value) => {
            collect_ref(token.name, bound, free);
            collect_value_vars(value, bound, free);
        }
        TypedCompKind::Prim(_, lhs, rhs)
        | TypedCompKind::RefSet(lhs, rhs)
        | TypedCompKind::InitAt(lhs, rhs) => {
            collect_value_vars(lhs, bound, free);
            collect_value_vars(rhs, bound, free);
        }
        TypedCompKind::Bind(first, binder, rest) => {
            collect_comp_vars(first, bound, free);
            under(bound, [binder.name], rest, free);
        }
        TypedCompKind::Lam(params, body) => {
            under(bound, params.iter().map(|binder| binder.name), body, free);
        }
        TypedCompKind::App { callee, args, .. } => {
            collect_comp_vars(callee, bound, free);
            for arg in args {
                collect_value_vars(arg, bound, free);
            }
        }
        TypedCompKind::If(condition, yes, no) => {
            collect_value_vars(condition, bound, free);
            collect_comp_vars(yes, bound, free);
            collect_comp_vars(no, bound, free);
        }
        TypedCompKind::Call { args, .. }
        | TypedCompKind::Io(_, args)
        | TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. } => {
            for arg in args {
                collect_value_vars(arg, bound, free);
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            collect_value_vars(scrutinee, bound, free);
            for (pattern, body) in arms {
                under(bound, pattern_binders(pattern), body, free);
            }
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            collect_comp_vars(body, bound, free);
            if let Some(return_body) = return_body {
                under(
                    bound,
                    return_binder.iter().map(|binder| binder.name),
                    return_body,
                    free,
                );
            }
            for arm in &ops.arms {
                under(
                    bound,
                    arm.params
                        .iter()
                        .map(|binder| binder.name)
                        .chain([arm.resume.name]),
                    &arm.body,
                    free,
                );
            }
        }
        TypedCompKind::Mask(_, body) => collect_comp_vars(body, bound, free),
        TypedCompKind::WithReuse { token, freed, body } => {
            collect_value_vars(freed, bound, free);
            under(bound, [token.name], body, free);
        }
    }
}

fn pattern_binders(pattern: &TypedPattern) -> Vec<Sym> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![binder.name],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            fields.iter().flatten().map(|binder| binder.name).collect()
        }
    }
}

fn pattern_typed_binders(pattern: &TypedPattern) -> Vec<(Sym, CoreType)> {
    match pattern {
        TypedPattern::Wild => Vec::new(),
        TypedPattern::Var(binder) => vec![(binder.name, binder.ty.clone())],
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => fields
            .iter()
            .flatten()
            .map(|binder| (binder.name, binder.ty.clone()))
            .collect(),
    }
}

/// Freshen every typed binder in legacy traversal order.
pub(super) fn freshen(comp: &TypedComp, counter: &mut u32, prefix: &'static str) -> TypedComp {
    freshen_with(comp, &BTreeMap::new(), counter, prefix)
}

/// Freshen every binder, seeded with renames supplied by the caller.
pub(super) fn freshen_with(
    comp: &TypedComp,
    renames: &BTreeMap<Sym, Sym>,
    counter: &mut u32,
    prefix: &'static str,
) -> TypedComp {
    Freshen { counter, prefix }.comp(comp, renames)
}

pub(super) fn next_fresh(counter: &mut u32, prefix: &'static str) -> Sym {
    let name = Sym::from(&names::fresh_binder(prefix, *counter));
    *counter += 1;
    name
}

struct Freshen<'a> {
    counter: &'a mut u32,
    prefix: &'static str,
}

impl Freshen<'_> {
    fn next(&mut self) -> Sym {
        next_fresh(self.counter, self.prefix)
    }

    fn fresh_binder(
        &mut self,
        binder: &TypedBinder,
        renames: &mut BTreeMap<Sym, Sym>,
    ) -> TypedBinder {
        let name = self.next();
        renames.insert(binder.name, name);
        TypedBinder::new(name, binder.ty.clone())
    }

    fn rename_ref(binder: &TypedBinder, renames: &BTreeMap<Sym, Sym>) -> TypedBinder {
        TypedBinder::new(
            renames.get(&binder.name).copied().unwrap_or(binder.name),
            binder.ty.clone(),
        )
    }

    fn fresh_pattern(
        &mut self,
        pattern: &TypedPattern,
        renames: &mut BTreeMap<Sym, Sym>,
    ) -> TypedPattern {
        match pattern {
            TypedPattern::Wild => TypedPattern::Wild,
            TypedPattern::Var(binder) => TypedPattern::Var(self.fresh_binder(binder, renames)),
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => TypedPattern::Ctor {
                name: *name,
                instantiation: instantiation.clone(),
                fields: fields
                    .iter()
                    .map(|binder| {
                        binder
                            .as_ref()
                            .map(|binder| self.fresh_binder(binder, renames))
                    })
                    .collect(),
            },
            TypedPattern::Tuple(fields) => TypedPattern::Tuple(
                fields
                    .iter()
                    .map(|binder| {
                        binder
                            .as_ref()
                            .map(|binder| self.fresh_binder(binder, renames))
                    })
                    .collect(),
            ),
        }
    }
}

impl Rewrite for Freshen<'_> {
    type Ctx = BTreeMap<Sym, Sym>;

    fn value(&mut self, value: &TypedValue, renames: &Self::Ctx) -> TypedValue {
        if let TypedValueKind::Var {
            name,
            instantiation,
        } = &value.kind
        {
            if let Some(name) = renames.get(name) {
                return TypedValue::new(
                    value.ty.clone(),
                    TypedValueKind::Var {
                        name: *name,
                        instantiation: instantiation.clone(),
                    },
                );
            }
        }
        self.descend_value(value, renames)
    }

    fn comp(&mut self, comp: &TypedComp, renames: &Self::Ctx) -> TypedComp {
        match &comp.kind {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, renames);
                let mut next = renames.clone();
                let binder = self.fresh_binder(binder, &mut next);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(Box::new(first), binder, Box::new(self.comp(rest, &next))),
                )
            }
            TypedCompKind::Lam(params, body) => {
                let mut next = renames.clone();
                let params = params
                    .iter()
                    .map(|binder| self.fresh_binder(binder, &mut next))
                    .collect();
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Lam(params, Box::new(self.comp(body, &next))),
                )
            }
            TypedCompKind::Case(scrutinee, arms) => {
                let scrutinee = self.value(scrutinee, renames);
                let mut next_arms = Vec::with_capacity(arms.len());
                for (pattern, body) in arms {
                    let mut next = renames.clone();
                    let pattern = self.fresh_pattern(pattern, &mut next);
                    next_arms.push((pattern, self.comp(body, &next)));
                }
                TypedComp::new(comp.sig.clone(), TypedCompKind::Case(scrutinee, next_arms))
            }
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                let body = Box::new(self.comp(body, renames));
                let (return_binder, return_body) = match return_binder {
                    Some(binder) => {
                        let mut next = renames.clone();
                        let binder = self.fresh_binder(binder, &mut next);
                        (
                            Some(binder),
                            return_body
                                .as_ref()
                                .map(|body| Box::new(self.comp(body, &next))),
                        )
                    }
                    None => (
                        None,
                        return_body
                            .as_ref()
                            .map(|body| Box::new(self.comp(body, renames))),
                    ),
                };
                let mut arms = Vec::with_capacity(ops.arms.len());
                for arm in &ops.arms {
                    let mut next = renames.clone();
                    let params = arm
                        .params
                        .iter()
                        .map(|binder| self.fresh_binder(binder, &mut next))
                        .collect();
                    let resume = self.fresh_binder(&arm.resume, &mut next);
                    arms.push(TypedHandleOp {
                        name: arm.name,
                        instantiation: arm.instantiation.clone(),
                        params,
                        resume,
                        body: self.comp(&arm.body, &next),
                    });
                }
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Handle {
                        body,
                        return_binder,
                        return_body,
                        ops: TypedHandler {
                            arms,
                            forwarded: ops.forwarded.clone(),
                        },
                    },
                )
            }
            TypedCompKind::WithReuse { token, freed, body } => {
                let freed = self.value(freed, renames);
                let mut next = renames.clone();
                let token = self.fresh_binder(token, &mut next);
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::WithReuse {
                        token,
                        freed,
                        body: Box::new(self.comp(body, &next)),
                    },
                )
            }
            TypedCompKind::Reuse(token, value) => TypedComp::new(
                comp.sig.clone(),
                TypedCompKind::Reuse(Self::rename_ref(token, renames), self.value(value, renames)),
            ),
            _ => self.descend_comp(comp, renames),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::core::cbpv::Value;
    use crate::core::fv;
    use crate::core::opt::{freshen_legacy, subst_comp_legacy};
    use crate::names::FRESH_SPECIALIZE;
    use crate::types::ty::{EffRow, Label};
    use crate::types::Type;

    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn int_type() -> CoreType {
        source(Type::Int)
    }

    fn sig(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn binder(name: &str) -> TypedBinder {
        TypedBinder::new(sym(name), int_type())
    }

    fn var(name: &str) -> TypedValue {
        TypedValue::new(
            int_type(),
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn ret(value: TypedValue) -> TypedComp {
        TypedComp::new(sig(value.ty.clone()), TypedCompKind::Return(value))
    }

    fn traversal_fixture() -> TypedComp {
        let op_body = TypedComp::new(
            sig(int_type()),
            TypedCompKind::WithReuse {
                token: binder("token"),
                freed: var("op_param"),
                body: Box::new(TypedComp::new(
                    sig(int_type()),
                    TypedCompKind::Reuse(binder("token"), var("resume")),
                )),
            },
        );
        let handler = TypedComp::new(
            sig(int_type()),
            TypedCompKind::Handle {
                body: Box::new(TypedComp::new(
                    sig(CoreType::Function(Box::new(CoreFnSig::new(
                        Vec::new(),
                        vec![int_type()],
                        sig(int_type()),
                    )))),
                    TypedCompKind::Lam(vec![binder("lambda")], Box::new(ret(var("lambda")))),
                )),
                return_binder: Some(binder("returned")),
                return_body: Some(Box::new(TypedComp::new(
                    sig(int_type()),
                    TypedCompKind::Case(
                        var("returned"),
                        vec![(TypedPattern::Var(binder("pattern")), ret(var("pattern")))],
                    ),
                ))),
                ops: TypedHandler {
                    arms: vec![TypedHandleOp {
                        name: sym("ask"),
                        instantiation: Vec::new(),
                        params: vec![binder("op_param")],
                        resume: binder("resume"),
                        body: op_body,
                    }],
                    forwarded: Vec::new(),
                },
            },
        );
        TypedComp::new(
            sig(int_type()),
            TypedCompKind::Bind(
                Box::new(ret(var("outside"))),
                binder("bound"),
                Box::new(handler),
            ),
        )
    }

    #[test]
    fn freshening_matches_legacy_structure_order_and_counter() {
        let typed = traversal_fixture();
        let legacy = typed.clone().erase();
        let mut typed_counter = 0;
        let mut legacy_counter = 0;
        let typed = freshen(&typed, &mut typed_counter, FRESH_SPECIALIZE).erase();
        let legacy = freshen_legacy(&legacy, &mut legacy_counter, FRESH_SPECIALIZE);
        assert_eq!(typed, legacy);
        assert_eq!(typed_counter, legacy_counter);
    }

    #[test]
    fn free_variables_match_legacy_across_all_binder_families() {
        let typed = traversal_fixture();
        assert_eq!(free_comp_vars(&typed), fv::comp(&typed.clone().erase()));
    }

    #[test]
    fn term_substitution_matches_legacy_capture_avoidance() {
        let polymorphic_capture = TypedValue::new(
            int_type(),
            TypedValueKind::Var {
                name: sym("capture"),
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
            },
        );
        let typed = TypedComp::new(
            sig(CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![int_type()],
                sig(int_type()),
            )))),
            TypedCompKind::Lam(
                vec![binder("capture")],
                Box::new(TypedComp::new(
                    sig(int_type()),
                    TypedCompKind::Prim(
                        crate::core::CoreOp::Add,
                        var("replace"),
                        polymorphic_capture,
                    ),
                )),
            ),
        );
        let legacy = typed.clone().erase();
        let mut typed_substitution = BTreeMap::new();
        typed_substitution.insert(sym("replace"), var("capture"));
        let mut legacy_substitution = BTreeMap::new();
        legacy_substitution.insert(sym("replace"), Value::Var(sym("capture")));
        let mut typed_counter = 0;
        let mut legacy_counter = 0;
        let typed = substitute_terms(
            &typed,
            &typed_substitution,
            &mut typed_counter,
            FRESH_SPECIALIZE,
        );
        let TypedCompKind::Lam(params, body) = &typed.kind else {
            panic!("expected lambda")
        };
        let TypedCompKind::Prim(_, _, renamed_use) = &body.kind else {
            panic!("expected primitive body")
        };
        let TypedValueKind::Var {
            name,
            instantiation,
        } = &renamed_use.kind
        else {
            panic!("expected renamed local use")
        };
        assert_eq!(*name, params[0].name);
        assert_eq!(
            instantiation,
            &[CoreInstantiation::Type(Type::Int)],
            "alpha-renaming must retain polymorphic use-site evidence"
        );
        let typed = typed.erase();
        let legacy = subst_comp_legacy(
            &legacy,
            &legacy_substitution,
            &mut legacy_counter,
            FRESH_SPECIALIZE,
        );
        assert_eq!(typed, legacy);
        assert_eq!(typed_counter, legacy_counter);
        assert_eq!(fv::comp(&typed), std::iter::once(sym("capture")).collect());
    }

    #[test]
    fn witness_substitution_reaches_patterns_handlers_and_forwarding() {
        let a = sym("a");
        let e = sym("e");
        let quantifiers = [CoreQuantifier::Type(a), CoreQuantifier::Row(e)];
        let arguments = [
            CoreInstantiation::Type(Type::Int),
            CoreInstantiation::Row(EffRow::singleton("IO")),
        ];
        let instantiation = vec![
            CoreInstantiation::Type(Type::Var(a)),
            CoreInstantiation::Row(EffRow::Var(e)),
        ];
        let effect = Label {
            name: sym("Emit"),
            args: vec![Type::Var(a)],
        };
        let variable_type = source(Type::Var(a));
        let variable_sig = CompSig::new(variable_type.clone(), EffRow::Var(e));
        let body = TypedComp::new(
            variable_sig.clone(),
            TypedCompKind::Case(
                TypedValue::new(
                    variable_type.clone(),
                    TypedValueKind::Var {
                        name: sym("scrutinee"),
                        instantiation: instantiation.clone(),
                    },
                ),
                vec![(
                    TypedPattern::Ctor {
                        name: sym("Box"),
                        instantiation: instantiation.clone(),
                        fields: vec![Some(TypedBinder::new(sym("field"), variable_type.clone()))],
                    },
                    TypedComp::new(
                        variable_sig.clone(),
                        TypedCompKind::Do {
                            operation: sym("emit"),
                            instantiation: instantiation.clone(),
                            args: vec![var("field")],
                        },
                    ),
                )],
            ),
        );
        let typed = TypedComp::new(
            variable_sig.clone(),
            TypedCompKind::Handle {
                body: Box::new(body),
                return_binder: Some(TypedBinder::new(sym("returned"), variable_type.clone())),
                return_body: Some(Box::new(ret(var("returned")))),
                ops: TypedHandler {
                    arms: vec![TypedHandleOp {
                        name: sym("emit"),
                        instantiation: instantiation.clone(),
                        params: vec![TypedBinder::new(sym("value"), variable_type.clone())],
                        resume: TypedBinder::new(
                            sym("resume"),
                            CoreType::Function(Box::new(CoreFnSig::new(
                                Vec::new(),
                                vec![variable_type],
                                variable_sig.clone(),
                            ))),
                        ),
                        body: TypedComp::new(
                            variable_sig,
                            TypedCompKind::Call {
                                callee: sym("consume"),
                                instantiation,
                                args: vec![var("value")],
                            },
                        ),
                    }],
                    forwarded: vec![TypedForward::new(sym("other"), effect)],
                },
            },
        );

        let substituted = substitute_witnesses(&typed, &quantifiers, &arguments);
        assert_eq!(
            substituted.sig,
            CompSig::new(source(Type::Int), EffRow::singleton("IO"))
        );
        let TypedCompKind::Handle {
            body,
            return_binder,
            ops,
            ..
        } = substituted.kind
        else {
            panic!("expected handler")
        };
        assert_eq!(return_binder.expect("return binder").ty, source(Type::Int));
        assert_eq!(
            ops.forwarded[0].effect,
            Label {
                name: sym("Emit"),
                args: vec![Type::Int],
            }
        );
        assert_eq!(ops.arms[0].params[0].ty, source(Type::Int));
        assert_eq!(
            ops.arms[0].instantiation,
            vec![
                CoreInstantiation::Type(Type::Int),
                CoreInstantiation::Row(EffRow::singleton("IO")),
            ]
        );
        let TypedCompKind::Case(scrutinee, arms) = body.kind else {
            panic!("expected case")
        };
        assert_eq!(scrutinee.ty, source(Type::Int));
        let TypedPattern::Ctor {
            instantiation,
            fields,
            ..
        } = &arms[0].0
        else {
            panic!("expected constructor pattern")
        };
        assert_eq!(instantiation, &ops.arms[0].instantiation);
        assert_eq!(fields[0].as_ref().expect("field").ty, source(Type::Int));
    }

    #[test]
    fn prefix_instantiation_freshens_a_retained_quantifier_before_substitution() {
        let a = sym("a");
        let b = sym("b");
        let signature = CoreFnSig::new(
            vec![CoreQuantifier::Type(a), CoreQuantifier::Type(b)],
            vec![source(Type::Var(a)), source(Type::Var(b))],
            sig(source(Type::Tuple(vec![Type::Var(a), Type::Var(b)]))),
        );
        let specialized =
            instantiate_fn_prefix(&signature, &[CoreInstantiation::Type(Type::Var(b))]);
        let [CoreQuantifier::Type(retained)] = specialized.quantifiers.as_slice() else {
            panic!("expected one retained type quantifier")
        };
        assert_ne!(*retained, b);
        assert_eq!(specialized.params[0], source(Type::Var(b)));
        assert_eq!(specialized.params[1], source(Type::Var(*retained)));
        assert_eq!(
            specialized.body.result,
            source(Type::Tuple(vec![Type::Var(b), Type::Var(*retained)]))
        );
    }
}
