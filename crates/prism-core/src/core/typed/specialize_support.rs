//! Private traversal substrate for witness-preserving dictionary specialization.
//!
//! This module deliberately contains no specialization policy. It supplies the
//! structural operations the typed pass needs while keeping their order locked
//! to the legacy pass: partial witness substitution, term-variable substitution,
//! free-variable collection, and deterministic binder freshening.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names;

use super::verify::{
    substitute_core_type, substitute_fn_sig, substitute_label, substitute_row, substitute_sig,
    substitute_type,
};
use super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedForward, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind,
};

pub(crate) use super::traverse::Rewrite;

/// Substitute any supplied prefix of a quantifier list through every typed-Core
/// witness. Unmatched quantifiers remain rigid, which lets specialization apply
/// only the concrete instance arguments it knows.
pub(crate) fn substitute_witnesses(
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
pub(crate) fn instantiate_fn_prefix(
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

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        self.rewrite_comp_from_hooks(comp, cx)
    }

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
pub(crate) fn substitute_terms(
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

#[cfg(test)]
pub(crate) use super::traverse::count_free_comp_var_visits;
pub(crate) use super::traverse::{
    binder_occurrence, free_comp_var_witnesses, free_comp_vars, free_value_vars,
};

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
pub(crate) fn freshen(comp: &TypedComp, counter: &mut u32, prefix: &'static str) -> TypedComp {
    freshen_with(comp, &BTreeMap::new(), counter, prefix)
}

/// Freshen every binder, seeded with renames supplied by the caller.
pub(crate) fn freshen_with(
    comp: &TypedComp,
    renames: &BTreeMap<Sym, Sym>,
    counter: &mut u32,
    prefix: &'static str,
) -> TypedComp {
    Freshen { counter, prefix }.comp(comp, renames)
}

pub(crate) fn next_fresh(counter: &mut u32, prefix: &'static str) -> Sym {
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
    use std::{collections::BTreeMap, iter, mem, thread};

    use crate::core::fv;
    use crate::core::typed::TypedCoreFn;
    use crate::types::ty::{EffRow, Label};
    use crate::types::Type;
    use prism_syntax::names::FRESH_SPECIALIZE;

    use super::*;

    const DEEP_REWRITE_LAYER_COUNT: usize = 5_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

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
                        instantiation: vec![CoreInstantiation::Type(Type::Int)],
                        params: vec![binder("op_param")],
                        resume: binder("resume"),
                        body: op_body,
                    }],
                    forwarded: vec![TypedForward::new(
                        sym("forwarded"),
                        Label {
                            name: sym("Forwarded"),
                            args: vec![Type::Int],
                        },
                    )],
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

    #[derive(Default)]
    struct HookTrace(Vec<&'static str>);

    impl Rewrite for HookTrace {
        type Ctx = ();

        fn core_type(&mut self, ty: &CoreType, (): &()) -> CoreType {
            self.0.push("type");
            ty.clone()
        }

        fn comp_sig(&mut self, sig: &CompSig, (): &()) -> CompSig {
            self.0.push("comp_sig");
            sig.clone()
        }

        fn fn_sig(&mut self, sig: &CoreFnSig, (): &()) -> CoreFnSig {
            self.0.push("fn_sig");
            sig.clone()
        }

        fn instantiation(
            &mut self,
            instantiation: &CoreInstantiation,
            (): &(),
        ) -> CoreInstantiation {
            self.0.push("instantiation");
            instantiation.clone()
        }

        fn forward(&mut self, forward: &TypedForward, (): &()) -> TypedForward {
            self.0.push("forward");
            forward.clone()
        }
    }

    #[test]
    fn iterative_rewrite_preserves_legacy_hook_order() {
        let function = TypedCoreFn::new(
            sym("traversal"),
            vec![binder("parameter")],
            traversal_fixture(),
            CoreFnSig::new(Vec::new(), vec![int_type()], sig(int_type())),
            0,
        );
        let mut legacy = HookTrace::default();
        let legacy_output = legacy.function(&function, &());
        let mut iterative = HookTrace::default();
        let iterative_output = iterative.rewrite_function_from_hooks(&function, &());

        assert_eq!(iterative.0, legacy.0);
        assert_eq!(iterative_output, legacy_output);
    }

    #[test]
    fn freshening_renames_binders_and_preserves_free_variables() {
        let fixture = traversal_fixture();
        // The only free reference in the fixture is the outer `Bind` producer.
        assert_eq!(
            free_comp_vars(&fixture),
            iter::once(sym("outside")).collect()
        );

        let mut counter = 0;
        let freshened = freshen(&fixture, &mut counter, FRESH_SPECIALIZE);
        // Freshening only rewrites binding occurrences, so the free set is invariant
        // and the counter advances once per binder it introduces.
        assert_eq!(free_comp_vars(&freshened), free_comp_vars(&fixture));
        assert!(counter > 0, "the fixture has binders to freshen");

        // Freshening is deterministic in structure and counter given the same start.
        let mut again = 0;
        let repeat = freshen(&fixture, &mut again, FRESH_SPECIALIZE);
        assert_eq!(freshened.erase(), repeat.erase());
        assert_eq!(counter, again);
    }

    #[test]
    fn free_variables_match_legacy_across_all_binder_families() {
        let typed = traversal_fixture();
        assert_eq!(free_comp_vars(&typed), fv::comp(&typed.clone().erase()));
    }

    #[test]
    fn typed_visit_handles_deep_bind_chain_on_the_normal_stack() {
        const DEPTH: usize = 20_000;
        let mut typed = ret(var("outside"));
        for _ in 0..DEPTH {
            typed = TypedComp::new(
                sig(int_type()),
                TypedCompKind::Bind(
                    Box::new(ret(TypedValue::new(int_type(), TypedValueKind::Int(0)))),
                    binder("shadow"),
                    Box::new(typed),
                ),
            );
        }
        assert_eq!(free_comp_vars(&typed), iter::once(sym("outside")).collect());
        // Recursive destruction of this deliberately adversarial fixture is
        // unrelated to the traversal property under test.
        mem::forget(typed);
    }

    #[test]
    fn typed_rewrite_handles_deep_mixed_terms_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-typed-rewrite".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let type_variable = sym("a");
                let row_variable = sym("e");
                let quantifiers = [
                    CoreQuantifier::Type(type_variable),
                    CoreQuantifier::Row(row_variable),
                ];
                let arguments = [
                    CoreInstantiation::Type(Type::Int),
                    CoreInstantiation::Row(EffRow::singleton("IO")),
                ];
                let variable_type = source(Type::Var(type_variable));
                let variable_sig = CompSig::new(variable_type.clone(), EffRow::Var(row_variable));
                let instantiation = vec![
                    CoreInstantiation::Type(Type::Var(type_variable)),
                    CoreInstantiation::Row(EffRow::Var(row_variable)),
                ];
                let polymorphic_value = || {
                    TypedValue::new(
                        variable_type.clone(),
                        TypedValueKind::Var {
                            name: sym("value"),
                            instantiation: instantiation.clone(),
                        },
                    )
                };
                let mut typed = TypedComp::new(
                    variable_sig.clone(),
                    TypedCompKind::Return(polymorphic_value()),
                );
                for _ in 0..DEEP_REWRITE_LAYER_COUNT {
                    let wrapped = TypedValue::new(
                        variable_type.clone(),
                        TypedValueKind::NewtypeRepr {
                            constructor: sym("Box"),
                            instantiation: instantiation.clone(),
                            value: Box::new(TypedValue::new(
                                variable_type.clone(),
                                TypedValueKind::Reinterpret(Box::new(polymorphic_value())),
                            )),
                        },
                    );
                    let first =
                        TypedComp::new(variable_sig.clone(), TypedCompKind::Return(wrapped));
                    typed = TypedComp::new(
                        variable_sig.clone(),
                        TypedCompKind::Bind(
                            Box::new(first),
                            TypedBinder::new(sym("bound"), variable_type.clone()),
                            Box::new(typed),
                        ),
                    );
                    typed = TypedComp::new(
                        variable_sig.clone(),
                        TypedCompKind::If(
                            TypedValue::new(source(Type::Bool), TypedValueKind::Bool(true)),
                            Box::new(typed),
                            Box::new(TypedComp::new(
                                variable_sig.clone(),
                                TypedCompKind::Return(polymorphic_value()),
                            )),
                        ),
                    );
                    typed = TypedComp::new(
                        variable_sig.clone(),
                        TypedCompKind::Mask(vec![sym("masked")], Box::new(typed)),
                    );
                }

                let rewritten = substitute_witnesses(&typed, &quantifiers, &arguments);
                let expected_sig = CompSig::new(source(Type::Int), EffRow::singleton("IO"));
                let expected_instantiation = vec![
                    CoreInstantiation::Type(Type::Int),
                    CoreInstantiation::Row(EffRow::singleton("IO")),
                ];
                let mut cursor = &rewritten;
                for _ in 0..DEEP_REWRITE_LAYER_COUNT {
                    assert_eq!(cursor.sig(), &expected_sig);
                    let TypedCompKind::Mask(_, masked) = cursor.kind() else {
                        panic!("expected mask")
                    };
                    let TypedCompKind::If(_, yes, _) = masked.kind() else {
                        panic!("expected conditional")
                    };
                    let TypedCompKind::Bind(first, binder, rest) = yes.kind() else {
                        panic!("expected bind")
                    };
                    assert_eq!(binder.ty(), expected_sig.result());
                    let TypedCompKind::Return(wrapped) = first.kind() else {
                        panic!("expected wrapped return")
                    };
                    let TypedValueKind::NewtypeRepr {
                        instantiation,
                        value,
                        ..
                    } = wrapped.kind()
                    else {
                        panic!("expected newtype wrapper")
                    };
                    assert_eq!(instantiation, &expected_instantiation);
                    let TypedValueKind::Reinterpret(value) = value.kind() else {
                        panic!("expected representation wrapper")
                    };
                    let TypedValueKind::Var { instantiation, .. } = value.kind() else {
                        panic!("expected polymorphic value")
                    };
                    assert_eq!(instantiation, &expected_instantiation);
                    cursor = rest;
                }
                assert_eq!(cursor.sig(), &expected_sig);
                let TypedCompKind::Return(value) = cursor.kind() else {
                    panic!("expected tail return")
                };
                let TypedValueKind::Var { instantiation, .. } = value.kind() else {
                    panic!("expected tail value")
                };
                assert_eq!(instantiation, &expected_instantiation);

                mem::forget(typed);
                mem::forget(rewritten);
            })
            .expect("spawn deep typed-rewrite test")
            .join()
            .expect("deep typed-rewrite test panicked");
    }

    #[test]
    fn typed_pass_pipeline_handles_deep_spines_on_an_ordinary_stack() {
        use crate::core::typed::{cse, simplify, Elaborated, UncheckedTypedCore};

        thread::Builder::new()
            .name("deep-typed-passes".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                // Each layer scrutinizes its own condition: a shared variable
                // would let branch refinement constant-fold every nested If,
                // and the fold's whole-subtree clone (recursive derived
                // Clone) is a data operation the construction-time depth
                // budget bounds, not the walks under test here.
                let condition = |layer: usize| {
                    TypedValue::new(
                        source(Type::Bool),
                        TypedValueKind::Var {
                            name: sym(&format!("condition_{layer}")),
                            instantiation: Vec::new(),
                        },
                    )
                };
                let mut typed = ret(var("input"));
                for layer in 0..DEEP_REWRITE_LAYER_COUNT {
                    typed = TypedComp::new(
                        sig(int_type()),
                        TypedCompKind::Bind(
                            Box::new(ret(var("input"))),
                            binder("bound"),
                            Box::new(typed),
                        ),
                    );
                    typed = TypedComp::new(
                        sig(int_type()),
                        TypedCompKind::If(
                            condition(layer),
                            Box::new(typed),
                            Box::new(ret(var("input"))),
                        ),
                    );
                }
                let mut params = vec![binder("input")];
                params.extend((0..DEEP_REWRITE_LAYER_COUNT).map(|layer| {
                    TypedBinder::new(sym(&format!("condition_{layer}")), source(Type::Bool))
                }));
                let signature = CoreFnSig::new(
                    Vec::new(),
                    params.iter().map(|binder| binder.ty.clone()).collect(),
                    typed.sig.clone(),
                );
                let function = TypedCoreFn::new(sym("main"), params, typed, signature, 0);
                let core = UncheckedTypedCore::<Elaborated>::new(vec![function]);
                let (core, _) = simplify(core).expect("the deep spine converges");
                let (core, _) = cse(core);
                // Recursive destruction of the adversarial fixture is a
                // separate concern; the property under test is the passes'
                // control-sensitive walks.
                mem::forget(core);
            })
            .expect("spawn deep-typed-passes test")
            .join()
            .expect("deep pass pipeline panicked on an ordinary stack");
    }

    #[test]
    fn term_substitution_avoids_capture() {
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
        let mut typed_substitution = BTreeMap::new();
        typed_substitution.insert(sym("replace"), var("capture"));
        let mut typed_counter = 0;
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
        // The lambda bound `capture`, so substituting `replace -> capture` must
        // alpha-rename the binder; the freed `capture` therefore stays free.
        let typed = typed.erase();
        assert_eq!(fv::comp(&typed), iter::once(sym("capture")).collect());
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
