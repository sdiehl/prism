//! Witness-preserving dictionary specialization.
//!
//! The term rewrite deliberately mirrors the compatibility pass. The additional
//! work here is scheme-level: every clone records which source quantifiers a
//! concrete dictionary fixes and which source or builder quantifiers must remain
//! abstract. Consequently the legacy memo key remains sufficient even when a
//! polymorphic nullary builder is used at several concrete types.

use std::collections::{BTreeMap, BTreeSet};

use crate::error::TypedCoreSpecializationFailure;
use crate::names::{self, DICT_PREFIX};
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;

use super::specialize_support::{
    free_comp_vars, freshen, substitute_terms, substitute_witnesses, Rewrite,
};
use super::verify::{substitute_core_type, substitute_sig};
use super::{
    instantiate_fn, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, TypedBinder, TypedComp,
    TypedCompKind, TypedCore, TypedCoreFn, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind,
};

/// Rewrite counts for typed dictionary specialization.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SpecializeStats {
    ticks: u64,
}

impl SpecializeStats {
    /// Clones generated plus dictionary projections reduced.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Specialize constrained calls while retaining independently checkable
/// type/effect witnesses.
pub(crate) fn specialize<P>(
    core: TypedCore<P>,
) -> Result<(TypedCore<P>, SpecializeStats), TypedCoreSpecializationFailure> {
    let builders = builders(&core);
    let constrained = constrained(&core);
    if builders.is_empty() || constrained.is_empty() {
        return Ok((core, SpecializeStats::default()));
    }
    let bodies = core
        .fns
        .iter()
        .map(|function| (function.name, function.clone()))
        .collect();
    let mut pass = Specializer {
        builders,
        constrained,
        bodies,
        memo: BTreeMap::new(),
        clones: Vec::new(),
        counter: 0,
        reductions: 0,
        fresh: 0,
        failure: None,
    };
    let empty = BTreeMap::new();
    let mut functions: Vec<_> = core
        .fns
        .iter()
        .map(|function| pass.function(function, &empty))
        .collect();
    if let Some(failure) = pass.failure {
        return Err(failure);
    }
    let ticks = pass.counter as u64 + pass.reductions;
    functions.extend(pass.clones);
    let mut dce = Dce {
        builders: &pass.builders,
    };
    let functions = functions
        .iter()
        .map(|function| dce.function(function, &()))
        .collect();
    Ok((TypedCore::new(functions), SpecializeStats { ticks }))
}

#[derive(Clone)]
struct Builder {
    function: TypedCoreFn,
}

fn builders<P>(core: &TypedCore<P>) -> BTreeMap<Sym, Builder> {
    core.fns
        .iter()
        .filter(|function| function.params.is_empty())
        .filter_map(|function| match &function.body.kind {
            TypedCompKind::Return(TypedValue {
                kind: TypedValueKind::Ctor { name, .. },
                ..
            }) if name.as_str().starts_with(DICT_PREFIX) => Some((
                function.name,
                Builder {
                    function: function.clone(),
                },
            )),
            _ => None,
        })
        .collect()
}

fn constrained<P>(core: &TypedCore<P>) -> BTreeMap<Sym, usize> {
    core.fns
        .iter()
        .filter(|function| function.dict_arity > 0)
        .map(|function| (function.name, function.dict_arity))
        .collect()
}

#[derive(Clone)]
struct BuilderBinding {
    name: Sym,
    instantiation: Vec<CoreInstantiation>,
}

#[derive(Clone)]
struct MemoEntry {
    clone: Sym,
    plan: SpecializationPlan,
}

struct Specializer {
    builders: BTreeMap<Sym, Builder>,
    constrained: BTreeMap<Sym, usize>,
    bodies: BTreeMap<Sym, TypedCoreFn>,
    memo: BTreeMap<(Sym, Vec<Sym>), MemoEntry>,
    clones: Vec<TypedCoreFn>,
    counter: usize,
    reductions: u64,
    fresh: u32,
    failure: Option<TypedCoreSpecializationFailure>,
}

impl Specializer {
    fn fail(&mut self, failure: TypedCoreSpecializationFailure) {
        if self.failure.is_none() {
            self.failure = Some(failure);
        }
    }

    fn request(&mut self, callee: Sym, insts: &[BuilderBinding]) -> Option<MemoEntry> {
        let key = (
            callee,
            insts.iter().map(|binding| binding.name).collect::<Vec<_>>(),
        );
        if let Some(entry) = self.memo.get(&key) {
            return Some(entry.clone());
        }
        let original = self.bodies.get(&callee)?.clone();
        let builder_defs: Option<Vec<_>> = insts
            .iter()
            .map(|binding| self.builders.get(&binding.name).cloned())
            .collect();
        let builder_defs = builder_defs?;
        let plan = match SpecializationPlan::build(&original, &builder_defs) {
            Ok(plan) => plan,
            Err(failure) => {
                self.fail(failure);
                return None;
            }
        };

        self.counter += 1;
        let clone = Sym::from(&names::specialized_clone(callee.as_str(), self.counter));
        let entry = MemoEntry {
            clone,
            plan: plan.clone(),
        };
        // Insert before descending into the clone so self-recursion resolves to
        // the in-flight name, exactly as in compatibility Core.
        self.memo.insert(key, entry.clone());

        let mut body = substitute_witnesses(
            &original.body,
            original.sig.quantifiers(),
            &plan.source_substitution,
        );
        let params: Vec<_> = original
            .params
            .iter()
            .map(|binder| {
                TypedBinder::new(
                    binder.name,
                    substitute_core_type(
                        &binder.ty,
                        original.sig.quantifiers(),
                        &plan.source_substitution,
                    ),
                )
            })
            .collect();
        for index in (0..insts.len()).rev() {
            let builder = &builder_defs[index].function;
            let builder_instantiation = plan.builder_substitutions[index].clone();
            let call_sig = substitute_sig(
                builder.sig.body(),
                builder.sig.quantifiers(),
                &builder_instantiation,
            );
            body = TypedComp::new(
                body.sig.clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        call_sig,
                        TypedCompKind::Call {
                            callee: insts[index].name,
                            instantiation: builder_instantiation,
                            args: Vec::new(),
                        },
                    )),
                    params[index].clone(),
                    Box::new(body),
                ),
            );
        }
        let body = self.comp(&body, &BTreeMap::new());
        let signature = CoreFnSig::new(
            plan.quantifiers.clone(),
            original.sig.params[insts.len()..]
                .iter()
                .map(|ty| {
                    substitute_core_type(ty, original.sig.quantifiers(), &plan.source_substitution)
                })
                .collect(),
            substitute_sig(
                original.sig.body(),
                original.sig.quantifiers(),
                &plan.source_substitution,
            ),
        );
        self.clones.push(TypedCoreFn::new(
            clone,
            params[insts.len()..].to_vec(),
            body,
            signature,
            0,
        ));
        Some(entry)
    }

    fn rewritten_call(
        &mut self,
        comp: &TypedComp,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        env: &BTreeMap<Sym, BuilderBinding>,
    ) -> TypedComp {
        if let Some(&arity) = self.constrained.get(&callee) {
            if args.len() >= arity {
                let builders: Option<Vec<_>> = args[..arity]
                    .iter()
                    .map(|argument| match &argument.kind {
                        TypedValueKind::Var { name, .. } => env.get(name).cloned(),
                        _ => None,
                    })
                    .collect();
                if let Some(builders) = builders {
                    if let Some(entry) = self.request(callee, &builders) {
                        match entry.plan.call_instantiation(
                            callee,
                            instantiation,
                            &builders,
                            &self.builders,
                        ) {
                            Ok(clone_instantiation) => {
                                return TypedComp::new(
                                    comp.sig.clone(),
                                    TypedCompKind::Call {
                                        callee: entry.clone,
                                        instantiation: clone_instantiation,
                                        args: args[arity..]
                                            .iter()
                                            .map(|argument| self.value(argument, env))
                                            .collect(),
                                    },
                                );
                            }
                            Err(failure) => self.fail(failure),
                        }
                    }
                }
            }
        }
        TypedComp::new(
            comp.sig.clone(),
            TypedCompKind::Call {
                callee,
                instantiation: instantiation.to_vec(),
                args: args
                    .iter()
                    .map(|argument| self.value(argument, env))
                    .collect(),
            },
        )
    }

    fn try_reduce_projection(
        &mut self,
        scrutinee: &TypedValue,
        arms: &[(TypedPattern, TypedComp)],
        env: &BTreeMap<Sym, BuilderBinding>,
    ) -> Option<TypedComp> {
        let TypedValueKind::Var { name, .. } = &scrutinee.kind else {
            return None;
        };
        let binding = env.get(name)?;
        let [(TypedPattern::Ctor { fields, .. }, arm)] = arms else {
            return None;
        };
        let mut bound = fields
            .iter()
            .enumerate()
            .filter_map(|(index, binder)| binder.as_ref().map(|binder| (index, binder.name)));
        let (field_index, method) = bound.next()?;
        if bound.next().is_some() {
            return None;
        }
        let TypedCompKind::App {
            callee,
            instantiation: method_instantiation,
            args,
        } = &arm.kind
        else {
            return None;
        };
        let TypedCompKind::Force(TypedValue {
            kind: TypedValueKind::Var { name: forced, .. },
            ..
        }) = &callee.kind
        else {
            return None;
        };
        if *forced != method {
            return None;
        }
        let builder = self.builders.get(&binding.name)?.clone();
        if binding.instantiation.len() != builder.function.sig.quantifiers().len() {
            self.fail(TypedCoreSpecializationFailure::BuilderInstantiationArity {
                builder: binding.name.to_string(),
                actual: binding.instantiation.len(),
                expected: builder.function.sig.quantifiers().len(),
            });
            return None;
        }
        let instantiated = substitute_witnesses(
            &builder.function.body,
            builder.function.sig.quantifiers(),
            &binding.instantiation,
        );
        let TypedCompKind::Return(TypedValue {
            kind: TypedValueKind::Ctor { fields, .. },
            ..
        }) = instantiated.kind
        else {
            return None;
        };
        let method_body = transparent_method_body(fields.get(field_index)?.clone())?;
        let CoreType::Function(method_signature) = method_body.sig.result().clone() else {
            return None;
        };
        let Ok(instantiated_signature) = instantiate_fn(&method_signature, method_instantiation)
        else {
            return None;
        };
        let TypedCompKind::Lam(params, body) = method_body.kind else {
            return None;
        };
        if params.len() != args.len() || params.len() != instantiated_signature.params().len() {
            return None;
        }
        // App's explicit scheme arguments are evidence, not erased decoration.
        // Apply them before beta reduction so the spliced body, its local uses,
        // and its result/effect witness all live at the call's monomorphic
        // instance. `substitute_witnesses` is capture-safe under any nested
        // schemes in the method body.
        let body =
            substitute_witnesses(&body, method_signature.quantifiers(), method_instantiation);
        let values: Vec<_> = args
            .iter()
            .map(|argument| self.value(argument, env))
            .collect();
        let substitution = params
            .into_iter()
            .map(|binder| {
                TypedBinder::new(
                    binder.name,
                    substitute_core_type(
                        &binder.ty,
                        method_signature.quantifiers(),
                        method_instantiation,
                    ),
                )
            })
            .map(|binder| binder.name)
            .zip(values)
            .collect();
        self.reductions += 1;
        let body = freshen(&body, &mut self.fresh, names::FRESH_SPECIALIZE);
        Some(substitute_terms(
            &body,
            &substitution,
            &mut self.fresh,
            names::FRESH_SPECIALIZE,
        ))
    }
}

// Compatibility Core erases these verifier-proven representation witnesses, so
// method recognition must look through the same narrow boundary before matching
// the thunk shape. The inner typed computation and all of its evidence remain
// intact for scheme instantiation and verification.
fn transparent_method_body(mut field: TypedValue) -> Option<TypedComp> {
    loop {
        match field.kind {
            TypedValueKind::Reinterpret(inner)
            | TypedValueKind::NewtypeRepr { value: inner, .. } => field = *inner,
            TypedValueKind::Thunk(body) => return Some(*body),
            _ => return None,
        }
    }
}

impl Rewrite for Specializer {
    type Ctx = BTreeMap<Sym, BuilderBinding>;

    fn comp(&mut self, comp: &TypedComp, env: &Self::Ctx) -> TypedComp {
        match &comp.kind {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, env);
                let mut next = env.clone();
                match &first.kind {
                    TypedCompKind::Call {
                        callee,
                        instantiation,
                        args,
                    } if args.is_empty() && self.builders.contains_key(callee) => {
                        next.insert(
                            binder.name,
                            BuilderBinding {
                                name: *callee,
                                instantiation: instantiation.clone(),
                            },
                        );
                    }
                    _ => {
                        next.remove(&binder.name);
                    }
                }
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(
                        Box::new(first),
                        binder.clone(),
                        Box::new(self.comp(rest, &next)),
                    ),
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => self.rewritten_call(comp, *callee, instantiation, args, env),
            TypedCompKind::Case(scrutinee, arms) => self
                .try_reduce_projection(scrutinee, arms, env)
                .unwrap_or_else(|| self.descend_comp(comp, env)),
            _ => self.descend_comp(comp, env),
        }
    }
}

struct Dce<'a> {
    builders: &'a BTreeMap<Sym, Builder>,
}

impl Rewrite for Dce<'_> {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, _context: &Self::Ctx) -> TypedComp {
        let kind = match &comp.kind {
            TypedCompKind::Bind(first, binder, rest) => {
                let rest = self.comp(rest, &());
                let dead = matches!(
                    &first.kind,
                    TypedCompKind::Call { callee, args, .. }
                        if args.is_empty() && self.builders.contains_key(callee)
                ) && !free_comp_vars(&rest).contains(&binder.name);
                if dead {
                    return rest;
                }
                TypedCompKind::Bind(
                    Box::new(self.comp(first, &())),
                    binder.clone(),
                    Box::new(rest),
                )
            }
            TypedCompKind::Lam(params, body) => {
                TypedCompKind::Lam(params.clone(), Box::new(self.comp(body, &())))
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => TypedCompKind::App {
                callee: Box::new(self.comp(callee, &())),
                instantiation: instantiation.clone(),
                args: args.clone(),
            },
            TypedCompKind::If(condition, yes, no) => TypedCompKind::If(
                condition.clone(),
                Box::new(self.comp(yes, &())),
                Box::new(self.comp(no, &())),
            ),
            TypedCompKind::Case(scrutinee, arms) => TypedCompKind::Case(
                scrutinee.clone(),
                arms.iter()
                    .map(|(pattern, body)| (pattern.clone(), self.comp(body, &())))
                    .collect(),
            ),
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => TypedCompKind::Handle {
                body: Box::new(self.comp(body, &())),
                return_binder: return_binder.clone(),
                return_body: return_body
                    .as_ref()
                    .map(|body| Box::new(self.comp(body, &()))),
                ops: TypedHandler {
                    arms: ops
                        .arms
                        .iter()
                        .map(|arm| TypedHandleOp {
                            name: arm.name,
                            instantiation: arm.instantiation.clone(),
                            params: arm.params.clone(),
                            resume: arm.resume.clone(),
                            body: self.comp(&arm.body, &()),
                        })
                        .collect(),
                    forwarded: ops.forwarded.clone(),
                },
            },
            TypedCompKind::Mask(effects, body) => {
                TypedCompKind::Mask(effects.clone(), Box::new(self.comp(body, &())))
            }
            TypedCompKind::WithReuse { token, freed, body } => TypedCompKind::WithReuse {
                token: token.clone(),
                freed: freed.clone(),
                body: Box::new(self.comp(body, &())),
            },
            // Legacy DCE treats every value position as opaque. In particular,
            // it does not enter thunk bodies through Return or call arguments.
            // Preserve that exact traversal boundary for erased-tree parity.
            _ => return comp.clone(),
        };
        TypedComp::new(comp.sig.clone(), kind)
    }
}

#[derive(Clone, Debug)]
struct SpecializationPlan {
    quantifiers: Vec<CoreQuantifier>,
    parameters: Vec<PlanParameter>,
    source_substitution: Vec<CoreInstantiation>,
    builder_substitutions: Vec<Vec<CoreInstantiation>>,
}

#[derive(Clone, Copy, Debug)]
enum PlanParameter {
    Source(usize),
    Builder {
        dictionary: usize,
        quantifier: usize,
    },
}

impl SpecializationPlan {
    fn build(
        function: &TypedCoreFn,
        builders: &[Builder],
    ) -> Result<Self, TypedCoreSpecializationFailure> {
        let dictionary_arity = function.dict_arity;
        if dictionary_arity > function.sig.params().len() {
            return Err(TypedCoreSpecializationFailure::DictionaryArity {
                function: function.name.to_string(),
                dictionary_arity,
                parameter_arity: function.sig.params().len(),
            });
        }

        let mut alpha = AlphaQuantifiers::new(function.sig.quantifiers(), builders);
        let source_types: Vec<_> = function.sig.params()[..dictionary_arity]
            .iter()
            .map(|ty| substitute_core_type(ty, function.sig.quantifiers(), &alpha.source_arguments))
            .collect();
        let builder_types: Vec<_> = builders
            .iter()
            .enumerate()
            .map(|(index, builder)| {
                substitute_core_type(
                    builder.function.sig.body().result(),
                    builder.function.sig.quantifiers(),
                    &alpha.builder_arguments[index],
                )
            })
            .collect();

        for (index, (source, builder)) in source_types.iter().zip(&builder_types).enumerate() {
            if !alpha.unifier.unify_core(source, builder) {
                return Err(TypedCoreSpecializationFailure::IncompatibleDictionary {
                    function: function.name.to_string(),
                    dictionary_index: index,
                    builder: builders[index].function.name.to_string(),
                });
            }
        }
        Ok(alpha.finish())
    }

    fn call_instantiation(
        &self,
        function: Sym,
        source: &[CoreInstantiation],
        bindings: &[BuilderBinding],
        builders: &BTreeMap<Sym, Builder>,
    ) -> Result<Vec<CoreInstantiation>, TypedCoreSpecializationFailure> {
        let source_expected = self.source_substitution.len();
        if source.len() != source_expected {
            return Err(TypedCoreSpecializationFailure::SourceInstantiationArity {
                function: function.to_string(),
                actual: source.len(),
                expected: source_expected,
            });
        }
        let mut arguments = Vec::with_capacity(self.parameters.len());
        for parameter in &self.parameters {
            match *parameter {
                PlanParameter::Source(index) => arguments.push(source[index].clone()),
                PlanParameter::Builder {
                    dictionary,
                    quantifier,
                } => {
                    let binding = &bindings[dictionary];
                    let expected = builders
                        .get(&binding.name)
                        .map_or(0, |builder| builder.function.sig.quantifiers().len());
                    if binding.instantiation.len() != expected {
                        return Err(TypedCoreSpecializationFailure::BuilderInstantiationArity {
                            builder: binding.name.to_string(),
                            actual: binding.instantiation.len(),
                            expected,
                        });
                    }
                    arguments.push(binding.instantiation[quantifier].clone());
                }
            }
        }
        Ok(arguments)
    }
}

struct AlphaQuantifiers {
    source_arguments: Vec<CoreInstantiation>,
    builder_arguments: Vec<Vec<CoreInstantiation>>,
    variables: Vec<AlphaVariable>,
    unifier: Unifier,
}

#[derive(Clone, Copy)]
struct AlphaVariable {
    internal: Sym,
    original: Sym,
    kind: QuantifierKind,
    origin: PlanParameter,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum QuantifierKind {
    Type,
    Row,
}

impl AlphaQuantifiers {
    fn new(source: &[CoreQuantifier], builders: &[Builder]) -> Self {
        let mut occupied: BTreeSet<_> = source.iter().map(quantifier_name).collect();
        occupied.extend(
            builders
                .iter()
                .flat_map(|builder| builder.function.sig.quantifiers().iter())
                .map(quantifier_name),
        );
        let mut counter = 0;
        let mut variables = Vec::new();
        let mut unifier = Unifier::default();
        let source_arguments = source
            .iter()
            .enumerate()
            .map(|(index, quantifier)| {
                let variable = alpha_variable(
                    quantifier,
                    PlanParameter::Source(index),
                    &mut occupied,
                    &mut counter,
                );
                unifier.insert(variable);
                variables.push(variable);
                variable.argument()
            })
            .collect();
        let builder_arguments = builders
            .iter()
            .enumerate()
            .map(|(dictionary, builder)| {
                builder
                    .function
                    .sig
                    .quantifiers()
                    .iter()
                    .enumerate()
                    .map(|(quantifier, declared)| {
                        let variable = alpha_variable(
                            declared,
                            PlanParameter::Builder {
                                dictionary,
                                quantifier,
                            },
                            &mut occupied,
                            &mut counter,
                        );
                        unifier.insert(variable);
                        variables.push(variable);
                        variable.argument()
                    })
                    .collect()
            })
            .collect();
        Self {
            source_arguments,
            builder_arguments,
            variables,
            unifier,
        }
    }

    fn finish(mut self) -> SpecializationPlan {
        let mut roots = Vec::new();
        for variable in &self.variables {
            if self.unifier.is_root(*variable) {
                roots.push(*variable);
            }
        }
        roots.sort_by_key(|variable| match variable.origin {
            PlanParameter::Source(index) => (0, index, 0),
            PlanParameter::Builder {
                dictionary,
                quantifier,
            } => (1, dictionary, quantifier),
        });

        let mut used = BTreeSet::new();
        let mut fresh = 0;
        let mut quantifiers = Vec::with_capacity(roots.len());
        let mut parameters = Vec::with_capacity(roots.len());
        let mut root_quantifiers = Vec::with_capacity(roots.len());
        let mut root_arguments = Vec::with_capacity(roots.len());
        for root in roots {
            let name = if used.insert(root.original) {
                root.original
            } else {
                loop {
                    let candidate = Sym::from(&names::fresh_binder(
                        names::FRESH_SPECIALIZE_QUANTIFIER,
                        fresh,
                    ));
                    fresh += 1;
                    if used.insert(candidate) {
                        break candidate;
                    }
                }
            };
            let (quantifier, argument) = match root.kind {
                QuantifierKind::Type => (
                    CoreQuantifier::Type(name),
                    CoreInstantiation::Type(Type::Var(name)),
                ),
                QuantifierKind::Row => (
                    CoreQuantifier::Row(name),
                    CoreInstantiation::Row(EffRow::Var(name)),
                ),
            };
            root_quantifiers.push(match root.kind {
                QuantifierKind::Type => CoreQuantifier::Type(root.internal),
                QuantifierKind::Row => CoreQuantifier::Row(root.internal),
            });
            root_arguments.push(argument);
            quantifiers.push(quantifier);
            parameters.push(root.origin);
        }

        let source_substitution = self
            .source_arguments
            .iter()
            .map(|argument| {
                self.unifier
                    .finish_argument(argument, &root_quantifiers, &root_arguments)
            })
            .collect();
        let builder_substitutions = self
            .builder_arguments
            .iter()
            .map(|arguments| {
                arguments
                    .iter()
                    .map(|argument| {
                        self.unifier
                            .finish_argument(argument, &root_quantifiers, &root_arguments)
                    })
                    .collect()
            })
            .collect();
        SpecializationPlan {
            quantifiers,
            parameters,
            source_substitution,
            builder_substitutions,
        }
    }
}

fn alpha_variable(
    quantifier: &CoreQuantifier,
    origin: PlanParameter,
    occupied: &mut BTreeSet<Sym>,
    counter: &mut u32,
) -> AlphaVariable {
    let internal = loop {
        let candidate = Sym::from(&names::fresh_binder(
            names::FRESH_SPECIALIZE_QUANTIFIER,
            *counter,
        ));
        *counter += 1;
        if occupied.insert(candidate) {
            break candidate;
        }
    };
    match quantifier {
        CoreQuantifier::Type(original) => AlphaVariable {
            internal,
            original: *original,
            kind: QuantifierKind::Type,
            origin,
        },
        CoreQuantifier::Row(original) => AlphaVariable {
            internal,
            original: *original,
            kind: QuantifierKind::Row,
            origin,
        },
    }
}

impl AlphaVariable {
    const fn argument(self) -> CoreInstantiation {
        match self.kind {
            QuantifierKind::Type => CoreInstantiation::Type(Type::Var(self.internal)),
            QuantifierKind::Row => CoreInstantiation::Row(EffRow::Var(self.internal)),
        }
    }
}

const fn quantifier_name(quantifier: &CoreQuantifier) -> Sym {
    match quantifier {
        CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => *name,
    }
}

#[derive(Default)]
struct Unifier {
    type_variables: BTreeMap<Sym, AlphaVariable>,
    row_variables: BTreeMap<Sym, AlphaVariable>,
    types: BTreeMap<Sym, Type>,
    rows: BTreeMap<Sym, EffRow>,
}

impl Unifier {
    fn insert(&mut self, variable: AlphaVariable) {
        match variable.kind {
            QuantifierKind::Type => {
                self.type_variables.insert(variable.internal, variable);
            }
            QuantifierKind::Row => {
                self.row_variables.insert(variable.internal, variable);
            }
        }
    }

    fn preferred(&self, left: Sym, right: Sym, kind: QuantifierKind) -> (Sym, Sym) {
        let variables = match kind {
            QuantifierKind::Type => &self.type_variables,
            QuantifierKind::Row => &self.row_variables,
        };
        let rank = |name: Sym| match variables[&name].origin {
            PlanParameter::Builder {
                dictionary,
                quantifier,
            } => (0, dictionary, quantifier),
            PlanParameter::Source(index) => (1, index, 0),
        };
        if rank(left) <= rank(right) {
            (left, right)
        } else {
            (right, left)
        }
    }

    fn is_root(&mut self, variable: AlphaVariable) -> bool {
        match variable.kind {
            QuantifierKind::Type => {
                self.resolve_type(&Type::Var(variable.internal)) == Type::Var(variable.internal)
            }
            QuantifierKind::Row => {
                self.resolve_row(&EffRow::Var(variable.internal)) == EffRow::Var(variable.internal)
            }
        }
    }

    fn finish_argument(
        &mut self,
        argument: &CoreInstantiation,
        roots: &[CoreQuantifier],
        replacements: &[CoreInstantiation],
    ) -> CoreInstantiation {
        match argument {
            CoreInstantiation::Type(ty) => CoreInstantiation::Type(super::verify::substitute_type(
                &self.resolve_type(ty),
                roots,
                replacements,
            )),
            CoreInstantiation::Row(row) => CoreInstantiation::Row(super::verify::substitute_row(
                &self.resolve_row(row),
                roots,
                replacements,
            )),
        }
    }

    fn unify_core(&mut self, left: &CoreType, right: &CoreType) -> bool {
        match (left, right) {
            (CoreType::Source(left), CoreType::Source(right)) => self.unify_type(left, right),
            _ => left == right,
        }
    }

    #[allow(clippy::too_many_lines)]
    fn unify_type(&mut self, left: &Type, right: &Type) -> bool {
        let left = self.resolve_type(left);
        let right = self.resolve_type(right);
        if left == right {
            return true;
        }
        if let Type::Var(name) = left {
            if self.type_variables.contains_key(&name) {
                return self.bind_type(name, right);
            }
            return false;
        }
        if let Type::Var(name) = right {
            if self.type_variables.contains_key(&name) {
                return self.bind_type(name, left);
            }
            return false;
        }
        match (left, right) {
            (Type::Fun(lp, le, lr), Type::Fun(rp, re, rr)) => {
                lp.len() == rp.len()
                    && lp.iter().zip(&rp).all(|(l, r)| self.unify_type(l, r))
                    && self.unify_row(&le, &re)
                    && self.unify_type(&lr, &rr)
            }
            (Type::Con(ln, la), Type::Con(rn, ra)) => {
                ln == rn
                    && la.len() == ra.len()
                    && la.iter().zip(&ra).all(|(l, r)| self.unify_type(l, r))
            }
            (Type::App(lh, la), Type::App(rh, ra)) => {
                self.unify_type(&lh, &rh) && self.unify_type(&la, &ra)
            }
            (Type::Tuple(left), Type::Tuple(right))
            | (Type::UnboxedTuple(left), Type::UnboxedTuple(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(&right)
                        .all(|(left, right)| self.unify_type(left, right))
            }
            (Type::UnboxedRecord(left), Type::UnboxedRecord(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(&right)
                        .all(|((ln, lt), (rn, rt))| ln == rn && self.unify_type(lt, rt))
            }
            (Type::OrNull(left), Type::OrNull(right)) => self.unify_type(&left, &right),
            (Type::Row(left), Type::Row(right)) => self.unify_row(&left, &right),
            (Type::Coeffect(left, lc), Type::Coeffect(right, rc)) => {
                lc == rc && self.unify_type(&left, &right)
            }
            (left, right) => left == right,
        }
    }

    fn bind_type(&mut self, name: Sym, value: Type) -> bool {
        if let Type::Var(other) = value {
            if self.type_variables.contains_key(&other) {
                let (keep, bind) = self.preferred(name, other, QuantifierKind::Type);
                self.types.insert(bind, Type::Var(keep));
                return true;
            }
            self.types.insert(name, Type::Var(other));
            return true;
        }
        if occurs_type(name, &value) {
            return false;
        }
        self.types.insert(name, value);
        true
    }

    fn unify_row(&mut self, left: &EffRow, right: &EffRow) -> bool {
        let left = self.resolve_row(left);
        let right = self.resolve_row(right);
        if left == right {
            return true;
        }
        if let EffRow::Var(name) = left {
            if self.row_variables.contains_key(&name) {
                return self.bind_row(name, right);
            }
            return false;
        }
        if let EffRow::Var(name) = right {
            if self.row_variables.contains_key(&name) {
                return self.bind_row(name, left);
            }
            return false;
        }
        match (left, right) {
            (EffRow::Extend(ll, lr), EffRow::Extend(rl, rr)) => {
                ll.name == rl.name
                    && ll.args.len() == rl.args.len()
                    && ll
                        .args
                        .iter()
                        .zip(&rl.args)
                        .all(|(left, right)| self.unify_type(left, right))
                    && self.unify_row(&lr, &rr)
            }
            (left, right) => left == right,
        }
    }

    fn bind_row(&mut self, name: Sym, value: EffRow) -> bool {
        if let EffRow::Var(other) = value {
            if self.row_variables.contains_key(&other) {
                let (keep, bind) = self.preferred(name, other, QuantifierKind::Row);
                self.rows.insert(bind, EffRow::Var(keep));
                return true;
            }
            self.rows.insert(name, EffRow::Var(other));
            return true;
        }
        if occurs_row(name, &value) {
            return false;
        }
        self.rows.insert(name, value);
        true
    }

    fn resolve_type(&mut self, ty: &Type) -> Type {
        match ty {
            Type::Var(name) => {
                if let Some(value) = self.types.get(name).cloned() {
                    let value = self.resolve_type(&value);
                    self.types.insert(*name, value.clone());
                    value
                } else {
                    ty.clone()
                }
            }
            Type::Forall(name, body) => Type::Forall(*name, Box::new(self.resolve_type(body))),
            Type::RowForall(name, body) => {
                Type::RowForall(*name, Box::new(self.resolve_type(body)))
            }
            Type::Fun(params, effects, result) => Type::Fun(
                params.iter().map(|ty| self.resolve_type(ty)).collect(),
                self.resolve_row(effects),
                Box::new(self.resolve_type(result)),
            ),
            Type::Con(name, args) => {
                Type::Con(*name, args.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::App(head, argument) => Type::App(
                Box::new(self.resolve_type(head)),
                Box::new(self.resolve_type(argument)),
            ),
            Type::Tuple(fields) => {
                Type::Tuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedTuple(fields) => {
                Type::UnboxedTuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedRecord(fields) => Type::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.resolve_type(ty)))
                    .collect(),
            ),
            Type::OrNull(inner) => Type::OrNull(Box::new(self.resolve_type(inner))),
            Type::Row(row) => Type::Row(self.resolve_row(row)),
            Type::Coeffect(inner, row) => {
                Type::Coeffect(Box::new(self.resolve_type(inner)), row.clone())
            }
            other => other.clone(),
        }
    }

    fn resolve_row(&mut self, row: &EffRow) -> EffRow {
        match row {
            EffRow::Var(name) => {
                if let Some(value) = self.rows.get(name).cloned() {
                    let value = self.resolve_row(&value);
                    self.rows.insert(*name, value.clone());
                    value
                } else {
                    row.clone()
                }
            }
            EffRow::Extend(label, rest) => EffRow::Extend(
                crate::types::ty::Label {
                    name: label.name,
                    args: label.args.iter().map(|ty| self.resolve_type(ty)).collect(),
                },
                Box::new(self.resolve_row(rest)),
            ),
            other => other.clone(),
        }
    }
}

fn occurs_type(name: Sym, ty: &Type) -> bool {
    let mut variables = BTreeSet::new();
    ty.free_ty_vars(&mut variables);
    variables.contains(&name)
}

fn occurs_row(name: Sym, row: &EffRow) -> bool {
    let mut variables = BTreeSet::new();
    if let EffRow::Var(tail) = row.tail() {
        variables.insert(*tail);
    }
    for label in row.labels() {
        for argument in &label.args {
            argument.free_row_vars(&mut variables);
        }
    }
    variables.contains(&name)
}

#[cfg(test)]
mod tests {
    use crate::core::opt::{run_spec_stage, CorePass, PassStage};
    use crate::error::{Error, TYPED_CORE_SPECIALIZATION};
    use crate::flags::DynFlags;

    use super::super::verify::ConstructorSig;
    use super::super::{verify, CompSig, Elaborated, VerifyEnv};
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn source(ty: Type) -> CoreType {
        CoreType::Source(ty)
    }

    fn pure(result: CoreType) -> CompSig {
        CompSig::new(result, EffRow::Empty)
    }

    fn dict_ty(class: &str, argument: Type) -> CoreType {
        source(Type::Con(sym(class), vec![argument]))
    }

    fn method_signature(argument: Type) -> CoreFnSig {
        CoreFnSig::new(
            Vec::new(),
            vec![source(argument.clone())],
            pure(source(argument)),
        )
    }

    fn method_type(argument: Type) -> CoreType {
        let lambda = pure(CoreType::Function(Box::new(method_signature(argument))));
        CoreType::Thunk(Box::new(lambda))
    }

    fn variable(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn literal(ty: &Type) -> TypedValue {
        match ty {
            Type::Int => TypedValue::new(source(Type::Int), TypedValueKind::Int(7)),
            Type::Bool => TypedValue::new(source(Type::Bool), TypedValueKind::Bool(true)),
            other => panic!("test literal does not support {other:?}"),
        }
    }

    fn identity_method(argument: Type, binder_name: &str) -> TypedValue {
        let binder = TypedBinder::new(sym(binder_name), source(argument.clone()));
        let body = TypedComp::new(
            pure(source(argument.clone())),
            TypedCompKind::Return(variable(binder_name, source(argument.clone()))),
        );
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(method_signature(argument)))),
            TypedCompKind::Lam(vec![binder], Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig.clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        )
    }

    fn type_polymorphic_method(quantifier: &str, binder_name: &str) -> TypedValue {
        let bound = sym(quantifier);
        let argument = Type::Var(bound);
        let signature = CoreFnSig::new(
            vec![CoreQuantifier::Type(bound)],
            vec![source(argument.clone())],
            pure(source(argument.clone())),
        );
        let binder = TypedBinder::new(sym(binder_name), source(argument.clone()));
        let body = TypedComp::new(
            pure(source(argument.clone())),
            TypedCompKind::Return(variable(binder_name, source(argument))),
        );
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(signature))),
            TypedCompKind::Lam(vec![binder], Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig.clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        )
    }

    fn row_polymorphic_method(quantifier: &str) -> TypedValue {
        let bound = sym(quantifier);
        let signature = CoreFnSig::new(
            vec![CoreQuantifier::Row(bound)],
            Vec::new(),
            CompSig::new(source(Type::Int), EffRow::Var(bound)),
        );
        let body = TypedComp::new(
            CompSig::new(source(Type::Int), EffRow::Var(bound)),
            TypedCompKind::Error(TypedValue::new(
                source(Type::Str),
                TypedValueKind::Str("unreachable polymorphic method".into()),
            )),
        );
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(signature))),
            TypedCompKind::Lam(Vec::new(), Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig.clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        )
    }

    fn install_dictionary_constructor_with_field(
        env: &mut VerifyEnv,
        class: &str,
        field: CoreType,
    ) {
        let parameter = sym(&format!("{class}_ctor_a"));
        env.insert_constructor(
            sym(class),
            ConstructorSig::new(
                vec![CoreQuantifier::Type(parameter)],
                0,
                vec![field],
                dict_ty(class, Type::Var(parameter)),
            ),
        );
    }

    fn builder_with_field(
        name: &str,
        class: &str,
        argument: Type,
        field: TypedValue,
    ) -> TypedCoreFn {
        let dictionary = dict_ty(class, argument.clone());
        TypedCoreFn::new(
            sym(name),
            Vec::new(),
            TypedComp::new(
                pure(dictionary.clone()),
                TypedCompKind::Return(TypedValue::new(
                    dictionary.clone(),
                    TypedValueKind::Ctor {
                        name: sym(class),
                        tag: 0,
                        instantiation: vec![CoreInstantiation::Type(argument)],
                        fields: vec![field],
                    },
                )),
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure(dictionary)),
            0,
        )
    }

    fn independently_polymorphic_projection(
        name: &str,
        class: &str,
        method_type: CoreType,
        method_instantiation: Vec<CoreInstantiation>,
        argument_types: &[Type],
        result: CoreType,
        effects: EffRow,
    ) -> TypedCoreFn {
        let dictionary = dict_ty(class, Type::Int);
        let dict_name = format!("{name}_dict");
        let method_name = format!("{name}_method");
        let mut params = vec![TypedBinder::new(sym(&dict_name), dictionary.clone())];
        params.extend(argument_types.iter().enumerate().map(|(index, ty)| {
            TypedBinder::new(sym(&format!("{name}_arg_{index}")), source(ty.clone()))
        }));
        let CoreType::Thunk(force_signature) = &method_type else {
            panic!("test method must be a thunk")
        };
        let force = TypedComp::new(
            force_signature.as_ref().clone(),
            TypedCompKind::Force(variable(&method_name, method_type.clone())),
        );
        let application = TypedComp::new(
            CompSig::new(result.clone(), effects.clone()),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: method_instantiation,
                args: argument_types
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| variable(&format!("{name}_arg_{index}"), source(ty.clone())))
                    .collect(),
            },
        );
        let body = TypedComp::new(
            CompSig::new(result.clone(), effects.clone()),
            TypedCompKind::Case(
                variable(&dict_name, dictionary),
                vec![(
                    TypedPattern::Ctor {
                        name: sym(class),
                        instantiation: vec![CoreInstantiation::Type(Type::Int)],
                        fields: vec![Some(TypedBinder::new(sym(&method_name), method_type))],
                    },
                    application,
                )],
            ),
        );
        TypedCoreFn::new(
            sym(name),
            params.clone(),
            body,
            CoreFnSig::new(
                Vec::new(),
                params.iter().map(|binder| binder.ty.clone()).collect(),
                CompSig::new(result, effects),
            ),
            1,
        )
    }

    fn direct_main(
        builder: &str,
        class: &str,
        target: &str,
        values: Vec<TypedValue>,
        result: CoreType,
        effects: EffRow,
    ) -> TypedCoreFn {
        let dictionary = dict_ty(class, Type::Int);
        let binder = TypedBinder::new(sym("direct_main_dict"), dictionary.clone());
        let mut arguments = vec![variable("direct_main_dict", dictionary.clone())];
        arguments.extend(values);
        let call = TypedComp::new(
            CompSig::new(result.clone(), effects.clone()),
            TypedCompKind::Call {
                callee: sym(target),
                instantiation: Vec::new(),
                args: arguments,
            },
        );
        let body = TypedComp::new(
            CompSig::new(result.clone(), effects.clone()),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    pure(dictionary),
                    TypedCompKind::Call {
                        callee: sym(builder),
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
                binder,
                Box::new(call),
            ),
        );
        TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(result, effects)),
            0,
        )
    }

    fn residual_row_function(name: &str, class: &str, row: &str) -> TypedCoreFn {
        let row = sym(row);
        let argument = sym(&format!("{name}_a"));
        let dictionary = dict_ty(class, Type::Var(argument));
        let body_sig = CompSig::new(source(Type::Int), EffRow::Var(row));
        TypedCoreFn::new(
            sym(name),
            vec![TypedBinder::new(
                sym(&format!("{name}_dict")),
                dictionary.clone(),
            )],
            TypedComp::new(
                body_sig.clone(),
                TypedCompKind::Error(TypedValue::new(
                    source(Type::Str),
                    TypedValueKind::Str("residual row witness".into()),
                )),
            ),
            CoreFnSig::new(
                vec![CoreQuantifier::Type(argument), CoreQuantifier::Row(row)],
                vec![dictionary],
                body_sig,
            ),
            1,
        )
    }

    fn residual_row_main(builder: &str, class: &str, target: &str, row: EffRow) -> TypedCoreFn {
        let dictionary = dict_ty(class, Type::Int);
        let binder = TypedBinder::new(sym("row_main_dict"), dictionary.clone());
        let result = CompSig::new(source(Type::Int), row.clone());
        let call = TypedComp::new(
            result.clone(),
            TypedCompKind::Call {
                callee: sym(target),
                instantiation: vec![
                    CoreInstantiation::Type(Type::Int),
                    CoreInstantiation::Row(row),
                ],
                args: vec![variable("row_main_dict", dictionary.clone())],
            },
        );
        let body = TypedComp::new(
            result.clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    pure(dictionary),
                    TypedCompKind::Call {
                        callee: sym(builder),
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
                binder,
                Box::new(call),
            ),
        );
        TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), result),
            0,
        )
    }

    fn install_dictionary_constructor(env: &mut VerifyEnv, class: &str) {
        let parameter = sym(&format!("{class}_ctor_a"));
        env.insert_constructor(
            sym(class),
            ConstructorSig::new(
                vec![CoreQuantifier::Type(parameter)],
                0,
                vec![method_type(Type::Var(parameter))],
                dict_ty(class, Type::Var(parameter)),
            ),
        );
    }

    fn builder(name: &str, class: &str, quantifier: Option<&str>, argument: Type) -> TypedCoreFn {
        let quantifiers = quantifier
            .map(|name| vec![CoreQuantifier::Type(sym(name))])
            .unwrap_or_default();
        let dictionary = dict_ty(class, argument.clone());
        let method = identity_method(argument.clone(), &format!("{name}_method_arg"));
        TypedCoreFn::new(
            sym(name),
            Vec::new(),
            TypedComp::new(
                pure(dictionary.clone()),
                TypedCompKind::Return(TypedValue::new(
                    dictionary.clone(),
                    TypedValueKind::Ctor {
                        name: sym(class),
                        tag: 0,
                        instantiation: vec![CoreInstantiation::Type(argument)],
                        fields: vec![method],
                    },
                )),
            ),
            CoreFnSig::new(quantifiers, Vec::new(), pure(dictionary)),
            0,
        )
    }

    fn projection_function(name: &str, class: &str) -> TypedCoreFn {
        let argument = sym(&format!("{name}_a"));
        let argument_ty = Type::Var(argument);
        let dictionary = dict_ty(class, argument_ty.clone());
        let method_ty = method_type(argument_ty.clone());
        let dict_binder = TypedBinder::new(sym(&format!("{name}_dict")), dictionary.clone());
        let value_binder =
            TypedBinder::new(sym(&format!("{name}_value")), source(argument_ty.clone()));
        let method_binder = TypedBinder::new(sym(&format!("{name}_method")), method_ty.clone());
        let force = TypedComp::new(
            pure(CoreType::Function(Box::new(method_signature(
                argument_ty.clone(),
            )))),
            TypedCompKind::Force(variable(&format!("{name}_method"), method_ty)),
        );
        let application = TypedComp::new(
            pure(source(argument_ty.clone())),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![variable(
                    &format!("{name}_value"),
                    source(argument_ty.clone()),
                )],
            },
        );
        let body = TypedComp::new(
            pure(source(argument_ty.clone())),
            TypedCompKind::Case(
                variable(&format!("{name}_dict"), dictionary.clone()),
                vec![(
                    TypedPattern::Ctor {
                        name: sym(class),
                        instantiation: vec![CoreInstantiation::Type(argument_ty.clone())],
                        fields: vec![Some(method_binder)],
                    },
                    application,
                )],
            ),
        );
        TypedCoreFn::new(
            sym(name),
            vec![dict_binder, value_binder],
            body,
            CoreFnSig::new(
                vec![CoreQuantifier::Type(argument)],
                vec![dictionary, source(argument_ty.clone())],
                pure(source(argument_ty)),
            ),
            1,
        )
    }

    fn plain_function(
        name: &str,
        quantifiers: &[&str],
        dictionaries: &[(&str, Type)],
        value: Type,
        recursive: bool,
    ) -> TypedCoreFn {
        let mut params: Vec<_> = dictionaries
            .iter()
            .enumerate()
            .map(|(index, (class, argument))| {
                TypedBinder::new(
                    sym(&format!("{name}_dict_{index}")),
                    dict_ty(class, argument.clone()),
                )
            })
            .collect();
        params.push(TypedBinder::new(
            sym(&format!("{name}_value")),
            source(value.clone()),
        ));
        let body = if recursive {
            TypedComp::new(
                pure(source(value.clone())),
                TypedCompKind::Call {
                    callee: sym(name),
                    instantiation: quantifiers
                        .iter()
                        .map(|name| CoreInstantiation::Type(Type::Var(sym(name))))
                        .collect(),
                    args: params
                        .iter()
                        .map(|binder| variable(binder.name.as_str(), binder.ty.clone()))
                        .collect(),
                },
            )
        } else {
            TypedComp::new(
                pure(source(value.clone())),
                TypedCompKind::Return(variable(&format!("{name}_value"), source(value.clone()))),
            )
        };
        TypedCoreFn::new(
            sym(name),
            params.clone(),
            body,
            CoreFnSig::new(
                quantifiers
                    .iter()
                    .map(|name| CoreQuantifier::Type(sym(name)))
                    .collect(),
                params.iter().map(|binder| binder.ty.clone()).collect(),
                pure(source(value)),
            ),
            dictionaries.len(),
        )
    }

    #[derive(Clone)]
    struct BuilderUse {
        name: &'static str,
        class: &'static str,
        instantiation: Vec<CoreInstantiation>,
        argument: Type,
    }

    #[derive(Clone)]
    struct Invocation {
        builders: Vec<BuilderUse>,
        instantiation: Vec<CoreInstantiation>,
        value: Type,
    }

    fn invocation_body(target: &str, invocations: &[Invocation], index: usize) -> TypedComp {
        let invocation = &invocations[index];
        let dictionary_binders: Vec<_> = invocation
            .builders
            .iter()
            .enumerate()
            .map(|(builder_index, builder)| {
                TypedBinder::new(
                    sym(&format!("main_dict_{index}_{builder_index}")),
                    dict_ty(builder.class, builder.argument.clone()),
                )
            })
            .collect();
        let mut arguments: Vec<_> = dictionary_binders
            .iter()
            .map(|binder| variable(binder.name.as_str(), binder.ty.clone()))
            .collect();
        arguments.push(literal(&invocation.value));
        let call = TypedComp::new(
            pure(source(invocation.value.clone())),
            TypedCompKind::Call {
                callee: sym(target),
                instantiation: invocation.instantiation.clone(),
                args: arguments,
            },
        );
        let mut body = if index + 1 == invocations.len() {
            call
        } else {
            let rest = invocation_body(target, invocations, index + 1);
            TypedComp::new(
                rest.sig.clone(),
                TypedCompKind::Bind(
                    Box::new(call),
                    TypedBinder::new(
                        sym(&format!("main_result_{index}")),
                        source(invocation.value.clone()),
                    ),
                    Box::new(rest),
                ),
            )
        };
        for (builder_index, builder) in invocation.builders.iter().enumerate().rev() {
            let dictionary = dict_ty(builder.class, builder.argument.clone());
            body = TypedComp::new(
                body.sig.clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        pure(dictionary),
                        TypedCompKind::Call {
                            callee: sym(builder.name),
                            instantiation: builder.instantiation.clone(),
                            args: Vec::new(),
                        },
                    )),
                    dictionary_binders[builder_index].clone(),
                    Box::new(body),
                ),
            );
        }
        body
    }

    fn main_function(target: &str, invocations: &[Invocation]) -> TypedCoreFn {
        let body = invocation_body(target, invocations, 0);
        TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            body.clone(),
            CoreFnSig::new(Vec::new(), Vec::new(), body.sig),
            0,
        )
    }

    fn assert_differential(
        functions: Vec<TypedCoreFn>,
        env: &VerifyEnv,
    ) -> (TypedCore<Elaborated>, u64) {
        let input = TypedCore::new(functions);
        if let Err(violations) = verify(&input, env) {
            panic!("input fixture is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let (expected, legacy_stats) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &[CorePass::Specialize],
            PassStage::PreLowering,
            &[],
            &DynFlags::default(),
        );
        let expected_ticks = legacy_stats.total();
        let (actual, stats) = specialize(input).expect("typed specialization");
        if let Err(violations) = verify(&actual, env) {
            panic!("specialized typed Core is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        assert_eq!(stats.ticks(), expected_ticks);
        (actual, expected_ticks)
    }

    #[test]
    fn monomorphic_builder_matches_legacy_projection_ticks_and_clone_order() {
        let mut env = VerifyEnv::new();
        install_dictionary_constructor(&mut env, "_DIdentity");
        let functions = vec![
            builder("identityInt", "_DIdentity", None, Type::Int),
            projection_function("applyIdentity", "_DIdentity"),
            main_function(
                "applyIdentity",
                &[Invocation {
                    builders: vec![BuilderUse {
                        name: "identityInt",
                        class: "_DIdentity",
                        instantiation: Vec::new(),
                        argument: Type::Int,
                    }],
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    value: Type::Int,
                }],
            ),
        ];
        let (actual, ticks) = assert_differential(functions, &env);
        assert_eq!(ticks, 2, "one clone plus one reduced projection");
        assert_eq!(
            actual
                .functions()
                .iter()
                .map(TypedCoreFn::name)
                .collect::<Vec<_>>(),
            vec![
                sym("identityInt"),
                sym("applyIdentity"),
                sym("main"),
                sym("applyIdentity$sp1"),
            ]
        );
        let clone = actual.functions().last().expect("specialized clone");
        assert!(clone.sig.quantifiers().is_empty());
    }

    #[test]
    fn independently_type_polymorphic_method_is_instantiated_before_splicing() {
        let mut env = VerifyEnv::new();
        let method = type_polymorphic_method("method_a", "poly_method_arg");
        // Real effect-polymorphic class methods (for example Foldable.fold_l)
        // cross the source/Core representation seam through this transparent
        // evidence wrapper before reaching the dictionary cell.
        let field = TypedValue::new(
            method.ty.clone(),
            TypedValueKind::Reinterpret(Box::new(method)),
        );
        let field_type = field.ty.clone();
        install_dictionary_constructor_with_field(&mut env, "_DPolyMethod", field_type.clone());
        let functions = vec![
            builder_with_field("polyMethodInt", "_DPolyMethod", Type::Int, field),
            independently_polymorphic_projection(
                "applyPolyMethod",
                "_DPolyMethod",
                field_type,
                vec![CoreInstantiation::Type(Type::Bool)],
                &[Type::Bool],
                source(Type::Bool),
                EffRow::Empty,
            ),
            direct_main(
                "polyMethodInt",
                "_DPolyMethod",
                "applyPolyMethod",
                vec![literal(&Type::Bool)],
                source(Type::Bool),
                EffRow::Empty,
            ),
        ];
        let (actual, ticks) = assert_differential(functions, &env);
        assert_eq!(ticks, 2, "one clone plus one polymorphic projection");
        let clone = actual.functions().last().expect("specialized clone");
        assert_eq!(clone.body.sig.result(), &source(Type::Bool));
        let TypedCompKind::Return(value) = &clone.body.kind else {
            panic!("polymorphic identity method should reduce to its argument")
        };
        assert_eq!(value.ty(), &source(Type::Bool));
    }

    #[test]
    fn independently_row_polymorphic_method_instantiates_body_effects() {
        let mut env = VerifyEnv::new();
        let field = row_polymorphic_method("method_e");
        let field_type = field.ty.clone();
        install_dictionary_constructor_with_field(&mut env, "_DRowMethod", field_type.clone());
        let io = EffRow::singleton(crate::names::IO_EFFECT);
        let functions = vec![
            builder_with_field("rowMethodInt", "_DRowMethod", Type::Int, field),
            independently_polymorphic_projection(
                "applyRowMethod",
                "_DRowMethod",
                field_type,
                vec![CoreInstantiation::Row(io.clone())],
                &[],
                source(Type::Int),
                io.clone(),
            ),
            direct_main(
                "rowMethodInt",
                "_DRowMethod",
                "applyRowMethod",
                Vec::new(),
                source(Type::Int),
                io.clone(),
            ),
        ];
        let (actual, ticks) = assert_differential(functions, &env);
        assert_eq!(ticks, 2, "one clone plus one row-polymorphic projection");
        let clone = actual.functions().last().expect("specialized clone");
        assert_eq!(clone.body.sig.effects(), &io);
        assert!(matches!(clone.body.kind, TypedCompKind::Error(_)));
    }

    #[test]
    fn residual_source_quantifier_survives_a_monomorphic_dictionary() {
        let mut env = VerifyEnv::new();
        install_dictionary_constructor(&mut env, "_DResidual");
        let function = plain_function(
            "keepResidual",
            &["res_a", "res_b"],
            &[("_DResidual", Type::Var(sym("res_a")))],
            Type::Var(sym("res_b")),
            false,
        );
        let functions = vec![
            builder("residualInt", "_DResidual", None, Type::Int),
            function,
            main_function(
                "keepResidual",
                &[Invocation {
                    builders: vec![BuilderUse {
                        name: "residualInt",
                        class: "_DResidual",
                        instantiation: Vec::new(),
                        argument: Type::Int,
                    }],
                    instantiation: vec![
                        CoreInstantiation::Type(Type::Int),
                        CoreInstantiation::Type(Type::Bool),
                    ],
                    value: Type::Bool,
                }],
            ),
        ];
        let (actual, _) = assert_differential(functions, &env);
        let clone = actual.functions().last().expect("specialized clone");
        assert_eq!(
            clone.sig.quantifiers(),
            &[CoreQuantifier::Type(sym("res_b"))]
        );
    }

    #[test]
    fn residual_source_row_quantifier_survives_a_monomorphic_dictionary() {
        let mut env = VerifyEnv::new();
        install_dictionary_constructor(&mut env, "_DResidualRow");
        let io = EffRow::singleton(crate::names::IO_EFFECT);
        let functions = vec![
            builder("residualRowInt", "_DResidualRow", None, Type::Int),
            residual_row_function("keepResidualRow", "_DResidualRow", "residual_e"),
            residual_row_main("residualRowInt", "_DResidualRow", "keepResidualRow", io),
        ];
        let (actual, ticks) = assert_differential(functions, &env);
        assert_eq!(ticks, 1);
        let clone = actual.functions().last().expect("specialized clone");
        assert_eq!(
            clone.sig.quantifiers(),
            &[CoreQuantifier::Row(sym("residual_e"))]
        );
        assert_eq!(clone.body.sig.effects(), &EffRow::Var(sym("residual_e")));
    }

    #[test]
    fn polymorphic_nullary_builder_used_at_two_types_produces_one_clone() {
        let mut env = VerifyEnv::new();
        install_dictionary_constructor(&mut env, "_DBlit");
        let functions = vec![
            builder(
                "blitArray",
                "_DBlit",
                Some("blit_element"),
                Type::Var(sym("blit_element")),
            ),
            projection_function("blit", "_DBlit"),
            main_function(
                "blit",
                &[
                    Invocation {
                        builders: vec![BuilderUse {
                            name: "blitArray",
                            class: "_DBlit",
                            instantiation: vec![CoreInstantiation::Type(Type::Int)],
                            argument: Type::Int,
                        }],
                        instantiation: vec![CoreInstantiation::Type(Type::Int)],
                        value: Type::Int,
                    },
                    Invocation {
                        builders: vec![BuilderUse {
                            name: "blitArray",
                            class: "_DBlit",
                            instantiation: vec![CoreInstantiation::Type(Type::Bool)],
                            argument: Type::Bool,
                        }],
                        instantiation: vec![CoreInstantiation::Type(Type::Bool)],
                        value: Type::Bool,
                    },
                ],
            ),
        ];
        let (actual, ticks) = assert_differential(functions, &env);
        assert_eq!(ticks, 2, "one clone and one clone-local projection");
        assert_eq!(
            actual
                .functions()
                .iter()
                .filter(|function| function.name.as_str().starts_with("blit$sp"))
                .count(),
            1
        );
        let clone = actual.functions().last().expect("specialized clone");
        assert_eq!(clone.sig.quantifiers().len(), 1);
    }

    #[test]
    fn shared_builder_quantifier_is_retained_once() {
        let mut env = VerifyEnv::new();
        install_dictionary_constructor(&mut env, "_DLeft");
        install_dictionary_constructor(&mut env, "_DRight");
        let shared = sym("shared_a");
        let function = plain_function(
            "shared",
            &["shared_a"],
            &[
                ("_DLeft", Type::Var(shared)),
                ("_DRight", Type::Var(shared)),
            ],
            Type::Var(shared),
            false,
        );
        let functions = vec![
            builder(
                "leftAny",
                "_DLeft",
                Some("left_a"),
                Type::Var(sym("left_a")),
            ),
            builder(
                "rightAny",
                "_DRight",
                Some("right_a"),
                Type::Var(sym("right_a")),
            ),
            function,
            main_function(
                "shared",
                &[Invocation {
                    builders: vec![
                        BuilderUse {
                            name: "leftAny",
                            class: "_DLeft",
                            instantiation: vec![CoreInstantiation::Type(Type::Int)],
                            argument: Type::Int,
                        },
                        BuilderUse {
                            name: "rightAny",
                            class: "_DRight",
                            instantiation: vec![CoreInstantiation::Type(Type::Int)],
                            argument: Type::Int,
                        },
                    ],
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    value: Type::Int,
                }],
            ),
        ];
        let (actual, _) = assert_differential(functions, &env);
        assert_eq!(
            actual.functions().last().unwrap().sig.quantifiers().len(),
            1
        );
    }

    #[test]
    fn recursive_specialization_uses_the_in_flight_clone() {
        let mut env = VerifyEnv::new();
        install_dictionary_constructor(&mut env, "_DRecursive");
        let recursive = plain_function(
            "recur",
            &["recur_a"],
            &[("_DRecursive", Type::Var(sym("recur_a")))],
            Type::Var(sym("recur_a")),
            true,
        );
        let functions = vec![
            builder("recursiveInt", "_DRecursive", None, Type::Int),
            recursive,
            main_function(
                "recur",
                &[Invocation {
                    builders: vec![BuilderUse {
                        name: "recursiveInt",
                        class: "_DRecursive",
                        instantiation: Vec::new(),
                        argument: Type::Int,
                    }],
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    value: Type::Int,
                }],
            ),
        ];
        let (actual, ticks) = assert_differential(functions, &env);
        assert_eq!(ticks, 1);
        let clone = actual.functions().last().expect("specialized clone");
        let TypedCompKind::Call { callee, .. } = &clone.body.kind else {
            panic!("dictionary materialization should be dead after recursive rewrite")
        };
        assert_eq!(*callee, clone.name);
    }

    #[test]
    fn incompatible_plan_uses_the_canonical_specialization_code() {
        let function = plain_function(
            "badPlan",
            &["bad_a"],
            &[("_DExpected", Type::Var(sym("bad_a")))],
            Type::Var(sym("bad_a")),
            false,
        );
        let wrong = Builder {
            function: builder("wrong", "_DWrong", None, Type::Int),
        };
        let failure = SpecializationPlan::build(&function, &[wrong]).unwrap_err();
        assert!(matches!(
            failure,
            TypedCoreSpecializationFailure::IncompatibleDictionary { .. }
        ));
        assert_eq!(Error::from(failure).code(), TYPED_CORE_SPECIALIZATION);
    }

    #[test]
    fn dce_keeps_legacy_value_thunk_boundary_opaque() {
        let builder = builder("opaqueBuilder", "_DOpaque", None, Type::Int);
        let builders = BTreeMap::from([(builder.name, Builder { function: builder })]);
        let dictionary = dict_ty("_DOpaque", Type::Int);
        let unit = source(Type::Unit);
        let inner = TypedComp::new(
            pure(unit.clone()),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    pure(dictionary.clone()),
                    TypedCompKind::Call {
                        callee: sym("opaqueBuilder"),
                        instantiation: Vec::new(),
                        args: Vec::new(),
                    },
                )),
                TypedBinder::new(sym("unused_dictionary"), dictionary),
                Box::new(TypedComp::new(
                    pure(unit.clone()),
                    TypedCompKind::Return(TypedValue::new(unit.clone(), TypedValueKind::Unit)),
                )),
            ),
        );
        let lambda_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(unit));
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(lambda_sig))),
            TypedCompKind::Lam(Vec::new(), Box::new(inner)),
        );
        let thunk_type = CoreType::Thunk(Box::new(lambda.sig.clone()));
        let outer = TypedComp::new(
            pure(thunk_type.clone()),
            TypedCompKind::Return(TypedValue::new(
                thunk_type,
                TypedValueKind::Thunk(Box::new(lambda)),
            )),
        );

        let actual = Dce {
            builders: &builders,
        }
        .comp(&outer, &());
        assert_eq!(actual, outer);
    }
}
