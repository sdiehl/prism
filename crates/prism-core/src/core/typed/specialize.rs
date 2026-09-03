//! Witness-preserving dictionary specialization.
//!
//! The term rewrite deliberately mirrors the compatibility pass. The additional
//! work here is scheme-level: every clone records which source quantifiers a
//! concrete dictionary fixes and which source or builder quantifiers must remain
//! abstract. Consequently the legacy memo key remains sufficient even when a
//! polymorphic nullary builder is used at several concrete types.

use std::collections::{BTreeMap, BTreeSet};

use crate::types::ty::{EffRow, Label};
use crate::types::Type;
use prism_common::sym::Sym;
use prism_syntax::error::TypedCoreSpecializationFailure;
use prism_syntax::names::{self, DICT_PREFIX};

use super::effect_lower::arena::installs_handler;
use super::effect_lower::walk::{collect_ops, each_subcomp, each_value};
use super::specialize_support::{
    free_comp_vars, free_value_vars, freshen, substitute_terms, substitute_witnesses, Rewrite,
};
use super::verify::{substitute_core_type, substitute_sig};
use super::{
    instantiate_fn, on_core_stack, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType,
    LoweredType, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedHandleOp,
    TypedHandler, TypedPattern, TypedValue, TypedValueKind, UncheckedTypedCore,
};

/// Rewrite counts for typed dictionary specialization.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SpecializeStats {
    ticks: u64,
}

impl SpecializeStats {
    /// Clones generated plus dictionary projections reduced.
    #[must_use]
    pub const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Specialize constrained calls while retaining independently checkable
/// type/effect witnesses.
///
/// # Errors
/// The first [`TypedCoreSpecializationFailure`] a rewrite records: a dictionary
/// arity or shape that contradicts the callee's Core signature, or a clone
/// whose erasure would change the compatibility tree.
pub fn specialize<P>(
    core: TypedCore<P>,
) -> Result<(UncheckedTypedCore<P>, SpecializeStats), TypedCoreSpecializationFailure> {
    on_core_stack(|| specialize_on_core_stack(core))
}

fn specialize_on_core_stack<P>(
    core: TypedCore<P>,
) -> Result<(UncheckedTypedCore<P>, SpecializeStats), TypedCoreSpecializationFailure> {
    let builders = builders(&core);
    let constrained = constrained(&core);
    if builders.is_empty() || constrained.is_empty() {
        return Ok((core.into_unchecked(), SpecializeStats::default()));
    }
    let source_functions = core.into_unchecked().into_functions();
    let bodies = source_functions
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
    let mut functions: Vec<_> = source_functions
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
    Ok((
        UncheckedTypedCore::new(functions),
        SpecializeStats { ticks },
    ))
}

mod higher_order;

#[cfg(test)]
use higher_order::direct_callees;
pub(crate) use higher_order::peel_coercions;
pub use higher_order::{callable_identity, ho_specialize};
#[derive(Clone)]
struct Builder {
    function: TypedCoreFn,
}

fn builders<P>(core: &TypedCore<P>) -> BTreeMap<Sym, Builder> {
    core.functions()
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
    core.functions()
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
        // Bind spines recurse per node ahead of the shared descent; grow
        // stack segments inside the recursion, same discipline as
        // `descend_comp`.
        on_core_stack(|| match &comp.kind {
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
        })
    }
}

struct Dce<'a> {
    builders: &'a BTreeMap<Sym, Builder>,
}

impl Rewrite for Dce<'_> {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, _context: &Self::Ctx) -> TypedComp {
        // Same growth discipline as the specializer's walk.
        on_core_stack(|| {
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
        })
    }
}

mod planning;
mod unify;

use planning::{comp_rigid_vars, core_type_row_vars, open_clone_variable, SpecializationPlan};
#[cfg(test)]
mod tests;
