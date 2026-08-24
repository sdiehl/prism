//! Context splitting for thunk-valued parameters.
//!
//! A named higher-order function has one symbol, so the ordinary flow analysis
//! joins every thunk passed to one parameter slot.  If one call passes a direct
//! thunk and another passes an effectful thunk, that join gives both calls one
//! runtime convention and can widen an otherwise pure hot path to the whole
//! free-monad program.  This pass gives statically known demand instances
//! distinct symbols before the canonical effect plan is solved.
//!
//! Clones keep the source scheme and every witness byte-for-byte.  Only direct
//! call heads change, so this pass never invents a representation coercion or
//! specializes a type/effect quantifier.  Unknown values and dynamic calls stay
//! on the original symbol and therefore retain the conservative fallback.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names::{self, ENTRY_POINT};

use super::super::specialize_support::Rewrite;
use super::super::verify::VerifyEnv;
use super::super::{
    verify, ArenaPrepared, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn,
    TypedHandleOp, TypedHandler, TypedPattern, TypedValue, TypedValueKind, UncheckedTypedCore,
};
use super::flow::{self, Sig, ThunkFlow};
use super::latent::Latent;
use prism_syntax::error::TypedCoreEffectLoweringFailure;

// These are compile-resource rails, not semantic limits.  Crossing either one
// leaves the already verified input untouched and lets the ordinary conservative
// lowering choose its wider tier.
const MAX_INSTANCES: usize = 256;
const MAX_INSTANCES_PER_FUNCTION: usize = 16;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Demand {
    Known(Sig),
    Unknown,
}

impl Demand {
    const fn pure() -> Self {
        Self::Known(Sig::new())
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Known(left), Self::Known(right)) => {
                let mut joined = left.clone();
                joined.extend(right.iter().copied());
                Self::Known(joined)
            }
            _ => Self::Unknown,
        }
    }
}

type Loc = BTreeMap<Sym, Demand>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Instance {
    function: Sym,
    key: Vec<Sig>,
}

struct Facts<'a> {
    functions: BTreeMap<Sym, &'a TypedCoreFn>,
    latent: &'a Latent,
    joined: &'a ThunkFlow,
}

impl<'a> Facts<'a> {
    fn new(functions: &'a [TypedCoreFn], latent: &'a Latent, joined: &'a ThunkFlow) -> Self {
        Self {
            functions: functions
                .iter()
                .map(|function| (function.name(), function))
                .collect(),
            latent,
            joined,
        }
    }

    fn joined_loc(&self, function: &TypedCoreFn) -> Loc {
        function
            .params()
            .iter()
            .enumerate()
            .map(|(index, binder)| {
                let demand = if thunk_slot(binder.ty()) {
                    self.joined
                        .param
                        .get(&function.name())
                        .and_then(|slots| slots.get(index))
                        .cloned()
                        .map_or(Demand::Unknown, Demand::Known)
                } else {
                    Demand::pure()
                };
                (binder.name(), demand)
            })
            .collect()
    }

    fn instance_loc(function: &TypedCoreFn, key: &[Sig]) -> Loc {
        function
            .params()
            .iter()
            .enumerate()
            .map(|(index, binder)| {
                let demand = if thunk_slot(binder.ty()) {
                    key.get(index)
                        .cloned()
                        .map_or(Demand::Unknown, Demand::Known)
                } else {
                    Demand::pure()
                };
                (binder.name(), demand)
            })
            .collect()
    }

    fn value_demand(&self, value: &TypedValue, loc: &Loc) -> Demand {
        match super::peel(value).kind() {
            TypedValueKind::Thunk(body) => Demand::Known(flow::body_sig(body, self.latent)),
            TypedValueKind::Var { name, .. } => loc.get(name).cloned().unwrap_or(Demand::Unknown),
            _ => Demand::Unknown,
        }
    }

    fn call_instance(&self, callee: Sym, args: &[TypedValue], loc: &Loc) -> Option<Instance> {
        // The control erasure recognizes bare `repeat_while`/`forever` spines
        // and consumes them into monomorphic drivers before any tier is
        // chosen. A clone would hide the spine behind a fresh symbol and keep
        // the loop's control ops alive into strategy selection, so the loop
        // drivers always stay on their original names.
        if super::erase_control::is_loop_driver(callee) {
            return None;
        }
        let declaration = self.functions.get(&callee)?;
        let joined = self.joined.param.get(&callee)?;
        if args.len() != declaration.sig().params().len() || joined.len() != args.len() {
            return None;
        }
        let mut key = Vec::with_capacity(args.len());
        for ((argument, parameter), joined_slot) in
            args.iter().zip(declaration.sig().params()).zip(joined)
        {
            let signature = if thunk_slot(parameter) {
                let Demand::Known(signature) = self.value_demand(argument, loc) else {
                    return None;
                };
                signature
            } else {
                Sig::new()
            };
            // The context-sensitive demand must be a refinement of the global
            // least-fixpoint join.  If it is not, retain the original symbol;
            // manufacturing a clone from contradictory analyses would be an
            // unsound narrowing.
            if !signature.is_subset(joined_slot) {
                return None;
            }
            key.push(signature);
        }
        (key != *joined).then_some(Instance {
            function: callee,
            key,
        })
    }

    fn call_result(
        &self,
        callee: Sym,
        args: &[TypedValue],
        loc: &Loc,
        returns: &BTreeMap<Instance, Demand>,
        requested: &mut BTreeSet<Instance>,
    ) -> Demand {
        if let Some(instance) = self.call_instance(callee, args, loc) {
            requested.insert(instance.clone());
            return returns.get(&instance).cloned().unwrap_or_else(Demand::pure);
        }
        self.joined
            .ret
            .get(&callee)
            .cloned()
            .map_or(Demand::Unknown, Demand::Known)
    }

    fn result_demand(
        &self,
        comp: &TypedComp,
        loc: &Loc,
        returns: &BTreeMap<Instance, Demand>,
        requested: &mut BTreeSet<Instance>,
    ) -> Demand {
        match comp.kind() {
            TypedCompKind::Return(value) => {
                self.scan_value(value, loc, returns, requested);
                self.value_demand(value, loc)
            }
            TypedCompKind::Call { callee, args, .. } => {
                for argument in args {
                    self.scan_value(argument, loc, returns, requested);
                }
                self.call_result(*callee, args, loc, returns, requested)
            }
            TypedCompKind::Bind(first, binder, rest) => {
                let first_result = self.result_demand(first, loc, returns, requested);
                let mut next = loc.clone();
                next.insert(
                    binder.name(),
                    if thunk_slot(binder.ty()) {
                        first_result
                    } else {
                        Demand::pure()
                    },
                );
                self.result_demand(rest, &next, returns, requested)
            }
            TypedCompKind::If(condition, yes, no) => {
                self.scan_value(condition, loc, returns, requested);
                let yes = self.result_demand(yes, loc, returns, requested);
                let no = self.result_demand(no, loc, returns, requested);
                yes.join(&no)
            }
            TypedCompKind::Case(scrutinee, arms) => {
                self.scan_value(scrutinee, loc, returns, requested);
                let mut demand = Demand::pure();
                for (pattern, body) in arms {
                    let mut next = loc.clone();
                    forget_pattern(pattern, &mut next);
                    demand = demand.join(&self.result_demand(body, &next, returns, requested));
                }
                demand
            }
            TypedCompKind::Lam(params, body) => {
                let mut next = loc.clone();
                forget_binders(params, &mut next);
                self.result_demand(body, &next, returns, requested);
                demand_for_result(comp.sig().result())
            }
            TypedCompKind::App { callee, args, .. } => {
                self.result_demand(callee, loc, returns, requested);
                for argument in args {
                    self.scan_value(argument, loc, returns, requested);
                }
                demand_for_result(comp.sig().result())
            }
            TypedCompKind::Mask(_, body) | TypedCompKind::WithReuse { body, .. } => {
                self.result_demand(body, loc, returns, requested)
            }
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                self.result_demand(body, loc, returns, requested);
                if let Some(return_body) = return_body {
                    let mut next = loc.clone();
                    if let Some(binder) = return_binder {
                        forget_binder(binder, &mut next);
                    }
                    self.result_demand(return_body, &next, returns, requested);
                }
                for arm in ops.arms() {
                    let mut next = loc.clone();
                    forget_binders(arm.params(), &mut next);
                    forget_binder(arm.resume(), &mut next);
                    self.result_demand(arm.body(), &next, returns, requested);
                }
                demand_for_result(comp.sig().result())
            }
            _ => {
                super::walk::each_value(comp, &mut |value| {
                    self.scan_value(value, loc, returns, requested);
                });
                demand_for_result(comp.sig().result())
            }
        }
    }

    fn scan_value(
        &self,
        value: &TypedValue,
        loc: &Loc,
        returns: &BTreeMap<Instance, Demand>,
        requested: &mut BTreeSet<Instance>,
    ) {
        match super::peel(value).kind() {
            TypedValueKind::Thunk(body) => {
                if let TypedCompKind::Lam(params, inner) = body.kind() {
                    let mut next = loc.clone();
                    forget_binders(params, &mut next);
                    self.result_demand(inner, &next, returns, requested);
                } else {
                    self.result_demand(body, loc, returns, requested);
                }
            }
            TypedValueKind::Ctor { fields, .. }
            | TypedValueKind::Tuple(fields)
            | TypedValueKind::UnboxedTuple(fields) => {
                for field in fields {
                    self.scan_value(field, loc, returns, requested);
                }
            }
            TypedValueKind::UnboxedRecord(fields) => {
                for (_, field) in fields {
                    self.scan_value(field, loc, returns, requested);
                }
            }
            _ => {}
        }
    }
}

const fn thunk_slot(ty: &CoreType) -> bool {
    matches!(ty, CoreType::Thunk(_))
}

const fn demand_for_result(ty: &CoreType) -> Demand {
    if thunk_slot(ty) {
        Demand::Unknown
    } else {
        Demand::pure()
    }
}

fn forget_binder(binder: &TypedBinder, loc: &mut Loc) {
    loc.insert(
        binder.name(),
        if thunk_slot(binder.ty()) {
            Demand::Unknown
        } else {
            Demand::pure()
        },
    );
}

fn forget_binders(binders: &[TypedBinder], loc: &mut Loc) {
    for binder in binders {
        forget_binder(binder, loc);
    }
}

fn forget_pattern(pattern: &TypedPattern, loc: &mut Loc) {
    match pattern {
        TypedPattern::Wild => {}
        TypedPattern::Var(binder) => forget_binder(binder, loc),
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            for binder in fields.iter().flatten() {
                forget_binder(binder, loc);
            }
        }
    }
}

fn within_budget(instances: &BTreeSet<Instance>) -> bool {
    if instances.len() > MAX_INSTANCES {
        return false;
    }
    let mut per_function = BTreeMap::<Sym, usize>::new();
    for instance in instances {
        let count = per_function.entry(instance.function).or_default();
        *count += 1;
        if *count > MAX_INSTANCES_PER_FUNCTION {
            return false;
        }
    }
    true
}

// Discover every statically known demand instance and its returned-thunk
// signature before interning a clone name or changing a call head.  Return
// `None` on a resource cap: the caller then returns its verified input intact.
fn discover(facts: &Facts<'_>, functions: &[TypedCoreFn]) -> Option<BTreeMap<Instance, Demand>> {
    let mut returns = BTreeMap::<Instance, Demand>::new();
    loop {
        let mut requested = BTreeSet::new();
        for function in functions {
            let loc = facts.joined_loc(function);
            facts.result_demand(function.body(), &loc, &returns, &mut requested);
        }

        let known: Vec<Instance> = returns.keys().cloned().collect();
        let mut updates = Vec::with_capacity(known.len());
        for instance in known {
            let function = facts.functions.get(&instance.function)?;
            let loc = Facts::instance_loc(function, &instance.key);
            let result = facts.result_demand(function.body(), &loc, &returns, &mut requested);
            updates.push((instance, result));
        }

        // `requested` is rebuilt by the current traversal. Include already
        // admitted keys as well so a future traversal-policy refinement cannot
        // accidentally make the transactional budget forget an earlier SCC.
        let all_instances: BTreeSet<_> = requested
            .iter()
            .cloned()
            .chain(returns.keys().cloned())
            .collect();
        if !within_budget(&all_instances) {
            return None;
        }
        let mut changed = false;
        for instance in requested {
            if let std::collections::btree_map::Entry::Vacant(slot) = returns.entry(instance) {
                slot.insert(Demand::pure());
                changed = true;
            }
        }
        for (instance, result) in updates {
            let slot = returns.get_mut(&instance)?;
            let joined = slot.join(&result);
            if *slot != joined {
                *slot = joined;
                changed = true;
            }
        }
        if !changed {
            return Some(returns);
        }
    }
}

fn assign_names(
    instances: &BTreeMap<Instance, Demand>,
    functions: &[TypedCoreFn],
) -> BTreeMap<Instance, Sym> {
    let mut ordered: Vec<_> = instances.keys().cloned().collect();
    ordered.sort_by(|left, right| {
        left.function
            .as_str()
            .cmp(right.function.as_str())
            .then_with(|| left.key.cmp(&right.key))
    });
    let mut occupied: BTreeSet<String> = functions
        .iter()
        .map(|function| function.name().as_str().to_owned())
        .collect();
    let mut next = 0usize;
    let mut spellings = Vec::with_capacity(ordered.len());
    for instance in &ordered {
        loop {
            next += 1;
            let candidate = names::convention_clone(instance.function.as_str(), next);
            if occupied.insert(candidate.clone()) {
                spellings.push(candidate);
                break;
            }
        }
    }
    // Intern only after discovery and cap checks have completed, so a declined
    // attempt cannot perturb the compilation-global symbol table.
    ordered
        .into_iter()
        .zip(spellings)
        .map(|(instance, spelling)| (instance, Sym::from(&spelling)))
        .collect()
}

struct Rewriter<'a> {
    facts: Facts<'a>,
    returns: &'a BTreeMap<Instance, Demand>,
    names: &'a BTreeMap<Instance, Sym>,
}

impl Rewriter<'_> {
    fn target(&self, callee: Sym, args: &[TypedValue], loc: &Loc) -> Sym {
        self.facts
            .call_instance(callee, args, loc)
            .and_then(|instance| self.names.get(&instance).copied())
            .unwrap_or(callee)
    }

    fn result(&self, comp: &TypedComp, loc: &Loc) -> Demand {
        let mut ignored = BTreeSet::new();
        self.facts
            .result_demand(comp, loc, self.returns, &mut ignored)
    }

    fn rewritten_function(&mut self, source: &TypedCoreFn, name: Sym, loc: &Loc) -> TypedCoreFn {
        TypedCoreFn::new(
            name,
            source.params().to_vec(),
            self.comp(source.body(), loc),
            source.sig().clone(),
            source.dict_arity(),
        )
    }
}

impl Rewrite for Rewriter<'_> {
    type Ctx = Loc;

    fn comp(&mut self, comp: &TypedComp, loc: &Loc) -> TypedComp {
        match comp.kind() {
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Call {
                    callee: self.target(*callee, args, loc),
                    instantiation: instantiation.clone(),
                    args: args
                        .iter()
                        .map(|argument| self.value(argument, loc))
                        .collect(),
                },
            ),
            TypedCompKind::Bind(first, binder, rest) => {
                let first_result = self.result(first, loc);
                let first = self.comp(first, loc);
                let mut next = loc.clone();
                next.insert(
                    binder.name(),
                    if thunk_slot(binder.ty()) {
                        first_result
                    } else {
                        Demand::pure()
                    },
                );
                TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(first),
                        binder.clone(),
                        Box::new(self.comp(rest, &next)),
                    ),
                )
            }
            TypedCompKind::Lam(params, body) => {
                let mut next = loc.clone();
                forget_binders(params, &mut next);
                TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Lam(params.clone(), Box::new(self.comp(body, &next))),
                )
            }
            TypedCompKind::Case(scrutinee, arms) => {
                let scrutinee = self.value(scrutinee, loc);
                let arms = arms
                    .iter()
                    .map(|(pattern, body)| {
                        let mut next = loc.clone();
                        forget_pattern(pattern, &mut next);
                        (pattern.clone(), self.comp(body, &next))
                    })
                    .collect();
                TypedComp::new(comp.sig().clone(), TypedCompKind::Case(scrutinee, arms))
            }
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => {
                let body = Box::new(self.comp(body, loc));
                let return_body = return_body.as_ref().map(|body| {
                    let mut next = loc.clone();
                    if let Some(binder) = return_binder {
                        forget_binder(binder, &mut next);
                    }
                    Box::new(self.comp(body, &next))
                });
                let arms = ops
                    .arms()
                    .iter()
                    .map(|arm| {
                        let mut next = loc.clone();
                        forget_binders(arm.params(), &mut next);
                        forget_binder(arm.resume(), &mut next);
                        TypedHandleOp::new(
                            arm.name(),
                            arm.instantiation().to_vec(),
                            arm.params().to_vec(),
                            arm.resume().clone(),
                            self.comp(arm.body(), &next),
                        )
                    })
                    .collect();
                let handler = TypedHandler::new(arms)
                    .expect("verified handler operation names remain unique")
                    .with_forwarded(ops.forwarded().to_vec());
                TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Handle {
                        body,
                        return_binder: return_binder.clone(),
                        return_body,
                        ops: handler,
                    },
                )
            }
            _ => self.descend_comp(comp, loc),
        }
    }
}

/// Split statically known thunk-demand instances and return a freshly verified
/// `ArenaPrepared` program.  A resource-cap decline returns `core` unchanged.
pub(super) fn split(
    core: TypedCore<ArenaPrepared>,
    env: &VerifyEnv,
) -> Result<TypedCore<ArenaPrepared>, TypedCoreEffectLoweringFailure> {
    let functions = core.functions();
    let latent = super::latent::latent_map(functions);
    let joined = flow::analyze(functions, &latent);
    let facts = Facts::new(functions, &latent, &joined);
    let Some(instances) = discover(&facts, functions) else {
        return Ok(core);
    };
    if instances.is_empty() {
        return Ok(core);
    }
    let names = assign_names(&instances, functions);
    let mut rewriter = Rewriter {
        facts,
        returns: &instances,
        names: &names,
    };
    let mut output: Vec<TypedCoreFn> = functions
        .iter()
        .map(|function| {
            let loc = rewriter.facts.joined_loc(function);
            rewriter.rewritten_function(function, function.name(), &loc)
        })
        .collect();
    let ordered_instances: Vec<_> = names.keys().cloned().collect();
    for instance in ordered_instances {
        let source = rewriter.facts.functions[&instance.function];
        let loc = Facts::instance_loc(source, &instance.key);
        output.push(rewriter.rewritten_function(source, names[&instance], &loc));
    }

    if output
        .iter()
        .any(|function| function.name().as_str() == ENTRY_POINT)
    {
        let live = super::reachable(&output);
        output.retain(|function| live.contains(&function.name()));
    }
    verify(UncheckedTypedCore::<ArenaPrepared>::new(output), env).map_err(|violations| {
        TypedCoreEffectLoweringFailure::Verification {
            first: violations
                .first()
                .map_or_else(String::new, ToString::to_string),
            count: violations.len(),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::typed::effect_lower::fixtures;
    use crate::core::typed::effect_lower::latent::MaskOp;

    fn joined_flow(functions: &[TypedCoreFn]) -> ThunkFlow {
        let mut effectful = Sig::new();
        effectful.insert(MaskOp {
            id: Sym::from(fixtures::ASK_OP),
            depth: 0,
        });
        ThunkFlow {
            ret: functions
                .iter()
                .map(|function| (function.name(), Sig::new()))
                .collect(),
            param: functions
                .iter()
                .map(|function| {
                    let slots = if function.name().as_str() == fixtures::RUN {
                        vec![effectful.clone()]
                    } else {
                        vec![Sig::new(); function.params().len()]
                    };
                    (function.name(), slots)
                })
                .collect(),
        }
    }

    #[test]
    fn narrower_direct_thunk_demand_requests_a_clone() {
        let functions = fixtures::capturing_program();
        let latent = Latent::new();
        let joined = joined_flow(&functions);
        let facts = Facts::new(&functions, &latent, &joined);
        let quiet_name = Sym::from("quiet");
        let quiet = fixtures::var(quiet_name, fixtures::action_ty());
        let loc = Loc::from([(quiet_name, Demand::pure())]);

        let instance = facts
            .call_instance(Sym::from(fixtures::RUN), &[quiet], &loc)
            .expect("a direct pure thunk refines the globally effectful slot");
        assert!(instance.key[0].is_empty());
    }

    #[test]
    fn same_key_and_unknown_values_stay_on_the_original() {
        let functions = fixtures::capturing_program();
        let latent = Latent::new();
        let joined = joined_flow(&functions);
        let facts = Facts::new(&functions, &latent, &joined);
        let effectful_name = Sym::from("effectful");
        let effectful = fixtures::var(effectful_name, fixtures::action_ty());
        let effectful_loc = Loc::from([(
            effectful_name,
            Demand::Known(joined.param[&Sym::from(fixtures::RUN)][0].clone()),
        )]);
        assert_eq!(
            facts.call_instance(Sym::from(fixtures::RUN), &[effectful], &effectful_loc),
            None,
            "the joined convention needs no clone"
        );

        let unknown = fixtures::var(Sym::from("dynamic"), fixtures::action_ty());
        assert_eq!(
            facts.call_instance(Sym::from(fixtures::RUN), &[unknown], &Loc::new()),
            None,
            "an untracked first-class thunk must retain the conservative fallback"
        );
    }
}
