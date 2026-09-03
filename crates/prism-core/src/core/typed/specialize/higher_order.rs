//! Higher-order callable recognition, lambda lifting, and clone rewriting.

use crate::core::typed::on_core_stack;
use crate::core::typed::traverse::Visit;

use super::{
    collect_ops, comp_rigid_vars, core_type_row_vars, free_comp_vars, free_value_vars, freshen,
    installs_handler, names, open_clone_variable, substitute_core_type, substitute_sig,
    substitute_terms, substitute_witnesses, BTreeMap, BTreeSet, CompSig, CoreFnSig,
    CoreInstantiation, CoreQuantifier, EffRow, Rewrite, SpecializeStats, Sym, TypedBinder,
    TypedComp, TypedCompKind, TypedCore, TypedCoreFn, TypedCoreSpecializationFailure, TypedValue,
    TypedValueKind, UncheckedTypedCore,
};

/// Higher-order specialization: clone a function on a constant callable argument
/// that never varies across the recursion, so the indirect force-and-apply
/// devirtualizes to a direct call.
///
/// A closed local lambda that flows to such an apply is first hoisted to a
/// fresh top-level definition and rebound as a closed eta-wrapper, giving it
/// the named identity the callable machinery keys on; the body moves once and
/// every collapse is then a direct call, never a copy.
///
/// Clone names are memoized before descending so recursive calls reuse the
/// in-progress clone.
///
/// # Errors
/// The first [`TypedCoreSpecializationFailure`] a clone records.
pub fn ho_specialize<P>(
    core: TypedCore<P>,
    report_declines: bool,
) -> Result<(UncheckedTypedCore<P>, SpecializeStats), TypedCoreSpecializationFailure> {
    on_core_stack(|| Ok(ho_specialize_on_core_stack(core, report_declines)))
}

fn ho_specialize_on_core_stack<P>(
    core: TypedCore<P>,
    report_declines: bool,
) -> (UncheckedTypedCore<P>, SpecializeStats) {
    let source_functions = core.into_unchecked().into_functions();
    let pre_lift = callable_parameters(&source_functions);
    let (source_functions, lifted) = lift_closed_lambdas(source_functions, &pre_lift);
    // Lifting adds definitions and may create new callable flows, so the map
    // is recomputed over the lifted program; without lifts the first stands.
    let callable = if lifted == 0 {
        pre_lift
    } else {
        callable_parameters(&source_functions)
    };
    if callable.is_empty() && lifted == 0 {
        return (
            UncheckedTypedCore::new(source_functions),
            SpecializeStats::default(),
        );
    }
    let bodies = source_functions
        .iter()
        .map(|function| (function.name, function.clone()))
        .collect();
    let installer_tainted = installer_tainted(&bodies);
    let mut pass = HoSpecializer {
        callable,
        bodies,
        installer_tainted,
        memo: BTreeMap::new(),
        clones_per_def: BTreeMap::new(),
        clones: Vec::new(),
        declines: Vec::new(),
        counter: 0,
        reductions: 0,
        fresh: 0,
    };
    let empty = BTreeMap::new();
    let mut functions: Vec<_> = source_functions
        .iter()
        .map(|function| pass.function(function, &empty))
        .collect();
    if report_declines {
        for decline in &pass.declines {
            eprintln!("ho-specialize decline: {decline}");
        }
    }
    let ticks = pass.counter as u64 + pass.reductions + lifted;
    functions.extend(pass.clones);
    (
        UncheckedTypedCore::new(functions),
        SpecializeStats { ticks },
    )
}

/// Maximum callable specializations per source definition.
const MAX_CALLABLES_PER_DEFINITION: usize = 16;

/// A closed constant callable flowing through a value parameter: an eta-wrapper
/// `\p. g(p)` whose wrapped callee `g` is its identity for memoization. The
/// stored `value` is spliced in whole when the force-and-apply is reduced.
#[derive(Clone)]
struct HoCallable {
    id: Sym,
    value: TypedValue,
}

#[derive(Clone)]
struct HoMemoEntry {
    clone: Sym,
    instantiation: Vec<CoreInstantiation>,
    // The clone's declared result and row, restamped onto every rewritten
    // call site: a direct call's stored sig must equal the callee's declared
    // one, and the tightened instantiation can narrow it below the site's.
    sig: CompSig,
}

// A memo key: the callee plus the identity of each fixed callable argument.
type HoMemoKey = (Sym, Vec<(usize, Sym)>);

struct HoSpecializer {
    callable: BTreeMap<Sym, BTreeSet<usize>>,
    bodies: BTreeMap<Sym, TypedCoreFn>,
    installer_tainted: BTreeSet<Sym>,
    // Monomorphized clones are reusable only at the same type/effect instance.
    memo: BTreeMap<HoMemoKey, Vec<HoMemoEntry>>,
    clones_per_def: BTreeMap<Sym, usize>,
    clones: Vec<TypedCoreFn>,
    declines: Vec<String>,
    counter: usize,
    reductions: u64,
    fresh: u32,
}

impl HoSpecializer {
    /// Narrow the call's row instantiation to what the fixed callables can
    /// actually perform. Inference solves an unannotated callback's row
    /// against the caller's ambient row, so the recorded argument is often
    /// wider than the callable being fixed (a pure callback carrying the
    /// caller's `{Fail}`). Cloning at the wide row stamps effects the clone
    /// can never perform into every stored signature, and the free-monad
    /// plan, which reads what bodies do rather than stored rows, then
    /// disagrees with the verifier over the clone's call sites. A row
    /// quantifier whose every parameter mention sits in a fixed-and-pure slot
    /// is instantiated at the empty row instead; anything less clear-cut
    /// keeps the recorded row.
    fn tightened_instantiation(
        &self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        fixed: &[(usize, HoCallable)],
    ) -> Vec<CoreInstantiation> {
        let mut out = instantiation.to_vec();
        let Some(original) = self.bodies.get(&callee) else {
            return out;
        };
        let params = original.sig.params();
        for (index, quantifier) in original.sig.quantifiers().iter().enumerate() {
            let CoreQuantifier::Row(name) = quantifier else {
                continue;
            };
            let Some(CoreInstantiation::Row(row)) = out.get(index) else {
                continue;
            };
            // An already-empty row has nothing to narrow; an open tail is the
            // caller's ambient variable, not a solved widening.
            if row.labels().is_empty() || !matches!(row.tail(), EffRow::Empty) {
                continue;
            }
            let mentions: Vec<usize> = params
                .iter()
                .enumerate()
                .filter(|(_, ty)| {
                    let mut vars = BTreeSet::new();
                    core_type_row_vars(ty, &mut vars);
                    vars.contains(name)
                })
                .map(|(slot, _)| slot)
                .collect();
            if mentions.is_empty() {
                continue;
            }
            // A result TYPE naming the quantifier (a returned thunk still
            // carrying the row) would change under the narrowing while the
            // caller's binder keeps the wide instantiation; only the result
            // row itself may move.
            let mut result_vars = BTreeSet::new();
            core_type_row_vars(original.sig.body().result(), &mut result_vars);
            if result_vars.contains(name) {
                continue;
            }
            let all_fixed_pure = mentions.iter().all(|slot| {
                fixed.iter().any(|(position, callable)| {
                    position == slot
                        && self.bodies.get(&callable.id).is_some_and(|body| {
                            body.sig.quantifiers().is_empty()
                                && *body.sig.body().effects() == EffRow::Empty
                        })
                })
            });
            if all_fixed_pure {
                out[index] = CoreInstantiation::Row(EffRow::Empty);
            }
        }
        out
    }

    /// Request (or reuse) a clone of `callee` with the given constant callables
    /// fixed at their positions, monomorphized at the call's instantiation.
    fn request(
        &mut self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        fixed: &[(usize, HoCallable)],
    ) -> Option<(Sym, CompSig)> {
        let instantiation = &self.tightened_instantiation(callee, instantiation, fixed)[..];
        let key = (
            callee,
            fixed.iter().map(|(index, c)| (*index, c.id)).collect(),
        );
        if let Some(entry) = self
            .memo
            .get(&key)
            .into_iter()
            .flatten()
            .find(|entry| entry.instantiation == instantiation)
        {
            return Some((entry.clone, entry.sig.clone()));
        }
        // Cloning a handler installer can inline the thunk that effect lowering
        // uses to place its frame, making lowering tiers observably disagree.
        // The structural taint includes callers that forward into an installer.
        if self.installer_tainted.contains(&callee) {
            self.declines.push(format!(
                "{callee}: handler installer, cloning would break effect lowering"
            ));
            return None;
        }
        // A top-level quantifier-free clone cannot capture a caller's rigid type
        // or effect-row variable.
        if let Some(open) = open_clone_variable(instantiation) {
            self.declines.push(format!(
                "{callee}: clone would capture free variable {open}"
            ));
            return None;
        }
        let count = self.clones_per_def.get(&callee).copied().unwrap_or(0);
        if count >= MAX_CALLABLES_PER_DEFINITION {
            self.declines
                .push(format!("{callee}: reached the per-definition callable cap"));
            return None;
        }
        let original = self.bodies.get(&callee)?.clone();
        let quantifiers = original.sig.quantifiers();
        self.counter += 1;
        let clone = Sym::from(&names::ho_specialized_clone(callee.as_str(), self.counter));
        self.clones_per_def.insert(callee, count + 1);
        // Record the clone name before descending so a self-recursive call on the
        // same callable resolves to the in-flight clone, exactly as compatibility
        // Core does for dictionary clones.
        let clone_sig = substitute_sig(original.sig.body(), quantifiers, instantiation);
        self.memo.entry(key).or_default().push(HoMemoEntry {
            clone,
            instantiation: instantiation.to_vec(),
            sig: clone_sig.clone(),
        });

        let params: Vec<_> = original
            .params
            .iter()
            .map(|binder| {
                TypedBinder::new(
                    binder.name,
                    substitute_core_type(&binder.ty, quantifiers, instantiation),
                )
            })
            .collect();
        let body = substitute_witnesses(&original.body, quantifiers, instantiation);
        let mut sorted = fixed.to_vec();
        sorted.sort_by_key(|(index, _)| *index);
        // Bind each fixed parameter to its constant callable, then descend so every
        // `force param`-and-apply inside the clone devirtualizes to a direct call.
        // The recursive self-calls drop the callable argument, so a fully
        // devirtualized parameter is left with no remaining use.
        let env: BTreeMap<Sym, HoCallable> = sorted
            .iter()
            .map(|(index, callable)| (params[*index].name, callable.clone()))
            .collect();
        let mut body = self.comp(&body, &env);
        // Materialize a fixed callable only when a live use survives devirtualization.
        // When every use was a force-and-apply the pass rewrote away, the parameter
        // is dead; emitting its binding would re-allocate the callable on each
        // recursive entry for nothing, so dropping it keeps the clone allocation-free
        // (the win the interpreter tier sees too, since it runs before the late DCE).
        for (index, callable) in sorted.iter().rev() {
            if !free_comp_vars(&body).contains(&params[*index].name) {
                continue;
            }
            body = TypedComp::new(
                body.sig.clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        // Materializing the fixed callable is a pure `Return`, so
                        // its row is empty regardless of the clone body's effects.
                        CompSig::new(params[*index].ty.clone(), EffRow::Empty),
                        TypedCompKind::Return(callable.value.clone()),
                    )),
                    params[*index].clone(),
                    Box::new(body),
                ),
            );
        }
        let fixed_indices: BTreeSet<_> = fixed.iter().map(|(index, _)| *index).collect();
        let signature = CoreFnSig::new(
            Vec::new(),
            original
                .sig
                .params()
                .iter()
                .enumerate()
                .filter(|(index, _)| !fixed_indices.contains(index))
                .map(|(_, ty)| substitute_core_type(ty, quantifiers, instantiation))
                .collect(),
            clone_sig.clone(),
        );
        let clone_params: Vec<_> = params
            .iter()
            .enumerate()
            .filter(|(index, _)| !fixed_indices.contains(index))
            .map(|(_, binder)| binder.clone())
            .collect();
        let clone_fn = TypedCoreFn::new(clone, clone_params, body, signature, 0);
        self.clones.push(clone_fn);
        Some((clone, clone_sig))
    }

    fn rewritten_call(
        &mut self,
        comp: &TypedComp,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        env: &BTreeMap<Sym, HoCallable>,
    ) -> TypedComp {
        if let Some(positions) = self.callable.get(&callee).cloned() {
            let fixed: Vec<_> = positions
                .iter()
                .filter_map(
                    |&index| match args.get(index).map(|arg| &peel_coercions(arg).kind) {
                        Some(TypedValueKind::Var { name, .. }) => {
                            env.get(name).map(|callable| (index, callable.clone()))
                        }
                        _ => None,
                    },
                )
                .collect();
            if !fixed.is_empty() {
                if let Some((clone, clone_sig)) = self.request(callee, instantiation, &fixed) {
                    let dropped: BTreeSet<_> = fixed.iter().map(|(index, _)| *index).collect();
                    return TypedComp::new(
                        clone_sig,
                        TypedCompKind::Call {
                            callee: clone,
                            instantiation: Vec::new(),
                            args: args
                                .iter()
                                .enumerate()
                                .filter(|(index, _)| !dropped.contains(index))
                                .map(|(_, argument)| self.value(argument, env))
                                .collect(),
                        },
                    );
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

    /// Reduce `(force v)(args)` to the callable's body with parameters bound to
    /// the arguments, when `v` is a constant callable in scope.
    fn try_devirtualize(
        &mut self,
        callee: &TypedComp,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
        env: &BTreeMap<Sym, HoCallable>,
    ) -> Option<TypedComp> {
        if !instantiation.is_empty() {
            return None;
        }
        let TypedCompKind::Force(forced) = &callee.kind else {
            return None;
        };
        let TypedValueKind::Var { name, .. } = &peel_coercions(forced).kind else {
            return None;
        };
        let callable = env.get(name)?.clone();
        let TypedValueKind::Thunk(lambda) = &peel_coercions(&callable.value).kind else {
            return None;
        };
        let TypedCompKind::Lam(params, inner) = &lambda.kind else {
            return None;
        };
        if params.len() != args.len() {
            return None;
        }
        let values: Vec<_> = args
            .iter()
            .map(|argument| self.value(argument, env))
            .collect();
        let substitution: BTreeMap<_, _> = params
            .iter()
            .map(|binder| binder.name)
            .zip(values)
            .collect();
        self.reductions += 1;
        let inner = freshen(inner, &mut self.fresh, names::FRESH_HO_SPECIALIZE);
        Some(substitute_terms(
            &inner,
            &substitution,
            &mut self.fresh,
            names::FRESH_HO_SPECIALIZE,
        ))
    }
}

impl Rewrite for HoSpecializer {
    type Ctx = BTreeMap<Sym, HoCallable>;

    fn comp(&mut self, comp: &TypedComp, env: &Self::Ctx) -> TypedComp {
        // Bind spines recurse per node ahead of the shared descent; grow
        // stack segments inside the recursion, same discipline as
        // `descend_comp`.
        on_core_stack(|| match &comp.kind {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, env);
                let mut next = env.clone();
                // A pure `Return` of a constant callable (a closed eta-thunk), or of a
                // variable already bound to one, aliases the binder to that callable so
                // its `force`-and-apply uses downstream devirtualize to direct calls.
                let bound_callable = match &first.kind {
                    TypedCompKind::Return(value) => {
                        closed_callable(value).or_else(|| match &peel_coercions(value).kind {
                            TypedValueKind::Var { name, .. } => env.get(name).cloned(),
                            _ => None,
                        })
                    }
                    _ => None,
                };
                match &bound_callable {
                    Some(callable) => {
                        next.insert(binder.name, callable.clone());
                    }
                    None => {
                        next.remove(&binder.name);
                    }
                }
                let rest = self.comp(rest, &next);
                // Once every use of a materialized callable devirtualized away, the
                // binding is a dead pure `Return`. Dropping it here, rather than
                // deferring to the late simplifier, keeps the clone allocation-free on
                // the free-monad tier too, where a surviving per-recursion
                // materialization would re-allocate the callable on each entry. A pure
                // `Return` rhs contributes an empty row, so the binder's result and the
                // rest's row already carry the whole `Bind`'s signature.
                if bound_callable.is_some() && !free_comp_vars(&rest).contains(&binder.name) {
                    return rest;
                }
                TypedComp::new(
                    comp.sig.clone(),
                    TypedCompKind::Bind(Box::new(first), binder.clone(), Box::new(rest)),
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => self.rewritten_call(comp, *callee, instantiation, args, env),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => self
                .try_devirtualize(callee, instantiation, args, env)
                .unwrap_or_else(|| self.descend_comp(comp, env)),
            _ => self.descend_comp(comp, env),
        })
    }
}

/// Peel erasable representation-preserving coercions to reach the value they
/// wrap. `Reinterpret` is a scalar coercion legacy Core erases, so a callable
/// behind one is still the same constant callable; the wrapper stays on the
/// stored value to keep the spliced clone well typed.
pub(crate) fn peel_coercions(value: &TypedValue) -> &TypedValue {
    let mut current = value;
    while let TypedValueKind::Reinterpret(inner) = &current.kind {
        current = inner;
    }
    current
}

/// The function a closed eta-wrapper `\p0 .. pn. g(p0, .., pn)` names, when
/// the value is one.
///
/// Non-eta or open callables have no simple identity and are left for a
/// later, more general pass. This identity is the bridge from a call-site
/// value to its function summary.
#[must_use]
pub fn callable_identity(value: &TypedValue) -> Option<Sym> {
    let TypedValueKind::Thunk(lambda) = &peel_coercions(value).kind else {
        return None;
    };
    let TypedCompKind::Lam(params, inner) = &lambda.kind else {
        return None;
    };
    let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = &inner.kind
    else {
        return None;
    };
    if !instantiation.is_empty() || args.len() != params.len() {
        return None;
    }
    for (argument, param) in args.iter().zip(params) {
        let TypedValueKind::Var {
            name,
            instantiation,
        } = &argument.kind
        else {
            return None;
        };
        if !instantiation.is_empty() || *name != param.name {
            return None;
        }
    }
    if !free_value_vars(value).is_empty() {
        return None;
    }
    Some(*callee)
}

/// Recognize a closed eta-wrapper, carrying the wrapper value along with the
/// identity so specialization can splice it into a clone.
fn closed_callable(value: &TypedValue) -> Option<HoCallable> {
    Some(HoCallable {
        id: callable_identity(value)?,
        value: value.clone(),
    })
}

/// Hoist each closed local lambda that flows to a collapsible application out
/// of its quantifier-free enclosing function, rebinding the local as a closed
/// eta-wrapper over the hoisted definition. The body moves exactly once, so
/// downstream devirtualization and callable specialization work with a named
/// direct call instead of duplicating the lambda.
fn lift_closed_lambdas(
    functions: Vec<TypedCoreFn>,
    callable: &BTreeMap<Sym, BTreeSet<usize>>,
) -> (Vec<TypedCoreFn>, u64) {
    let mut rewritten = Vec::with_capacity(functions.len());
    let mut hoisted = Vec::new();
    let mut ticks = 0u64;
    for function in functions {
        // A lifted definition is quantifier-free, so lifting only out of
        // quantifier-free functions makes capturing an enclosing rigid type or
        // effect-row variable impossible rather than merely checked.
        if !function.sig.quantifiers().is_empty() {
            rewritten.push(function);
            continue;
        }
        // Effect lowering classifies the thunks a handler-installing body
        // captures by walking their structure in place; replacing one with an
        // eta-wrapper over a top-level call hides that structure behind an
        // indirection the capture analysis cannot follow, demoting the whole
        // program's tier. Such functions keep every lambda where it is.
        if installs_handler(function.body()) {
            rewritten.push(function);
            continue;
        }
        let mut lifter = LambdaLifter {
            callable,
            enclosing: function.name,
            lifted: Vec::new(),
            counter: 0,
        };
        rewritten.push(lifter.function(&function, &()));
        ticks += lifter.lifted.len() as u64;
        hoisted.append(&mut lifter.lifted);
    }
    rewritten.extend(hoisted);
    (rewritten, ticks)
}

/// The rewrite hoisting liftable lambda bindings within one enclosing
/// function. Lift order is source order, so minted names are deterministic.
struct LambdaLifter<'a> {
    callable: &'a BTreeMap<Sym, BTreeSet<usize>>,
    enclosing: Sym,
    lifted: Vec<TypedCoreFn>,
    counter: usize,
}

impl LambdaLifter<'_> {
    /// Hoist `value` when it is a liftable lambda that `rest` applies through
    /// `binder`, returning the closed eta-wrapper that takes its place. Every
    /// guard fails closed: a declined lambda simply stays where it is.
    fn lift(
        &mut self,
        value: &TypedValue,
        binder: &TypedBinder,
        rest: &TypedComp,
    ) -> Option<TypedValue> {
        let peeled = peel_coercions(value);
        let TypedValueKind::Thunk(lambda) = &peeled.kind else {
            return None;
        };
        let TypedCompKind::Lam(params, inner) = &lambda.kind else {
            return None;
        };
        // An eta-wrapper already carries its callee as identity; re-lifting it
        // would only add a hop.
        if closed_callable(value).is_some() {
            return None;
        }
        // Only a closed lambda can move to the top level unchanged.
        if !free_value_vars(value).is_empty() {
            return None;
        }
        // Effect lowering places handler frames against the thunk structure it
        // sees, so a handler-installing body keeps its original home.
        if installs_handler(inner) {
            return None;
        }
        // Any operation the body performs (or handles or masks in a nested
        // thunk) is discharged against a handler or `var` frame enclosing this
        // binding lexically; hoisting the body to the top level would move the
        // op out of the region lowering rewrites, so it stays where it is.
        let mut ops = BTreeSet::new();
        collect_ops(inner, &mut ops);
        if !ops.is_empty() {
            return None;
        }
        // The op scan is syntactic: a body that performs nothing itself but
        // calls into an effectful function still carries a non-empty row.
        // Free-monad reification rewrites the rows of the thunks it can see;
        // a hoisted effectful body would sit outside that rewrite and hand
        // lowering a bind whose stored row no longer covers its callee's.
        if !matches!(inner.sig.effects(), EffRow::Empty) {
            return None;
        }
        // Term closure is not type closure: a case arm unpacking an
        // existential introduces a rigid brand type variable with no
        // enclosing quantifier, and the quantifier-free-function guard
        // upstream cannot see it. Hoisting a body whose types mention any
        // rigid variable would leave that variable unbound at the top level,
        // so the lift declines when the lambda mentions one anywhere.
        let mut rigid = BTreeSet::new();
        comp_rigid_vars(lambda, &mut rigid);
        if !rigid.is_empty() {
            return None;
        }
        // Lift only when the binder provably reaches a collapsible apply;
        // anywhere else the surviving wrapper would add indirection for
        // nothing.
        if !applied_in(binder.name, params.len(), rest, self.callable) {
            return None;
        }
        self.counter += 1;
        let name = Sym::from(&names::lifted_lambda(self.enclosing.as_str(), self.counter));
        let body = self.comp(inner, &());
        let signature = CoreFnSig::new(
            Vec::new(),
            params.iter().map(|param| param.ty.clone()).collect(),
            inner.sig.clone(),
        );
        self.lifted
            .push(TypedCoreFn::new(name, params.clone(), body, signature, 0));
        let call = TypedComp::new(
            inner.sig.clone(),
            TypedCompKind::Call {
                callee: name,
                instantiation: Vec::new(),
                args: params
                    .iter()
                    .map(|param| {
                        TypedValue::new(
                            param.ty.clone(),
                            TypedValueKind::Var {
                                name: param.name,
                                instantiation: Vec::new(),
                            },
                        )
                    })
                    .collect(),
            },
        );
        let wrapper = TypedComp::new(
            lambda.sig.clone(),
            TypedCompKind::Lam(params.clone(), Box::new(call)),
        );
        let thunk = TypedValue::new(peeled.ty.clone(), TypedValueKind::Thunk(Box::new(wrapper)));
        Some(rewrap_coercions(value, thunk))
    }
}

/// Rebuild `original`'s erasable coercion chain around `replacement`, so a
/// lifted lambda found behind a `Reinterpret` keeps the exact wrapper
/// structure the surrounding types expect.
fn rewrap_coercions(original: &TypedValue, replacement: TypedValue) -> TypedValue {
    match &original.kind {
        TypedValueKind::Reinterpret(inner) => TypedValue::new(
            original.ty.clone(),
            TypedValueKind::Reinterpret(Box::new(rewrap_coercions(inner, replacement))),
        ),
        _ => replacement,
    }
}

impl Rewrite for LambdaLifter<'_> {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        // Same growth discipline as the specializer's walk.
        on_core_stack(|| {
            if let TypedCompKind::Bind(first, binder, rest) = &comp.kind {
                if let TypedCompKind::Return(value) = &first.kind {
                    if let Some(wrapper) = self.lift(value, binder, rest) {
                        let first =
                            TypedComp::new(first.sig.clone(), TypedCompKind::Return(wrapper));
                        let rest = self.comp(rest, cx);
                        return TypedComp::new(
                            comp.sig.clone(),
                            TypedCompKind::Bind(Box::new(first), binder.clone(), Box::new(rest)),
                        );
                    }
                }
            }
            self.descend_comp(comp, cx)
        })
    }
}

/// Whether `name` flows to a site the specializer can collapse once the
/// lambda has an identity: a direct force-and-apply at its arity, or a
/// callable parameter of a named call. ANF rebinds a value on the way to its
/// use (`return f to t`), so the check follows transparent aliases first.
fn applied_in(
    name: Sym,
    arity: usize,
    rest: &TypedComp,
    callable: &BTreeMap<Sym, BTreeSet<usize>>,
) -> bool {
    let mut pairs = Vec::new();
    collect_alias_pairs(rest, &mut pairs);
    let mut group = BTreeSet::from([name]);
    loop {
        let mut changed = false;
        for (bound, source) in &pairs {
            if group.contains(source) && group.insert(*bound) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    group_applied_in(&group, arity, rest, callable)
}

fn group_applied_in(
    group: &BTreeSet<Sym>,
    arity: usize,
    comp: &TypedComp,
    callable: &BTreeMap<Sym, BTreeSet<usize>>,
) -> bool {
    let mut scan = AppliedScan {
        group,
        arity,
        callable,
        found: false,
    };
    scan.walk_comp(comp);
    scan.found
}

struct AppliedScan<'a> {
    group: &'a BTreeSet<Sym>,
    arity: usize,
    callable: &'a BTreeMap<Sym, BTreeSet<usize>>,
    found: bool,
}

impl Visit for AppliedScan<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        self.found |= match comp.kind() {
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } if instantiation.is_empty() && args.len() == self.arity => match callee.kind() {
                TypedCompKind::Force(forced) => matches!(
                    peel_coercions(forced).kind(),
                    TypedValueKind::Var { name: used, .. } if self.group.contains(used)
                ),
                _ => false,
            },
            TypedCompKind::Call { callee, args, .. } => {
                self.callable.get(callee).is_some_and(|positions| {
                    positions.iter().any(|&index| {
                        matches!(
                            args.get(index).map(|arg| peel_coercions(arg).kind()),
                            Some(TypedValueKind::Var { name: used, .. })
                                if self.group.contains(used)
                        )
                    })
                })
            }
            _ => false,
        };
        !self.found
    }
}

/// Which value parameters of each function reach a force-and-apply, directly or
/// by being forwarded into another function's callable parameter. Fixpoint,
/// because forwarding is transitive.
fn callable_parameters(functions: &[TypedCoreFn]) -> BTreeMap<Sym, BTreeSet<usize>> {
    let aliases: BTreeMap<_, _> = functions
        .iter()
        .map(|function| (function.name, alias_map(function)))
        .collect();
    let mut callable: BTreeMap<Sym, BTreeSet<usize>> = BTreeMap::new();
    loop {
        let mut changed = false;
        for function in functions {
            let mut positions = BTreeSet::new();
            collect_callable_positions(
                &function.body,
                &aliases[&function.name],
                &callable,
                &mut positions,
            );
            let entry = callable.entry(function.name).or_default();
            for index in positions {
                if entry.insert(index) {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    callable.retain(|_, positions| !positions.is_empty());
    callable
}

/// Map each local binder that transparently aliases a parameter (`return p to
/// b`) to that parameter's index.
fn alias_map(function: &TypedCoreFn) -> BTreeMap<Sym, usize> {
    let mut map: BTreeMap<Sym, usize> = function
        .params
        .iter()
        .enumerate()
        .map(|(index, binder)| (binder.name, index))
        .collect();
    let mut pairs = Vec::new();
    collect_alias_pairs(&function.body, &mut pairs);
    loop {
        let mut changed = false;
        for (bound, source) in &pairs {
            if let Some(&index) = map.get(source) {
                if map.insert(*bound, index).is_none() {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    map
}

fn collect_alias_pairs(comp: &TypedComp, pairs: &mut Vec<(Sym, Sym)>) {
    AliasCollector(pairs).walk_comp(comp);
}

struct AliasCollector<'a>(&'a mut Vec<(Sym, Sym)>);

impl Visit for AliasCollector<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        if let TypedCompKind::Bind(first, binder, _) = comp.kind() {
            if let TypedCompKind::Return(value) = first.kind() {
                if let TypedValueKind::Var { name, .. } = peel_coercions(value).kind() {
                    self.0.push((binder.name(), *name));
                }
            }
        }
        true
    }
}

fn collect_callable_positions(
    comp: &TypedComp,
    aliases: &BTreeMap<Sym, usize>,
    callable: &BTreeMap<Sym, BTreeSet<usize>>,
    positions: &mut BTreeSet<usize>,
) {
    CallablePositionCollector {
        aliases,
        callable,
        positions,
    }
    .walk_comp(comp);
}

struct CallablePositionCollector<'a> {
    aliases: &'a BTreeMap<Sym, usize>,
    callable: &'a BTreeMap<Sym, BTreeSet<usize>>,
    positions: &'a mut BTreeSet<usize>,
}

impl Visit for CallablePositionCollector<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        match comp.kind() {
            TypedCompKind::App { callee, .. } => {
                if let TypedCompKind::Force(forced) = callee.kind() {
                    if let TypedValueKind::Var { name, .. } = peel_coercions(forced).kind() {
                        if let Some(&index) = self.aliases.get(name) {
                            self.positions.insert(index);
                        }
                    }
                }
            }
            TypedCompKind::Call { callee, args, .. } => {
                if let Some(forwarded) = self.callable.get(callee) {
                    for &position in forwarded {
                        if let Some(TypedValueKind::Var { name, .. }) =
                            args.get(position).map(|arg| peel_coercions(arg).kind())
                        {
                            if let Some(&index) = self.aliases.get(name) {
                                self.positions.insert(index);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        true
    }
}

/// Every function a computation calls by name, the edges of the call graph the
/// installer taint propagates along.
pub(super) fn direct_callees(comp: &TypedComp, out: &mut BTreeSet<Sym>) {
    DirectCalleeCollector(out).walk_comp(comp);
}

struct DirectCalleeCollector<'a>(&'a mut BTreeSet<Sym>);

impl Visit for DirectCalleeCollector<'_> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        if let TypedCompKind::Call { callee, .. } = comp.kind() {
            self.0.insert(*callee);
        }
        true
    }
}

/// Functions that install a handler directly or call another tainted function.
/// Declining this structural call cone keeps handler thunks available to effect
/// lowering without hard-coding handler names.
fn installer_tainted(bodies: &BTreeMap<Sym, TypedCoreFn>) -> BTreeSet<Sym> {
    let mut tainted: BTreeSet<Sym> = bodies
        .iter()
        .filter(|(_, function)| installs_handler(function.body()))
        .map(|(name, _)| *name)
        .collect();
    let callees: BTreeMap<Sym, BTreeSet<Sym>> = bodies
        .iter()
        .map(|(name, function)| {
            let mut set = BTreeSet::new();
            direct_callees(function.body(), &mut set);
            (*name, set)
        })
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (name, set) in &callees {
            if !tainted.contains(name) && set.iter().any(|callee| tainted.contains(callee)) {
                tainted.insert(*name);
                changed = true;
            }
        }
    }
    tainted
}
