//! Bounded inliner for typed Core (late pass).
//!
//! Mirrors [`super::super::opt::inline::inline_counted`] rule-for-rule: inlines
//! a top-level function called exactly once (a single `Call` head, and never
//! referenced first-class) so its body moves rather than duplicates, with its
//! parameters let-bound to the evaluated arguments and every binder alpha-
//! renamed to a fresh `%i{n}` name from a per-compilation counter. The
//! typed-specific step is scheme instantiation: a typed `Call` carries the
//! callee's explicit type/row instantiation, which must be substituted through
//! the callee's body *before* freshening and binding its parameters, so every
//! witness in the spliced term already reflects the call's monomorphic
//! instance. `Inline` is whole-program, exactly like the legacy pass: it does
//! not confine itself to one strongly connected component.

use std::collections::{BTreeMap, BTreeSet};

use crate::names::{self, ENTRY_POINT};
use crate::sym::Sym;
use crate::types::ty::EffRow;

use super::specialize_support::{
    free_comp_vars, freshen_with, next_fresh, substitute_witnesses, Rewrite,
};
use super::verify::substitute_core_type;
use super::{
    CompSig, CoreInstantiation, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn,
    TypedValue, TypedValueKind,
};

/// Rewrite counts for typed inlining.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct InlineStats {
    ticks: u64,
}

impl InlineStats {
    /// Call sites inlined.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Inline single-call-site non-recursive functions, preserving every witness.
pub(crate) fn inline<P>(core: TypedCore<P>) -> (TypedCore<P>, InlineStats) {
    let names: BTreeSet<Sym> = core.fns.iter().map(|function| function.name).collect();

    // Per-function call-site count (Call heads) and whether it is ever used
    // first-class (as a value), across all bodies.
    let mut call_count: BTreeMap<Sym, usize> = BTreeMap::new();
    let mut first_class: BTreeSet<Sym> = BTreeSet::new();
    for function in &core.fns {
        for head in calls_in(&function.body) {
            *call_count.entry(head).or_default() += 1;
        }
        for v in free_comp_vars(&function.body) {
            if names.contains(&v) {
                first_class.insert(v);
            }
        }
    }

    let recursive = recursive_set(&core, &names);
    let entry = Sym::new(ENTRY_POINT);
    let inlinable: BTreeSet<Sym> = names
        .iter()
        .copied()
        .filter(|name| {
            *name != entry
                && !recursive.contains(name)
                && !first_class.contains(name)
                && call_count.get(name).copied() == Some(1)
        })
        .collect();
    if inlinable.is_empty() {
        return (core, InlineStats::default());
    }

    let mut inliner = Inliner {
        fns: core
            .fns
            .iter()
            .map(|function| (function.name, function.clone()))
            .collect(),
        inlinable,
        ticks: 0,
        counter: 0,
    };
    let fns = core
        .fns
        .iter()
        .map(|function| {
            TypedCoreFn::new(
                function.name,
                function.params.clone(),
                inliner.comp(&function.body, &()),
                function.sig.clone(),
                function.dict_arity,
            )
        })
        .collect();
    (
        TypedCore::new(fns),
        InlineStats {
            ticks: inliner.ticks,
        },
    )
}

// The functions that (transitively) call themselves. Never inlined: it would
// not terminate and would reshape the spines native codegen expects.
fn recursive_set<P>(core: &TypedCore<P>, names: &BTreeSet<Sym>) -> BTreeSet<Sym> {
    let mut edges: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
    for function in &core.fns {
        let heads = calls_in(&function.body);
        edges.insert(
            function.name,
            heads
                .into_iter()
                .filter(|head| names.contains(head))
                .collect(),
        );
    }
    let mut recursive = BTreeSet::new();
    for &start in names {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<Sym> = edges.get(&start).into_iter().flatten().copied().collect();
        while let Some(next) = stack.pop() {
            if next == start {
                recursive.insert(start);
                break;
            }
            if seen.insert(next) {
                stack.extend(edges.get(&next).into_iter().flatten().copied());
            }
        }
    }
    recursive
}

// Every direct `Call` head reachable anywhere in `comp`, including inside
// thunked values, in occurrence order. A bare function name flowing as a
// first-class value (not a call head) is not counted here.
pub(super) fn calls_in(comp: &TypedComp) -> Vec<Sym> {
    let mut heads = Vec::new();
    collect_calls_comp(comp, &mut heads);
    heads
}

fn collect_calls_comp(comp: &TypedComp, heads: &mut Vec<Sym>) {
    match &comp.kind {
        TypedCompKind::Call { callee, args, .. } => {
            heads.push(*callee);
            for arg in args {
                collect_calls_value(arg, heads);
            }
        }
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::Reuse(_, value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => collect_calls_value(value, heads),
        TypedCompKind::Prim(_, lhs, rhs)
        | TypedCompKind::RefSet(lhs, rhs)
        | TypedCompKind::InitAt(lhs, rhs) => {
            collect_calls_value(lhs, heads);
            collect_calls_value(rhs, heads);
        }
        TypedCompKind::Bind(first, _, rest) => {
            collect_calls_comp(first, heads);
            collect_calls_comp(rest, heads);
        }
        TypedCompKind::Lam(_, body) | TypedCompKind::Mask(_, body) => {
            collect_calls_comp(body, heads);
        }
        TypedCompKind::App { callee, args, .. } => {
            collect_calls_comp(callee, heads);
            for arg in args {
                collect_calls_value(arg, heads);
            }
        }
        TypedCompKind::If(condition, yes, no) => {
            collect_calls_value(condition, heads);
            collect_calls_comp(yes, heads);
            collect_calls_comp(no, heads);
        }
        TypedCompKind::Io(_, args)
        | TypedCompKind::Do { args, .. }
        | TypedCompKind::StrBuiltin { args, .. } => {
            for arg in args {
                collect_calls_value(arg, heads);
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            collect_calls_value(scrutinee, heads);
            for (_, body) in arms {
                collect_calls_comp(body, heads);
            }
        }
        TypedCompKind::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            collect_calls_comp(body, heads);
            if let Some(return_body) = return_body {
                collect_calls_comp(return_body, heads);
            }
            for arm in &ops.arms {
                collect_calls_comp(&arm.body, heads);
            }
        }
        TypedCompKind::WithReuse { freed, body, .. } => {
            collect_calls_value(freed, heads);
            collect_calls_comp(body, heads);
        }
    }
}

fn collect_calls_value(value: &TypedValue, heads: &mut Vec<Sym>) {
    match &value.kind {
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            collect_calls_value(inner, heads);
        }
        TypedValueKind::Thunk(body) => collect_calls_comp(body, heads),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                collect_calls_value(field, heads);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                collect_calls_value(field, heads);
            }
        }
        TypedValueKind::Var { .. }
        | TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => {}
    }
}

struct Inliner {
    fns: BTreeMap<Sym, TypedCoreFn>,
    inlinable: BTreeSet<Sym>,
    ticks: u64,
    // Per-compilation freshening counter, threaded across every inlined site so
    // each freshened binder gets a distinct deterministic `%i{n}` name.
    counter: u32,
}

impl Rewrite for Inliner {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, cx: &()) -> TypedComp {
        if let TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } = &comp.kind
        {
            if self.inlinable.contains(callee) {
                let function = self.fns[callee].clone();
                if function.params.len() == args.len() {
                    let args: Vec<TypedValue> =
                        args.iter().map(|arg| self.value(arg, cx)).collect();
                    self.ticks += 1;
                    let spliced = inline_call(&function, instantiation, &args, &mut self.counter);
                    // Recurse into the spliced body: a single-call-site callee
                    // it in turn calls is still single-site (its one site just
                    // moved here), so one sweep inlines the whole chain.
                    return self.comp(&spliced, cx);
                }
            }
        }
        self.descend_comp(comp, cx)
    }
}

// The callee body with its scheme quantifiers instantiated at the call site,
// every binder freshened, and its parameters bound to the argument values:
// `let p0' = a0 in ... let pk' = ak in <instantiated, freshened body>`. The
// fresh binder takes the callee's DECLARED (instantiated) parameter type, not
// the argument's own witness type: the call rule admits an argument at a
// narrower effect row than the declaration, but every occurrence in the body
// was checked against the declared type exactly, so a subsumed argument
// crosses into the binder through the same representation-preserving
// coercion the verifier accepts (rows are representation-irrelevant).
// `counter` is the caller's per-compilation freshening counter, threaded so
// every binder across every site gets a distinct deterministic name.
fn inline_call(
    callee: &TypedCoreFn,
    instantiation: &[CoreInstantiation],
    args: &[TypedValue],
    counter: &mut u32,
) -> TypedComp {
    let body = substitute_witnesses(&callee.body, callee.sig.quantifiers(), instantiation);
    let mut renames: BTreeMap<Sym, Sym> = BTreeMap::new();
    for param in &callee.params {
        renames.insert(param.name, next_fresh(counter, names::FRESH_INLINE));
    }
    let mut out = freshen_with(&body, &renames, counter, names::FRESH_INLINE);
    for index in (0..callee.params.len()).rev() {
        let fresh = renames[&callee.params[index].name];
        let declared = substitute_core_type(
            &callee.params[index].ty,
            callee.sig.quantifiers(),
            instantiation,
        );
        let mut argument = args[index].clone();
        if argument.ty != declared {
            argument = TypedValue::new(declared, TypedValueKind::Reinterpret(Box::new(argument)));
        }
        let binder = TypedBinder::new(fresh, argument.ty.clone());
        out = TypedComp::new(
            out.sig.clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(argument.ty.clone(), EffRow::Empty),
                    TypedCompKind::Return(argument),
                )),
                binder,
                Box::new(out),
            ),
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::core::opt::{run_spec_stage, CorePass, PassStage};
    use crate::core::{EffectStrategy, OpGrades};
    use crate::flags::{DynFlags, EffectTier};
    use crate::types::ty::Label;
    use crate::types::Type;

    use super::super::effect_lower::lower_effects;
    use super::super::verify::{verify, OperationSig, VerifyEnv};
    use super::super::{
        CoreFnSig, CoreQuantifier, CoreType, EffectLowered, Elaborated, TypedLowering,
    };
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

    fn var(name: &str, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name: sym(name),
                instantiation: Vec::new(),
            },
        )
    }

    fn ret(value: TypedValue) -> TypedComp {
        TypedComp::new(pure(value.ty.clone()), TypedCompKind::Return(value))
    }

    // `g(z) = z`, an Int -> Int leaf callee referenced by several fixtures below.
    fn g_fn() -> TypedCoreFn {
        TypedCoreFn::new(
            sym("g"),
            vec![TypedBinder::new(sym("z"), source(Type::Int))],
            ret(var("z", source(Type::Int))),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
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
        let (expected, legacy_ticks) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &[CorePass::Inline],
            PassStage::Late,
            &[],
            &DynFlags::default(),
        );
        let expected_ticks = legacy_ticks.total();
        let (actual, stats) = inline(input);
        if let Err(violations) = verify(&actual, env) {
            panic!("inlined typed Core is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        assert_eq!(stats.ticks(), expected_ticks);
        (actual, expected_ticks)
    }

    fn lowered_inline_fixture() -> (TypedCore<EffectLowered>, VerifyEnv) {
        let operation = sym("ask");
        let effect = sym("Ask");
        let mut env = VerifyEnv::new();
        env.insert_operation(
            operation,
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                source(Type::Int),
                Label::bare(effect),
            ),
        );

        let increment = TypedCoreFn::new(
            sym("increment"),
            vec![TypedBinder::new(sym("n"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Prim(
                    crate::core::CoreOp::Add,
                    var("n", source(Type::Int)),
                    TypedValue::new(source(Type::Int), TypedValueKind::Int(1)),
                ),
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        let effects = EffRow::singleton(effect);
        let performed_answer = TypedBinder::new(sym("performed_answer"), source(Type::Int));
        let answer = TypedBinder::new(sym("answer"), source(Type::Int));
        let performed = TypedComp::new(
            CompSig::new(source(Type::Int), effects.clone()),
            TypedCompKind::Do {
                operation,
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let increment_call = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Call {
                callee: sym("increment"),
                instantiation: Vec::new(),
                args: vec![var("answer", source(Type::Int))],
            },
        );
        // Match the front end's ANF alias between an effect result and its
        // source-level `let` binder. Besides being the production shape, the
        // two resulting `ebind` sites keep the ABI helper out of this
        // single-target Inline fixture.
        let continuation = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(ret(var("performed_answer", source(Type::Int)))),
                answer,
                Box::new(increment_call),
            ),
        );
        let main_body = TypedComp::new(
            CompSig::new(source(Type::Int), effects.clone()),
            TypedCompKind::Bind(
                Box::new(performed),
                performed_answer,
                Box::new(continuation),
            ),
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(source(Type::Int), effects),
            ),
            0,
        );
        let input = TypedCore::<Elaborated>::new(vec![increment, main]);
        if let Err(violations) = verify(&input, &env) {
            panic!("elaborated late-pass fixture is invalid: {violations:#?}");
        }
        let flags = DynFlags {
            effect_tier: EffectTier::FreeMonad,
            quiet: true,
            ..DynFlags::default()
        };
        let TypedLowering {
            core: lowered,
            env,
            ctors,
            warning: _,
            strategy,
        } = lower_effects(input, &env, &BTreeMap::new(), &flags, &OpGrades::new())
            .expect("fixture lowers through the production effect ABI");
        assert_eq!(strategy, EffectStrategy::SelectiveFreeMonad);
        assert!(ctors.contains_key("EPure"));
        assert!(ctors.contains_key("EOp"));
        if let Err(violations) = verify(&lowered, &env) {
            panic!("effect-lowered late-pass fixture is invalid: {violations:#?}");
        }
        let lowered_main = lowered
            .functions()
            .iter()
            .find(|function| function.name() == sym("main"))
            .expect("main survives effect lowering");
        let TypedCompKind::Bind(monadic_body, _, _) = lowered_main.body().kind() else {
            panic!("the selective entry must unwrap its lowered effect value")
        };
        let TypedCompKind::Bind(_, _, ebind_call) = monadic_body.kind() else {
            panic!("the source bind must lower through ebind")
        };
        let TypedCompKind::Call { callee, args, .. } = ebind_call.kind() else {
            panic!("the lowered source bind must call ebind")
        };
        assert_eq!(callee, &sym("ebind"));
        let [_, continuation] = args.as_slice() else {
            panic!("ebind must receive its effect value and continuation")
        };
        let TypedValueKind::Thunk(lambda) = &continuation.kind else {
            panic!("ebind's continuation must be a thunk")
        };
        let TypedCompKind::Lam(_, continuation_body) = lambda.kind() else {
            panic!("ebind's continuation thunk must contain a lambda")
        };
        assert_eq!(
            continuation_body.sig().effects(),
            &EffRow::Var(sym(crate::names::FREE_MONAD_ROW)),
            "the Inline target must sit under the production open-row continuation"
        );
        assert_eq!(
            calls_in(continuation_body)
                .into_iter()
                .filter(|callee| *callee == sym("increment"))
                .count(),
            1,
            "the one Inline target must be nested in the lowered continuation"
        );
        (lowered, env)
    }

    fn assert_lowered_differential(
        input: TypedCore<EffectLowered>,
        env: &VerifyEnv,
    ) -> (TypedCore<EffectLowered>, u64) {
        if let Err(violations) = verify(&input, env) {
            panic!("effect-lowered Inline input is invalid: {violations:#?}");
        }
        let legacy_input = input.clone().erase();
        let (expected, legacy_ticks) = run_spec_stage(
            &legacy_input,
            &BTreeSet::new(),
            &[CorePass::Inline],
            PassStage::Late,
            &[],
            &DynFlags::default(),
        );
        let (actual, stats) = inline(input);
        if let Err(violations) = verify(&actual, env) {
            panic!("effect-lowered Inline output is invalid: {violations:#?}");
        }
        assert_eq!(actual.clone().erase(), expected);
        assert_eq!(stats.ticks(), legacy_ticks.total());
        (actual, stats.ticks())
    }

    #[test]
    fn effect_lowered_inline_matches_the_legacy_pass() {
        let (input, env) = lowered_inline_fixture();
        let (actual, ticks) = assert_lowered_differential(input, &env);
        assert_eq!(ticks, 1, "the lowered helper call must be inlined");
        assert!(actual
            .functions()
            .iter()
            .flat_map(|function| calls_in(function.body()))
            .all(|callee| callee != sym("increment")));
    }

    // A wrapper called exactly once is inlined and its parameter let-bound to
    // the argument; the wrapper call is gone, replaced by the (freshened)
    // forwarded call.
    #[test]
    fn single_call_site_wrapper_is_inlined() {
        let env = VerifyEnv::new();
        let main = TypedCoreFn::new(
            sym("main"),
            vec![TypedBinder::new(sym("x"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("wrap"),
                    instantiation: Vec::new(),
                    args: vec![var("x", source(Type::Int))],
                },
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        let wrap = TypedCoreFn::new(
            sym("wrap"),
            vec![TypedBinder::new(sym("a"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("g"),
                    instantiation: Vec::new(),
                    args: vec![var("a", source(Type::Int))],
                },
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        // Both `wrap` (called once from `main`) and `g` (called once from
        // `wrap`) are single-call-site and get spliced: two ticks chain-inline
        // `main`'s call, and a third re-inlines `g` into `wrap`'s own
        // (now-orphaned but still rewritten) body.
        let (actual, ticks) = assert_differential(vec![main, wrap, g_fn()], &env);
        assert_eq!(ticks, 3);
        let main = actual
            .functions()
            .iter()
            .find(|function| function.name() == sym("main"))
            .unwrap();
        match main.body().kind() {
            TypedCompKind::Bind(rhs, _, body) => {
                assert!(matches!(
                    &rhs.kind,
                    TypedCompKind::Return(TypedValue {
                        kind: TypedValueKind::Var { name, .. },
                        ..
                    }) if *name == sym("x")
                ));
                assert!(matches!(&body.kind, TypedCompKind::Bind(..)));
            }
            other => panic!("expected inlined `let a = x in ...`, got {other:?}"),
        }
        assert!(calls_in(main.body()).is_empty());
    }

    // A recursive function is never inlined, even at a lone call site.
    #[test]
    fn recursive_function_is_not_inlined() {
        let env = VerifyEnv::new();
        let looping = TypedCoreFn::new(
            sym("loop"),
            Vec::new(),
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("loop"),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
            0,
        );
        let (_, ticks) = assert_differential(vec![looping], &env);
        assert_eq!(ticks, 0);
    }

    // A function referenced first-class (as a value, not only called) is
    // never inlined, even when it also has exactly one call site.
    #[test]
    fn first_class_reference_prevents_inlining() {
        let env = VerifyEnv::new();
        let fn_ty = CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![source(Type::Int)],
            pure(source(Type::Int)),
        )));
        let main = TypedCoreFn::new(
            sym("main"),
            vec![TypedBinder::new(sym("x"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        pure(fn_ty.clone()),
                        TypedCompKind::Return(TypedValue::new(
                            fn_ty.clone(),
                            TypedValueKind::Var {
                                name: sym("wrap"),
                                instantiation: Vec::new(),
                            },
                        )),
                    )),
                    TypedBinder::new(sym("_captured"), fn_ty),
                    Box::new(TypedComp::new(
                        pure(source(Type::Int)),
                        TypedCompKind::Call {
                            callee: sym("wrap"),
                            instantiation: Vec::new(),
                            args: vec![var("x", source(Type::Int))],
                        },
                    )),
                ),
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        let wrap = TypedCoreFn::new(
            sym("wrap"),
            vec![TypedBinder::new(sym("a"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("g"),
                    instantiation: Vec::new(),
                    args: vec![var("a", source(Type::Int))],
                },
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        // `wrap` is used first-class (captured into `_captured`), so its own
        // call from `main` is never inlined; `g`, called once from `wrap` and
        // never captured, is still inlined into `wrap`'s body regardless.
        let (_, ticks) = assert_differential(vec![main, wrap, g_fn()], &env);
        assert_eq!(ticks, 1);
    }

    // A type-polymorphic single-call-site callee has its scheme quantifier
    // instantiated with the call's explicit type argument before splicing, so
    // the spliced body carries the monomorphic instance, not the generic one.
    #[test]
    fn polymorphic_call_instantiates_before_splicing() {
        let env = VerifyEnv::new();
        let quantified = sym("a");
        let identity = TypedCoreFn::new(
            sym("identity"),
            vec![TypedBinder::new(
                sym("v"),
                CoreType::Source(Type::Var(quantified)),
            )],
            ret(var("v", CoreType::Source(Type::Var(quantified)))),
            CoreFnSig::new(
                vec![CoreQuantifier::Type(quantified)],
                vec![CoreType::Source(Type::Var(quantified))],
                pure(CoreType::Source(Type::Var(quantified))),
            ),
            0,
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("identity"),
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    args: vec![TypedValue::new(source(Type::Int), TypedValueKind::Int(9))],
                },
            ),
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
            0,
        );
        let (actual, ticks) = assert_differential(vec![main, identity], &env);
        assert_eq!(ticks, 1);
        let main = actual
            .functions()
            .iter()
            .find(|function| function.name() == sym("main"))
            .unwrap();
        match main.body().kind() {
            TypedCompKind::Bind(rhs, binder, body) => {
                assert_eq!(binder.ty, source(Type::Int));
                assert!(matches!(
                    &rhs.kind,
                    TypedCompKind::Return(TypedValue {
                        kind: TypedValueKind::Int(9),
                        ..
                    })
                ));
                assert!(matches!(
                    &body.kind,
                    TypedCompKind::Return(TypedValue {
                        kind: TypedValueKind::Var { .. },
                        ..
                    })
                ));
            }
            other => panic!("expected inlined identity body, got {other:?}"),
        }
    }

    // A chain of two single-call-site wrappers inlines fully in one sweep: the
    // spliced body is recursively re-processed, so `main -> wrap -> g` collapses
    // straight to `g` with both layers of parameters bound.
    #[test]
    fn chained_single_call_sites_fully_inline_in_one_sweep() {
        let env = VerifyEnv::new();
        let main = TypedCoreFn::new(
            sym("main"),
            vec![TypedBinder::new(sym("x"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("outer"),
                    instantiation: Vec::new(),
                    args: vec![var("x", source(Type::Int))],
                },
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        let outer = TypedCoreFn::new(
            sym("outer"),
            vec![TypedBinder::new(sym("b"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("inner"),
                    instantiation: Vec::new(),
                    args: vec![var("b", source(Type::Int))],
                },
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        let inner = TypedCoreFn::new(
            sym("inner"),
            vec![TypedBinder::new(sym("c"), source(Type::Int))],
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("g"),
                    instantiation: Vec::new(),
                    args: vec![var("c", source(Type::Int))],
                },
            ),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        // Three single-call-site functions (`outer`, `inner`, `g`) each get
        // spliced both at their live call site and, redundantly, while
        // rewriting their own now-orphaned top-level body: 3 (main's fully
        // chained call) + 2 (outer's own body re-inlining inner then g) + 1
        // (inner's own body re-inlining g) = 6.
        let (_, ticks) = assert_differential(vec![main, outer, inner, g_fn()], &env);
        assert_eq!(ticks, 6);
    }
}
