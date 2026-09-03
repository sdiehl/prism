//! Bounded inliner for typed Core (late pass).
//!
//! Two admission rules share one splicing mechanism. A top-level function
//! called exactly once (a single `Call` head, and never referenced
//! first-class) is inlined so its body moves rather than duplicates. A
//! multi-site function is inlined at every site only when its interprocedural
//! summary proves substitution exposes a cheaper result and duplication is
//! free: the result is a constant or a forwarded parameter, the body
//! allocates nothing, invokes no callbacks, builds no closures, performs no
//! effects, and stays under a small node budget. Either way the parameters
//! are let-bound to the evaluated arguments and every binder alpha-renamed to
//! a fresh `%i{n}` name from a per-compilation counter. Typed Core adds
//! scheme instantiation: a typed `Call` carries the callee's explicit
//! type/row instantiation, which must be substituted through the callee's body
//! *before* freshening and binding its parameters, so every witness in the
//! spliced term already reflects the call's monomorphic instance. `Inline` is
//! whole-program: it does not confine itself to one strongly connected
//! component.

use std::collections::{BTreeMap, BTreeSet};

use crate::types::ty::EffRow;
use prism_common::scc::tarjan_scc;
use prism_common::sym::Sym;
use prism_syntax::names::{self, ENTRY_POINT};

use super::specialize_support::{
    free_comp_vars, freshen_with, next_fresh, substitute_witnesses, Rewrite,
};
use super::summary::{summarize, AllocBound, CaptureState, FunctionSummary, ResultShape};
use super::traverse::Visit;
use super::verify::{representation_preserving_stable, substitute_core_type};
use super::{
    on_core_stack, CompSig, CoreInstantiation, TypedBinder, TypedComp, TypedCompKind, TypedCore,
    TypedCoreFn, TypedValue, TypedValueKind, UncheckedTypedCore,
};

// The node budget for summary-admitted multi-site bodies. Splicing duplicates
// the body once per call site, so only a body whose whole tree is smaller than
// the call machinery it replaces may be pasted everywhere; anything larger
// keeps the single-call-site rule as its only way in.
const INLINE_CHEAP_BODY_MAX: usize = 16;

/// Rewrite counts for typed inlining.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct InlineStats {
    ticks: u64,
}

impl InlineStats {
    /// Call sites inlined.
    pub const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Inline single-call-site non-recursive functions, preserving every witness.
#[must_use]
pub fn inline<P>(core: TypedCore<P>) -> (UncheckedTypedCore<P>, InlineStats) {
    on_core_stack(|| inline_on_core_stack(core))
}

fn inline_on_core_stack<P>(core: TypedCore<P>) -> (UncheckedTypedCore<P>, InlineStats) {
    let names: BTreeSet<Sym> = core
        .functions()
        .iter()
        .map(|function| function.name)
        .collect();

    // Per-function call-site count (Call heads) and whether it is ever used
    // first-class (as a value), across all bodies.
    let mut call_count: BTreeMap<Sym, usize> = BTreeMap::new();
    let mut first_class: BTreeSet<Sym> = BTreeSet::new();
    for function in core.functions() {
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
    let summaries = summarize(core.functions());
    let entry = Sym::new(ENTRY_POINT);
    let mut inlinable: BTreeSet<Sym> = BTreeSet::new();
    let mut multi_site: BTreeSet<Sym> = BTreeSet::new();
    for function in core.functions() {
        if function.name == entry
            || recursive.contains(&function.name)
            || first_class.contains(&function.name)
        {
            continue;
        }
        if call_count.get(&function.name).copied() == Some(1) {
            inlinable.insert(function.name);
        } else if cheap_at_every_site(function, &summaries) {
            inlinable.insert(function.name);
            multi_site.insert(function.name);
        }
    }
    if inlinable.is_empty() {
        return (core.into_unchecked(), InlineStats::default());
    }

    let source_functions = core.into_unchecked().into_functions();
    let mut inliner = Inliner {
        fns: source_functions
            .iter()
            .map(|function| (function.name, function.clone()))
            .collect(),
        inlinable,
        multi_site,
        ticks: 0,
        counter: 0,
    };
    let fns = source_functions
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
        UncheckedTypedCore::new(fns),
        InlineStats {
            ticks: inliner.ticks,
        },
    )
}

// Whether every call site profits from splicing this body even without a
// single-site guarantee. The summary is the oracle that substitution exposes a
// cheaper result: the tail is already resolved to a constant or a forwarded
// parameter, and the body it drags along is free to duplicate because it
// allocates nothing, invokes no callback, builds no closure, performs no
// effects, and fits the node budget. Every clause fails closed: a missing
// summary, an open or effectful row, or an unknown shape keeps the function
// on the single-call-site rule alone.
fn cheap_at_every_site(function: &TypedCoreFn, summaries: &BTreeMap<Sym, FunctionSummary>) -> bool {
    let Some(summary) = summaries.get(&function.name) else {
        return false;
    };
    matches!(
        summary.result,
        ResultShape::Constant | ResultShape::Param(_)
    ) && summary.allocation == AllocBound::Zero
        && summary.callbacks.is_empty()
        && summary.capture == CaptureState::NoClosures
        && summary.effects == EffRow::Empty
        && body_size(&function.body) <= INLINE_CHEAP_BODY_MAX
}

// Total computation-node count of a body, the budget `cheap_at_every_site`
// charges against. Thunked computations do not need visiting: the closure
// gate already rejects any body that builds one.
fn body_size(comp: &TypedComp) -> usize {
    #[derive(Default)]
    struct CompCounter(usize);

    impl Visit for CompCounter {
        fn comp(&mut self, _comp: &TypedComp) -> bool {
            self.0 += 1;
            true
        }

        fn value(&mut self, _value: &TypedValue) -> bool {
            false
        }
    }

    let mut counter = CompCounter::default();
    counter.walk_comp(comp);
    counter.0
}

// The functions that (transitively) call themselves. Never inlined: it would
// not terminate and would reshape the spines native codegen expects. A name is
// recursive when the call graph induced on `names` puts it in a multi-member
// strongly connected component or gives it a self-edge.
fn recursive_set<P>(core: &TypedCore<P>, names: &BTreeSet<Sym>) -> BTreeSet<Sym> {
    let order: Vec<Sym> = names.iter().copied().collect();
    let index: BTreeMap<Sym, usize> = order.iter().enumerate().map(|(i, &n)| (n, i)).collect();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); order.len()];
    for function in core.functions() {
        let Some(&v) = index.get(&function.name) else {
            continue;
        };
        let mut heads: Vec<usize> = calls_in(&function.body)
            .into_iter()
            .filter_map(|head| index.get(&head).copied())
            .collect();
        heads.sort_unstable();
        heads.dedup();
        adj[v] = heads;
    }
    tarjan_scc(&adj)
        .into_iter()
        .filter(|scc| scc.len() > 1 || adj[scc[0]].contains(&scc[0]))
        .flatten()
        .map(|v| order[v])
        .collect()
}

// Every direct `Call` head reachable anywhere in `comp`, including inside
// thunked values, in occurrence order. A bare function name flowing as a
// first-class value (not a call head) is not counted here.
pub(crate) fn calls_in(comp: &TypedComp) -> Vec<Sym> {
    let mut collector = CallCollector::default();
    collector.walk_comp(comp);
    collector.heads
}

#[derive(Default)]
struct CallCollector {
    heads: Vec<Sym>,
}

impl Visit for CallCollector {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        if let TypedCompKind::Call { callee, .. } = comp.kind() {
            self.heads.push(*callee);
        }
        true
    }
}

struct Inliner {
    fns: BTreeMap<Sym, TypedCoreFn>,
    inlinable: BTreeSet<Sym>,
    // Summary-admitted names with more than one call site. Their splice must
    // be row-neutral: the callee's row is empty, so it only replaces a call
    // node stamped with that same empty row. A site the lowering stamped
    // with a wider row keeps the call, because splicing a narrower tree
    // there would shift the computed rows out from under every enclosing
    // stored sig the verifier already checked.
    multi_site: BTreeSet<Sym>,
    ticks: u64,
    // Per-compilation freshening counter, threaded across every inlined site so
    // each freshened binder gets a distinct deterministic `%i{n}` name.
    counter: u32,
}

impl Rewrite for Inliner {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, cx: &()) -> TypedComp {
        // Spliced-chain inlining recurses per call site; grow stack segments
        // inside the recursion, same discipline as `descend_comp`.
        on_core_stack(|| {
            if let TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } = &comp.kind
            {
                if self.inlinable.contains(callee) {
                    let function = self.fns[callee].clone();
                    let row_neutral =
                        !self.multi_site.contains(callee) || comp.sig.effects() == &EffRow::Empty;
                    if function.params.len() == args.len() {
                        let args: Vec<TypedValue> =
                            args.iter().map(|arg| self.value(arg, cx)).collect();
                        if row_neutral && arguments_admissible(&function, instantiation, &args) {
                            if let Some(spliced) =
                                inline_call(&function, instantiation, &args, &mut self.counter)
                            {
                                self.ticks += 1;
                                // Recurse into the spliced body: a single-call-site
                                // callee it in turn calls is still single-site (its
                                // one site just moved here), so one sweep inlines
                                // the whole chain.
                                return self.comp(&spliced, cx);
                            }
                        }
                        return TypedComp::new(
                            comp.sig.clone(),
                            TypedCompKind::Call {
                                callee: *callee,
                                instantiation: instantiation.clone(),
                                args,
                            },
                        );
                    }
                }
            }
            self.descend_comp(comp, cx)
        })
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
/// Whether every argument can cross into its parameter binder. An argument
/// whose type differs from the declared (instantiated) binder type crosses
/// through a representation-preserving coercion; a pair that coercion cannot
/// bless would splice a cast the verifier rejects, so the call site is kept
/// as a call instead. The substitution-stable rule is required, not the
/// verifier's: a declared row whose tail is an enclosing function's row
/// quantifier is still substitutable, and chain inlining will substitute
/// through the minted cast, so a cast blessed only by the abstract-tail
/// absorb rule can become a concrete label vanishing into a smaller concrete
/// row, which the verifier rejects as effect laundering.
fn arguments_admissible(
    callee: &TypedCoreFn,
    instantiation: &[CoreInstantiation],
    args: &[TypedValue],
) -> bool {
    callee.params.iter().zip(args).all(|(param, arg)| {
        let declared = substitute_core_type(&param.ty, callee.sig.quantifiers(), instantiation);
        arg.ty == declared || representation_preserving_stable(&arg.ty, &declared)
    })
}

/// Every representation-preserving coercion in the tree still satisfies the
/// substitution-stable cast rule after witness substitution. Substitution can
/// break one: a cast that erased a row quantifier's abstract tail (`!{X | e}`
/// to `!{X}`) is legal until the call instantiates `e` to a row with more
/// labels, which widens the cast's source but not its already-closed target,
/// leaving a concrete label vanishing into a smaller concrete row. Such a
/// body must not be spliced. The recheck is the stable rule, not the
/// verifier's, because the spliced cast lands in a pre-fusion tree: with the
/// absorb rule, a widened source label could sink into a still-open target
/// tail, and stream fusion reads purity off a row's explicit heads, so the
/// splice would hide an effectful thunk behind the open tail. Declining the
/// inline instead is a pure cost decision.
fn casts_verify(c: &TypedComp) -> bool {
    struct StableCastCheck(bool);

    impl Visit for StableCastCheck {
        fn comp(&mut self, _comp: &TypedComp) -> bool {
            self.0
        }

        fn value(&mut self, value: &TypedValue) -> bool {
            if let TypedValueKind::Reinterpret(inner) = value.kind() {
                self.0 &= representation_preserving_stable(inner.ty(), value.ty());
            }
            self.0
        }
    }

    let mut check = StableCastCheck(true);
    check.walk_comp(c);
    check.0
}

fn inline_call(
    callee: &TypedCoreFn,
    instantiation: &[CoreInstantiation],
    args: &[TypedValue],
    counter: &mut u32,
) -> Option<TypedComp> {
    let body = substitute_witnesses(&callee.body, callee.sig.quantifiers(), instantiation);
    if !casts_verify(&body) {
        return None;
    }
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
    Some(out)
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, mem, thread};

    use crate::core::{CoreOp, EffectStrategy, OpGrades};
    use crate::flags::{DynFlags, EffectTier};
    use crate::types::ty::Label;
    use crate::types::Type;

    use super::super::effect_lower::lower_effects;
    use super::super::verify::{OperationSig, VerifyEnv};
    use super::super::{verify, CoreFnSig, CoreQuantifier, CoreType, EffectLowered, Elaborated};
    use super::*;

    const DEEP_INLINE_QUERY_NODE_COUNT: usize = 50_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

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

    #[test]
    fn inline_queries_handle_deep_terms_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-inline-queries".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut value = TypedValue::new(source(Type::Int), TypedValueKind::Int(0));
                for index in 0..DEEP_INLINE_QUERY_NODE_COUNT {
                    let ty = if index % 2 == 0 {
                        source(Type::Char)
                    } else {
                        source(Type::Int)
                    };
                    value = TypedValue::new(ty, TypedValueKind::Reinterpret(Box::new(value)));
                }
                let mut body = ret(value);
                for _ in 0..DEEP_INLINE_QUERY_NODE_COUNT {
                    let sig = body.sig().clone();
                    body = TypedComp::new(sig, TypedCompKind::Mask(Vec::new(), Box::new(body)));
                }

                assert_eq!(body_size(&body), DEEP_INLINE_QUERY_NODE_COUNT + 1);
                assert!(casts_verify(&body));
                mem::forget(body);
            })
            .expect("spawn deep inline-query test")
            .join()
            .expect("deep inline-query test panicked");
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

    fn run_inline(functions: Vec<TypedCoreFn>, env: &VerifyEnv) -> (TypedCore<Elaborated>, u64) {
        let input = verify(UncheckedTypedCore::<Elaborated>::new(functions), env)
            .unwrap_or_else(|violations| panic!("input fixture is invalid: {violations:#?}"));
        let (actual, stats) = inline(input);
        let actual = verify(actual, env)
            .unwrap_or_else(|violations| panic!("inlined typed Core is invalid: {violations:#?}"));
        (actual, stats.ticks())
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
                    CoreOp::Add,
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
        let input = verify(
            UncheckedTypedCore::<Elaborated>::new(vec![increment, main]),
            &env,
        )
        .unwrap_or_else(|violations| {
            panic!("elaborated late-pass fixture is invalid: {violations:#?}")
        });
        let flags = DynFlags {
            effect_tier: EffectTier::FreeMonad,
            quiet: true,
            ..DynFlags::default()
        };
        let lowering = lower_effects(input, &env, &BTreeMap::new(), &flags, &OpGrades::new())
            .expect("fixture lowers through the production effect ABI");
        assert_eq!(lowering.strategy(), EffectStrategy::SelectiveFreeMonad);
        assert!(lowering.constructors().contains_key("EPure"));
        assert!(lowering.constructors().contains_key("EOp"));
        let env = lowering.env().clone();
        let lowered = lowering.core().clone();
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
            &EffRow::Var(sym(prism_syntax::names::FREE_MONAD_ROW)),
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

    fn run_lowered_inline(
        input: TypedCore<EffectLowered>,
        env: &VerifyEnv,
    ) -> (TypedCore<EffectLowered>, u64) {
        let (actual, stats) = inline(input);
        let actual = verify(actual, env).unwrap_or_else(|violations| {
            panic!("effect-lowered Inline output is invalid: {violations:#?}")
        });
        (actual, stats.ticks())
    }

    #[test]
    fn effect_lowered_inline_removes_the_helper_call() {
        let (input, env) = lowered_inline_fixture();
        let (actual, ticks) = run_lowered_inline(input, &env);
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
        let (actual, ticks) = run_inline(vec![main, wrap, g_fn()], &env);
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
        let (_, ticks) = run_inline(vec![looping], &env);
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
        let (_, ticks) = run_inline(vec![main, wrap, g_fn()], &env);
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
        let (actual, ticks) = run_inline(vec![main, identity], &env);
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

    // A multi-site callee admitted by its summary: `two` returns a constant,
    // allocates nothing, builds no closures, and is tiny, so both call sites
    // splice it and no call to it remains anywhere.
    #[test]
    fn cheap_constant_function_inlines_at_every_site() {
        let env = VerifyEnv::new();
        let two = TypedCoreFn::new(
            sym("two"),
            Vec::new(),
            ret(TypedValue::new(source(Type::Int), TypedValueKind::Int(2))),
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
            0,
        );
        let call_two = || {
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("two"),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            )
        };
        let sum = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Prim(
                CoreOp::Add,
                var("a", source(Type::Int)),
                var("b", source(Type::Int)),
            ),
        );
        let main_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(call_two()),
                TypedBinder::new(sym("a"), source(Type::Int)),
                Box::new(TypedComp::new(
                    pure(source(Type::Int)),
                    TypedCompKind::Bind(
                        Box::new(call_two()),
                        TypedBinder::new(sym("b"), source(Type::Int)),
                        Box::new(sum),
                    ),
                )),
            ),
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
            0,
        );
        let (actual, ticks) = run_inline(vec![main, two], &env);
        assert_eq!(ticks, 2, "both sites of the cheap constant must splice");
        let main = actual
            .functions()
            .iter()
            .find(|function| function.name() == sym("main"))
            .unwrap();
        assert!(calls_in(main.body()).is_empty());
    }

    // A multi-site callee that allocates its result is never
    // summary-admitted: splicing would duplicate the allocation decision at
    // every site, so with two call sites it must stay a call.
    #[test]
    fn allocating_multi_site_function_stays_a_call() {
        let env = VerifyEnv::new();
        let pair_ty = source(Type::Tuple(vec![Type::Int, Type::Int]));
        let pair = TypedCoreFn::new(
            sym("pair"),
            vec![TypedBinder::new(sym("p"), source(Type::Int))],
            ret(TypedValue::new(
                pair_ty.clone(),
                TypedValueKind::Tuple(vec![
                    var("p", source(Type::Int)),
                    var("p", source(Type::Int)),
                ]),
            )),
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(pair_ty.clone())),
            0,
        );
        let call_pair = |n: i64| {
            TypedComp::new(
                pure(pair_ty.clone()),
                TypedCompKind::Call {
                    callee: sym("pair"),
                    instantiation: Vec::new(),
                    args: vec![TypedValue::new(source(Type::Int), TypedValueKind::Int(n))],
                },
            )
        };
        let main_body = TypedComp::new(
            pure(pair_ty.clone()),
            TypedCompKind::Bind(
                Box::new(call_pair(1)),
                TypedBinder::new(sym("first_pair"), pair_ty.clone()),
                Box::new(call_pair(2)),
            ),
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(pair_ty)),
            0,
        );
        let (_, ticks) = run_inline(vec![main, pair], &env);
        assert_eq!(ticks, 0, "an allocating body must not be pasted per site");
    }

    // The node budget is a hard clause: a multi-site body that forwards its
    // parameter and allocates nothing is still declined once its tree exceeds
    // the budget, so code growth stays bounded by construction.
    #[test]
    fn oversized_multi_site_function_stays_a_call() {
        let env = VerifyEnv::new();
        // A chain of rebinds of `x`: harmless, non-allocating, and past the
        // node budget by construction.
        let mut body = ret(var("x", source(Type::Int)));
        for step in 0..INLINE_CHEAP_BODY_MAX {
            body = TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Bind(
                    Box::new(ret(var("x", source(Type::Int)))),
                    TypedBinder::new(sym(&format!("step{step}")), source(Type::Int)),
                    Box::new(body),
                ),
            );
        }
        let big = TypedCoreFn::new(
            sym("big"),
            vec![TypedBinder::new(sym("x"), source(Type::Int))],
            body,
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], pure(source(Type::Int))),
            0,
        );
        let call_big = |n: i64| {
            TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("big"),
                    instantiation: Vec::new(),
                    args: vec![TypedValue::new(source(Type::Int), TypedValueKind::Int(n))],
                },
            )
        };
        let main_body = TypedComp::new(
            pure(source(Type::Int)),
            TypedCompKind::Bind(
                Box::new(call_big(1)),
                TypedBinder::new(sym("ignored"), source(Type::Int)),
                Box::new(call_big(2)),
            ),
        );
        let main = TypedCoreFn::new(
            sym("main"),
            Vec::new(),
            main_body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
            0,
        );
        let (_, ticks) = run_inline(vec![main, big], &env);
        assert_eq!(ticks, 0, "an oversized body must not be pasted per site");
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
        let (_, ticks) = run_inline(vec![main, outer, inner, g_fn()], &env);
        assert_eq!(ticks, 6);
    }
}
