use crate::core::CoreOp;
use crate::types::Type;

use super::super::verify::{ConstructorSig, VerifyEnv};
use super::super::{verify, Elaborated};
use super::*;

const DEEP_PURITY_CALL_GRAPH_DEPTH: usize = 10_000;
const DEEP_TYPED_TRAVERSAL_DEPTH: usize = 10_000;

fn sym(name: &str) -> Sym {
    Sym::new(name)
}

fn source(ty: Type) -> CoreType {
    CoreType::Source(ty)
}

fn int() -> CoreType {
    source(Type::Int)
}

fn pure_sig(result: CoreType) -> CompSig {
    CompSig::new(result, EffRow::Empty)
}

fn step_ty() -> CoreType {
    source(Type::Con(sym("Step"), vec![Type::Int]))
}

// A pull sequence: a thunk of a one-argument step closure `(Unit) -> Step`.
fn seq_ty() -> CoreType {
    CoreType::Thunk(Box::new(pure_sig(CoreType::Function(Box::new(
        CoreFnSig::new(Vec::new(), vec![source(Type::Unit)], pure_sig(step_ty())),
    )))))
}

fn mapper_ty() -> CoreType {
    CoreType::Thunk(Box::new(pure_sig(CoreType::Function(Box::new(
        CoreFnSig::new(Vec::new(), vec![int()], pure_sig(int())),
    )))))
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

fn lit(n: i64) -> TypedValue {
    TypedValue::new(int(), TypedValueKind::Int(n))
}

fn unit() -> TypedValue {
    TypedValue::new(source(Type::Unit), TypedValueKind::Unit)
}

fn ret(v: TypedValue) -> TypedComp {
    TypedComp::new(pure_sig(v.ty().clone()), TypedCompKind::Return(v))
}

// All fixture rows are `Empty`, so the verified `Bind` sig collapses to the
// continuation's sig.
fn bind(first: TypedComp, name: &str, ty: CoreType, rest: TypedComp) -> TypedComp {
    TypedComp::new(
        rest.sig().clone(),
        TypedCompKind::Bind(
            Box::new(first),
            TypedBinder::new(sym(name), ty),
            Box::new(rest),
        ),
    )
}

fn prim(op: CoreOp, result: CoreType, a: TypedValue, b: TypedValue) -> TypedComp {
    TypedComp::new(pure_sig(result), TypedCompKind::Prim(op, a, b))
}

fn call(f: &str, args: Vec<TypedValue>, result: CoreType) -> TypedComp {
    TypedComp::new(
        pure_sig(result),
        TypedCompKind::Call {
            callee: sym(f),
            instantiation: Vec::new(),
            args,
        },
    )
}

fn purity_cx(functions: Vec<TypedCoreFn>) -> Cx {
    Cx {
        fns: functions
            .into_iter()
            .map(|function| (function.name(), function))
            .collect(),
        pure: BTreeMap::new(),
        fresh: 0,
        joins: 0,
        emitted: Vec::new(),
    }
}

fn sdone() -> TypedValue {
    TypedValue::new(
        step_ty(),
        TypedValueKind::Ctor {
            name: sym("SDone"),
            tag: 0,
            instantiation: Vec::new(),
            fields: Vec::new(),
        },
    )
}

fn smore(head: TypedValue, tail: TypedValue) -> TypedValue {
    TypedValue::new(
        step_ty(),
        TypedValueKind::Ctor {
            name: sym("SMore"),
            tag: 1,
            instantiation: Vec::new(),
            fields: vec![head, tail],
        },
    )
}

// The step application `force(seq)(())`.
fn force_app(seq: TypedValue) -> TypedComp {
    let fun = CoreFnSig::new(Vec::new(), vec![source(Type::Unit)], pure_sig(step_ty()));
    let force = TypedComp::new(
        pure_sig(CoreType::Function(Box::new(fun))),
        TypedCompKind::Force(seq),
    );
    TypedComp::new(
        pure_sig(step_ty()),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![unit()],
        },
    )
}

fn step_lam(step: TypedComp) -> TypedComp {
    let lam_sig = CoreFnSig::new(Vec::new(), vec![source(Type::Unit)], pure_sig(step_ty()));
    TypedComp::new(
        pure_sig(CoreType::Function(Box::new(lam_sig))),
        TypedCompKind::Lam(
            vec![TypedBinder::new(sym("u"), source(Type::Unit))],
            Box::new(step),
        ),
    )
}

fn done_pattern() -> TypedPattern {
    TypedPattern::Ctor {
        name: sym("SDone"),
        instantiation: Vec::new(),
        fields: Vec::new(),
    }
}

fn more_pattern(head: &str, tail: &str) -> TypedPattern {
    TypedPattern::Ctor {
        name: sym("SMore"),
        instantiation: Vec::new(),
        fields: vec![
            Some(TypedBinder::new(sym(head), int())),
            Some(TypedBinder::new(sym(tail), seq_ty())),
        ],
    }
}

// fn count(i, n) = return thunk \u.
//   bind b = i <= n in
//   if b then bind i2 = i + 1 in bind t = count(i2, n) in return SMore(i, t)
//   else return SDone
fn count_fn() -> TypedCoreFn {
    let yield_branch = bind(
        prim(CoreOp::Add, int(), var("i", int()), lit(1)),
        "i2",
        int(),
        bind(
            call("count", vec![var("i2", int()), var("n", int())], seq_ty()),
            "t",
            seq_ty(),
            ret(smore(var("i", int()), var("t", seq_ty()))),
        ),
    );
    let step = bind(
        prim(
            CoreOp::Le,
            source(Type::Bool),
            var("i", int()),
            var("n", int()),
        ),
        "b",
        source(Type::Bool),
        TypedComp::new(
            pure_sig(step_ty()),
            TypedCompKind::If(
                var("b", source(Type::Bool)),
                Box::new(yield_branch),
                Box::new(ret(sdone())),
            ),
        ),
    );
    let body = ret(TypedValue::new(
        seq_ty(),
        TypedValueKind::Thunk(Box::new(step_lam(step))),
    ));
    TypedCoreFn::new(
        sym("count"),
        vec![
            TypedBinder::new(sym("i"), int()),
            TypedBinder::new(sym("n"), int()),
        ],
        body,
        CoreFnSig::new(Vec::new(), vec![int(), int()], pure_sig(seq_ty())),
        0,
    )
}

// fn map(f, s) = return thunk \u.
//   bind st = force(s)(()) in
//   case st of
//     SDone => return SDone
//     SMore(x, rest) =>
//       bind y = force(f)(x) in bind t = map(f, rest) in return SMore(y, t)
fn map_fn() -> TypedCoreFn {
    let apply_f = {
        let fun = CoreFnSig::new(Vec::new(), vec![int()], pure_sig(int()));
        let force = TypedComp::new(
            pure_sig(CoreType::Function(Box::new(fun))),
            TypedCompKind::Force(var("f", mapper_ty())),
        );
        TypedComp::new(
            pure_sig(int()),
            TypedCompKind::App {
                callee: Box::new(force),
                instantiation: Vec::new(),
                args: vec![var("x", int())],
            },
        )
    };
    let more_body = bind(
        apply_f,
        "y",
        int(),
        bind(
            call(
                "map",
                vec![var("f", mapper_ty()), var("rest", seq_ty())],
                seq_ty(),
            ),
            "t",
            seq_ty(),
            ret(smore(var("y", int()), var("t", seq_ty()))),
        ),
    );
    let case = TypedComp::new(
        pure_sig(step_ty()),
        TypedCompKind::Case(
            var("st", step_ty()),
            vec![
                (done_pattern(), ret(sdone())),
                (more_pattern("x", "rest"), more_body),
            ],
        ),
    );
    let step = bind(force_app(var("s", seq_ty())), "st", step_ty(), case);
    let body = ret(TypedValue::new(
        seq_ty(),
        TypedValueKind::Thunk(Box::new(step_lam(step))),
    ));
    TypedCoreFn::new(
        sym("map"),
        vec![
            TypedBinder::new(sym("f"), mapper_ty()),
            TypedBinder::new(sym("s"), seq_ty()),
        ],
        body,
        CoreFnSig::new(Vec::new(), vec![mapper_ty(), seq_ty()], pure_sig(seq_ty())),
        0,
    )
}

// fn total(s, acc) =
//   bind st = force(s)(()) in
//   case st of
//     SDone => return acc
//     SMore(x, rest) => bind acc2 = acc + x in total(rest, acc2)
fn total_fn() -> TypedCoreFn {
    let more_body = bind(
        prim(CoreOp::Add, int(), var("acc", int()), var("x", int())),
        "acc2",
        int(),
        call(
            "total",
            vec![var("rest", seq_ty()), var("acc2", int())],
            int(),
        ),
    );
    let case = TypedComp::new(
        pure_sig(int()),
        TypedCompKind::Case(
            var("st", step_ty()),
            vec![
                (done_pattern(), ret(var("acc", int()))),
                (more_pattern("x", "rest"), more_body),
            ],
        ),
    );
    let body = bind(force_app(var("s", seq_ty())), "st", step_ty(), case);
    TypedCoreFn::new(
        sym("total"),
        vec![
            TypedBinder::new(sym("s"), seq_ty()),
            TypedBinder::new(sym("acc"), int()),
        ],
        body,
        CoreFnSig::new(Vec::new(), vec![seq_ty(), int()], pure_sig(int())),
        0,
    )
}

fn step_env() -> VerifyEnv {
    let mut env = VerifyEnv::new();
    env.insert_constructor(
        sym("SDone"),
        ConstructorSig::new(Vec::new(), 0, Vec::new(), step_ty()),
    );
    env.insert_constructor(
        sym("SMore"),
        ConstructorSig::new(Vec::new(), 1, vec![int(), seq_ty()], step_ty()),
    );
    env
}

// Verify the fixture, run the typed pass on the witnesses, verify the
// output, and return the fused tree with the pass's own tick count for the
// caller's structural assertions.
fn run_and_verify(functions: Vec<TypedCoreFn>, env: &VerifyEnv) -> (TypedCore<Elaborated>, u64) {
    let input = verify(UncheckedTypedCore::<Elaborated>::new(functions), env)
        .unwrap_or_else(|violations| panic!("input fixture is invalid: {violations:#?}"));
    let (actual, stats) = fuse(input);
    let actual = verify(actual, env)
        .unwrap_or_else(|violations| panic!("fused typed Core is invalid: {violations:#?}"));
    (actual, stats.ticks())
}

// `total(count(3, 10), 0)`: the producer-fold seed fuses into one join
// whose loop carries the advancing counter and the accumulator.
#[test]
fn producer_fold_pipeline_fuses_to_a_join() {
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        bind(
            call("count", vec![lit(3), lit(10)], seq_ty()),
            "s",
            seq_ty(),
            call("total", vec![var("s", seq_ty()), lit(0)], int()),
        ),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let (actual, ticks) = run_and_verify(vec![count_fn(), total_fn(), main], &step_env());
    assert_eq!(ticks, 1);
    let join = Sym::new(&names::fused_join(0));
    assert!(actual.functions().iter().any(|f| f.name() == join));
}

// `total(map(dbl, count(3, 10)), 0)`: the transformer composes with the
// producer (case-of-case through the driven leaves) and the whole nested
// pipeline still residualizes into a single join.
#[test]
fn mapped_pipeline_fuses_through_the_transformer() {
    let dbl = {
        let fun = CoreFnSig::new(Vec::new(), vec![int()], pure_sig(int()));
        let lam = TypedComp::new(
            pure_sig(CoreType::Function(Box::new(fun))),
            TypedCompKind::Lam(
                vec![TypedBinder::new(sym("z"), int())],
                Box::new(prim(CoreOp::Mul, int(), var("z", int()), lit(2))),
            ),
        );
        TypedValue::new(mapper_ty(), TypedValueKind::Thunk(Box::new(lam)))
    };
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        bind(
            call("count", vec![lit(3), lit(10)], seq_ty()),
            "s0",
            seq_ty(),
            bind(
                ret(dbl),
                "d",
                mapper_ty(),
                bind(
                    call(
                        "map",
                        vec![var("d", mapper_ty()), var("s0", seq_ty())],
                        seq_ty(),
                    ),
                    "s1",
                    seq_ty(),
                    call("total", vec![var("s1", seq_ty()), lit(0)], int()),
                ),
            ),
        ),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let (actual, ticks) = run_and_verify(vec![count_fn(), map_fn(), total_fn(), main], &step_env());
    assert_eq!(ticks, 1);
    let join = Sym::new(&names::fused_join(0));
    assert!(actual.functions().iter().any(|f| f.name() == join));
}

// A consumer whose sequence argument is an opaque parameter (no upstream
// binding to resolve) is left exactly as written on both sides.
#[test]
fn unresolved_stream_leaves_the_call_untouched() {
    let opaque = TypedCoreFn::new(
        sym("opaque"),
        vec![TypedBinder::new(sym("s"), seq_ty())],
        call("total", vec![var("s", seq_ty()), lit(0)], int()),
        CoreFnSig::new(Vec::new(), vec![seq_ty()], pure_sig(int())),
        0,
    );
    let (_, ticks) = run_and_verify(vec![total_fn(), opaque], &step_env());
    assert_eq!(ticks, 0);
}

// A fold whose per-element action contains an effect node (the aborting
// `Error` intrinsic) fails the purity gate and degrades to not fusing.
#[test]
fn impure_step_refuses_to_fuse() {
    let more_body = bind(
        TypedComp::new(pure_sig(int()), TypedCompKind::Error(lit(0))),
        "e",
        int(),
        bind(
            prim(CoreOp::Add, int(), var("acc", int()), var("x", int())),
            "acc2",
            int(),
            call(
                "crashy",
                vec![var("rest", seq_ty()), var("acc2", int())],
                int(),
            ),
        ),
    );
    let case = TypedComp::new(
        pure_sig(int()),
        TypedCompKind::Case(
            var("st", step_ty()),
            vec![
                (done_pattern(), ret(var("acc", int()))),
                (more_pattern("x", "rest"), more_body),
            ],
        ),
    );
    let crashy = TypedCoreFn::new(
        sym("crashy"),
        vec![
            TypedBinder::new(sym("s"), seq_ty()),
            TypedBinder::new(sym("acc"), int()),
        ],
        bind(force_app(var("s", seq_ty())), "st", step_ty(), case),
        CoreFnSig::new(Vec::new(), vec![seq_ty(), int()], pure_sig(int())),
        0,
    );
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        bind(
            call("count", vec![lit(3), lit(10)], seq_ty()),
            "s",
            seq_ty(),
            call("crashy", vec![var("s", seq_ty()), lit(0)], int()),
        ),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let (_, ticks) = run_and_verify(vec![count_fn(), crashy, main], &step_env());
    assert_eq!(ticks, 0);
}

#[test]
fn peel_crosses_lowered_representation_boundaries() {
    let wrapped = super::super::effect_lower::test_lowered_repr(
        lit(7),
        CoreType::Lowered(super::super::LoweredType::Word),
    );
    assert!(matches!(&peel(&wrapped).kind, TypedValueKind::Int(7)));
}

#[test]
fn lowered_representation_cannot_hide_an_effectful_thunk() {
    let effectful_sig = CompSig::new(int(), EffRow::singleton(sym("Crash")));
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(effectful_sig.clone())),
        TypedValueKind::Thunk(Box::new(TypedComp::new(
            effectful_sig,
            TypedCompKind::Error(lit(0)),
        ))),
    );
    let wrapped = super::super::effect_lower::test_lowered_repr(
        thunk,
        CoreType::Lowered(super::super::LoweredType::Word),
    );
    let mut cx = purity_cx(Vec::new());

    assert!(!value_thunks_pure(&wrapped, &mut cx));
}

// A mapper that arrives through a parameter is a bare variable at the
// pipeline site: there is no thunk body to walk, and the structural gate
// that walks one passes it. Its type still carries the row, two levels in
// for a closure (a thunk of a function), and reading that witness is what
// refuses the fusion.
//
// Tested here rather than on a program because the pull-`Sequence` element
// type stores its tail as a pure thunk, so no source pipeline can carry an
// effectful step past the checker. This gate also covers any combinator whose
// step arrives through an effectful parameter.
#[test]
fn an_effectful_thunk_parameter_cannot_pass_as_pure() {
    let mapper = CoreFnSig::new(
        Vec::new(),
        vec![int()],
        CompSig::new(int(), EffRow::singleton(sym("Log"))),
    );
    let opaque = var(
        "f",
        CoreType::Thunk(Box::new(pure_sig(CoreType::Function(Box::new(mapper))))),
    );
    let mut cx = purity_cx(Vec::new());

    assert!(!value_pure(&opaque, &mut cx));
    assert!(!value_thunks_pure(&opaque, &mut cx));
}

// The same parameter under a row variable: the row proves nothing, so the
// structural verdict stands and a row-polymorphic combinator stays fusible
// at the pure instantiations its call sites supply.
#[test]
fn a_row_polymorphic_thunk_parameter_keeps_its_structural_verdict() {
    let mapper = CoreFnSig::new(
        Vec::new(),
        vec![int()],
        CompSig::new(int(), EffRow::Var(sym("e"))),
    );
    let opaque = var(
        "f",
        CoreType::Thunk(Box::new(pure_sig(CoreType::Function(Box::new(mapper))))),
    );
    let mut cx = purity_cx(Vec::new());

    assert!(value_pure(&opaque, &mut cx));
    assert!(value_thunks_pure(&opaque, &mut cx));
}

// Discovery starts at `a`: the old optimistic recursion breaker finalized
// `b` as pure while `a` was provisionally true, then found `a`'s effect and
// left the stale `b = true` memo behind. Both members share the SCC verdict.
#[test]
fn mutual_recursion_cannot_hide_a_sibling_effect() {
    let a = TypedCoreFn::new(
        sym("a"),
        Vec::new(),
        bind(
            call("b", Vec::new(), int()),
            "from_b",
            int(),
            TypedComp::new(pure_sig(int()), TypedCompKind::Error(lit(0))),
        ),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let b = TypedCoreFn::new(
        sym("b"),
        Vec::new(),
        call("a", Vec::new(), int()),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let mut cx = purity_cx(vec![a, b]);

    assert!(!fn_pure(sym("a"), &mut cx));
    assert_eq!(cx.pure.get(&sym("a")), Some(&false));
    assert_eq!(cx.pure.get(&sym("b")), Some(&false));
}

#[test]
fn pure_mutual_recursion_keeps_one_pure_scc_verdict() {
    let a = TypedCoreFn::new(
        sym("a"),
        Vec::new(),
        call("b", Vec::new(), int()),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let b = TypedCoreFn::new(
        sym("b"),
        Vec::new(),
        call("a", Vec::new(), int()),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let mut cx = purity_cx(vec![a, b]);

    assert!(fn_pure(sym("a"), &mut cx));
    assert_eq!(cx.pure.get(&sym("a")), Some(&true));
    assert_eq!(cx.pure.get(&sym("b")), Some(&true));
}

#[test]
fn deep_purity_call_graph_does_not_overflow() {
    let functions = (0..DEEP_PURITY_CALL_GRAPH_DEPTH)
        .map(|index| {
            let name = format!("deep_pure_{index}");
            let body = if index + 1 == DEEP_PURITY_CALL_GRAPH_DEPTH {
                ret(lit(0))
            } else {
                call(&format!("deep_pure_{}", index + 1), Vec::new(), int())
            };
            TypedCoreFn::new(
                sym(&name),
                Vec::new(),
                body,
                CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
                0,
            )
        })
        .collect();
    let mut cx = purity_cx(functions);

    assert!(fn_pure(sym("deep_pure_0"), &mut cx));
    assert_eq!(cx.pure.len(), DEEP_PURITY_CALL_GRAPH_DEPTH);
}

#[test]
fn deep_forced_parameter_scan_uses_the_bounded_typed_walk() {
    let mut body = force_app(var("stream", seq_ty()));
    for _ in 0..DEEP_TYPED_TRAVERSAL_DEPTH {
        body = bind(ret(lit(0)), "padding", int(), body);
    }

    assert_eq!(forced_params(&body, &[sym("stream")]), vec![0]);
    // Typed Core owns recursive boxes; keep the assertion about the analysis,
    // not the standard recursive destructor for this synthetic hostile tree.
    std::mem::forget(body);
}

#[test]
fn deep_pure_bind_chain_uses_the_bounded_typed_walk() {
    let mut body = ret(lit(0));
    for _ in 0..DEEP_TYPED_TRAVERSAL_DEPTH {
        body = bind(ret(lit(1)), "padding", int(), body);
    }
    let mut cx = purity_cx(Vec::new());

    assert!(comp_pure(&body, &mut cx));
    std::mem::forget(body);
}

#[test]
fn deep_nested_value_uses_the_bounded_typed_walk() {
    let mut value = lit(0);
    for _ in 0..DEEP_TYPED_TRAVERSAL_DEPTH {
        value = TypedValue::new(int(), TypedValueKind::Reinterpret(Box::new(value)));
    }
    let mut cx = purity_cx(Vec::new());

    assert!(value_pure(&value, &mut cx));
    assert!(value_thunks_pure(&value, &mut cx));
    std::mem::forget(value);
}

#[test]
fn deep_latent_effect_type_uses_an_explicit_chain_walk() {
    let mut ty = CoreType::Thunk(Box::new(CompSig::new(
        int(),
        EffRow::singleton(sym("DeepEffect")),
    )));
    for _ in 0..DEEP_TYPED_TRAVERSAL_DEPTH {
        ty = CoreType::Thunk(Box::new(pure_sig(ty)));
    }
    let value = var("opaque", ty);
    let mut cx = purity_cx(Vec::new());

    assert!(!value_thunks_pure(&value, &mut cx));
    std::mem::forget(value);
}

#[test]
fn deep_stream_pipeline_uses_an_explicit_worklist() {
    let comb = sym("deep_stream_comb");
    let function = TypedCoreFn::new(
        comb,
        Vec::new(),
        ret(lit(0)),
        CoreFnSig::new(Vec::new(), Vec::new(), pure_sig(int())),
        0,
    );
    let mut stream = StreamExpr {
        comb,
        instantiation: Vec::new(),
        args: vec![Arg::Val(lit(0))],
    };
    for _ in 0..DEEP_TYPED_TRAVERSAL_DEPTH {
        stream = StreamExpr {
            comb,
            instantiation: Vec::new(),
            args: vec![Arg::Stream(Box::new(stream))],
        };
    }
    let mut cx = purity_cx(vec![function]);

    assert!(stream_pure(&stream, &mut cx));
    std::mem::forget(stream);
}

// Defense-in-depth guard, tested directly because no curated pipeline can
// reach it: every tail-advance value residualized into a join body references
// only the abstracted stream variables plus top-level functions and literals,
// never a binder introduced during driving. An open tail makes the seed
// degrade to not-fusing instead of emitting an open join (a miscompile).
#[test]
fn scope_guard_refuses_a_leaked_local() {
    let p = sym("p0");
    let leaked = sym("leaked");
    let closed = ret(var("p0", int()));
    assert!(join_is_closed(&closed, &[p]));
    let open = ret(var("leaked", int()));
    assert!(!join_is_closed(&open, &[p]));
    let _ = leaked;
}

#[test]
fn stream_equality_compares_float_bits() {
    let comb = sym("producer");
    let float = |x: f64| TypedValue::new(source(Type::Float), TypedValueKind::Float(x));
    let a = StreamExpr {
        comb,
        instantiation: Vec::new(),
        args: vec![Arg::Val(float(0.0))],
    };
    let b = StreamExpr {
        comb,
        instantiation: Vec::new(),
        args: vec![Arg::Val(float(-0.0))],
    };
    assert!(!stream_eq(&a, &b));
}

#[test]
fn classify_rejects_changed_non_abstracted_float_bits() {
    let comb = sym("producer");
    let float = |x: f64| TypedValue::new(source(Type::Float), TypedValueKind::Float(x));
    let sym_seed = StreamExpr {
        comb,
        instantiation: Vec::new(),
        args: vec![Arg::Val(float(0.0))],
    };
    let tail = StreamExpr {
        comb,
        instantiation: Vec::new(),
        args: vec![Arg::Val(float(-0.0))],
    };
    assert!(classify(
        &sym_seed,
        &tail,
        &BTreeMap::new(),
        &mut Vec::new(),
        &mut Vec::new(),
        &mut BTreeMap::new(),
    )
    .is_none());
}
