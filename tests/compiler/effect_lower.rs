// Effect-lowering strategy and boundary tests: relocated from the
// `effect_lower` module when the middle end moved to `prism-core`, because
// they exercise the full front end (resolve, check, elaborate) that lives
// above that crate.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use prism::core::CoreOp;
use prism::flags::EffectTier;
use prism::types::ty::Label;
use prism_common::fresh::Fresh;

use prism::core::typed::verify::OperationSig;
use prism::core::typed::{CompSig, CoreFnSig, CoreQuantifier, CoreType, TypedBinder, TypedPattern};

use prism::core::typed::effect_lower::diagnostics::DriftLog;
use prism::core::typed::effect_lower::*;
use prism::core::typed::effect_lower::{
    analysis, arena, assemble_local_partial, functions_use_constructor, monadic, monadic_fallback,
    operation_ids, prepare, raw_effects, residual, state, trampoline, walk, with_local_decline,
    Decision,
};
use prism::core::typed::effect_lower::{LocalDeclinePoint, LocalSplit, LoweringAnalysis};
use prism::core::typed::*;
use prism::core::EffectStrategy::{
    Evidence, LocalPartial, Pure, SelectiveFreeMonad, StateFusion, WholeProgramFreeMonad,
};
use prism::core::{
    audit_typed_core, verify_typed_core, EffectStrategy, OpGrades, UncheckedTypedCore,
};
use prism::flags::DynFlags;
use prism::types::ty::EffRow;
use prism::types::CtorInfo;
use prism::types::Type;
use prism_common::sym::Sym;
use prism_syntax::ast::Grade;

fn sym(name: &str) -> Sym {
    Sym::new(name)
}

// The row-union failure path is unreachable on well-typed input, so a debug
// build keeps it loud: `union_effects` trips the invariant debug_assert. This is
// the development tripwire, not a program-visible outcome.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "typed effect-lowering row union invariant")]
fn row_union_failure_is_loud_in_debug() {
    let left = EffRow::Var(sym("left"));
    let right = EffRow::Var(sym("right"));
    let _ = union_effects(&left, &right);
}

// In release the same path must never crash: it degrades to a total, silent
// widening (the union of both children's effects under the left tail, keeping
// every effect). A tier-observable panic here would betray which lowering fired,
// exactly what the determinism contract forbids, so the release gate pins the
// widening rather than a panic.
#[test]
#[cfg(not(debug_assertions))]
fn row_union_failure_widens_in_release() {
    let left = EffRow::canonical([Label::bare("State")], EffRow::Var(sym("l")));
    let right = EffRow::canonical([Label::bare("Exn")], EffRow::Var(sym("r")));
    let widened = union_effects(&left, &right);
    let names: BTreeSet<&str> = widened
        .labels()
        .iter()
        .map(|label| label.name.as_str())
        .collect();
    assert!(
        names.contains("State") && names.contains("Exn"),
        "widening must keep every effect; got {}",
        widened.show()
    );
}

const fn source(ty: Type) -> CoreType {
    CoreType::Source(ty)
}

const fn int() -> CoreType {
    source(Type::Int)
}

const fn pure_sig(result: CoreType) -> CompSig {
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

const fn lit(n: i64) -> TypedValue {
    TypedValue::new(int(), TypedValueKind::Int(n))
}

fn eop_operation_ids(functions: &[TypedCoreFn], region: &BTreeSet<Sym>) -> Vec<i64> {
    let mut ids = Vec::new();
    for function in functions
        .iter()
        .filter(|function| region.contains(&function.name()))
    {
        collect_eop_ids_comp(function.body(), &mut ids);
    }
    ids
}

fn collect_eop_ids_comp(comp: &TypedComp, ids: &mut Vec<i64>) {
    walk::each_value(comp, &mut |value| collect_eop_ids_value(value, ids));
    walk::each_subcomp(comp, &mut |child| collect_eop_ids_comp(child, ids));
}

fn collect_eop_ids_value(value: &TypedValue, ids: &mut Vec<i64>) {
    match value.kind() {
        TypedValueKind::Ctor { name, fields, .. } => {
            if name.as_str() == "EOp" {
                if let Some(TypedValueKind::Int(id)) = fields.first().map(TypedValue::kind) {
                    ids.push(*id);
                }
            }
            for field in fields {
                collect_eop_ids_value(field, ids);
            }
        }
        TypedValueKind::Thunk(body) => collect_eop_ids_comp(body, ids),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => {
            collect_eop_ids_value(inner, ids);
        }
        TypedValueKind::Tuple(fields) | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                collect_eop_ids_value(field, ids);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                collect_eop_ids_value(field, ids);
            }
        }
        TypedValueKind::Var { .. }
        | TypedValueKind::Unit
        | TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Str(_) => {}
    }
}

fn contains_init_at(comp: &TypedComp) -> bool {
    if matches!(comp.kind(), TypedCompKind::InitAt(..)) {
        return true;
    }
    let mut found = false;
    walk::each_subterm(comp, &mut |child| found |= contains_init_at(child));
    found
}

fn ret(v: TypedValue) -> TypedComp {
    TypedComp::new(pure_sig(v.ty().clone()), TypedCompKind::Return(v))
}

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

const fn prim(op: CoreOp, result: CoreType, a: TypedValue, b: TypedValue) -> TypedComp {
    TypedComp::new(pure_sig(result), TypedCompKind::Prim(op, a, b))
}

fn int_fn(name: &str, params: &[&str], body: TypedComp) -> TypedCoreFn {
    TypedCoreFn::new(
        sym(name),
        params
            .iter()
            .map(|p| TypedBinder::new(sym(p), int()))
            .collect(),
        body,
        CoreFnSig::new(Vec::new(), vec![int(); params.len()], pure_sig(int())),
        0,
    )
}

// Verify both sides of the typed phase transition and its erased residual
// invariant. Individual fixtures pin the strategy and structure they are
// intended to exercise.
fn assert_lowering(
    functions: Vec<TypedCoreFn>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
) -> TypedLowering {
    let input = verify_typed_core(UncheckedTypedCore::new(functions), env)
        .unwrap_or_else(|violations| panic!("input fixture is invalid: {violations:#?}"));
    assert_typed_lowering(input, env, ctors, &DynFlags::default(), &OpGrades::new())
}

fn assert_typed_lowering(
    input: TypedCore<Elaborated>,
    env: &VerifyEnv,
    ctors: &BTreeMap<String, CtorInfo>,
    flags: &DynFlags,
    grades: &OpGrades,
) -> TypedLowering {
    if let Err(violations) = audit_typed_core(&input, env) {
        panic!("input fixture is invalid: {violations:#?}");
    }
    let out = lower_effects(input, env, ctors, flags, grades).expect("typed lowering succeeds");
    if let Err(violations) = audit_typed_core(&out.core, &out.env) {
        panic!("lowered typed Core is invalid: {violations:#?}");
    }
    prism::core::residual_effects(&out.core.clone().erase())
        .expect("typed lowering must eliminate raw effects");
    out
}

// A pure program with a dead helper: the transition prunes to the reachable
// set, classifies pure, and extends nothing.
#[test]
fn pure_program_lowers_with_reachability_pruning() {
    let helper = int_fn(
        "helper",
        &["x"],
        prim(CoreOp::Add, int(), var("x", int()), lit(1)),
    );
    let dead = int_fn("dead", &[], ret(lit(9)));
    let main = int_fn(
        "main",
        &[],
        bind(
            call("helper", vec![lit(41)], int()),
            "r",
            int(),
            ret(var("r", int())),
        ),
    );
    let out = assert_lowering(
        vec![helper, main, dead],
        &VerifyEnv::new(),
        &BTreeMap::new(),
    );
    assert_eq!(out.strategy, EffectStrategy::Pure);
    let names: Vec<&str> = out
        .core
        .functions()
        .iter()
        .map(|f| f.name().as_str())
        .collect();
    assert_eq!(names, ["helper", "main"], "dead helper pruned, order kept");
}

// Without an entry point nothing is pruned (a library compile).
#[test]
fn entryless_program_is_left_unpruned() {
    let helper = int_fn("helper", &["x"], ret(var("x", int())));
    let out = assert_lowering(vec![helper], &VerifyEnv::new(), &BTreeMap::new());
    assert_eq!(out.core.functions().len(), 1);
    assert_eq!(out.strategy, EffectStrategy::Pure);
}

// An unhandled effect takes the selective free-monad path and retains the
// top-level trap, warning, and synthetic constructors.
#[test]
fn effectful_program_routes_to_the_selective_free_monad() {
    let operation = sym("ask");
    let effect = sym("Ask");
    let mut env = VerifyEnv::new();
    env.insert_operation(
        operation,
        OperationSig::new(Vec::new(), Vec::new(), int(), Label::bare(effect)),
    );
    let body = TypedComp::new(
        CompSig::new(int(), EffRow::singleton(effect)),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body,
        CoreFnSig::new(
            Vec::new(),
            Vec::new(),
            CompSig::new(int(), EffRow::singleton(effect)),
        ),
        0,
    );
    let out = assert_lowering(vec![main], &env, &BTreeMap::new());
    assert_eq!(out.strategy, EffectStrategy::SelectiveFreeMonad);
}

#[test]
fn every_effect_strategy_and_lowering_flag_boundary_is_accounted_for() {
    struct Fixture {
        name: &'static str,
        source: &'static str,
        // One rung per knob position, in `EffectTier::ALL` order.
        expected: [EffectStrategy; EffectTier::ALL.len()],
    }

    let fixtures = [
        Fixture {
            name: "pure",
            source: include_str!("../../examples/accum.pr"),
            expected: [Pure, Pure, Pure, Pure, Pure],
        },
        Fixture {
            name: "evidence",
            source: include_str!("../../examples/eff_reader.pr"),
            expected: [
                Evidence,
                SelectiveFreeMonad,
                SelectiveFreeMonad,
                SelectiveFreeMonad,
                WholeProgramFreeMonad,
            ],
        },
        Fixture {
            name: "state",
            source: include_str!("../../examples/eff_state.pr"),
            expected: [
                StateFusion,
                StateFusion,
                SelectiveFreeMonad,
                SelectiveFreeMonad,
                WholeProgramFreeMonad,
            ],
        },
        Fixture {
            name: "local",
            source: include_str!("../cases/run/local_mono_combined.pr"),
            expected: [
                LocalPartial,
                LocalPartial,
                LocalPartial,
                WholeProgramFreeMonad,
                WholeProgramFreeMonad,
            ],
        },
        Fixture {
            name: "selective",
            source: include_str!("../../examples/eff_nontail.pr"),
            expected: [
                SelectiveFreeMonad,
                SelectiveFreeMonad,
                SelectiveFreeMonad,
                SelectiveFreeMonad,
                WholeProgramFreeMonad,
            ],
        },
        Fixture {
            // The bottom rung needs a program every partial lowering must
            // decline: a declared-effectful callback hidden in a list is
            // opaque to the flow analysis at every knob position. A merely
            // effect-polymorphic caller no longer qualifies, because the
            // builder records exact stored witnesses and the region confines.
            name: "whole",
            source: include_str!("../cases/run/row_widen_named_effect_list.pr"),
            expected: [
                WholeProgramFreeMonad,
                WholeProgramFreeMonad,
                WholeProgramFreeMonad,
                WholeProgramFreeMonad,
                WholeProgramFreeMonad,
            ],
        },
    ];

    // Collect the whole table before judging it, so one failing run reports
    // every knob position rather than aborting on the first.
    let mut table = Vec::new();
    let mut want = Vec::new();
    for fixture in fixtures {
        let (typed, env, ctors, grades) = typed_from_program(fixture.source);
        let mut row = Vec::new();
        for effect_tier in EffectTier::ALL {
            let mut rung = None;
            for native_effects in [false, true] {
                for trampoline in [false, true] {
                    for quiet in [false, true] {
                        let flags = DynFlags {
                            native_effects,
                            trampoline,
                            quiet,
                            effect_tier,
                            ..DynFlags::default()
                        };
                        let out =
                            assert_typed_lowering(typed.clone(), &env, &ctors, &flags, &grades);
                        assert_eq!(
                            *rung.get_or_insert(out.strategy),
                            out.strategy,
                            "{} at {}: the auxiliary flags must not move the rung",
                            fixture.name,
                            effect_tier.label()
                        );
                        if fixture.name == "local" {
                            assert!(
                                out.warning.is_some(),
                                "quiet must not remove the structured fallback warning"
                            );
                        }
                        if fixture.name == "selective" {
                            // The native handler driver takes closed handlers
                            // only, so it appears exactly when the native-effects
                            // cell is on *and* the program stayed selective:
                            // whole-program scope declares every handler open,
                            // leaving the driver nothing to take.
                            let native_driver = native_effects
                                && out.strategy == EffectStrategy::SelectiveFreeMonad;
                            assert_eq!(
                                functions_use_constructor(out.core.functions(), "EResume"),
                                native_driver,
                                "the native-effects cell must exercise the native driver"
                            );
                            assert_eq!(out.ctors.contains_key("EResume"), native_driver);
                        }
                    }
                }
            }
            row.push((
                effect_tier.label(),
                rung.expect("one cell per knob position"),
            ));
        }
        want.push((
            fixture.name,
            EffectTier::ALL
                .iter()
                .zip(fixture.expected)
                .map(|(tier, rung)| (tier.label(), rung))
                .collect::<Vec<_>>(),
        ));
        table.push((fixture.name, row));
    }
    assert_eq!(table, want);
}

#[test]
fn direct_io_survives_selective_free_monad_reification() {
    let flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        ..DynFlags::default()
    };
    let compiled = typed_from_source(
        "effect Ask\n  ask() : Int\n\nfn main() =\n  let answer = ask()\n  println(answer)\n",
    );
    let (typed, env, ctors, grades) = compiled;
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, EffectStrategy::SelectiveFreeMonad);
}

#[test]
fn an_open_callback_row_coalesces_into_the_monadic_ambient() {
    let flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        ..DynFlags::default()
    };
    let (typed, env, ctors, grades) = typed_from_source(
            "effect Ask\n  ask() : Int\n\nfn apply(f : (Int) -> Int ! {| e}, x : Int) = f(x)\n\nfn use(f : (Int) -> Int ! {IO}) : Int ! {Ask, IO} =\n  let answer = ask()\n  apply(f, answer)\n\nfn main() = use(\\(n) -> let _ = println(n) in n)\n",
        );
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, EffectStrategy::SelectiveFreeMonad);
    let use_fn = out
        .core
        .functions()
        .iter()
        .find(|function| function.name().as_str() == "use")
        .expect("use survives reachability");
    assert_eq!(
        use_fn.sig().quantifiers().last(),
        Some(&CoreQuantifier::Row(Sym::from(
            prism_syntax::names::FREE_MONAD_ROW
        )))
    );
}

// Compile source through the real front end so fixtures carry the exact
// desugar shapes: parse -> resolve -> desugar -> typecheck ->
// elaborate_typed.
// A loop fixture needs the prelude: `while`/`for` desugar to calls to the
// prelude's `repeat_while`/`forever` drivers, so a prelude-free loop does
// not even typecheck.
fn typed_from_program(
    src: &str,
) -> (
    TypedCore<Elaborated>,
    VerifyEnv,
    BTreeMap<String, CtorInfo>,
    OpGrades,
) {
    typed_from_source(&prism::driver::with_prelude(src))
}

fn typed_from_source(
    src: &str,
) -> (
    TypedCore<Elaborated>,
    VerifyEnv,
    BTreeMap<String, CtorInfo>,
    OpGrades,
) {
    let parsed = prism_syntax::parse::parse(src)
        .expect("fixture parses")
        .program;
    // The embedded stdlib alone: a fixture imports only prelude modules,
    // never a file beside the compiler.
    let roots = [prism::resolve::Root::Embedded(prism::stdlib::STDLIB)];
    let resolved = prism::resolve::resolve_modules_in(parsed, &roots).expect("fixture resolves");
    let program = prism::syntax::desugar::desugar(resolved).expect("fixture desugars");
    let checked = prism::types::check(&program).expect("fixture typechecks");
    let grades = checked.op_grades();
    let ctors = checked.ctors.clone();
    let elaboration = prism::core::elaborate_typed(&program, &checked).expect("fixture elaborates");
    let (_compat, typed, env) = elaboration.into_parts();
    (typed, env, ctors, grades)
}

fn assert_program_lowering(src: &str) -> TypedLowering {
    assert_compiled_lowering(typed_from_program(src))
}

fn assert_source_lowering(src: &str) -> TypedLowering {
    assert_compiled_lowering(typed_from_source(src))
}

fn assert_compiled_lowering(
    compiled: (
        TypedCore<Elaborated>,
        VerifyEnv,
        BTreeMap<String, CtorInfo>,
        OpGrades,
    ),
) -> TypedLowering {
    let (typed, env, ctors, grades) = compiled;
    if let Err(violations) = audit_typed_core(&typed, &env) {
        panic!("compiled fixture is invalid: {violations:#?}");
    }
    let flags = DynFlags::default();
    let out = lower_effects(typed, &env, &ctors, &flags, &grades).expect("typed lowering succeeds");
    if let Err(violations) = audit_typed_core(&out.core, &out.env) {
        panic!("lowered typed Core is invalid: {violations:#?}");
    }
    prism::core::residual_effects(&out.core.clone().erase())
        .expect("typed lowering must eliminate raw effects");
    out
}

// A loop-free var program: the var handler erases to a mutable cell on
// both sides and the residue classifies pure, byte-identically (fresh
// `{n}@cell` names included).
#[test]
fn var_block_erases_to_a_cell() {
    let out = assert_source_lowering(
        "fn main() : Int ! {} =
  var x := 1
  x := 2
  x
",
    );
    assert_eq!(out.strategy, EffectStrategy::Pure);
}

// Nested vars erase inside out, keeping the two cells distinct.
#[test]
fn nested_var_blocks_erase_to_two_cells() {
    let out = assert_source_lowering(
        "fn main() : Int ! {} =
  var x := 1
  var y := 10
  x := y + 1
  y := x + 1
  x + y
",
    );
    assert_eq!(out.strategy, EffectStrategy::Pure);
}

// A guard `return` with no loop: the return handler erases to `Step`
// threading and a seed unwrap.
#[test]
fn guard_return_erases_to_step_threading() {
    let out = assert_source_lowering(
            "fn classify(n : Int) : Int =\n  if n < 0 then\n    return 0 - 1\n  1\n\nfn main() : Int = classify(0 - 8)\n",
        );
    assert_eq!(out.strategy, EffectStrategy::Pure);
}

// A return inside a match arm threads through the arm.
#[test]
fn return_in_match_arm_erases() {
    let out = assert_source_lowering(
            "fn describe(n : Int) : Int =\n  match n of\n    0 => return 100\n    _ => n * 2\n\nfn main() : Int = describe(0)\n",
        );
    assert_eq!(out.strategy, EffectStrategy::Pure);
}

// A `while` loop with a `break`: the loop erases to a generated
// tail-recursive `{n}@loopdrv` whose parameters are the captured cells.
#[test]
fn break_loop_erases_to_a_driver() {
    let out = assert_program_lowering(
            "fn count_to(n : Int) : Int =\n  var i := 0\n  while true do\n    if i >= n then\n      break\n    i := i + 1\n  i\n\nfn main() : Int = count_to(5)\n",
        );
    assert_eq!(out.strategy, EffectStrategy::Pure);
    assert!(
        out.core
            .functions()
            .iter()
            .any(|f| f.name().as_str().ends_with("@loopdrv")),
        "a driver is generated: {:?}",
        out.core
            .functions()
            .iter()
            .map(|f| f.name().as_str())
            .collect::<Vec<_>>()
    );
}

// The evidence rung on a real handler: a tail-resumptive reader whose
// clause becomes the evidence its perform site forces.
#[test]
fn tail_resumptive_handler_lowers_by_evidence() {
    let out = assert_program_lowering(
            "effect Ask\n  ask() : Int\n\nfn reader() : Int ! {Ask} = ask() + 1\n\nfn main() : Int =\n  handle reader() with {\n    ask() resume k => k(41),\n    return x => x\n  }\n",
        );
    assert_eq!(out.strategy, EffectStrategy::Evidence);
}

// The evidence signature prepass replaces `run`'s source residual row with a
// fresh ambient row. An unchanged polymorphic call retains that row in its
// explicit Core instantiation, both inside a handler clause and after the
// handle, so the substitution has to cover the entire typed body before the
// threading rewrite. Both programs also compile from a lower ladder start;
// the default evidence result and the forced fallback must independently
// verify.
#[test]
fn evidence_rewrites_residual_rows_through_the_whole_body() {
    let fixtures = [
        include_str!("../cases/run/evidence_residual_row_clause.pr"),
        include_str!("../cases/run/evidence_residual_row_after_handle.pr"),
    ];
    for src in fixtures {
        let (typed, env, ctors, grades) = typed_from_program(src);
        let evidence =
            assert_typed_lowering(typed.clone(), &env, &ctors, &DynFlags::default(), &grades);
        assert_eq!(evidence.strategy, EffectStrategy::Evidence);

        let state_flags = DynFlags {
            effect_tier: EffectTier::StateFusion,
            ..DynFlags::default()
        };
        let state = assert_typed_lowering(typed, &env, &ctors, &state_flags, &grades);
        assert_eq!(state.strategy, EffectStrategy::SelectiveFreeMonad);
    }
}

// A callback stored in data is recovered through a pattern, so the flow plan
// cannot attach one exact runtime convention to it. Even when every concrete
// callback is pure, the stored effectful witness is authoritative after that
// extraction. The cascade must recognize the opacity before a selective rung
// commits and route both the one- and two-element forms through the uniform
// whole-program convention.
#[test]
fn declared_effectful_callbacks_hidden_in_data_route_whole() {
    let src = include_str!("../cases/run/row_widen_named_effect_list.pr");
    for effect_tier in [EffectTier::Auto, EffectTier::StateFusion] {
        let (typed, env, ctors, grades) = typed_from_program(src);
        let flags = DynFlags {
            effect_tier,
            ..DynFlags::default()
        };
        let lowered = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
        assert_eq!(lowered.strategy, EffectStrategy::WholeProgramFreeMonad);
    }
}

// A stream producer returns an effectful thunk rather than performing in
// the producer call itself. The signature plan must widen that returned
// thunk from `flow.ret`, then carry the new witness through map/filter
// calls and their handler clauses. Otherwise the eventual force site adds
// an evidence row to the stale monomorphic thunk and the entire pipeline
// falls onto the allocating whole-program free monad.
#[test]
fn returned_stream_thunks_lower_by_evidence() {
    let out = assert_program_lowering(include_str!(
        "../../examples/fixtures/compiler/stream_fuse.pr"
    ));
    assert_eq!(out.strategy, EffectStrategy::Evidence);
}

// A whole arena program through the real cascade, and the first higher-order
// handler program to lower exactly. Preparation rewrites the constructors
// `build` and `scratch` allocate into `alloc`/`init_at` and re-verifies; the
// evidence engine then threads the `Alloc` clause `with_arena` installs down
// to them, including through `body`, the thunk parameter `with_arena` forces.
//
// That last step is what this pins. `body : () -> a ! {Alloc}` is a rank-2
// position: its ambient row is bound inside the parameter's own type, and the
// caller's thunk and the callee's declared parameter are minted by different
// passes that share no counter, so they agree only because the row is named
// by the operations it carries rather than by a counter.
#[test]
fn arena_program_lowers_exactly() {
    let out = assert_program_lowering("import Arena (..)\n\nfn build(n : Int, acc : List(Int)) : List(Int) =\n  if n == 0 then\n    acc\n  else\n    build(n - 1, Cons(n, acc))\n\nfn total(xs : List(Int)) : Int =\n  match xs of\n    Nil => 0\n    Cons(h, t) => h + total(t)\n\nfn scratch() : Int = total(build(3, Nil))\n\nfn main() : Int = with_arena(scratch)\n");
    assert_eq!(out.strategy, EffectStrategy::Evidence);
}

#[test]
fn arena_program_forced_to_the_free_monad_lowers_exactly() {
    let flags = DynFlags {
        effect_tier: EffectTier::WholeProgramFreeMonad,
        ..DynFlags::default()
    };
    let (typed, env, ctors, grades) = typed_from_program(include_str!("../../examples/arena.pr"));
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, EffectStrategy::WholeProgramFreeMonad);
    assert!(
        out.core
            .functions()
            .iter()
            .any(|function| contains_init_at(function.body())),
        "forced free-monad lowering must retain arena initialization"
    );
}

// Preparation is where an arena program's constructors actually move, and it
// is checked on its own rather than only through a cascade that declines
// later: the rewrite lands, and the prepared tree verifies at `ArenaPrepared`
// (which `prepare` will not stamp otherwise).
#[test]
fn arena_preparation_rewrites_constructors_and_verifies() {
    let src = "import Arena (..)\n\nfn build(n : Int, acc : List(Int)) : List(Int) =\n  if n == 0 then\n    acc\n  else\n    build(n - 1, Cons(n, acc))\n\nfn total(xs : List(Int)) : Int =\n  match xs of\n    Nil => 0\n    Cons(h, t) => h + total(t)\n\nfn scratch() : Int = total(build(3, Nil))\n\nfn main() : Int = with_arena(scratch)\n";
    let (typed, mut env, _, _) = typed_from_program(src);
    // The production seam (`prepare` in this module) seeds the region-hook
    // signatures before invoking the pass; a direct invocation must too.
    arena::insert_builtin_sigs(&mut env);
    let before = typed.clone().erase();
    let prepared = arena::prepare(typed.functions().to_vec(), &env).expect("preparation");
    assert_eq!(audit_typed_core(&prepared, &env), Ok(()));
    assert!(
        prepared
            .functions()
            .iter()
            .any(|function| contains_init_at(function.body())),
        "arena preparation must introduce InitAt"
    );
    let after = prepared.erase();
    assert_ne!(after, before, "an arena program must be rewritten");
}

// The no-op path: a program that never installs an `Alloc` handler must come
// through arena preparation untouched, which is what keeps the whole non-arena
// corpus byte-identical.
#[test]
fn a_program_without_an_arena_is_untouched_by_preparation() {
    let (typed, env, _, _) = typed_from_program("fn main() : List(Int) = Cons(1, Nil)\n");
    let before = typed.clone().erase();
    let prepared = arena::prepare(typed.functions().to_vec(), &env).expect("preparation");
    assert_eq!(prepared.erase(), before);
}

// A production State fixture must route through the typed State rung.
fn assert_state_fusion_routes(src: &str) {
    let out = assert_program_lowering(src);
    assert_eq!(
        out.strategy,
        EffectStrategy::StateFusion,
        "the fixture must exercise the State production rung"
    );
}

// A `get`/`put` handler interpreting state by parameter passing must produce
// a verified effect-free tree.
#[test]
fn threading_eff_state_verifies_and_eliminates_effects() {
    let src = "effect State\n  get() : Int\n  put(Int) : Unit\n\nfn tick() : Int ! {State} =\n  let n = get()\n  put(n + 1)\n  n\n\nfn counter() : Int ! {State} =\n  tick()\n  tick()\n  tick()\n  get()\n\nfn run_counter(init) =\n  let f =\n    handle counter() with\n      get() resume k => \\(s) -> k(s)(s)\n      put(s2) resume k => \\(_s) -> k(())(s2)\n      return r => \\(_s) -> r\n  f(init)\n\nfn main() = println(run_counter(0))\n";
    let (typed, env, ctors, grades) = typed_from_program(src);
    let flags = DynFlags::default();
    let (threaded, threaded_env) = threaded_state_typed(typed, &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("and the state engine threads this program");
    assert_eq!(audit_typed_core(&threaded, &threaded_env), Ok(()));
    prism::core::residual_effects(&threaded.erase()).expect("no raw effects survive");
}

// The writer, the other answer convention: the threaded accumulator is itself
// the answer, its return clause is the identity transformer and is absorbed,
// and the accumulator is a list rather than an `Int`, so nothing about the
// threading may assume the shape `eff_state` happens to have.
#[test]
fn threading_a_writer_verifies() {
    assert_threading_verifies(
            "effect Writer\n  tell(Int) : Unit\n\nfn trace() : Unit ! {Writer} =\n  tell(1)\n  tell(2)\n  tell(3)\n\nfn run_writer() =\n  let f =\n    handle trace() with\n      tell(m) resume k => \\(log) -> k(())(Cons(m, log))\n      return r => \\(log) -> log\n  f(Nil)\n\nfn main() = println(sum(run_writer()))\n",
        );
}

// A stream chain: `srange` returns an escaping producer thunk (a lambda that
// performs `emit` when forced), so the thunk gains evidence and accumulator
// parameters, `sfold`'s parameter declares the threaded type, and the force
// site inside the fold handle appends the matching arguments. This is the
// shape the whole `srange`-based corpus is built from.
#[test]
fn threading_a_stream_chain_verifies() {
    assert_threading_verifies("fn main() = println(srange(1, 5).ssum())\n");
}

// The forwarder and the escaping thunk together: `smap` re-emits under fresh
// shadowing evidence, and both the source and the mapped stream are escaping
// thunks. Producer, map and fold collapse to one loop.
#[test]
fn threading_a_mapped_stream_verifies() {
    assert_threading_verifies(
        "fn dbl(n) = n * 2\n\nfn main() = println(srange(1, 5).smap(dbl).ssum())\n",
    );
}

// Early termination through the `Step` protocol: `stake` drops its
// continuation after three elements, so every producer threads `Step` and
// stops on `SDone`, the take's evidence pairs its counter with the
// downstream state, and the fold's evidence becomes `Step`-aware. The whole
// pipeline still collapses to one loop.
#[test]
fn threading_a_take_verifies() {
    assert_threading_verifies("fn main() = println(srange(1, 10).stake(3).ssum())\n");
}

// The corpus take program whole: folds, maps, filters, takes, collects, a
// seeded sfold, and a for-loop control consumer, mixed in one program. This
// is `tests/cases/run/stream_take.pr` inlined (never `include_str!`: paths
// outside the compiler source roots are invisible to the gate cache).
//
#[test]
fn threading_the_take_corpus_program_verifies() {
    assert_threading_verifies(
            "fn dbl(n) = n * 2\n\nfn main() =\n  println(srange(1, 100).stake(0).ssum())\n  println(srange(1, 3).stake(10).ssum())\n  println(srange(1, 100).smap(dbl).skeep(\\(x) -> x > 2).stake(3).ssum())\n  println(length(srange(1, 100).stake(4).scollect()))\n  println(sum(srange(1, 100).skeep(even).stake(3).scollect()))\n  println(sfold(srange(1, 100).stake(4), 1, \\(acc, x) -> acc * x))\n  for x in srange(10, 100).stake(2) do\n    println(x)\n",
        );
}

// Every public corpus program routed through state threading, plus the two
// compiler-only stream fixtures, read from the tree and checked one by one.
// This is the population, not a sample, so a threading change that loses any
// one of them fails at its source. Read at run time rather than `include_str!`;
// this is an always-run library test, not a cached native verdict.
#[test]
fn production_state_corpus_routes_and_eliminates_effects() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let corpus = [
        "examples/eff_state.pr",
        "examples/eff_writer.pr",
        "examples/interaction.pr",
        "examples/param_effects.pr",
        "examples/fixtures/compiler/stream_fold.pr",
        "examples/streams.pr",
        "examples/fixtures/compiler/stream_ufcs.pr",
        "tests/cases/run/comp_map_once.pr",
        "tests/cases/run/fold_chains.pr",
        "tests/cases/run/stream_take.pr",
        "tests/cases/run/streams_edge.pr",
    ];
    for path in corpus {
        let src = fs::read_to_string(root.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
        let (typed, env, ctors, grades) = typed_from_program(&src);
        let flags = DynFlags::default();
        let threaded = lower_effects(typed, &env, &ctors, &flags, &grades)
            .unwrap_or_else(|e| panic!("{path}: the typed production rung fails: {e:?}"));
        assert_eq!(threaded.strategy, EffectStrategy::StateFusion);
        assert_eq!(
            audit_typed_core(&threaded.core, &threaded.env),
            Ok(()),
            "{path}: typed State output must verify"
        );
        prism::core::residual_effects(&threaded.core.erase())
            .unwrap_or_else(|error| panic!("{path}: {error}"));
    }
}

// The threaded corpus must verify before the rung stamps `EffectLowered`;
// this runs per program so a violation names its program.
#[test]
fn threaded_state_corpus_verifies() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let corpus = [
        "examples/eff_state.pr",
        "examples/eff_writer.pr",
        "examples/interaction.pr",
        "examples/param_effects.pr",
        "examples/fixtures/compiler/stream_fold.pr",
        "examples/streams.pr",
        "examples/fixtures/compiler/stream_ufcs.pr",
        "tests/cases/run/comp_map_once.pr",
        "tests/cases/run/fold_chains.pr",
        "tests/cases/run/stream_take.pr",
        "tests/cases/run/streams_edge.pr",
    ];
    let mut failures = Vec::new();
    for path in corpus {
        let src = fs::read_to_string(root.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
        let (typed, env, ctors, grades) = typed_from_program(&src);
        let flags = DynFlags::default();
        let (threaded, env2) = threaded_state_typed(typed, &env, &ctors, &flags, &grades)
            .unwrap_or_else(|e| panic!("{path}: cascade fails: {e:?}"))
            .unwrap_or_else(|| panic!("{path}: declines"));
        if let Err(violations) = audit_typed_core(&threaded, &env2) {
            failures.push(format!(
                "{path}: {} violations, first three: {:#?}",
                violations.len(),
                &violations[..violations.len().min(3)]
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn threaded_state_bind_rows_cover_transformed_children() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for path in ["examples/eff_state.pr", "examples/param_effects.pr"] {
        let src = fs::read_to_string(root.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
        let (typed, env, ctors, grades) = typed_from_program(&src);
        let (threaded, env2) =
            threaded_state_typed(typed, &env, &ctors, &DynFlags::default(), &grades)
                .unwrap_or_else(|e| panic!("{path}: cascade fails: {e:?}"))
                .unwrap_or_else(|| panic!("{path}: state engine declines"));
        if let Err(violations) = audit_typed_core(&threaded, &env2) {
            panic!("{path}: transformed Bind hides child effects: {violations:#?}");
        }
    }
}

// Exercise the State engine directly and require its witness and erased
// residual invariants.
fn assert_threading_verifies(src: &str) {
    let (typed, env, ctors, grades) = typed_from_program(src);
    let flags = DynFlags::default();
    let (threaded, threaded_env) = threaded_state_typed(typed, &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("and the state engine threads this program");
    assert_eq!(audit_typed_core(&threaded, &threaded_env), Ok(()));
    prism::core::residual_effects(&threaded.erase()).expect("no raw effects survive");
}

// A `get`/`put` handler interpreting state by parameter passing: each clause
// returns a transformer `\s -> ..` and `k(v)(s)` threads the state forward.
// The return clause `\(_s) -> r` is a get-style transformer, so the answer is
// the producer value rather than the accumulator.
#[test]
fn parameter_passing_state_handler_routes() {
    assert_state_fusion_routes(
            "effect State\n  get() : Int\n  put(Int) : Unit\n\nfn tick() : Int ! {State} =\n  let n = get()\n  put(n + 1)\n  n\n\nfn counter() : Int ! {State} =\n  tick()\n  tick()\n  get()\n\nfn run_counter(init) =\n  let f =\n    handle counter() with\n      get() resume k => \\(s) -> k(s)(s)\n      put(s2) resume k => \\(_s) -> k(())(s2)\n      return r => \\(_s) -> r\n  f(init)\n\nfn main() = run_counter(0)\n",
        );
}

#[test]
fn native_function_answer_region_matches_the_typed_production_route() {
    let src = "effect State\n  get() : Int\n  put(Int) : Unit\n\nfn tick() : Int ! {State} =\n  let n = get()\n  put(n + 1)\n  n\n\nfn counter() : Int ! {State} =\n  tick()\n  tick()\n  tick()\n  get()\n\nfn run_counter(init) =\n  let f =\n    handle counter() with\n      get() resume k => \\(s) -> k(s)(s)\n      put(s2) resume k => \\(_s) -> k(())(s2)\n      return r => \\(_s) -> r\n  f(init)\n\nfn main() = println(run_counter(0))\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    let flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        native_effects: true,
        quiet: true,
        ..DynFlags::default()
    };
    let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, EffectStrategy::SelectiveFreeMonad);
    let prepared = prepare(source, &env, &ctors, &flags, &grades).expect("typed preparation");
    let ops = operation_ids(&prepared.fns).expect("operation ids");
    let effects = EffectPlan::analyze(&prepared.fns);
    let latent = effects.latent();
    let plan = analysis::plan(&prepared.fns, &effects, false);
    assert_eq!(plan.scope, analysis::MonadicScope::Selective);

    let mut fresh = Fresh::new();
    let mut lowered = monadic::lower_selective(
        &prepared.fns,
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &monadic::Region {
            plan: &plan,
            latent,
            flow: effects.flow(),
            native_enabled: true,
        },
    )
    .expect("native function-answer region lowers");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut lowered_env = prepared.env.clone();
    abi::insert(&mut lowered_env);
    let typed = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(lowered),
        &lowered_env,
    )
    .expect("native function-answer lowering must mint effect-lowered authority");
    assert_eq!(typed.erase(), out.core.clone().erase());

    let off_flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        native_effects: false,
        quiet: true,
        ..DynFlags::default()
    };
    let off_source = typed_from_program(src).0;
    let off_out = assert_typed_lowering(off_source, &env, &ctors, &off_flags, &grades);
    assert_eq!(off_out.strategy, EffectStrategy::SelectiveFreeMonad);
    assert_ne!(
        out.core.erase(),
        off_out.core.clone().erase(),
        "the native-effects flag must exercise distinct production lowerings"
    );
    let mut off_fresh = Fresh::new();
    let mut off_functions = monadic::lower_selective(
        &prepared.fns,
        &ops,
        &mut off_fresh,
        &EffRow::Empty,
        &monadic::Region {
            plan: &plan,
            latent,
            flow: effects.flow(),
            native_enabled: false,
        },
    )
    .expect("typed non-native function-answer fallback");
    off_functions.push(abi::ebind_fn());
    off_functions.push(abi::qapply_fn());
    let mut off_env = prepared.env;
    abi::insert(&mut off_env);
    let off = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(off_functions),
        &off_env,
    )
    .expect("non-native fallback must mint effect-lowered authority");
    assert_eq!(off.erase(), off_out.core.erase());
}

#[test]
fn whole_program_trampoline_is_deterministic_and_verifies() {
    let src = "effect Ask\n  ask() : Int\n\nfn make() = \\() -> let answer = ask() in let _ = println(answer) in answer\n\nfn main() =\n  let unused = make()\n  0\n";
    let (source, env, ctors, grades) = typed_from_source(src);
    let flags = DynFlags {
        effect_tier: EffectTier::WholeProgramFreeMonad,
        quiet: true,
        ..DynFlags::default()
    };
    let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, EffectStrategy::WholeProgramFreeMonad);
    assert!(out
        .core
        .functions()
        .iter()
        .any(|function| function.name().as_str() == "prism_drive"));
    assert!(functions_use_constructor(out.core.functions(), "EBounce"));
    assert!(out.ctors.contains_key("EBounce"));

    let off_flags = DynFlags {
        trampoline: false,
        ..flags.clone()
    };
    let off = assert_typed_lowering(source.clone(), &env, &ctors, &off_flags, &grades);
    assert_eq!(off.strategy, EffectStrategy::WholeProgramFreeMonad);
    assert!(!off
        .core
        .functions()
        .iter()
        .any(|function| function.name().as_str() == "prism_drive"));
    assert!(!functions_use_constructor(off.core.functions(), "EBounce"));
    assert!(!off.ctors.contains_key("EBounce"));

    let prepared = prepare(source, &env, &ctors, &flags, &grades).expect("typed preparation");
    let ops = operation_ids(&prepared.fns).expect("operation ids");
    let residual = residual::plan(&prepared.fns, &ops, &prepared.env)
        .expect("residual rows are declaration-owned");
    let mut fresh = Fresh::new();
    let mut lowered = monadic::lower_whole(&prepared.fns, &ops, &mut fresh, &residual)
        .expect("whole-program monadic lowering");
    let make = lowered
        .iter()
        .find(|function| function.name().as_str() == "make")
        .expect("make survives reachability");
    assert!(make
        .sig()
        .body()
        .effects()
        .label_names()
        .contains(&Sym::from(prism_syntax::names::IO_EFFECT)));
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());

    let mut first_fresh = Fresh::new();
    let mut second_fresh = Fresh::new();
    for _ in 0..11 {
        first_fresh.bump();
        second_fresh.bump();
    }
    let mut first = trampoline::trampolinize(&lowered, &mut first_fresh)
        .expect("first typed isolated trampoline lowering");
    first.push(trampoline::prism_drive_fn());
    let mut second = trampoline::trampolinize(&lowered, &mut second_fresh)
        .expect("second typed isolated trampoline lowering");
    second.push(trampoline::prism_drive_fn());
    assert_eq!(
        first, second,
        "the transform must be deterministic for the same fresh-name state"
    );

    lowered = trampoline::trampolinize(&lowered, &mut fresh).expect("typed trampoline lowering");
    lowered.push(trampoline::prism_drive_fn());

    let mut lowered_env = prepared.env;
    abi::insert(&mut lowered_env);
    let typed = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(lowered),
        &lowered_env,
    )
    .expect("trampoline lowering must mint effect-lowered authority");
    assert_eq!(typed.erase(), out.core.erase());

    // The control asks for the free-monad rung without pinning its scope, so
    // the cascade settles on the confined one and the trampoline stays out of a
    // program that never needed it.
    let selective_flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        ..flags
    };
    let (selective, selective_env, selective_ctors, selective_grades) =
        typed_from_source("effect Ask\n  ask() : Int\n\nfn main() = ask()\n");
    let selective = assert_typed_lowering(
        selective,
        &selective_env,
        &selective_ctors,
        &selective_flags,
        &selective_grades,
    );
    assert_eq!(selective.strategy, EffectStrategy::SelectiveFreeMonad);
    assert!(!selective
        .core
        .functions()
        .iter()
        .any(|function| function.name().as_str() == "prism_drive"));
    assert!(!functions_use_constructor(
        selective.core.functions(),
        "EBounce"
    ));
    assert!(!selective.ctors.contains_key("EBounce"));
}

#[test]
fn whole_program_direct_io_owns_a_nonempty_residual_row() {
    let src = r#"effect Ask
  ask() : Int

fn make() =
  \() -> let _ = println("inside") in ask()

fn main() =
  let unused = make()
  0
"#;
    let (source, env, ctors, grades) = typed_from_source(src);
    let flags = DynFlags {
        effect_tier: EffectTier::WholeProgramFreeMonad,
        quiet: true,
        ..DynFlags::default()
    };
    let out = assert_typed_lowering(source, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, EffectStrategy::WholeProgramFreeMonad);
    let ambient = Sym::from(prism_syntax::names::FREE_MONAD_ROW);
    let io = EffRow::canonical([Label::bare("IO")], EffRow::Var(ambient));
    let make = out
        .core
        .functions()
        .iter()
        .find(|function| function.name().as_str() == "make")
        .expect("make remains reachable through its first-class reference");
    assert_eq!(make.sig().body().result(), &abi::eff(io.clone()));
    assert_eq!(make.sig().body().effects(), &io);
    assert_eq!(
        make.sig().quantifiers().last(),
        Some(&CoreQuantifier::Row(ambient))
    );
}

// The answer convention is a property of the program, not of a chain, and
// that is deliberate rather than the accumulator's scope bug wearing a
// different hat.
//
// A writer chain and a state chain each fuse alone. Together they do not: the
// state chain's return clause is a get-style transformer, which puts the whole
// program in producer-answer mode, and the writer's handle body then has to be
// value-coincident too, which a body ending in a write is not. The typed
// State rung therefore declines this combined program.
#[test]
fn one_producer_answer_chain_sets_the_convention_for_the_whole_program() {
    let writer = "effect Writer\n  tell(Int) : Unit\n\nfn trace() : Unit ! {Writer} =\n  tell(1)\n  tell(2)\n\nfn run_writer() =\n  let f =\n    handle trace() with\n      tell(m) resume k => \\(log) -> k(())(Cons(m, log))\n      return r => \\(log) -> log\n  f(Nil)\n";
    let state = "effect State\n  get() : Int\n  put(Int) : Unit\n\nfn tick() : Int ! {State} =\n  let n = get()\n  put(n + 1)\n  n\n\nfn counter() : Int ! {State} =\n  tick()\n  get()\n\nfn run_counter(init) =\n  let f =\n    handle counter() with\n      get() resume k => \\(s) -> k(s)(s)\n      put(s2) resume k => \\(_s) -> k(())(s2)\n      return r => \\(_s) -> r\n  f(init)\n";

    assert_state_fusion_routes(&format!(
        "{writer}\nfn main() = println(sum(run_writer()))\n"
    ));
    assert_state_fusion_routes(&format!("{state}\nfn main() = println(run_counter(0))\n"));

    let (typed, env, ctors, grades) = typed_from_program(&format!(
        "{writer}\n{state}\nfn main() =\n  println(sum(run_writer()))\n  println(run_counter(0))\n"
    ));
    let flags = DynFlags::default();
    let recognized = recognized_strategy(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(recognized, EffectStrategy::StateFusion);
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, recognized);
}

// A gate-positive program the State rung still declines, which is the shape
// `examples/time.pr` has in the corpus: a real parameter-passing state
// handler (so the gate is right to admit it) whose body reads and then
// computes with the value.
//
// The threaded loop yields the accumulator, but the answer here is `n + 100`,
// so the two do not coincide and the engine would return the state where the
// program means the value. Declining is what keeps that from being a
// miscompile, and this rung must fall through to a slower engine exactly here
// rather than report a strategy it cannot deliver. Only the whole program is
// wrong: the same handler over a body whose tail is a read fuses.
#[test]
fn a_read_whose_value_is_computed_with_declines_below_the_gate() {
    // The two programs differ only in the tail of `counter`, which is what
    // makes the pair worth more than either half: the handler, the operations
    // and the producers are identical, so the gate cannot be what separates
    // them. A bare read is coincident (a read returns the state); binding that
    // read and computing with it is not.
    let program = |tail: &str| {
        format!("effect State\n  get() : Int\n  put(Int) : Unit\n\nfn tick() : Int ! {{State}} =\n  let n = get()\n  put(n + 1)\n  n\n\nfn counter() : Int ! {{State}} =\n  tick()\n  tick()\n  {tail}\n\nfn run_counter(init) =\n  let f =\n    handle counter() with\n      get() resume k => \\(s) -> k(s)(s)\n      put(s2) resume k => \\(_s) -> k(())(s2)\n      return r => \\(_s) -> r\n  f(init)\n\nfn main() = println(run_counter(0))\n")
    };
    assert_state_fusion_routes(&program("get()"));

    let (typed, env, ctors, grades) = typed_from_program(&program("let n = get()\n  n + 100"));
    let flags = DynFlags::default();
    let recognized = recognized_strategy(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(recognized, EffectStrategy::StateFusion);
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, recognized);
}

// Two independent chains, each folding its own effect at its own accumulator
// type. Nothing ties the two accumulators together: no producer is latent in
// both operations, so `p1` threads an `Int` and `p2` a `Bool`.
//
// The accumulator is therefore a property of a producer's own operations, not
// of the program: reading every fold clause in the program and demanding one
// type incorrectly declines this fusible program.
#[test]
fn two_chains_fold_at_their_own_accumulator_types() {
    assert_state_fusion_routes(
            "effect S1\n  get1() : Int\n\neffect S2\n  get2() : Bool\n\nfn p1() : Int ! {S1} = get1()\n\nfn p2() : Bool ! {S2} = get2()\n\nfn run1() =\n  let f =\n    handle p1() with\n      get1() resume k => \\(s) -> k(s)(s)\n      return r => \\(_s) -> r\n  f(0)\n\nfn run2() =\n  let g =\n    handle p2() with\n      get2() resume k => \\(s) -> k(s)(s)\n      return r => \\(_s) -> r\n  g(true)\n\nfn main() =\n  println(show_int(run1()))\n  println(show_bool(run2()))\n",
        );
}

// The same independent-operation boundary through escaping producer thunks.
// Each dynamic application passes only the evidence carried by the forced
// thunk; the other chain's globally numbered evidence is neither in scope nor
// part of the widened thunk signature.
#[test]
fn two_escaping_chains_pass_only_their_carried_evidence() {
    assert_state_fusion_routes(
            "effect E1\n  emit1(Int) : Unit\n\neffect E2\n  emit2(Int) : Unit\n\nfn p1() = \\(_u) -> emit1(1)\n\nfn p2() = \\(_u) -> emit2(2)\n\nfn run1(source : (Unit) -> Unit ! {E1}) =\n  let f =\n    handle source(()) with\n      emit1(x) resume k => \\(acc) -> k(())(acc + x)\n      return _r => \\(acc) -> acc\n  f(0)\n\nfn run2(source : (Unit) -> Unit ! {E2}) =\n  let g =\n    handle source(()) with\n      emit2(x) resume k => \\(acc) -> k(())(acc + x)\n      return _r => \\(acc) -> acc\n  g(0)\n\nfn main() =\n  println(run1(p1()))\n  println(run2(p2()))\n",
        );
}

// A writer, the other answer convention: the return clause `\(log) -> log` is
// the identity transformer, so the threaded accumulator is itself the answer.
// One handler, several fold clauses, and a `Cons` accumulator rather than an
// `Int` all ride the same gate.
#[test]
fn writer_handler_routes() {
    assert_state_fusion_routes(
            "effect Writer\n  tell(Int) : Unit\n\nfn trace() : Unit ! {Writer} =\n  tell(1)\n  tell(2)\n  tell(3)\n\nfn run_writer() =\n  let f =\n    handle trace() with\n      tell(m) resume k => \\(log) -> k(())(Cons(m, log))\n      return r => \\(log) -> log\n  f(Nil)\n\nfn main() = sum(run_writer())\n",
        );
}

// A var in scope of a genuinely multishot handler must NOT erase (a cell
// would share state across resumptions pure State keeps independent). The
// typed side then still carries raw effect nodes and reports the unsupported
// strategy, while the executable side proceeds to its free-monad strategy.
#[test]
fn multishot_scope_blocks_var_erasure() {
    let src = "effect Choice
  flip() : Bool

fn choose() : Int ! {Choice} =
  var x := 0
  if flip() then
    x := 1
  else
    x := 2
  x

fn main() : Int ! {} =
  handle choose() with {
    flip() resume k => k(true) + k(false),
    return x => x
  }
";
    let (typed, env, ctors, grades) = typed_from_source(src);
    if let Err(violations) = audit_typed_core(&typed, &env) {
        panic!("compiled fixture is invalid: {violations:#?}");
    }
    let flags = DynFlags::default();
    let recognized = recognized_strategy(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(recognized, EffectStrategy::Pure, "var state must not erase");
    // The declining half of the state gate: a multishot clause is no kind of
    // fold, so the typed gate must decline rather than recognize a program
    // that cannot thread an accumulator.
    assert_ne!(recognized, EffectStrategy::StateFusion);
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy, recognized);
}

// The clause classification, not the declared grade, decides multishot
// membership. A stale `once` grade on a clause that resumes twice must not
// re-admit var erasure: erasing would share one cell across resumptions the
// pure semantics keeps independent, and the miscompile would only surface in
// release builds if the disagreement were guarded by a debug assertion.
#[test]
fn a_multishot_clause_outranks_a_stale_once_grade() {
    let src = "effect Choice
  flip() : Bool

fn choose() : Int ! {Choice} =
  var x := 0
  if flip() then
    x := 1
  else
    x := 2
  x

fn main() : Int ! {} =
  handle choose() with {
    flip() resume k => k(true) + k(false),
    return x => x
  }
";
    let (typed, env, ctors, mut grades) = typed_from_source(src);
    grades.insert(sym("flip"), Grade::Once);
    let flags = DynFlags::default();
    let recognized = recognized_strategy(typed, &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(
        recognized,
        EffectStrategy::Pure,
        "a twice-resuming clause must block var erasure whatever the grade says"
    );
}

// Effects hiding inside thunks and constructor fields are still seen by
// the raw-effects scan.
#[test]
fn raw_effects_sees_through_thunks() {
    let operation = sym("ask");
    let effect = sym("Ask");
    let do_node = TypedComp::new(
        CompSig::new(int(), EffRow::singleton(effect)),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(do_node.sig().clone())),
        TypedValueKind::Thunk(Box::new(do_node)),
    );
    assert!(raw_effects(&ret(thunk.clone())));
    // An unboxed carrier is still a carrier: a thunk hidden in an unboxed
    // tuple field must not slip past the scan.
    let field_type = Type::Fun(Vec::new(), EffRow::singleton(effect), Box::new(Type::Int));
    let unboxed = TypedValue::new(
        CoreType::Source(Type::UnboxedTuple(vec![field_type])),
        TypedValueKind::UnboxedTuple(vec![thunk]),
    );
    assert!(raw_effects(&ret(unboxed)));
    assert!(!raw_effects(&ret(lit(1))));
    let _ = TypedPattern::Wild;
}

#[test]
fn local_partial_region_matches_the_pinned_program_split() {
    let src = include_str!("../cases/run/local_mono_combined.pr");
    let (typed, env, ctors, grades) = typed_from_program(src);
    let flags = DynFlags::default();
    let prepared = prepare(typed, &env, &ctors, &flags, &grades).expect("typed preparation");
    let effects = EffectPlan::analyze(&prepared.fns);
    let (region, entries) =
        analysis::local_region(&prepared.fns, &effects).expect("clean local region");
    assert!(region.contains(&sym("logged")));
    assert!(region.contains(&sym("run_all")));
    assert!(!region.contains(&sym("weight")));
    assert!(!region.contains(&sym("main")));
    assert_eq!(entries, BTreeSet::from([sym("logged")]));
}

#[test]
fn local_partial_rejects_a_closure_hidden_behind_boundary_variables() {
    let out = assert_program_lowering(
        "effect Log
  log(Int) : Int

fn weight(x) = x * 3

fn invoke(f) = f()
fn make() = \\() -> 7

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f())

fn logged(f) =
  let fs = [\\() -> log(weight(1)), \\() -> log(weight(2)), \\() -> log(weight(3))]
  let n =
    handle run_all(fs, 0) with
      log(value) resume k => k(value)
      return result => result
  n + invoke(f)

fn square(n) = n * n

fn main() =
  let stream = srange(1, 100).smap(square).ssum()
  let f = make()
  stream + logged(f)
",
    );
    assert_eq!(out.strategy, EffectStrategy::WholeProgramFreeMonad);
}

fn dynamic_application_program(value: &str, consumer: &str) -> String {
    format!(
        "effect Log
  log(Int) : Int

effect Ask
  ask() : Int

fn identity(x) = x
fn invoke(f) = f()
fn make_through(m) = m()

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f())

fn logged(value) =
  let fs = [\\() -> log(1), \\() -> log(2)]
  let n =
    handle run_all(fs, 0) with
      log(item) resume k => k(item)
      return result => result
  n + {consumer}(value)

fn request() : Int ! {{Ask}} = ask()

fn answered() =
  handle request() with
    ask() resume k => k(40)
    return result => result

fn main() =
  let value = {value}
  logged(value) + answered()
"
    )
}

#[test]
fn local_partial_rejects_a_closure_returned_by_dynamic_application() {
    let source = dynamic_application_program("make_through(\\() -> \\() -> 7)", "invoke");
    let out = assert_program_lowering(&source);
    assert_eq!(out.strategy, EffectStrategy::WholeProgramFreeMonad);
}

#[test]
fn scalar_dynamic_application_preserves_the_local_split() {
    let source = dynamic_application_program("make_through(\\() -> 7)", "identity");
    let out = assert_program_lowering(&source);
    assert_eq!(out.strategy, EffectStrategy::LocalPartial);
}

#[test]
fn applying_the_returned_closure_recovers_its_scalar_result() {
    let source = dynamic_application_program("invoke(make_through(\\() -> \\() -> 7))", "identity");
    let out = assert_program_lowering(&source);
    assert_eq!(out.strategy, EffectStrategy::LocalPartial);
}

#[test]
fn local_partial_rejects_a_closure_returned_through_resume() {
    let source = "effect Log
  log(Int) : Int

effect AskFn
  ask_fn() : (Unit) -> Int

fn invoke(f) = f(())

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f(()))

fn logged(value) =
  let fs = [\\(_u) -> log(1), \\(_u) -> log(2)]
  let n =
    handle run_all(fs, 0) with
      log(item) resume k => k(item)
      return result => result
  n + invoke(value)

fn request() = ask_fn()

fn answered() =
  handle request() with
    ask_fn() resume k => k(\\(_u) -> 40)
    return result => result

fn main() = logged(answered())
";
    let out = assert_program_lowering(source);
    assert_eq!(out.strategy, EffectStrategy::WholeProgramFreeMonad);
}

#[test]
fn state_backed_local_partial_routes_and_is_exact() {
    let src = include_str!("../cases/run/local_mono_combined.pr");
    let out = assert_program_lowering(src);
    assert_eq!(out.strategy, EffectStrategy::LocalPartial);
}

#[test]
fn local_partial_with_an_evidence_rest_routes_and_verifies() {
    let src = r"effect Log
  log(Int) : Int

effect Ask
  ask() : Int

fn run_all(fs, acc) =
  match fs of
    Nil => acc
    Cons(f, rest) => run_all(rest, acc + f())

fn logged() =
  let fs = [\() -> log(1), \() -> log(2)]
  handle run_all(fs, 0) with
    log(n) resume k => k(n)
    return r => r

fn request() : Int ! {Ask} = ask()

fn answered() =
  handle request() with
    ask() resume k => k(40)
    return r => r

fn main() = println(logged() + answered())
";
    let (typed, env, ctors, grades) = typed_from_program(src);
    let out = assert_typed_lowering(typed, &env, &ctors, &DynFlags::default(), &grades);
    assert_eq!(out.strategy, EffectStrategy::LocalPartial);
    assert_eq!(audit_typed_core(&out.core, &out.env), Ok(()));
}

#[test]
fn local_partial_composes_fused_rest_and_monadic_region_exactly() {
    let src = include_str!("../cases/run/local_mono_combined.pr");
    let (combined, lowered_env, region, entries) = local_partial_composition(src);
    assert!(region.contains(&sym("logged")));
    assert!(region.contains(&sym("run_all")));
    assert_eq!(entries, BTreeSet::from([sym("logged")]));
    let eop_ids = eop_operation_ids(combined.functions(), &region);
    assert!(!eop_ids.is_empty(), "the escaping region emits EOp values");
    assert!(
        eop_ids.iter().all(|id| *id == 0),
        "the alphabetically first alog operation keeps global id 0"
    );
    let srange_go = combined
        .functions()
        .iter()
        .find(|function| function.name().as_str() == "srange_go")
        .expect("the fused State producer survives");
    let state_suffix: Vec<Sym> = srange_go
        .params()
        .iter()
        .rev()
        .take(2)
        .map(TypedBinder::name)
        .collect();
    assert_eq!(
        state_suffix,
        [
            Sym::from(prism_syntax::names::STATE_ACC),
            Sym::from(prism_syntax::names::ev(1))
        ],
        "State evidence remains globally numbered and precedes the accumulator"
    );
    assert_eq!(
        srange_go.sig().quantifiers().last(),
        Some(&CoreQuantifier::Row(Sym::from(
            prism_syntax::names::evidence_row(&[1])
        ))),
        "the State producer's evidence row keeps the same global hole"
    );
    assert_eq!(audit_typed_core(&combined, &lowered_env), Ok(()));
    prism::core::residual_effects(&combined.erase()).expect("no raw effects survive");
}

#[test]
fn local_partial_retags_direct_and_tuple_carried_closures_exactly() {
    let src = r"effect Log
  log(Int) : Int

fn weight(x) = x * 3

fn apply_one(f) = f()

fn run_pair(pair, acc) =
  match pair of
    (f, g) => acc + apply_one(f) + apply_one(g)

fn logged() =
  let pair = (\() -> log(weight(1)), \() -> log(weight(2)))
  handle run_pair(pair, 0) with
    log(n) resume k => k(n)
    return r => r

fn square(n) = n * n

fn main() =
  println(weight(srange(1, 100).smap(square).ssum()))
  println(logged())
";
    let (combined, lowered_env, region, entries) = local_partial_composition(src);
    assert!(region.contains(&sym("apply_one")));
    assert!(region.contains(&sym("run_pair")));
    assert!(region.contains(&sym("logged")));
    assert_eq!(entries, BTreeSet::from([sym("logged")]));
    assert_eq!(audit_typed_core(&combined, &lowered_env), Ok(()));
    prism::core::residual_effects(&combined.erase()).expect("no raw effects survive");
}

#[test]
fn local_partial_region_retains_its_direct_io_row_exactly() {
    let src = include_str!("../cases/run/local_mono_combined.pr")
        .replace("fn logged() =\n", "fn logged() =\n  println(\"inside\")\n");
    let (combined, lowered_env, region, entries) = local_partial_composition(&src);
    assert!(region.contains(&sym("logged")));
    assert_eq!(entries, BTreeSet::from([sym("logged")]));
    let logged = combined
        .functions()
        .iter()
        .find(|function| function.name().as_str() == "logged")
        .expect("the LocalPartial entry survives");
    let ambient = Sym::from(prism_syntax::names::FREE_MONAD_ROW);
    assert_eq!(
        logged.sig().quantifiers().last(),
        Some(&CoreQuantifier::Row(ambient))
    );
    assert!(logged
        .sig()
        .body()
        .effects()
        .label_names()
        .contains(&Sym::from(prism_syntax::names::IO_EFFECT)));
    assert_eq!(audit_typed_core(&combined, &lowered_env), Ok(()));
    prism::core::residual_effects(&combined.erase()).expect("no raw effects survive");
}

fn local_partial_composition(
    src: &str,
) -> (
    TypedCore<EffectLowered>,
    VerifyEnv,
    BTreeSet<Sym>,
    BTreeSet<Sym>,
) {
    let (typed, env, ctors, grades) = typed_from_program(src);
    let flags = DynFlags::default();
    let prepared = prepare(typed, &env, &ctors, &flags, &grades).expect("typed preparation");
    let effects = EffectPlan::analyze(&prepared.fns);
    let (latent, flow) = (effects.latent(), effects.flow());
    let (region, entries) =
        analysis::local_region(&prepared.fns, &effects).expect("clean local region");
    let rest: Vec<TypedCoreFn> = prepared
        .fns
        .iter()
        .filter(|function| !region.contains(&function.name()))
        .cloned()
        .collect();
    let ops = operation_ids(&prepared.fns).expect("operation ids");
    let mut fresh = Fresh::new();
    assert!(
        evidence::try_lower_ev(
            &rest,
            latent,
            flow,
            &ops,
            &prepared.env,
            &DriftLog::new(true),
            &mut fresh,
        )
        .is_none(),
        "the fused rest takes the State rung"
    );
    let state_analysis = state::StateAnalysis::new(&ops, latent, flow, &prepared.env);
    let state_plan = state::fold_uniform(&rest, &state_analysis).expect("state rest plan");
    assert!(state::threads(&state_plan, &rest, &state_analysis));
    let lowered = state::thread_program(
        &rest,
        &state_plan,
        &state_analysis,
        &DriftLog::new(true),
        &mut fresh,
    )
    .expect("fused rest threads");
    let artifacts = assemble_local_partial(
        &prepared.fns,
        lowered,
        &prepared.env,
        &prepared.ctors,
        &LoweringAnalysis {
            ops: &ops,
            plan: &effects,
        },
        &LocalSplit {
            region: &region,
            entries: &entries,
        },
        &mut fresh,
    )
    .expect("LocalPartial assembly is total after planning")
    .expect("the LocalPartial whole-style boundary is sound");
    let combined = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(artifacts.fns),
        &artifacts.env,
    )
    .expect("LocalPartial assembly must mint effect-lowered authority");
    (combined, artifacts.env, region, entries)
}

fn typed_local_decline_digests(point: LocalDeclinePoint) -> (String, String) {
    let src = include_str!("../cases/run/local_mono_combined.pr");
    let flags = DynFlags::default();

    let (typed, env, ctors, grades) = typed_from_program(src);
    let probed = with_local_decline(point, || {
        lower_effects(typed, &env, &ctors, &flags, &grades)
            .expect("the typed late decline must fall through")
    });
    assert_eq!(probed.strategy, EffectStrategy::WholeProgramFreeMonad);

    let (typed, env, ctors, grades) = typed_from_program(src);
    let prepared =
        prepare(typed, &env, &ctors, &flags, &grades).expect("typed preparation succeeds");
    let ops = operation_ids(&prepared.fns).expect("operation ids");
    let effects = EffectPlan::analyze(&prepared.fns);
    let analysis = LoweringAnalysis {
        ops: &ops,
        plan: &effects,
    };
    let mut fresh = Fresh::new();
    let Decision::Lowered(clean) = monadic_fallback(
        &prepared.fns,
        &prepared.env,
        &prepared.ctors,
        &flags,
        &analysis,
        &mut fresh,
    )
    .expect("clean typed fallback lowers");
    let clean = *clean;
    assert_eq!(clean.strategy, EffectStrategy::WholeProgramFreeMonad);
    assert_eq!(probed.ctors, clean.ctors);
    assert_eq!(probed.warning, clean.warning);

    for lowering in [&probed, &clean] {
        assert_eq!(audit_typed_core(&lowering.core, &lowering.env), Ok(()));
        prism::core::residual_effects(&lowering.core.clone().erase())
            .expect("typed fallback leaves no raw effects");
        assert!(lowering
            .core
            .functions()
            .iter()
            .any(|function| function.name().as_str() == "prism_drive"));
        assert!(functions_use_constructor(
            lowering.core.functions(),
            "EBounce"
        ));
        assert!(lowering.ctors.contains_key("EBounce"));
    }

    let probed = blake3::hash(prism::core::pp_core(&probed.core.erase()).as_bytes())
        .to_hex()
        .to_string();
    let clean = blake3::hash(prism::core::pp_core(&clean.core.erase()).as_bytes())
        .to_hex()
        .to_string();
    assert_ne!(
        probed, clean,
        "a late LocalPartial decline must preserve names consumed by its attempt"
    );
    (probed, clean)
}

// These pin a blake3 of the `pp_core` dump, which prints raw fresh ids. The
// digests depend on both the program and process-global `Sym` supply.
// What the tests actually guard (probed != clean) is intact; only the concrete
// hex is regenerated when the supply moves. Canonical (`core-hash`) output is
// unaffected, which `tests/determinism.rs` proves.
#[test]
fn local_partial_rest_fusion_decline_preserves_the_typed_name_supply() {
    let (probed, clean) = typed_local_decline_digests(LocalDeclinePoint::AfterRestFusion);
    assert_eq!(
        probed,
        "9be4e15036553dcb820daac96e29cd87c194eaa84097f20871d4a92420126a55"
    );
    assert_eq!(
        clean,
        "a9f365f86b080fb3b5a665f5837a2860a77128cb8fdbb4cf0c8950f404e5d3c9"
    );
}

#[test]
fn local_partial_boundary_decline_preserves_the_typed_name_supply() {
    let (probed, clean) = typed_local_decline_digests(LocalDeclinePoint::AfterBoundaryAssembly);
    assert_eq!(
        probed,
        "b248766afb51b84b77d8326dc9ab3cb2c7a674341b45173af8f85f0843a8638b"
    );
    assert_eq!(
        clean,
        "a9f365f86b080fb3b5a665f5837a2860a77128cb8fdbb4cf0c8950f404e5d3c9"
    );
}
