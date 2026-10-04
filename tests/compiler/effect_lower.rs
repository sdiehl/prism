// Effect-lowering strategy and boundary tests: relocated from the
// `effect_lower` module when the middle end moved to `prism-core`, because
// they exercise the full front end (resolve, check, elaborate) that lives
// above that crate.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::{panic, thread};

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
    LocalPartial, Pure, SelectiveFreeMonad, StateFusion, WholeProgramFreeMonad,
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

const MEBIBYTE: usize = 1024 * 1024;
const ORDINARY_TEST_STACK: usize = 2 * MEBIBYTE;

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

// The cascade with the consolidated state route off. The fixtures below pin
// the rung a program reaches when the state route is not offered the whole
// program first; with the route on, every one of them is threaded state and
// the rung they are written to exercise is never asked.
fn cascade_flags() -> DynFlags {
    DynFlags {
        consolidate: false,
        ..DynFlags::default()
    }
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
    assert_typed_lowering(input, env, ctors, &cascade_flags(), &OpGrades::new())
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
    if let Err(violations) = audit_typed_core(out.core(), out.env()) {
        panic!("lowered typed Core is invalid: {violations:#?}");
    }
    prism::core::residual_effects(&out.core().clone().erase())
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
    assert_eq!(out.strategy(), EffectStrategy::Pure);
    let names: Vec<&str> = out
        .core()
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
    assert_eq!(out.core().functions().len(), 1);
    assert_eq!(out.strategy(), EffectStrategy::Pure);
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
    assert_eq!(out.strategy(), EffectStrategy::SelectiveFreeMonad);
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
            name: "reader",
            source: include_str!("../../examples/eff_reader.pr"),
            expected: [
                StateFusion,
                StateFusion,
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
                            ..cascade_flags()
                        };
                        let out =
                            assert_typed_lowering(typed.clone(), &env, &ctors, &flags, &grades);
                        assert_eq!(
                            *rung.get_or_insert_with(|| out.strategy()),
                            out.strategy(),
                            "{} at {}: the auxiliary flags must not move the rung",
                            fixture.name,
                            effect_tier.label()
                        );
                        if fixture.name == "local" {
                            assert!(
                                out.warning().is_some(),
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
                                && out.strategy() == EffectStrategy::SelectiveFreeMonad;
                            assert_eq!(
                                functions_use_constructor(out.core().functions(), "EResume"),
                                native_driver,
                                "the native-effects cell must exercise the native driver"
                            );
                            assert_eq!(out.constructors().contains_key("EResume"), native_driver);
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
        ..cascade_flags()
    };
    let compiled = typed_from_source(
        "effect Ask\n  ask() : Int\n\nfn main() =\n  let answer = ask()\n  println(answer)\n",
    );
    let (typed, env, ctors, grades) = compiled;
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), EffectStrategy::SelectiveFreeMonad);
}

#[test]
fn an_open_callback_row_coalesces_into_the_monadic_ambient() {
    let flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        ..cascade_flags()
    };
    let (typed, env, ctors, grades) = typed_from_source(
            "effect Ask\n  ask() : Int\n\nfn apply(f : (Int) -> Int ! {| e}, x : Int) = f(x)\n\nfn use(f : (Int) -> Int ! {IO}) : Int ! {Ask, IO} =\n  let answer = ask()\n  apply(f, answer)\n\nfn main() = use(\\(n) -> let _ = println(n) in n)\n",
        );
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), EffectStrategy::SelectiveFreeMonad);
    let use_fn = out
        .core()
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
    let ctors = checked.defs.ctors.clone();
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
    let flags = cascade_flags();
    let out = lower_effects(typed, &env, &ctors, &flags, &grades).expect("typed lowering succeeds");
    if let Err(violations) = audit_typed_core(out.core(), out.env()) {
        panic!("lowered typed Core is invalid: {violations:#?}");
    }
    prism::core::residual_effects(&out.core().clone().erase())
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
    assert_eq!(out.strategy(), EffectStrategy::Pure);
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
    assert_eq!(out.strategy(), EffectStrategy::Pure);
}

// A guard `return` with no loop: the return handler erases to `Step`
// threading and a seed unwrap.
#[test]
fn guard_return_erases_to_step_threading() {
    let out = assert_source_lowering(
            "fn classify(n : Int) : Int =\n  if n < 0 then\n    return 0 - 1\n  1\n\nfn main() : Int = classify(0 - 8)\n",
        );
    assert_eq!(out.strategy(), EffectStrategy::Pure);
}

// A return inside a match arm threads through the arm.
#[test]
fn return_in_match_arm_erases() {
    let out = assert_source_lowering(
            "fn describe(n : Int) : Int =\n  match n of\n    0 => return 100\n    _ => n * 2\n\nfn main() : Int = describe(0)\n",
        );
    assert_eq!(out.strategy(), EffectStrategy::Pure);
}

// A `while` loop with a `break`: the loop erases to a generated
// tail-recursive `{n}@loopdrv` whose parameters are the captured cells.
#[test]
fn break_loop_erases_to_a_driver() {
    let out = assert_program_lowering(
            "fn count_to(n : Int) : Int =\n  var i := 0\n  while true do\n    if i >= n then\n      break\n    i := i + 1\n  i\n\nfn main() : Int = count_to(5)\n",
        );
    assert_eq!(out.strategy(), EffectStrategy::Pure);
    assert!(
        out.core()
            .functions()
            .iter()
            .any(|f| f.name().as_str().ends_with("@loopdrv")),
        "a driver is generated: {:?}",
        out.core()
            .functions()
            .iter()
            .map(|f| f.name().as_str())
            .collect::<Vec<_>>()
    );
}

// A tail-resumptive reader: the clause answers its operation and resumes in
// tail position, so no continuation is ever reified and the consolidated state
// route takes the whole program.
#[test]
fn the_default_route_is_the_consolidated_state_route() {
    let (typed, env, ctors, grades) = typed_from_program(
        "effect Ask\n  ask() : Int\n\nfn reader() : Int ! {Ask} = ask() + 1\n\nfn main() : Int =\n  handle reader() with {\n    ask() resume k => k(41),\n    return x => x\n  }\n",
    );
    let out = assert_typed_lowering(typed, &env, &ctors, &DynFlags::default(), &grades);
    assert_eq!(out.strategy(), EffectStrategy::StateFusion);
}

// The signature prepass replaces `run`'s source residual row with a fresh
// ambient row. An unchanged polymorphic call retains that row in its explicit
// Core instantiation, both inside a handler clause and after the handle, so
// the substitution has to cover the entire typed body before the threading
// rewrite. Both programs are lowered at the default position and with the
// state rung forced, and both results must independently verify.
#[test]
fn residual_rows_are_rewritten_through_the_whole_body() {
    let fixtures = [
        include_str!("../cases/run/evidence_residual_row_clause.pr"),
        include_str!("../cases/run/evidence_residual_row_after_handle.pr"),
    ];
    for src in fixtures {
        let (typed, env, ctors, grades) = typed_from_program(src);
        let default =
            assert_typed_lowering(typed.clone(), &env, &ctors, &DynFlags::default(), &grades);
        assert_eq!(default.strategy(), EffectStrategy::StateFusion);

        let state_flags = DynFlags {
            effect_tier: EffectTier::StateFusion,
            ..cascade_flags()
        };
        let state = assert_typed_lowering(typed, &env, &ctors, &state_flags, &grades);
        assert_eq!(state.strategy(), EffectStrategy::StateFusion);
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
    let result = thread::Builder::new()
        .name("effect-lowering-normal-stack".into())
        .stack_size(ORDINARY_TEST_STACK)
        .spawn(assert_hidden_callbacks_route_whole)
        .expect("spawning ordinary-stack lowering probe")
        .join();
    if let Err(payload) = result {
        panic::resume_unwind(payload);
    }
}

fn assert_hidden_callbacks_route_whole() {
    let src = include_str!("../cases/run/row_widen_named_effect_list.pr");
    for effect_tier in [EffectTier::Auto, EffectTier::StateFusion] {
        let (typed, env, ctors, grades) = typed_from_program(src);
        let flags = DynFlags {
            effect_tier,
            ..cascade_flags()
        };
        let lowered = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
        assert_eq!(lowered.strategy(), EffectStrategy::WholeProgramFreeMonad);
    }
}

// A stream producer returns an effectful thunk rather than performing in
// the producer call itself. The signature plan must widen that returned
// thunk from `flow.ret`, then carry the new witness through map/filter
// calls and their handler clauses. Otherwise the eventual force site adds
// an ambient row to the stale monomorphic thunk and the entire pipeline
// falls onto the allocating whole-program free monad.
#[test]
fn returned_stream_thunks_thread_by_value() {
    let (typed, env, ctors, grades) = typed_from_program(include_str!(
        "../../examples/fixtures/compiler/stream_fuse.pr"
    ));
    let out = assert_typed_lowering(typed, &env, &ctors, &DynFlags::default(), &grades);
    assert_eq!(out.strategy(), EffectStrategy::StateFusion);
}

// A whole arena program through the real cascade, and the first higher-order
// handler program to lower exactly. Preparation rewrites the constructors
// `build` and `scratch` allocate into `alloc`/`init_at` and re-verifies; the
// threading then carries the `Alloc` clause `with_arena` installs down to
// them, including through `body`, the thunk parameter `with_arena` forces.
//
// That last step is what this pins. `body : () -> a ! {Alloc}` is a rank-2
// position: its ambient row is bound inside the parameter's own type, and the
// caller's thunk and the callee's declared parameter are minted by different
// passes that share no counter, so they agree only because the row is named
// by the operations it carries rather than by a counter.
#[test]
fn arena_program_lowers_exactly() {
    let (typed, env, ctors, grades) = typed_from_program("import Arena (..)\n\nfn build(n : Int, acc : List(Int)) : List(Int) =\n  if n == 0 then\n    acc\n  else\n    build(n - 1, Cons(n, acc))\n\nfn total(xs : List(Int)) : Int =\n  match xs of\n    Nil => 0\n    Cons(h, t) => h + total(t)\n\nfn scratch() : Int = total(build(3, Nil))\n\nfn main() : Int = with_arena(scratch)\n");
    let out = assert_typed_lowering(typed, &env, &ctors, &DynFlags::default(), &grades);
    assert_eq!(out.strategy(), EffectStrategy::StateFusion);
}

#[test]
fn arena_program_forced_to_the_free_monad_lowers_exactly() {
    let flags = DynFlags {
        effect_tier: EffectTier::WholeProgramFreeMonad,
        ..cascade_flags()
    };
    let (typed, env, ctors, grades) = typed_from_program(include_str!("../../examples/arena.pr"));
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), EffectStrategy::WholeProgramFreeMonad);
    assert!(
        out.core()
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
        out.strategy(),
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
    let flags = cascade_flags();
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
        let flags = cascade_flags();
        let threaded = lower_effects(typed, &env, &ctors, &flags, &grades)
            .unwrap_or_else(|e| panic!("{path}: the typed production rung fails: {e:?}"));
        assert_eq!(threaded.strategy(), EffectStrategy::StateFusion);
        assert_eq!(
            audit_typed_core(threaded.core(), threaded.env()),
            Ok(()),
            "{path}: typed State output must verify"
        );
        prism::core::residual_effects(&threaded.core().clone().erase())
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
        let flags = cascade_flags();
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
        let (threaded, env2) = threaded_state_typed(typed, &env, &ctors, &cascade_flags(), &grades)
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
    let flags = cascade_flags();
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
        ..cascade_flags()
    };
    let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), EffectStrategy::SelectiveFreeMonad);
    let prepared = prepare(source, &env, &ctors, &flags, &grades).expect("typed preparation");
    let ops = operation_ids(prepared.functions()).expect("operation ids");
    let effects = EffectPlan::analyze(prepared.functions());
    let latent = effects.latent();
    let plan = analysis::plan(prepared.functions(), &effects, false);
    assert_eq!(plan.scope, analysis::MonadicScope::Selective);

    let mut fresh = Fresh::new();
    let mut lowered = monadic::lower_selective(
        prepared.functions(),
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
    let mut lowered_env = prepared.env().clone();
    abi::insert(&mut lowered_env);
    let typed = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(lowered),
        &lowered_env,
    )
    .expect("native function-answer lowering must mint effect-lowered authority");
    assert_eq!(typed.erase(), out.core().clone().erase());

    let off_flags = DynFlags {
        effect_tier: EffectTier::FreeMonad,
        native_effects: false,
        quiet: true,
        ..cascade_flags()
    };
    let off_source = typed_from_program(src).0;
    let off_out = assert_typed_lowering(off_source, &env, &ctors, &off_flags, &grades);
    assert_eq!(off_out.strategy(), EffectStrategy::SelectiveFreeMonad);
    assert_ne!(
        out.core().clone().erase(),
        off_out.core().clone().erase(),
        "the native-effects flag must exercise distinct production lowerings"
    );
    let mut off_fresh = Fresh::new();
    let mut off_functions = monadic::lower_selective(
        prepared.functions(),
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
    let mut off_env = prepared.env().clone();
    abi::insert(&mut off_env);
    let off = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(off_functions),
        &off_env,
    )
    .expect("non-native fallback must mint effect-lowered authority");
    assert_eq!(off.erase(), off_out.core().clone().erase());
}

#[test]
fn whole_program_trampoline_is_deterministic_and_verifies() {
    let src = "effect Ask\n  ask() : Int\n\nfn make() = \\() -> let answer = ask() in let _ = println(answer) in answer\n\nfn main() =\n  let unused = make()\n  0\n";
    let (source, env, ctors, grades) = typed_from_source(src);
    let flags = DynFlags {
        effect_tier: EffectTier::WholeProgramFreeMonad,
        quiet: true,
        ..cascade_flags()
    };
    let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), EffectStrategy::WholeProgramFreeMonad);
    assert!(out
        .core()
        .functions()
        .iter()
        .any(|function| function.name().as_str() == "prism_drive"));
    assert!(functions_use_constructor(out.core().functions(), "EBounce"));
    assert!(out.constructors().contains_key("EBounce"));

    let off_flags = DynFlags {
        trampoline: false,
        ..flags.clone()
    };
    let off = assert_typed_lowering(source.clone(), &env, &ctors, &off_flags, &grades);
    assert_eq!(off.strategy(), EffectStrategy::WholeProgramFreeMonad);
    assert!(!off
        .core()
        .functions()
        .iter()
        .any(|function| function.name().as_str() == "prism_drive"));
    assert!(!functions_use_constructor(
        off.core().functions(),
        "EBounce"
    ));
    assert!(!off.constructors().contains_key("EBounce"));

    let prepared = prepare(source, &env, &ctors, &flags, &grades).expect("typed preparation");
    let ops = operation_ids(prepared.functions()).expect("operation ids");
    let residual = residual::plan(prepared.functions(), &ops, prepared.env())
        .expect("residual rows are declaration-owned");
    let mut fresh = Fresh::new();
    let mut lowered = monadic::lower_whole(prepared.functions(), &ops, &mut fresh, &residual)
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

    let mut lowered_env = prepared.env().clone();
    abi::insert(&mut lowered_env);
    let typed = verify_typed_core(
        UncheckedTypedCore::<EffectLowered>::new(lowered),
        &lowered_env,
    )
    .expect("trampoline lowering must mint effect-lowered authority");
    assert_eq!(typed.erase(), out.core().clone().erase());

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
    assert_eq!(selective.strategy(), EffectStrategy::SelectiveFreeMonad);
    assert!(!selective
        .core()
        .functions()
        .iter()
        .any(|function| function.name().as_str() == "prism_drive"));
    assert!(!functions_use_constructor(
        selective.core().functions(),
        "EBounce"
    ));
    assert!(!selective.constructors().contains_key("EBounce"));
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
        ..cascade_flags()
    };
    let out = assert_typed_lowering(source, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), EffectStrategy::WholeProgramFreeMonad);
    let ambient = Sym::from(prism_syntax::names::FREE_MONAD_ROW);
    let io = EffRow::canonical([Label::bare("IO")], EffRow::Var(ambient));
    let make = out
        .core()
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
    let flags = cascade_flags();
    let recognized = recognized_strategy(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(recognized, EffectStrategy::StateFusion);
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), recognized);
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
    let flags = cascade_flags();
    let recognized = recognized_strategy(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(recognized, EffectStrategy::StateFusion);
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), recognized);
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
    // With reification off, so the fold is the state gate's only answer.
    let flags = DynFlags {
        reify: false,
        ..cascade_flags()
    };
    let recognized = recognized_strategy(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("the typed cascade classifies")
        .expect("the typed cascade selects a strategy");
    assert_ne!(recognized, EffectStrategy::Pure, "var state must not erase");
    // The declining half of the state gate: a multishot clause is no kind of
    // fold, so without a reified continuation the typed gate must decline
    // rather than recognize a program that cannot thread an accumulator.
    assert_ne!(recognized, EffectStrategy::StateFusion);
    let out = assert_typed_lowering(typed, &env, &ctors, &flags, &grades);
    assert_eq!(out.strategy(), recognized);
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
    let flags = cascade_flags();
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
    let flags = cascade_flags();
    let prepared = prepare(typed, &env, &ctors, &flags, &grades).expect("typed preparation");
    let effects = EffectPlan::analyze(prepared.functions());
    let (region, entries) =
        analysis::local_region(prepared.functions(), &effects).expect("clean local region");
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
    assert_eq!(out.strategy(), EffectStrategy::WholeProgramFreeMonad);
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
    assert_eq!(out.strategy(), EffectStrategy::WholeProgramFreeMonad);
}

#[test]
fn scalar_dynamic_application_preserves_the_local_split() {
    let source = dynamic_application_program("make_through(\\() -> 7)", "identity");
    let out = assert_program_lowering(&source);
    assert_eq!(out.strategy(), EffectStrategy::LocalPartial);
}

#[test]
fn applying_the_returned_closure_recovers_its_scalar_result() {
    let source = dynamic_application_program("invoke(make_through(\\() -> \\() -> 7))", "identity");
    let out = assert_program_lowering(&source);
    assert_eq!(out.strategy(), EffectStrategy::LocalPartial);
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
    assert_eq!(out.strategy(), EffectStrategy::WholeProgramFreeMonad);
}

#[test]
fn state_backed_local_partial_routes_and_is_exact() {
    let src = include_str!("../cases/run/local_mono_combined.pr");
    let out = assert_program_lowering(src);
    assert_eq!(out.strategy(), EffectStrategy::LocalPartial);
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
    let out = assert_typed_lowering(typed, &env, &ctors, &cascade_flags(), &grades);
    assert_eq!(out.strategy(), EffectStrategy::LocalPartial);
    assert_eq!(audit_typed_core(out.core(), out.env()), Ok(()));
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
    let flags = cascade_flags();
    let prepared = prepare(typed, &env, &ctors, &flags, &grades).expect("typed preparation");
    let effects = EffectPlan::analyze(prepared.functions());
    let (latent, flow) = (effects.latent(), effects.flow());
    let (region, entries) =
        analysis::local_region(prepared.functions(), &effects).expect("clean local region");
    let rest: Vec<TypedCoreFn> = prepared
        .functions()
        .iter()
        .filter(|function| !region.contains(&function.name()))
        .cloned()
        .collect();
    let ops = operation_ids(prepared.functions()).expect("operation ids");
    let mut fresh = Fresh::new();
    let state_analysis = state::StateAnalysis::new(
        &ops,
        latent,
        flow,
        prepared.env(),
        BTreeSet::new(),
        false,
        false,
    );
    let state_plan = state::fold_uniform(&rest, &state_analysis).expect("state rest plan");
    assert!(state::threads(&state_plan, &rest, &state_analysis));
    let lowered = state::thread_program(
        &rest,
        &state_plan,
        &state_analysis,
        &DriftLog::new(true),
        &mut fresh,
    )
    .expect("fused rest threads")
    .functions;
    let artifacts = assemble_local_partial(
        prepared.functions(),
        lowered,
        prepared.env(),
        prepared.constructors(),
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
    let flags = cascade_flags();

    let (typed, env, ctors, grades) = typed_from_program(src);
    let probed = with_local_decline(point, || {
        lower_effects(typed, &env, &ctors, &flags, &grades)
            .expect("the typed late decline must fall through")
    });
    assert_eq!(probed.strategy(), EffectStrategy::WholeProgramFreeMonad);

    let (typed, env, ctors, grades) = typed_from_program(src);
    let prepared =
        prepare(typed, &env, &ctors, &flags, &grades).expect("typed preparation succeeds");
    let ops = operation_ids(prepared.functions()).expect("operation ids");
    let effects = EffectPlan::analyze(prepared.functions());
    let analysis = LoweringAnalysis {
        ops: &ops,
        plan: &effects,
    };
    let mut fresh = Fresh::new();
    let Decision::Lowered(clean) = monadic_fallback(
        prepared.functions(),
        prepared.env(),
        prepared.constructors(),
        &flags,
        &analysis,
        &mut fresh,
    )
    .expect("clean typed fallback lowers");
    let clean = *clean;
    assert_eq!(clean.strategy(), EffectStrategy::WholeProgramFreeMonad);
    assert_eq!(probed.constructors(), clean.constructors());
    assert_eq!(probed.warning(), clean.warning());

    for lowering in [&probed, &clean] {
        assert_eq!(audit_typed_core(lowering.core(), lowering.env()), Ok(()));
        prism::core::residual_effects(&lowering.core().clone().erase())
            .expect("typed fallback leaves no raw effects");
        assert!(lowering
            .core()
            .functions()
            .iter()
            .any(|function| function.name().as_str() == "prism_drive"));
        assert!(functions_use_constructor(
            lowering.core().functions(),
            "EBounce"
        ));
        assert!(lowering.constructors().contains_key("EBounce"));
    }

    let probed = blake3::hash(prism::core::pp_core(&probed.core().clone().erase()).as_bytes())
        .to_hex()
        .to_string();
    let clean = blake3::hash(prism::core::pp_core(&clean.core().clone().erase()).as_bytes())
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
        "e73bf8e4ab8d3360f86388b28c7dcbf75b45591b2c2131640319ed919e6e82c2"
    );
    assert_eq!(
        clean,
        "0a1157600d1b35eb81adf19c0b99b23baac38bb11868f9d4eecf7b5b74400979"
    );
}

#[test]
fn local_partial_boundary_decline_preserves_the_typed_name_supply() {
    let (probed, clean) = typed_local_decline_digests(LocalDeclinePoint::AfterBoundaryAssembly);
    assert_eq!(
        probed,
        "259565ef116161952c5fb87273740c407a1dbf783f397a1aa59c9190be1d498b"
    );
    assert_eq!(
        clean,
        "0a1157600d1b35eb81adf19c0b99b23baac38bb11868f9d4eecf7b5b74400979"
    );
}

// The state route with reified continuations: a clause that resumes twice
// answers with a cell instead of folding, and the program still reaches
// threaded state. With the knob off the same program falls to the free monad.
fn reify_flags() -> DynFlags {
    DynFlags {
        reify: true,
        quiet: true,
        ..DynFlags::default()
    }
}

fn assert_reified_landing(src: &str) -> TypedLowering {
    let (source, env, ctors, grades) = typed_from_program(src);
    let off = assert_typed_lowering(
        source.clone(),
        &env,
        &ctors,
        &DynFlags {
            reify: false,
            quiet: true,
            ..DynFlags::default()
        },
        &grades,
    );
    assert_ne!(
        off.strategy(),
        StateFusion,
        "the fixture must need a reified continuation"
    );
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_eq!(out.strategy(), StateFusion);
    out
}

#[test]
fn multishot_clause_reifies_on_the_state_route() {
    assert_reified_landing(
        "effect Peek\n  peek(Int) : Int\n\nfn ask() : Int ! {Peek} = peek(4) + peek(7)\n\nfn peeked() =\n  handle ask() with\n    peek(n) resume k => k(n) + k(n * 2)\n    return r => r\n\nfn main() = println(peeked())\n",
    );
}

#[test]
fn threaded_operation_beside_a_reified_one_lands() {
    assert_reified_landing(
        "effect Ask\n  ask() : Int\n\neffect Peek\n  peek(Int) : Int\n\nfn once() : Int ! {Ask} = ask() + 1\n\nfn twice() : Int ! {Peek} = peek(3) * 10\n\nfn main() =\n  let a =\n    handle once() with\n      ask() resume k => k(1)\n      return r => r\n  let b =\n    handle twice() with\n      peek(n) resume k => k(n) + k(n + 1)\n      return r => r\n  println(a + b)\n",
    );
}

#[test]
fn thunk_valued_performer_reifies_at_its_declared_type() {
    assert_reified_landing(
        "effect Peek\n  peek(Int) : Int\n\nfn run_thunks(fs, acc) =\n  match fs of\n    Nil => acc\n    Cons(f, rest) => run_thunks(rest, acc + f())\n\nfn peeked() =\n  let fs = [\\() -> peek(4), \\() -> peek(7)]\n  handle run_thunks(fs, 0) with\n    peek(n) resume k => k(n) + k(n * 2)\n    return r => r\n\nfn main() = println(peeked())\n",
    );
}

// A handler over a thunk parameter typed over a bare row variable, whose
// result mentions that variable: the parameter is read as cells because the
// flow says every thunk reaching it is rebuilt, and the driver is quantified
// as the function it is minted inside.
#[test]
fn row_polymorphic_handle_site_reifies_with_a_quantified_driver() {
    assert_reified_landing(
        "effect Gen\n  yield(Int) : Unit\n\ntype Step(e : Row) = Done | More(Int, () -> Step(e) ! {e})\n\nfn count(n) : Unit ! {Gen} =\n  if n > 0 then\n    yield(n)\n    count(n - 1)\n  else\n    ()\n\nfn to_stream(thunk : () -> a ! {| e}) : Step(e) =\n  handle thunk() with\n    yield(v) resume k => More(v, \\() -> k(()))\n    return r => Done\n\nfn total(s) =\n  match s of\n    Done => 0\n    More(x, k) => x + total(k())\n\nfn main() = println(total(to_stream(\\() -> count(4))))\n",
    );
}

// A `var` handler that runs under a multishot operation: the operation
// arrives in a thunk parameter, so the state handle is met inside cells and
// becomes a driver over cells of its own, forwarding the multishot operation
// outward. Each resumption then gets its own state, printing [1, 1].
#[test]
fn state_handle_nested_under_a_multishot_operation_reifies() {
    assert_reified_landing(
        "effect Amb\n  choose(Int) : Int\n\nfn worker(k) : Int =\n  var s := 0\n  k()\n  s := s + 1\n  s\n\nfn main() =\n  println(handle worker(\\() -> choose(2)) with {\n    choose(m) resume k => flatten(map(\\(i) -> k(i), range(0, m))),\n    return r => Cons(r, Nil)\n  })\n",
    );
}

// A scheduler host quantified over a row tail beyond the reified effect and
// `IO`: the island row is spelled under that tail, calls back into the host
// from cells subtract the labels the extension added and close the tail, and
// a command value whose row argument is a representation phantom passes to a
// consumer spelling the residual row.
#[test]
fn row_tailed_scheduler_host_reifies_over_a_phantom_row_carrier() {
    assert_reified_landing(
        "effect Async\n  yield() : Unit\n\ntype Cmd(a, e : Row) = Done(a) | Yielded(() -> Cmd(a, e) ! {e})\n\ntype Sched(a, e : Row) = Sched(List(() -> Cmd(a, e) ! {e}))\n\nfn step(t : () -> a ! {Async, IO | e}) : Cmd(a, {IO | e}) ! {IO | e} =\n  handle t() with\n    yield() resume k => Yielded(\\() -> k(()))\n    return r => Done(r)\n\nfn run_next(s : Sched(Int, {IO})) : Unit ! {IO} =\n  match s of\n    Sched(Nil) => ()\n    Sched(Cons(k, rest)) =>\n      match k() of\n        Done(r) =>\n          println(r)\n          run_next(Sched(rest))\n        Yielded(k2) => run_next(Sched(append(rest, [k2])))\n\nfn tick(name : String, n : Int) : Int ! {Async, IO} =\n  if n > 0 then\n    println(name)\n    yield()\n    tick(name, n - 1)\n  else\n    n\n\nfn main() =\n  run_next(Sched([\n      \\() -> step(\\() -> tick(\"a\", 2)),\n      \\() -> step(\\() -> tick(\"b\", 1)),\n    ]))\n",
    );
}

// A latent operation at the entry point wraps `main` in a fault handle, and
// that handle is promoted because its body reaches the reified `yield`: the
// whole of `main` becomes cells at its own site row, which carries the `IO`
// its prints perform while the island's row is empty. The scheduler's cells
// are read at the wider row through a representation conversion.
#[test]
fn entry_fault_handle_reads_island_cells_at_the_site_row() {
    assert_reified_landing("effect Async\n  yield() : Unit\n\ntype Cmd(a, e : Row) = Done(a) | Yielded(() -> Cmd(a, e) ! {e})\n\nfn step(t : () -> a ! {Async}) : Cmd(a, {}) =\n  handle t() with\n    yield() resume k => Yielded(\\() -> k(()))\n    return r => Done(r)\n\nfn run_all(ks : List(() -> Cmd(Int, {}))) : Int =\n  match ks of\n    Nil => 0\n    Cons(k, rest) =>\n      match k() of\n        Done(r) => r + run_all(rest)\n        Yielded(k2) => run_all(append(rest, [k2]))\n\nfn tick(n : Int) : Int ! {Async} =\n  if n > 0 then\n    yield()\n    n + tick(n - 1)\n  else\n    0\n\nfn main() =\n  let total = run_all([\\() -> step(\\() -> tick(2)), \\() -> step(\\() -> tick(1))])\n  println(total)\n  if total < 0 then fail()\n");
}

// Every capability operation is reified by the replay handlers, so no named
// function is a member of the island: the only performer is the thunk `main`
// hands the world handler, and its body performs real IO through `record`.
// A thunk literal handed to a cells position is a member without a name, and
// the island's row names what its body keeps.
#[test]
fn a_handed_thunk_literal_contributes_its_row_to_the_island() {
    assert_reified_landing("import Replay (..)\n\nfn main() =\n  let (r, t) = record(\\(_u) -> rng_rand() + env_argc())\n  let r2 = replay(t, \\(_u) -> rng_rand() + env_argc())\n  if r == r2 then\n    println(\"same\")\n  else\n    println(\"different\")\n");
}

// A forwarding wrapper around a reified body: its resuming arms re-perform the
// operation and its never-arm runs a cleanup before re-raising. The handle is
// promoted because its body reaches the reified `yield`, so how its arms agree
// is never asked of the threaded fold. The cleanup thunk is typed over the row
// variable the carrying body also spells, but the flow says nothing reified
// reaches it, so its force is direct code.
#[test]
fn a_forwarding_wrapper_with_a_never_arm_and_a_direct_cleanup_reifies() {
    assert_reified_landing("effect Async\n  yield() : Unit\n  never stop() : b\n\ntype Cmd(a, e : Row) = Done(a) | Stopped | Yielded(() -> Cmd(a, e) ! {e})\n\nfn step(t : () -> a ! {Async, IO}) : Cmd(a, {IO}) ! {IO} =\n  handle t() with\n    yield() resume k => Yielded(\\() -> k(()))\n    never stop() => Stopped\n    return r => Done(r)\n\nfn on_stop(cleanup : () -> Unit ! {| e}, body : () -> a ! {Async | e}) : a ! {Async | e} =\n  handle body() with\n    yield() resume k => k(yield())\n    never stop() =>\n      cleanup()\n      stop()\n    return r => r\n\nfn run_all(ks : List(() -> Cmd(Int, {IO}) ! {IO})) : Int ! {IO} =\n  match ks of\n    Nil => 0\n    Cons(k, rest) =>\n      match k() of\n        Done(r) => r + run_all(rest)\n        Stopped => run_all(rest)\n        Yielded(k2) => run_all(append(rest, [k2]))\n\nfn tick(n : Int) : Int ! {Async, IO} =\n  if n > 0 then\n    println(n)\n    yield()\n    n + tick(n - 1)\n  else\n    stop()\n\nfn main() =\n  let total = run_all([\\() -> step(\\() -> on_stop(\\() -> println(\"cleanup\"), \\() -> tick(2)))])\n  println(total)\n");
}

// A reified island resumes by applying its queue and re-entering its driver,
// and its cells compose through `ebind`: every hop is a call, so without the
// trampoline a long forwarding chain runs the stack out. The route requires
// the trampoline and refuses explicitly when the option is off, rather than
// lowering a program whose termination depends on its depth.
#[test]
fn a_reified_island_declines_without_the_trampoline() {
    let src = "effect Tick\n  tick() : Int\n\neffect Note\n  note() : Int\n\nfn spin(n : Int) : Int ! {Tick, Note} =\n  if n == 0 then\n    note()\n  else\n    tick()\n    spin(n - 1)\n\nfn forwarded(n : Int) : Int ! {Note} =\n  handle spin(n) with\n    tick() resume k => k(1)\n    return x => x\n\nfn main() =\n  let total =\n    handle forwarded(1000) with\n      note() resume k => k(7) + k(8)\n      return x => x\n  println(show(total))\n";
    let landed = assert_reified_landing(src);
    assert!(
        landed
            .core()
            .functions()
            .iter()
            .any(|f| f.name().as_str() == "prism_drive"),
        "the landed island is driven by the trampoline loop"
    );
    let (source, env, ctors, grades) = typed_from_program(src);
    let refused = assert_typed_lowering(
        source,
        &env,
        &ctors,
        &DynFlags {
            reify: true,
            trampoline: false,
            quiet: true,
            ..DynFlags::default()
        },
        &grades,
    );
    assert_ne!(refused.strategy(), StateFusion);
    assert_eq!(
        refused.state_decline(),
        Some("a reified island without the trampoline")
    );
}

// The reified set is keyed by operation, not by handler: a multishot handler
// of `peek` in one function makes every performer of `peek` cells code, and a
// tail-resumptive handler of the same operation over a direct loop elsewhere
// is promoted rather than folded. The loop's lowered signature answers a
// cell, which pins the boundary as measured, not as local.
#[test]
fn an_independent_multishot_handler_reifies_a_direct_loop_over_the_same_operation() {
    let landed = assert_reified_landing(
        "effect Peek\n  peek(Int) : Int\n\nfn ask() : Int ! {Peek} = peek(4) + peek(7)\n\nfn peeked() =\n  handle ask() with\n    peek(n) resume k => k(n) + k(n * 2)\n    return r => r\n\nfn count(n : Int, acc : Int) : Int ! {Peek} =\n  if n == 0 then acc else count(n - 1, acc + peek(n))\n\nfn counted() =\n  handle count(3, 0) with\n    peek(n) resume k => k(n + 1)\n    return r => r\n\nfn main() = println(peeked() + counted())\n",
    );
    let count = landed
        .core()
        .functions()
        .iter()
        .find(|f| f.name().as_str() == "count")
        .expect("the direct loop survives lowering under its own name");
    assert!(
        matches!(
            count.sig().body().result(),
            CoreType::Lowered(LoweredType::Eff(_))
        ),
        "the direct loop over a reified operation answers a cell: {:?}",
        count.sig().body().result()
    );
}

// A stream handler whose answer is typed over its own row quantifier, read by
// a consumer that is quantified the same way: the caller instantiates both
// quantifiers at the reified effect, so the thunks the driver's clauses build
// and the reads the consumer performs are cells on both sides, and the host
// that instantiates them reads the consumer's answer through a runner. The
// consumer being direct while the handler consumed the effect gave native
// output that disagreed with the interpreter (a cell read as a step tag).
#[test]
fn a_handler_answering_over_its_quantifier_and_its_consumer_are_members() {
    let out = assert_reified_landing(
        "effect Gen\n  yield(Int) : Unit\n\ntype Tree = Leaf(Int) | Node(Tree, Tree)\n\ntype Step(e : Row) = Done | More(Int, () -> Step(e) ! {e})\n\nfn leaves(t) : Unit ! {Gen} =\n  match t of\n    Leaf(n) => yield(n)\n    Node(l, r) =>\n      leaves(l)\n      leaves(r)\n\nfn to_stream(thunk : () -> a ! {| e}) : Step(e) =\n  handle thunk() with\n    yield(v) resume k => More(v, \\() -> k(()))\n    return r => Done\n\nfn same(s1, s2) =\n  match (s1, s2) of\n    (Done, Done) => true\n    (More(a, k1), More(b, k2)) => a == b && same(k1(), k2())\n    _ => false\n\nfn main() =\n  let t1 = Node(Leaf(1), Node(Leaf(2), Leaf(3)))\n  let t2 = Node(Node(Leaf(1), Leaf(2)), Leaf(3))\n  let t3 = Node(Leaf(1), Leaf(3))\n  println(same(to_stream(\\() -> leaves(t1)), to_stream(\\() -> leaves(t2))))\n  println(same(to_stream(\\() -> leaves(t1)), to_stream(\\() -> leaves(t3))))\n",
    );
    let answers_cells: BTreeMap<&str, bool> = out
        .core()
        .functions()
        .iter()
        .map(|f| {
            (
                f.name().as_str(),
                abi::answers_with_effect_cell(f.sig().body().result()),
            )
        })
        .collect();
    for member in ["leaves", "to_stream", "same"] {
        assert_eq!(
            answers_cells.get(member),
            Some(&true),
            "{member} answers cells"
        );
    }
    assert_eq!(
        answers_cells.get("main"),
        Some(&false),
        "the entry is read by the runtime"
    );
}

fn answers_cells_by_name(out: &TypedLowering) -> BTreeMap<&str, bool> {
    out.core()
        .functions()
        .iter()
        .map(|f| {
            (
                f.name().as_str(),
                abi::answers_with_effect_cell(f.sig().body().result()),
            )
        })
        .collect()
}

const STREAM_HOST: &str = "effect Gen\n  yield(Int) : Unit\n\ntype Step(e : Row) = Done | More(Int, () -> Step(e) ! {e})\n\nfn count(n) : Unit ! {Gen} =\n  if n > 0 then\n    yield(n)\n    count(n - 1)\n  else\n    ()\n\nfn to_stream(thunk : () -> a ! {| e}) : Step(e) =\n  handle thunk() with\n    yield(v) resume k => More(v, \\() -> k(()))\n    return r => Done\n\nfn total(s) =\n  match s of\n    Done => 0\n    More(x, k) => x + total(k())\n";

// A mutually recursive pair of direct functions with different arities,
// reached only from an unexecuted branch under a multishot handler: the pair
// answers plain values, so its tail calls are a native loop and not bounces,
// and the island lands. Seeding the trampoline's bounce set with every
// function declined this program as an island the trampoline refuses.
#[test]
fn a_direct_cycle_behind_an_unexecuted_multishot_branch_is_not_bounced() {
    let out = assert_reified_landing(
        "effect Peek\n  peek() : Int\n\nfn direct_a() : Int = direct_b(1)\n\nfn direct_b(n) : Int = direct_a()\n\nfn probe_it() : Int ! {Peek} =\n  if peek() == 0 then\n    direct_a()\n  else\n    7\n\nfn main() =\n  println(handle probe_it() with {\n    peek() resume k => k(1) + k(2),\n    return r => r\n  })\n",
    );
    let answers_cells = answers_cells_by_name(&out);
    assert_eq!(answers_cells.get("probe_it"), Some(&true));
    for direct in ["direct_a", "direct_b"] {
        assert_eq!(
            answers_cells.get(direct),
            Some(&false),
            "{direct} stays direct code"
        );
    }
}

// A closed-row forwarder: a handler declared over `{Gen, Peek}` that answers
// `yield` and lets `peek` pass to the multishot handler outside it. The
// forwarder is a member by its spelled label, with no row quantifier
// involved, and the outer driver resumes it twice.
#[test]
fn a_forwarder_over_a_closed_row_lands() {
    let out = assert_reified_landing(
        "effect Gen\n  yield(Int) : Unit\n\neffect Peek\n  peek() : Int\n\nfn work() : Int ! {Gen, Peek} =\n  yield(1)\n  yield(2)\n  peek()\n\nfn count_yields(body : () -> Int ! {Gen, Peek}) : Int ! {Peek} =\n  handle body() with\n    yield(v) resume k => k(()) + 1\n    return r => r\n\nfn main() =\n  println(handle count_yields(\\() -> work()) with {\n    peek() resume k => k(10) + k(20),\n    return r => r\n  })\n",
    );
    let answers_cells = answers_cells_by_name(&out);
    assert_eq!(answers_cells.get("work"), Some(&true));
    assert_eq!(answers_cells.get("count_yields"), Some(&true));
    assert_eq!(answers_cells.get("main"), Some(&false));
}

// A host quantified over the reified effect is instantiated once at the
// reified row and once at the empty row, in either order. Both
// instantiations of the host answer cells, and the pure one is read through a
// runner rather than folded.
#[test]
fn a_reifying_and_a_pure_instantiation_of_one_host_land_in_either_order() {
    for tail in [
        "fn main() =\n  println(total(to_stream(\\() -> count(3))))\n  println(total(to_stream(\\() -> ())))\n",
        "fn main() =\n  println(total(to_stream(\\() -> ())))\n  println(total(to_stream(\\() -> count(3))))\n",
    ] {
        let out = assert_reified_landing(&format!("{STREAM_HOST}\n{tail}"));
        let answers_cells = answers_cells_by_name(&out);
        assert_eq!(answers_cells.get("to_stream"), Some(&true));
        assert_eq!(answers_cells.get("total"), Some(&true));
        assert_eq!(answers_cells.get("main"), Some(&false));
    }
}

// The calling convention is recorded per named call. A host answering cells
// that is passed as a function value reaches the lowering as a lambda that
// calls the host by name at the reader's instantiation, so the edge the
// convention needs is there, and the reader is cloned at that row. The
// program lands, and the host is a member on both of its uses.
#[test]
fn a_cells_answering_host_passed_as_a_value_calls_it_by_name() {
    let out = assert_reified_landing(&format!(
        "{STREAM_HOST}\nfn apply(f, t) = f(t)\n\nfn main() =\n  println(total(to_stream(\\() -> count(3))))\n  println(total(apply(to_stream, \\() -> count(2))))\n"
    ));
    let answers_cells = answers_cells_by_name(&out);
    assert_eq!(answers_cells.get("to_stream"), Some(&true));
    assert_eq!(answers_cells.get("main"), Some(&false));
}

fn contains_bind_of(comp: &TypedComp, name: &str) -> bool {
    if matches!(comp.kind(), TypedCompKind::Bind(_, binder, _) if binder.name().as_str() == name) {
        return true;
    }
    let mut found = false;
    walk::each_subterm(comp, &mut |child| found |= contains_bind_of(child, name));
    found
}

// A parameter read as direct code, applied through a `let` alias that shares
// the driver's row quantifier with the cells. The alias is read by its type,
// not by the parameter's reading: giving the alias the parameter's reading
// made the record clauses of the replay corpus fail verification, because
// their resume thunks are bound to a name before they are applied and that
// name is the site the native corpus validated. The alias survives to the
// typed lowering, so the shape is exercised rather than folded away.
#[test]
fn a_direct_parameter_applied_through_an_alias_lands() {
    let out = assert_reified_landing(
        "effect Gen\n  yield(Int) : Unit\n\nfn count(n) : Unit ! {Gen} =\n  if n > 0 then\n    yield(n)\n    count(n - 1)\n  else\n    ()\n\nfn with_cleanup(body : () -> Unit ! {Gen | e}, cleanup : () -> Int ! {| e}) : Int ! {| e} =\n  let c = cleanup\n  handle body() with\n    yield(v) resume k => k(()) + k(()) + v\n    return r => c()\n\nfn main() = println(with_cleanup(\\() -> count(2), \\() -> 100))\n",
    );
    let with_cleanup = out
        .core()
        .functions()
        .iter()
        .find(|f| f.name().as_str() == "with_cleanup")
        .expect("the driver survives under its own name");
    assert!(
        contains_bind_of(with_cleanup.body(), "c"),
        "the alias of the direct parameter is still bound in the lowered driver"
    );
}

/// A landed driver whose parameters keep their declared thunk types over the
/// quantifier, read at each instantiation, and whose answer is cells.
fn assert_answers_cells(out: &TypedLowering, name: &str) {
    let f = out
        .core()
        .functions()
        .iter()
        .find(|f| f.name().as_str() == name)
        .expect("the driver survives under its own name");
    assert!(
        matches!(f.sig().body().result(), CoreType::Lowered(_)),
        "`{name}` answers cells, not the declared word"
    );
    for param in f.params() {
        assert!(
            matches!(param.ty(), CoreType::Thunk(_)),
            "`{name}` keeps its thunk parameters at their declared types"
        );
    }
}

// The alias fixture with a second reified effect instantiating the driver's
// quantifier from outside: `cleanup` is typed over `e`, carries nothing, and
// is built by its caller at a row naming `Tick`. The driver must read it at
// that row.
#[test]
fn an_alias_of_a_parameter_over_an_instantiated_quantifier_lands() {
    let out = assert_reified_landing(
        "effect Gen\n  yield(Int) : Unit\n\neffect Tick\n  tick() : Int\n\nfn down(n) : Unit ! {Gen} =\n  if n > 0 then\n    yield(n)\n    down(n - 1)\n  else\n    ()\n\nfn with_cleanup(body : () -> Unit ! {Gen | e}, cleanup : () -> Int ! {| e}) : Int ! {| e} =\n  let c = cleanup\n  handle body() with\n    yield(v) resume k => k(()) + k(()) + v\n    return r => c()\n\nfn main() =\n  let r =\n    handle with_cleanup(\\() -> down(tick()), \\() -> 100) with\n      tick() resume k => k(1) + k(2)\n      return r => r\n  println(r)\n",
    );
    assert_answers_cells(&out, "with_cleanup");
}

// The replay recorder: its one parameter over the quantifier is the thunk
// its handle drives, forced once, and its answer is not typed over the
// quantifier, so the handle consumes the operations it answers and the
// recorder's clauses stay direct, with the threaded evidence in the
// resumption's type out of cells code. Read from the tree so the pin follows
// the stdlib.
#[test]
fn the_replay_recorder_consumes_on_its_driven_quantifier() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src =
        fs::read_to_string(root.join("examples/record_replay.pr")).expect("the corpus program");
    let (source, env, ctors, grades) = typed_from_program(&src);
    assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_reified_landing(&src);
}

// A parameter typed over the driver's own quantifier, read after the handle
// that answers the reified effect. Its caller builds it at a row naming the
// effect, so the callee reads cells there even though its own handle has
// already answered them: subtracting the handled effect from the quantifier
// read `b` as direct code and returned a heap cell as the `Int`.
#[test]
fn a_parameter_read_past_a_driver_on_its_own_quantifier_lands() {
    let out = assert_reified_landing(
        "effect Tick\n  tick() : Int\n\nfn run_both(a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  let x =\n    handle a() with\n      tick() resume k => k(1) + k(2)\n      return r => r\n  x + b()\n\nfn main() =\n  println(run_both(\\() -> tick() * 100, \\() -> 5))\n",
    );
    assert_answers_cells(&out, "run_both");
}

// The same parameter read inside the handle's body, beside the one the
// clauses answer.
#[test]
fn a_parameter_read_beside_a_driver_on_its_own_quantifier_lands() {
    assert_reified_landing(
        "effect Tick\n  tick() : Int\n\nfn run_both(a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  handle a() + b() with\n    tick() resume k => k(1) + k(2)\n    return r => r\n\nfn main() =\n  println(run_both(\\() -> tick() * 100, \\() -> 5))\n",
    );
}

// The driver instantiated at two rows from one caller: the one naming the
// reified effect reads its parameters as cells, the empty one as direct code.
#[test]
fn a_driver_instantiated_at_two_rows_lands_at_each() {
    assert_reified_landing(
        "effect Tick\n  tick() : Int\n\nfn run_both(a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  let x =\n    handle a() with\n      tick() resume k => k(1) + k(2)\n      return r => r\n  x + b()\n\nfn main() =\n  println(run_both(\\() -> tick() * 100, \\() -> 5) + run_both(\\() -> 7, \\() -> 5))\n",
    );
}

// The parameter read on the branch the driver does not take.
#[test]
fn two_drivers_forcing_different_parameters_over_one_quantifier_land() {
    let src = r"
effect Tick
  tick() : Int

effect Tock
  tock() : Int

fn run_two(a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =
  let x =
    handle a() with
      tick() resume k => k(1) + k(2)
      return r => r
  let y =
    handle b() with
      tock() resume k => k(10)
      return r => r
  x + y

fn main() =
  let r =
    handle run_two(\() -> tick() * 100 + tock(), \() -> tock() + 1) with
      tock() resume k => k(3)
      return r => r
  println(r)
";
    let out = assert_reified_landing(src);
    assert_answers_cells(&out, "run_two");
}

#[test]
fn a_branch_reading_a_parameter_past_a_driver_lands() {
    assert_reified_landing(
        "effect Tick\n  tick() : Int\n\nfn run_either(c : Bool, a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  if c then\n    handle a() with\n      tick() resume k => k(1) + k(2)\n      return r => r\n  else\n    b()\n\nfn main() =\n  println(run_either(false, \\() -> tick() * 100, \\() -> 5) + run_either(true, \\() -> tick() * 100, \\() -> 5))\n",
    );
}

// A second effect the outer scope handles reaching the same parameter: the
// state route has no spelling for the threaded value and declines, and the
// program runs on the next rung.
#[test]
fn a_foreign_effect_beside_a_driver_declines_without_a_spelling() {
    for (src, reason) in [
        (
            "effect Tick\n  tick() : Int\n\neffect Peek\n  peek(Int) : Int\n\nfn run_both(a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  let x =\n    handle a() with\n      tick() resume k => k(1) + k(2)\n      return r => r\n  x + b()\n\nfn main() =\n  let total =\n    handle run_both(\\() -> tick() * 100, \\() -> peek(2)) with\n      peek(n) resume k => k(n) * 10\n      return r => r\n  println(total)\n",
            "`run_both`: a threaded value with no source spelling",
        ),
        (
            "effect Tick\n  tick() : Int\n\neffect Peek\n  peek(Int) : Int\n\nfn run_either(c : Bool, a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  if c then\n    handle a() with\n      tick() resume k => k(1) + k(2)\n      return r => r\n  else\n    b()\n\nfn main() =\n  let total =\n    handle run_either(false, \\() -> tick() * 100, \\() -> peek(2)) + run_either(true, \\() -> tick() * 100, \\() -> peek(2)) with\n      peek(n) resume k => k(n) * 10\n      return r => r\n  println(total)\n",
            "`run_either`: a threaded value with no source spelling",
        ),
    ] {
        let (source, env, ctors, grades) = typed_from_program(src);
        let refused = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
        assert_ne!(refused.strategy(), StateFusion);
        assert_eq!(refused.state_decline(), Some(reason));
    }
}

// Branches threaded at distinct open tails: one answers the reified effect
// on the quantifier, the other forwards a foreign one. The producer's own
// residual joins the receiver's row, so both branches run at one row and
// the single-resume driver threads as plain state.
#[test]
fn branches_threaded_at_distinct_tails_land() {
    let (source, env, ctors, grades) = typed_from_program(
        "effect Tick\n  tick() : Int\n\neffect Peek\n  peek(Int) : Int\n\nfn run_either(c : Bool, a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  if c then\n    handle a() with\n      tick() resume k => k(1)\n      return r => r\n  else\n    b()\n\nfn main() =\n  let total =\n    handle run_either(false, \\() -> tick() * 100, \\() -> peek(2)) + run_either(true, \\() -> tick() * 100, \\() -> peek(2)) with\n      peek(n) resume k => k(n) * 10\n      return r => r\n  println(total)\n",
    );
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_eq!(out.state_decline(), None);
    assert_eq!(out.strategy(), StateFusion);
}

// A foreign effect read past a single-resume driver on the driver's own
// quantifier: the handle's residual row keeps the quantifier and the scope
// it is threaded in runs at the receiver's row, which the residual joins.
#[test]
fn a_handle_at_a_row_its_scope_joins_lands() {
    let (source, env, ctors, grades) = typed_from_program(
        "effect Tick\n  tick() : Int\n\neffect Peek\n  peek(Int) : Int\n\nfn both(a : () -> Int ! {| e}, b : () -> Int ! {| e}) : Int ! {| e} =\n  let x =\n    handle a() with\n      tick() resume k => k(1)\n      return r => r\n  x + b()\n\nfn main() =\n  let total =\n    handle both(\\() -> tick() * 100, \\() -> peek(2)) with\n      peek(n) resume k => k(n) * 10\n      return r => r\n  println(total)\n",
    );
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_eq!(out.state_decline(), None);
    assert_eq!(out.strategy(), StateFusion);
}

// The parameter counts of every callable stored in a `ctor` cell of the
// lowered program, in construction order.
fn stored_callable_arities(out: &TypedLowering, ctor: &str) -> Vec<usize> {
    fn callable_arity(ty: &CoreType) -> Option<usize> {
        match ty {
            CoreType::Thunk(inner) => match inner.result() {
                CoreType::Function(fun) => Some(fun.params().len()),
                _ => None,
            },
            CoreType::Source(Type::Fun(params, _, _)) => Some(params.len()),
            _ => None,
        }
    }
    fn in_value(value: &TypedValue, ctor: &str, out: &mut Vec<usize>) {
        let TypedValueKind::Ctor { name, fields, .. } = value.kind() else {
            return;
        };
        if name.as_str() == ctor {
            out.extend(fields.iter().filter_map(|f| callable_arity(f.ty())));
        }
        for field in fields {
            in_value(field, ctor, out);
        }
    }
    fn in_comp(comp: &TypedComp, ctor: &str, out: &mut Vec<usize>) {
        walk::each_value(comp, &mut |value| in_value(value, ctor, out));
        walk::each_subcomp(comp, &mut |child| in_comp(child, ctor, out));
    }
    let mut arities = Vec::new();
    for f in out.core().functions() {
        in_comp(f.body(), ctor, &mut arities);
    }
    arities
}

const GEN: &str = "effect Gen\n  gen() : Int\n\n";

// A callable stored in a constructor cell and forced after projection takes
// exactly one evidence parameter beyond its source arity, whether the cell
// is a newtype or a field nested inside another constructor. The lowered
// program is audited by the independent verifier against the widened
// declarations, so the store and the force site agree by construction.
#[test]
fn stored_callables_take_one_evidence_parameter_at_landing() {
    for (src, ctor, arity) in [
        (
            format!("{GEN}newtype Act = Act(() -> Int ! {{Gen}})\n\nfn make() : Act = Act(\\() -> gen() * 2)\n\nfn run(a : Act) : Int ! {{Gen}} =\n  match a of\n    Act(f) => f()\n\nfn main() =\n  let total =\n    handle run(make()) with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n"),
            "Act",
            1,
        ),
        (
            format!("{GEN}type Inner = Inner(() -> Int ! {{Gen}})\n\ntype Outer = Outer(Inner, Int)\n\nfn build() : Outer = Outer(Inner(\\() -> gen() + 1), 10)\n\nfn run_outer(o : Outer) : Int ! {{Gen}} =\n  match o of\n    Outer(i, n) =>\n      match i of\n        Inner(f) => f() + n\n\nfn main() =\n  let total =\n    handle run_outer(build()) with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n"),
            "Inner",
            1,
        ),
        // A carrier stored through a generic type argument is declared by
        // the constructor's scheme at that argument, so the store widens it
        // exactly as a field the constructor spells itself.
        (
            format!("{GEN}type Box(a) = Box(a)\n\nfn stored() : Box(() -> Int ! {{Gen}}) = Box(\\() -> gen() + gen())\n\nfn force(b : Box(() -> Int ! {{Gen}})) : Int ! {{Gen}} =\n  match b of\n    Box(f) => f()\n\nfn main() =\n  let total =\n    handle force(stored()) with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n"),
            "Box",
            1,
        ),
        // The same beside a second operation on the accumulator channel: the
        // stored carrier takes both operations' evidence and the accumulator.
        (
            format!("{GEN}effect Tick\n  tick() : Int\n\ntype Box(a) = Box(a)\n\nfn stored() : Box(() -> Int ! {{Gen, Tick}}) = Box(\\() -> gen() + tick())\n\nfn force(b : Box(() -> Int ! {{Gen, Tick}})) : Int ! {{Gen, Tick}} =\n  match b of\n    Box(f) => f()\n\nfn inner() : Int ! {{Gen}} =\n  handle force(stored()) with\n    tick() resume k => k(1) + 1\n    return r => r\n\nfn main() =\n  let total =\n    handle inner() with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n"),
            "Box",
            3,
        ),
        // A value-channel carrier forced inside a scope threading an
        // accumulator takes its one evidence and no accumulator: the force
        // site hands what the carrier's own type declares, not what the
        // scope around it threads.
        (
            format!("{GEN}effect Tick\n  tick() : Int\n\ntype Box(a) = Box(a)\n\nfn stored() : Box(() -> Int ! {{Gen}}) = Box(\\() -> gen() + gen())\n\nfn force(b : Box(() -> Int ! {{Gen}})) : Int ! {{Gen, Tick}} =\n  match b of\n    Box(f) => f() + tick()\n\nfn inner() : Int ! {{Gen}} =\n  handle force(stored()) with\n    tick() resume k => k(1) + 1\n    return r => r\n\nfn main() =\n  let total =\n    handle inner() with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n"),
            "Box",
            1,
        ),
    ] {
        let (source, env, ctors, grades) = typed_from_program(&src);
        let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
        assert_eq!(
            out.strategy(),
            StateFusion,
            "{ctor}: {:?}",
            out.state_decline()
        );
        assert_eq!(stored_callable_arities(&out, ctor), vec![arity], "{ctor}");
    }
}

// A head or tail inside a scope threading an accumulator that performs only
// a value-channel operation, through a named producer or a stored carrier,
// takes that operation's evidence exactly as it would in a value scope: the
// accumulator passes through it, and its answer is read beside it.
// An operation's parameter is not a store position. A carrier handed
// through one reads back in the clause at the row the clause was elaborated
// at, while the store that keeps it and the perform sites that hand it name
// their own, and widened carriers at different rows are different types with
// no subtyping between them. A payload carrying the operation's own effect
// mentions the operation's own row quantifier, which makes the operation
// reified: the payload is cells, and the fold threads what is left.
#[test]
fn a_carrier_payload_over_the_operation_own_effect_reifies() {
    assert_reified_landing(
        "effect Reg\n  reg_memo(() -> Int ! {Reg | e}) : Int\n  reg_get(Int) : Int\n\ntype Node(e : Row) = MemoN(() -> Int ! {Reg | e}, Int)\n\nfn run_thunk(s : Option(Node(e)), action : () -> a ! {Reg | e}) : (Option(Node(e)), a) =\n  let f =\n    handle action() with\n      reg_memo(th) resume k => \\(st) -> k(1)(Some(MemoN(th, 0)))\n      reg_get(n) resume k => \\(st) -> k(n + 1)(st)\n      return x => \\(st) -> (st, x)\n  f(s)\n\nfn main() =\n  let r = run_thunk(None, \\() -> reg_get(reg_memo(\\() -> reg_get(4))))\n  println(snd(r))\n",
    );
}

// A payload carrying another fused effect names no quantifier of its own
// operation, so nothing makes the operation reified, and the store the
// clause keeps it in is refused by name before anything is threaded.
#[test]
fn a_carrier_payload_over_another_fused_effect_declines_by_name() {
    let src = "effect Tick\n  tick() : Int\n\neffect Reg\n  reg_memo(() -> Int ! {Tick | e}) : Int\n\ntype Node(e : Row) = MemoN(() -> Int ! {Tick | e}, Int)\n\nfn run_thunk(s : Option(Node(e)), action : () -> a ! {Reg | e}) : (Option(Node(e)), a) =\n  let f =\n    handle action() with\n      reg_memo(th) resume k => \\(st) -> k(1)(Some(MemoN(th, 0)))\n      return x => \\(st) -> (st, x)\n  f(s)\n\nfn force_all(s : Option(Node(e))) : Int ! {Tick | e} =\n  match s of\n    Some(MemoN(f, _)) => f() + tick()\n    None => 0\n\nfn main() =\n  let r = run_thunk(None, \\() -> reg_memo(\\() -> tick() + 4))\n  let total = handle force_all(fst(r)) with\n    tick() resume k => k(10)\n  println(snd(r) + total)\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_eq!(out.state_decline(), Some("`reg_memo`: a carrier payload"));
}

#[test]
fn value_channel_heads_inside_a_state_scope_take_their_evidence() {
    const TICK: &str = "effect Tick\n  tick() : Int\n\nfn inner() : Int ! {Gen} =\n  handle force() with\n    tick() resume k => k(1) + 1\n    return r => r\n\nfn main() =\n  let total =\n    handle inner() with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n";
    for (name, body) in [
        (
            "named head",
            "fn g() : Int ! {Gen} = gen() + gen()\n\nfn force() : Int ! {Gen, Tick} =\n  let a = g()\n  a + tick()\n\n",
        ),
        (
            "named tail",
            "fn g() : Int ! {Gen} = gen() + gen()\n\nfn force() : Int ! {Gen, Tick} =\n  let t = tick()\n  g() + t\n\n",
        ),
        (
            "carrier tail",
            "type Box(a) = Box(a)\n\nfn stored() : Box(() -> Int ! {Gen}) = Box(\\() -> gen() + gen())\n\nfn force() : Int ! {Gen, Tick} =\n  let t = tick()\n  match stored() of\n    Box(f) => f()\n\n",
        ),
    ] {
        let src = format!("{GEN}{body}{TICK}");
        let (source, env, ctors, grades) = typed_from_program(&src);
        let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
        assert_eq!(
            out.strategy(),
            StateFusion,
            "{name}: {:?}",
            out.state_decline()
        );
    }
}

// A store the state route has no single convention for declines by name
// rather than landing at a guessed one: a row-parameterised field whose two
// instantiations would widen to two different arities. A conservative
// decline the verifier never has to refuse.
#[test]
fn stores_without_one_convention_decline_by_name() {
    let src = format!("{GEN}type Cell(e : Row) = Cell(() -> Int ! {{e}})\n\nfn run_cell(c) =\n  match c of\n    Cell(f) => f()\n\nfn main() =\n  let quiet = Cell(\\() -> 5)\n  let loud = Cell(\\() -> gen())\n  let total =\n    handle run_cell(loud) + run_cell(quiet) with\n      gen() resume k => k(3)\n      return r => r\n  println(total)\n");
    let reason =
        "`main`: an argument the callee's parameter does not accept (Cell({Gen}) at Cell({}))";
    let (source, env, ctors, grades) = typed_from_program(&src);
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_ne!(out.strategy(), StateFusion, "{reason}");
    assert_eq!(out.state_decline(), Some(reason));
}

// A producer under several aborts has no one stop to step onto, so the
// aborts are reified: the handle answering them drives cells, and the
// program still reaches threaded state.
#[test]
fn two_aborts_in_one_producer_land_on_the_reified_route() {
    let src = "error NotFound(String)\n\nerror Malformed(String)\n\nfn lookup(k) =\n  if k == \"x\" then\n    7\n  else\n    throw NotFound(k)\n\nfn parse_num(s) =\n  if s == \"1\" then\n    1\n  else\n    throw Malformed(s)\n\nfn both(k, s) : Int ! {NotFound, Malformed} =\n  lookup(k) + parse_num(s)\n\nfn main() =\n  let c =\n    try\n      both(\"y\", \"1\")\n    catch\n      NotFound(k) => 100\n      Malformed(m) => 200\n  println(c)\n";
    assert_reified_landing(src);
}

// Two aborts each raised by a producer of its own and joined only at the
// handle answering both: the scope under that handle reaches two aborts, so
// they are reified together.
#[test]
fn two_aborts_joined_at_one_handle_land_on_the_reified_route() {
    let src = "error A(Int)\n\nerror B(Int)\n\nfn g(n) : Int ! {A} =\n  if n == 0 then\n    throw A(1)\n  else\n    n\n\nfn h(n) : Int ! {B} =\n  if n == 1 then\n    throw B(2)\n  else\n    n\n\nfn main() =\n  let r =\n    try\n      g(0) + h(1)\n    catch\n      A(x) => x + 10\n      B(y) => y + 20\n  println(r)\n";
    assert_reified_landing(src);
}

// A handle inside a live scope that discharges the scope's abort has no
// threading arm: the accumulator threaded past it cannot survive the abort
// inside a step. The abort and the operation that accumulator is threaded
// for are reified together, and the fold answering that operation drives
// the cells.
#[test]
fn an_abort_discharged_inside_a_state_producer_lands_on_the_reified_route() {
    let src = "effect Raise\n  raise(Int) : Int\n\neffect Tick\n  tick(Unit) : Int\n\nfn total(n) : Int ! {Raise, Tick} =\n  let a = tick(())\n  let b =\n    if n == 0 then\n      raise(a)\n    else\n      n * tick(())\n  a + b\n\nfn recover(n) : Int ! {Tick} =\n  handle total(n) with\n    never raise(c) => 0 - c\n    return r => r\n\nfn run_one(n) =\n  let f =\n    handle recover(n) with\n      tick(u) resume k => \\(s) -> k(s)(s + 1)\n      return r => \\(_s) -> r\n  f(1)\n\nfn main() =\n  println(run_one(0))\n  println(run_one(3))\n";
    assert_reified_landing(src);
}

// The channel of an operation is decided once for the program, so a direct
// consumer of an operation another handler folds over an Int has no seed of
// that type to thread. Its operations are reified instead: each handle
// answers its own performs from the queue.
#[test]
fn a_consumer_of_an_operation_pinned_elsewhere_lands_on_the_reified_route() {
    let src = "effect Counter\n  get() : Int\n  bump() : Unit\n\nfn twice() : Int ! {Counter} =\n  bump()\n  get() * 2\n\nfn counted() : Int =\n  let run =\n    handle twice() with\n      get() resume k => \\(s) -> k(s)(s)\n      bump() resume k => \\(s) -> k(())(s + 1)\n      return r => \\(_s) -> r\n  run(0)\n\nfn add_get(total) : Int ! {Counter} =\n  bump()\n  total + get()\n\nfn main() =\n  let total = counted()\n  let more =\n    handle add_get(total) with\n      get() resume k => k(7)\n      bump() resume k => k(())\n  println(more)\n";
    assert_reified_landing(src);
}

// A while loop's condition is a producing head of a thunk parameter: not a
// read, not a write, and not unit, so an accumulator alone cannot rebuild
// it. The scope carries the accumulator and the value side by side instead,
// which needs no reified continuation.
#[test]
fn a_while_head_over_state_threads_a_pair() {
    let src = "effect Counter\n  get() : Int\n  bump() : Unit\n\nfn count_up() : Unit ! {Counter, IO} =\n  while get() < 4 do\n    println(get() * 10)\n    bump()\n\nfn main() =\n  let f =\n    handle count_up() with\n      get() resume k => \\(s) -> k(s)(s)\n      bump() resume k => \\(s) -> k(())(s + 1)\n      return r => \\(s) -> s\n  println(f(0))\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    for reify in [false, true] {
        let flags = DynFlags {
            reify,
            quiet: true,
            ..DynFlags::default()
        };
        let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
        assert_eq!(out.strategy(), StateFusion, "reify = {reify}");
    }
}

// A producer's closed declared row keeps labels the fold does not answer.
// Those labels stand ahead of the ambient in the producer's row, so the IO
// it performs at its own top level types there, and a caller instantiates
// the ambient at its row less what the producer already spells.
#[test]
fn a_state_producer_keeps_its_declared_residual_labels() {
    let src = "effect Counter\n  get() : Int\n  bump() : Unit\n\nfn count_up() : Unit ! {Counter, IO} =\n  println(get() * 10)\n  bump()\n  println(get())\n\nfn main() =\n  let f =\n    handle count_up() with\n      get() resume k => \\(s) -> k(s)(s)\n      bump() resume k => \\(s) -> k(())(s + 1)\n      return r => \\(s) -> s\n  println(f(0))\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    for reify in [false, true] {
        let flags = DynFlags {
            reify,
            quiet: true,
            ..DynFlags::default()
        };
        let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
        assert_eq!(out.strategy(), StateFusion, "reify = {reify}");
    }
}

// A `var` is a cell by the time the reified rewrite sees the scope that
// declares it: reading and writing the cell performs nothing reified, so a
// direct scope carries those computations as it carries any other value
// traffic.
#[test]
fn a_var_cell_read_in_a_direct_scope_lands_on_the_reified_route() {
    let src = "effect Counter\n  get() : Int\n  bump() : Unit\n\nfn counted() : Int =\n  let run =\n    with handler\n      get() resume k => \\(s) -> k(s)(s)\n      bump() resume k => \\(s) -> k(())(s + 1)\n      return r => \\(_s) -> r\n    bump()\n    get() * 2\n  run(0)\n\nfn main() =\n  var total := counted()\n  with handler\n    get() resume k => k(7)\n    bump() resume k => k(())\n  bump()\n  total := total + get()\n  println(total)\n";
    assert_reified_landing(src);
}

// A bare-row thunk parameter forced under a var-cell handler: nothing in
// the forwarder's scope fixes `cput`'s effect parameter, so the forwarder
// binds a quantifier for it and the call under the handler instantiates
// that quantifier from the row it hands over. Both channels: the put-only
// twin's clause has no result to keep generic.
#[test]
fn a_bare_row_carrier_with_an_unfixed_effect_parameter_lands() {
    let run_cell = "effect Cell(s)\n  cget() : s\n  cput(s) : Unit\n\nfn run_cell(init : s, action : () -> a ! {Cell(s) | e}) : (a, s) ! {| e} =\n  var cell := init\n  let r =\n    handle action() with\n      cget() resume k => k(cell)\n      cput(s2) resume k =>\n        cell := s2\n        k(())\n      return r => r\n  (r, cell)\n\nfn apply(combine : (Int, Int) -> Int ! {| e}, a : Int, b : Int) : Int ! {| e} =\n  combine(a, b)\n\n";
    for tick in [
        "fn tick(v : Int) : Int ! {Cell(Int)} =\n  cput(cget() + 1)\n  v\n\n",
        "fn tick(v : Int) : Int ! {Cell(Int)} =\n  cput(v)\n  v\n\n",
        "fn tick(v : Int) : Int ! {Cell(Int)} =\n  v + cget()\n\n",
    ] {
        let src = format!(
            "{run_cell}{tick}fn main() =\n  let r = run_cell(0, \\() -> apply(\\(a, b) -> tick(a + b), 1, 2))\n  println(r)\n"
        );
        let (source, env, ctors, grades) = typed_from_program(&src);
        for reify in [false, true] {
            let flags = DynFlags {
                reify,
                quiet: true,
                ..DynFlags::default()
            };
            let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
            assert_eq!(out.strategy(), StateFusion, "reify = {reify}: {tick}");
        }
    }
}

// An operation whose parameter mentions the operation's own row quantifier:
// no clause type fixes that quantifier from the forwarder's scope, so the
// operation is reified and its payload is cells. The payload names an effect
// the fold threads, whose evidence the forwarder's caller made: it runs at
// the row that evidence is typed at, the caller is credited with what it
// performs, and the forwarder reads it through its gained ambient.
#[test]
fn an_operation_own_row_quantifier_in_a_parameter_reifies() {
    assert_reified_landing("effect Out\n  out(Int) : Unit\n\neffect Wrap\n  wrap(() -> Int ! {Wrap | e}) : Int\n\nfn run_wrap(action : () -> a ! {Wrap | e}) : a =\n  handle action() with\n    wrap(th) resume k => k(run_wrap(th))\n    return x => x\n\nfn inner() : Int ! {Out} =\n  out(7)\n  3\n\nfn driver() : Int ! {Wrap, Out} = wrap(inner)\n\nfn main() =\n  println(handle run_wrap(driver) with {\n    out(n) resume k => let _ = println(n) in k(()),\n    return r => r\n  })\n");
}

// The same forwarder with a generic clause row: the forwarder's own handle
// answers the reified operation over its quantifier, the payload is written
// where the caller's handler for the threaded effect lives, and a thunk
// built there that performs nothing threaded runs at the island's row.
#[test]
fn a_payload_forwarder_with_a_generic_clause_row_reifies() {
    assert_reified_landing("effect Out\n  out(Int) : Unit\n\neffect Wrap\n  wrap(() -> Int ! {Wrap | e}) : Int\n\nfn run_wrap(action : () -> a ! {Wrap | e}) : a ! {| e} =\n  handle action() with\n    wrap(th) resume k => k(run_wrap(th))\n    return x => x\n\nfn inner() : Int ! {Out} =\n  out(7)\n  3\n\nfn driver() : Int ! {Wrap, Out} = wrap(inner)\n\nfn main() =\n  println(handle run_wrap(driver) with {\n    out(n) resume k => let _ = println(n) in k(()),\n    return r => r\n  })\n");
}

// A mask has no threading arm yet: the program declines before any plan.
#[test]
fn a_masked_effect_declines_by_name() {
    let src = "effect Tick\n  tick() : Int\n\nfn inner() : Int ! {Tick} = tick()\n\nfn outer() : Int ! {Tick} =\n  handle mask<Tick>(inner()) with\n    tick() resume k => k(100)\n    return r => r\n\nfn main() =\n  let r =\n    handle outer() with\n      tick() resume k => k(1)\n      return r => r\n  println(r)\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_ne!(out.strategy(), StateFusion);
    assert_eq!(out.state_decline(), Some("the program masks an effect"));
}

// A state producer with an open declared row names its own ambient, so a
// consumer it calls returns at that ambient rather than a second open tail.
#[test]
fn a_state_producer_with_an_open_row_calls_a_consumer_at_its_ambient() {
    let src = "effect Warn\n  warn(String) : Unit\n\nfn capture(action : () -> a ! {Warn | r}) : (a, Int) =\n  let f =\n    handle action() with\n      warn(_m) resume k => \\(n) -> k(())(n + 1)\n      return v => \\(n) -> (v, n)\n  f(0)\n\nfn tolerate(action : () -> a ! {Warn | r}) : a ! {Warn | r} =\n  match capture(action) of\n    (v, n) =>\n      warn(\"captured\")\n      v\n\nfn branch() : Int ! {Warn} =\n  let x = tolerate(\\() -> warn(\"inner\"))\n  warn(\"after\")\n  7\n\nfn count(action : () -> a ! {Warn}) : Int =\n  let f =\n    handle action() with\n      warn(_m) resume k => \\(n) -> k(())(n + 1)\n      return v => \\(n) -> n\n  f(0)\n\nfn main() = println(count(branch))\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    let out = assert_typed_lowering(source, &env, &ctors, &reify_flags(), &grades);
    assert_eq!(out.state_decline(), None);
    assert_eq!(out.strategy(), StateFusion);
}

// An open-row adapter whose direct clause performs an operation a downstream
// handler threads as state: the clause holds no accumulator to hand that
// operation, so its own operation reifies, and the island closes over the
// state handler its clause performs into. Without reification the same
// shape is the named decline.
#[test]
fn an_open_row_adapter_over_a_state_consumer() {
    let src = "effect Ask\n  ask() : Int\n\neffect Tell\n  tell() : Int\n\nfn adapt(action : () -> a ! {Ask | e}) =\n  handle action() with\n    ask() resume k => k(tell() + 1)\n    return r => r\n\nfn serve(action) =\n  let f =\n    handle action() with\n      tell() resume k => \\(n) -> k(n)(n + 1)\n      return r => \\(_n) -> r\n  f(10)\n\nfn client() : Int ! {Ask} = ask() + ask()\n\nfn main() = println(serve(\\() -> adapt(client)))\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    let off = assert_typed_lowering(
        source,
        &env,
        &ctors,
        &DynFlags {
            reify: false,
            quiet: true,
            ..DynFlags::default()
        },
        &grades,
    );
    assert_ne!(off.strategy(), StateFusion);
    assert_eq!(
        off.state_decline(),
        Some("`adapt`: a direct clause performing `tell`, which this scope threads as state")
    );
    assert_reified_landing(src);
}

// The same adapter resuming from inside a thunk: the clause is reified on
// its own account, and the state operation it performs still joins its
// island rather than leaving the driver's body at a row its signature lost.
#[test]
fn a_thunk_resuming_adapter_over_a_state_consumer() {
    assert_reified_landing(
        "effect Ask\n  ask() : Int\n\neffect Tell\n  tell() : Int\n\nfn adapt(action : () -> a ! {Ask | e}) =\n  handle action() with\n    ask() resume k => let th = \\() -> k(tell() + 1) in th()\n    return r => r\n\nfn serve(action) =\n  let f =\n    handle action() with\n      tell() resume k => \\(n) -> k(n)(n + 1)\n      return r => \\(_n) -> r\n  f(10)\n\nfn client() : Int ! {Ask} = ask() + ask()\n\nfn main() = println(serve(\\() -> adapt(client)))\n",
    );
}

// A multishot adapter performing a state operation: the island closure is
// what keeps the verifier from seeing a driver whose body keeps `Tell`.
#[test]
fn resuming_into_a_state_body_does_not_make_a_direct_clause_an_island() {
    // The resumption's type carries the row of the rest of the handled body,
    // here `tick`, which the outer handler folds. Resuming is not the clause
    // performing `tick`: the inner handle stays threaded, and nothing is
    // reified.
    let src = "effect Ask\n  ask() : Int\n\neffect Tick\n  tick(Unit) : Unit\n\nfn inner() : Int =\n  var c := 0\n  tick(())\n  c := c + ask()\n  tick(())\n  c := c * 2\n  c + ask()\n\nfn middle() : Int =\n  handle inner() with\n    ask() resume k => k(5)\n    return x => x\n\nfn main() =\n  let r =\n    handle middle() with\n      tick(u) resume k => k(()) + 100\n      return x => x\n  println(r)\n";
    let (source, env, ctors, grades) = typed_from_program(src);
    for flags in [
        DynFlags {
            reify: false,
            quiet: true,
            ..DynFlags::default()
        },
        reify_flags(),
    ] {
        let out = assert_typed_lowering(source.clone(), &env, &ctors, &flags, &grades);
        assert_eq!(out.strategy(), StateFusion);
        assert_eq!(out.state_decline(), None);
        assert!(
            !functions_use_constructor(out.core().functions(), "EOp"),
            "the direct clause was promoted to a cell under reify={}",
            flags.reify
        );
    }
}

#[test]
fn a_multishot_adapter_over_a_state_consumer() {
    assert_reified_landing(
        "effect Ask\n  ask() : Int\n\neffect Tell\n  tell() : Int\n\nfn adapt(action : () -> Int ! {Ask | e}) : Int =\n  handle action() with\n    ask() resume k => k(tell() + 1) + k(0)\n    return r => r\n\nfn serve(action) =\n  let f =\n    handle action() with\n      tell() resume k => \\(n) -> k(n)(n + 1)\n      return r => \\(_n) -> r\n  f(10)\n\nfn client() : Int ! {Ask} = ask() + ask()\n\nfn main() = println(serve(\\() -> adapt(client)))\n",
    );
}

const SETTLED_READ: &str = "an operation cell reached a site whose row admits none";

fn comp_mentions_str(comp: &TypedComp, needle: &str) -> bool {
    let mut found = false;
    walk::each_value(comp, &mut |value| {
        found |= value_mentions_str(value, needle);
    });
    walk::each_subcomp(comp, &mut |child| found |= comp_mentions_str(child, needle));
    found
}

fn value_mentions_str(value: &TypedValue, needle: &str) -> bool {
    match value.kind() {
        TypedValueKind::Str(text) => text.contains(needle),
        TypedValueKind::Thunk(body) => comp_mentions_str(body, needle),
        TypedValueKind::Ctor { fields, .. }
        | TypedValueKind::Tuple(fields)
        | TypedValueKind::UnboxedTuple(fields) => {
            fields.iter().any(|field| value_mentions_str(field, needle))
        }
        TypedValueKind::UnboxedRecord(fields) => fields
            .iter()
            .any(|(_, field)| value_mentions_str(field, needle)),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => value_mentions_str(inner, needle),
        _ => false,
    }
}

// The functions whose lowered bodies read a cells thunk through a settled
// plain adapter: the adapter forces the cells thunk and reads the value out
// of the pure cell, and its operation arm is the ICE no admitted row reaches.
fn settled_readers(out: &TypedLowering) -> Vec<String> {
    out.core()
        .functions()
        .iter()
        .filter(|function| comp_mentions_str(function.body(), SETTLED_READ))
        .map(|function| function.name().as_str().to_string())
        .collect()
}

// A combinator (`rw_try`) quantified over the rule's row builds its result
// thunk as cells where the row reifies, and `main` hands that result to a
// reader (`rw_bottom_up` instantiated at a row admitting nothing reified)
// whose own type spells a plain thunk. The hand-off must settle the cells
// result rather than pass it plain: passing it plain read the pure cell as
// the value natively while every verifier passed, since a cells thunk and a
// plain one are the same machine word. The settled reader drives the cells
// at the island's row and is bridged back to the declared type. The corpus
// program is read from the tree (its imports are outside the compiler source
// roots).
#[test]
fn a_cells_combinator_result_settles_at_its_plain_reader() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src = fs::read_to_string(root.join("tests/cases/run/rewrite_strategies.pr")).unwrap();
    let (typed, env, ctors, grades) = typed_from_program(&src);
    let out = assert_typed_lowering(typed, &env, &ctors, &reify_flags(), &grades);
    assert_eq!(out.strategy(), StateFusion, "{:?}", out.state_decline());
    let readers = settled_readers(&out);
    assert!(
        readers.iter().any(|name| name == "main"),
        "`main` must settle the combinator's cells result before handing it to a plain reader: {readers:?}"
    );
}
