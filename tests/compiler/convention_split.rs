use std::collections::{BTreeMap, BTreeSet};

use prism::core::typed::effect_lower::analysis::{self, MonadicScope};
use prism::core::typed::effect_lower::plan::collect_calls;
use prism::core::typed::effect_lower::{lower_effects, prepare, EffectPlan};
use prism::core::typed::verify::VerifyEnv;
use prism::core::typed::{Elaborated, TypedCore, TypedCoreFn};
use prism::core::{EffectStrategy, OpGrades};
use prism::flags::DynFlags;
use prism::types::CtorInfo;
use prism_common::sym::Sym;

const PURE: &str = include_str!("../fixtures/tier_cross/convention_split_map_pure.pr");
const MIXED: &str = include_str!("../fixtures/tier_cross/convention_split_map.pr");
const UNROLLED: &str = include_str!("../fixtures/tier_cross/convention_split_map_unrolled.pr");

fn typed_from_program(
    source: &str,
) -> (
    TypedCore<Elaborated>,
    VerifyEnv,
    BTreeMap<String, CtorInfo>,
    OpGrades,
) {
    let source = prism::driver::with_prelude(source);
    let parsed = prism_syntax::parse::parse(&source)
        .expect("fixture parses")
        .program;
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

fn calls(function: &TypedCoreFn) -> BTreeSet<Sym> {
    let mut calls = BTreeSet::new();
    collect_calls(function.body(), &mut calls);
    calls
}

#[test]
fn mixed_direct_and_effectful_map_keeps_the_pure_clone_direct() {
    let (typed, env, ctors, grades) = typed_from_program(MIXED);
    let flags = DynFlags::default();
    let prepared = prepare(typed.clone(), &env, &ctors, &flags, &grades)
        .expect("convention preparation succeeds");
    let clone = prepared
        .fns
        .iter()
        .find(|function| function.name().as_str().starts_with("Data.List.map$ec"))
        .expect("the mixed demand materializes a map convention clone");
    let clone_name = clone.name();
    let clone_sig = clone.sig().clone();
    let original = Sym::new("Data.List.map");
    let pure_use = prepared
        .fns
        .iter()
        .find(|function| function.name().as_str() == "pure_use")
        .expect("pure caller remains reachable");
    let effect_use = prepared
        .fns
        .iter()
        .find(|function| function.name().as_str() == "effect_use")
        .expect("effectful caller remains reachable");

    assert!(calls(pure_use).contains(&clone_name));
    assert!(!calls(pure_use).contains(&original));
    assert!(calls(effect_use).contains(&original));
    assert!(!calls(effect_use).contains(&clone_name));
    assert!(calls(clone).contains(&clone_name));
    assert!(!calls(clone).contains(&original));

    let effects = EffectPlan::analyze(&prepared.fns);
    let region = analysis::plan(&prepared.fns, &effects, false);
    assert_eq!(region.scope, MonadicScope::Selective);
    assert!(region.members.contains(&original));
    assert!(region.members.contains(&effect_use.name()));
    assert!(!region.members.contains(&clone_name));
    assert!(!region.members.contains(&pure_use.name()));
    assert_eq!(
        region.monadic_params.get(&original),
        Some(&BTreeSet::from([0]))
    );
    assert!(!region.monadic_params.contains_key(&clone_name));

    let lowered = lower_effects(typed, &env, &ctors, &flags, &grades)
        .expect("the convention-split program lowers");
    assert_ne!(lowered.strategy, EffectStrategy::WholeProgramFreeMonad);
    assert_eq!(
        lowered
            .core
            .functions()
            .iter()
            .find(|function| function.name() == clone_name)
            .expect("the direct clone survives lowering")
            .sig(),
        &clone_sig,
        "the pure clone never crosses a monadic convention boundary"
    );

    let run = prism::interpret(&prism::driver::with_prelude(MIXED))
        .expect("the reference interpreter accepts the same fixture");
    assert_eq!(run.term, "[2, 3, 4][8, 10]");
}

#[test]
fn pure_and_unrolled_controls_pin_the_expected_tiers_and_outputs() {
    for (name, source, strategy, output) in [
        ("pure", PURE, EffectStrategy::Pure, "[2, 3, 4]"),
        (
            "unrolled",
            UNROLLED,
            EffectStrategy::Evidence,
            "[2, 3, 4][8, 10]",
        ),
    ] {
        let (typed, env, ctors, grades) = typed_from_program(source);
        let lowered = lower_effects(typed, &env, &ctors, &DynFlags::default(), &grades)
            .unwrap_or_else(|error| panic!("{name} control lowers: {error}"));
        assert_eq!(lowered.strategy, strategy, "{name} control tier");

        let run = prism::interpret(&prism::driver::with_prelude(source))
            .unwrap_or_else(|error| panic!("{name} control interprets: {error}"));
        assert_eq!(run.term, output, "{name} control output");
    }
}

#[test]
fn a_single_effectful_map_demand_keeps_the_original_symbol() {
    let source = r#"
effect Log
  emit(Int) : Unit

fn shout(x : Int) : Int ! {Log} =
  let _u = emit(x)
  x * 2

fn main() =
  let _handled =
    handle map(shout, [1]) with
      emit(_n) resume k => k(())
      return r => r
  print("ok")
"#;
    let (typed, env, ctors, grades) = typed_from_program(source);
    let prepared = prepare(typed, &env, &ctors, &DynFlags::default(), &grades)
        .expect("single-convention preparation succeeds");
    assert!(
        prepared
            .fns
            .iter()
            .all(|function| !function.name().as_str().contains("$ec")),
        "one known convention does not need a clone"
    );
}
