use std::slice;

use prism_common::fresh::Fresh;

use crate::core::typed::verify::OperationSig;
use crate::types::ty::Label;
use crate::types::Type;

use super::super::{as_var, binder_var, latent::latent_map};
use super::*;

const FIRST_EVIDENCE_ID: i64 = 0;

fn env_with(ops: &[(&str, &str, Type)]) -> VerifyEnv {
    let mut env = VerifyEnv::new();
    for (op, effect, result) in ops {
        env.insert_operation(
            Sym::new(op),
            OperationSig::new(
                Vec::new(),
                Vec::new(),
                CoreType::Source(result.clone()),
                Label::bare(Sym::new(effect)),
            ),
        );
    }
    env
}

fn kinds(entries: &[(&str, FoldAKind)]) -> BTreeMap<Sym, FoldAKind> {
    entries.iter().map(|(op, k)| (Sym::new(op), *k)).collect()
}

fn plan_over(entries: &[(&str, FoldAKind)], env: &VerifyEnv) -> FoldPlan {
    let kinds = kinds(entries);
    FoldPlan {
        ops: kinds.keys().copied().collect(),
        pins: pins(&kinds, env).expect("every operation is declared"),
        kinds,
        answer: StateAnswerMode::Accumulator,
        early: EarlyExitMode::Continue,
    }
}

fn ops(names: &[&str]) -> BTreeSet<Sym> {
    names.iter().map(|n| Sym::new(n)).collect()
}

#[test]
fn accumulator_answer_excludes_value_bearing_unclassified_producer_results() {
    // A value-bearing (non-Unit) unclassified producer result declines the
    // state rung rather than crashing: the accumulator cannot rebuild it,
    // so it falls through to the free-monad fallback, symmetric with the
    // producer arm. Tier selection stays unobservable.
    let st = TypedBinder::new(Sym::from(STATE_ACC), CoreType::Source(Type::Int));
    let bound = bound_producer_result(
        StateAnswerMode::Accumulator,
        None,
        &st,
        &CoreType::Source(Type::Int),
    );
    assert!(
        bound.is_none(),
        "a value-bearing producer result must decline, not bind"
    );
}

fn thunk_performing(op: Sym, instantiation: Type) -> TypedValue {
    let unit = CoreType::Source(Type::Unit);
    let body = TypedComp::new(
        CompSig::new(unit, EffRow::Empty),
        TypedCompKind::Do {
            operation: op,
            instantiation: vec![CoreInstantiation::Type(instantiation)],
            args: Vec::new(),
        },
    );
    TypedValue::new(
        CoreType::Thunk(Box::new(body.sig().clone())),
        TypedValueKind::Thunk(Box::new(body)),
    )
}

// `stake_go` performs its re-emit inside the state-transformer thunk its
// handler clause returns. That `Do` is still the producer declaration's
// evidence instantiation; a sub-computation-only walk silently misses it.
#[test]
fn lexical_instantiation_finds_a_perform_inside_a_returned_thunk() {
    let op = Sym::new("emit");
    let element = Sym::new("element");
    let thunk = thunk_performing(op, Type::Var(element));
    let outer = TypedComp::new(
        CompSig::new(thunk.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(thunk),
    );

    assert_eq!(
        lexical_instantiation(&outer, op, &[], &Latent::new(), LEXICAL_DEPTH),
        Some(vec![CoreInstantiation::Type(Type::Var(element))])
    );
}

// Two escaping thunks performing the same operation at different types do
// not admit one shared evidence clause. Traversing thunk bodies must retain
// the existing conflict result rather than selecting whichever is visited
// first.
#[test]
fn conflicting_thunk_performs_have_no_lexical_instantiation() {
    let op = Sym::new("emit");
    let first_value = thunk_performing(op, Type::Int);
    let second_value = thunk_performing(op, Type::Bool);
    let first = TypedComp::new(
        CompSig::new(first_value.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(first_value),
    );
    let second = TypedComp::new(
        CompSig::new(second_value.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(second_value),
    );
    let result = second.sig().clone();
    let first_result = first.sig().result().clone();
    let outer = TypedComp::new(
        result,
        TypedCompKind::Bind(
            Box::new(first),
            TypedBinder::new(Sym::new("ignored_thunk"), first_result),
            Box::new(second),
        ),
    );

    assert_eq!(
        lexical_instantiation(&outer, op, &[], &Latent::new(), LEXICAL_DEPTH),
        None
    );
}

// The operation declaration conventionally calls its parameter `a`, and a
// producer may independently bind an unrelated result `a`. `stake_go` is
// exactly this collision: its re-emitted payload is `b`. The actual `Do<b>`
// inside the returned transformer, not either printed `a`, owns the clause.
#[test]
fn producer_evidence_uses_the_thunked_perform_not_a_colliding_name() {
    let declaration_a = Sym::new("a");
    let payload_b = Sym::new("b");
    let operation = Sym::new("emit");
    let mut env = VerifyEnv::new();
    env.insert_operation(
        operation,
        OperationSig::new(
            vec![CoreQuantifier::Type(declaration_a)],
            vec![CoreType::Source(Type::Var(declaration_a))],
            CoreType::Source(Type::Unit),
            Label {
                name: Sym::new("Emit"),
                args: vec![Type::Var(declaration_a)],
            },
        ),
    );
    let plan = plan_over(&[("emit", FoldAKind::Unit)], &env);
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let thunk = thunk_performing(operation, Type::Var(payload_b));
    let body = TypedComp::new(
        CompSig::new(thunk.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(thunk),
    );
    let producer = TypedCoreFn::new(
        Sym::new("collision_producer"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(
            vec![
                CoreQuantifier::Type(declaration_a),
                CoreQuantifier::Type(payload_b),
            ],
            Vec::new(),
            body.sig().clone(),
        ),
        0,
    );

    let planned = plan_producer(
        &producer,
        &plan.ops,
        &plan,
        &ids,
        slice::from_ref(&producer),
        &Latent::new(),
        &env,
    )
    .expect("the producer has one concrete evidence scheme");
    let CoreType::Thunk(evidence) = planned.evidence[0].ty() else {
        panic!("the producer receives thunked evidence");
    };
    let CoreType::Function(clause) = evidence.result() else {
        panic!("the evidence contains a clause function");
    };
    assert!(clause.quantifiers().is_empty());
    assert_eq!(
        clause.params()[0],
        CoreType::Source(Type::Var(payload_b)),
        "the actual payload b wins over the unrelated canonical a"
    );
}

// Forwarding through a polymorphic producer substitutes the complete
// operation instantiation. Type and row arguments follow the same call
// edge; retaining the callee's row variable would split one evidence scheme
// into two vocabularies.
#[test]
fn forwarding_substitutes_mixed_type_and_row_operation_arguments() {
    let operation = Sym::new("mixed_emit");
    let target_name = Sym::new("mixed_target");
    let element = Sym::new("element");
    let residual = Sym::new("residual");
    let unit = CoreType::Source(Type::Unit);
    let target_body = TypedComp::new(
        CompSig::new(unit.clone(), EffRow::Var(residual)),
        TypedCompKind::Do {
            operation,
            instantiation: vec![
                CoreInstantiation::Type(Type::Var(element)),
                CoreInstantiation::Row(EffRow::Var(residual)),
            ],
            args: Vec::new(),
        },
    );
    let target = TypedCoreFn::new(
        target_name,
        Vec::new(),
        target_body.clone(),
        CoreFnSig::new(
            vec![CoreQuantifier::Type(element), CoreQuantifier::Row(residual)],
            Vec::new(),
            target_body.sig().clone(),
        ),
        0,
    );
    let concrete_row = EffRow::singleton(Sym::new("IO"));
    let call = TypedComp::new(
        CompSig::new(unit, concrete_row.clone()),
        TypedCompKind::Call {
            callee: target_name,
            instantiation: vec![
                CoreInstantiation::Type(Type::Int),
                CoreInstantiation::Row(concrete_row.clone()),
            ],
            args: Vec::new(),
        },
    );
    let functions = [target];
    let latent = latent_map(&functions);

    assert_eq!(
        lexical_instantiation(&call, operation, &functions, &latent, LEXICAL_DEPTH),
        Some(vec![
            CoreInstantiation::Type(Type::Int),
            CoreInstantiation::Row(concrete_row),
        ])
    );
}

// A writer streams only writes, so nothing observes the accumulator and every
// producer stays parametric in it. This is what lets one stream producer feed
// two chains at two accumulator types in a single program.
#[test]
fn writes_alone_leave_the_accumulator_free() {
    let env = env_with(&[("tell", "Writer", Type::Unit)]);
    let plan = plan_over(&[("tell", FoldAKind::Unit)], &env);
    assert_eq!(
        plan.accumulator_for(&ops(&["tell"])),
        Some(Accumulator::Free)
    );
}

// An escaping producer thunk can already bind source quantifiers. State
// threading appends its state and ambient binders inside that same thunk;
// it must not replace the source scheme, or the rewritten value and every
// direct call typed by the signature prepass disagree.
#[test]
fn a_quantified_escaping_thunk_keeps_its_source_scheme() {
    let env = env_with(&[("tell", "Writer", Type::Unit)]);
    let plan = plan_over(&[("tell", FoldAKind::Unit)], &env);
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let source_row = Sym::new("source_row");
    let unit = CoreType::Source(Type::Unit);
    let effects = EffRow::Extend(
        Label::bare(Sym::new("Writer")),
        Box::new(EffRow::Var(source_row)),
    );
    let parameter = TypedBinder::new(Sym::new("u"), unit.clone());
    let body = TypedComp::new(
        CompSig::new(unit.clone(), effects.clone()),
        TypedCompKind::Do {
            operation: Sym::new("tell"),
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let source_sig = CoreFnSig::new(
        vec![CoreQuantifier::Row(source_row)],
        vec![unit.clone()],
        CompSig::new(unit, effects),
    );
    let lambda = TypedComp::new(
        CompSig::new(CoreType::Function(Box::new(source_sig)), EffRow::Empty),
        TypedCompKind::Lam(vec![parameter], Box::new(body)),
    );
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    );
    let operation = Sym::new("tell");
    let evs = BTreeMap::from([(operation, Sym::from(names::ev(FIRST_EVIDENCE_ID)))]);
    let flow = ThunkFlow {
        ret: BTreeMap::new(),
        param: BTreeMap::new(),
    };
    let mut fresh = Fresh::new();
    let mut threader = Threader {
        plan: &plan,
        ids: &ids,
        env: &env,
        latent: &Latent::new(),
        flow: &flow,
        drift: &DriftLog::new(true),
        retyped: Retyped::new(),
        evidence_types: BTreeMap::new(),
        signatures: BTreeMap::new(),
        step: None,
        row: EffRow::Empty,
        fresh: &mut fresh,
    };

    let rewritten = threader
        .rewrite_value(&thunk, &Loc::new(), &evs)
        .expect("the quantified producer thunk threads");
    let expected = threaded_thunk_type(thunk.ty(), &plan.ops, &plan, &ids, &env)
        .expect("the signature prepass types the same thunk");

    assert_eq!(rewritten.ty(), &expected);
    let CoreType::Thunk(rewritten_thunk) = rewritten.ty() else {
        panic!("the rewritten value remains a thunk: {:?}", rewritten.ty());
    };
    let CoreType::Function(rewritten_fun) = rewritten_thunk.result() else {
        panic!("the thunk still contains a function: {rewritten_thunk:?}");
    };
    assert_eq!(
        rewritten_fun.quantifiers().first(),
        Some(&CoreQuantifier::Row(source_row)),
        "the source scheme precedes State's appended binders"
    );
}

// A forwarded thunk whose row no longer carries the effect has no declared
// operation instantiation. Even a same-spelled quantifier on the thunk is a
// distinct binder, so the evidence must retain the operation's generic
// scheme rather than manufacture a dependency by name.
#[test]
fn an_unlabelled_forwarded_thunk_does_not_guess_from_a_same_spelled_binder() {
    let operation_element = Sym::new("shadowed_element");
    let thunk_element = Sym::fresh_named(operation_element);
    assert_eq!(operation_element.as_str(), thunk_element.as_str());
    assert_ne!(operation_element, thunk_element);

    let residual = Sym::new("e");
    let operation = Sym::new("emit");
    let mut env = VerifyEnv::new();
    env.insert_operation(
        operation,
        OperationSig::new(
            vec![CoreQuantifier::Type(operation_element)],
            vec![CoreType::Source(Type::Var(operation_element))],
            CoreType::Source(Type::Unit),
            Label {
                name: Sym::new("Emit"),
                args: vec![Type::Var(operation_element)],
            },
        ),
    );
    let plan = plan_over(&[("emit", FoldAKind::Unit)], &env);
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let unit = CoreType::Source(Type::Unit);
    let declared = CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            vec![CoreQuantifier::Type(thunk_element)],
            vec![unit.clone()],
            CompSig::new(unit, EffRow::Var(residual)),
        ))),
        EffRow::Empty,
    )));

    let threaded = threaded_thunk_type(&declared, &plan.ops, &plan, &ids, &env)
        .expect("the forwarded thunk has a threaded type");
    let CoreType::Thunk(thunk) = threaded else {
        panic!("the result remains a thunk: {threaded:?}");
    };
    let CoreType::Function(function) = thunk.result() else {
        panic!("the thunk contains a function: {thunk:?}");
    };
    let CoreType::Thunk(evidence) = &function.params()[1] else {
        panic!(
            "the second parameter is evidence: {:?}",
            function.params()[1]
        );
    };
    let CoreType::Function(clause) = evidence.result() else {
        panic!("the evidence contains a clause: {evidence:?}");
    };
    assert_eq!(
        clause.quantifiers(),
        [CoreQuantifier::Type(operation_element)],
        "without a label the operation clause stays generic"
    );
    assert_eq!(
        clause.params()[0],
        CoreType::Source(Type::Var(operation_element)),
        "printed spelling cannot capture the operation binder"
    );
}

// Ordinary top-level instantiation must stop at the thunk's own rank. The
// inner binder deliberately prints like the outer one, while its Emit label
// makes the threaded evidence depend on the inner identity; instantiating
// the outer scheme at Int must preserve both witnesses unchanged.
#[test]
fn top_level_instantiation_preserves_a_nested_same_spelled_thunk_scheme() {
    let outer_element = Sym::new("ranked_element");
    let inner_element = Sym::fresh_named(outer_element);
    assert_eq!(outer_element.as_str(), inner_element.as_str());
    assert_ne!(outer_element, inner_element);

    let operation_element = Sym::new("operation_element");
    let operation = Sym::new("ranked_emit");
    let mut env = VerifyEnv::new();
    env.insert_operation(
        operation,
        OperationSig::new(
            vec![CoreQuantifier::Type(operation_element)],
            vec![CoreType::Source(Type::Var(operation_element))],
            CoreType::Source(Type::Unit),
            Label {
                name: Sym::new("RankedEmit"),
                args: vec![Type::Var(operation_element)],
            },
        ),
    );
    let plan = plan_over(&[("ranked_emit", FoldAKind::Unit)], &env);
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let unit = CoreType::Source(Type::Unit);
    let declared = CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            vec![CoreQuantifier::Type(inner_element)],
            vec![unit.clone()],
            CompSig::new(
                unit,
                EffRow::Extend(
                    Label {
                        name: Sym::new("RankedEmit"),
                        args: vec![Type::Var(inner_element)],
                    },
                    Box::new(EffRow::Empty),
                ),
            ),
        ))),
        EffRow::Empty,
    )));
    let threaded = threaded_thunk_type(&declared, &plan.ops, &plan, &ids, &env)
        .expect("the nested thunk receives typed evidence");
    let top = CoreFnSig::new(
        vec![CoreQuantifier::Type(outer_element)],
        Vec::new(),
        CompSig::new(threaded, EffRow::Empty),
    );

    let applied = super::instantiate_fn(&top, &[CoreInstantiation::Type(Type::Int)])
        .expect("ordinary top-level instantiation is well-kinded");
    let CoreType::Thunk(thunk) = applied.body().result() else {
        panic!("the top-level result remains a thunk");
    };
    let CoreType::Function(function) = thunk.result() else {
        panic!("the thunk remains callable");
    };
    assert_eq!(
        function.quantifiers().first(),
        Some(&CoreQuantifier::Type(inner_element)),
        "outer instantiation cannot consume the nested binder"
    );
    let CoreType::Thunk(evidence) = &function.params()[1] else {
        panic!("the threaded second parameter is evidence");
    };
    let CoreType::Function(clause) = evidence.result() else {
        panic!("the evidence contains a clause function");
    };
    assert!(clause.quantifiers().is_empty());
    assert_eq!(
        clause.params()[0],
        CoreType::Source(Type::Var(inner_element)),
        "the clause remains dependent on the nested binder"
    );
}

// A read resumes with the accumulator itself, so the operation's declared
// result is the accumulator and pins its type: a producer reading `get` then
// observes it as an `Int`, which a quantifier would make unverifiable.
// A candidate name rebound under an inner Lam must be harvested only at its
// free occurrence, never the shadowed one: the free `x : Int` outside is
// what the bridge would retype, and the inner `x : Bool` is a different
// binder the collector must not confuse for it.
#[test]
fn lexical_collector_respects_inner_shadowing() {
    let int = CoreType::Source(Type::Int);
    let boolean = CoreType::Source(Type::Bool);
    let x_free = TypedValue::new(
        int.clone(),
        TypedValueKind::Var {
            name: Sym::new("x"),
            instantiation: Vec::new(),
        },
    );
    // `return x` where x : Int, then a thunk `\(x : Bool) -> return x`.
    let inner_lam = TypedComp::new(
        CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![boolean.clone()],
                CompSig::new(boolean.clone(), EffRow::Empty),
            ))),
            EffRow::Empty,
        ),
        TypedCompKind::Lam(
            vec![TypedBinder::new(Sym::new("x"), boolean.clone())],
            Box::new(TypedComp::new(
                CompSig::new(boolean.clone(), EffRow::Empty),
                TypedCompKind::Return(TypedValue::new(
                    boolean,
                    TypedValueKind::Var {
                        name: Sym::new("x"),
                        instantiation: Vec::new(),
                    },
                )),
            )),
        ),
    );
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(inner_lam.sig().clone())),
        TypedValueKind::Thunk(Box::new(inner_lam)),
    );
    let body = TypedComp::new(
        CompSig::new(int.clone(), EffRow::Empty),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                CompSig::new(thunk.ty().clone(), EffRow::Empty),
                TypedCompKind::Return(thunk),
            )),
            TypedBinder::new(Sym::new("_t"), CoreType::Source(Type::Unit)),
            Box::new(TypedComp::new(
                CompSig::new(int.clone(), EffRow::Empty),
                TypedCompKind::Return(x_free),
            )),
        ),
    );
    let mut wanted: BTreeSet<Sym> = BTreeSet::new();
    wanted.insert(Sym::new("x"));
    let types = lexical_types(&body, &wanted).expect("no genuine free conflict");
    // The free `x` is captured at its Int occurrence; the inner Bool `x`
    // under the lambda is shadowed and never recorded.
    assert_eq!(types.get(&Sym::new("x")).map(TypedValue::ty), Some(&int));
}

// Cover a candidate shadowed by a WithReuse token and a genuinely free
// occurrence buried under an aggregate and a representation wrapper. The
// collector must exclude the first and find the second.
#[test]
fn lexical_collector_excludes_reuse_token_and_finds_wrapped_free() {
    let int = CoreType::Source(Type::Int);
    let free_ref = TypedValue::new(
        int.clone(),
        TypedValueKind::Var {
            name: Sym::new("y"),
            instantiation: Vec::new(),
        },
    );
    // `y` free, buried under Tuple(.., Reinterpret(y)).
    let wrapped = TypedValue::new(
        CoreType::Source(Type::Tuple(vec![Type::Int])),
        TypedValueKind::Tuple(vec![TypedValue::new(
            int.clone(),
            TypedValueKind::Reinterpret(Box::new(free_ref)),
        )]),
    );
    // A WithReuse whose token is named `y`, shadowing any outer `y` in body.
    let shadow = TypedComp::new(
        CompSig::new(int.clone(), EffRow::Empty),
        TypedCompKind::WithReuse {
            token: TypedBinder::new(
                Sym::new("y"),
                CoreType::ReuseToken(Box::new(CoreType::Source(Type::Unit))),
            ),
            freed: TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit),
            body: Box::new(TypedComp::new(
                CompSig::new(int.clone(), EffRow::Empty),
                TypedCompKind::Return(TypedValue::new(
                    int.clone(),
                    TypedValueKind::Var {
                        name: Sym::new("y"),
                        instantiation: Vec::new(),
                    },
                )),
            )),
        },
    );
    let body = TypedComp::new(
        CompSig::new(int.clone(), EffRow::Empty),
        TypedCompKind::Bind(
            Box::new(shadow),
            TypedBinder::new(Sym::new("_t"), CoreType::Source(Type::Unit)),
            Box::new(TypedComp::new(
                CompSig::new(int.clone(), EffRow::Empty),
                TypedCompKind::Return(wrapped),
            )),
        ),
    );
    let mut wanted: BTreeSet<Sym> = BTreeSet::new();
    wanted.insert(Sym::new("y"));
    let types = lexical_types(&body, &wanted).expect("the free y is unambiguous");
    // Found under the wrapper at Int; the reuse-token-shadowed y is excluded,
    // so no ReuseToken type poisons the capture.
    assert_eq!(types.get(&Sym::new("y")).map(TypedValue::ty), Some(&int));
}

#[test]
fn a_read_pins_the_accumulator_to_its_result() {
    let env = env_with(&[("get", "State", Type::Int), ("put", "State", Type::Unit)]);
    let plan = plan_over(&[("get", FoldAKind::Acc), ("put", FoldAKind::Unit)], &env);
    assert_eq!(
        plan.accumulator_for(&ops(&["get", "put"])),
        Some(Accumulator::Pinned(CoreType::Source(Type::Int)))
    );
}

// One producer threads one accumulator, so two reads it performs cannot pin
// that accumulator to two types. The untyped pass has no types to check and
// threads them together regardless; here it is a decline, not a miscompile.
#[test]
fn one_producer_reading_two_types_declines() {
    let env = env_with(&[("get", "State", Type::Int), ("peek", "Other", Type::Bool)]);
    let plan = plan_over(&[("get", FoldAKind::Acc), ("peek", FoldAKind::Acc)], &env);
    assert_eq!(plan.accumulator_for(&ops(&["get", "peek"])), None);
}

// A nullary producer, the shape a `get`/`put` state handler threads.
fn producer(name: &str) -> TypedCoreFn {
    let unit = CoreType::Source(Type::Unit);
    TypedCoreFn::new(
        Sym::new(name),
        Vec::new(),
        TypedComp::new(
            CompSig::new(unit.clone(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(unit.clone(), TypedValueKind::Unit)),
        ),
        CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(unit, EffRow::Empty)),
        0,
    )
}

// The order a producer's threaded parameters go in, which three separately
// rewritten sites have to agree on: its declaration, its call sites, and the
// accumulator's own type.
#[test]
fn a_producer_takes_its_evidence_then_the_accumulator() {
    let env = env_with(&[("get", "State", Type::Int), ("put", "State", Type::Unit)]);
    let plan = plan_over(&[("get", FoldAKind::Acc), ("put", FoldAKind::Unit)], &env);
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let f = producer("tick");
    let out = plan_producer(&f, &plan.ops, &plan, &ids, &[], &Latent::new(), &env)
        .expect("a plannable producer");

    // `get` sorts before `put`, so the evidence is `ev@0, ev@1`, and the
    // accumulator trails it, the canonical convention pinned by
    // `examples/eff_state.pr`: `fn tick(ev@0, ev@1, st@)`.
    let names: Vec<String> = out
        .params(f.params())
        .iter()
        .map(|p| p.name().as_str().to_string())
        .collect();
    assert_eq!(names, ["ev@0", "ev@1", "st@"]);

    // A read pins the accumulator, so it is concrete and adds no quantifier.
    assert_eq!(out.accumulator.ty(), &CoreType::Source(Type::Int));
    assert_eq!(out.quantifiers, [CoreQuantifier::Row(out.ambient)]);
}

// A nullary operation's clause is not padded with a unit parameter the way an
// evidence clause is. The accumulator is appended to every clause, so a
// nullary operation's clause already takes one argument, and padding it would
// declare an argument the perform site does not pass.
#[test]
fn a_nullary_clause_takes_the_accumulator_alone() {
    let env = env_with(&[("get", "State", Type::Int)]);
    let plan = plan_over(&[("get", FoldAKind::Acc)], &env);
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let f = producer("tick");
    let out = plan_producer(&f, &plan.ops, &plan, &ids, &[], &Latent::new(), &env)
        .expect("a plannable producer");

    let CoreType::Thunk(thunk) = out.evidence[0].ty() else {
        panic!("evidence is a thunk: {:?}", out.evidence[0].ty());
    };
    let CoreType::Function(clause) = thunk.result() else {
        panic!("of a clause function: {:?}", thunk.result());
    };
    assert_eq!(clause.params(), [CoreType::Source(Type::Int)]);
    assert_eq!(clause.body().result(), &CoreType::Source(Type::Int));
}

// A read in tail position is the smallest thing the producer rewrite has to
// get right: `get()` becomes `force(ev@0)(st@)`, an application of the
// operation's clause to the accumulator alone, returning the next
// accumulator. The evidence is forced, not called, and the accumulator is the
// only argument because the operation is nullary.
#[test]
fn a_read_in_tail_position_forces_its_evidence_on_the_accumulator() {
    let env = env_with(&[("get", "State", Type::Int)]);
    let plan = plan_over(&[("get", FoldAKind::Acc)], &env);
    let int = CoreType::Source(Type::Int);
    let st = TypedBinder::new(Sym::from(STATE_ACC), int.clone());
    let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
    evs.insert(Sym::new("get"), Sym::from(names::ev(FIRST_EVIDENCE_ID)));
    let flow = ThunkFlow {
        ret: BTreeMap::new(),
        param: BTreeMap::new(),
    };
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let mut threader = Threader {
        plan: &plan,
        ids: &ids,
        env: &env,
        latent: &Latent::new(),
        flow: &flow,
        drift: &DriftLog::new(true),
        retyped: Retyped::new(),
        evidence_types: BTreeMap::new(),
        signatures: BTreeMap::new(),
        step: None,
        row: EffRow::Empty,
        fresh: &mut Fresh::new(),
    };
    let read = TypedComp::new(
        CompSig::new(int.clone(), EffRow::Empty),
        TypedCompKind::Do {
            operation: Sym::new("get"),
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );

    let out = threader
        .thread_st(&read, &evs, &Loc::new(), &st)
        .expect("a read threads");

    let TypedCompKind::App { callee, args, .. } = out.kind() else {
        panic!("a read becomes an application: {:?}", out.kind());
    };
    assert!(
        matches!(callee.kind(), TypedCompKind::Force(v) if as_var(v) == Some(Sym::from(names::ev(FIRST_EVIDENCE_ID)))),
        "of its forced evidence: {:?}",
        callee.kind()
    );
    assert_eq!(args.len(), 1, "to the accumulator alone");
    assert_eq!(as_var(&args[0]), Some(Sym::from(STATE_ACC)));
    assert_eq!(out.sig().result(), &int, "and it yields the accumulator");
}

// The `put` clause of a parameter-passing state handler, as a typed tree:
// `\(_s) -> k(())(s2)`, whose inner body is `force(k)(()) to k'; force(k')(s2)`.
fn write_clause(acc: Sym, resume: Sym, s2: &TypedBinder) -> TypedComp {
    let unit = CoreType::Source(Type::Unit);
    let int = CoreType::Source(Type::Int);
    let kont = TypedBinder::new(
        Sym::new("k'"),
        CoreType::Thunk(Box::new(CompSig::new(int.clone(), EffRow::Empty))),
    );
    let resumed = TypedComp::new(
        CompSig::new(kont.ty().clone(), EffRow::Empty),
        TypedCompKind::App {
            callee: Box::new(TypedComp::new(
                CompSig::new(kont.ty().clone(), EffRow::Empty),
                TypedCompKind::Force(binder_var(&TypedBinder::new(
                    resume,
                    CoreType::Thunk(Box::new(CompSig::new(kont.ty().clone(), EffRow::Empty))),
                ))),
            )),
            instantiation: Vec::new(),
            args: vec![TypedValue::new(unit, TypedValueKind::Unit)],
        },
    );
    let _ = acc;
    TypedComp::new(
        CompSig::new(int.clone(), EffRow::Empty),
        TypedCompKind::Bind(
            Box::new(resumed),
            kont.clone(),
            Box::new(TypedComp::new(
                CompSig::new(int, EffRow::Empty),
                TypedCompKind::App {
                    callee: Box::new(TypedComp::new(
                        CompSig::new(kont.ty().clone(), EffRow::Empty),
                        TypedCompKind::Force(binder_var(&kont)),
                    )),
                    instantiation: Vec::new(),
                    args: vec![binder_var(s2)],
                },
            )),
        ),
    )
}

// Stripping a write clause: the double application `k(())(s2)` collapses to
// `return s2`, the resume binder is gone, and the resume value was unit, so
// the clause is a write.
//
// The kind is the cross-check that keeps this port honest. It is also what
// the shared `is_fold` reports for the same clause, and the two are computed
// by different code over different trees: this rewrite walks the typed tree,
// and `is_fold` walks the erased one. They must agree, and agreeing on a
// fixture is the weakest form of that; the caller checks it on every program.
#[test]
fn stripping_a_write_clause_leaves_the_new_accumulator() {
    let acc = Sym::new("s");
    let resume = Sym::new("k");
    let s2 = TypedBinder::new(Sym::new("s2"), CoreType::Source(Type::Int));
    let clause = write_clause(acc, resume, &s2);
    let mut aliases: BTreeSet<Sym> = BTreeSet::new();
    aliases.insert(resume);

    let (stripped, kind) = strip_state(&clause, &aliases, acc).expect("a write clause strips");

    assert_eq!(kind, FoldAKind::Unit, "resuming with unit is a write");
    let TypedCompKind::Return(v) = stripped.kind() else {
        panic!("the double application collapses to a return: {stripped:?}");
    };
    assert_eq!(
        as_var(v),
        Some(s2.name()),
        "of the new accumulator the clause resumed into"
    );
    assert!(
        free_comp_vars(&stripped).is_disjoint(&aliases),
        "and the resume binder is gone"
    );
}

// The same clause resuming with the accumulator rather than unit is a read,
// which is what pins the accumulator's type.
#[test]
fn a_clause_resuming_with_the_accumulator_is_a_read() {
    let acc = Sym::new("s");
    assert_eq!(
        a_kind(
            &binder_var(&TypedBinder::new(acc, CoreType::Source(Type::Int))),
            acc
        ),
        Some(FoldAKind::Acc)
    );
    assert_eq!(
        a_kind(
            &TypedValue::new(CoreType::Source(Type::Unit), TypedValueKind::Unit),
            acc
        ),
        Some(FoldAKind::Unit)
    );
    // Resuming with anything else is not a fold this engine admits.
    assert_eq!(
        a_kind(
            &binder_var(&TypedBinder::new(
                Sym::new("other"),
                CoreType::Source(Type::Int)
            )),
            acc
        ),
        None
    );
}

// A read whose result the tail reads: `let n = get() in return n` threads to
// `force(ev@0)(st@) to {n}@st; return st@ to n; return {n}@st`.
//
// Two things are pinned. The bound `n` reads the accumulator that was live
// *before* the read, because that is what a read resumes with, so it is `st@`
// and not the freshly bound one. And the accumulator the tail returns is the
// new one the read produced, so the two names are distinct: getting either
// wrong yields a program that threads a stale state.
#[test]
fn a_read_binds_the_accumulator_that_was_live_before_it() {
    let env = env_with(&[("get", "State", Type::Int)]);
    let plan = plan_over(&[("get", FoldAKind::Acc)], &env);
    let int = CoreType::Source(Type::Int);
    let st = TypedBinder::new(Sym::from(STATE_ACC), int.clone());
    let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
    evs.insert(Sym::new("get"), Sym::from(names::ev(FIRST_EVIDENCE_ID)));
    let flow = ThunkFlow {
        ret: BTreeMap::new(),
        param: BTreeMap::new(),
    };
    let ids = OpIds::assign(&plan.ops).expect("ids");
    let mut threader = Threader {
        plan: &plan,
        ids: &ids,
        env: &env,
        latent: &Latent::new(),
        flow: &flow,
        drift: &DriftLog::new(true),
        retyped: Retyped::new(),
        evidence_types: BTreeMap::new(),
        signatures: BTreeMap::new(),
        step: None,
        row: EffRow::Empty,
        fresh: &mut Fresh::new(),
    };
    let n = TypedBinder::new(Sym::new("n"), int.clone());
    let body = TypedComp::new(
        CompSig::new(int.clone(), EffRow::Empty),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                CompSig::new(int.clone(), EffRow::Empty),
                TypedCompKind::Do {
                    operation: Sym::new("get"),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            )),
            n.clone(),
            Box::new(TypedComp::new(
                CompSig::new(int, EffRow::Empty),
                TypedCompKind::Return(binder_var(&n)),
            )),
        ),
    );

    let out = threader
        .thread_st(&body, &evs, &Loc::new(), &st)
        .expect("a read and its use thread");

    // The outer bind names the accumulator the read produced.
    let TypedCompKind::Bind(head, st2, tail) = out.kind() else {
        panic!("a producing bind stays a bind: {:?}", out.kind());
    };
    assert!(matches!(head.kind(), TypedCompKind::App { .. }));
    assert_ne!(st2.name(), st.name(), "the new accumulator is a fresh name");

    // The tail binds `n` to the accumulator live before the read, then
    // returns the new one.
    let TypedCompKind::Bind(bound, x, rest) = tail.kind() else {
        panic!("the read's result is rebound: {:?}", tail.kind());
    };
    assert_eq!(x.name(), n.name());
    let TypedCompKind::Return(v) = bound.kind() else {
        panic!("from a return: {:?}", bound.kind());
    };
    assert_eq!(
        as_var(v),
        Some(st.name()),
        "of the accumulator live before the read"
    );
    let TypedCompKind::Return(v) = rest.kind() else {
        panic!("and the tail returns: {:?}", rest.kind());
    };
    assert_eq!(
        as_var(v),
        Some(st2.name()),
        "the accumulator the read produced"
    );
}

// The same two reads in one program, but split across producers that share no
// operation: two independent chains, each threading its own accumulator at its
// own type. Asking the question per program would decline this; asking it per
// producer is what makes each chain answerable.
#[test]
fn independent_chains_pin_their_own_accumulators() {
    let env = env_with(&[("get", "State", Type::Int), ("peek", "Other", Type::Bool)]);
    let plan = plan_over(&[("get", FoldAKind::Acc), ("peek", FoldAKind::Acc)], &env);
    assert_eq!(
        plan.accumulator_for(&ops(&["get"])),
        Some(Accumulator::Pinned(CoreType::Source(Type::Int)))
    );
    assert_eq!(
        plan.accumulator_for(&ops(&["peek"])),
        Some(Accumulator::Pinned(CoreType::Source(Type::Bool)))
    );
}
