use std::collections::BTreeSet;

use crate::core::cbpv::{Comp, CoreOp, CorePat, Value};
use crate::core::typed::verify::VerifyEnv;
use crate::types::ty::Label;

use super::super::super::{
    verify, CoreFnSig, EffectLowered, Elaborated, TypedCoreFn, TypedHandleOp, TypedHandler,
    UncheckedTypedCore,
};
use super::super::{analysis, fixtures, EffectPlan};
use super::*;

struct MissingRows;

impl Rows for MissingRows {
    fn row(&self, _function: Sym) -> Option<EffRow> {
        None
    }
}

#[test]
fn call_instantiation_rewrites_only_the_answer_row_quantifier() {
    let unrelated = Sym::from("unrelated");
    let answer = Sym::from("answer");
    let signature = CoreFnSig::new(
        vec![CoreQuantifier::Row(unrelated), CoreQuantifier::Row(answer)],
        Vec::new(),
        CompSig::new(
            CoreType::Source(Type::Int),
            EffRow::canonical([Label::bare("Need")], EffRow::Var(answer)),
        ),
    );
    let source = vec![
        CoreInstantiation::Row(EffRow::canonical(
            [Label::bare("Left")],
            EffRow::Var(Sym::from("outer")),
        )),
        CoreInstantiation::Row(EffRow::canonical(
            [Label::bare("Old")],
            EffRow::Var(Sym::from("source")),
        )),
    ];
    let expected_answer = EffRow::canonical(
        [Label::bare("Keep")],
        EffRow::Var(Sym::from(names::FREE_MONAD_ROW)),
    );
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
    let calls = BTreeMap::new();
    let mut fresh = Fresh::new();
    let mut monadic = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls);
    monadic.set_row(EffRow::canonical(
        [Label::bare("Keep"), Label::bare("Need")],
        EffRow::Var(Sym::from(names::FREE_MONAD_ROW)),
    ));
    let rewritten = monadic
        .call_instantiation(&signature, &source)
        .expect("ambient call instantiation");
    assert_eq!(rewritten[0], source[0], "unrelated row stays unchanged");
    assert_eq!(
        rewritten[1],
        CoreInstantiation::Row(expected_answer),
        "only the declaration answer row becomes ambient"
    );

    monadic.set_row(EffRow::canonical(
        [Label::bare("Keep"), Label::bare("Need")],
        EffRow::Var(Sym::from("ordinary")),
    ));
    assert_eq!(
        monadic.call_instantiation(&signature, &source),
        Some(source),
        "outside the free-monad ambient the source instantiation is unchanged"
    );
}

#[test]
fn direct_call_retags_higher_order_arguments_at_the_answer_row() {
    let callee = Sym::from("apply");
    let function = Sym::from("f");
    let answer = Sym::from("answer");
    let source = Sym::from("source");
    let ambient = Sym::from(names::FREE_MONAD_ROW);
    let callable = |row| {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![CoreType::Source(Type::Unit)],
                CompSig::new(CoreType::Source(Type::Int), row),
            ))),
            EffRow::Empty,
        )))
    };
    let declaration = CoreFnSig::new(
        vec![CoreQuantifier::Row(answer)],
        vec![callable(EffRow::Var(answer))],
        CompSig::new(CoreType::Source(Type::Int), EffRow::Var(answer)),
    );
    let source_instantiation = vec![CoreInstantiation::Row(EffRow::Var(source))];
    let source_signature =
        instantiate_fn(&declaration, &source_instantiation).expect("source signature");
    let source_argument = TypedValue::new(
        callable(EffRow::Var(source)),
        TypedValueKind::Var {
            name: function,
            instantiation: Vec::new(),
        },
    );
    let call = TypedComp::new(
        source_signature.body().clone(),
        TypedCompKind::Call {
            callee,
            instantiation: source_instantiation,
            args: vec![source_argument],
        },
    );
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
    let calls = BTreeMap::from([(callee, declaration.clone())]);
    let mut fresh = Fresh::new();
    let mut monadic = Monadic::new(&ops, &mut fresh, EffRow::Var(ambient), &calls);

    let rewritten = monadic.direct(&call).expect("direct call");
    let TypedCompKind::Call {
        instantiation,
        args,
        ..
    } = rewritten.kind()
    else {
        panic!("direct call stays a call");
    };
    let signature = instantiate_fn(&declaration, instantiation).expect("rewritten signature");
    assert_eq!(args[0].ty(), &signature.params()[0]);
    assert_eq!(rewritten.clone().erase(), call.erase());
}

#[test]
fn local_region_rejects_an_incomplete_plan_before_minting_names() {
    let name = Sym::from("member");
    let body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Return(TypedValue::new(
            CoreType::Source(Type::Int),
            TypedValueKind::Int(0),
        )),
    );
    let function = TypedCoreFn::new(
        name,
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    );
    let ops = OpIds::assign(&BTreeSet::new()).expect("the empty operation plan is valid");
    let mut fresh = Fresh::new();
    let error = lower_region(
        &[function],
        &BTreeSet::from([name]),
        &BTreeSet::new(),
        &ops,
        &mut fresh,
        &MissingRows,
    )
    .expect_err("a committed LocalPartial plan requires every residual row");
    assert_eq!(error, Decline::whole(Refusal::MissingRow, name));
    assert_eq!(fresh.bump(), 0, "planning failures cannot consume names");
}

fn source_int_thunk() -> TypedValue {
    let body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Return(TypedValue::new(
            CoreType::Source(Type::Int),
            TypedValueKind::Int(7),
        )),
    );
    let function = CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone());
    let lambda = TypedComp::new(
        CompSig::new(CoreType::Function(Box::new(function)), EffRow::Empty),
        TypedCompKind::Lam(Vec::new(), Box::new(body)),
    );
    TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    )
}

#[test]
fn bind_and_operation_translate_exactly_and_verify() {
    let operation = Sym::from("Ask.ask");
    let mut operation_set = BTreeSet::new();
    operation_set.insert(operation);
    let ops = OpIds::assign(&operation_set).expect("one operation has an id");
    let x = TypedBinder::new(Sym::from("x"), CoreType::Source(Type::Int));
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(41),
            )],
        },
    );
    let returned = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Return(Monadic::var(x.name(), x.ty().clone())),
    );
    let source = TypedComp::new(
        returned.sig().clone(),
        TypedCompKind::Bind(Box::new(performed), x.clone(), Box::new(returned)),
    );
    let mut fresh = Fresh::new();
    let calls = BTreeMap::new();
    let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
        .comp(&source)
        .expect("closed structural translation");
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    );
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(
        UncheckedTypedCore::<EffectLowered>::new(vec![main, abi::ebind_fn(), abi::qapply_fn()]),
        &env,
    )
    .expect("translated bind and operation verify");

    let m = Sym::from(names::lowered("m", 0));
    assert_eq!(
        body.erase(),
        Comp::Bind(
            Box::new(Comp::Return(Value::Ctor(
                Sym::from("EOp"),
                1,
                vec![Value::Int(0), Value::Int(0), Value::Int(41), Value::Unit],
            ))),
            m,
            Box::new(Comp::Call(
                Sym::from("ebind"),
                vec![
                    Value::Var(m),
                    Value::Thunk(Box::new(Comp::Lam(
                        vec![x.name()],
                        Box::new(Comp::Return(Value::Ctor(
                            Sym::from("EPure"),
                            0,
                            vec![Value::Var(x.name())],
                        ))),
                    ))),
                ],
            )),
        )
    );
}

#[test]
fn tuple_fields_keep_their_declared_thunk_witness() {
    let thunk = source_int_thunk();
    let function_type = Type::Fun(Vec::new(), EffRow::Empty, Box::new(Type::Int));
    let tuple = TypedValue::new(
        CoreType::Source(Type::Tuple(vec![function_type.clone()])),
        TypedValueKind::Tuple(vec![thunk.clone()]),
    );
    let unboxed = TypedValue::new(
        CoreType::Source(Type::UnboxedTuple(vec![function_type])),
        TypedValueKind::UnboxedTuple(vec![thunk]),
    );
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
    let calls = BTreeMap::new();
    let mut fresh = Fresh::new();
    let mut monadic = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls);
    let transformed = monadic.value(&tuple).expect("tuple transforms");
    assert_eq!(monadic.value(&unboxed), Some(unboxed));

    let body = TypedComp::new(
        CompSig::new(tuple.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(transformed),
    );
    let function = TypedCoreFn::new(
        Sym::from("tuple_fixture"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    );
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(
        UncheckedTypedCore::<EffectLowered>::new(vec![function]),
        &env,
    )
    .expect("tuple fixture verifies");
}

#[test]
fn a_region_call_retags_a_monadified_thunk_to_its_parameter() {
    let thunk = source_int_thunk();
    let callee_name = Sym::from("consume");
    let callee_signature = CoreFnSig::new(
        Vec::new(),
        vec![thunk.ty().clone()],
        CompSig::new(abi::eff(EffRow::Empty), EffRow::Empty),
    );
    let calls = BTreeMap::from([(callee_name, callee_signature.clone())]);
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty operation map");
    let source_call = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Call {
            callee: callee_name,
            instantiation: Vec::new(),
            args: vec![thunk],
        },
    );
    let mut fresh = Fresh::new();
    let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
        .comp(&source_call)
        .expect("region call transforms");

    let parameter = TypedBinder::new(Sym::from("action"), callee_signature.params()[0].clone());
    let callee_body = abi::epure(
        abi::lowered_repr(
            TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(0)),
            abi::word(),
        ),
        EffRow::Empty,
    );
    let consumer = TypedCoreFn::new(
        callee_name,
        vec![parameter],
        callee_body,
        callee_signature,
        0,
    );
    let invocation = TypedCoreFn::new(
        Sym::from("caller"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    );
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(
        UncheckedTypedCore::<EffectLowered>::new(vec![consumer, invocation]),
        &env,
    )
    .expect("retagged region call verifies");
}

#[test]
fn dynamic_lambda_application_uses_the_monadic_convention() {
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty op table");
    let x = TypedBinder::new(Sym::from("x"), CoreType::Source(Type::Int));
    let returned = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Return(Monadic::var(x.name(), x.ty().clone())),
    );
    let lambda = Monadic::lam(vec![x.clone()], returned);
    let source = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::App {
            callee: Box::new(lambda),
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )],
        },
    );
    let mut fresh = Fresh::new();
    let calls = BTreeMap::new();
    let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
        .comp(&source)
        .expect("dynamic application translates");
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    );
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(UncheckedTypedCore::<EffectLowered>::new(vec![main]), &env)
        .expect("dynamic application verifies");
    assert_eq!(
        body.erase(),
        Comp::App(
            Box::new(Comp::Lam(
                vec![x.name()],
                Box::new(Comp::Return(Value::Ctor(
                    Sym::from("EPure"),
                    0,
                    vec![Value::Var(x.name())],
                ))),
            )),
            vec![Value::Int(7)],
        )
    );
}

#[test]
fn whole_program_direct_calls_share_the_monadic_signature() {
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty op table");
    let x = TypedBinder::new(Sym::from("x"), CoreType::Source(Type::Int));
    let id_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Return(Monadic::var(x.name(), x.ty().clone())),
    );
    let id = TypedCoreFn::new(
        Sym::from("id"),
        vec![x.clone()],
        id_body.clone(),
        CoreFnSig::new(Vec::new(), vec![x.ty().clone()], id_body.sig().clone()),
        0,
    );
    let main_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Call {
            callee: id.name(),
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )],
        },
    );
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        main_body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), main_body.sig().clone()),
        0,
    );
    let mut fresh = Fresh::new();
    let lowered = lower_whole(&[id, main], &ops, &mut fresh, &EffRow::Empty)
        .expect("whole-program convention closes direct calls");
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(
        UncheckedTypedCore::<EffectLowered>::new(lowered.clone()),
        &env,
    )
    .expect("whole-program direct calls verify");
    assert_eq!(
        lowered
            .into_iter()
            .map(|function| function.erase().body)
            .collect::<Vec<_>>(),
        vec![
            Comp::Return(Value::Ctor(
                Sym::from("EPure"),
                0,
                vec![Value::Var(x.name())],
            )),
            Comp::Bind(
                Box::new(Comp::Call(Sym::from("id"), vec![Value::Int(7)])),
                Sym::from(names::lowered("r", 0)),
                Box::new(Comp::Case(
                    Value::Var(Sym::from(names::lowered("r", 0))),
                    vec![
                        (
                            CorePat::Ctor(
                                Sym::from("EPure"),
                                vec![Some(Sym::from(names::lowered("x", 1)))],
                            ),
                            Comp::Return(Value::Var(Sym::from(names::lowered("x", 1)))),
                        ),
                        (
                            CorePat::Ctor(
                                Sym::from("EOp"),
                                vec![
                                    Some(Sym::from(names::lowered("id", 2))),
                                    Some(Sym::from("_us")),
                                    Some(Sym::from("_ua")),
                                    Some(Sym::from("_uk")),
                                ],
                            ),
                            Comp::Error(Value::Str("unhandled effect".into())),
                        ),
                    ],
                )),
            ),
        ]
    );
}

#[test]
fn a_direct_primitive_is_lifted_once_and_exactly() {
    let ops = OpIds::assign(&BTreeSet::new()).expect("empty op table");
    let source = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Prim(
            CoreOp::Add,
            TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
            TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(2)),
        ),
    );
    let calls = BTreeMap::new();
    let mut fresh = Fresh::new();
    let body = Monadic::new(&ops, &mut fresh, EffRow::Empty, &calls)
        .comp(&source)
        .expect("primitive lifts");
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    );
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(UncheckedTypedCore::<EffectLowered>::new(vec![main]), &env)
        .expect("lifted primitive verifies");
    let p = Sym::from(names::lowered("p", 0));
    assert_eq!(
        body.erase(),
        Comp::Bind(
            Box::new(Comp::Prim(CoreOp::Add, Value::Int(1), Value::Int(2))),
            p,
            Box::new(Comp::Return(Value::Ctor(
                Sym::from("EPure"),
                0,
                vec![Value::Var(p)],
            ))),
        )
    );
}

#[test]
fn a_captured_open_nary_handler_erases_exactly_to_the_executable_driver() {
    let operation = Sym::from("Ask.ask");
    let escaping = Sym::from("Leak.leak");
    let mut operation_set = BTreeSet::new();
    operation_set.insert(operation);
    operation_set.insert(escaping);
    let ops = OpIds::assign(&operation_set).expect("two operations have ids");
    let captured_a = TypedBinder::new(Sym::from("a_offset"), CoreType::Source(Type::Int));
    let captured_z = TypedBinder::new(Sym::from("z_offset"), CoreType::Source(Type::Int));
    let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
    let extra = TypedBinder::new(Sym::from("unused_extra"), CoreType::Source(Type::Int));
    let resume_signature = CoreFnSig::new(
        Vec::new(),
        vec![CoreType::Source(Type::Int)],
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
    );
    let resume = TypedBinder::new(
        Sym::from("resume"),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(resume_signature)),
            EffRow::Empty,
        ))),
    );
    let clause_result = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Prim(
            CoreOp::Add,
            Monadic::var(parameter.name(), parameter.ty().clone()),
            Monadic::var(captured_a.name(), captured_a.ty().clone()),
        ),
    );
    let escaped = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
        TypedCompKind::Do {
            operation: escaping,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let clause_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Leak")),
        TypedCompKind::Bind(
            Box::new(escaped),
            TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
            Box::new(clause_result),
        ),
    );
    let clause = TypedHandleOp::new(
        operation,
        Vec::new(),
        vec![parameter, extra],
        resume,
        clause_body,
    );
    let clauses = TypedHandler::new(vec![clause]).expect("one unique clause");
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: vec![
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(9)),
            ],
        },
    );
    let handle_comp = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Handle {
            body: Box::new(performed),
            return_binder: Some(TypedBinder::new(
                Sym::from("answer"),
                CoreType::Source(Type::Int),
            )),
            return_body: Some(Box::new(TypedComp::new(
                CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                TypedCompKind::Prim(
                    CoreOp::Add,
                    Monadic::var(Sym::from("answer"), CoreType::Source(Type::Int)),
                    Monadic::var(captured_z.name(), captured_z.ty().clone()),
                ),
            ))),
            ops: clauses,
        },
    );
    let source_body = TypedComp::new(
        handle_comp.sig().clone(),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                TypedCompKind::Return(TypedValue::new(
                    CoreType::Source(Type::Int),
                    TypedValueKind::Int(40),
                )),
            )),
            captured_z,
            Box::new(TypedComp::new(
                handle_comp.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
                        TypedCompKind::Return(TypedValue::new(
                            CoreType::Source(Type::Int),
                            TypedValueKind::Int(2),
                        )),
                    )),
                    captured_a,
                    Box::new(handle_comp),
                ),
            )),
        ),
    );
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        source_body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), source_body.sig().clone()),
        0,
    );
    let source = UncheckedTypedCore::<Elaborated>::new(vec![main]);
    let mut fresh = Fresh::new();
    let mut lowered = lower_whole(source.functions(), &ops, &mut fresh, &EffRow::Empty)
        .expect("open handler translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("open handler output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_routed_resume_application_erases_exactly_and_verifies() {
    let operation = Sym::from("Ask.ask");
    let escaping = Sym::from("Leak.leak");
    let operation_set = BTreeSet::from([operation, escaping]);
    let ops = OpIds::assign(&operation_set).expect("two operations have ids");
    let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
    let resume_signature = CoreFnSig::new(
        Vec::new(),
        vec![CoreType::Source(Type::Int)],
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
    );
    let resume = TypedBinder::new(
        Sym::from("resume"),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(resume_signature.clone())),
            EffRow::Empty,
        ))),
    );
    let routed = TypedBinder::new(Sym::from("routed_resume"), resume.ty().clone());
    let route = TypedComp::new(
        CompSig::new(resume.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(Monadic::var(resume.name(), resume.ty().clone())),
    );
    let force = TypedComp::new(
        CompSig::new(
            CoreType::Function(Box::new(resume_signature)),
            EffRow::Empty,
        ),
        TypedCompKind::Force(Monadic::var(routed.name(), routed.ty().clone())),
    );
    let apply = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![Monadic::var(parameter.name(), parameter.ty().clone())],
        },
    );
    let routed_body = TypedComp::new(
        apply.sig().clone(),
        TypedCompKind::Bind(Box::new(route), routed, Box::new(apply)),
    );
    let escaped = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
        TypedCompKind::Do {
            operation: escaping,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let clause_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Leak")),
        TypedCompKind::Bind(
            Box::new(escaped),
            TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
            Box::new(routed_body),
        ),
    );
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        operation,
        Vec::new(),
        vec![parameter],
        resume,
        clause_body,
    )])
    .expect("one unique clause");
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )],
        },
    );
    let handled = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Handle {
            body: Box::new(performed),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    );
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        handled.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), handled.sig().clone()),
        0,
    );
    let source = UncheckedTypedCore::<Elaborated>::new(vec![main]);
    let mut fresh = Fresh::new();
    let mut lowered = lower_whole(source.functions(), &ops, &mut fresh, &EffRow::Empty)
        .expect("routed resume application translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("routed resume output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_mask_driver_erases_exactly_and_verifies() {
    let operation = Sym::from("Ask.ask");
    let operation_set = BTreeSet::from([operation]);
    let ops = OpIds::assign(&operation_set).expect("one operation has an id");
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )],
        },
    );
    let masked = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Mask(vec![operation], Box::new(performed)),
    );
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        masked.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), masked.sig().clone()),
        0,
    );
    let source = UncheckedTypedCore::<Elaborated>::new(vec![main]);
    let mut fresh = Fresh::new();
    let mut lowered = lower_whole(source.functions(), &ops, &mut fresh, &EffRow::Empty)
        .expect("mask driver translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("mask driver output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_selective_closed_handler_keeps_the_direct_convention_exactly() {
    let operation = Sym::from("Ask.ask");
    let operation_set = BTreeSet::from([operation]);
    let ops = OpIds::assign(&operation_set).expect("one operation has an id");
    let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
    let resume_signature = CoreFnSig::new(
        Vec::new(),
        vec![CoreType::Source(Type::Int)],
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
    );
    let resume = TypedBinder::new(
        Sym::from("resume"),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(resume_signature)),
            EffRow::Empty,
        ))),
    );
    let clause_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Return(Monadic::var(parameter.name(), parameter.ty().clone())),
    );
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        operation,
        Vec::new(),
        vec![parameter],
        resume,
        clause_body,
    )])
    .expect("one unique clause");
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )],
        },
    );
    let handled = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Handle {
            body: Box::new(performed),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    );
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        handled.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), handled.sig().clone()),
        0,
    );
    let source = UncheckedTypedCore::<Elaborated>::new(vec![main]);
    let effects = EffectPlan::analyze(source.functions());
    let latent = effects.latent();
    let plan = analysis::plan(source.functions(), &effects, false);
    assert_eq!(plan.scope, MonadicScope::Selective);

    let mut fresh = Fresh::new();
    let mut lowered = lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &Region {
            plan: &plan,
            latent,
            flow: effects.flow(),
            native_enabled: false,
        },
    )
    .expect("selective closed handler translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("selective closed-handler output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_closed_tail_resume_and_return_clause_use_the_native_region_exactly() {
    let operation = Sym::from("Ask.ask");
    let operation_set = BTreeSet::from([operation]);
    let ops = OpIds::assign(&operation_set).expect("one operation has an id");
    let parameter = TypedBinder::new(Sym::from("question"), CoreType::Source(Type::Int));
    let resume_signature = CoreFnSig::new(
        Vec::new(),
        vec![CoreType::Source(Type::Int)],
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
    );
    let resume = TypedBinder::new(
        Sym::from("resume"),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(resume_signature.clone())),
            EffRow::Empty,
        ))),
    );
    let force = TypedComp::new(
        CompSig::new(
            CoreType::Function(Box::new(resume_signature)),
            EffRow::Empty,
        ),
        TypedCompKind::Force(Monadic::var(resume.name(), resume.ty().clone())),
    );
    let clause_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![Monadic::var(parameter.name(), parameter.ty().clone())],
        },
    );
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        operation,
        Vec::new(),
        vec![parameter],
        resume,
        clause_body,
    )])
    .expect("one unique clause");
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: vec![TypedValue::new(
                CoreType::Source(Type::Int),
                TypedValueKind::Int(7),
            )],
        },
    );
    let return_binder = TypedBinder::new(Sym::from("answer"), CoreType::Source(Type::Int));
    let return_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Prim(
            CoreOp::Add,
            Monadic::var(return_binder.name(), return_binder.ty().clone()),
            TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(1)),
        ),
    );
    let handled = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Int), EffRow::Empty),
        TypedCompKind::Handle {
            body: Box::new(performed),
            return_binder: Some(return_binder),
            return_body: Some(Box::new(return_body)),
            ops: clauses,
        },
    );
    let main = TypedCoreFn::new(
        Sym::from("main"),
        Vec::new(),
        handled.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), handled.sig().clone()),
        0,
    );
    let source = UncheckedTypedCore::<Elaborated>::new(vec![main]);
    let effects = EffectPlan::analyze(source.functions());
    let latent = effects.latent();
    let plan = analysis::plan(source.functions(), &effects, false);
    let mut fresh = Fresh::new();
    let mut lowered = lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &Region {
            plan: &plan,
            latent,
            flow: effects.flow(),
            native_enabled: true,
        },
    )
    .expect("native selective handler translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("native-region output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_generic_capture_is_scoped_by_the_generated_driver_scheme() {
    let operation = Sym::from("Ask.ask");
    let escaping = Sym::from("Leak.leak");
    let mut operation_set = BTreeSet::new();
    operation_set.insert(operation);
    operation_set.insert(escaping);
    let ops = OpIds::assign(&operation_set).expect("two operations have ids");

    let a = Sym::from("a");
    let captured = TypedBinder::new(Sym::from("captured"), CoreType::Source(Type::Var(a)));
    let resume_signature = CoreFnSig::new(
        Vec::new(),
        vec![CoreType::Source(Type::Var(a))],
        CompSig::new(CoreType::Source(Type::Var(a)), EffRow::Empty),
    );
    let resume = TypedBinder::new(
        Sym::from("resume"),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(resume_signature)),
            EffRow::Empty,
        ))),
    );
    let escaped = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton("Leak")),
        TypedCompKind::Do {
            operation: escaping,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let clause_result = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Var(a)), EffRow::Empty),
        TypedCompKind::Return(Monadic::var(captured.name(), captured.ty().clone())),
    );
    let clause_body = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Var(a)), EffRow::singleton("Leak")),
        TypedCompKind::Bind(
            Box::new(escaped),
            TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
            Box::new(clause_result),
        ),
    );
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        operation,
        Vec::new(),
        Vec::new(),
        resume,
        clause_body,
    )])
    .expect("one unique clause");
    let performed = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Var(a)), EffRow::singleton("Ask")),
        TypedCompKind::Do {
            operation,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let handle = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Var(a)), EffRow::Empty),
        TypedCompKind::Handle {
            body: Box::new(performed),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    );
    let run = TypedCoreFn::new(
        Sym::from("run"),
        vec![captured.clone()],
        handle.clone(),
        CoreFnSig::new(
            vec![CoreQuantifier::Type(a)],
            vec![captured.ty().clone()],
            handle.sig().clone(),
        ),
        0,
    );

    let mut fresh = Fresh::new();
    let mut lowered = lower_whole(&[run], &ops, &mut fresh, &EffRow::Empty)
        .expect("generic captured handler translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("generic captured-handler output verifies");
}

#[test]
fn a_confined_region_translates_and_leaves_no_raw_effects() {
    let ops = OpIds::assign(&BTreeSet::from([Sym::from(fixtures::ASK_OP)]))
        .expect("one operation has an id");
    let functions = fixtures::capturing_program();
    let source = UncheckedTypedCore::<Elaborated>::new(functions);
    let effects = EffectPlan::analyze(source.functions());
    let plan = analysis::plan(source.functions(), &effects, false);
    assert_eq!(plan.scope, MonadicScope::Selective);
    assert!(
        !plan.members.contains(&Sym::from(ENTRY_POINT)),
        "the capturer stays outside the region"
    );

    let mut fresh = Fresh::new();
    let mut lowered = lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &Region {
            plan: &plan,
            latent: effects.latent(),
            flow: effects.flow(),
            native_enabled: false,
        },
    )
    .expect("the confined region translates");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("confined-region output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_region_reaching_through_an_island_handler_translates_and_verifies() {
    // The forwarder forces what it is handed from inside a handler for an
    // unrelated operation, so the operation the computation performs is in
    // no row the forwarder's own body discharges. The thunk is still built
    // at the monadic convention, and the bind inside it still suspends at
    // the row its body performs, which is the pairing the verifier checks.
    let ops = OpIds::assign(&BTreeSet::from([
        Sym::from(fixtures::ASK_OP),
        Sym::from(fixtures::LEAK_OP),
    ]))
    .expect("both operations have ids");
    let source = UncheckedTypedCore::<Elaborated>::new(fixtures::island_program());
    let effects = EffectPlan::analyze(source.functions());
    let plan = analysis::plan(source.functions(), &effects, false);
    assert_eq!(plan.scope, MonadicScope::Selective);
    assert!(plan.members.contains(&Sym::from(fixtures::RUN)));

    let mut fresh = Fresh::new();
    let mut lowered = lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &Region {
            plan: &plan,
            latent: effects.latent(),
            flow: effects.flow(),
            native_enabled: true,
        },
    )
    .expect("the region reaches through the island handler");
    lowered.push(abi::ebind_fn());
    lowered.push(abi::qapply_fn());
    let mut env = VerifyEnv::new();
    abi::insert(&mut env);
    let typed = verify(UncheckedTypedCore::<EffectLowered>::new(lowered), &env)
        .expect("island-handler output verifies");
    crate::core::residual_effects(&typed.erase()).expect("no raw effects survive");
}

#[test]
fn a_clause_handing_its_continuation_to_direct_code_declines_the_region() {
    // The clause suspends a resume application and passes it to a
    // declaration outside the region, which is the shape a clause takes
    // when something else decides how often to resume. The region reifies
    // that continuation, so the suspension holds a binder of the region's
    // own shape where the direct convention describes a source function. A
    // continuation performs whatever the computation it resumes performs,
    // so no flow fact reports this and the builder is the only place that
    // can see the value cross the boundary.
    let refusal = refusal_of(
        fixtures::resume_capturing_program(),
        &confined(&[fixtures::BUMP, fixtures::HELPER]),
    );
    assert_eq!(
        refusal,
        Decline::whole(Refusal::ThunkBoundary, Sym::from(fixtures::HELPER)),
    );
}

#[test]
fn a_direct_thunk_reading_a_reified_binder_declines_the_region() {
    // The member binds what the operation answers, which the transform
    // reifies into a word parameter of the continuation, and hands a
    // suspension reading that binder to a declaration outside the region.
    // The suspension performs nothing, so it stays at the direct
    // convention and is copied verbatim: no crossing reaches the reference
    // inside it, and the copy would read the binder at its source type
    // where the word is what is in scope.
    let refusal = refusal_of(
        fixtures::word_capturing_program(),
        &confined(&[fixtures::HELPER]),
    );
    assert_eq!(
        refusal,
        Decline::whole(Refusal::WordCapture, Sym::from(fixtures::HELPER)),
    );
}

#[test]
fn a_performing_handler_answering_with_a_transformer_declines_the_region() {
    // The clause answers with a lambda for the code around the handle to
    // apply, and that lambda still performs, so the region rewrites it at
    // the monadic convention. The answer leaves the driver as an ordinary
    // value word: the source type names a function, the monadic bind erases
    // the binder holding it, and the driver's pure arm answers with a
    // transformer built at the direct convention, so no use site can read
    // back which convention it holds. Applying it directly would consume an
    // effect cell as a result, which is a wrong value rather than a crash.
    let refusal = refusal_of(
        fixtures::transformer_answer_program(),
        &confined(&[fixtures::BUMP, fixtures::HELPER]),
    );
    assert_eq!(
        refusal,
        Decline::whole(Refusal::HandlerAnswer, Sym::from(fixtures::HELPER)),
    );
}

#[test]
fn a_region_missing_a_forcer_declines_instead_of_mixing_conventions() {
    let ops = OpIds::assign(&BTreeSet::from([Sym::from(fixtures::ASK_OP)]))
        .expect("one operation has an id");
    let functions = fixtures::capturing_program();
    let source = UncheckedTypedCore::<Elaborated>::new(functions);
    let effects = EffectPlan::analyze(source.functions());
    let mut plan = analysis::plan(source.functions(), &effects, false);
    // Hand-narrow the region to drop the forwarder. Nothing in the planner
    // produces this shape; the point is that if anything ever did, the
    // builder refuses to emit direct code that forces a monadic thunk
    // rather than emitting a program whose two halves disagree.
    assert!(plan.members.remove(&Sym::from(fixtures::RUN)));
    plan.monadic_params.remove(&Sym::from(fixtures::RUN));

    let mut fresh = Fresh::new();
    let refusal = lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &Region {
            plan: &plan,
            latent: effects.latent(),
            flow: effects.flow(),
            native_enabled: false,
        },
    )
    .expect_err("forcing a monadic thunk from direct code declines the region");
    assert_eq!(
        refusal,
        Decline::new(
            Refusal::DirectForce,
            Sym::from(fixtures::RUN),
            Site::Name(Sym::from("action")),
        ),
        "the refusal names the forwarder and the parameter it forces"
    );
}

/// A region confined to exactly these declarations. The refusals below turn
/// on shapes no planner produces, so the plan is written rather than
/// derived from the program it is applied to.
fn confined(members: &[&str]) -> MonadicRegionPlan {
    let members: BTreeSet<Sym> = members.iter().copied().map(Sym::from).collect();
    MonadicRegionPlan {
        genuine_effects: members.clone(),
        members,
        entries: BTreeSet::new(),
        monadic_params: BTreeMap::new(),
        scope: MonadicScope::Selective,
    }
}

/// Run the confined builder over a hand-written program and region, and
/// report the refusal it recorded.
fn refusal_of(functions: Vec<TypedCoreFn>, plan: &MonadicRegionPlan) -> Decline {
    let ops = OpIds::assign(&BTreeSet::from([
        Sym::from(fixtures::ASK_OP),
        Sym::from(fixtures::LEAK_OP),
    ]))
    .expect("both operations have ids");
    let source = UncheckedTypedCore::<Elaborated>::new(functions);
    let effects = EffectPlan::analyze(source.functions());
    let mut fresh = Fresh::new();
    lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &EffRow::Empty,
        &Region {
            plan,
            latent: effects.latent(),
            flow: effects.flow(),
            native_enabled: false,
        },
    )
    .expect_err("the confined builder refuses this program")
}

#[test]
fn a_cell_holding_a_computation_the_region_owns_declines_the_region() {
    // Storing the suspension in a reference is a form the rewrite copies
    // verbatim, so copying it would leave the source-convention closure
    // where every force of it expects an effect cell.
    let stashed = fixtures::nullary_thunk(fixtures::call(
        fixtures::BUMP,
        Vec::new(),
        fixtures::asking(),
    ));
    let stash = TypedComp::new(
        CompSig::new(CoreType::Ref(Box::new(stashed.ty().clone())), EffRow::Empty),
        TypedCompKind::RefNew(stashed),
    );
    let refusal = refusal_of(
        vec![
            fixtures::named(fixtures::BUMP, Vec::new(), fixtures::performed()),
            fixtures::named(fixtures::HELPER, Vec::new(), stash),
        ],
        &confined(&[fixtures::BUMP]),
    );
    assert_eq!(
        refusal,
        Decline::whole(Refusal::DirectHolds, Sym::from(fixtures::HELPER)),
    );
}

#[test]
fn a_form_the_confined_builder_cannot_rewrite_declines_the_region() {
    // An open handler is not a convention crossing at all: the confined
    // builder simply has no rewrite for one, and the whole-program builder
    // is the one that handles it.
    let leaking = fixtures::handling_ask(
        fixtures::call(fixtures::BUMP, Vec::new(), fixtures::asking()),
        true,
    );
    let refusal = refusal_of(
        vec![
            fixtures::named(fixtures::BUMP, Vec::new(), fixtures::performed()),
            fixtures::named(fixtures::HELPER, Vec::new(), leaking),
        ],
        &confined(&[fixtures::BUMP]),
    );
    assert_eq!(
        refusal,
        Decline::whole(Refusal::UnsupportedForm, Sym::from(fixtures::HELPER)),
    );
}

#[test]
fn a_member_with_no_residual_row_declines_before_minting_names() {
    let ops = OpIds::assign(&BTreeSet::from([Sym::from(fixtures::ASK_OP)]))
        .expect("one operation has an id");
    let source = UncheckedTypedCore::<Elaborated>::new(fixtures::capturing_program());
    let effects = EffectPlan::analyze(source.functions());
    let plan = analysis::plan(source.functions(), &effects, false);
    let mut fresh = Fresh::new();
    let refusal = lower_selective(
        source.functions(),
        &ops,
        &mut fresh,
        &MissingRows,
        &Region {
            plan: &plan,
            latent: effects.latent(),
            flow: effects.flow(),
            native_enabled: false,
        },
    )
    .expect_err("a member needs a residual row for its monadic signature");
    assert_eq!(
        refusal,
        Decline::whole(Refusal::MissingRow, Sym::from(fixtures::BUMP)),
    );
    assert_eq!(fresh.bump(), 0, "planning failures cannot consume names");
}

#[test]
fn a_slot_reached_at_two_conventions_declines_the_region() {
    // The forwarder's slot is driven at the monadic convention because one
    // call site fills it with a computation that performs. A second site
    // fills the same slot with one that only declares the row and performs
    // nothing, which the flow solution leaves at the direct convention. A
    // thunk carries no convention in its type, so there is nothing to
    // retag and no coercion to insert: the region declines.
    let quiet = fixtures::nullary_thunk(TypedComp::new(
        CompSig::new(fixtures::int(), fixtures::asking()),
        TypedCompKind::Return(TypedValue::new(
            fixtures::int(),
            TypedValueKind::Int(0.into()),
        )),
    ));
    let mut functions = fixtures::capturing_program();
    functions.push(fixtures::named(
        fixtures::HELPER,
        Vec::new(),
        fixtures::call(fixtures::RUN, vec![quiet], fixtures::asking()),
    ));
    let source = UncheckedTypedCore::<Elaborated>::new(functions);
    let effects = EffectPlan::analyze(source.functions());
    let plan = analysis::plan(source.functions(), &effects, false);
    assert_eq!(
        plan.monadic_params.get(&Sym::from(fixtures::RUN)),
        Some(&BTreeSet::from([0])),
        "the performing call site is what makes the slot monadic",
    );
    let refusal = refusal_of(source.into_functions(), &plan);
    assert_eq!(
        refusal,
        Decline::whole(Refusal::ThunkBoundary, Sym::from(fixtures::HELPER)),
    );
}
