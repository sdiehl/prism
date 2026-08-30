use super::*;
use crate::core::builtins::FloatOp;
use crate::core::typed::{verify, TypedForward, TypedHandler, UncheckedTypedCore};
use crate::core::Comp;
use prism_syntax::kw;
use prism_syntax::names::ALLOC_EFFECT;

fn source(ty: Type) -> CoreType {
    CoreType::Source(ty)
}

/// Whether a violation says a node has no place in phase `P`.
fn is_illegal_in<P: TypedCorePhase>(error: &CoreViolation) -> bool {
    matches!(error.kind(), Violation::PhaseIllegal { phase, .. } if *phase == P::NAME)
}

fn pure(result: CoreType) -> CompSig {
    CompSig::new(result, EffRow::Empty)
}

fn value(ty: Type, kind: TypedValueKind) -> TypedValue {
    TypedValue::new(source(ty), kind)
}

fn return_value(value: TypedValue) -> TypedComp {
    TypedComp::new(pure(value.ty().clone()), TypedCompKind::Return(value))
}

fn fatal_error(sig: CompSig) -> TypedComp {
    TypedComp::new(
        sig,
        TypedCompKind::Error(value(Type::Str, TypedValueKind::Str("boom".into()))),
    )
}

fn function<P>(body: &TypedComp) -> UncheckedTypedCore<P> {
    UncheckedTypedCore::new(vec![TypedCoreFn::new(
        Sym::new("main"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig().clone()),
        0,
    )])
}

fn local(name: &str, ty: Type) -> TypedValue {
    value(
        ty,
        TypedValueKind::Var {
            name: Sym::new(name),
            instantiation: Vec::new(),
        },
    )
}

#[test]
fn accepts_a_closed_well_typed_program() {
    let body = return_value(value(Type::Int, TypedValueKind::Int(42)));
    let _core = verify(function::<Elaborated>(&body), &VerifyEnv::new())
        .expect("closed well-typed fixture must mint elaborated authority");
}

#[test]
fn case_arms_may_widen_latent_effect_rows_but_not_narrow_them() {
    let row_name = Sym::new("e");
    let closure = |effects| {
        CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
            CoreFnSig::new(
                Vec::new(),
                vec![source(Type::U64)],
                CompSig::new(source(Type::Int), effects),
            ),
        )))))
    };
    let pure_closure = closure(EffRow::Empty);
    let open_closure = closure(EffRow::Var(row_name));
    let program = |arm_ty: CoreType, result_ty: CoreType| {
        let choice = TypedBinder::new(Sym::new("choice"), source(Type::Bool));
        let selected = TypedBinder::new(Sym::new("selected"), arm_ty.clone());
        let arm_value = TypedValue::new(
            arm_ty.clone(),
            TypedValueKind::Var {
                name: selected.name(),
                instantiation: Vec::new(),
            },
        );
        let body = TypedComp::new(
            pure(result_ty.clone()),
            TypedCompKind::Case(
                TypedValue::new(
                    choice.ty().clone(),
                    TypedValueKind::Var {
                        name: choice.name(),
                        instantiation: Vec::new(),
                    },
                ),
                vec![(TypedPattern::Wild, return_value(arm_value))],
            ),
        );
        UncheckedTypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            vec![choice, selected],
            body,
            CoreFnSig::new(
                vec![CoreQuantifier::Row(row_name)],
                vec![source(Type::Bool), arm_ty],
                pure(result_ty),
            ),
            0,
        )])
    };

    let _core = verify(
        program(pure_closure.clone(), open_closure.clone()),
        &VerifyEnv::new(),
    )
    .expect("widening latent effects must mint elaborated authority");
    let errors = verify(program(open_closure, pure_closure), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.path().ends_with("body.arm[0]")
            && matches!(
                error.kind(),
                Violation::TypeMismatch {
                    relation: TypeRelation::Subtype,
                    expected: CoreType::Thunk(_),
                    ..
                }
            )
    }));
}

#[test]
fn rc_sequence_witness_is_confined_to_administrative_owned_binds() {
    let unit = source(Type::Unit);
    let unit_value = || value(Type::Unit, TypedValueKind::Unit);
    // The operation acts on a reference, so every fixture below owns one:
    // `held` is bound around the administrative bind under test.
    let held = || local("held", Type::Unit);
    let owning = |rest: TypedComp| {
        TypedComp::new(
            rest.sig().clone(),
            TypedCompKind::Bind(
                Box::new(return_value(unit_value())),
                TypedBinder::new(Sym::new("held"), unit.clone()),
                Box::new(rest),
            ),
        )
    };
    let sequence = |binder: TypedBinder, rest: TypedComp| {
        owning(TypedComp::new(
            rest.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    pure(unit.clone()),
                    TypedCompKind::Dup(held()),
                )),
                binder,
                Box::new(rest),
            ),
        ))
    };

    let valid = sequence(TypedBinder::rc_sequence(), return_value(unit_value()));
    let valid_core = function::<Owned>(&valid);
    let valid_core =
        verify(valid_core, &VerifyEnv::new()).expect("valid RC sequence must mint owned authority");
    let Comp::Bind(_, _, administrative) = &valid_core.erase().fns[0].body else {
        panic!("expected the owning bind");
    };
    let Comp::Bind(_, erased_binder, _) = &**administrative else {
        panic!("expected erased administrative bind");
    };
    assert_eq!(erased_binder.as_str(), "_");

    // A retain on a value that reads no binding has no owner to act on, so
    // the operation stands on nothing a later consumer could ask about.
    let built_operand = owning(TypedComp::new(
        pure(unit.clone()),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(unit.clone()),
                TypedCompKind::Dup(unit_value()),
            )),
            TypedBinder::rc_sequence(),
            Box::new(return_value(unit_value())),
        ),
    ));
    let errors = verify(function::<Owned>(&built_operand), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(
        |error| error.kind() == &Violation::RcSequence(RcSequenceFault::OperandIsNotAReference)
    ));

    let too_early = sequence(TypedBinder::rc_sequence(), return_value(unit_value()));
    let errors = verify(function::<EffectLowered>(&too_early), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(is_illegal_in::<EffectLowered>));

    let ordinary_first = owning(TypedComp::new(
        pure(unit.clone()),
        TypedCompKind::Bind(
            Box::new(return_value(unit_value())),
            TypedBinder::rc_sequence(),
            Box::new(return_value(unit_value())),
        ),
    ));
    let errors = verify(function::<Owned>(&ordinary_first), &VerifyEnv::new()).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.kind() == &Violation::RcSequence(RcSequenceFault::NotADupOrDrop)));

    let missing_witness = sequence(
        TypedBinder::new(Sym::new(names::RC_SEQUENCE_BINDER), unit.clone()),
        return_value(unit_value()),
    );
    let errors = verify(function::<Owned>(&missing_witness), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(
        |error| error.kind() == &Violation::RcSequence(RcSequenceFault::MissingErasureWitness)
    ));

    let wrong_name = sequence(
        TypedBinder {
            name: Sym::new("wrong"),
            ty: unit.clone(),
            erasure: BinderErasure::RcSequence,
        },
        return_value(unit_value()),
    );
    let errors = verify(function::<Owned>(&wrong_name), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(
        |error| error.kind() == &Violation::RcSequence(RcSequenceFault::WrongReservedIdentity)
    ));

    let wrong_type = sequence(
        TypedBinder {
            name: Sym::new(names::RC_SEQUENCE_BINDER),
            ty: source(Type::Int),
            erasure: BinderErasure::RcSequence,
        },
        return_value(unit_value()),
    );
    let errors = verify(function::<Owned>(&wrong_type), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::TypeMismatch {
            site: Site::At(SITE_RC_SEQUENCE_WITNESS),
            ..
        }
    )));

    let lambda_body = return_value(unit_value());
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![unit.clone()],
            lambda_body.sig().clone(),
        )))),
        TypedCompKind::Lam(vec![TypedBinder::rc_sequence()], Box::new(lambda_body)),
    );
    let errors = verify(function::<Owned>(&lambda), &VerifyEnv::new()).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.kind()
            == &Violation::RcSequence(RcSequenceFault::OutsideAdministrativeBind)));

    let parameter_body = return_value(unit_value());
    let parameter_core = UncheckedTypedCore::<Owned>::new(vec![TypedCoreFn::new(
        Sym::new("parameter"),
        vec![TypedBinder::rc_sequence()],
        parameter_body.clone(),
        CoreFnSig::new(Vec::new(), vec![unit.clone()], parameter_body.sig().clone()),
        0,
    )]);
    let errors = verify(parameter_core, &VerifyEnv::new()).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.kind()
            == &Violation::RcSequence(RcSequenceFault::OutsideAdministrativeBind)));

    let dangling = TypedValue::new(
        unit.clone(),
        TypedValueKind::Var {
            name: Sym::new(names::RC_SEQUENCE_BINDER),
            instantiation: Vec::new(),
        },
    );
    let referenced = sequence(TypedBinder::rc_sequence(), return_value(dangling));
    let errors = verify(function::<Owned>(&referenced), &VerifyEnv::new()).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| matches!(error.kind(), Violation::UnboundReference { .. })));
}

#[test]
fn rc_operands_must_be_countable_values() {
    // A `dup` of a parameter, wrapped in the administrative bind the Owned
    // phase requires, with only the parameter's type varying between cases.
    let dup_of = |operand_ty: CoreType| {
        let held = TypedBinder::new(Sym::new("held"), operand_ty.clone());
        let operand = TypedValue::new(
            operand_ty.clone(),
            TypedValueKind::Var {
                name: held.name(),
                instantiation: Vec::new(),
            },
        );
        let rest = return_value(value(Type::Unit, TypedValueKind::Unit));
        let body = TypedComp::new(
            rest.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    pure(source(Type::Unit)),
                    TypedCompKind::Dup(operand),
                )),
                TypedBinder::rc_sequence(),
                Box::new(rest),
            ),
        );
        UncheckedTypedCore::<Owned>::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            vec![held],
            body.clone(),
            CoreFnSig::new(Vec::new(), vec![operand_ty], body.sig().clone()),
            0,
        )])
    };

    // A linear reuse token is never counted.
    let errors = verify(
        dup_of(CoreType::ReuseToken(Box::new(source(Type::Int)))),
        &VerifyEnv::new(),
    )
    .unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.kind() == &Violation::RcOperand(RcOperandFault::ReuseToken)));

    // An effect row has no runtime value representation to count.
    let errors = verify(dup_of(source(Type::Row(EffRow::Empty))), &VerifyEnv::new()).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.kind() == &Violation::RcOperand(RcOperandFault::NotAValue)));

    // A nominal without declaration evidence is a runtime word whose count
    // the tag bit decides dynamically, so it stays accepted.
    let bare_nominal = dup_of(source(Type::Con(Sym::new("Box"), Vec::new())));
    verify(bare_nominal, &VerifyEnv::new())
        .expect("a nominal without boxing evidence must stay countable");

    // The same nominal with boxing evidence is an allocated cell: also counted.
    let mut env = VerifyEnv::new();
    env.mark_boxed_nominal(Sym::new("Box"));
    verify(dup_of(source(Type::Con(Sym::new("Box"), Vec::new()))), &env)
        .expect("a boxed nominal must stay countable");
}

#[test]
fn rejects_a_drifting_literal_witness() {
    let body = return_value(value(Type::Bool, TypedValueKind::Int(42)));
    let errors = verify(function::<Elaborated>(&body), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::LiteralWitness {
            site: Site::At(SITE_INTEGER_LITERAL),
            ..
        }
    )));
}

#[test]
fn rejects_effect_row_drift() {
    let body = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Io(IoOp::ReadInt, Vec::new()),
    );
    let errors = verify(function::<Elaborated>(&body), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::RowMismatch {
            site: Site::At(SITE_IO_OPERATION),
            ..
        }
    )));
}

#[test]
fn accepts_error_with_arbitrary_well_formed_inherited_witnesses() {
    let inherited = fatal_error(CompSig::new(
        source(Type::Bool),
        EffRow::singleton(prism_syntax::names::IO_EFFECT),
    ));
    let _core = verify(function::<Elaborated>(&inherited), &VerifyEnv::new())
        .expect("well-formed inherited error witnesses must mint authority");
}

#[test]
fn rejects_error_with_an_unbound_result_type_witness() {
    let unbound_result = Sym::new("unbound_error_result");
    let bad_result = fatal_error(pure(source(Type::Var(unbound_result))));
    let bad_result_core = UncheckedTypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
        Sym::new("bad_result"),
        Vec::new(),
        bad_result,
        CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Unit))),
        0,
    )]);
    let errors = verify(bad_result_core, &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.kind()
            == &Violation::UnboundRigid {
                kind: QuantifierKind::Type,
                name: unbound_result,
                ty: Type::Var(unbound_result),
            }
    }));
}

#[test]
fn rejects_error_with_an_unbound_effect_row_witness() {
    let unbound_effects = Sym::new("unbound_error_effects");
    let bad_effects = fatal_error(CompSig::new(
        source(Type::Unit),
        EffRow::Var(unbound_effects),
    ));
    let bad_effects_core = UncheckedTypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
        Sym::new("bad_effects"),
        Vec::new(),
        bad_effects,
        CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Unit))),
        0,
    )]);
    let errors = verify(bad_effects_core, &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.kind()
            == &Violation::UnboundRigidRow {
                name: unbound_effects,
            }
    }));
}

#[test]
fn rejects_a_bind_that_hides_a_child_effect() {
    let unit = source(Type::Unit);
    let io = TypedComp::new(
        CompSig::new(
            unit.clone(),
            EffRow::singleton(prism_syntax::names::IO_EFFECT),
        ),
        TypedCompKind::Io(IoOp::PrintNl, Vec::new()),
    );
    let rest = return_value(value(Type::Unit, TypedValueKind::Unit));
    let hidden = TypedComp::new(
        pure(unit.clone()),
        TypedCompKind::Bind(
            Box::new(io),
            TypedBinder::new(Sym::new("ignored"), unit),
            Box::new(rest),
        ),
    );
    let errors = verify(function::<Elaborated>(&hidden), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::RowMismatch {
            relation: RowRelation::Includes,
            expected,
            ..
        } if expected == &EffRow::singleton(IO_EFFECT)
    )));
}

#[test]
fn rejects_unknown_references_and_duplicate_binders() {
    let binder = TypedBinder::new(Sym::new("x"), source(Type::Int));
    let unknown = value(
        Type::Int,
        TypedValueKind::Var {
            name: Sym::new("missing"),
            instantiation: Vec::new(),
        },
    );
    let lambda_body = return_value(unknown);
    let lambda_sig = CoreFnSig::new(
        Vec::new(),
        vec![source(Type::Int), source(Type::Int)],
        lambda_body.sig().clone(),
    );
    let body = TypedComp::new(
        pure(CoreType::Function(Box::new(lambda_sig))),
        TypedCompKind::Lam(vec![binder.clone(), binder], Box::new(lambda_body)),
    );
    let errors = verify(function::<Elaborated>(&body), &VerifyEnv::new()).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| matches!(error.kind(), Violation::DuplicateBinder { .. })));
    assert!(errors
        .iter()
        .any(|error| matches!(error.kind(), Violation::UnboundReference { .. })));
}

#[test]
fn checks_explicit_polymorphic_call_instantiation() {
    let type_parameter = Sym::new("a");
    let parameter = TypedBinder::new(Sym::new("x"), source(Type::Var(type_parameter)));
    let id_body = return_value(local("x", Type::Var(type_parameter)));
    let id = TypedCoreFn::new(
        Sym::new("id"),
        vec![parameter],
        id_body.clone(),
        CoreFnSig::new(
            vec![CoreQuantifier::Type(type_parameter)],
            vec![source(Type::Var(type_parameter))],
            id_body.sig().clone(),
        ),
        0,
    );
    let call = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Call {
            callee: Sym::new("id"),
            instantiation: vec![CoreInstantiation::Type(Type::Int)],
            args: vec![value(Type::Int, TypedValueKind::Int(1))],
        },
    );
    let main = TypedCoreFn::new(
        Sym::new("main"),
        Vec::new(),
        call.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), call.sig().clone()),
        0,
    );
    let core = UncheckedTypedCore::<Elaborated>::new(vec![id.clone(), main]);
    let _core = verify(core, &VerifyEnv::new())
        .expect("well-kinded explicit instantiation must mint authority");

    let bad_call = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Call {
            callee: Sym::new("id"),
            instantiation: vec![CoreInstantiation::Row(EffRow::Empty)],
            args: vec![value(Type::Int, TypedValueKind::Int(1))],
        },
    );
    let bad_main = TypedCoreFn::new(
        Sym::new("main"),
        Vec::new(),
        bad_call.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), bad_call.sig().clone()),
        0,
    );
    let errors = verify(
        UncheckedTypedCore::<Elaborated>::new(vec![id, bad_main]),
        &VerifyEnv::new(),
    )
    .unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::Instantiation {
            error: InstantiationError::Kind { .. },
            ..
        }
    )));
}

#[test]
fn rejects_constructor_tag_and_field_drift() {
    let parameter = Sym::new("a");
    let mut env = VerifyEnv::new();
    env.insert_constructor(
        Sym::new("Some"),
        ConstructorSig::new(
            vec![CoreQuantifier::Type(parameter)],
            7,
            vec![source(Type::Var(parameter))],
            source(Type::Con(Sym::new("Option"), vec![Type::Var(parameter)])),
        ),
    );
    let option_int = Type::Con(Sym::new("Option"), vec![Type::Int]);
    let constructor = TypedValue::new(
        source(option_int),
        TypedValueKind::Ctor {
            name: Sym::new("Some"),
            tag: 8,
            instantiation: vec![CoreInstantiation::Type(Type::Int)],
            fields: vec![value(Type::Bool, TypedValueKind::Bool(true))],
        },
    );
    let errors = verify(function::<Elaborated>(&return_value(constructor)), &env).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| matches!(error.kind(), Violation::ConstructorTag { declared: 7, .. })));
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::TypeMismatch {
            site: Site::At(SITE_CONSTRUCTOR_FIELD),
            ..
        }
    )));
}

#[test]
fn checks_handler_residual_rows_and_resumption_type() {
    let operation_name = Sym::new("get");
    let effect_name = Sym::new("State");
    let mut env = VerifyEnv::new();
    env.insert_operation(
        operation_name,
        OperationSig::new(
            Vec::new(),
            Vec::new(),
            source(Type::Int),
            Label::bare(effect_name),
        ),
    );
    let handled = TypedComp::new(
        CompSig::new(source(Type::Int), EffRow::singleton(effect_name)),
        TypedCompKind::Do {
            operation: operation_name,
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let outer = pure(source(Type::Int));
    let resume = TypedBinder::new(
        Sym::new("resume"),
        CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], outer.clone()),
        ))))),
    );
    let arm = TypedHandleOp::new(
        operation_name,
        Vec::new(),
        Vec::new(),
        resume,
        return_value(value(Type::Int, TypedValueKind::Int(0))),
    );
    let clauses = TypedHandler::new(vec![arm]).unwrap();
    let body = TypedComp::new(
        outer,
        TypedCompKind::Handle {
            body: Box::new(handled.clone()),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    );
    let _core = verify(function::<Elaborated>(&body), &env)
        .expect("fully handled effects must mint elaborated authority");

    env.insert_operation(
        Sym::new("put"),
        OperationSig::new(
            Vec::new(),
            vec![source(Type::Int)],
            source(Type::Unit),
            Label::bare(effect_name),
        ),
    );
    let residual = CompSig::new(source(Type::Int), EffRow::singleton(effect_name));
    let resume = TypedBinder::new(
        Sym::new("resume_partial"),
        CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
            CoreFnSig::new(Vec::new(), vec![source(Type::Int)], residual.clone()),
        ))))),
    );
    let arm = TypedHandleOp::new(
        operation_name,
        Vec::new(),
        Vec::new(),
        resume,
        return_value(value(Type::Int, TypedValueKind::Int(0))),
    );
    let partial = TypedComp::new(
        residual,
        TypedCompKind::Handle {
            body: Box::new(handled),
            return_binder: None,
            return_body: None,
            ops: TypedHandler::new(vec![arm])
                .unwrap()
                .with_forwarded(vec![TypedForward::new(
                    Sym::new("put"),
                    Label::bare(effect_name),
                )]),
        },
    );
    let _core = verify(function::<Elaborated>(&partial), &env)
        .expect("forwarded residual effects must mint elaborated authority");
}

#[test]
fn rejects_nodes_outside_their_phase() {
    let integer = value(Type::Int, TypedValueKind::Int(1));
    let ref_new = TypedComp::new(
        pure(CoreType::Ref(Box::new(source(Type::Int)))),
        TypedCompKind::RefNew(integer),
    );
    let elaborated_errors =
        verify(function::<Elaborated>(&ref_new), &VerifyEnv::new()).unwrap_err();
    assert!(elaborated_errors.iter().any(is_illegal_in::<Elaborated>));

    let returned = return_value(value(Type::Int, TypedValueKind::Int(1)));
    let mask = TypedComp::new(
        returned.sig().clone(),
        TypedCompKind::Mask(Vec::new(), Box::new(returned)),
    );
    let lowered_errors = verify(function::<EffectLowered>(&mask), &VerifyEnv::new()).unwrap_err();
    assert!(lowered_errors.iter().any(is_illegal_in::<EffectLowered>));
}

// `init_at` is the proof that a cell an allocator handed out now holds a
// constructor. Each premise of that claim is independent, so each is pinned:
// the phase it may appear in, that the cell is the declared `alloc` result,
// that the payload is something a cell can hold, and that the node's own
// witness is the constructor's.
#[test]
fn init_at_checks_every_premise_of_its_claim() {
    let boxed = Type::Con(Sym::new("Boxed"), Vec::new());
    let cell = Type::Con(Sym::new("Arena.Cell"), Vec::new());
    let mut env = VerifyEnv::new();
    env.insert_constructor(
        Sym::new("Boxed"),
        ConstructorSig::new(Vec::new(), 0, Vec::new(), source(boxed.clone())),
    );
    env.insert_operation(
        Sym::new(ALLOC_OP),
        OperationSig::new(
            Vec::new(),
            vec![source(Type::Int)],
            source(cell.clone()),
            Label::bare(ALLOC_EFFECT),
        ),
    );
    let ctor = || {
        TypedValue::new(
            source(boxed.clone()),
            TypedValueKind::Ctor {
                name: Sym::new("Boxed"),
                tag: 0,
                instantiation: Vec::new(),
                fields: Vec::new(),
            },
        )
    };
    let init_at = |cell_value: TypedValue, payload: TypedValue, result: Type| {
        TypedComp::new(
            pure(source(result)),
            TypedCompKind::InitAt(cell_value, payload),
        )
    };
    let good = || init_at(local("c", cell.clone()), ctor(), boxed.clone());
    let in_scope = |body: &TypedComp| {
        TypedComp::new(
            CompSig::new(body.sig().result().clone(), EffRow::singleton(ALLOC_EFFECT)),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(source(cell.clone()), EffRow::singleton(ALLOC_EFFECT)),
                    TypedCompKind::Do {
                        operation: Sym::new(ALLOC_OP),
                        instantiation: Vec::new(),
                        args: vec![value(Type::Int, TypedValueKind::Int(0))],
                    },
                )),
                TypedBinder::new(Sym::new("c"), source(cell.clone())),
                Box::new(body.clone()),
            ),
        )
    };

    // Legal once an arena has been prepared, and never before.
    let _core = verify(function::<ArenaPrepared>(&in_scope(&good())), &env)
        .expect("valid init-at must mint arena-prepared authority");
    let too_early = verify(function::<Elaborated>(&in_scope(&good())), &env).unwrap_err();
    assert!(too_early.iter().any(is_illegal_in::<Elaborated>));

    // The cell must be what this allocator hands out.
    let wrong_cell = in_scope(&init_at(local("c", Type::Int), ctor(), boxed.clone()));
    let errors = verify(function::<ArenaPrepared>(&wrong_cell), &env).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::TypeMismatch {
            site: Site::At(SITE_INIT_AT_CELL),
            ..
        }
    )));

    // A cell holds a constructor, not an arbitrary value.
    let not_a_ctor = in_scope(&init_at(
        local("c", cell.clone()),
        value(Type::Int, TypedValueKind::Int(1)),
        Type::Int,
    ));
    let errors = verify(function::<ArenaPrepared>(&not_a_ctor), &env).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.kind() == &Violation::InitAtPayloadIsNotAllocation));

    // The node returns the constructor it wrote, purely.
    let drifting = in_scope(&init_at(local("c", cell.clone()), ctor(), Type::Int));
    let errors = verify(function::<ArenaPrepared>(&drifting), &env).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::TypeMismatch {
            site: Site::At(SITE_INIT_AT),
            ..
        }
    )));
}

#[test]
fn reference_count_operations_return_unit() {
    let dup = TypedComp::new(
        pure(source(Type::Unit)),
        TypedCompKind::Dup(value(Type::Int, TypedValueKind::Int(1))),
    );
    let _core = verify(function::<Owned>(&dup), &VerifyEnv::new())
        .expect("unit-returning dup must mint owned authority");

    let drifting = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Dup(value(Type::Int, TypedValueKind::Int(1))),
    );
    let errors = verify(function::<Owned>(&drifting), &VerifyEnv::new()).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::TypeMismatch {
            site: Site::At(SITE_DUP),
            ..
        }
    )));
}

#[test]
fn row_instantiation_stacks_duplicate_labels() {
    // An ordinary instantiation row is the demand BEYOND the declared head
    // (the builder's `subsume_row` consumes matching occurrences one-to-one
    // and routes only the surplus into the flexible tail), so substituting
    // `e := {IO}` under a declared `IO` stacks to the two-level `{IO, IO}`.
    let row_parameter = Sym::new("e");
    let signature = CoreFnSig::new(
        vec![CoreQuantifier::Row(row_parameter)],
        Vec::new(),
        CompSig::new(
            source(Type::Unit),
            EffRow::Extend(Label::bare(IO_EFFECT), Box::new(EffRow::Var(row_parameter))),
        ),
    );
    let instantiated = instantiate_fn(
        &signature,
        &[CoreInstantiation::Row(EffRow::singleton(IO_EFFECT))],
    )
    .unwrap();
    let stacked = EffRow::Extend(
        Label::bare(IO_EFFECT),
        Box::new(EffRow::singleton(IO_EFFECT)),
    );
    assert_eq!(instantiated.body().effects(), &stacked);
}

#[test]
fn evidence_row_instantiation_merges_duplicate_labels() {
    // An evidence-row variable is the threading's rewidening artifact: it
    // stands for the residual ambient row at the SAME handler level as the
    // declared head, so an overlapping label merges per-label MAX instead of
    // fabricating a phantom second level.
    let row_parameter = Sym::from(names::evidence_row(&[1]));
    let signature = CoreFnSig::new(
        vec![CoreQuantifier::Row(row_parameter)],
        Vec::new(),
        CompSig::new(
            source(Type::Unit),
            EffRow::Extend(Label::bare(IO_EFFECT), Box::new(EffRow::Var(row_parameter))),
        ),
    );
    let instantiated = instantiate_fn(
        &signature,
        &[CoreInstantiation::Row(EffRow::singleton(IO_EFFECT))],
    )
    .unwrap();
    assert_eq!(instantiated.body().effects(), &EffRow::singleton(IO_EFFECT));
}

#[test]
fn scheme_instantiation_is_simultaneous() {
    let first = Sym::new("a");
    let second = Sym::new("b");
    let signature = CoreFnSig::new(
        vec![CoreQuantifier::Type(first), CoreQuantifier::Type(second)],
        vec![source(Type::Var(first))],
        pure(source(Type::Var(second))),
    );
    let instantiated = instantiate_fn(
        &signature,
        &[
            CoreInstantiation::Type(Type::Var(second)),
            CoreInstantiation::Type(Type::Int),
        ],
    )
    .unwrap();
    assert_eq!(instantiated.params(), &[source(Type::Var(second))]);
    assert_eq!(instantiated.body().result(), &source(Type::Int));
}

#[test]
fn canonical_builtin_signatures_are_checked_without_inference() {
    let sqrt = TypedComp::new(
        pure(source(Type::Float)),
        TypedCompKind::FloatBuiltin(
            FloatOp::Sqrt,
            value(Type::Float, TypedValueKind::Float(4.0)),
        ),
    );
    let _core = verify(function::<Elaborated>(&sqrt), &VerifyEnv::new())
        .expect("canonical float builtin must mint elaborated authority");

    let array_int = Type::Con(Sym::new("Array"), vec![Type::Int]);
    let get = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::StrBuiltin {
            op: Builtin::ArrayGet,
            instantiation: vec![CoreInstantiation::Type(Type::Int)],
            args: vec![
                local("array", array_int.clone()),
                value(Type::Int, TypedValueKind::Int(0)),
            ],
        },
    );
    let array = TypedBinder::new(Sym::new("array"), source(array_int.clone()));
    let core = UncheckedTypedCore::<Elaborated>::new(vec![TypedCoreFn::new(
        Sym::new("main"),
        vec![array],
        get.clone(),
        CoreFnSig::new(Vec::new(), vec![source(array_int)], get.sig().clone()),
        0,
    )]);
    let _core = verify(core, &VerifyEnv::new())
        .expect("canonical array builtin must mint elaborated authority");
}

#[test]
fn reuse_credit_must_be_consumed_once_on_every_branch() {
    let boxed = Type::Con(Sym::new("Boxed"), Vec::new());
    let mut env = VerifyEnv::new();
    env.insert_constructor(
        Sym::new("Boxed"),
        ConstructorSig::new(Vec::new(), 0, Vec::new(), source(boxed.clone())),
    );
    let old = TypedBinder::new(Sym::new("old"), source(boxed.clone()));
    let token = TypedBinder::new(
        Sym::new("token"),
        CoreType::ReuseToken(Box::new(source(boxed.clone()))),
    );
    let rebuild = || {
        TypedValue::new(
            source(boxed.clone()),
            TypedValueKind::Ctor {
                name: Sym::new("Boxed"),
                tag: 0,
                instantiation: Vec::new(),
                fields: Vec::new(),
            },
        )
    };
    let reuse = || {
        TypedComp::new(
            pure(source(boxed.clone())),
            TypedCompKind::Reuse(token.clone(), rebuild()),
        )
    };
    let branches = TypedComp::new(
        pure(source(boxed.clone())),
        TypedCompKind::If(
            value(Type::Bool, TypedValueKind::Bool(true)),
            Box::new(reuse()),
            Box::new(reuse()),
        ),
    );
    let body = TypedComp::new(
        branches.sig().clone(),
        TypedCompKind::WithReuse {
            token: token.clone(),
            freed: local("old", boxed.clone()),
            body: Box::new(branches),
        },
    );
    let make_program = |body: TypedComp| {
        let body = TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Case(
                local("old", boxed.clone()),
                vec![(
                    TypedPattern::Ctor {
                        name: Sym::new("Boxed"),
                        instantiation: Vec::new(),
                        fields: Vec::new(),
                    },
                    body,
                )],
            ),
        );
        UncheckedTypedCore::<ReuseLowered>::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            vec![old.clone()],
            body.clone(),
            CoreFnSig::new(Vec::new(), vec![source(boxed.clone())], body.sig().clone()),
            0,
        )])
    };
    let _core = verify(make_program(body), &env)
        .expect("balanced reuse credits must mint reuse-lowered authority");

    let unbalanced = TypedComp::new(
        pure(source(boxed.clone())),
        TypedCompKind::If(
            value(Type::Bool, TypedValueKind::Bool(true)),
            Box::new(reuse()),
            Box::new(return_value(rebuild())),
        ),
    );
    let unbalanced = TypedComp::new(
        unbalanced.sig().clone(),
        TypedCompKind::WithReuse {
            token,
            freed: local("old", boxed.clone()),
            body: Box::new(unbalanced),
        },
    );
    let errors = verify(make_program(unbalanced), &env).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::Reuse(ReuseFault::UnequalCredits(_))
    )));
}

// The wired nullable frees no cell when matched, so an arm on its
// constructors supplies no shell authority to a with-reuse claim.
#[test]
fn or_null_arm_grants_no_reuse_shell() {
    let element = Type::Int;
    let or_null = Type::OrNull(Box::new(element.clone()));
    let boxed = Type::Con(Sym::new("Boxed"), Vec::new());
    let mut env = VerifyEnv::new();
    env.insert_constructor(
        Sym::new("Boxed"),
        ConstructorSig::new(Vec::new(), 0, Vec::new(), source(boxed.clone())),
    );
    env.insert_constructor(
        Sym::from(kw::CTOR_THIS),
        ConstructorSig::new(
            Vec::new(),
            kw::OR_THIS_TAG,
            vec![source(element.clone())],
            source(or_null.clone()),
        ),
    );
    let old = TypedBinder::new(Sym::new("old"), source(or_null.clone()));
    let token = TypedBinder::new(
        Sym::new("token"),
        CoreType::ReuseToken(Box::new(source(or_null.clone()))),
    );
    let rebuild = value(
        boxed.clone(),
        TypedValueKind::Ctor {
            name: Sym::new("Boxed"),
            tag: 0,
            instantiation: Vec::new(),
            fields: Vec::new(),
        },
    );
    let spend = TypedComp::new(
        pure(source(boxed)),
        TypedCompKind::Reuse(token.clone(), rebuild),
    );
    let claim = TypedComp::new(
        spend.sig().clone(),
        TypedCompKind::WithReuse {
            token,
            freed: local("old", or_null.clone()),
            body: Box::new(spend),
        },
    );
    let body = TypedComp::new(
        claim.sig().clone(),
        TypedCompKind::Case(
            local("old", or_null.clone()),
            vec![(
                TypedPattern::Ctor {
                    name: Sym::from(kw::CTOR_THIS),
                    instantiation: Vec::new(),
                    fields: vec![Some(TypedBinder::new(Sym::new("x"), source(element)))],
                },
                claim,
            )],
        ),
    );
    let program = UncheckedTypedCore::<ReuseLowered>::new(vec![TypedCoreFn::new(
        Sym::new("main"),
        vec![old],
        body.clone(),
        CoreFnSig::new(Vec::new(), vec![source(or_null)], body.sig().clone()),
        0,
    )]);
    let errors = verify(program, &env).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::Reuse(ReuseFault::ScrutineeNotActive)
    )));
}

// The wired nullable allocates no cell, so rebuilding one can never spend a
// reuse token, even inside an otherwise valid shell.
#[test]
fn or_null_rebuild_is_not_an_allocation() {
    let element = Type::Int;
    let or_null = Type::OrNull(Box::new(element.clone()));
    let boxed = Type::Con(Sym::new("Boxed"), Vec::new());
    let mut env = VerifyEnv::new();
    env.insert_constructor(
        Sym::new("Boxed"),
        ConstructorSig::new(
            Vec::new(),
            0,
            vec![source(element.clone())],
            source(boxed.clone()),
        ),
    );
    env.insert_constructor(
        Sym::from(kw::CTOR_THIS),
        ConstructorSig::new(
            Vec::new(),
            kw::OR_THIS_TAG,
            vec![source(element.clone())],
            source(or_null.clone()),
        ),
    );
    let old = TypedBinder::new(Sym::new("old"), source(boxed.clone()));
    let token = TypedBinder::new(
        Sym::new("token"),
        CoreType::ReuseToken(Box::new(source(boxed.clone()))),
    );
    let rebuild = value(
        or_null.clone(),
        TypedValueKind::Ctor {
            name: Sym::from(kw::CTOR_THIS),
            tag: kw::OR_THIS_TAG,
            instantiation: Vec::new(),
            fields: vec![value(element, TypedValueKind::Int(7))],
        },
    );
    let spend = TypedComp::new(
        pure(source(or_null)),
        TypedCompKind::Reuse(token.clone(), rebuild),
    );
    let claim = TypedComp::new(
        spend.sig().clone(),
        TypedCompKind::WithReuse {
            token,
            freed: local("old", boxed.clone()),
            body: Box::new(spend),
        },
    );
    let body = TypedComp::new(
        claim.sig().clone(),
        TypedCompKind::Case(
            local("old", boxed.clone()),
            vec![(
                TypedPattern::Ctor {
                    name: Sym::new("Boxed"),
                    instantiation: Vec::new(),
                    fields: vec![None],
                },
                claim,
            )],
        ),
    );
    let program = UncheckedTypedCore::<ReuseLowered>::new(vec![TypedCoreFn::new(
        Sym::new("main"),
        vec![old],
        body.clone(),
        CoreFnSig::new(Vec::new(), vec![source(boxed)], body.sig().clone()),
        0,
    )]);
    let errors = verify(program, &env).unwrap_err();
    assert!(errors.iter().any(|error| matches!(
        error.kind(),
        Violation::Reuse(ReuseFault::RebuildIsNotAllocation)
    )));
}

#[test]
fn polymorphic_function_subtyping_is_alpha_invariant() {
    let a = Sym::new("a");
    let renamed = Sym::from(prism_syntax::names::typed_quantifier("a", 0));
    let function = |name| {
        CoreType::Function(Box::new(CoreFnSig::new(
            vec![CoreQuantifier::Type(name)],
            vec![source(Type::Var(name))],
            pure(source(Type::Var(name))),
        )))
    };
    assert!(core_subtype(&function(a), &function(renamed)));
    assert!(core_subtype(&function(renamed), &function(a)));
}

#[test]
fn alpha_alignment_does_not_capture_a_free_type_variable() {
    let bound = Sym::new("bound");
    let other_bound = Sym::new("other_bound");
    let free = Sym::new("free");
    let actual = CoreType::Function(Box::new(CoreFnSig::new(
        vec![CoreQuantifier::Type(bound)],
        vec![source(Type::Var(bound)), source(Type::Var(free))],
        pure(source(Type::Var(bound))),
    )));
    let expected = CoreType::Function(Box::new(CoreFnSig::new(
        vec![CoreQuantifier::Type(other_bound)],
        vec![
            source(Type::Var(other_bound)),
            source(Type::Var(other_bound)),
        ],
        pure(source(Type::Var(other_bound))),
    )));
    assert!(!core_subtype(&actual, &expected));
}
