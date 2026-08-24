//! Fixtures for reference-count insertion.

use crate::core::{Comp, Value};
use crate::types::ty::{EffRow, Label};
use crate::types::Type;
use prism_syntax::names::{self, ALLOC_OP};

use super::super::specialize_support::{binder_occurrence, count_free_comp_var_visits};
use super::super::verify::{OperationSig, VerifyEnv};
use super::super::{
    verify, CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType,
    TypedHandler, TypedValue, TypedValueKind, UncheckedTypedCore,
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

fn function(name: &str, params: Vec<TypedBinder>, body: TypedComp) -> TypedCoreFn {
    let signature = CoreFnSig::new(
        Vec::new(),
        params.iter().map(|binder| binder.ty.clone()).collect(),
        body.sig.clone(),
    );
    TypedCoreFn::new(sym(name), params, body, signature, 0)
}

fn head_dup<'a>(comp: &'a Comp, name: &str) -> &'a Comp {
    let Comp::Bind(op, binder, rest) = comp else {
        panic!("expected a leading dup, found {comp:?}");
    };
    assert_eq!(binder.as_str(), "_");
    assert!(matches!(
        &**op,
        Comp::Dup(Value::Var(actual)) if *actual == sym(name)
    ));
    rest
}

fn head_drop<'a>(comp: &'a Comp, name: &str) -> &'a Comp {
    let Comp::Bind(op, binder, rest) = comp else {
        panic!("expected a leading drop, found {comp:?}");
    };
    assert_eq!(binder.as_str(), "_");
    assert!(matches!(
        &**op,
        Comp::Drop(Value::Var(actual)) if *actual == sym(name)
    ));
    rest
}

fn run_and_verify(
    input: UncheckedTypedCore<EffectLowered>,
    sigs: &Sigs,
    env: &VerifyEnv,
) -> TypedCore<Owned> {
    let input = verify(input, env)
        .unwrap_or_else(|violations| panic!("input fixture is invalid: {violations:#?}"));
    verify(insert_rc(input, sigs), env)
        .unwrap_or_else(|violations| panic!("owned typed Core is invalid: {violations:#?}"))
}

// `EffectLowered` promises that no source handler remains. The verifier must
// refuse to mint that authority before RC can see the invalid tree.
#[test]
fn surviving_handle_cannot_mint_rc_input_authority() {
    let unit = source(Type::Unit);
    let body = ret(TypedValue::new(unit.clone(), TypedValueKind::Unit));
    let handled = TypedComp::new(
        pure(unit),
        TypedCompKind::Handle {
            body: Box::new(body),
            return_binder: None,
            return_body: None,
            ops: TypedHandler::new(Vec::new()).unwrap(),
        },
    );
    let input =
        UncheckedTypedCore::<EffectLowered>::new(vec![function("main", Vec::new(), handled)]);
    verify(input, &VerifyEnv::new()).expect_err("a surviving handler must remain unchecked");
}

#[test]
fn borrow_masks_preserve_the_calling_convention() {
    let int = source(Type::Int);
    let parameter = TypedBinder::new(sym("borrowed"), int.clone());
    let body = ret(var("borrowed", int));
    let observe = function("observe", vec![parameter], body);
    let retained = TypedBinder::new(sym("retained"), source(Type::Int));
    let call = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Call {
            callee: sym("observe"),
            instantiation: Vec::new(),
            args: vec![var("retained", source(Type::Int))],
        },
    );
    let caller = function("caller", vec![retained], call);
    let input = UncheckedTypedCore::new(vec![observe, caller]);
    let sigs = std::iter::once((sym("observe"), vec![true])).collect();
    let actual = run_and_verify(input, &sigs, &VerifyEnv::new()).erase();
    let observe_rest = head_dup(&actual.fns[0].body, "borrowed");
    assert!(matches!(
        observe_rest,
        Comp::Return(Value::Var(name)) if *name == sym("borrowed")
    ));
    let Comp::Bind(call, result, post) = &actual.fns[1].body else {
        panic!("borrowed tail call must retain its argument through the call");
    };
    assert!(matches!(
        &**call,
        Comp::Call(name, args)
            if *name == sym("observe")
                && matches!(args.as_slice(), [Value::Var(arg)] if *arg == sym("retained"))
    ));
    assert_eq!(result.as_str(), "%rc0");
    let returned = head_drop(post, "retained");
    assert!(matches!(
        returned,
        Comp::Return(Value::Var(name)) if name == result
    ));
}

#[test]
fn an_owned_and_borrowed_alias_keeps_a_loan_token_through_the_call() {
    let int = source(Type::Int);
    let owned = TypedBinder::new(sym("owned"), int.clone());
    let loan = TypedBinder::new(sym("loan"), int.clone());
    let callee = function(
        "consume_and_borrow",
        vec![owned, loan],
        ret(var("owned", int.clone())),
    );
    let shared = TypedBinder::new(sym("shared"), int.clone());
    let call = TypedComp::new(
        pure(int.clone()),
        TypedCompKind::Call {
            callee: sym("consume_and_borrow"),
            instantiation: Vec::new(),
            args: vec![var("shared", int.clone()), var("shared", int)],
        },
    );
    let invoking_function = function("caller", vec![shared], call);
    let input = UncheckedTypedCore::new(vec![callee, invoking_function]);
    let sigs = std::iter::once((sym("consume_and_borrow"), vec![false, true])).collect();
    let actual = run_and_verify(input, &sigs, &VerifyEnv::new()).erase();

    let after_loan = head_dup(&actual.fns[1].body, "shared");
    let Comp::Bind(call, result, post) = after_loan else {
        panic!("aliased call must defer loan cleanup");
    };
    assert!(matches!(
        &**call,
        Comp::Call(name, args)
            if *name == sym("consume_and_borrow")
                && matches!(
                    args.as_slice(),
                    [Value::Var(lhs), Value::Var(rhs)]
                        if *lhs == sym("shared") && *rhs == sym("shared")
                )
    ));
    assert_eq!(result.as_str(), "%rc0");
    let returned = head_drop(post, "shared");
    assert!(matches!(
        returned,
        Comp::Return(Value::Var(name)) if name == result
    ));
}

// The optimizer may inline a boxed scalar literal directly into a borrowed
// position after masks are committed. The pass must anchor it to a fresh
// binder so the caller owns the cell and releases it once the loan ends;
// leaving it inline would leak the box the backend allocates for it.
#[test]
fn a_borrowed_boxed_literal_is_anchored_and_released_after_the_call() {
    let float = source(Type::Float);
    let parameter = TypedBinder::new(sym("borrowed"), float.clone());
    let body = ret(var("borrowed", float.clone()));
    let observe = function("observe", vec![parameter], body);
    let literal = TypedValue::new(float.clone(), TypedValueKind::Float(2.5));
    let call = TypedComp::new(
        pure(float),
        TypedCompKind::Call {
            callee: sym("observe"),
            instantiation: Vec::new(),
            args: vec![literal],
        },
    );
    let caller = function("caller", Vec::new(), call);
    let input = UncheckedTypedCore::new(vec![observe, caller]);
    let sigs = std::iter::once((sym("observe"), vec![true])).collect();
    let actual = run_and_verify(input, &sigs, &VerifyEnv::new()).erase();

    let Comp::Bind(anchor, owner, rest) = &actual.fns[1].body else {
        panic!("a borrowed literal must be anchored to a binder");
    };
    assert!(matches!(
        &**anchor,
        Comp::Return(Value::Float(x)) if x.to_bits() == 2.5f64.to_bits()
    ));
    assert_eq!(owner.as_str(), "%rc0");
    let Comp::Bind(call, result, post) = &**rest else {
        panic!("the anchored loan must defer its release past the call");
    };
    assert!(matches!(
        &**call,
        Comp::Call(name, args)
            if *name == sym("observe")
                && matches!(args.as_slice(), [Value::Var(arg)] if arg == owner)
    ));
    assert_eq!(result.as_str(), "%rc1");
    let returned = head_drop(post, "%rc0");
    assert!(matches!(
        returned,
        Comp::Return(Value::Var(name)) if name == result
    ));
}

#[test]
fn thunk_captures_are_borrowed_inside_the_suspension() {
    let int = source(Type::Int);
    let capture = TypedBinder::new(sym("capture"), int.clone());
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(pure(int.clone()))),
        TypedValueKind::Thunk(Box::new(ret(var("capture", int)))),
    );
    let input = UncheckedTypedCore::new(vec![function("main", vec![capture], ret(thunk))]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new()).erase();

    // The capture is threaded through to the suspension's result. Perceus may
    // insert a balancing `Dup` before the return; its placement tracks this
    // hand-built fixture's process-global `Sym` supply (adding a builtin or
    // prelude effect moves it), not real elaboration, so peel any leading `Dup`
    // binds and assert the tail returns `capture` untouched: no rename, no drop
    // of the captured value. `run_and_verify` above already proved the RC is
    // balanced, and real programs are covered by the parity and snapshot
    // corpora, which are byte-identical across this change.
    let Comp::Return(Value::Thunk(closure)) = &actual.fns[0].body else {
        panic!("expected a returned thunk");
    };
    let mut tail = &**closure;
    while let Comp::Bind(bound, _, rest) = tail {
        assert!(
            matches!(&**bound, Comp::Dup(_)),
            "only a balancing Dup may precede the return, got {bound:?}"
        );
        tail = rest;
    }
    assert!(matches!(
        tail,
        Comp::Return(Value::Var(name)) if *name == sym("capture")
    ));
}

#[test]
fn rc_sequence_binders_do_not_shadow_a_lowered_word_discard() {
    let int = source(Type::Int);
    let capture = TypedBinder::new(sym("capture"), int.clone());
    let word = CoreType::Lowered(LoweredType::Word);
    let discarded = TypedBinder::new(sym("_"), word.clone());
    let lambda_sig = CoreFnSig::new(Vec::new(), vec![word], pure(int.clone()));
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(lambda_sig))),
        TypedCompKind::Lam(vec![discarded], Box::new(ret(var("capture", int)))),
    );
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig.clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    );
    let input = UncheckedTypedCore::new(vec![function("main", vec![capture], ret(thunk))]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new());

    let TypedCompKind::Return(thunk) = &actual.functions()[0].body.kind else {
        panic!("expected returned thunk");
    };
    let TypedValueKind::Thunk(lambda) = &thunk.kind else {
        panic!("expected retained thunk body");
    };
    let TypedCompKind::Lam(_, body) = &lambda.kind else {
        panic!("expected retained lambda body");
    };
    let TypedCompKind::Bind(_, first_sequence, rest) = &body.kind else {
        panic!("expected the capture dup to be sequenced");
    };
    assert_eq!(first_sequence.name().as_str(), names::RC_SEQUENCE_BINDER);
    assert_eq!(first_sequence.erase_name().as_str(), "_");
    let TypedCompKind::Bind(_, second_sequence, _) = &rest.kind else {
        panic!("expected the discarded parameter drop to be sequenced");
    };
    assert_eq!(second_sequence.name().as_str(), names::RC_SEQUENCE_BINDER);
    assert_eq!(second_sequence.erase_name().as_str(), "_");
}

#[test]
fn unboxed_products_rewrite_the_thunks_they_contain() {
    let int = source(Type::Int);
    let source_function = Type::Fun(Vec::new(), EffRow::Empty, Box::new(Type::Int));
    let captured_thunk = |capture: &str| {
        let closure_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(int.clone()));
        let closure = TypedComp::new(
            pure(CoreType::Function(Box::new(closure_sig))),
            TypedCompKind::Lam(Vec::new(), Box::new(ret(var(capture, int.clone())))),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(closure.sig.clone())),
            TypedValueKind::Thunk(Box::new(closure)),
        )
    };

    let tuple_capture = TypedBinder::new(sym("tuple_capture"), int.clone());
    let tuple = TypedValue::new(
        source(Type::UnboxedTuple(vec![source_function.clone()])),
        TypedValueKind::UnboxedTuple(vec![captured_thunk("tuple_capture")]),
    );
    let tuple_function = function("tuple", vec![tuple_capture], ret(tuple));

    let field_name = sym("run");
    let record_capture = TypedBinder::new(sym("record_capture"), int.clone());
    let record = TypedValue::new(
        source(Type::UnboxedRecord(vec![(field_name, source_function)])),
        TypedValueKind::UnboxedRecord(vec![(field_name, captured_thunk("record_capture"))]),
    );
    let record_function = function("record", vec![record_capture], ret(record));
    let input = UncheckedTypedCore::new(vec![tuple_function, record_function]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new()).erase();

    let Comp::Return(Value::UnboxedTuple(tuple_fields)) = &actual.fns[0].body else {
        panic!("expected unboxed tuple return");
    };
    let Value::Thunk(tuple_closure) = &tuple_fields[0] else {
        panic!("expected tuple thunk");
    };
    let Comp::Lam(_, tuple_body) = &**tuple_closure else {
        panic!("expected tuple closure");
    };
    let tuple_rest = head_dup(tuple_body, "tuple_capture");
    assert!(matches!(
        tuple_rest,
        Comp::Return(Value::Var(name)) if *name == sym("tuple_capture")
    ));

    let Comp::Return(Value::UnboxedRecord(record_fields)) = &actual.fns[1].body else {
        panic!("expected unboxed record return");
    };
    let Value::Thunk(record_closure) = &record_fields[0].1 else {
        panic!("expected record thunk");
    };
    let Comp::Lam(_, record_body) = &**record_closure else {
        panic!("expected record closure");
    };
    let record_rest = head_dup(record_body, "record_capture");
    assert!(matches!(
        record_rest,
        Comp::Return(Value::Var(name)) if *name == sym("record_capture")
    ));
}

#[test]
fn branches_and_refs_balance_on_every_path() {
    let int = source(Type::Int);
    let condition = TypedBinder::new(sym("condition"), source(Type::Bool));
    let cell_ty = CoreType::Ref(Box::new(int.clone()));
    let cell = TypedBinder::new(sym("cell"), cell_ty.clone());
    let get = || {
        TypedComp::new(
            pure(int.clone()),
            TypedCompKind::RefGet(var("cell", cell_ty.clone())),
        )
    };
    let body = TypedComp::new(
        pure(int.clone()),
        TypedCompKind::If(
            var("condition", source(Type::Bool)),
            Box::new(get()),
            Box::new(get()),
        ),
    );
    let input = UncheckedTypedCore::new(vec![function("main", vec![condition, cell], body)]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new()).erase();

    // Each arm must independently balance: the unused boolean is dropped on
    // both paths, and the cell is consumed by its read.
    let Comp::If(_, yes, no) = &actual.fns[0].body else {
        panic!("expected the branch structure to survive RC insertion");
    };
    for branch in [&**yes, &**no] {
        let after_drop = head_drop(branch, "condition");
        assert!(matches!(
            after_drop,
            Comp::RefGet(Value::Var(name)) if *name == sym("cell")
        ));
    }
}

#[test]
fn pattern_arms_duplicate_live_fields_before_dropping_the_scrutinee() {
    let int = source(Type::Int);
    let tuple_ty = source(Type::Tuple(vec![Type::Int]));
    let scrutinee = TypedBinder::new(sym("scrutinee"), tuple_ty.clone());
    let field = TypedBinder::new(sym("field"), int.clone());
    let body = TypedComp::new(
        pure(int.clone()),
        TypedCompKind::Case(
            var("scrutinee", tuple_ty),
            vec![(
                TypedPattern::Tuple(vec![Some(field)]),
                ret(var("field", int)),
            )],
        ),
    );
    let input = UncheckedTypedCore::new(vec![function("main", vec![scrutinee], body)]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new()).erase();
    let Comp::Case(_, arms) = &actual.fns[0].body else {
        panic!("expected case after RC insertion");
    };
    let field_rest = head_dup(&arms[0].1, "field");
    let scrutinee_rest = head_drop(field_rest, "scrutinee");
    assert!(matches!(
        scrutinee_rest,
        Comp::Return(Value::Var(name)) if *name == sym("field")
    ));
}

#[test]
fn init_at_consumes_the_cell_and_every_constructor_field() {
    let int = source(Type::Int);
    let tuple = source(Type::Tuple(vec![Type::Int, Type::Int]));
    let cell = TypedBinder::new(sym("cell"), int.clone());
    let field = TypedBinder::new(sym("field"), int.clone());
    let ctor = TypedValue::new(
        tuple.clone(),
        TypedValueKind::Tuple(vec![var("field", int.clone()), var("field", int.clone())]),
    );
    let body = TypedComp::new(
        pure(tuple),
        TypedCompKind::InitAt(var("cell", int.clone()), ctor),
    );
    let input = UncheckedTypedCore::new(vec![function("main", vec![cell, field], body)]);
    let mut env = VerifyEnv::new();
    env.insert_operation(
        sym(ALLOC_OP),
        OperationSig::new(
            Vec::new(),
            vec![int.clone()],
            int,
            Label::bare(sym("Arena")),
        ),
    );
    let actual = run_and_verify(input, &Sigs::new(), &env).erase();
    let after_dup = head_dup(&actual.fns[0].body, "field");
    assert!(matches!(
        after_dup,
        Comp::InitAt(Value::Var(cell), Value::Tuple(fields))
            if *cell == sym("cell")
                && matches!(
                    fields.as_slice(),
                    [Value::Var(lhs), Value::Var(rhs)]
                        if *lhs == sym("field") && *rhs == sym("field")
                )
    ));
}

#[test]
fn each_polymorphic_global_capture_retains_at_its_own_instantiation() {
    let id = sym("id");
    let parameter_type = sym("a");
    let generic = source(Type::Var(parameter_type));
    let parameter = TypedBinder::new(sym("value"), generic.clone());
    let id_body = ret(var("value", generic.clone()));
    let id_sig = CoreFnSig::new(
        vec![CoreQuantifier::Type(parameter_type)],
        vec![generic.clone()],
        pure(generic),
    );
    let id_function = TypedCoreFn::new(id, vec![parameter], id_body, id_sig, 0);

    let capture = |name: &str, ty: Type| {
        let instance = CoreFnSig::new(
            Vec::new(),
            vec![source(ty.clone())],
            pure(source(ty.clone())),
        );
        let global = TypedValue::new(
            CoreType::Function(Box::new(instance)),
            TypedValueKind::Var {
                name: id,
                instantiation: vec![CoreInstantiation::Type(ty)],
            },
        );
        let closure_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(global.ty.clone()));
        let closure = TypedComp::new(
            pure(CoreType::Function(Box::new(closure_sig))),
            TypedCompKind::Lam(Vec::new(), Box::new(ret(global))),
        );
        function(name, Vec::new(), closure)
    };
    let input = UncheckedTypedCore::new(vec![
        id_function,
        capture("int_capture", Type::Int),
        capture("bool_capture", Type::Bool),
    ]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new());
    let instance = |ty: &Type| {
        CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![source(ty.clone())],
            pure(source(ty.clone())),
        )))
    };

    // Both closures capture the same symbol at different types. The retain
    // names the occurrence that captured it, so each carries its own
    // instantiation: a consumer asking which reference a later release
    // discharges gets the instance it was taken at, not whichever one the
    // whole-program walk happened to reach first.
    for (function, ty) in actual.functions()[1..].iter().zip([Type::Int, Type::Bool]) {
        let TypedCompKind::Lam(_, body) = &function.body.kind else {
            panic!("expected captured global closure");
        };
        let TypedCompKind::Bind(dup, _, _) = &body.kind else {
            panic!("expected a capture dup");
        };
        let TypedCompKind::Dup(operand) = &dup.kind else {
            panic!("expected a typed dup operand");
        };
        assert_eq!(
            operand.ty,
            instance(&ty),
            "{} retained at the wrong type",
            function.name
        );
        let TypedValueKind::Var {
            name,
            instantiation,
        } = &operand.kind
        else {
            panic!("expected the capturing occurrence as the witness");
        };
        assert_eq!(*name, id);
        assert_eq!(instantiation.as_slice(), [CoreInstantiation::Type(ty)]);
    }
}

#[test]
fn a_deferred_release_names_the_binder_not_the_borrowed_occurrence() {
    let int = source(Type::Int);
    let chr = source(Type::Char);
    let borrowed = TypedBinder::new(sym("borrowed"), chr.clone());
    let observe = function("observe", vec![borrowed], ret(var("borrowed", chr.clone())));
    let held = TypedBinder::new(sym("held"), int.clone());
    // The occurrence at the call is deliberately not the binder's own value,
    // so the two candidate witnesses are distinguishable in the result.
    let wrapped = TypedValue::new(
        chr.clone(),
        TypedValueKind::Reinterpret(Box::new(var("held", int))),
    );
    let call = TypedComp::new(
        pure(chr),
        TypedCompKind::Call {
            callee: sym("observe"),
            instantiation: Vec::new(),
            args: vec![wrapped],
        },
    );
    let caller = function("caller", vec![held], call);
    let input = UncheckedTypedCore::new(vec![observe, caller]);
    let sigs = std::iter::once((sym("observe"), vec![true])).collect();
    let actual = run_and_verify(input, &sigs, &VerifyEnv::new());

    let TypedCompKind::Bind(_, _, post) = &actual.functions()[1].body.kind else {
        panic!("a borrowed call defers its cleanup past the call");
    };
    let TypedCompKind::Bind(release, _, _) = &post.kind else {
        panic!("expected the deferred release");
    };
    let TypedCompKind::Drop(operand) = &release.kind else {
        panic!("expected a drop");
    };
    assert!(
        matches!(
            &operand.kind,
            TypedValueKind::Var { name, instantiation }
                if *name == sym("held") && instantiation.is_empty()
        ),
        "a release discharges a reference the site owns and does not use, so it \
         has no occurrence to name and must name the binder: {operand:?}"
    );
}

#[test]
fn a_same_named_local_elsewhere_cannot_supply_a_capture_witness() {
    let global_name = sym("f");
    let int = source(Type::Int);
    let unit = source(Type::Unit);
    let global_sig = CoreFnSig::new(Vec::new(), vec![unit.clone()], pure(unit.clone()));

    let poison_param = TypedBinder::new(global_name, int.clone());
    let poison = function(
        "poison",
        vec![poison_param],
        ret(TypedValue::new(
            int,
            TypedValueKind::Var {
                name: global_name,
                instantiation: Vec::new(),
            },
        )),
    );
    let global_param = TypedBinder::new(sym("arg"), unit);
    let global = TypedCoreFn::new(
        global_name,
        vec![global_param.clone()],
        ret(binder_occurrence(&global_param)),
        global_sig.clone(),
        0,
    );
    let global_value = TypedValue::new(
        CoreType::Function(Box::new(global_sig.clone())),
        TypedValueKind::Var {
            name: global_name,
            instantiation: Vec::new(),
        },
    );
    let capture_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(global_value.ty.clone()));
    let capture = function(
        "capture",
        Vec::new(),
        TypedComp::new(
            pure(CoreType::Function(Box::new(capture_sig))),
            TypedCompKind::Lam(Vec::new(), Box::new(ret(global_value))),
        ),
    );
    let input = UncheckedTypedCore::new(vec![poison, global, capture]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new());
    let TypedCompKind::Lam(_, body) = &actual.functions()[2].body.kind else {
        panic!("expected global-capturing closure");
    };
    let TypedCompKind::Bind(dup, _, _) = &body.kind else {
        panic!("expected capture dup");
    };
    let TypedCompKind::Dup(operand) = &dup.kind else {
        panic!("expected typed dup operand");
    };
    assert_eq!(
        operand.ty,
        CoreType::Function(Box::new(global_sig)),
        "the witness comes from the occurrence that captured f, so the earlier \
         local f:Int is not a candidate for it at all"
    );
}

#[test]
fn insertion_order_is_name_stable() {
    let int = source(Type::Int);
    let zulu = TypedBinder::new(sym("zulu"), int.clone());
    let alpha = TypedBinder::new(sym("alpha"), int);
    let unit = TypedValue::new(source(Type::Unit), TypedValueKind::Unit);
    let input = UncheckedTypedCore::new(vec![function("main", vec![zulu, alpha], ret(unit))]);
    let actual = run_and_verify(input, &Sigs::new(), &VerifyEnv::new()).erase();
    let rendered = crate::core::pp_core(&actual);
    let alpha_at = rendered.find("drop alpha").expect("alpha drop");
    let zulu_at = rendered.find("drop zulu").expect("zulu drop");
    assert!(
        zulu_at < alpha_at,
        "name-sorted insertion wraps the later name outermost"
    );
}

#[test]
fn bind_spine_free_variable_work_scales_linearly() {
    fn fixture(bindings: usize) -> UncheckedTypedCore<EffectLowered> {
        let unit = source(Type::Unit);
        let returned_unit = || ret(TypedValue::new(unit.clone(), TypedValueKind::Unit));
        let mut body = returned_unit();
        for index in (0..bindings).rev() {
            body = TypedComp::new(
                pure(unit.clone()),
                TypedCompKind::Bind(
                    Box::new(returned_unit()),
                    TypedBinder::new(sym(&format!("spine_{index}")), unit.clone()),
                    Box::new(body),
                ),
            );
        }
        UncheckedTypedCore::new(vec![function("main", Vec::new(), body)])
    }

    fn visits(bindings: usize) -> usize {
        let input = fixture(bindings);
        let input = verify(input, &VerifyEnv::new()).expect("bind-spine fixture must be valid");
        let (owned, visits) = count_free_comp_var_visits(|| insert_rc(input, &Sigs::new()));
        verify(owned, &VerifyEnv::new()).expect("RC output must remain valid");
        visits
    }

    const SMALL: usize = 128;
    const LARGE: usize = 256;
    let small = visits(SMALL);
    let large = visits(LARGE);

    assert!(
        large <= small * 2 + 2,
        "doubling a bind spine must approximately double free-variable work: \
         {SMALL} bindings visited {small} nodes, {LARGE} visited {large}"
    );
    assert!(
        large <= LARGE * 4,
        "free-variable work must stay linear in bind-spine length: \
         {LARGE} bindings visited {large} nodes"
    );
}
