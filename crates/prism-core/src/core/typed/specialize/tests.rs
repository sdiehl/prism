use prism_syntax::error::{Error, TYPED_CORE_SPECIALIZATION};

use super::super::verify::ConstructorSig;
use super::super::{verify, CompSig, Elaborated, VerifyEnv};
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

fn dict_ty(class: &str, argument: Type) -> CoreType {
    source(Type::Con(sym(class), vec![argument]))
}

fn method_signature(argument: Type) -> CoreFnSig {
    CoreFnSig::new(
        Vec::new(),
        vec![source(argument.clone())],
        pure(source(argument)),
    )
}

fn method_type(argument: Type) -> CoreType {
    let lambda = pure(CoreType::Function(Box::new(method_signature(argument))));
    CoreType::Thunk(Box::new(lambda))
}

fn variable(name: &str, ty: CoreType) -> TypedValue {
    TypedValue::new(
        ty,
        TypedValueKind::Var {
            name: sym(name),
            instantiation: Vec::new(),
        },
    )
}

fn literal(ty: &Type) -> TypedValue {
    match ty {
        Type::Int => TypedValue::new(source(Type::Int), TypedValueKind::Int(7)),
        Type::Bool => TypedValue::new(source(Type::Bool), TypedValueKind::Bool(true)),
        other => panic!("test literal does not support {other:?}"),
    }
}

fn identity_method(argument: Type, binder_name: &str) -> TypedValue {
    let binder = TypedBinder::new(sym(binder_name), source(argument.clone()));
    let body = TypedComp::new(
        pure(source(argument.clone())),
        TypedCompKind::Return(variable(binder_name, source(argument.clone()))),
    );
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(method_signature(argument)))),
        TypedCompKind::Lam(vec![binder], Box::new(body)),
    );
    TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig.clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    )
}

fn type_polymorphic_method(quantifier: &str, binder_name: &str) -> TypedValue {
    let bound = sym(quantifier);
    let argument = Type::Var(bound);
    let signature = CoreFnSig::new(
        vec![CoreQuantifier::Type(bound)],
        vec![source(argument.clone())],
        pure(source(argument.clone())),
    );
    let binder = TypedBinder::new(sym(binder_name), source(argument.clone()));
    let body = TypedComp::new(
        pure(source(argument.clone())),
        TypedCompKind::Return(variable(binder_name, source(argument))),
    );
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(signature))),
        TypedCompKind::Lam(vec![binder], Box::new(body)),
    );
    TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig.clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    )
}

fn row_polymorphic_method(quantifier: &str) -> TypedValue {
    let bound = sym(quantifier);
    let signature = CoreFnSig::new(
        vec![CoreQuantifier::Row(bound)],
        Vec::new(),
        CompSig::new(source(Type::Int), EffRow::Var(bound)),
    );
    let body = TypedComp::new(
        CompSig::new(source(Type::Int), EffRow::Var(bound)),
        TypedCompKind::Error(TypedValue::new(
            source(Type::Str),
            TypedValueKind::Str("unreachable polymorphic method".into()),
        )),
    );
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(signature))),
        TypedCompKind::Lam(Vec::new(), Box::new(body)),
    );
    TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig.clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    )
}

fn install_dictionary_constructor_with_field(env: &mut VerifyEnv, class: &str, field: CoreType) {
    let parameter = sym(&format!("{class}_ctor_a"));
    env.insert_constructor(
        sym(class),
        ConstructorSig::new(
            vec![CoreQuantifier::Type(parameter)],
            0,
            vec![field],
            dict_ty(class, Type::Var(parameter)),
        ),
    );
}

fn builder_with_field(name: &str, class: &str, argument: Type, field: TypedValue) -> TypedCoreFn {
    let dictionary = dict_ty(class, argument.clone());
    TypedCoreFn::new(
        sym(name),
        Vec::new(),
        TypedComp::new(
            pure(dictionary.clone()),
            TypedCompKind::Return(TypedValue::new(
                dictionary.clone(),
                TypedValueKind::Ctor {
                    name: sym(class),
                    tag: 0,
                    instantiation: vec![CoreInstantiation::Type(argument)],
                    fields: vec![field],
                },
            )),
        ),
        CoreFnSig::new(Vec::new(), Vec::new(), pure(dictionary)),
        0,
    )
}

fn independently_polymorphic_projection(
    name: &str,
    class: &str,
    method_type: CoreType,
    method_instantiation: Vec<CoreInstantiation>,
    argument_types: &[Type],
    result: CoreType,
    effects: EffRow,
) -> TypedCoreFn {
    let dictionary = dict_ty(class, Type::Int);
    let dict_name = format!("{name}_dict");
    let method_name = format!("{name}_method");
    let mut params = vec![TypedBinder::new(sym(&dict_name), dictionary.clone())];
    params.extend(argument_types.iter().enumerate().map(|(index, ty)| {
        TypedBinder::new(sym(&format!("{name}_arg_{index}")), source(ty.clone()))
    }));
    let CoreType::Thunk(force_signature) = &method_type else {
        panic!("test method must be a thunk")
    };
    let force = TypedComp::new(
        force_signature.as_ref().clone(),
        TypedCompKind::Force(variable(&method_name, method_type.clone())),
    );
    let application = TypedComp::new(
        CompSig::new(result.clone(), effects.clone()),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: method_instantiation,
            args: argument_types
                .iter()
                .enumerate()
                .map(|(index, ty)| variable(&format!("{name}_arg_{index}"), source(ty.clone())))
                .collect(),
        },
    );
    let body = TypedComp::new(
        CompSig::new(result.clone(), effects.clone()),
        TypedCompKind::Case(
            variable(&dict_name, dictionary),
            vec![(
                TypedPattern::Ctor {
                    name: sym(class),
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    fields: vec![Some(TypedBinder::new(sym(&method_name), method_type))],
                },
                application,
            )],
        ),
    );
    TypedCoreFn::new(
        sym(name),
        params.clone(),
        body,
        CoreFnSig::new(
            Vec::new(),
            params.iter().map(|binder| binder.ty.clone()).collect(),
            CompSig::new(result, effects),
        ),
        1,
    )
}

fn direct_main(
    builder: &str,
    class: &str,
    target: &str,
    values: Vec<TypedValue>,
    result: CoreType,
    effects: EffRow,
) -> TypedCoreFn {
    let dictionary = dict_ty(class, Type::Int);
    let binder = TypedBinder::new(sym("direct_main_dict"), dictionary.clone());
    let mut arguments = vec![variable("direct_main_dict", dictionary.clone())];
    arguments.extend(values);
    let call = TypedComp::new(
        CompSig::new(result.clone(), effects.clone()),
        TypedCompKind::Call {
            callee: sym(target),
            instantiation: Vec::new(),
            args: arguments,
        },
    );
    let body = TypedComp::new(
        CompSig::new(result.clone(), effects.clone()),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(dictionary),
                TypedCompKind::Call {
                    callee: sym(builder),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            )),
            binder,
            Box::new(call),
        ),
    );
    TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body,
        CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(result, effects)),
        0,
    )
}

fn residual_row_function(name: &str, class: &str, row: &str) -> TypedCoreFn {
    let row = sym(row);
    let argument = sym(&format!("{name}_a"));
    let dictionary = dict_ty(class, Type::Var(argument));
    let body_sig = CompSig::new(source(Type::Int), EffRow::Var(row));
    TypedCoreFn::new(
        sym(name),
        vec![TypedBinder::new(
            sym(&format!("{name}_dict")),
            dictionary.clone(),
        )],
        TypedComp::new(
            body_sig.clone(),
            TypedCompKind::Error(TypedValue::new(
                source(Type::Str),
                TypedValueKind::Str("residual row witness".into()),
            )),
        ),
        CoreFnSig::new(
            vec![CoreQuantifier::Type(argument), CoreQuantifier::Row(row)],
            vec![dictionary],
            body_sig,
        ),
        1,
    )
}

fn residual_row_main(builder: &str, class: &str, target: &str, row: EffRow) -> TypedCoreFn {
    let dictionary = dict_ty(class, Type::Int);
    let binder = TypedBinder::new(sym("row_main_dict"), dictionary.clone());
    let result = CompSig::new(source(Type::Int), row.clone());
    let call = TypedComp::new(
        result.clone(),
        TypedCompKind::Call {
            callee: sym(target),
            instantiation: vec![
                CoreInstantiation::Type(Type::Int),
                CoreInstantiation::Row(row),
            ],
            args: vec![variable("row_main_dict", dictionary.clone())],
        },
    );
    let body = TypedComp::new(
        result.clone(),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(dictionary),
                TypedCompKind::Call {
                    callee: sym(builder),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            )),
            binder,
            Box::new(call),
        ),
    );
    TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body,
        CoreFnSig::new(Vec::new(), Vec::new(), result),
        0,
    )
}

fn install_dictionary_constructor(env: &mut VerifyEnv, class: &str) {
    let parameter = sym(&format!("{class}_ctor_a"));
    env.insert_constructor(
        sym(class),
        ConstructorSig::new(
            vec![CoreQuantifier::Type(parameter)],
            0,
            vec![method_type(Type::Var(parameter))],
            dict_ty(class, Type::Var(parameter)),
        ),
    );
}

fn builder(name: &str, class: &str, quantifier: Option<&str>, argument: Type) -> TypedCoreFn {
    let quantifiers = quantifier
        .map(|name| vec![CoreQuantifier::Type(sym(name))])
        .unwrap_or_default();
    let dictionary = dict_ty(class, argument.clone());
    let method = identity_method(argument.clone(), &format!("{name}_method_arg"));
    TypedCoreFn::new(
        sym(name),
        Vec::new(),
        TypedComp::new(
            pure(dictionary.clone()),
            TypedCompKind::Return(TypedValue::new(
                dictionary.clone(),
                TypedValueKind::Ctor {
                    name: sym(class),
                    tag: 0,
                    instantiation: vec![CoreInstantiation::Type(argument)],
                    fields: vec![method],
                },
            )),
        ),
        CoreFnSig::new(quantifiers, Vec::new(), pure(dictionary)),
        0,
    )
}

fn projection_function(name: &str, class: &str) -> TypedCoreFn {
    let argument = sym(&format!("{name}_a"));
    let argument_ty = Type::Var(argument);
    let dictionary = dict_ty(class, argument_ty.clone());
    let method_ty = method_type(argument_ty.clone());
    let dict_binder = TypedBinder::new(sym(&format!("{name}_dict")), dictionary.clone());
    let value_binder = TypedBinder::new(sym(&format!("{name}_value")), source(argument_ty.clone()));
    let method_binder = TypedBinder::new(sym(&format!("{name}_method")), method_ty.clone());
    let force = TypedComp::new(
        pure(CoreType::Function(Box::new(method_signature(
            argument_ty.clone(),
        )))),
        TypedCompKind::Force(variable(&format!("{name}_method"), method_ty)),
    );
    let application = TypedComp::new(
        pure(source(argument_ty.clone())),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![variable(
                &format!("{name}_value"),
                source(argument_ty.clone()),
            )],
        },
    );
    let body = TypedComp::new(
        pure(source(argument_ty.clone())),
        TypedCompKind::Case(
            variable(&format!("{name}_dict"), dictionary.clone()),
            vec![(
                TypedPattern::Ctor {
                    name: sym(class),
                    instantiation: vec![CoreInstantiation::Type(argument_ty.clone())],
                    fields: vec![Some(method_binder)],
                },
                application,
            )],
        ),
    );
    TypedCoreFn::new(
        sym(name),
        vec![dict_binder, value_binder],
        body,
        CoreFnSig::new(
            vec![CoreQuantifier::Type(argument)],
            vec![dictionary, source(argument_ty.clone())],
            pure(source(argument_ty)),
        ),
        1,
    )
}

fn plain_function(
    name: &str,
    quantifiers: &[&str],
    dictionaries: &[(&str, Type)],
    value: Type,
    recursive: bool,
) -> TypedCoreFn {
    let mut params: Vec<_> = dictionaries
        .iter()
        .enumerate()
        .map(|(index, (class, argument))| {
            TypedBinder::new(
                sym(&format!("{name}_dict_{index}")),
                dict_ty(class, argument.clone()),
            )
        })
        .collect();
    params.push(TypedBinder::new(
        sym(&format!("{name}_value")),
        source(value.clone()),
    ));
    let body = if recursive {
        TypedComp::new(
            pure(source(value.clone())),
            TypedCompKind::Call {
                callee: sym(name),
                instantiation: quantifiers
                    .iter()
                    .map(|name| CoreInstantiation::Type(Type::Var(sym(name))))
                    .collect(),
                args: params
                    .iter()
                    .map(|binder| variable(binder.name.as_str(), binder.ty.clone()))
                    .collect(),
            },
        )
    } else {
        TypedComp::new(
            pure(source(value.clone())),
            TypedCompKind::Return(variable(&format!("{name}_value"), source(value.clone()))),
        )
    };
    TypedCoreFn::new(
        sym(name),
        params.clone(),
        body,
        CoreFnSig::new(
            quantifiers
                .iter()
                .map(|name| CoreQuantifier::Type(sym(name)))
                .collect(),
            params.iter().map(|binder| binder.ty.clone()).collect(),
            pure(source(value)),
        ),
        dictionaries.len(),
    )
}

#[derive(Clone)]
struct BuilderUse {
    name: &'static str,
    class: &'static str,
    instantiation: Vec<CoreInstantiation>,
    argument: Type,
}

#[derive(Clone)]
struct Invocation {
    builders: Vec<BuilderUse>,
    instantiation: Vec<CoreInstantiation>,
    value: Type,
}

fn invocation_body(target: &str, invocations: &[Invocation], index: usize) -> TypedComp {
    let invocation = &invocations[index];
    let dictionary_binders: Vec<_> = invocation
        .builders
        .iter()
        .enumerate()
        .map(|(builder_index, builder)| {
            TypedBinder::new(
                sym(&format!("main_dict_{index}_{builder_index}")),
                dict_ty(builder.class, builder.argument.clone()),
            )
        })
        .collect();
    let mut arguments: Vec<_> = dictionary_binders
        .iter()
        .map(|binder| variable(binder.name.as_str(), binder.ty.clone()))
        .collect();
    arguments.push(literal(&invocation.value));
    let call = TypedComp::new(
        pure(source(invocation.value.clone())),
        TypedCompKind::Call {
            callee: sym(target),
            instantiation: invocation.instantiation.clone(),
            args: arguments,
        },
    );
    let mut body = if index + 1 == invocations.len() {
        call
    } else {
        let rest = invocation_body(target, invocations, index + 1);
        TypedComp::new(
            rest.sig.clone(),
            TypedCompKind::Bind(
                Box::new(call),
                TypedBinder::new(
                    sym(&format!("main_result_{index}")),
                    source(invocation.value.clone()),
                ),
                Box::new(rest),
            ),
        )
    };
    for (builder_index, builder) in invocation.builders.iter().enumerate().rev() {
        let dictionary = dict_ty(builder.class, builder.argument.clone());
        body = TypedComp::new(
            body.sig.clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    pure(dictionary),
                    TypedCompKind::Call {
                        callee: sym(builder.name),
                        instantiation: builder.instantiation.clone(),
                        args: Vec::new(),
                    },
                )),
                dictionary_binders[builder_index].clone(),
                Box::new(body),
            ),
        );
    }
    body
}

fn main_function(target: &str, invocations: &[Invocation]) -> TypedCoreFn {
    let body = invocation_body(target, invocations, 0);
    TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body.clone(),
        CoreFnSig::new(Vec::new(), Vec::new(), body.sig),
        0,
    )
}

fn run_and_verify(functions: Vec<TypedCoreFn>, env: &VerifyEnv) -> (TypedCore<Elaborated>, u64) {
    let input = verify(UncheckedTypedCore::<Elaborated>::new(functions), env)
        .unwrap_or_else(|violations| panic!("input fixture is invalid: {violations:#?}"));
    let (actual, stats) = specialize(input).expect("typed specialization");
    let actual = verify(actual, env)
        .unwrap_or_else(|violations| panic!("specialized typed Core is invalid: {violations:#?}"));
    (actual, stats.ticks())
}

fn ho_run_and_verify(functions: Vec<TypedCoreFn>, env: &VerifyEnv) -> (TypedCore<Elaborated>, u64) {
    let input = verify(UncheckedTypedCore::<Elaborated>::new(functions), env)
        .unwrap_or_else(|violations| panic!("input fixture is invalid: {violations:#?}"));
    let (actual, stats) = ho_specialize(input, false).expect("higher-order specialization");
    let actual = verify(actual, env).unwrap_or_else(|violations| {
        panic!("higher-order specialized typed Core is invalid: {violations:#?}")
    });
    (actual, stats.ticks())
}

// `let f = \x. x in (force f)(7)`: a closed non-eta lambda whose only use
// is a direct apply. The lambda must move to one lifted definition and the
// apply must become a direct call to it, with the dead binding dropped.
#[test]
fn closed_lambda_lifts_and_devirtualizes_a_local_apply() {
    let env = VerifyEnv::new();
    let f_ty = method_type(Type::Int);
    let force = TypedComp::new(
        pure(CoreType::Function(Box::new(method_signature(Type::Int)))),
        TypedCompKind::Force(variable("f", f_ty.clone())),
    );
    let apply = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![literal(&Type::Int)],
        },
    );
    let body = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(f_ty.clone()),
                TypedCompKind::Return(identity_method(Type::Int, "x")),
            )),
            TypedBinder::new(sym("f"), f_ty),
            Box::new(apply),
        ),
    );
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body,
        CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
        0,
    );
    let (actual, ticks) = ho_run_and_verify(vec![main], &env);
    assert_eq!(ticks, 2, "one lift plus one devirtualized apply");
    assert_eq!(
        actual
            .functions()
            .iter()
            .map(TypedCoreFn::name)
            .collect::<Vec<_>>(),
        vec![sym("main"), sym("main$ll1")]
    );
    let TypedCompKind::Call { callee, args, .. } = &actual.functions()[0].body.kind else {
        panic!(
            "devirtualized apply with a dead binding must collapse to a direct call, got {:?}",
            actual.functions()[0].body.kind
        );
    };
    assert_eq!(*callee, sym("main$ll1"));
    assert_eq!(args.len(), 1);
}

// `let f = \x. x in apply(f, 7)` where `apply` force-applies its first
// parameter: the lambda lifts, the callee specializes on it, and the clone
// calls the lifted definition directly. The body exists exactly once.
#[test]
fn closed_lambda_argument_specializes_the_callee_without_duplication() {
    let env = VerifyEnv::new();
    let f_ty = method_type(Type::Int);
    let force = TypedComp::new(
        pure(CoreType::Function(Box::new(method_signature(Type::Int)))),
        TypedCompKind::Force(variable("g", f_ty.clone())),
    );
    let apply_body = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![variable("y", source(Type::Int))],
        },
    );
    let apply = TypedCoreFn::new(
        sym("apply"),
        vec![
            TypedBinder::new(sym("g"), f_ty.clone()),
            TypedBinder::new(sym("y"), source(Type::Int)),
        ],
        apply_body,
        CoreFnSig::new(
            Vec::new(),
            vec![f_ty.clone(), source(Type::Int)],
            pure(source(Type::Int)),
        ),
        0,
    );
    let main_body = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(f_ty.clone()),
                TypedCompKind::Return(identity_method(Type::Int, "x")),
            )),
            TypedBinder::new(sym("f"), f_ty.clone()),
            Box::new(TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Call {
                    callee: sym("apply"),
                    instantiation: Vec::new(),
                    args: vec![variable("f", f_ty), literal(&Type::Int)],
                },
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
    let (actual, ticks) = ho_run_and_verify(vec![apply, main], &env);
    assert_eq!(ticks, 3, "one lift, one clone, one devirtualized apply");
    assert_eq!(
        actual
            .functions()
            .iter()
            .map(TypedCoreFn::name)
            .collect::<Vec<_>>(),
        vec![sym("apply"), sym("main"), sym("main$ll1"), sym("apply$hs1"),]
    );
    let TypedCompKind::Call { callee, args, .. } = &actual.functions()[1].body.kind else {
        panic!("the fixed callable argument must drop from the specialized call");
    };
    assert_eq!(*callee, sym("apply$hs1"));
    assert_eq!(args.len(), 1, "the callable argument is fixed, not passed");
    let clone = &actual.functions()[3];
    let mut callees = BTreeSet::new();
    direct_callees(&clone.body, &mut callees);
    assert!(
        callees.contains(&sym("main$ll1")),
        "the clone must call the lifted definition directly"
    );
}

// A lambda that captures a local is not closed and must stay in place.
#[test]
fn capturing_lambda_is_not_lifted() {
    let env = VerifyEnv::new();
    let f_ty = method_type(Type::Int);
    let captured = TypedBinder::new(sym("outer"), source(Type::Int));
    let lambda_body = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Return(variable("outer", source(Type::Int))),
    );
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(method_signature(Type::Int)))),
        TypedCompKind::Lam(
            vec![TypedBinder::new(sym("x"), source(Type::Int))],
            Box::new(lambda_body),
        ),
    );
    let value = TypedValue::new(f_ty.clone(), TypedValueKind::Thunk(Box::new(lambda)));
    let force = TypedComp::new(
        pure(CoreType::Function(Box::new(method_signature(Type::Int)))),
        TypedCompKind::Force(variable("f", f_ty.clone())),
    );
    let apply = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![literal(&Type::Int)],
        },
    );
    let body = TypedComp::new(
        pure(source(Type::Int)),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Return(literal(&Type::Int)),
            )),
            captured,
            Box::new(TypedComp::new(
                pure(source(Type::Int)),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        pure(f_ty.clone()),
                        TypedCompKind::Return(value),
                    )),
                    TypedBinder::new(sym("f"), f_ty),
                    Box::new(apply),
                ),
            )),
        ),
    );
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body,
        CoreFnSig::new(Vec::new(), Vec::new(), pure(source(Type::Int))),
        0,
    );
    let (actual, ticks) = ho_run_and_verify(vec![main], &env);
    assert_eq!(ticks, 0, "an open lambda proves nothing to lift");
    assert_eq!(actual.functions().len(), 1);
}

// A closed lambda that never reaches an apply gains nothing from a lifted
// identity; the binding must stay untouched.
#[test]
fn unapplied_lambda_is_not_lifted() {
    let env = VerifyEnv::new();
    let f_ty = method_type(Type::Int);
    let body = TypedComp::new(
        pure(f_ty.clone()),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(f_ty.clone()),
                TypedCompKind::Return(identity_method(Type::Int, "x")),
            )),
            TypedBinder::new(sym("f"), f_ty.clone()),
            Box::new(TypedComp::new(
                pure(f_ty.clone()),
                TypedCompKind::Return(variable("f", f_ty.clone())),
            )),
        ),
    );
    let main = TypedCoreFn::new(
        sym("main"),
        Vec::new(),
        body,
        CoreFnSig::new(Vec::new(), Vec::new(), pure(f_ty)),
        0,
    );
    let (actual, ticks) = ho_run_and_verify(vec![main], &env);
    assert_eq!(ticks, 0, "a lambda that escapes unapplied stays in place");
    assert_eq!(actual.functions().len(), 1);
}

#[test]
fn monomorphic_builder_projection_ticks_and_clone_order() {
    let mut env = VerifyEnv::new();
    install_dictionary_constructor(&mut env, "_DIdentity");
    let functions = vec![
        builder("identityInt", "_DIdentity", None, Type::Int),
        projection_function("applyIdentity", "_DIdentity"),
        main_function(
            "applyIdentity",
            &[Invocation {
                builders: vec![BuilderUse {
                    name: "identityInt",
                    class: "_DIdentity",
                    instantiation: Vec::new(),
                    argument: Type::Int,
                }],
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
                value: Type::Int,
            }],
        ),
    ];
    let (actual, ticks) = run_and_verify(functions, &env);
    assert_eq!(ticks, 2, "one clone plus one reduced projection");
    assert_eq!(
        actual
            .functions()
            .iter()
            .map(TypedCoreFn::name)
            .collect::<Vec<_>>(),
        vec![
            sym("identityInt"),
            sym("applyIdentity"),
            sym("main"),
            sym("applyIdentity$sp1"),
        ]
    );
    let clone = actual.functions().last().expect("specialized clone");
    assert!(clone.sig.quantifiers().is_empty());
}

#[test]
fn independently_type_polymorphic_method_is_instantiated_before_splicing() {
    let mut env = VerifyEnv::new();
    let method = type_polymorphic_method("method_a", "poly_method_arg");
    // Real effect-polymorphic class methods (for example Foldable.fold_l)
    // cross the source/Core representation seam through this transparent
    // evidence wrapper before reaching the dictionary cell.
    let field = TypedValue::new(
        method.ty.clone(),
        TypedValueKind::Reinterpret(Box::new(method)),
    );
    let field_type = field.ty.clone();
    install_dictionary_constructor_with_field(&mut env, "_DPolyMethod", field_type.clone());
    let functions = vec![
        builder_with_field("polyMethodInt", "_DPolyMethod", Type::Int, field),
        independently_polymorphic_projection(
            "applyPolyMethod",
            "_DPolyMethod",
            field_type,
            vec![CoreInstantiation::Type(Type::Bool)],
            &[Type::Bool],
            source(Type::Bool),
            EffRow::Empty,
        ),
        direct_main(
            "polyMethodInt",
            "_DPolyMethod",
            "applyPolyMethod",
            vec![literal(&Type::Bool)],
            source(Type::Bool),
            EffRow::Empty,
        ),
    ];
    let (actual, ticks) = run_and_verify(functions, &env);
    assert_eq!(ticks, 2, "one clone plus one polymorphic projection");
    let clone = actual.functions().last().expect("specialized clone");
    assert_eq!(clone.body.sig.result(), &source(Type::Bool));
    let TypedCompKind::Return(value) = &clone.body.kind else {
        panic!("polymorphic identity method should reduce to its argument")
    };
    assert_eq!(value.ty(), &source(Type::Bool));
}

#[test]
fn independently_row_polymorphic_method_instantiates_body_effects() {
    let mut env = VerifyEnv::new();
    let field = row_polymorphic_method("method_e");
    let field_type = field.ty.clone();
    install_dictionary_constructor_with_field(&mut env, "_DRowMethod", field_type.clone());
    let io = EffRow::singleton(prism_syntax::names::IO_EFFECT);
    let functions = vec![
        builder_with_field("rowMethodInt", "_DRowMethod", Type::Int, field),
        independently_polymorphic_projection(
            "applyRowMethod",
            "_DRowMethod",
            field_type,
            vec![CoreInstantiation::Row(io.clone())],
            &[],
            source(Type::Int),
            io.clone(),
        ),
        direct_main(
            "rowMethodInt",
            "_DRowMethod",
            "applyRowMethod",
            Vec::new(),
            source(Type::Int),
            io.clone(),
        ),
    ];
    let (actual, ticks) = run_and_verify(functions, &env);
    assert_eq!(ticks, 2, "one clone plus one row-polymorphic projection");
    let clone = actual.functions().last().expect("specialized clone");
    assert_eq!(clone.body.sig.effects(), &io);
    assert!(matches!(clone.body.kind, TypedCompKind::Error(_)));
}

#[test]
fn residual_source_quantifier_survives_a_monomorphic_dictionary() {
    let mut env = VerifyEnv::new();
    install_dictionary_constructor(&mut env, "_DResidual");
    let function = plain_function(
        "keepResidual",
        &["res_a", "res_b"],
        &[("_DResidual", Type::Var(sym("res_a")))],
        Type::Var(sym("res_b")),
        false,
    );
    let functions = vec![
        builder("residualInt", "_DResidual", None, Type::Int),
        function,
        main_function(
            "keepResidual",
            &[Invocation {
                builders: vec![BuilderUse {
                    name: "residualInt",
                    class: "_DResidual",
                    instantiation: Vec::new(),
                    argument: Type::Int,
                }],
                instantiation: vec![
                    CoreInstantiation::Type(Type::Int),
                    CoreInstantiation::Type(Type::Bool),
                ],
                value: Type::Bool,
            }],
        ),
    ];
    let (actual, _) = run_and_verify(functions, &env);
    let clone = actual.functions().last().expect("specialized clone");
    assert_eq!(
        clone.sig.quantifiers(),
        &[CoreQuantifier::Type(sym("res_b"))]
    );
}

#[test]
fn residual_source_row_quantifier_survives_a_monomorphic_dictionary() {
    let mut env = VerifyEnv::new();
    install_dictionary_constructor(&mut env, "_DResidualRow");
    let io = EffRow::singleton(prism_syntax::names::IO_EFFECT);
    let functions = vec![
        builder("residualRowInt", "_DResidualRow", None, Type::Int),
        residual_row_function("keepResidualRow", "_DResidualRow", "residual_e"),
        residual_row_main("residualRowInt", "_DResidualRow", "keepResidualRow", io),
    ];
    let (actual, ticks) = run_and_verify(functions, &env);
    assert_eq!(ticks, 1);
    let clone = actual.functions().last().expect("specialized clone");
    assert_eq!(
        clone.sig.quantifiers(),
        &[CoreQuantifier::Row(sym("residual_e"))]
    );
    assert_eq!(clone.body.sig.effects(), &EffRow::Var(sym("residual_e")));
}

#[test]
fn polymorphic_nullary_builder_used_at_two_types_produces_one_clone() {
    let mut env = VerifyEnv::new();
    install_dictionary_constructor(&mut env, "_DBlit");
    let functions = vec![
        builder(
            "blitArray",
            "_DBlit",
            Some("blit_element"),
            Type::Var(sym("blit_element")),
        ),
        projection_function("blit", "_DBlit"),
        main_function(
            "blit",
            &[
                Invocation {
                    builders: vec![BuilderUse {
                        name: "blitArray",
                        class: "_DBlit",
                        instantiation: vec![CoreInstantiation::Type(Type::Int)],
                        argument: Type::Int,
                    }],
                    instantiation: vec![CoreInstantiation::Type(Type::Int)],
                    value: Type::Int,
                },
                Invocation {
                    builders: vec![BuilderUse {
                        name: "blitArray",
                        class: "_DBlit",
                        instantiation: vec![CoreInstantiation::Type(Type::Bool)],
                        argument: Type::Bool,
                    }],
                    instantiation: vec![CoreInstantiation::Type(Type::Bool)],
                    value: Type::Bool,
                },
            ],
        ),
    ];
    let (actual, ticks) = run_and_verify(functions, &env);
    assert_eq!(ticks, 2, "one clone and one clone-local projection");
    assert_eq!(
        actual
            .functions()
            .iter()
            .filter(|function| function.name.as_str().starts_with("blit$sp"))
            .count(),
        1
    );
    let clone = actual.functions().last().expect("specialized clone");
    assert_eq!(clone.sig.quantifiers().len(), 1);
}

#[test]
fn shared_builder_quantifier_is_retained_once() {
    let mut env = VerifyEnv::new();
    install_dictionary_constructor(&mut env, "_DLeft");
    install_dictionary_constructor(&mut env, "_DRight");
    let shared = sym("shared_a");
    let function = plain_function(
        "shared",
        &["shared_a"],
        &[
            ("_DLeft", Type::Var(shared)),
            ("_DRight", Type::Var(shared)),
        ],
        Type::Var(shared),
        false,
    );
    let functions = vec![
        builder(
            "leftAny",
            "_DLeft",
            Some("left_a"),
            Type::Var(sym("left_a")),
        ),
        builder(
            "rightAny",
            "_DRight",
            Some("right_a"),
            Type::Var(sym("right_a")),
        ),
        function,
        main_function(
            "shared",
            &[Invocation {
                builders: vec![
                    BuilderUse {
                        name: "leftAny",
                        class: "_DLeft",
                        instantiation: vec![CoreInstantiation::Type(Type::Int)],
                        argument: Type::Int,
                    },
                    BuilderUse {
                        name: "rightAny",
                        class: "_DRight",
                        instantiation: vec![CoreInstantiation::Type(Type::Int)],
                        argument: Type::Int,
                    },
                ],
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
                value: Type::Int,
            }],
        ),
    ];
    let (actual, _) = run_and_verify(functions, &env);
    assert_eq!(
        actual.functions().last().unwrap().sig.quantifiers().len(),
        1
    );
}

#[test]
fn recursive_specialization_uses_the_in_flight_clone() {
    let mut env = VerifyEnv::new();
    install_dictionary_constructor(&mut env, "_DRecursive");
    let recursive = plain_function(
        "recur",
        &["recur_a"],
        &[("_DRecursive", Type::Var(sym("recur_a")))],
        Type::Var(sym("recur_a")),
        true,
    );
    let functions = vec![
        builder("recursiveInt", "_DRecursive", None, Type::Int),
        recursive,
        main_function(
            "recur",
            &[Invocation {
                builders: vec![BuilderUse {
                    name: "recursiveInt",
                    class: "_DRecursive",
                    instantiation: Vec::new(),
                    argument: Type::Int,
                }],
                instantiation: vec![CoreInstantiation::Type(Type::Int)],
                value: Type::Int,
            }],
        ),
    ];
    let (actual, ticks) = run_and_verify(functions, &env);
    assert_eq!(ticks, 1);
    let clone = actual.functions().last().expect("specialized clone");
    let TypedCompKind::Call { callee, .. } = &clone.body.kind else {
        panic!("dictionary materialization should be dead after recursive rewrite")
    };
    assert_eq!(*callee, clone.name);
}

#[test]
fn incompatible_plan_uses_the_canonical_specialization_code() {
    let function = plain_function(
        "badPlan",
        &["bad_a"],
        &[("_DExpected", Type::Var(sym("bad_a")))],
        Type::Var(sym("bad_a")),
        false,
    );
    let wrong = Builder {
        function: builder("wrong", "_DWrong", None, Type::Int),
    };
    let failure = SpecializationPlan::build(&function, &[wrong]).unwrap_err();
    assert!(matches!(
        failure,
        TypedCoreSpecializationFailure::IncompatibleDictionary { .. }
    ));
    assert_eq!(Error::from(failure).code(), TYPED_CORE_SPECIALIZATION);
}

#[test]
fn dce_keeps_legacy_value_thunk_boundary_opaque() {
    let builder = builder("opaqueBuilder", "_DOpaque", None, Type::Int);
    let builders = BTreeMap::from([(builder.name, Builder { function: builder })]);
    let dictionary = dict_ty("_DOpaque", Type::Int);
    let unit = source(Type::Unit);
    let inner = TypedComp::new(
        pure(unit.clone()),
        TypedCompKind::Bind(
            Box::new(TypedComp::new(
                pure(dictionary.clone()),
                TypedCompKind::Call {
                    callee: sym("opaqueBuilder"),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            )),
            TypedBinder::new(sym("unused_dictionary"), dictionary),
            Box::new(TypedComp::new(
                pure(unit.clone()),
                TypedCompKind::Return(TypedValue::new(unit.clone(), TypedValueKind::Unit)),
            )),
        ),
    );
    let lambda_sig = CoreFnSig::new(Vec::new(), Vec::new(), pure(unit));
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(lambda_sig))),
        TypedCompKind::Lam(Vec::new(), Box::new(inner)),
    );
    let thunk_type = CoreType::Thunk(Box::new(lambda.sig.clone()));
    let outer = TypedComp::new(
        pure(thunk_type.clone()),
        TypedCompKind::Return(TypedValue::new(
            thunk_type,
            TypedValueKind::Thunk(Box::new(lambda)),
        )),
    );

    let actual = Dce {
        builders: &builders,
    }
    .comp(&outer, &());
    assert_eq!(actual, outer);
}
