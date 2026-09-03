//! Source-scheme lowering and the typed-Core verification environment.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::error::{Error, TypedCoreEnvironmentFailure};
use prism_syntax::kw;
use prism_syntax::names;

use crate::core::builtins::Builtin;
use crate::types::sig::parse_checked_signature;
use crate::types::ty::{EffRow, Kind, Label};
use crate::types::{CtorInfo, EffOpInfo, Type};

use super::super::verify::{
    clone_type, rename_row_variable_in_row, rename_row_variable_in_type, rename_type_variable,
    rename_type_variable_in_row, representation_preserving_stable,
};
use super::super::violation::{BuildError, SchemeError};
use super::super::{
    scheme_to_fn_sig, CompSig, ConstructorSig, CoreFnSig, CoreQuantifier, CoreType, LoweredType,
    OperationSig, VerifyEnv,
};

const INTRINSIC_ITEM: &str = "typed Core intrinsic";

/// Translate a checked source function scheme to its Core calling convention.
///
/// # Errors
/// A message naming the scheme, when what it peels down to is not a function
/// type and so has no calling convention.
pub fn core_fn_sig(scheme: &Type, prefix: Vec<CoreType>) -> Result<CoreFnSig, SchemeError> {
    let (quantifiers, body) = peel_quantifiers(scheme);
    let Type::Fun(params, effects, result) = body else {
        return Err(SchemeError {
            found: body.clone(),
        });
    };
    let mut lowered = prefix;
    lowered.extend(params.iter().map(lower_value_type));
    Ok(normalize_core_sig(&CoreFnSig::new(
        quantifiers,
        lowered,
        CompSig::new(lower_value_type(result), effects.clone()),
    )))
}

// Inference may generalize a fresh ambient tail even when the body is pure
// (`forall e. () -> Int ! e`). Core records the effects the body actually
// performs. A row tail remains semantic when it is tied to a parameter/result
// (the usual higher-order forwarding case); a top-level-only tail is vacuous and
// is closed here together with its now-unused quantifier.
fn normalize_core_sig(sig: &CoreFnSig) -> CoreFnSig {
    let escaping = escaping_effects(sig.body());
    let params = sig
        .params()
        .iter()
        .map(|param| remove_escaping_label_contamination(param, &escaping))
        .collect();
    let sig = CoreFnSig::new(sig.quantifiers().to_vec(), params, sig.body().clone());
    let EffRow::Var(tail) = sig.body().effects().tail() else {
        return sig;
    };
    let tail = *tail;
    let mut used = BTreeSet::new();
    for param in sig.params() {
        core_row_vars(param, &mut used);
    }
    core_row_vars(sig.body().result(), &mut used);
    for label in sig.body().effects().labels() {
        for arg in &label.args {
            arg.free_row_vars(&mut used);
        }
    }
    if used.contains(&tail) {
        return sig;
    }
    let effects = EffRow::canonical(
        sig.body().effects().labels().into_iter().cloned(),
        EffRow::Empty,
    );
    CoreFnSig::new(
        sig.quantifiers()
            .iter()
            .filter(|quantifier| !matches!(quantifier, CoreQuantifier::Row(name) if *name == tail))
            .cloned()
            .collect(),
        sig.params().to_vec(),
        CompSig::new(sig.body().result().clone(), effects),
    )
}

fn escaping_effects(signature: &CompSig) -> EffRow {
    let mut labels: Vec<Label> = signature.effects().labels().into_iter().cloned().collect();
    if let CoreType::Thunk(thunk) = signature.result() {
        labels.extend(thunk.effects().labels().into_iter().cloned());
        if let CoreType::Function(function) = thunk.result() {
            labels.extend(
                escaping_effects(function.body())
                    .labels()
                    .into_iter()
                    .cloned(),
            );
        }
    }
    EffRow::canonical(labels, EffRow::Empty)
}

// A handler over a higher-order input has two rows: the handled input row and
// the row performed by its clauses after discharge. Legacy row inference uses
// equality to connect the handled body's residual tail to the outer row, so an
// escaping `Emit(b)` can flow backward into an input already carrying
// `Emit(a)`, leaving both instantiations on that parameter. Core rows admit one
// instantiation of an effect per scope. If a latent parameter row contains two
// labels with one name and one of them is exactly an enclosing escaping label,
// remove that enclosing copy; the other label is the handler-scoped input.
fn remove_escaping_label_contamination(ty: &CoreType, outer: &EffRow) -> CoreType {
    match ty {
        CoreType::Thunk(signature) => {
            let result = match signature.result() {
                CoreType::Function(function) => {
                    let labels = function.body().effects().labels();
                    let effects = EffRow::canonical(
                        labels
                            .iter()
                            .copied()
                            .filter(|label| {
                                let has_distinct_peer = labels
                                    .iter()
                                    .any(|peer| peer.name == label.name && *peer != *label);
                                !(has_distinct_peer
                                    && outer.labels().into_iter().any(|item| item == *label))
                            })
                            .cloned(),
                        function.body().effects().tail().clone(),
                    );
                    let function = CoreFnSig::new(
                        function.quantifiers().to_vec(),
                        function
                            .params()
                            .iter()
                            .map(|param| remove_escaping_label_contamination(param, outer))
                            .collect(),
                        CompSig::new(function.body().result().clone(), effects),
                    );
                    CoreType::Function(Box::new(function))
                }
                other => remove_escaping_label_contamination(other, outer),
            };
            CoreType::Thunk(Box::new(CompSig::new(result, signature.effects().clone())))
        }
        CoreType::Function(function) => CoreType::Function(Box::new(CoreFnSig::new(
            function.quantifiers().to_vec(),
            function
                .params()
                .iter()
                .map(|param| remove_escaping_label_contamination(param, outer))
                .collect(),
            function.body().clone(),
        ))),
        CoreType::Ref(inner) => {
            CoreType::Ref(Box::new(remove_escaping_label_contamination(inner, outer)))
        }
        CoreType::ReuseToken(inner) => {
            CoreType::ReuseToken(Box::new(remove_escaping_label_contamination(inner, outer)))
        }
        CoreType::Source(_) | CoreType::Lowered(_) => ty.clone(),
    }
}

pub(super) fn core_row_vars(ty: &CoreType, rows: &mut BTreeSet<Sym>) {
    match ty {
        CoreType::Source(ty) => ty.free_row_vars(rows),
        CoreType::Thunk(sig) => {
            core_row_vars(sig.result(), rows);
            row_vars(sig.effects(), rows);
        }
        CoreType::Function(sig) => {
            for param in sig.params() {
                core_row_vars(param, rows);
            }
            core_row_vars(sig.body().result(), rows);
            row_vars(sig.body().effects(), rows);
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => core_row_vars(inner, rows),
        CoreType::Lowered(LoweredType::Word) => {}
        CoreType::Lowered(
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row),
        ) => row_vars(row, rows),
    }
}

pub(super) fn row_vars(row: &EffRow, rows: &mut BTreeSet<Sym>) {
    if let EffRow::Var(name) = row.tail() {
        rows.insert(*name);
    }
    for label in row.labels() {
        for arg in &label.args {
            arg.free_row_vars(rows);
        }
    }
}

fn peel_quantifiers(mut ty: &Type) -> (Vec<CoreQuantifier>, &Type) {
    let mut quantifiers = Vec::new();
    loop {
        match ty {
            Type::Forall(name, body) => {
                quantifiers.push(CoreQuantifier::Type(*name));
                ty = body;
            }
            Type::RowForall(name, body) => {
                quantifiers.push(CoreQuantifier::Row(*name));
                ty = body;
            }
            _ => return (quantifiers, ty),
        }
    }
}

pub(crate) fn lower_value_type(ty: &Type) -> CoreType {
    enum Task {
        Type(Type),
        Function(Vec<CoreQuantifier>, usize, EffRow),
    }

    let mut work = vec![Task::Type(clone_type(ty))];
    let mut output = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Type(mut ty) => {
                let mut quantifiers = Vec::new();
                let body = loop {
                    match ty {
                        Type::Forall(name, body) => {
                            quantifiers.push(CoreQuantifier::Type(name));
                            ty = *body;
                        }
                        Type::RowForall(name, body) => {
                            quantifiers.push(CoreQuantifier::Row(name));
                            ty = *body;
                        }
                        body => break body,
                    }
                };
                match body {
                    Type::Fun(params, effects, result) => {
                        let (quantifiers, params, effects, result) =
                            hygienic_nested_fn(quantifiers, params, effects, *result);
                        work.push(Task::Function(quantifiers, params.len(), effects));
                        work.push(Task::Type(result));
                        work.extend(params.into_iter().rev().map(Task::Type));
                    }
                    Type::Coeffect(inner, _) => work.push(Task::Type(*inner)),
                    body => {
                        let source =
                            quantifiers
                                .into_iter()
                                .rev()
                                .fold(body, |body, quantifier| match quantifier {
                                    CoreQuantifier::Type(name) => {
                                        Type::Forall(name, Box::new(body))
                                    }
                                    CoreQuantifier::Row(name) => {
                                        Type::RowForall(name, Box::new(body))
                                    }
                                });
                        output.push(CoreType::Source(source));
                    }
                }
            }
            Task::Function(quantifiers, param_count, effects) => {
                let result = output.pop().expect("function result type is available");
                let start = output.len() - param_count;
                let params = output.drain(start..).collect();
                let signature = CoreFnSig::new(quantifiers, params, CompSig::new(result, effects));
                output.push(CoreType::Thunk(Box::new(CompSig::new(
                    CoreType::Function(Box::new(signature)),
                    EffRow::Empty,
                ))));
            }
        }
    }
    output.pop().expect("type lowering produces one Core type")
}

fn hygienic_nested_fn(
    mut quantifiers: Vec<CoreQuantifier>,
    params: Vec<Type>,
    effects: EffRow,
    result: Type,
) -> (Vec<CoreQuantifier>, Vec<Type>, EffRow, Type) {
    let mut params = params;
    let mut effects = effects;
    let mut result = result;
    for (index, quantifier) in quantifiers.iter_mut().enumerate() {
        match quantifier {
            CoreQuantifier::Type(name) => {
                let old = *name;
                let fresh = Sym::from(names::typed_bound(old.as_str(), index));
                params = params
                    .iter()
                    .map(|ty| rename_type_variable(ty, old, fresh))
                    .collect();
                effects = rename_type_variable_in_row(&effects, old, fresh);
                result = rename_type_variable(&result, old, fresh);
                *name = fresh;
            }
            CoreQuantifier::Row(name) => {
                let old = *name;
                let fresh = Sym::from(names::typed_bound(old.as_str(), index));
                params = params
                    .iter()
                    .map(|ty| rename_row_variable_in_type(ty, old, fresh))
                    .collect();
                effects = rename_row_variable_in_row(&effects, old, fresh);
                result = rename_row_variable_in_type(&result, old, fresh);
                *name = fresh;
            }
        }
    }
    (quantifiers, params, effects, result)
}

const fn declared_argument(param: Sym, kind: &Kind) -> Type {
    match kind {
        Kind::Row => Type::Row(EffRow::Var(param)),
        Kind::Type | Kind::Nat | Kind::Fun(_, _) => Type::Var(param),
    }
}

/// Build the constructor, operation, and intrinsic signature environment from
/// the same checked declarations the source elaborator consumes.
///
/// # Errors
/// [`TypedCoreEnvironmentFailure::InvalidSignature`] when a wired-in builtin or
/// intrinsic signature does not parse, or does not lower to a function
/// signature.
pub fn build_verify_env(
    ctors: &BTreeMap<String, CtorInfo>,
    eff_ops: &BTreeMap<String, EffOpInfo>,
) -> Result<VerifyEnv, Error> {
    let mut env = VerifyEnv::new();
    for (name, info) in ctors {
        let quantifiers = info
            .params
            .iter()
            .zip(&info.param_kinds)
            .map(|(param, kind)| match kind {
                Kind::Row => CoreQuantifier::Row(*param),
                Kind::Type | Kind::Nat | Kind::Fun(_, _) => CoreQuantifier::Type(*param),
            })
            .collect();
        let result = Type::Con(
            info.type_name,
            info.params
                .iter()
                .zip(&info.param_kinds)
                .map(|(param, kind)| declared_argument(*param, kind))
                .collect(),
        );
        env.insert_constructor(
            Sym::from(name),
            ConstructorSig::new(
                quantifiers,
                info.tag,
                info.args.iter().map(lower_value_type).collect(),
                CoreType::Source(result),
            ),
        );
    }
    // `OrNull` is a wired-in representation type rather than a source data
    // declaration, so its two constructors are absent from `checked.ctors`.
    // Give the typed environment the same canonical shapes used by inference
    // and code generation.
    let element = Sym::from("$typed_or_null_element");
    let result = CoreType::Source(Type::OrNull(Box::new(Type::Var(element))));
    env.insert_constructor(
        Sym::from(kw::CTOR_NULL),
        ConstructorSig::new(
            vec![CoreQuantifier::Type(element)],
            kw::OR_NULL_TAG,
            Vec::new(),
            result.clone(),
        ),
    );
    env.insert_constructor(
        Sym::from(kw::CTOR_THIS),
        ConstructorSig::new(
            vec![CoreQuantifier::Type(element)],
            kw::OR_THIS_TAG,
            vec![CoreType::Source(Type::Var(element))],
            result,
        ),
    );
    for (name, info) in eff_ops {
        let mut params = info.params.clone();
        let mut ret = info.ret.clone();
        let mut quantifiers: Vec<_> = info
            .eff_params
            .iter()
            .map(|param| CoreQuantifier::Type(*param))
            .collect();
        let mut effect_args: Vec<_> = info
            .eff_params
            .iter()
            .map(|param| Type::Var(*param))
            .collect();
        // Non-resuming throw-like operations have a hygienic result variable
        // that is intentionally fresh at every perform site but is not an
        // effect parameter. Retain all such operation-local polymorphism in the
        // explicit Core scheme.
        let mut free_types = BTreeSet::new();
        let mut free_rows = BTreeSet::new();
        for param in &params {
            param.free_ty_vars(&mut free_types);
            param.free_row_vars(&mut free_rows);
        }
        ret.free_ty_vars(&mut free_types);
        ret.free_row_vars(&mut free_rows);
        for param in &info.eff_params {
            free_types.remove(param);
        }
        quantifiers.extend(free_types.into_iter().map(CoreQuantifier::Type));
        quantifiers.extend(free_rows.into_iter().map(CoreQuantifier::Row));
        // Desugared `var` effects pin their cell type with a checker
        // existential shared by the generated get/put declarations. Checked
        // operation metadata intentionally retains that marker. Open any such
        // declaration existential as explicit typed-Core polymorphism so each
        // perform site carries concrete evidence rather than leaking an
        // unsolved `Exist` into the verification environment.
        let mut declaration_existentials = BTreeSet::new();
        for param in &params {
            param.free_exist(&mut declaration_existentials);
        }
        ret.free_exist(&mut declaration_existentials);
        for id in declaration_existentials {
            let variable = Sym::from(format!("$typed_op_{name}_{id}"));
            params = params
                .into_iter()
                .map(|param| param.subst_exist(id, &Type::Var(variable)))
                .collect();
            ret = ret.subst_exist(id, &Type::Var(variable));
            quantifiers.push(CoreQuantifier::Type(variable));
            effect_args.push(Type::Var(variable));
        }
        env.insert_operation(
            Sym::from(name),
            OperationSig::new(
                quantifiers,
                params.iter().map(lower_value_type).collect(),
                lower_value_type(&ret),
                Label {
                    name: info.effect_name,
                    args: effect_args,
                },
            ),
        );
    }

    for (builtin, signature) in [
        (Builtin::BigLit, "(String) -> Int"),
        (Builtin::I64Add, "(I64, I64) -> I64"),
        (Builtin::I64Sub, "(I64, I64) -> I64"),
        (Builtin::I64Mul, "(I64, I64) -> I64"),
        (Builtin::I64Div, "(I64, I64) -> I64"),
        (Builtin::I64Rem, "(I64, I64) -> I64"),
        (Builtin::U64Add, "(U64, U64) -> U64"),
        (Builtin::U64Sub, "(U64, U64) -> U64"),
        (Builtin::U64Mul, "(U64, U64) -> U64"),
        (Builtin::U64Div, "(U64, U64) -> U64"),
        (Builtin::U64Rem, "(U64, U64) -> U64"),
        (Builtin::StringOfBytes, "(Array(Int)) -> String"),
        (Builtin::SortPrim, "forall a. (Int, List(a)) -> List(a)"),
    ] {
        let ty = parse_checked_signature(builtin.name(), signature).map_err(|error| {
            TypedCoreEnvironmentFailure::InvalidSignature {
                item: builtin.name().into(),
                detail: error.to_string(),
            }
        })?;
        let signature = scheme_to_fn_sig(ty).map_err(|error| {
            TypedCoreEnvironmentFailure::InvalidSignature {
                item: builtin.name().into(),
                detail: error.to_string(),
            }
        })?;
        env.insert_builtin_override(builtin, signature);
    }
    Ok(env)
}

#[must_use]
pub fn dict_type(class: Sym, argument: Type) -> CoreType {
    CoreType::Source(Type::Con(
        Sym::from(&names::dict_ctor(class.as_str())),
        vec![argument],
    ))
}

/// Recover the source-language shape stored inside a Core product witness.
/// Functions use the CBPV thunk/function encoding at value level, so this is
/// deliberately the inverse of `lower_value_type` rather than a simple unwrap.
///
/// State fusion needs the same inverse to compute the type argument a producer's
/// accumulator quantifier is instantiated with at each call site, so this is the
/// one home for it rather than a second copy that could drift from
/// `lower_value_type`.
pub(crate) fn source_type(ty: &CoreType) -> Result<Type, BuildError> {
    match ty {
        CoreType::Source(ty) => Ok(ty.clone()),
        CoreType::Thunk(sig)
            if sig.effects() == &EffRow::Empty && matches!(sig.result(), CoreType::Function(_)) =>
        {
            let CoreType::Function(function) = sig.result() else {
                unreachable!()
            };
            let mut ty = Type::Fun(
                function
                    .params()
                    .iter()
                    .map(source_type)
                    .collect::<Result<Vec<_>, _>>()?,
                function.body().effects().clone(),
                Box::new(source_type(function.body().result())?),
            );
            for quantifier in function.quantifiers().iter().rev() {
                ty = match quantifier {
                    CoreQuantifier::Type(name) => Type::Forall(*name, Box::new(ty)),
                    CoreQuantifier::Row(name) => Type::RowForall(*name, Box::new(ty)),
                };
            }
            Ok(ty)
        }
        other => Err(BuildError::NoSourceType {
            found: other.clone(),
        }),
    }
}

/// The elaboration-time cast rule is the substitution-stable one: an expected
/// row whose tail is still an open variable absorbs nothing, because at this
/// point an open tail means the solver has not committed the row, and taking
/// the cast would skip the subsumption that records the actual row's labels
/// into that variable. The solver would then be free to close it without
/// them, leaving a cast the final verifier rejects as effect laundering.
pub(super) fn representation_preserving(actual: &CoreType, expected: &CoreType) -> bool {
    representation_preserving_stable(actual, expected)
}

pub(super) fn intrinsic_sig(text: &str) -> Result<CoreFnSig, BuildError> {
    let ty = parse_checked_signature(INTRINSIC_ITEM, text).map_err(|error| {
        BuildError::SignatureParse {
            item: INTRINSIC_ITEM,
            error: error.to_string(),
        }
    })?;
    scheme_to_fn_sig(ty).map_err(BuildError::Scheme)
}

pub(super) fn subtract_names(row: &EffRow, effects: &[Sym]) -> EffRow {
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !effects.contains(&label.name))
            .cloned(),
        row.tail().clone(),
    )
}

pub(super) fn subtract_labels(row: &EffRow, effects: &BTreeSet<Label>) -> EffRow {
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !effects.contains(*label))
            .cloned(),
        row.tail().clone(),
    )
}
