//! Typed builders at the elaboration boundary.
//!
//! The builder consumes the elaborator's executable Core as a compatibility
//! input, reconstructs witnesses from checked declaration schemes, verifies the
//! result, and erases at the typed-prefix boundary. No source inference is
//! called here.

use std::collections::{BTreeMap, BTreeSet};

use crate::error::{Error, TypedCoreConstructionFailure, TypedCoreEnvironmentFailure};
use crate::kw;
use crate::names::{self, IO_EFFECT};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Kind, Label};
use crate::types::{Checked, Type};

use super::{
    instantiate_constructor, instantiate_fn, instantiate_operation, scheme_to_fn_sig, CompSig,
    ConstructorSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, Elaborated,
    LoweredType, OperationSig, TypedBinder, TypedComp, TypedCompKind, TypedCore, TypedCoreFn,
    TypedForward, TypedHandleOp, TypedHandler, TypedPattern, TypedValue, TypedValueKind, VerifyEnv,
};
use crate::core::builtins::Builtin;
use crate::core::{CheckedHandler, Comp, Core, CoreOp, CorePat, IoOp, NegLane, Value};

/// Translate a checked source function scheme to its Core calling convention.
pub(in crate::core) fn core_fn_sig(
    scheme: &Type,
    prefix: Vec<CoreType>,
) -> Result<CoreFnSig, String> {
    let (quantifiers, body) = peel_quantifiers(scheme);
    let Type::Fun(params, effects, result) = body else {
        return Err(format!("expected function scheme, got {body:?}"));
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

fn core_row_vars(ty: &CoreType, rows: &mut BTreeSet<Sym>) {
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

fn row_vars(row: &EffRow, rows: &mut BTreeSet<Sym>) {
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

pub(super) fn lower_value_type(ty: &Type) -> CoreType {
    let (quantifiers, body) = peel_quantifiers(ty);
    match body {
        Type::Fun(params, effects, result) => {
            let (quantifiers, params, effects, result) =
                hygienic_nested_fn(quantifiers, params, effects, result);
            let signature = CoreFnSig::new(
                quantifiers,
                params.iter().map(lower_value_type).collect(),
                CompSig::new(lower_value_type(&result), effects),
            );
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(signature)),
                EffRow::Empty,
            )))
        }
        Type::Coeffect(inner, _) => lower_value_type(inner),
        _ => CoreType::Source(ty.clone()),
    }
}

fn hygienic_nested_fn(
    mut quantifiers: Vec<CoreQuantifier>,
    params: &[Type],
    effects: &EffRow,
    result: &Type,
) -> (Vec<CoreQuantifier>, Vec<Type>, EffRow, Type) {
    let mut params = params.to_vec();
    let mut effects = effects.clone();
    let mut result = result.clone();
    for (index, quantifier) in quantifiers.iter_mut().enumerate() {
        match quantifier {
            CoreQuantifier::Type(name) => {
                let old = *name;
                let fresh = Sym::from(format!("{old}$typed_bound{index}"));
                params = params
                    .iter()
                    .map(|ty| ty.subst_var(old, &Type::Var(fresh)))
                    .collect();
                effects = effects.map_args(&|ty| ty.subst_var(old, &Type::Var(fresh)));
                result = result.subst_var(old, &Type::Var(fresh));
                *name = fresh;
            }
            CoreQuantifier::Row(name) => {
                let old = *name;
                let fresh = Sym::from(format!("{old}$typed_bound{index}"));
                params = params
                    .iter()
                    .map(|ty| ty.subst_row_var(old, &EffRow::Var(fresh)))
                    .collect();
                effects = effects.subst_row_var(old, &EffRow::Var(fresh));
                result = result.subst_row_var(old, &EffRow::Var(fresh));
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
pub(in crate::core) fn build_verify_env(checked: &Checked) -> Result<VerifyEnv, Error> {
    let mut env = VerifyEnv::new();
    for (name, info) in &checked.ctors {
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
    for (name, info) in &checked.eff_ops {
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
        let ty =
            crate::tc::parse_checked_signature(builtin.name(), signature).map_err(|error| {
                TypedCoreEnvironmentFailure::InvalidSignature {
                    item: builtin.name().into(),
                    detail: error.to_string(),
                }
            })?;
        let signature = scheme_to_fn_sig(ty).map_err(|detail| {
            TypedCoreEnvironmentFailure::InvalidSignature {
                item: builtin.name().into(),
                detail,
            }
        })?;
        env.insert_builtin_override(builtin, signature);
    }
    Ok(env)
}

pub(in crate::core) fn dict_type(class: Sym, argument: Type) -> CoreType {
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
pub(in crate::core) fn source_type(ty: &CoreType) -> Result<Type, String> {
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
        other => Err(format!(
            "typed builder: {other:?} has no source-language value type"
        )),
    }
}

fn representation_preserving(actual: &CoreType, expected: &CoreType) -> bool {
    if matches!(
        (actual, expected),
        (CoreType::Source(Type::Int), CoreType::Source(Type::Char))
            | (CoreType::Source(Type::Char), CoreType::Source(Type::Int))
    ) {
        return true;
    }
    let (CoreType::Thunk(actual), CoreType::Thunk(expected)) = (actual, expected) else {
        return false;
    };
    let (CoreType::Function(actual_fn), CoreType::Function(expected_fn)) =
        (actual.result(), expected.result())
    else {
        return false;
    };
    actual.effects() == expected.effects()
        && actual_fn.quantifiers() == expected_fn.quantifiers()
        && actual_fn.params() == expected_fn.params()
        && actual_fn.body().result() == expected_fn.body().result()
}

fn intrinsic_sig(text: &str) -> Result<CoreFnSig, String> {
    let ty = crate::tc::parse_checked_signature("typed Core intrinsic", text)
        .map_err(|error| error.to_string())?;
    scheme_to_fn_sig(ty)
}

fn subtract_names(row: &EffRow, effects: &[Sym]) -> EffRow {
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !effects.contains(&label.name))
            .cloned(),
        row.tail().clone(),
    )
}

fn subtract_labels(row: &EffRow, effects: &BTreeSet<Label>) -> EffRow {
    EffRow::canonical(
        row.labels()
            .into_iter()
            .filter(|label| !effects.contains(*label))
            .cloned(),
        row.tail().clone(),
    )
}

#[derive(Clone, Default)]
struct Solver {
    next: u32,
    core: BTreeMap<u32, CoreType>,
    types: BTreeMap<u32, Type>,
    rows: BTreeMap<u32, EffRow>,
    int_defaults: BTreeSet<u32>,
}

impl Solver {
    const fn fresh_core(&mut self) -> CoreType {
        let id = self.bump();
        CoreType::Source(Type::Exist(id))
    }

    const fn fresh_type(&mut self) -> Type {
        let id = self.bump();
        Type::Exist(id)
    }

    fn fresh_int_core(&mut self) -> CoreType {
        let id = self.bump();
        self.int_defaults.insert(id);
        CoreType::Source(Type::Exist(id))
    }

    const fn fresh_row(&mut self) -> EffRow {
        let id = self.bump();
        EffRow::Exist(id)
    }

    const fn bump(&mut self) -> u32 {
        let id = self.next;
        self.next = self
            .next
            .checked_add(1)
            .expect("typed builder metavariable overflow");
        id
    }

    fn fresh_instantiation(&mut self, quantifiers: &[CoreQuantifier]) -> Vec<CoreInstantiation> {
        quantifiers
            .iter()
            .map(|quantifier| match quantifier {
                CoreQuantifier::Type(_) => CoreInstantiation::Type(self.fresh_type()),
                CoreQuantifier::Row(_) => CoreInstantiation::Row(self.fresh_row()),
            })
            .collect()
    }

    fn resolve_core(&self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Source(Type::Exist(id)) if self.core.contains_key(id) => {
                self.resolve_core(&self.core[id])
            }
            CoreType::Source(ty) => {
                let resolved = self.resolve_type(ty);
                if let Type::Exist(id) = resolved {
                    if let Some(core) = self.core.get(&id) {
                        return self.resolve_core(core);
                    }
                }
                lower_value_type(&resolved)
            }
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.resolve_sig(sig))),
            CoreType::Function(sig) => CoreType::Function(Box::new(self.resolve_fn_sig(sig))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.resolve_core(inner))),
            CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(self.resolve_core(inner))),
            CoreType::Lowered(kind) => CoreType::Lowered(match kind {
                LoweredType::Word => LoweredType::Word,
                LoweredType::Eff(row) => LoweredType::Eff(self.resolve_row(row)),
                LoweredType::Queue(row) => LoweredType::Queue(self.resolve_row(row)),
                LoweredType::QueueView(row) => LoweredType::QueueView(self.resolve_row(row)),
            }),
        }
    }

    // Reveal only enough structure to choose a Core typing rule. Keeping the
    // interior witnesses un-zonked is important for subsumption: an expected
    // function row may still carry the original flexible tail whose lower
    // bound has already accumulated labels from an earlier argument.
    fn resolve_core_head(&self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Source(Type::Exist(id)) if self.core.contains_key(id) => {
                self.resolve_core_head(&self.core[id])
            }
            CoreType::Source(Type::Exist(_)) => {
                let resolved = self.resolve_type(match ty {
                    CoreType::Source(source) => source,
                    _ => unreachable!(),
                });
                if let Type::Exist(id) = resolved {
                    if let Some(core) = self.core.get(&id) {
                        return self.resolve_core_head(core);
                    }
                }
                lower_value_type(&resolved)
            }
            _ => ty.clone(),
        }
    }

    fn resolve_sig(&self, sig: &CompSig) -> CompSig {
        CompSig::new(
            self.resolve_core(sig.result()),
            self.resolve_row(sig.effects()),
        )
    }

    fn resolve_fn_sig(&self, sig: &CoreFnSig) -> CoreFnSig {
        CoreFnSig::new(
            sig.quantifiers().to_vec(),
            sig.params()
                .iter()
                .map(|ty| self.resolve_core(ty))
                .collect(),
            self.resolve_sig(sig.body()),
        )
    }

    fn resolve_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Exist(id) if self.types.contains_key(id) => self.resolve_type(&self.types[id]),
            Type::Forall(name, body) => Type::Forall(*name, Box::new(self.resolve_type(body))),
            Type::RowForall(name, body) => {
                Type::RowForall(*name, Box::new(self.resolve_type(body)))
            }
            Type::Fun(params, row, result) => Type::Fun(
                params.iter().map(|ty| self.resolve_type(ty)).collect(),
                self.resolve_row(row),
                Box::new(self.resolve_type(result)),
            ),
            Type::Con(name, args) => {
                Type::Con(*name, args.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::App(head, arg) => Type::app(self.resolve_type(head), self.resolve_type(arg)),
            Type::Tuple(fields) => {
                Type::Tuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedTuple(fields) => {
                Type::UnboxedTuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedRecord(fields) => Type::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.resolve_type(ty)))
                    .collect(),
            ),
            Type::OrNull(inner) => Type::OrNull(Box::new(self.resolve_type(inner))),
            Type::Row(row) => Type::Row(self.resolve_row(row)),
            Type::Coeffect(inner, row) => {
                Type::Coeffect(Box::new(self.resolve_type(inner)), row.clone())
            }
            _ => ty.clone(),
        }
    }

    fn resolve_row(&self, row: &EffRow) -> EffRow {
        match row {
            EffRow::Exist(id) if self.rows.contains_key(id) => self.resolve_row(&self.rows[id]),
            EffRow::Extend(label, rest) => {
                let rest = self.resolve_row(rest);
                EffRow::canonical(
                    std::iter::once(Label {
                        name: label.name,
                        args: label.args.iter().map(|ty| self.resolve_type(ty)).collect(),
                    })
                    .chain(rest.labels().into_iter().cloned()),
                    rest.tail().clone(),
                )
            }
            _ => row.clone(),
        }
    }

    fn unify_core(&mut self, left: &CoreType, right: &CoreType) -> Result<(), String> {
        let left = self.resolve_core(left);
        let right = self.resolve_core(right);
        if left == right {
            return Ok(());
        }
        match (&left, &right) {
            // Keep source metavariables in the source substitution table so
            // the same solution also zonks explicit type instantiations. The
            // Core table is reserved for a placeholder that is discovered to
            // have a genuinely non-source CBPV shape (Function/Thunk/etc.).
            (CoreType::Source(a), CoreType::Source(b)) => self.unify_type(a, b),
            (CoreType::Source(Type::Exist(id)), other)
            | (other, CoreType::Source(Type::Exist(id))) => {
                if core_occurs(*id, other) {
                    return Err(format!("recursive Core metavariable ?{id} in {other:?}"));
                }
                self.core.insert(*id, other.clone());
                Ok(())
            }
            (CoreType::Thunk(a), CoreType::Thunk(b)) => self.unify_sig(a, b),
            (CoreType::Function(a), CoreType::Function(b)) => self.unify_fn_sig(a, b),
            (CoreType::Ref(a), CoreType::Ref(b))
            | (CoreType::ReuseToken(a), CoreType::ReuseToken(b)) => self.unify_core(a, b),
            _ => Err(format!("cannot unify Core types {left:?} and {right:?}")),
        }
    }

    fn unify_sig(&mut self, left: &CompSig, right: &CompSig) -> Result<(), String> {
        self.unify_core(left.result(), right.result())
            .map_err(|error| format!("computation result: {error}"))?;
        self.unify_row(left.effects(), right.effects())
            .map_err(|error| format!("computation effects: {error}"))
    }

    fn unify_fn_sig(&mut self, left: &CoreFnSig, right: &CoreFnSig) -> Result<(), String> {
        if left.quantifiers() != right.quantifiers() || left.params().len() != right.params().len()
        {
            return Err(format!(
                "cannot unify function signatures {left:?} and {right:?}"
            ));
        }
        for (a, b) in left.params().iter().zip(right.params()) {
            self.unify_core(a, b)
                .map_err(|error| format!("function parameter: {error}"))?;
        }
        self.unify_sig(left.body(), right.body())
            .map_err(|error| format!("function body: {error}"))
    }

    fn subsume_core(&mut self, actual: &CoreType, expected: &CoreType) -> Result<(), String> {
        let actual = self.resolve_core_head(actual);
        let expected = self.resolve_core_head(expected);
        if actual == expected {
            return Ok(());
        }
        match (&actual, &expected) {
            (CoreType::Source(Type::Exist(_)), _) | (_, CoreType::Source(Type::Exist(_))) => {
                self.unify_core(&actual, &expected)
            }
            (CoreType::Source(a), CoreType::Source(b)) => self.unify_type(a, b),
            (CoreType::Thunk(a), CoreType::Thunk(b)) => self.subsume_sig(a, b),
            (CoreType::Function(a), CoreType::Function(b)) => self.subsume_fn_sig(a, b),
            (CoreType::Ref(a), CoreType::Ref(b))
            | (CoreType::ReuseToken(a), CoreType::ReuseToken(b)) => self.unify_core(a, b),
            _ => Err(format!(
                "Core type {actual:?} is not a subtype of {expected:?}"
            )),
        }
    }

    fn subsume_sig(&mut self, actual: &CompSig, expected: &CompSig) -> Result<(), String> {
        self.subsume_core(actual.result(), expected.result())?;
        self.subsume_row(actual.effects(), expected.effects())
    }

    fn subsume_fn_sig(&mut self, actual: &CoreFnSig, expected: &CoreFnSig) -> Result<(), String> {
        if actual.quantifiers() != expected.quantifiers()
            || actual.params().len() != expected.params().len()
        {
            return Err(format!(
                "function signature {actual:?} is not a subtype of {expected:?}"
            ));
        }
        for (actual, expected) in actual.params().iter().zip(expected.params()) {
            self.unify_core(actual, expected)?;
        }
        self.subsume_sig(actual.body(), expected.body())
    }

    fn subsume_row(&mut self, actual: &EffRow, expected: &EffRow) -> Result<(), String> {
        let flexible_expected = match expected.tail() {
            EffRow::Exist(id) => Some(*id),
            _ => None,
        };
        let actual = self.resolve_row(actual);
        let expected = self.resolve_row(expected);
        if actual == expected || actual == EffRow::Empty {
            return Ok(());
        }
        if matches!(actual, EffRow::Exist(_)) || matches!(expected, EffRow::Exist(_)) {
            return self.unify_row(&actual, &expected);
        }
        let mut unmatched = Vec::new();
        for label in actual.labels() {
            let Some(wanted) = expected
                .labels()
                .into_iter()
                .find(|wanted| wanted.name == label.name)
            else {
                if flexible_expected.is_some() {
                    unmatched.push(label.clone());
                    continue;
                }
                return Err(format!(
                    "effect row {} is not included in {}",
                    actual.show(),
                    expected.show()
                ));
            };
            if label.args.len() != wanted.args.len() {
                return Err(format!(
                    "effect label {} is not included in {}",
                    label.show(),
                    expected.show()
                ));
            }
            for (actual, expected) in label.args.iter().zip(&wanted.args) {
                self.unify_type(actual, expected)?;
            }
        }
        if let Some(id) = flexible_expected {
            return self.constrain_row_join(
                &EffRow::Exist(id),
                &EffRow::canonical(unmatched, actual.tail().clone()),
            );
        }
        match actual.tail() {
            EffRow::Empty => Ok(()),
            EffRow::Var(name) if expected.tail() == &EffRow::Var(*name) => Ok(()),
            actual_tail @ (EffRow::Var(_) | EffRow::Exist(_))
                if matches!(expected.tail(), EffRow::Exist(_)) =>
            {
                self.unify_row(actual_tail, expected.tail())
            }
            EffRow::Exist(_) => self.unify_row(actual.tail(), expected.tail()),
            _ => Err(format!(
                "effect row {} is not included in {}",
                actual.show(),
                expected.show()
            )),
        }
    }

    fn unify_type(&mut self, left: &Type, right: &Type) -> Result<(), String> {
        let left = self.resolve_type(left);
        let right = self.resolve_type(right);
        if left == right {
            return Ok(());
        }
        match (&left, &right) {
            // `Char` is represented by the integer lane and source coercions
            // such as `chr` are erased before CBPV elaboration. Keep that
            // representation equality available when a constraint arrives
            // only after an ANF producer has already fixed its witness.
            (Type::Int, Type::Char) | (Type::Char, Type::Int) => Ok(()),
            (Type::Exist(id), other) | (other, Type::Exist(id)) => {
                let mut occurs = BTreeSet::new();
                other.free_exist(&mut occurs);
                if occurs.contains(id) {
                    return Err(format!("recursive type metavariable ?{id} in {other:?}"));
                }
                // A source metavariable can already carry a richer CBPV shape
                // from an earlier ANF binding.  Reconcile that evidence before
                // recording its source-language view so row constraints are not
                // lost between the two solver tables.
                if let Some(actual) = self.core.get(id).cloned() {
                    self.subsume_core(&actual, &lower_value_type(other))?;
                }
                if self.int_defaults.contains(id) {
                    if let Type::Exist(other_id) = other {
                        self.int_defaults.insert(*other_id);
                    }
                }
                self.types.insert(*id, other.clone());
                Ok(())
            }
            (Type::Fun(ap, ae, ar), Type::Fun(bp, be, br)) if ap.len() == bp.len() => {
                for (a, b) in ap.iter().zip(bp) {
                    self.unify_type(a, b)?;
                }
                self.unify_row(ae, be)?;
                self.unify_type(ar, br)
            }
            (Type::Con(an, aa), Type::Con(bn, ba)) if an == bn && aa.len() == ba.len() => {
                for (a, b) in aa.iter().zip(ba) {
                    self.unify_type(a, b)?;
                }
                Ok(())
            }
            (Type::App(ah, aa), Type::App(bh, ba)) => {
                self.unify_type(ah, bh)?;
                self.unify_type(aa, ba)
            }
            (Type::Tuple(a), Type::Tuple(b)) | (Type::UnboxedTuple(a), Type::UnboxedTuple(b))
                if a.len() == b.len() =>
            {
                for (a, b) in a.iter().zip(b) {
                    self.unify_type(a, b)?;
                }
                Ok(())
            }
            (Type::UnboxedRecord(a), Type::UnboxedRecord(b)) if a.len() == b.len() => {
                for ((an, a), (bn, b)) in a.iter().zip(b) {
                    if an != bn {
                        return Err(format!("record field mismatch {an} and {bn}"));
                    }
                    self.unify_type(a, b)?;
                }
                Ok(())
            }
            (Type::OrNull(a), Type::OrNull(b)) => self.unify_type(a, b),
            (Type::Row(a), Type::Row(b)) => self.unify_row(a, b),
            (Type::Coeffect(a, ar), Type::Coeffect(b, br)) if ar == br => self.unify_type(a, b),
            _ => Err(format!("cannot unify source types {left:?} and {right:?}")),
        }
    }

    fn unify_row(&mut self, left: &EffRow, right: &EffRow) -> Result<(), String> {
        let left = self.resolve_row(left);
        let right = self.resolve_row(right);
        if left == right {
            return Ok(());
        }
        match (&left, &right) {
            (EffRow::Exist(id), other) | (other, EffRow::Exist(id)) => {
                let mut occurs = BTreeSet::new();
                other.free_exist_row(&mut occurs);
                if occurs.contains(id) {
                    // A resumed handler gives the least fixed-point equation
                    // `r = labels | r`. Effect rows are sets, so its solution is
                    // exactly `labels`; discard only the recursive tail.
                    if other.tail() == &EffRow::Exist(*id) {
                        self.rows.insert(
                            *id,
                            EffRow::canonical(other.labels().into_iter().cloned(), EffRow::Empty),
                        );
                        return Ok(());
                    }
                    return Err(format!("recursive row metavariable ?r{id} in {other:?}"));
                }
                self.rows.insert(*id, other.clone());
                Ok(())
            }
            _ => {
                if !matches!(left, EffRow::Extend(..)) && !matches!(right, EffRow::Extend(..)) {
                    return Err(format!(
                        "cannot unify effect-row tails {} and {}",
                        left.show(),
                        right.show()
                    ));
                }
                let left_labels = left.labels();
                let right_labels = right.labels();
                if left_labels.len() != right_labels.len() {
                    return Err(format!(
                        "cannot unify effect rows {} and {}",
                        left.show(),
                        right.show()
                    ));
                }
                for (a, b) in left_labels.iter().zip(right_labels) {
                    if a.name != b.name || a.args.len() != b.args.len() {
                        return Err(format!(
                            "cannot unify effect rows {} and {}",
                            left.show(),
                            right.show()
                        ));
                    }
                    for (a, b) in a.args.iter().zip(&b.args) {
                        self.unify_type(a, b)?;
                    }
                }
                self.unify_row(left.tail(), right.tail())
            }
        }
    }

    fn union_rows(&mut self, left: &EffRow, right: &EffRow) -> Result<EffRow, String> {
        // Empty is the identity of row union. Preserve a flexible row itself,
        // rather than resolving it to a snapshot of its current lower bound:
        // later constraints must remain visible to every parent that reused
        // this union.
        if left == &EffRow::Empty {
            return Ok(right.clone());
        }
        if right == &EffRow::Empty {
            return Ok(left.clone());
        }
        let left = self.resolve_row(left);
        let right = self.resolve_row(right);
        let tail = match (left.tail(), right.tail()) {
            (a, b) if a == b => a.clone(),
            (EffRow::Empty, other) | (other, EffRow::Empty) => other.clone(),
            (EffRow::Exist(id), other) | (other, EffRow::Exist(id)) => {
                self.unify_row(&EffRow::Exist(*id), other)?;
                self.resolve_row(&EffRow::Exist(*id))
            }
            (a, b) => {
                return Err(format!(
                    "cannot combine open effect rows {} and {}",
                    a.show(),
                    b.show()
                ));
            }
        };
        let mut labels: BTreeMap<Sym, Label> = BTreeMap::new();
        for label in left.labels().into_iter().chain(right.labels()) {
            if let Some(existing) = labels.get(&label.name).cloned() {
                if existing.args.len() != label.args.len() {
                    // Generated local-state rows predate explicit typed-Core
                    // evidence: a checked function row names the effect while
                    // its operation node carries the recovered cell type.
                    // Preserve the richer witness when the other occurrence
                    // is precisely the legacy zero-argument spelling.
                    if existing.args.is_empty() {
                        labels.insert(label.name, label.clone());
                        continue;
                    }
                    if label.args.is_empty() {
                        continue;
                    }
                    return Err(format!(
                        "cannot combine effect labels {} and {}",
                        existing.show(),
                        label.show()
                    ));
                }
                for (a, b) in existing.args.iter().zip(&label.args) {
                    self.unify_type(a, b)?;
                }
                labels.insert(
                    label.name,
                    Label {
                        name: label.name,
                        args: existing
                            .args
                            .iter()
                            .map(|ty| self.resolve_type(ty))
                            .collect(),
                    },
                );
            } else {
                labels.insert(label.name, label.clone());
            }
        }
        Ok(EffRow::canonical(labels.into_values(), tail))
    }

    fn join_core(&mut self, left: &CoreType, right: &CoreType) -> Result<CoreType, String> {
        let left = self.resolve_core(left);
        let right = self.resolve_core(right);
        if left == right {
            return Ok(left);
        }
        match (&left, &right) {
            (CoreType::Source(Type::Exist(_)), _) | (_, CoreType::Source(Type::Exist(_))) => {
                self.unify_core(&left, &right)?;
                Ok(self.resolve_core(&left))
            }
            (CoreType::Source(a), CoreType::Source(b)) => {
                self.unify_type(a, b)?;
                Ok(CoreType::Source(self.resolve_type(a)))
            }
            (CoreType::Thunk(a), CoreType::Thunk(b)) => {
                Ok(CoreType::Thunk(Box::new(self.join_sig(a, b)?)))
            }
            (CoreType::Function(a), CoreType::Function(b)) => {
                Ok(CoreType::Function(Box::new(self.join_fn_sig(a, b)?)))
            }
            (CoreType::Ref(a), CoreType::Ref(b)) => {
                Ok(CoreType::Ref(Box::new(self.join_core(a, b)?)))
            }
            (CoreType::ReuseToken(a), CoreType::ReuseToken(b)) => {
                Ok(CoreType::ReuseToken(Box::new(self.join_core(a, b)?)))
            }
            _ => Err(format!("cannot join Core types {left:?} and {right:?}")),
        }
    }

    fn constrain_join(&mut self, target: &CoreType, value: &CoreType) -> Result<(), String> {
        if let CoreType::Source(Type::Exist(id)) = target {
            let current = self.resolve_core(target);
            let joined = if current == *target {
                self.resolve_core(value)
            } else {
                self.join_core(&current, value)?
            };
            if joined == *target {
                // A pending application can make a handler's result lower bound
                // be the same still-flexible metavariable. This is a vacuous
                // constraint, not the recursive type `?a = F(?a)`; leave it open
                // for the resumed application to solve.
                return Ok(());
            }
            if core_occurs(*id, &joined) {
                return Err(format!(
                    "recursive Core metavariable ?{id} in joined type {joined:?}"
                ));
            }
            self.core.insert(*id, joined);
            Ok(())
        } else {
            let joined = self.join_core(target, value)?;
            if self.resolve_core(target) == joined {
                Ok(())
            } else {
                Err(format!(
                    "joined result {joined:?} exceeds expected type {:?}",
                    self.resolve_core(target)
                ))
            }
        }
    }

    fn constrain_row_join(&mut self, target: &EffRow, value: &EffRow) -> Result<(), String> {
        if let EffRow::Exist(id) = target {
            let root = self.row_root(*id);
            if root != *id {
                return self.constrain_row_join(&EffRow::Exist(root), value);
            }
            let current = self.resolve_row(target);
            let value = self.resolve_row(value);
            if value == EffRow::Empty {
                // Subsuming a pure computation contributes no lower bound to
                // an open expected row.  Leave it flexible for later
                // arguments in the same application.
                return Ok(());
            }
            if current != *target {
                if let EffRow::Exist(tail) = current.tail() {
                    return self.constrain_row_join(&EffRow::Exist(*tail), &value);
                }
            }
            let value = if value.tail() == &EffRow::Exist(*id) {
                // Rows denote sets, so `?r = {labels | ?r}` has the least
                // solution `{labels}`.  Closing only the recursive tail keeps
                // the concrete lower bound without installing a cyclic
                // substitution.
                EffRow::canonical(value.labels().into_iter().cloned(), EffRow::Empty)
            } else {
                value
            };
            let joined = if current == *target {
                value
            } else {
                self.union_rows(&current, &value)?
            };
            self.rows.insert(*id, joined);
            Ok(())
        } else {
            self.subsume_row(value, target)
        }
    }

    fn row_root(&self, mut id: u32) -> u32 {
        let mut seen = BTreeSet::new();
        while seen.insert(id) {
            let Some(EffRow::Exist(next)) = self.rows.get(&id) else {
                break;
            };
            id = *next;
        }
        id
    }

    fn join_sig(&mut self, left: &CompSig, right: &CompSig) -> Result<CompSig, String> {
        Ok(CompSig::new(
            self.join_core(left.result(), right.result())?,
            self.union_rows(left.effects(), right.effects())?,
        ))
    }

    fn join_fn_sig(&mut self, left: &CoreFnSig, right: &CoreFnSig) -> Result<CoreFnSig, String> {
        if left.quantifiers() != right.quantifiers() || left.params().len() != right.params().len()
        {
            return Err(format!(
                "cannot join function signatures {left:?} and {right:?}"
            ));
        }
        for (a, b) in left.params().iter().zip(right.params()) {
            self.unify_core(a, b)?;
        }
        Ok(CoreFnSig::new(
            left.quantifiers().to_vec(),
            left.params()
                .iter()
                .map(|ty| self.resolve_core(ty))
                .collect(),
            self.join_sig(left.body(), right.body())?,
        ))
    }

    fn zonk_instantiation(&self, instantiation: Vec<CoreInstantiation>) -> Vec<CoreInstantiation> {
        instantiation
            .into_iter()
            .map(|argument| match argument {
                CoreInstantiation::Type(ty) => CoreInstantiation::Type(self.resolve_type(&ty)),
                CoreInstantiation::Row(row) => CoreInstantiation::Row(self.resolve_row(&row)),
            })
            .collect()
    }
}

fn core_occurs(id: u32, ty: &CoreType) -> bool {
    fn source_occurs(id: u32, ty: &Type) -> bool {
        let mut types = BTreeSet::new();
        ty.free_exist(&mut types);
        types.contains(&id)
    }

    match ty {
        CoreType::Source(ty) => source_occurs(id, ty),
        CoreType::Thunk(sig) => {
            core_occurs(id, sig.result())
                || sig
                    .effects()
                    .labels()
                    .iter()
                    .any(|label| label.args.iter().any(|ty| source_occurs(id, ty)))
        }
        CoreType::Function(sig) => {
            sig.params().iter().any(|ty| core_occurs(id, ty))
                || core_occurs(id, sig.body().result())
                || sig
                    .body()
                    .effects()
                    .labels()
                    .iter()
                    .any(|label| label.args.iter().any(|ty| source_occurs(id, ty)))
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => core_occurs(id, inner),
        CoreType::Lowered(LoweredType::Word) => false,
        CoreType::Lowered(
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row),
        ) => row
            .labels()
            .iter()
            .any(|label| label.args.iter().any(|ty| source_occurs(id, ty))),
    }
}

fn free_row_vars(row: &EffRow, type_vars: &mut BTreeSet<Sym>, row_vars: &mut BTreeSet<Sym>) {
    if let EffRow::Var(name) = row.tail() {
        row_vars.insert(*name);
    }
    for label in row.labels() {
        for argument in &label.args {
            argument.free_ty_vars(type_vars);
            argument.free_row_vars(row_vars);
        }
    }
}

fn free_core_vars(ty: &CoreType, type_vars: &mut BTreeSet<Sym>, row_vars: &mut BTreeSet<Sym>) {
    match ty {
        CoreType::Source(ty) => {
            ty.free_ty_vars(type_vars);
            ty.free_row_vars(row_vars);
        }
        CoreType::Thunk(signature) => {
            free_core_vars(signature.result(), type_vars, row_vars);
            free_row_vars(signature.effects(), type_vars, row_vars);
        }
        CoreType::Function(signature) => {
            let mut nested_types = BTreeSet::new();
            let mut nested_rows = BTreeSet::new();
            for param in signature.params() {
                free_core_vars(param, &mut nested_types, &mut nested_rows);
            }
            free_core_vars(
                signature.body().result(),
                &mut nested_types,
                &mut nested_rows,
            );
            free_row_vars(
                signature.body().effects(),
                &mut nested_types,
                &mut nested_rows,
            );
            for quantifier in signature.quantifiers() {
                match quantifier {
                    CoreQuantifier::Type(name) => {
                        nested_types.remove(name);
                    }
                    CoreQuantifier::Row(name) => {
                        nested_rows.remove(name);
                    }
                }
            }
            type_vars.extend(nested_types);
            row_vars.extend(nested_rows);
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => {
            free_core_vars(inner, type_vars, row_vars);
        }
        CoreType::Lowered(LoweredType::Word) => {}
        CoreType::Lowered(
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row),
        ) => free_row_vars(row, type_vars, row_vars),
    }
}

struct Builder<'a> {
    globals: &'a BTreeMap<Sym, CoreFnSig>,
    verify_env: &'a VerifyEnv,
    solver: Solver,
    scopes: BTreeMap<Sym, Vec<(Sym, CoreType)>>,
    pending_handler_rows: Vec<PendingHandlerRow>,
}

struct PendingHandlerRow {
    target: EffRow,
    body: EffRow,
    handled: BTreeMap<Sym, Label>,
    clauses: EffRow,
}

impl<'a> Builder<'a> {
    fn new(globals: &'a BTreeMap<Sym, CoreFnSig>, verify_env: &'a VerifyEnv) -> Self {
        Self {
            globals,
            verify_env,
            solver: Solver::default(),
            scopes: BTreeMap::new(),
            pending_handler_rows: Vec::new(),
        }
    }

    fn bind(&mut self, raw: Sym, ty: CoreType) -> TypedBinder {
        self.scopes.entry(raw).or_default().push((raw, ty.clone()));
        TypedBinder::new(raw, ty)
    }

    fn unbind(&mut self, raw: Sym) {
        if let Some(stack) = self.scopes.get_mut(&raw) {
            stack.pop();
            if stack.is_empty() {
                self.scopes.remove(&raw);
            }
        }
    }

    fn local(&self, raw: Sym) -> Option<(Sym, CoreType)> {
        self.scopes
            .get(&raw)
            .and_then(|stack| stack.last())
            .cloned()
    }

    fn finish_comp(
        &mut self,
        sig: CompSig,
        kind: TypedCompKind,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        self.solve_pending_handler_rows(false)?;
        if let Some(expected) = expected {
            self.solver.subsume_sig(&sig, expected)?;
        }
        Ok(TypedComp::new(sig, kind))
    }

    fn solve_pending_handler_rows(&mut self, force: bool) -> Result<(), String> {
        let pending = std::mem::take(&mut self.pending_handler_rows);
        for constraint in pending {
            let resolved_body = self.solver.resolve_row(&constraint.body);
            if !force && resolved_body == constraint.body {
                self.pending_handler_rows.push(constraint);
                continue;
            }
            let effects = self.derive_handler_effects(
                &resolved_body,
                &constraint.handled,
                &constraint.clauses,
                &constraint.target,
            )?;
            self.solver
                .constrain_row_join(&constraint.target, &effects)?;
        }
        Ok(())
    }

    fn value(&mut self, value: Value, expected: Option<&CoreType>) -> Result<TypedValue, String> {
        let (ty, kind) = match value {
            Value::Var(raw) => {
                if let Some((name, ty)) = self.local(raw) {
                    let declared = self.solver.resolve_core_head(&ty);
                    let preserve_scheme = expected
                        .is_none_or(|expected| self.solver.resolve_core_head(expected) == declared);
                    let quantifiers = if preserve_scheme {
                        &[][..]
                    } else {
                        match &declared {
                            CoreType::Function(signature) => signature.quantifiers(),
                            CoreType::Thunk(signature) => match signature.result() {
                                CoreType::Function(function) => function.quantifiers(),
                                _ => &[],
                            },
                            _ => &[],
                        }
                    };
                    let instantiation = self.solver.fresh_instantiation(quantifiers);
                    let ty = if preserve_scheme {
                        ty
                    } else {
                        super::instantiate_value_scheme(&ty, &instantiation)?
                    };
                    (
                        ty,
                        TypedValueKind::Var {
                            name,
                            instantiation,
                        },
                    )
                } else {
                    let declared = self
                        .globals
                        .get(&raw)
                        .ok_or_else(|| format!("typed builder: unknown value reference {raw}"))?
                        .clone();
                    let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                    let instantiated = instantiate_fn(&declared, &instantiation)?;
                    (
                        CoreType::Function(Box::new(instantiated)),
                        TypedValueKind::Var {
                            name: raw,
                            instantiation,
                        },
                    )
                }
            }
            Value::Int(value) => {
                let ty = if let Some(expected) = expected {
                    if let CoreType::Source(Type::Exist(id)) = expected {
                        self.solver.int_defaults.insert(*id);
                    }
                    expected.clone()
                } else {
                    self.solver.fresh_int_core()
                };
                (ty, TypedValueKind::Int(value))
            }
            Value::I64(value) => (CoreType::Source(Type::I64), TypedValueKind::I64(value)),
            Value::U64(value) => (CoreType::Source(Type::U64), TypedValueKind::U64(value)),
            Value::Float(value) => (CoreType::Source(Type::Float), TypedValueKind::Float(value)),
            Value::Bool(value) => (CoreType::Source(Type::Bool), TypedValueKind::Bool(value)),
            Value::Unit => (CoreType::Source(Type::Unit), TypedValueKind::Unit),
            Value::Str(value) => (CoreType::Source(Type::Str), TypedValueKind::Str(value)),
            Value::Thunk(body) => {
                let expected = expected.map(|expected| self.solver.resolve_core_head(expected));
                let expected_sig = match &expected {
                    Some(CoreType::Thunk(signature)) => Some(signature.as_ref().clone()),
                    _ => None,
                };
                let body = self.comp(*body, expected_sig.as_ref())?;
                (
                    CoreType::Thunk(Box::new(body.sig().clone())),
                    TypedValueKind::Thunk(Box::new(body)),
                )
            }
            Value::Ctor(name, tag, fields) => {
                let declared = self
                    .verify_env
                    .constructor(name)
                    .ok_or_else(|| format!("typed builder: unknown constructor {name}"))?
                    .clone();
                let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                let instantiated = instantiate_constructor(&declared, &instantiation)?;
                if tag != instantiated.tag {
                    return Err(format!(
                        "typed builder: constructor {name} tag {tag} != {}",
                        instantiated.tag
                    ));
                }
                if let Some(expected) = expected {
                    self.solver.unify_core(&instantiated.result, expected)?;
                }
                if fields.len() != instantiated.fields.len() {
                    return Err(format!(
                        "typed builder: constructor {name} arity {} != {}",
                        fields.len(),
                        instantiated.fields.len()
                    ));
                }
                let fields = fields
                    .into_iter()
                    .zip(&instantiated.fields)
                    .map(|(field, expected)| self.value(field, Some(expected)))
                    .collect::<Result<Vec<_>, _>>()?;
                (
                    instantiated.result,
                    TypedValueKind::Ctor {
                        name,
                        tag,
                        instantiation,
                        fields,
                    },
                )
            }
            Value::Tuple(fields) => {
                let expected_fields = match expected {
                    Some(CoreType::Source(Type::Tuple(fields))) => Some(fields.clone()),
                    _ => None,
                };
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, field)| {
                        let expected = expected_fields
                            .as_ref()
                            .and_then(|fields| fields.get(index))
                            .map(lower_value_type);
                        self.value(field, expected.as_ref())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = Type::Tuple(
                    fields
                        .iter()
                        .map(|field| source_type(field.ty()))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                (CoreType::Source(ty), TypedValueKind::Tuple(fields))
            }
            Value::UnboxedTuple(fields) => {
                let expected_fields = match expected {
                    Some(CoreType::Source(Type::UnboxedTuple(fields))) => Some(fields.clone()),
                    Some(CoreType::Source(Type::UnboxedRecord(fields))) => {
                        Some(fields.iter().map(|(_, ty)| ty.clone()).collect())
                    }
                    _ => None,
                };
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, field)| {
                        let expected = expected_fields
                            .as_ref()
                            .and_then(|fields| fields.get(index))
                            .map(lower_value_type);
                        self.value(field, expected.as_ref())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let field_types = fields
                    .iter()
                    .map(|field| source_type(field.ty()))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = match expected {
                    Some(CoreType::Source(Type::UnboxedRecord(names))) => Type::UnboxedRecord(
                        names
                            .iter()
                            .zip(field_types)
                            .map(|((name, _), ty)| (*name, ty))
                            .collect(),
                    ),
                    _ => Type::UnboxedTuple(field_types),
                };
                (CoreType::Source(ty), TypedValueKind::UnboxedTuple(fields))
            }
            Value::UnboxedRecord(fields) => {
                let expected_fields = match expected {
                    Some(CoreType::Source(Type::UnboxedRecord(fields))) => Some(fields.clone()),
                    _ => None,
                };
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, (name, field))| {
                        let expected = expected_fields
                            .as_ref()
                            .and_then(|fields| fields.get(index))
                            .map(|(_, ty)| lower_value_type(ty));
                        Ok((name, self.value(field, expected.as_ref())?))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                let ty = Type::UnboxedRecord(
                    fields
                        .iter()
                        .map(|(name, field)| Ok((*name, source_type(field.ty())?)))
                        .collect::<Result<Vec<_>, String>>()?,
                );
                (CoreType::Source(ty), TypedValueKind::UnboxedRecord(fields))
            }
        };
        let value = TypedValue::new(ty.clone(), kind);
        if let Some(expected) = expected {
            let actual = self.solver.resolve_core(&ty);
            let wanted = self.solver.resolve_core(expected);
            if representation_preserving(&actual, &wanted) {
                return Ok(TypedValue::new(
                    expected.clone(),
                    TypedValueKind::Reinterpret(Box::new(value)),
                ));
            }
            self.solver.subsume_core(&ty, expected)?;
        }
        Ok(value)
    }

    #[allow(clippy::too_many_lines)]
    fn comp(&mut self, comp: Comp, expected: Option<&CompSig>) -> Result<TypedComp, String> {
        match comp {
            Comp::Return(value) => {
                let value = self.value(value, expected.map(CompSig::result))?;
                self.finish_comp(
                    CompSig::new(value.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(value),
                    expected,
                )
            }
            Comp::Bind(first, raw, rest) => {
                let first = *first;
                let rest = *rest;
                let (first, binder, rest) = if matches!(&first, Comp::Return(Value::Thunk(_))) {
                    // A suspended function is a checking form: its rank and
                    // latent row can be determined only by the continuation's
                    // use. Propagate that demand backwards across the bind.
                    let rest_retry = rest.clone();
                    let binder_ty = self.solver.fresh_core();
                    let speculative_binder = self.bind(raw, binder_ty.clone());
                    let rest_expected = expected.map(|expected| {
                        CompSig::new(expected.result().clone(), self.solver.fresh_row())
                    });
                    let pending_before = self.pending_handler_rows.len();
                    let speculative_rest = self
                        .comp(rest, rest_expected.as_ref())
                        .map_err(|error| format!("bind {raw} rest: {error}"))?;
                    let retry_exact = self.pending_handler_rows.len() > pending_before;
                    self.unbind(raw);
                    let first_expected = CompSig::new(binder_ty, self.solver.fresh_row());
                    let first = self
                        .comp(first, Some(&first_expected))
                        .map_err(|error| format!("bind {raw} first: {error}"))?;
                    // The backwards demand is deliberately flexible. Once the
                    // producer has checked, the bind witness records its exact
                    // result rather than the broader metavariable shape used to
                    // type the continuation (notably a closure returned after an
                    // effectful prefix can itself be pure).
                    if retry_exact {
                        let binder = TypedBinder::new(raw, first.sig().result().clone());
                        self.bind(raw, first.sig().result().clone());
                        let rest = self
                            .comp(rest_retry, rest_expected.as_ref())
                            .map_err(|error| format!("bind {raw} exact rest: {error}"))?;
                        self.unbind(raw);
                        (first, binder, rest)
                    } else {
                        (first, speculative_binder, speculative_rest)
                    }
                } else {
                    let first = self
                        .comp(first, None)
                        .map_err(|error| format!("bind {raw} first: {error}"))?;
                    let binder = self.bind(raw, first.sig().result().clone());
                    let rest_expected = expected.map(|expected| {
                        CompSig::new(expected.result().clone(), self.solver.fresh_row())
                    });
                    let rest = self
                        .comp(rest, rest_expected.as_ref())
                        .map_err(|error| format!("bind {raw} rest: {error}"))?;
                    self.unbind(raw);
                    (first, binder, rest)
                };
                let effects = self
                    .solver
                    .union_rows(first.sig().effects(), rest.sig().effects())?;
                self.finish_comp(
                    CompSig::new(rest.sig().result().clone(), effects),
                    TypedCompKind::Bind(Box::new(first), binder, Box::new(rest)),
                    expected,
                )
            }
            Comp::Force(value) => {
                let value = self.value(value, None)?;
                let forced = match self.solver.resolve_core(value.ty()) {
                    CoreType::Thunk(forced) => *forced,
                    CoreType::Source(Type::Exist(_)) => {
                        // Every force emitted by source elaboration exposes a
                        // suspended function. Constructing the closure is pure;
                        // the function body's latent row is inferred separately
                        // when the enclosing application is built.
                        let forced = CompSig::new(self.solver.fresh_core(), EffRow::Empty);
                        self.solver
                            .unify_core(value.ty(), &CoreType::Thunk(Box::new(forced.clone())))?;
                        forced
                    }
                    other => {
                        return Err(format!(
                            "typed builder: force operand is not a thunk: {other:?}"
                        ));
                    }
                };
                self.finish_comp(forced, TypedCompKind::Force(value), expected)
            }
            Comp::Lam(params, body) => {
                let expected_fn = expected.and_then(|expected| match expected.result() {
                    CoreType::Function(signature) => Some(signature.as_ref()),
                    _ => None,
                });
                let mut binders = Vec::new();
                for (index, raw) in params.iter().enumerate() {
                    let ty = expected_fn
                        .and_then(|signature| signature.params().get(index))
                        .cloned()
                        .unwrap_or_else(|| self.solver.fresh_core());
                    binders.push(self.bind(*raw, ty));
                }
                let body = self.comp(*body, None)?;
                if let Some(expected_fn) = expected_fn {
                    self.solver.subsume_sig(body.sig(), expected_fn.body())?;
                }
                for raw in params.into_iter().rev() {
                    self.unbind(raw);
                }
                let signature = CoreFnSig::new(
                    expected_fn
                        .map(CoreFnSig::quantifiers)
                        .unwrap_or_default()
                        .to_vec(),
                    binders.iter().map(|binder| binder.ty().clone()).collect(),
                    expected_fn
                        .map(CoreFnSig::body)
                        .cloned()
                        .unwrap_or_else(|| body.sig().clone()),
                );
                self.finish_comp(
                    CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
                    TypedCompKind::Lam(binders, Box::new(body)),
                    expected,
                )
            }
            Comp::App(callee, args) => {
                let callee = self.comp(*callee, None)?;
                let resolved_callee = self.solver.resolve_core(callee.sig().result());
                let declared = match resolved_callee {
                    CoreType::Function(declared) => declared,
                    CoreType::Source(Type::Exist(_)) => {
                        let inferred = CoreFnSig::new(
                            Vec::new(),
                            args.iter().map(|_| self.solver.fresh_core()).collect(),
                            CompSig::new(
                                expected
                                    .map(CompSig::result)
                                    .cloned()
                                    .unwrap_or_else(|| self.solver.fresh_core()),
                                self.solver.fresh_row(),
                            ),
                        );
                        self.solver.unify_core(
                            callee.sig().result(),
                            &CoreType::Function(Box::new(inferred.clone())),
                        )?;
                        Box::new(inferred)
                    }
                    other => {
                        return Err(format!(
                            "typed builder: application callee is not a function: {other:?}"
                        ));
                    }
                };
                let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                let signature = instantiate_fn(&declared, &instantiation)?;
                if args.len() != signature.params().len() {
                    return Err(format!(
                        "typed builder: computed application arity {} != {}",
                        args.len(),
                        signature.params().len()
                    ));
                }
                let args = args
                    .into_iter()
                    .zip(signature.params())
                    .enumerate()
                    .map(|(index, (arg, expected))| {
                        self.value(arg, Some(expected)).map_err(|error| {
                            format!(
                                "computed application argument {index} against {:?}: {error}",
                                self.solver.resolve_core(expected)
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let effects = self
                    .solver
                    .union_rows(callee.sig().effects(), signature.body().effects())?;
                self.finish_comp(
                    CompSig::new(signature.body().result().clone(), effects),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation,
                        args,
                    },
                    expected,
                )
            }
            Comp::If(condition, yes, no) => {
                let condition = self.value(condition, Some(&CoreType::Source(Type::Bool)))?;
                let branch_result = expected
                    .map(CompSig::result)
                    .cloned()
                    .unwrap_or_else(|| self.solver.fresh_core());
                let yes_expected = CompSig::new(branch_result.clone(), self.solver.fresh_row());
                let no_expected = CompSig::new(branch_result, self.solver.fresh_row());
                let yes = self.comp(*yes, Some(&yes_expected))?;
                let no = self.comp(*no, Some(&no_expected))?;
                self.solver
                    .unify_core(yes.sig().result(), no.sig().result())?;
                let effects = self
                    .solver
                    .union_rows(yes.sig().effects(), no.sig().effects())?;
                self.finish_comp(
                    CompSig::new(yes.sig().result().clone(), effects),
                    TypedCompKind::If(condition, Box::new(yes), Box::new(no)),
                    expected,
                )
            }
            Comp::Prim(op, lhs, rhs) => self.primitive(op, lhs, rhs, expected),
            Comp::Call(callee, args) => self.call(callee, args, expected),
            Comp::Io(op, args) => self.io(op, args, expected),
            Comp::Error(value) => {
                let value = self.value(value, None)?;
                let result = expected
                    .map(CompSig::result)
                    .cloned()
                    .unwrap_or_else(|| self.solver.fresh_core());
                let effects = expected
                    .map(CompSig::effects)
                    .cloned()
                    .unwrap_or(EffRow::Empty);
                self.finish_comp(
                    CompSig::new(result, effects),
                    TypedCompKind::Error(value),
                    expected,
                )
            }
            Comp::Case(scrutinee, arms) => self.case(scrutinee, arms, expected),
            Comp::FloatBuiltin(op, value) => {
                let signature = intrinsic_sig(op.signature())?;
                let value = self.value(value, signature.params().first())?;
                self.finish_comp(
                    signature.body().clone(),
                    TypedCompKind::FloatBuiltin(op, value),
                    expected,
                )
            }
            Comp::Neg(lane, value) => {
                let ty = match lane {
                    NegLane::Int => Type::Int,
                    NegLane::I64 => Type::I64,
                    NegLane::Float => Type::Float,
                };
                let value = self.value(value, Some(&CoreType::Source(ty.clone())))?;
                self.finish_comp(
                    CompSig::new(CoreType::Source(ty), EffRow::Empty),
                    TypedCompKind::Neg(lane, value),
                    expected,
                )
            }
            Comp::UnboxedProject(value, field) => {
                let value = self.value(value, None)?;
                let result = expected
                    .map(CompSig::result)
                    .cloned()
                    .unwrap_or_else(|| self.solver.fresh_core());
                self.finish_comp(
                    CompSig::new(result, EffRow::Empty),
                    TypedCompKind::UnboxedProject(value, field),
                    expected,
                )
            }
            Comp::Do(operation, args) => self.operation(operation, args, expected),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => self.handle(
                *body,
                return_var,
                return_body.map(|body| *body),
                &ops,
                expected,
            ),
            Comp::Mask(effects, body) => {
                let body = self.comp(*body, None)?;
                let residual = subtract_names(body.sig().effects(), &effects);
                self.finish_comp(
                    CompSig::new(body.sig().result().clone(), residual),
                    TypedCompKind::Mask(effects, Box::new(body)),
                    expected,
                )
            }
            Comp::StrBuiltin(op, args) => self.builtin(op, args, expected),
            Comp::Dup(_)
            | Comp::Drop(_)
            | Comp::WithReuse { .. }
            | Comp::Reuse(..)
            | Comp::RefNew(_)
            | Comp::RefGet(_)
            | Comp::RefSet(..)
            | Comp::InitAt(..) => Err("runtime node reached typed elaboration builder".into()),
        }
    }

    fn primitive(
        &mut self,
        op: CoreOp,
        lhs: Value,
        rhs: Value,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        use CoreOp::{
            Add, Addf, Div, Divf, Eq, Eqf, Ge, Gef, Gt, Gtf, Le, Lef, Lt, Ltf, Mul, Mulf, Ne, Nef,
            Rem, Sub, Subf,
        };
        let (operand, result) = match op {
            Add | Sub | Mul | Div | Rem => (CoreType::Source(Type::Int), Type::Int),
            Addf | Subf | Mulf | Divf => (CoreType::Source(Type::Float), Type::Float),
            Eqf | Nef | Ltf | Lef | Gtf | Gef => (CoreType::Source(Type::Float), Type::Bool),
            Eq | Ne | Lt | Le | Gt | Ge => {
                let operand = self.solver.fresh_core();
                (operand, Type::Bool)
            }
        };
        let lhs = self.value(lhs, Some(&operand))?;
        let rhs = self.value(rhs, Some(&operand))?;
        self.finish_comp(
            CompSig::new(CoreType::Source(result), EffRow::Empty),
            TypedCompKind::Prim(op, lhs, rhs),
            expected,
        )
    }

    fn call(
        &mut self,
        callee: Sym,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        let declared = self
            .globals
            .get(&callee)
            .ok_or_else(|| format!("typed builder: call to unknown function {callee}"))?
            .clone();
        let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
        let signature = instantiate_fn(&declared, &instantiation)?;
        if args.len() != signature.params().len() {
            return Err(format!(
                "typed builder: call {callee} arity {} != {}",
                args.len(),
                signature.params().len()
            ));
        }
        let args = args
            .into_iter()
            .zip(signature.params())
            .map(|(arg, expected)| self.value(arg, Some(expected)))
            .collect::<Result<Vec<_>, _>>()?;
        self.finish_comp(
            signature.body().clone(),
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            },
            expected,
        )
    }

    fn io(
        &mut self,
        op: IoOp,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        if args.len() != op.arity() {
            return Err(format!("typed builder: bad I/O arity for {op:?}"));
        }
        let args = args
            .into_iter()
            .map(|arg| {
                let ty = match op {
                    IoOp::PrintF => Some(CoreType::Source(Type::Float)),
                    IoOp::PrintS => Some(CoreType::Source(Type::Str)),
                    IoOp::Srand => Some(CoreType::Source(Type::Int)),
                    IoOp::Print | IoOp::PrintNl | IoOp::ReadInt | IoOp::ReadLine | IoOp::Rand => {
                        None
                    }
                };
                self.value(arg, ty.as_ref())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result = match op {
            IoOp::ReadInt | IoOp::Rand => Type::Int,
            IoOp::ReadLine => Type::Str,
            IoOp::Print | IoOp::PrintF | IoOp::PrintS | IoOp::PrintNl | IoOp::Srand => Type::Unit,
        };
        self.finish_comp(
            CompSig::new(CoreType::Source(result), EffRow::singleton(IO_EFFECT)),
            TypedCompKind::Io(op, args),
            expected,
        )
    }

    fn builtin(
        &mut self,
        op: Builtin,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        let unsigned_shared_lane =
            matches!(op, Builtin::I64Add | Builtin::I64Sub | Builtin::I64Mul)
                && (matches!(
                    expected.map(CompSig::result),
                    Some(CoreType::Source(Type::U64))
                ) || args.first().is_some_and(|arg| match arg {
                    Value::U64(_) => true,
                    Value::Var(name) => self.local(*name).is_some_and(|(_, ty)| {
                        self.solver.resolve_core(&ty) == CoreType::Source(Type::U64)
                    }),
                    _ => false,
                }));
        let declared = if unsigned_shared_lane {
            intrinsic_sig("(U64, U64) -> U64")?
        } else if let Some(signature) = op.signature() {
            intrinsic_sig(signature)?
        } else {
            self.verify_env
                .builtin_override(op)
                .ok_or_else(|| {
                    format!(
                        "typed builder: elaborator-only builtin {} has no signature",
                        op.name()
                    )
                })?
                .clone()
        };
        let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
        let signature = instantiate_fn(&declared, &instantiation)?;
        if args.len() != signature.params().len() {
            return Err(format!(
                "typed builder: builtin {} arity {} != {}",
                op.name(),
                args.len(),
                signature.params().len()
            ));
        }
        let args = args
            .into_iter()
            .zip(signature.params())
            .map(|(arg, expected)| self.value(arg, Some(expected)))
            .collect::<Result<Vec<_>, _>>()?;
        self.finish_comp(
            signature.body().clone(),
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            },
            expected,
        )
    }

    fn operation(
        &mut self,
        name: Sym,
        args: Vec<Value>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        let declared = self
            .verify_env
            .operation(name)
            .ok_or_else(|| format!("typed builder: unknown effect operation {name}"))?
            .clone();
        let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
        let operation = instantiate_operation(&declared, &instantiation)?;
        if args.len() != operation.params.len() {
            return Err(format!(
                "typed builder: operation {name} arity {} != {}",
                args.len(),
                operation.params.len()
            ));
        }
        let args = args
            .into_iter()
            .zip(&operation.params)
            .map(|(arg, expected)| self.value(arg, Some(expected)))
            .collect::<Result<Vec<_>, _>>()?;
        self.finish_comp(
            CompSig::new(
                operation.result,
                EffRow::canonical([operation.effect], EffRow::Empty),
            ),
            TypedCompKind::Do {
                operation: name,
                instantiation,
                args,
            },
            expected,
        )
    }

    fn case(
        &mut self,
        scrutinee: Value,
        arms: Vec<(CorePat, Comp)>,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        if arms.is_empty() {
            return Err("typed builder: case has no arms".into());
        }
        let scrutinee = self.value(scrutinee, None)?;
        let result = expected
            .map(CompSig::result)
            .cloned()
            .unwrap_or_else(|| self.solver.fresh_core());
        let mut effects = EffRow::Empty;
        let mut typed_arms = Vec::with_capacity(arms.len());
        for (pattern, body) in arms {
            let (pattern, raw_binders) = self.pattern(pattern, scrutinee.ty())?;
            let body_expected = CompSig::new(result.clone(), self.solver.fresh_row());
            let body = self.comp(body, Some(&body_expected))?;
            for raw in raw_binders.into_iter().rev() {
                self.unbind(raw);
            }
            effects = self.solver.union_rows(&effects, body.sig().effects())?;
            typed_arms.push((pattern, body));
        }
        self.finish_comp(
            CompSig::new(result, effects),
            TypedCompKind::Case(scrutinee, typed_arms),
            expected,
        )
    }

    fn pattern(
        &mut self,
        pattern: CorePat,
        scrutinee: &CoreType,
    ) -> Result<(TypedPattern, Vec<Sym>), String> {
        match pattern {
            CorePat::Wild => Ok((TypedPattern::Wild, Vec::new())),
            CorePat::Var(raw) => Ok((
                TypedPattern::Var(self.bind(raw, scrutinee.clone())),
                vec![raw],
            )),
            CorePat::Tuple(fields) => {
                let field_count = fields.len();
                let resolved = self.solver.resolve_core(scrutinee);
                let field_types = match resolved {
                    CoreType::Source(Type::Tuple(types) | Type::UnboxedTuple(types))
                        if types.len() == fields.len() =>
                    {
                        types
                    }
                    CoreType::Source(Type::UnboxedRecord(record_fields))
                        if record_fields.len() == field_count =>
                    {
                        record_fields.into_iter().map(|(_, ty)| ty).collect()
                    }
                    _ => {
                        let types: Vec<_> =
                            fields.iter().map(|_| self.solver.fresh_type()).collect();
                        self.solver
                            .unify_core(scrutinee, &CoreType::Source(Type::Tuple(types.clone())))?;
                        types
                    }
                };
                let mut raw_binders = Vec::new();
                let fields = fields
                    .into_iter()
                    .zip(field_types)
                    .map(|(raw, ty)| {
                        raw.map(|raw| {
                            raw_binders.push(raw);
                            self.bind(raw, lower_value_type(&ty))
                        })
                    })
                    .collect();
                Ok((TypedPattern::Tuple(fields), raw_binders))
            }
            CorePat::Ctor(name, fields) => {
                let declared = self
                    .verify_env
                    .constructor(name)
                    .ok_or_else(|| format!("typed builder: unknown pattern constructor {name}"))?
                    .clone();
                let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
                let constructor = instantiate_constructor(&declared, &instantiation)?;
                self.solver.unify_core(scrutinee, &constructor.result)?;
                if fields.len() != constructor.fields.len() {
                    return Err(format!(
                        "typed builder: pattern {name} arity {} != {}",
                        fields.len(),
                        constructor.fields.len()
                    ));
                }
                let mut raw_binders = Vec::new();
                let fields = fields
                    .into_iter()
                    .zip(constructor.fields)
                    .map(|(raw, ty)| {
                        raw.map(|raw| {
                            raw_binders.push(raw);
                            self.bind(raw, ty)
                        })
                    })
                    .collect();
                Ok((
                    TypedPattern::Ctor {
                        name,
                        instantiation,
                        fields,
                    },
                    raw_binders,
                ))
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn handle(
        &mut self,
        body: Comp,
        return_var: Option<Sym>,
        return_body: Option<Comp>,
        ops: &CheckedHandler,
        expected: Option<&CompSig>,
    ) -> Result<TypedComp, String> {
        if return_var.is_some() != return_body.is_some() {
            return Err("typed builder: incomplete handler return clause".into());
        }
        let body = self.comp(body, None)?;
        let result = expected
            .map(CompSig::result)
            .cloned()
            .unwrap_or_else(|| self.solver.fresh_core());
        let outer_effects = expected
            .map(CompSig::effects)
            .cloned()
            .unwrap_or_else(|| self.solver.fresh_row());
        let outer = CompSig::new(result.clone(), outer_effects.clone());
        let mut clause_results = Vec::new();

        let (return_binder, return_body, mut clause_effects) =
            if let (Some(raw), Some(return_body)) = (return_var, return_body) {
                let binder = self.bind(raw, body.sig().result().clone());
                let return_body = self.comp(return_body, None)?;
                self.unbind(raw);
                clause_results.push(return_body.sig().result().clone());
                let effects = return_body.sig().effects().clone();
                (Some(binder), Some(Box::new(return_body)), effects)
            } else {
                clause_results.push(body.sig().result().clone());
                (None, None, EffRow::Empty)
            };

        let mut handled = BTreeMap::new();
        let mut typed_ops = Vec::new();
        for arm in ops.arms().iter().cloned() {
            let declared = self
                .verify_env
                .operation(arm.name)
                .ok_or_else(|| format!("typed builder: unknown handled operation {}", arm.name))?
                .clone();
            let instantiation = self.solver.fresh_instantiation(declared.quantifiers());
            let operation = instantiate_operation(&declared, &instantiation)?;
            if arm.params.len() != operation.params.len() {
                return Err(format!(
                    "typed builder: handler operation {} arity {} != {}",
                    arm.name,
                    arm.params.len(),
                    operation.params.len()
                ));
            }
            let mut params = Vec::new();
            for (raw, ty) in arm.params.iter().copied().zip(&operation.params) {
                params.push(self.bind(raw, ty.clone()));
            }
            let resume_ty = CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    vec![operation.result.clone()],
                    outer.clone(),
                ))),
                EffRow::Empty,
            )));
            let resume = self.bind(arm.resume, resume_ty);
            let arm_body = self
                .comp(arm.body, None)
                .map_err(|error| format!("handler operation {} body: {error}", arm.name))?;
            self.unbind(arm.resume);
            for raw in arm.params.into_iter().rev() {
                self.unbind(raw);
            }
            clause_effects = self
                .solver
                .union_rows(&clause_effects, arm_body.sig().effects())?;
            clause_results.push(arm_body.sig().result().clone());
            handled.insert(arm.name, operation.effect);
            typed_ops.push(TypedHandleOp::new(
                arm.name,
                instantiation,
                params,
                resume,
                arm_body,
            ));
        }

        let mut joined_result = clause_results
            .first()
            .cloned()
            .ok_or_else(|| "typed builder: handler has no result clause".to_string())?;
        for clause_result in clause_results.iter().skip(1) {
            joined_result = self.solver.join_core(&joined_result, clause_result)?;
        }
        self.solver.constrain_join(&result, &joined_result)?;

        let handled: BTreeMap<_, _> = handled
            .into_iter()
            .map(|(name, label)| {
                (
                    name,
                    Label {
                        name: label.name,
                        args: label
                            .args
                            .iter()
                            .map(|ty| self.solver.resolve_type(ty))
                            .collect(),
                    },
                )
            })
            .collect();
        let forwarded = self.lower_residual_forwarding(&handled);
        let body_effects = self.solver.resolve_row(body.sig().effects());
        if body_effects.labels().is_empty()
            && matches!(body_effects.tail(), EffRow::Exist(_))
            && !handled.is_empty()
        {
            // Continuation-directed checking can build a handler before a local
            // thunk's latent row is known. Keep the subtraction equation until
            // that thunk is checked; linking the handler output directly to the
            // unresolved body row would retain an effect that a now-known
            // exhaustive clause should discharge.
            self.pending_handler_rows.push(PendingHandlerRow {
                target: outer_effects.clone(),
                body: body.sig().effects().clone(),
                handled: handled.clone(),
                clauses: clause_effects.clone(),
            });
        } else {
            let effects = self.derive_handler_effects(
                &body_effects,
                &handled,
                &clause_effects,
                &outer_effects,
            )?;
            self.solver.constrain_row_join(&outer_effects, &effects)?;
        }
        let ops = TypedHandler::new(typed_ops)
            .map_err(|name| format!("typed builder: duplicate handler operation {name}"))?
            .with_forwarded(forwarded);
        let derived_effects = outer.effects().show();
        let expected_effects = expected.map(|signature| signature.effects().show());
        self.finish_comp(
            outer,
            TypedCompKind::Handle {
                body: Box::new(body),
                return_binder,
                return_body,
                ops,
            },
            expected,
        )
        .map_err(|error| {
            format!(
                "handler effects derived {derived_effects}, expected {expected_effects:?}: {error}"
            )
        })
    }

    fn derive_handler_effects(
        &mut self,
        body_effects: &EffRow,
        handled: &BTreeMap<Sym, Label>,
        clause_effects: &EffRow,
        outer_effects: &EffRow,
    ) -> Result<EffRow, String> {
        let discharged = self.exhaustively_handled_labels(body_effects, handled);
        // Matching a parametric arm can solve type arguments that were still
        // existential in the body's label. Re-zonk before exact set
        // subtraction so the discharged witness and body label agree.
        let body_effects = self.solver.resolve_row(body_effects);
        let residual = subtract_labels(&body_effects, &discharged);
        let resolved_outer = self.solver.resolve_row(outer_effects);
        let resolved_clauses = self.solver.resolve_row(clause_effects);
        if matches!(resolved_outer, EffRow::Exist(_)) && resolved_clauses.tail() == &resolved_outer
        {
            // Resumption clauses carry the handler's own row recursively. The
            // least fixed point of `outer = residual | clauses | outer` is the
            // union of the non-recursive labels over the residual's tail.
            Ok(EffRow::canonical(
                residual
                    .labels()
                    .into_iter()
                    .chain(resolved_clauses.labels())
                    .cloned(),
                residual.tail().clone(),
            ))
        } else {
            self.solver.union_rows(&residual, &resolved_clauses)
        }
    }

    // The first born-typed lowering: make the implicit fall-through edges of a
    // partial handler explicit as checked witness data. Erasure drops the
    // witnesses because both executable handler tiers already implement the
    // same forward-and-reperform edge from an absent clause.
    fn lower_residual_forwarding(&self, arms: &BTreeMap<Sym, Label>) -> Vec<TypedForward> {
        let effects: BTreeMap<Sym, Label> = arms
            .values()
            .map(|label| (label.name, label.clone()))
            .collect();
        self.verify_env
            .operations()
            .iter()
            .filter_map(|(operation, declared)| {
                effects
                    .get(&declared.effect().name)
                    .filter(|_| !arms.contains_key(operation))
                    .cloned()
                    .map(|effect| TypedForward::new(*operation, effect))
            })
            .collect()
    }

    fn exhaustively_handled_labels(
        &mut self,
        body: &EffRow,
        arms: &BTreeMap<Sym, Label>,
    ) -> BTreeSet<Label> {
        let mut discharged = BTreeSet::new();
        for label in body.labels() {
            let declared: Vec<_> = self
                .verify_env
                .operations()
                .iter()
                .filter(|(_, operation)| operation.effect().name == label.name)
                .map(|(name, _)| *name)
                .collect();
            if declared.is_empty() {
                continue;
            }
            let mut exhaustive = true;
            let mut trial = self.solver.clone();
            for name in declared {
                let Some(handled) = arms.get(&name) else {
                    exhaustive = false;
                    break;
                };
                if handled.name != label.name || handled.args.len() != label.args.len() {
                    exhaustive = false;
                    break;
                }
                for (handled, body) in handled.args.iter().zip(&label.args) {
                    if trial.unify_type(handled, body).is_err() {
                        exhaustive = false;
                        break;
                    }
                }
                if !exhaustive {
                    break;
                }
            }
            if exhaustive {
                self.solver = trial;
                discharged.insert(Label {
                    name: label.name,
                    args: label
                        .args
                        .iter()
                        .map(|ty| self.solver.resolve_type(ty))
                        .collect(),
                });
            }
        }
        discharged
    }
}

impl Solver {
    fn final_core(&self, ty: &CoreType) -> CoreType {
        if let CoreType::Source(Type::Exist(id)) = ty {
            if !self.core.contains_key(id)
                && !self.types.contains_key(id)
                && self.int_defaults.contains(id)
            {
                return CoreType::Source(Type::Int);
            }
        }
        match self.resolve_core(ty) {
            CoreType::Source(ty) => lower_value_type(&self.final_type(&ty)),
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.final_sig(&sig))),
            CoreType::Function(sig) => CoreType::Function(Box::new(self.final_fn_sig(&sig))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.final_core(&inner))),
            CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(self.final_core(&inner))),
            CoreType::Lowered(kind) => CoreType::Lowered(match kind {
                LoweredType::Word => LoweredType::Word,
                LoweredType::Eff(row) => LoweredType::Eff(self.final_row(&row)),
                LoweredType::Queue(row) => LoweredType::Queue(self.final_row(&row)),
                LoweredType::QueueView(row) => LoweredType::QueueView(self.final_row(&row)),
            }),
        }
    }

    fn final_sig(&self, sig: &CompSig) -> CompSig {
        CompSig::new(self.final_core(sig.result()), self.final_row(sig.effects()))
    }

    fn final_fn_sig(&self, sig: &CoreFnSig) -> CoreFnSig {
        let params: Vec<_> = sig.params().iter().map(|ty| self.final_core(ty)).collect();
        let body = self.final_sig(sig.body());
        CoreFnSig::new(sig.quantifiers().to_vec(), params, body)
    }

    fn final_type(&self, ty: &Type) -> Type {
        match self.resolve_type(ty) {
            Type::Exist(id) if self.core.contains_key(&id) => {
                // Keep an impossible source/Core crossing visible to the
                // independent checker; it will become a coded E9997 violation
                // instead of being silently rewritten to Unit.
                source_type(&self.final_core(&self.core[&id])).map_or(Type::Exist(id), |ty| ty)
            }
            Type::Exist(id) if self.int_defaults.contains(&id) => Type::Int,
            Type::Exist(_) => Type::Unit,
            Type::Forall(name, body) => Type::Forall(name, Box::new(self.final_type(&body))),
            Type::RowForall(name, body) => Type::RowForall(name, Box::new(self.final_type(&body))),
            Type::Fun(params, effects, result) => Type::Fun(
                params.iter().map(|ty| self.final_type(ty)).collect(),
                self.final_row(&effects),
                Box::new(self.final_type(&result)),
            ),
            Type::Con(name, args) => {
                Type::Con(name, args.iter().map(|ty| self.final_type(ty)).collect())
            }
            Type::App(head, arg) => Type::app(self.final_type(&head), self.final_type(&arg)),
            Type::Tuple(fields) => {
                Type::Tuple(fields.iter().map(|ty| self.final_type(ty)).collect())
            }
            Type::UnboxedTuple(fields) => {
                Type::UnboxedTuple(fields.iter().map(|ty| self.final_type(ty)).collect())
            }
            Type::UnboxedRecord(fields) => Type::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.final_type(ty)))
                    .collect(),
            ),
            Type::OrNull(inner) => Type::OrNull(Box::new(self.final_type(&inner))),
            Type::Row(row) => Type::Row(self.final_row(&row)),
            Type::Coeffect(inner, row) => Type::Coeffect(Box::new(self.final_type(&inner)), row),
            other => other,
        }
    }

    fn final_row(&self, row: &EffRow) -> EffRow {
        let row = self.resolve_row(row);
        let tail = match row.tail() {
            EffRow::Exist(_) => EffRow::Empty,
            other => other.clone(),
        };
        EffRow::canonical(
            row.labels().into_iter().map(|label| Label {
                name: label.name,
                args: label.args.iter().map(|ty| self.final_type(ty)).collect(),
            }),
            tail,
        )
    }

    fn final_instantiation(&self, instantiation: Vec<CoreInstantiation>) -> Vec<CoreInstantiation> {
        self.zonk_instantiation(instantiation)
            .into_iter()
            .map(|argument| match argument {
                CoreInstantiation::Type(ty) => CoreInstantiation::Type(self.final_type(&ty)),
                CoreInstantiation::Row(row) => CoreInstantiation::Row(self.final_row(&row)),
            })
            .collect()
    }

    fn zonk_binder(&self, binder: &TypedBinder) -> TypedBinder {
        TypedBinder::new(binder.name, self.final_core(&binder.ty))
    }

    fn zonk_pattern(&self, pattern: TypedPattern) -> TypedPattern {
        match pattern {
            TypedPattern::Wild => TypedPattern::Wild,
            TypedPattern::Var(binder) => TypedPattern::Var(self.zonk_binder(&binder)),
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => TypedPattern::Ctor {
                name,
                instantiation: self.final_instantiation(instantiation),
                fields: fields
                    .into_iter()
                    .map(|binder| binder.map(|binder| self.zonk_binder(&binder)))
                    .collect(),
            },
            TypedPattern::Tuple(fields) => TypedPattern::Tuple(
                fields
                    .into_iter()
                    .map(|binder| binder.map(|binder| self.zonk_binder(&binder)))
                    .collect(),
            ),
        }
    }

    fn zonk_value(&self, value: TypedValue) -> TypedValue {
        let kind = match value.kind {
            TypedValueKind::Var {
                name,
                instantiation,
            } => TypedValueKind::Var {
                name,
                instantiation: self.final_instantiation(instantiation),
            },
            TypedValueKind::Int(value) => TypedValueKind::Int(value),
            TypedValueKind::I64(value) => TypedValueKind::I64(value),
            TypedValueKind::U64(value) => TypedValueKind::U64(value),
            TypedValueKind::Float(value) => TypedValueKind::Float(value),
            TypedValueKind::Bool(value) => TypedValueKind::Bool(value),
            TypedValueKind::Unit => TypedValueKind::Unit,
            TypedValueKind::Str(value) => TypedValueKind::Str(value),
            TypedValueKind::Reinterpret(value) => {
                TypedValueKind::Reinterpret(Box::new(self.zonk_value(*value)))
            }
            TypedValueKind::LoweredRepr { .. } => {
                unreachable!("lowered representation node reached typed elaboration zonker")
            }
            TypedValueKind::NewtypeRepr { .. } => {
                unreachable!("newtype representation node reached typed elaboration zonker")
            }
            TypedValueKind::Thunk(body) => TypedValueKind::Thunk(Box::new(self.zonk_comp(*body))),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValueKind::Ctor {
                name,
                tag,
                instantiation: self.final_instantiation(instantiation),
                fields: fields
                    .into_iter()
                    .map(|field| self.zonk_value(field))
                    .collect(),
            },
            TypedValueKind::Tuple(fields) => TypedValueKind::Tuple(
                fields
                    .into_iter()
                    .map(|field| self.zonk_value(field))
                    .collect(),
            ),
            TypedValueKind::UnboxedTuple(fields) => TypedValueKind::UnboxedTuple(
                fields
                    .into_iter()
                    .map(|field| self.zonk_value(field))
                    .collect(),
            ),
            TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
                fields
                    .into_iter()
                    .map(|(name, field)| (name, self.zonk_value(field)))
                    .collect(),
            ),
        };
        TypedValue::new(self.final_core(&value.ty), kind)
    }

    #[allow(clippy::too_many_lines)]
    fn zonk_comp(&self, comp: TypedComp) -> TypedComp {
        let kind = match comp.kind {
            TypedCompKind::Return(value) => TypedCompKind::Return(self.zonk_value(value)),
            TypedCompKind::Bind(first, binder, rest) => TypedCompKind::Bind(
                Box::new(self.zonk_comp(*first)),
                self.zonk_binder(&binder),
                Box::new(self.zonk_comp(*rest)),
            ),
            TypedCompKind::Force(value) => TypedCompKind::Force(self.zonk_value(value)),
            TypedCompKind::Lam(params, body) => TypedCompKind::Lam(
                params
                    .into_iter()
                    .map(|binder| self.zonk_binder(&binder))
                    .collect(),
                Box::new(self.zonk_comp(*body)),
            ),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => TypedCompKind::App {
                callee: Box::new(self.zonk_comp(*callee)),
                instantiation: self.final_instantiation(instantiation),
                args: args.into_iter().map(|arg| self.zonk_value(arg)).collect(),
            },
            TypedCompKind::If(condition, yes, no) => TypedCompKind::If(
                self.zonk_value(condition),
                Box::new(self.zonk_comp(*yes)),
                Box::new(self.zonk_comp(*no)),
            ),
            TypedCompKind::Prim(op, lhs, rhs) => {
                TypedCompKind::Prim(op, self.zonk_value(lhs), self.zonk_value(rhs))
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => TypedCompKind::Call {
                callee,
                instantiation: self.final_instantiation(instantiation),
                args: args.into_iter().map(|arg| self.zonk_value(arg)).collect(),
            },
            TypedCompKind::Io(op, args) => TypedCompKind::Io(
                op,
                args.into_iter().map(|arg| self.zonk_value(arg)).collect(),
            ),
            TypedCompKind::Error(value) => TypedCompKind::Error(self.zonk_value(value)),
            TypedCompKind::Case(scrutinee, arms) => TypedCompKind::Case(
                self.zonk_value(scrutinee),
                arms.into_iter()
                    .map(|(pattern, body)| (self.zonk_pattern(pattern), self.zonk_comp(body)))
                    .collect(),
            ),
            TypedCompKind::FloatBuiltin(op, value) => {
                TypedCompKind::FloatBuiltin(op, self.zonk_value(value))
            }
            TypedCompKind::Neg(lane, value) => TypedCompKind::Neg(lane, self.zonk_value(value)),
            TypedCompKind::UnboxedProject(value, field) => {
                TypedCompKind::UnboxedProject(self.zonk_value(value), field)
            }
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => TypedCompKind::Do {
                operation,
                instantiation: self.final_instantiation(instantiation),
                args: args.into_iter().map(|arg| self.zonk_value(arg)).collect(),
            },
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => TypedCompKind::Handle {
                body: Box::new(self.zonk_comp(*body)),
                return_binder: return_binder.map(|binder| self.zonk_binder(&binder)),
                return_body: return_body.map(|body| Box::new(self.zonk_comp(*body))),
                ops: TypedHandler {
                    arms: ops
                        .arms
                        .into_iter()
                        .map(|arm| TypedHandleOp {
                            name: arm.name,
                            instantiation: self.final_instantiation(arm.instantiation),
                            params: arm
                                .params
                                .into_iter()
                                .map(|binder| self.zonk_binder(&binder))
                                .collect(),
                            resume: self.zonk_binder(&arm.resume),
                            body: self.zonk_comp(arm.body),
                        })
                        .collect(),
                    forwarded: ops
                        .forwarded
                        .into_iter()
                        .map(|forward| TypedForward {
                            operation: forward.operation,
                            effect: Label {
                                name: forward.effect.name,
                                args: forward
                                    .effect
                                    .args
                                    .iter()
                                    .map(|ty| self.resolve_type(ty))
                                    .collect(),
                            },
                        })
                        .collect(),
                },
            },
            TypedCompKind::Mask(effects, body) => {
                TypedCompKind::Mask(effects, Box::new(self.zonk_comp(*body)))
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedCompKind::StrBuiltin {
                op,
                instantiation: self.final_instantiation(instantiation),
                args: args.into_iter().map(|arg| self.zonk_value(arg)).collect(),
            },
            TypedCompKind::Dup(_)
            | TypedCompKind::Drop(_)
            | TypedCompKind::WithReuse { .. }
            | TypedCompKind::Reuse(..)
            | TypedCompKind::InitAt(..)
            | TypedCompKind::RefNew(_)
            | TypedCompKind::RefGet(_)
            | TypedCompKind::RefSet(..) => {
                unreachable!("runtime node reached typed elaboration zonker")
            }
        };
        TypedComp::new(self.final_sig(&comp.sig), kind)
    }
}

fn unanchored_result_quantifier(signature: &CoreFnSig) -> Option<Sym> {
    let CoreType::Source(Type::Var(result)) = signature.body().result() else {
        return None;
    };
    if !signature
        .quantifiers()
        .contains(&CoreQuantifier::Type(*result))
    {
        return None;
    }
    let mut types = BTreeSet::new();
    let mut rows = BTreeSet::new();
    for param in signature.params() {
        free_core_vars(param, &mut types, &mut rows);
    }
    free_row_vars(signature.body().effects(), &mut types, &mut rows);
    (!types.contains(result)).then_some(*result)
}

fn has_unreported_param_row(signature: &CoreFnSig) -> bool {
    let quantified: BTreeSet<_> = signature
        .quantifiers()
        .iter()
        .filter_map(|quantifier| match quantifier {
            CoreQuantifier::Row(name) => Some(*name),
            CoreQuantifier::Type(_) => None,
        })
        .collect();
    let mut parameter_rows = BTreeSet::new();
    for parameter in signature.params() {
        core_row_vars(parameter, &mut parameter_rows);
    }
    let mut reported = BTreeSet::new();
    row_vars(signature.body().effects(), &mut reported);
    parameter_rows
        .intersection(&quantified)
        .any(|name| !reported.contains(name))
}

/// Reconstruct checked witnesses for the legacy elaborator's compatibility
/// tree. The returned program is ready for the independent proof checker; the
/// only public escape from this module is semantic erasure.
pub(in crate::core) fn build_typed(
    core: Core,
    signatures: &BTreeMap<Sym, CoreFnSig>,
    verify_env: &VerifyEnv,
) -> Result<TypedCore<Elaborated>, Error> {
    const MIN_REMAINING_STACK: usize = 4 * 1024 * 1024;
    const BUILDER_STACK: usize = 8 * 1024 * 1024;
    stacker::maybe_grow(MIN_REMAINING_STACK, BUILDER_STACK, || {
        build_typed_on_grown_stack(core, signatures, verify_env)
    })
}

fn build_typed_on_grown_stack(
    core: Core,
    signatures: &BTreeMap<Sym, CoreFnSig>,
    verify_env: &VerifyEnv,
) -> Result<TypedCore<Elaborated>, Error> {
    let mut signatures = signatures.clone();
    // An inferred scheme `forall a. (...) -> a` whose result variable is
    // completely unanchored by parameters/effects can arise when a handler
    // installs the computation returned by the rest of a block. Probe those
    // rare signatures against a fresh result witness, then specialize the
    // typed environment to the Core body that was actually elaborated. This is
    // a structural refinement pass over every function, not an entry-point or
    // source-name exception.
    for function in &core.fns {
        let Some(signature) = signatures.get(&function.name).cloned() else {
            continue;
        };
        let Some(result_var) = unanchored_result_quantifier(&signature) else {
            continue;
        };
        let inferred = {
            let mut builder = Builder::new(&signatures, verify_env);
            for (raw, ty) in function.params.iter().copied().zip(signature.params()) {
                builder.bind(raw, ty.clone());
            }
            let expected = CompSig::new(
                builder.solver.fresh_core(),
                signature.body().effects().clone(),
            );
            let body = builder
                .comp(function.body.clone(), Some(&expected))
                .map_err(|detail| TypedCoreConstructionFailure::InvalidWitness {
                    function: function.name.to_string(),
                    path: "result refinement".into(),
                    detail,
                })?;
            builder.solve_pending_handler_rows(true).map_err(|detail| {
                TypedCoreConstructionFailure::InvalidWitness {
                    function: function.name.to_string(),
                    path: "result refinement residual handlers".into(),
                    detail,
                }
            })?;
            builder.solver.resolve_core(body.sig().result())
        };
        if inferred != CoreType::Source(Type::Var(result_var))
            && !matches!(inferred, CoreType::Source(Type::Exist(_)))
        {
            signatures.insert(
                function.name,
                CoreFnSig::new(
                    signature
                        .quantifiers()
                        .iter()
                        .filter(|quantifier| **quantifier != CoreQuantifier::Type(result_var))
                        .cloned()
                        .collect(),
                    signature.params().to_vec(),
                    CompSig::new(inferred, signature.body().effects().clone()),
                ),
            );
        }
    }
    // The legacy checker can also leave a quantified latent row visible in a
    // parameter while omitting the same row from a function body that invokes
    // that parameter. Probe only signatures with that structural asymmetry and
    // widen their typed computation witness to the effects the Core body
    // actually performs.
    loop {
        let mut changed = false;
        for function in &core.fns {
            let Some(signature) = signatures.get(&function.name).cloned() else {
                continue;
            };
            if !has_unreported_param_row(&signature) {
                continue;
            }
            let inferred = {
                let mut builder = Builder::new(&signatures, verify_env);
                for (raw, ty) in function.params.iter().copied().zip(signature.params()) {
                    builder.bind(raw, ty.clone());
                }
                let expected = CompSig::new(
                    signature.body().result().clone(),
                    builder.solver.fresh_row(),
                );
                let body = builder
                    .comp(function.body.clone(), Some(&expected))
                    .map_err(|detail| TypedCoreConstructionFailure::InvalidWitness {
                        function: function.name.to_string(),
                        path: "effect refinement".into(),
                        detail,
                    })?;
                builder.solve_pending_handler_rows(true).map_err(|detail| {
                    TypedCoreConstructionFailure::InvalidWitness {
                        function: function.name.to_string(),
                        path: "effect refinement residual handlers".into(),
                        detail,
                    }
                })?;
                builder.solver.final_row(body.sig().effects())
            };
            if inferred != *signature.body().effects() {
                signatures.insert(
                    function.name,
                    CoreFnSig::new(
                        signature.quantifiers().to_vec(),
                        signature.params().to_vec(),
                        CompSig::new(signature.body().result().clone(), inferred),
                    ),
                );
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut functions = Vec::with_capacity(core.fns.len());
    for function in core.fns {
        let signature = signatures
            .get(&function.name)
            .ok_or_else(|| TypedCoreConstructionFailure::MissingGlobalSignature {
                function: function.name.to_string(),
            })?
            .clone();
        if function.params.len() != signature.params().len() {
            return Err(TypedCoreConstructionFailure::ParameterArity {
                function: function.name.to_string(),
                actual: function.params.len(),
                expected: signature.params().len(),
            }
            .into());
        }
        let mut builder = Builder::new(&signatures, verify_env);
        let mut params = Vec::with_capacity(function.params.len());
        for (raw, ty) in function.params.iter().copied().zip(signature.params()) {
            params.push(builder.bind(raw, ty.clone()));
        }
        let body = builder
            .comp(function.body, Some(signature.body()))
            .map_err(|detail| TypedCoreConstructionFailure::InvalidWitness {
                function: function.name.to_string(),
                path: "body".into(),
                detail,
            })?;
        builder.solve_pending_handler_rows(true).map_err(|detail| {
            TypedCoreConstructionFailure::InvalidWitness {
                function: function.name.to_string(),
                path: "body residual handlers".into(),
                detail,
            }
        })?;
        for raw in function.params.into_iter().rev() {
            builder.unbind(raw);
        }
        let params = params
            .into_iter()
            .map(|binder| builder.solver.zonk_binder(&binder))
            .collect();
        let body = builder.solver.zonk_comp(body);
        let signature = builder.solver.final_fn_sig(&signature);
        functions.push(TypedCoreFn::new(
            function.name,
            params,
            body,
            signature,
            function.dict_arity,
        ));
    }
    Ok(TypedCore::new(functions))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unary_thunk(effects: EffRow) -> CoreType {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![CoreType::Source(Type::Int)],
                CompSig::new(CoreType::Source(Type::Int), effects),
            ))),
            EffRow::Empty,
        )))
    }

    #[test]
    fn source_aliases_recover_richer_core_evidence() {
        let mut solver = Solver::default();
        solver.core.insert(1, unary_thunk(EffRow::Empty));
        solver.unify_type(&Type::Exist(0), &Type::Exist(1)).unwrap();

        assert_eq!(
            solver.final_type(&Type::Exist(0)),
            Type::fun(vec![Type::Int], Type::Int)
        );
    }

    #[test]
    fn pure_rows_do_not_close_flexible_lower_bounds() {
        let mut solver = Solver::default();
        let open = EffRow::Exist(0);
        solver.constrain_row_join(&open, &EffRow::Empty).unwrap();
        assert_eq!(solver.resolve_row(&open), open);

        let io = EffRow::singleton(IO_EFFECT);
        solver.constrain_row_join(&open, &io).unwrap();
        assert_eq!(solver.resolve_row(&open), io);
    }

    #[test]
    fn pure_union_retains_flexible_row_authority() {
        let mut solver = Solver::default();
        let open = EffRow::Exist(0);
        let local = EffRow::singleton("Local");
        solver.constrain_row_join(&open, &local).unwrap();

        let joined = solver.union_rows(&EffRow::Empty, &open).unwrap();
        assert_eq!(joined, open);

        let ambient = EffRow::Var(Sym::from("e0"));
        solver.constrain_row_join(&open, &ambient).unwrap();
        assert_eq!(
            solver.final_row(&joined),
            EffRow::canonical(local.labels().into_iter().cloned(), ambient)
        );
    }

    #[test]
    fn row_alias_constraints_reach_the_canonical_root() {
        let mut solver = Solver::default();
        solver
            .unify_row(&EffRow::Exist(1), &EffRow::Exist(0))
            .unwrap();
        let io = EffRow::singleton(IO_EFFECT);
        solver.constrain_row_join(&EffRow::Exist(1), &io).unwrap();
        assert_eq!(solver.resolve_row(&EffRow::Exist(0)), io);
    }

    #[test]
    fn representation_coercion_keeps_closure_shape_fixed() {
        let actual = unary_thunk(EffRow::Var(Sym::from("e")));
        let expected = unary_thunk(EffRow::Empty);
        assert!(representation_preserving(&actual, &expected));

        let different_result = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![CoreType::Source(Type::Int)],
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            ))),
            EffRow::Empty,
        )));
        assert!(!representation_preserving(&actual, &different_result));
    }
}
