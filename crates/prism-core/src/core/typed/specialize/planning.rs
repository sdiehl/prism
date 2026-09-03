//! Dictionary clone planning, quantifier alignment, and unification.

use super::unify::{eff_row_vars, Unifier};
use super::{
    each_subcomp, each_value, names, substitute_core_type, BTreeMap, BTreeSet, Builder,
    BuilderBinding, CompSig, CoreInstantiation, CoreQuantifier, CoreType, EffRow, LoweredType, Sym,
    Type, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedCoreSpecializationFailure,
    TypedPattern, TypedValue, TypedValueKind,
};

#[derive(Clone, Debug)]
pub(super) struct SpecializationPlan {
    pub(super) quantifiers: Vec<CoreQuantifier>,
    pub(super) parameters: Vec<PlanParameter>,
    pub(super) source_substitution: Vec<CoreInstantiation>,
    pub(super) builder_substitutions: Vec<Vec<CoreInstantiation>>,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum PlanParameter {
    Source(usize),
    Builder {
        dictionary: usize,
        quantifier: usize,
    },
}

impl SpecializationPlan {
    pub(super) fn build(
        function: &TypedCoreFn,
        builders: &[Builder],
    ) -> Result<Self, TypedCoreSpecializationFailure> {
        let dictionary_arity = function.dict_arity;
        if dictionary_arity > function.sig.params().len() {
            return Err(TypedCoreSpecializationFailure::DictionaryArity {
                function: function.name.to_string(),
                dictionary_arity,
                parameter_arity: function.sig.params().len(),
            });
        }

        let mut alpha = AlphaQuantifiers::new(function.sig.quantifiers(), builders);
        let source_types: Vec<_> = function.sig.params()[..dictionary_arity]
            .iter()
            .map(|ty| substitute_core_type(ty, function.sig.quantifiers(), &alpha.source_arguments))
            .collect();
        let builder_types: Vec<_> = builders
            .iter()
            .enumerate()
            .map(|(index, builder)| {
                substitute_core_type(
                    builder.function.sig.body().result(),
                    builder.function.sig.quantifiers(),
                    &alpha.builder_arguments[index],
                )
            })
            .collect();

        for (index, (source, builder)) in source_types.iter().zip(&builder_types).enumerate() {
            if !alpha.unifier.unify_core(source, builder) {
                return Err(TypedCoreSpecializationFailure::IncompatibleDictionary {
                    function: function.name.to_string(),
                    dictionary_index: index,
                    builder: builders[index].function.name.to_string(),
                });
            }
        }
        Ok(alpha.finish())
    }

    pub(super) fn call_instantiation(
        &self,
        function: Sym,
        source: &[CoreInstantiation],
        bindings: &[BuilderBinding],
        builders: &BTreeMap<Sym, Builder>,
    ) -> Result<Vec<CoreInstantiation>, TypedCoreSpecializationFailure> {
        let source_expected = self.source_substitution.len();
        if source.len() != source_expected {
            return Err(TypedCoreSpecializationFailure::SourceInstantiationArity {
                function: function.to_string(),
                actual: source.len(),
                expected: source_expected,
            });
        }
        let mut arguments = Vec::with_capacity(self.parameters.len());
        for parameter in &self.parameters {
            match *parameter {
                PlanParameter::Source(index) => arguments.push(source[index].clone()),
                PlanParameter::Builder {
                    dictionary,
                    quantifier,
                } => {
                    let binding = &bindings[dictionary];
                    let expected = builders
                        .get(&binding.name)
                        .map_or(0, |builder| builder.function.sig.quantifiers().len());
                    if binding.instantiation.len() != expected {
                        return Err(TypedCoreSpecializationFailure::BuilderInstantiationArity {
                            builder: binding.name.to_string(),
                            actual: binding.instantiation.len(),
                            expected,
                        });
                    }
                    arguments.push(binding.instantiation[quantifier].clone());
                }
            }
        }
        Ok(arguments)
    }
}

struct AlphaQuantifiers {
    source_arguments: Vec<CoreInstantiation>,
    builder_arguments: Vec<Vec<CoreInstantiation>>,
    variables: Vec<AlphaVariable>,
    unifier: Unifier,
}

#[derive(Clone, Copy)]
pub(super) struct AlphaVariable {
    pub(super) internal: Sym,
    pub(super) original: Sym,
    pub(super) kind: QuantifierKind,
    pub(super) origin: PlanParameter,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum QuantifierKind {
    Type,
    Row,
}

impl AlphaQuantifiers {
    fn new(source: &[CoreQuantifier], builders: &[Builder]) -> Self {
        let mut occupied: BTreeSet<_> = source.iter().map(quantifier_name).collect();
        occupied.extend(
            builders
                .iter()
                .flat_map(|builder| builder.function.sig.quantifiers().iter())
                .map(quantifier_name),
        );
        let mut counter = 0;
        let mut variables = Vec::new();
        let mut unifier = Unifier::default();
        let source_arguments = source
            .iter()
            .enumerate()
            .map(|(index, quantifier)| {
                let variable = alpha_variable(
                    quantifier,
                    PlanParameter::Source(index),
                    &mut occupied,
                    &mut counter,
                );
                unifier.insert(variable);
                variables.push(variable);
                variable.argument()
            })
            .collect();
        let builder_arguments = builders
            .iter()
            .enumerate()
            .map(|(dictionary, builder)| {
                builder
                    .function
                    .sig
                    .quantifiers()
                    .iter()
                    .enumerate()
                    .map(|(quantifier, declared)| {
                        let variable = alpha_variable(
                            declared,
                            PlanParameter::Builder {
                                dictionary,
                                quantifier,
                            },
                            &mut occupied,
                            &mut counter,
                        );
                        unifier.insert(variable);
                        variables.push(variable);
                        variable.argument()
                    })
                    .collect()
            })
            .collect();
        Self {
            source_arguments,
            builder_arguments,
            variables,
            unifier,
        }
    }

    fn finish(mut self) -> SpecializationPlan {
        let mut roots = Vec::new();
        for variable in &self.variables {
            if self.unifier.is_root(*variable) {
                roots.push(*variable);
            }
        }
        roots.sort_by_key(|variable| match variable.origin {
            PlanParameter::Source(index) => (0, index, 0),
            PlanParameter::Builder {
                dictionary,
                quantifier,
            } => (1, dictionary, quantifier),
        });

        let mut used = BTreeSet::new();
        let mut fresh = 0;
        let mut quantifiers = Vec::with_capacity(roots.len());
        let mut parameters = Vec::with_capacity(roots.len());
        let mut root_quantifiers = Vec::with_capacity(roots.len());
        let mut root_arguments = Vec::with_capacity(roots.len());
        for root in roots {
            let name = if used.insert(root.original) {
                root.original
            } else {
                loop {
                    let candidate = Sym::from(&names::fresh_binder(
                        names::FRESH_SPECIALIZE_QUANTIFIER,
                        fresh,
                    ));
                    fresh += 1;
                    if used.insert(candidate) {
                        break candidate;
                    }
                }
            };
            let (quantifier, argument) = match root.kind {
                QuantifierKind::Type => (
                    CoreQuantifier::Type(name),
                    CoreInstantiation::Type(Type::Var(name)),
                ),
                QuantifierKind::Row => (
                    CoreQuantifier::Row(name),
                    CoreInstantiation::Row(EffRow::Var(name)),
                ),
            };
            root_quantifiers.push(match root.kind {
                QuantifierKind::Type => CoreQuantifier::Type(root.internal),
                QuantifierKind::Row => CoreQuantifier::Row(root.internal),
            });
            root_arguments.push(argument);
            quantifiers.push(quantifier);
            parameters.push(root.origin);
        }

        let source_substitution = self
            .source_arguments
            .iter()
            .map(|argument| {
                self.unifier
                    .finish_argument(argument, &root_quantifiers, &root_arguments)
            })
            .collect();
        let builder_substitutions = self
            .builder_arguments
            .iter()
            .map(|arguments| {
                arguments
                    .iter()
                    .map(|argument| {
                        self.unifier
                            .finish_argument(argument, &root_quantifiers, &root_arguments)
                    })
                    .collect()
            })
            .collect();
        SpecializationPlan {
            quantifiers,
            parameters,
            source_substitution,
            builder_substitutions,
        }
    }
}

fn alpha_variable(
    quantifier: &CoreQuantifier,
    origin: PlanParameter,
    occupied: &mut BTreeSet<Sym>,
    counter: &mut u32,
) -> AlphaVariable {
    let internal = loop {
        let candidate = Sym::from(&names::fresh_binder(
            names::FRESH_SPECIALIZE_QUANTIFIER,
            *counter,
        ));
        *counter += 1;
        if occupied.insert(candidate) {
            break candidate;
        }
    };
    match quantifier {
        CoreQuantifier::Type(original) => AlphaVariable {
            internal,
            original: *original,
            kind: QuantifierKind::Type,
            origin,
        },
        CoreQuantifier::Row(original) => AlphaVariable {
            internal,
            original: *original,
            kind: QuantifierKind::Row,
            origin,
        },
    }
}

impl AlphaVariable {
    const fn argument(self) -> CoreInstantiation {
        match self.kind {
            QuantifierKind::Type => CoreInstantiation::Type(Type::Var(self.internal)),
            QuantifierKind::Row => CoreInstantiation::Row(EffRow::Var(self.internal)),
        }
    }
}

const fn quantifier_name(quantifier: &CoreQuantifier) -> Sym {
    match quantifier {
        CoreQuantifier::Type(name) | CoreQuantifier::Row(name) => *name,
    }
}

/// Collect every effect-row variable a Core type mentions, tail variables and
/// label arguments included. Over-approximation is harmless here: an extra
/// name only disables an instantiation tightening, never enables one.
pub(super) fn core_type_row_vars(ty: &CoreType, acc: &mut BTreeSet<Sym>) {
    match ty {
        CoreType::Source(source) => source.free_row_vars(acc),
        CoreType::Thunk(sig) => comp_sig_row_vars(sig, acc),
        CoreType::Function(sig) => {
            for param in sig.params() {
                core_type_row_vars(param, acc);
            }
            comp_sig_row_vars(sig.body(), acc);
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => core_type_row_vars(inner, acc),
        CoreType::Lowered(lowered) => match lowered {
            LoweredType::Word => {}
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row) => {
                eff_row_vars(row, acc);
            }
        },
    }
}

fn comp_sig_row_vars(sig: &CompSig, acc: &mut BTreeSet<Sym>) {
    core_type_row_vars(sig.result(), acc);
    eff_row_vars(sig.effects(), acc);
}

/// Collect every rigid type and effect-row variable a Core type mentions.
/// Over-approximation is harmless at the one consumer: an extra name only
/// declines a lambda lift, never enables one, so variables bound by a nested
/// signature's own quantifiers are not subtracted.
fn core_type_rigid_vars(ty: &CoreType, acc: &mut BTreeSet<Sym>) {
    match ty {
        CoreType::Source(source) => {
            source.free_ty_vars(acc);
            source.free_row_vars(acc);
        }
        CoreType::Thunk(sig) => comp_sig_rigid_vars(sig, acc),
        CoreType::Function(sig) => {
            for param in sig.params() {
                core_type_rigid_vars(param, acc);
            }
            comp_sig_rigid_vars(sig.body(), acc);
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => core_type_rigid_vars(inner, acc),
        CoreType::Lowered(lowered) => match lowered {
            LoweredType::Word => {}
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row) => {
                eff_row_rigid_vars(row, acc);
            }
        },
    }
}

fn comp_sig_rigid_vars(sig: &CompSig, acc: &mut BTreeSet<Sym>) {
    core_type_rigid_vars(sig.result(), acc);
    eff_row_rigid_vars(sig.effects(), acc);
}

fn eff_row_rigid_vars(row: &EffRow, acc: &mut BTreeSet<Sym>) {
    if let EffRow::Var(tail) = row.tail() {
        acc.insert(*tail);
    }
    for label in row.labels() {
        for argument in &label.args {
            argument.free_ty_vars(acc);
            argument.free_row_vars(acc);
        }
    }
}

fn instantiation_rigid_vars(arguments: &[CoreInstantiation], acc: &mut BTreeSet<Sym>) {
    for argument in arguments {
        match argument {
            CoreInstantiation::Type(ty) => {
                ty.free_ty_vars(acc);
                ty.free_row_vars(acc);
            }
            CoreInstantiation::Row(row) => eff_row_rigid_vars(row, acc),
        }
    }
}

fn binder_rigid_vars(binder: &TypedBinder, acc: &mut BTreeSet<Sym>) {
    core_type_rigid_vars(&binder.ty, acc);
}

fn pattern_rigid_vars(pattern: &TypedPattern, acc: &mut BTreeSet<Sym>) {
    match pattern {
        TypedPattern::Wild => {}
        TypedPattern::Var(binder) => binder_rigid_vars(binder, acc),
        TypedPattern::Ctor {
            instantiation,
            fields,
            ..
        } => {
            instantiation_rigid_vars(instantiation, acc);
            for field in fields.iter().flatten() {
                binder_rigid_vars(field, acc);
            }
        }
        TypedPattern::Tuple(fields) => {
            for field in fields.iter().flatten() {
                binder_rigid_vars(field, acc);
            }
        }
    }
}

fn value_rigid_vars(value: &TypedValue, acc: &mut BTreeSet<Sym>) {
    core_type_rigid_vars(&value.ty, acc);
    match &value.kind {
        TypedValueKind::Var { instantiation, .. } => instantiation_rigid_vars(instantiation, acc),
        TypedValueKind::Ctor {
            instantiation,
            fields,
            ..
        } => {
            instantiation_rigid_vars(instantiation, acc);
            for field in fields {
                value_rigid_vars(field, acc);
            }
        }
        TypedValueKind::Tuple(fields) | TypedValueKind::UnboxedTuple(fields) => {
            for field in fields {
                value_rigid_vars(field, acc);
            }
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields {
                value_rigid_vars(field, acc);
            }
        }
        TypedValueKind::Thunk(body) => comp_rigid_vars(body, acc),
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr { value: inner, .. }
        | TypedValueKind::NewtypeRepr { value: inner, .. } => value_rigid_vars(inner, acc),
        _ => {}
    }
}

/// Every rigid type and effect-row variable mentioned anywhere in a typed
/// computation: signatures, binders (including pattern and handler-arm
/// binders), value types, and explicit instantiations.
pub(super) fn comp_rigid_vars(comp: &TypedComp, acc: &mut BTreeSet<Sym>) {
    comp_sig_rigid_vars(&comp.sig, acc);
    match &comp.kind {
        TypedCompKind::Bind(_, binder, _) => binder_rigid_vars(binder, acc),
        TypedCompKind::Lam(params, _) => {
            for param in params {
                binder_rigid_vars(param, acc);
            }
        }
        TypedCompKind::Case(_, arms) => {
            for (pattern, _) in arms {
                pattern_rigid_vars(pattern, acc);
            }
        }
        TypedCompKind::Handle {
            return_binder, ops, ..
        } => {
            if let Some(binder) = return_binder {
                binder_rigid_vars(binder, acc);
            }
            for op in ops.arms() {
                instantiation_rigid_vars(&op.instantiation, acc);
                for param in &op.params {
                    binder_rigid_vars(param, acc);
                }
                binder_rigid_vars(&op.resume, acc);
            }
        }
        TypedCompKind::Call { instantiation, .. }
        | TypedCompKind::App { instantiation, .. }
        | TypedCompKind::Do { instantiation, .. }
        | TypedCompKind::StrBuiltin { instantiation, .. } => {
            instantiation_rigid_vars(instantiation, acc);
        }
        TypedCompKind::WithReuse { token, .. } | TypedCompKind::Reuse(token, _) => {
            binder_rigid_vars(token, acc);
        }
        _ => {}
    }
    each_value(comp, &mut |value| value_rigid_vars(value, acc));
    each_subcomp(comp, &mut |child| comp_rigid_vars(child, acc));
}

/// The first rigid type or effect-row variable a monomorphized clone would
/// capture free under the call's instantiation. A clone carries no quantifiers,
/// so any variable a substituted argument still names is unbound inside it; the
/// canonical shape is an effect-polymorphic callee applied under an open ambient
/// row. `None` means every argument is ground and the clone is closed.
pub(super) fn open_clone_variable(instantiation: &[CoreInstantiation]) -> Option<Sym> {
    let mut variables = BTreeSet::new();
    for argument in instantiation {
        match argument {
            CoreInstantiation::Type(ty) => {
                ty.free_ty_vars(&mut variables);
                ty.free_row_vars(&mut variables);
            }
            CoreInstantiation::Row(row) => {
                if let EffRow::Var(tail) = row.tail() {
                    variables.insert(*tail);
                }
                for label in row.labels() {
                    for argument in &label.args {
                        argument.free_ty_vars(&mut variables);
                        argument.free_row_vars(&mut variables);
                    }
                }
            }
        }
    }
    variables.into_iter().next()
}
