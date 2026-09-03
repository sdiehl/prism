//! Typed builders at the elaboration boundary.
//!
//! The builder consumes the elaborator's executable Core as a compatibility
//! input, reconstructs witnesses from checked declaration schemes, verifies the
//! result, and erases at the typed-prefix boundary. No source inference is
//! called here.

mod env;
mod solve;
mod walk;
mod zonk;

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::error::{Error, TypedCoreConstructionFailure};

use crate::core::Core;
use crate::types::Type;

pub use env::{build_verify_env, core_fn_sig, dict_type};
pub(crate) use env::{lower_value_type, source_type};

use env::{core_row_vars, row_vars};
use solve::{free_core_vars, free_row_vars};
use walk::Builder;

use super::on_core_stack;
use super::verify::row_included;
use super::{
    CompSig, CoreFnSig, CoreQuantifier, CoreType, Elaborated, TypedCoreFn, UncheckedTypedCore,
    VerifyEnv,
};

#[cfg(test)]
use crate::types::ty::EffRow;
#[cfg(test)]
use prism_syntax::names::IO_EFFECT;
#[cfg(test)]
use solve::Solver;

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

/// Reconstruct checked witnesses for the elaborator's compatibility tree. The
/// returned program is ready for the independent proof checker; the only public
/// escape from this module is semantic erasure.
///
/// # Errors
/// A [`TypedCoreConstructionFailure`] when a node's witnesses cannot be
/// reconstructed from the declared schemes, or a
/// [`prism_syntax::error::TypedCoreEnvironmentFailure`] when the environment those schemes come from
/// is itself ill-formed.
pub fn build_typed(
    core: Core,
    signatures: &BTreeMap<Sym, CoreFnSig>,
    verify_env: &VerifyEnv,
) -> Result<UncheckedTypedCore<Elaborated>, Error> {
    on_core_stack(|| build_typed_on_grown_stack(core, signatures, verify_env))
}

fn build_typed_on_grown_stack(
    core: Core,
    signatures: &BTreeMap<Sym, CoreFnSig>,
    verify_env: &VerifyEnv,
) -> Result<UncheckedTypedCore<Elaborated>, Error> {
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
                .map_err(|error| TypedCoreConstructionFailure::InvalidWitness {
                    function: function.name.to_string(),
                    path: "result refinement".into(),
                    detail: error.to_string(),
                })?;
            builder.solve_pending_handler_rows(true).map_err(|error| {
                TypedCoreConstructionFailure::InvalidWitness {
                    function: function.name.to_string(),
                    path: "result refinement residual handlers".into(),
                    detail: error.to_string(),
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
                    .map_err(|error| TypedCoreConstructionFailure::InvalidWitness {
                        function: function.name.to_string(),
                        path: "effect refinement".into(),
                        detail: error.to_string(),
                    })?;
                builder.solve_pending_handler_rows(true).map_err(|error| {
                    TypedCoreConstructionFailure::InvalidWitness {
                        function: function.name.to_string(),
                        path: "effect refinement residual handlers".into(),
                        detail: error.to_string(),
                    }
                })?;
                builder.solver.final_row(body.sig().effects())
            };
            if inferred != *signature.body().effects() {
                // The refinement may only widen a declared row toward what the
                // body performs; a replacement that drops a declared effect
                // would launder the very rows the verifier checks.
                if !row_included(signature.body().effects(), &inferred) {
                    return Err(TypedCoreConstructionFailure::InvalidWitness {
                        function: function.name.to_string(),
                        path: "effect refinement monotonicity".into(),
                        detail: format!(
                            "refined row {} does not include the declared row {}",
                            inferred.show(),
                            signature.body().effects().show()
                        ),
                    }
                    .into());
                }
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
            .map_err(|error| TypedCoreConstructionFailure::InvalidWitness {
                function: function.name.to_string(),
                path: "body".into(),
                detail: error.to_string(),
            })?;
        builder.solve_pending_handler_rows(true).map_err(|error| {
            TypedCoreConstructionFailure::InvalidWitness {
                function: function.name.to_string(),
                path: "body residual handlers".into(),
                detail: error.to_string(),
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
    Ok(UncheckedTypedCore::new(functions))
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
        assert!(env::representation_preserving(&actual, &expected));

        let different_result = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![CoreType::Source(Type::Int)],
                CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            ))),
            EffRow::Empty,
        )));
        assert!(!env::representation_preserving(&actual, &different_result));
    }
}
