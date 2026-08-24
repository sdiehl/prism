use crate::types::Type;

use super::super::build::lower_value_type;
use super::super::violation::{InstantiationError, QuantifierKind, SchemeError};
use super::super::{CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType};
use super::env::{ConstructorSig, OperationSig};
use super::subst::{substitute_core_type, substitute_label, substitute_sig};

pub(super) use super::env::{MonoConstructor, MonoOperation};

/// The Core calling convention of a checked scheme: its quantifiers, its
/// lowered parameter types, and the computation signature it answers with.
///
/// # Errors
/// [`SchemeError`] naming what the scheme peels down to, when that is not a
/// function type.
pub fn scheme_to_fn_sig(mut ty: Type) -> Result<CoreFnSig, SchemeError> {
    let mut quantifiers = Vec::new();
    loop {
        match ty {
            Type::Forall(name, body) => {
                quantifiers.push(CoreQuantifier::Type(name));
                ty = *body;
            }
            Type::RowForall(name, body) => {
                quantifiers.push(CoreQuantifier::Row(name));
                ty = *body;
            }
            Type::Fun(params, effects, result) => {
                return Ok(CoreFnSig::new(
                    quantifiers,
                    params.iter().map(lower_value_type).collect(),
                    CompSig::new(lower_value_type(&result), effects),
                ));
            }
            other => return Err(SchemeError { found: other }),
        }
    }
}

/// Substitute `arguments` through a function signature, yielding the
/// monomorphic signature the call site must match.
///
/// # Errors
/// [`InstantiationError`] when `arguments` do not match the signature's
/// quantifiers in count or in kind.
pub fn instantiate_fn(
    signature: &CoreFnSig,
    arguments: &[CoreInstantiation],
) -> Result<CoreFnSig, InstantiationError> {
    require_instantiation(signature.quantifiers(), arguments)?;
    let params = signature
        .params()
        .iter()
        .map(|ty| substitute_core_type(ty, signature.quantifiers(), arguments))
        .collect();
    let body = substitute_sig(signature.body(), signature.quantifiers(), arguments);
    Ok(CoreFnSig::new(Vec::new(), params, body))
}

/// Substitute `arguments` through a value's type, looking through a thunk to
/// the function it suspends. A value that quantifies nothing accepts only an
/// empty instantiation.
///
/// # Errors
/// [`InstantiationError`] when `arguments` do not match the type's quantifiers
/// in count or in kind.
pub fn instantiate_value_scheme(
    ty: &CoreType,
    arguments: &[CoreInstantiation],
) -> Result<CoreType, InstantiationError> {
    match ty {
        CoreType::Function(signature) => instantiate_fn(signature, arguments)
            .map(|signature| CoreType::Function(Box::new(signature))),
        CoreType::Thunk(suspension) => {
            let CoreType::Function(signature) = suspension.result() else {
                require_instantiation(&[], arguments)?;
                return Ok(ty.clone());
            };
            let signature = instantiate_fn(signature, arguments)?;
            Ok(CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(signature)),
                suspension.effects().clone(),
            ))))
        }
        _ => {
            require_instantiation(&[], arguments)?;
            Ok(ty.clone())
        }
    }
}

/// Substitute `arguments` through a constructor signature, yielding the field
/// and result types this occurrence commits to.
///
/// # Errors
/// [`InstantiationError`] when `arguments` do not match the constructor's
/// quantifiers in count or in kind.
pub fn instantiate_constructor(
    signature: &ConstructorSig,
    arguments: &[CoreInstantiation],
) -> Result<MonoConstructor, InstantiationError> {
    require_instantiation(&signature.quantifiers, arguments)?;
    Ok(MonoConstructor {
        tag: signature.tag,
        fields: signature
            .fields
            .iter()
            .map(|ty| substitute_core_type(ty, &signature.quantifiers, arguments))
            .collect(),
        result: substitute_core_type(&signature.result, &signature.quantifiers, arguments),
    })
}

/// Substitute `arguments` through an operation signature, yielding the
/// parameter, result, and effect label this occurrence commits to.
///
/// # Errors
/// [`InstantiationError`] when `arguments` do not match the operation's
/// quantifiers in count or in kind.
pub fn instantiate_operation(
    signature: &OperationSig,
    arguments: &[CoreInstantiation],
) -> Result<MonoOperation, InstantiationError> {
    require_instantiation(&signature.quantifiers, arguments)?;
    Ok(MonoOperation {
        params: signature
            .params
            .iter()
            .map(|ty| substitute_core_type(ty, &signature.quantifiers, arguments))
            .collect(),
        result: substitute_core_type(&signature.result, &signature.quantifiers, arguments),
        effect: substitute_label(&signature.effect, &signature.quantifiers, arguments),
    })
}

fn require_instantiation(
    quantifiers: &[CoreQuantifier],
    arguments: &[CoreInstantiation],
) -> Result<(), InstantiationError> {
    if quantifiers.len() != arguments.len() {
        return Err(InstantiationError::Count {
            found: arguments.len(),
            quantifiers: quantifiers.len(),
        });
    }
    for (index, (quantifier, argument)) in quantifiers.iter().zip(arguments).enumerate() {
        if !matches!(
            (quantifier, argument),
            (CoreQuantifier::Type(_), CoreInstantiation::Type(_))
                | (CoreQuantifier::Row(_), CoreInstantiation::Row(_))
        ) {
            return Err(InstantiationError::Kind {
                index,
                expected: match quantifier {
                    CoreQuantifier::Type(_) => QuantifierKind::Type,
                    CoreQuantifier::Row(_) => QuantifierKind::Row,
                },
            });
        }
    }
    Ok(())
}
