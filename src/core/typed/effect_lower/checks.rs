//! Structural invariants at direct/monadic calling-convention boundaries.

use std::collections::{BTreeMap, BTreeSet};

use crate::names::ENTRY_POINT;
use crate::sym::Sym;

use super::super::{TypedComp, TypedCompKind, TypedCoreFn, TypedValueKind};
use super::{abi, walk};

/// Validate the tails that use the free-monad calling convention.
///
/// Whole-program lowering also monadifies every stored thunk and lambda body;
/// selective lowering checks only the named top-level declarations. Entry
/// functions are exempt because their final `EPure` is unwrapped for direct
/// callers before this rail runs.
pub(super) fn check_convention_boundaries(
    arity_functions: &[TypedCoreFn],
    functions: &[&TypedCoreFn],
    monadic: &BTreeSet<Sym>,
    blanket: bool,
    exempt: &BTreeSet<Sym>,
) -> Result<(), String> {
    let arities: BTreeMap<Sym, usize> = arity_functions
        .iter()
        .map(|function| (function.name(), function.params().len()))
        .collect();
    for function in functions {
        if !monadic.contains(&function.name()) || exempt.contains(&function.name()) {
            continue;
        }
        check_tails(function.name(), function.body(), &arities)?;
        if blanket {
            let mut thunks = Vec::new();
            walk::thunks_in_comp(function.body(), &mut thunks);
            for thunk in thunks {
                let body = match thunk.kind() {
                    TypedCompKind::Lam(_, body) => body.as_ref(),
                    _ => thunk,
                };
                check_tails(function.name(), body, &arities)?;
            }
        }
    }
    Ok(())
}

fn check_tails(
    function: Sym,
    comp: &TypedComp,
    arities: &BTreeMap<Sym, usize>,
) -> Result<(), String> {
    match comp.kind() {
        TypedCompKind::Bind(_, _, tail) => check_tails(function, tail, arities),
        TypedCompKind::If(_, yes, no) => {
            check_tails(function, yes, arities)?;
            check_tails(function, no, arities)
        }
        TypedCompKind::Case(_, arms) => {
            for (_, body) in arms {
                check_tails(function, body, arities)?;
            }
            Ok(())
        }
        TypedCompKind::Return(value)
            if matches!(
                value.kind(),
                TypedValueKind::Ctor { name, .. }
                    if abi::is_monadic_tail_constructor(*name)
            ) =>
        {
            Ok(())
        }
        TypedCompKind::Call { callee, args, .. }
            if callee.as_str() != ENTRY_POINT && arities.get(callee) == Some(&args.len()) =>
        {
            Ok(())
        }
        TypedCompKind::App { .. } | TypedCompKind::Error(_) => Ok(()),
        other => Err(format!(
            "monadification: `{function}` tail is not Eff-shaped: {}",
            kind_name(other)
        )),
    }
}

const fn kind_name(kind: &TypedCompKind) -> &'static str {
    match kind {
        TypedCompKind::Return(_) => "return",
        TypedCompKind::Bind(..) => "bind",
        TypedCompKind::Force(_) => "force",
        TypedCompKind::Lam(..) => "lambda",
        TypedCompKind::App { .. } => "application",
        TypedCompKind::If(..) => "if",
        TypedCompKind::Prim(..) => "primitive",
        TypedCompKind::Call { .. } => "call",
        TypedCompKind::Io(..) => "io",
        TypedCompKind::Error(_) => "error",
        TypedCompKind::Case(..) => "case",
        TypedCompKind::FloatBuiltin(..) => "float builtin",
        TypedCompKind::Neg(..) => "negation",
        TypedCompKind::UnboxedProject(..) => "unboxed projection",
        TypedCompKind::Do { .. } => "effect operation",
        TypedCompKind::Handle { .. } => "handler",
        TypedCompKind::Mask(..) => "effect mask",
        TypedCompKind::StrBuiltin { .. } => "string builtin",
        TypedCompKind::Dup(_) => "dup",
        TypedCompKind::Drop(_) => "drop",
        TypedCompKind::WithReuse { .. } => "with-reuse",
        TypedCompKind::Reuse(..) => "reuse",
        TypedCompKind::InitAt(..) => "init-at",
        TypedCompKind::RefNew(_) => "ref-new",
        TypedCompKind::RefGet(_) => "ref-get",
        TypedCompKind::RefSet(..) => "ref-set",
    }
}

#[cfg(test)]
mod tests {
    use crate::core::typed::{CompSig, CoreFnSig, CoreType, TypedValue};
    use crate::types::ty::EffRow;
    use crate::types::Type;

    use super::*;

    fn int() -> CoreType {
        CoreType::Source(Type::Int)
    }

    fn bare_return(value: i64) -> TypedComp {
        TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::Return(TypedValue::new(int(), TypedValueKind::Int(value))),
        )
    }

    fn function(name: &str, body: TypedComp) -> TypedCoreFn {
        let signature = body.sig().clone();
        TypedCoreFn::new(
            Sym::from(name),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), signature),
            0,
        )
    }

    #[test]
    fn a_bare_monadic_tail_is_rejected_but_an_entry_is_exempt() {
        let function = function("worker", bare_return(1));
        let functions = vec![function];
        let monadic = BTreeSet::from([Sym::from("worker")]);
        let refs = functions.iter().collect::<Vec<_>>();
        assert!(
            check_convention_boundaries(&functions, &refs, &monadic, false, &BTreeSet::new(),)
                .is_err()
        );
        assert_eq!(
            check_convention_boundaries(&functions, &refs, &monadic, false, &monadic),
            Ok(())
        );
    }

    #[test]
    fn whole_program_mode_checks_stored_lambda_tails() {
        let lambda_body = bare_return(2);
        let lambda = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    Vec::new(),
                    lambda_body.sig().clone(),
                ))),
                EffRow::Empty,
            ),
            TypedCompKind::Lam(Vec::new(), Box::new(lambda_body)),
        );
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        );
        let head = TypedComp::new(
            CompSig::new(thunk.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(thunk),
        );
        let result =
            crate::core::typed::TypedBinder::new(Sym::from("stored"), head.sig().result().clone());
        let tail = abi::epure(
            abi::lowered_repr(TypedValue::new(int(), TypedValueKind::Int(0)), abi::word()),
            EffRow::Empty,
        );
        let body = TypedComp::new(
            tail.sig().clone(),
            TypedCompKind::Bind(Box::new(head), result, Box::new(tail)),
        );
        let function = function("worker", body);
        let functions = vec![function];
        let refs = functions.iter().collect::<Vec<_>>();
        let monadic = BTreeSet::from([Sym::from("worker")]);

        assert_eq!(
            check_convention_boundaries(&functions, &refs, &monadic, false, &BTreeSet::new(),),
            Ok(())
        );
        assert!(
            check_convention_boundaries(&functions, &refs, &monadic, true, &BTreeSet::new(),)
                .is_err()
        );
    }
}
