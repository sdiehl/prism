//! Structural invariants at direct/monadic calling-convention boundaries.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;
use prism_syntax::names::ENTRY_POINT;

use super::super::{TypedComp, TypedCompKind, TypedCoreFn, TypedValueKind};
use super::decline::{Decline, Refusal, Site};
use super::{abi, walk};

/// Which convention the thunks inside a checked program were built at.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ThunkRule {
    /// Every suspended computation belongs to the free-monad convention, so
    /// each owes an `Eff`-shaped tail. Whole-program and `LocalPartial`
    /// lowering both monadify every thunk they walk into.
    AllMonadic,
    /// The two conventions coexist within one program, so each thunk answers
    /// for the one it was actually built at.
    PerThunk,
}

/// Validate the boundaries between the direct and free-monad conventions.
///
/// Entry functions are exempt because their final `EPure` is unwrapped for
/// direct callers before this rail runs, which is also why a direct declaration
/// may call one.
///
/// Under [`ThunkRule::PerThunk`] every declaration is walked. A declaration
/// outside the region is exactly where a thunk left at
/// the direct convention can be found, and the mistake worth catching is such a
/// thunk reaching code that answers with an effect cell. A thunk carries no
/// type-level mark of its convention, so the convention is read back off the
/// shape of the body it suspends.
pub(crate) fn check_convention_boundaries(
    arity_functions: &[TypedCoreFn],
    functions: &[&TypedCoreFn],
    monadic: &BTreeSet<Sym>,
    rule: ThunkRule,
    exempt: &BTreeSet<Sym>,
) -> Result<(), Decline> {
    let arities: BTreeMap<Sym, usize> = arity_functions
        .iter()
        .map(|function| (function.name(), function.params().len()))
        .collect();
    let reachable_monadic: BTreeSet<Sym> = monadic.difference(exempt).copied().collect();
    for function in functions {
        let member = monadic.contains(&function.name()) && !exempt.contains(&function.name());
        if member {
            check_tails(function.name(), function.body(), &arities)?;
        } else if rule == ThunkRule::AllMonadic {
            continue;
        }
        let mut thunks = Vec::new();
        walk::thunks_in_comp(function.body(), &mut thunks);
        for thunk in thunks {
            let body = match thunk.kind() {
                TypedCompKind::Lam(_, body) => body.as_ref(),
                _ => thunk,
            };
            if rule == ThunkRule::AllMonadic || suspends_effect_cell(thunk) {
                check_tails(function.name(), body, &arities)?;
            } else {
                check_direct_thunk(function.name(), body, &reachable_monadic)?;
            }
        }
    }
    Ok(())
}

/// Whether the computation a thunk suspends answers with an effect cell, the
/// only structural evidence that the monadic builder produced it.
fn suspends_effect_cell(thunk: &TypedComp) -> bool {
    abi::answers_with_effect_cell(thunk.sig().result())
}

/// A thunk left at the direct convention is copied verbatim into the output, so
/// it must not reach the other convention anywhere in its body. A member call
/// buried mid-body answers with an effect cell the
/// direct code around it would consume as an ordinary result.
///
/// Nested thunks are not descended into. Each is a site of its own with its own
/// convention, and is checked as one by the caller's walk.
fn check_direct_thunk(
    function: Sym,
    comp: &TypedComp,
    monadic: &BTreeSet<Sym>,
) -> Result<(), Decline> {
    match comp.kind() {
        TypedCompKind::Call { callee, .. } if monadic.contains(callee) => {
            return Err(Decline::new(
                Refusal::ThunkBoundary,
                function,
                Site::Name(*callee),
            ));
        }
        TypedCompKind::Return(value)
            if matches!(
                value.kind(),
                TypedValueKind::Ctor { name, .. } if abi::is_monadic_tail_constructor(*name)
            ) =>
        {
            return Err(Decline::whole(Refusal::ThunkBoundary, function));
        }
        _ => {}
    }
    let mut failure = Ok(());
    walk::each_subcomp(comp, &mut |child| {
        if failure.is_ok() {
            failure = check_direct_thunk(function, child, monadic);
        }
    });
    failure
}

fn check_tails(
    function: Sym,
    comp: &TypedComp,
    arities: &BTreeMap<Sym, usize>,
) -> Result<(), Decline> {
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
        other => Err(Decline::new(
            Refusal::MemberTail,
            function,
            Site::Shape(kind_name(other)),
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
        assert_eq!(
            check_convention_boundaries(
                &functions,
                &refs,
                &monadic,
                ThunkRule::PerThunk,
                &BTreeSet::new(),
            ),
            Err(Decline::new(
                Refusal::MemberTail,
                Sym::from("worker"),
                Site::Shape("return"),
            )),
            "the refusal names the member and the shape its tail had"
        );
        assert_eq!(
            check_convention_boundaries(&functions, &refs, &monadic, ThunkRule::PerThunk, &monadic),
            Ok(())
        );
    }

    /// A thunk whose body is `body`, at whatever convention `body` was built.
    fn thunk_of(body: TypedComp) -> TypedValue {
        let lambda = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    Vec::new(),
                    body.sig().clone(),
                ))),
                EffRow::Empty,
            ),
            TypedCompKind::Lam(Vec::new(), Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        )
    }

    fn returning(value: TypedValue) -> TypedComp {
        TypedComp::new(
            CompSig::new(value.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(value),
        )
    }

    /// A member's body: an effect cell, which is what makes calling it from the
    /// direct convention wrong.
    fn effect_cell() -> TypedComp {
        abi::epure(
            abi::lowered_repr(TypedValue::new(int(), TypedValueKind::Int(0)), abi::word()),
            EffRow::Empty,
        )
    }

    #[test]
    fn a_direct_thunk_may_not_call_a_function_using_the_other_convention() {
        let worker = function("worker", effect_cell());
        let call_worker = TypedComp::new(
            CompSig::new(int(), EffRow::Empty),
            TypedCompKind::Call {
                callee: Sym::from("worker"),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let builder = function("builder", returning(thunk_of(call_worker.clone())));
        let functions = vec![worker, builder];
        let refs: Vec<&TypedCoreFn> = functions.iter().collect();
        let monadic = BTreeSet::from([Sym::from("worker")]);

        assert_eq!(
            check_convention_boundaries(
                &functions,
                &refs,
                &monadic,
                ThunkRule::PerThunk,
                &BTreeSet::new(),
            ),
            Err(Decline::new(
                Refusal::ThunkBoundary,
                Sym::from("builder"),
                Site::Name(Sym::from("worker")),
            )),
            "a thunk left at the direct convention must not reach a function \
             that answers with an effect cell, and the refusal names both"
        );

        // The same call is well formed once the thunk holding it was built by
        // the monadic builder, which the effect-cell result records.
        let monadic_thunk = returning(thunk_of(TypedComp::new(
            CompSig::new(abi::eff(EffRow::Empty), EffRow::Empty),
            call_worker.kind().clone(),
        )));
        let functions = vec![functions[0].clone(), function("builder", monadic_thunk)];
        let refs: Vec<&TypedCoreFn> = functions.iter().collect();
        assert_eq!(
            check_convention_boundaries(
                &functions,
                &refs,
                &monadic,
                ThunkRule::PerThunk,
                &BTreeSet::new(),
            ),
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
            check_convention_boundaries(
                &functions,
                &refs,
                &monadic,
                ThunkRule::PerThunk,
                &BTreeSet::new(),
            ),
            Ok(())
        );
        assert!(check_convention_boundaries(
            &functions,
            &refs,
            &monadic,
            ThunkRule::AllMonadic,
            &BTreeSet::new(),
        )
        .is_err());
    }
}
