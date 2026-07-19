//! Typed whole-program runtime trampoline.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::effect_abi::{BOUNCE_TAG, EBOUNCE, EOP, EPURE, ERESUME};
use crate::names;
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::util::fresh::Fresh;

use super::super::{
    CompSig, CoreFnSig, CoreQuantifier, CoreType, LoweredType, TypedBinder, TypedComp,
    TypedCompKind, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind,
};
use super::abi;

const DRIVE: &str = "prism_drive";
const NO_FRAME: usize = usize::MAX;
const DRIVE_ROW: &str = "rho_drive@";

const fn pure(result: CoreType) -> CompSig {
    CompSig::new(result, EffRow::Empty)
}

fn var(binder: &TypedBinder) -> TypedValue {
    TypedValue::new(
        binder.ty().clone(),
        TypedValueKind::Var {
            name: binder.name(),
            instantiation: Vec::new(),
        },
    )
}

fn is_eff_ctor(name: Sym) -> bool {
    matches!(name.as_str(), EPURE | EOP | ERESUME | EBOUNCE)
}

fn eff_row(ty: &CoreType) -> Option<EffRow> {
    let CoreType::Lowered(LoweredType::Eff(row)) = ty else {
        return None;
    };
    Some(row.clone())
}

fn is_eff_case(arms: &[(TypedPattern, TypedComp)]) -> bool {
    arms.iter().any(
        |(pattern, _)| matches!(pattern, TypedPattern::Ctor { name, .. } if is_eff_ctor(*name)),
    )
}

fn eff_tail(comp: &TypedComp, eff: &BTreeSet<Sym>) -> bool {
    match comp.kind() {
        TypedCompKind::Return(TypedValue {
            kind: TypedValueKind::Ctor { name, .. },
            ..
        }) => is_eff_ctor(*name),
        TypedCompKind::Call { callee, .. } => eff.contains(callee),
        TypedCompKind::App { .. } | TypedCompKind::Force(_) | TypedCompKind::Error(_) => true,
        TypedCompKind::If(_, yes, no) => eff_tail(yes, eff) && eff_tail(no, eff),
        TypedCompKind::Case(_, arms) => arms.iter().all(|(_, body)| eff_tail(body, eff)),
        TypedCompKind::Bind(_, _, tail) => eff_tail(tail, eff),
        _ => false,
    }
}

fn eff_functions(functions: &[TypedCoreFn]) -> BTreeSet<Sym> {
    let mut eff: BTreeSet<Sym> = functions.iter().map(TypedCoreFn::name).collect();
    loop {
        let mut changed = false;
        for function in functions {
            if eff.contains(&function.name()) && !eff_tail(function.body(), &eff) {
                eff.remove(&function.name());
                changed = true;
            }
        }
        if !changed {
            return eff;
        }
    }
}

fn bounce(comp: TypedComp) -> Option<TypedComp> {
    let row = eff_row(comp.sig().result())?;
    let signature = CoreFnSig::new(Vec::new(), Vec::new(), comp.sig().clone());
    let lambda = TypedComp::new(
        pure(CoreType::Function(Box::new(signature))),
        TypedCompKind::Lam(Vec::new(), Box::new(comp)),
    );
    let thunk = TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    );
    let value = TypedValue::new(
        abi::eff(row.clone()),
        TypedValueKind::Ctor {
            name: Sym::from(EBOUNCE),
            tag: BOUNCE_TAG,
            instantiation: abi::row_instantiation(row),
            fields: vec![thunk],
        },
    );
    Some(TypedComp::new(
        pure(value.ty().clone()),
        TypedCompKind::Return(value),
    ))
}

fn drive(value: TypedValue, row: EffRow) -> TypedComp {
    TypedComp::new(
        CompSig::new(abi::eff(row.clone()), row.clone()),
        TypedCompKind::Call {
            callee: Sym::from(DRIVE),
            instantiation: abi::row_instantiation(row),
            args: vec![value],
        },
    )
}

/// The row-polymorphic loop that forces one deferred hop at a time.
pub(super) fn prism_drive_fn() -> TypedCoreFn {
    let row_name = Sym::from(DRIVE_ROW);
    let row = EffRow::Var(row_name);
    let current = TypedBinder::new(Sym::from(names::RET), abi::eff(row.clone()));
    let thunk = TypedBinder::new(Sym::from(names::EBIND_FN), abi::bounce(row.clone()));
    let next = TypedBinder::new(Sym::from(names::COMPOSE), abi::eff(row.clone()));

    let forced = TypedComp::new(
        match thunk.ty() {
            CoreType::Thunk(signature) => (**signature).clone(),
            _ => unreachable!("the bounce field is a thunk"),
        },
        TypedCompKind::Force(var(&thunk)),
    );
    let applied = TypedComp::new(
        CompSig::new(abi::eff(row.clone()), row.clone()),
        TypedCompKind::App {
            callee: Box::new(forced),
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    let redrive = drive(var(&next), row.clone());
    let bounce_arm = (
        TypedPattern::Ctor {
            name: Sym::from(EBOUNCE),
            instantiation: abi::row_instantiation(row.clone()),
            fields: vec![Some(thunk)],
        },
        TypedComp::new(
            redrive.sig().clone(),
            TypedCompKind::Bind(Box::new(applied), next, Box::new(redrive)),
        ),
    );
    let other_arm = (
        TypedPattern::Wild,
        TypedComp::new(
            pure(current.ty().clone()),
            TypedCompKind::Return(var(&current)),
        ),
    );
    let body = TypedComp::new(
        CompSig::new(abi::eff(row.clone()), row.clone()),
        TypedCompKind::Case(var(&current), vec![bounce_arm, other_arm]),
    );
    TypedCoreFn::new(
        Sym::from(DRIVE),
        vec![current],
        body,
        CoreFnSig::new(
            vec![CoreQuantifier::Row(row_name)],
            vec![abi::eff(row.clone())],
            CompSig::new(abi::eff(row.clone()), row),
        ),
        0,
    )
}

struct Tr<'a> {
    eff: &'a BTreeSet<Sym>,
    arity: &'a BTreeMap<Sym, usize>,
    fresh: &'a mut Fresh,
    current_arity: usize,
}

impl Tr<'_> {
    fn native_tail(&self, callee: Sym, arguments: usize) -> bool {
        self.arity.get(&callee) == Some(&arguments) && arguments == self.current_arity
    }

    fn value(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let ty = value.ty().clone();
        Some(match value.kind() {
            TypedValueKind::Thunk(body) => {
                let context = eff_tail(body, self.eff);
                let saved = std::mem::replace(&mut self.current_arity, NO_FRAME);
                let body = self.go(body, context, true);
                self.current_arity = saved;
                let body = body?;
                TypedValue::new(
                    CoreType::Thunk(Box::new(body.sig().clone())),
                    TypedValueKind::Thunk(Box::new(body)),
                )
            }
            TypedValueKind::Reinterpret(inner) => TypedValue::new(
                ty,
                TypedValueKind::Reinterpret(Box::new(self.value(inner)?)),
            ),
            TypedValueKind::LoweredRepr { value, proof } => TypedValue::new(
                ty,
                TypedValueKind::LoweredRepr {
                    value: Box::new(self.value(value)?),
                    proof: proof.clone(),
                },
            ),
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValue::new(
                ty,
                TypedValueKind::NewtypeRepr {
                    constructor: *constructor,
                    instantiation: instantiation.clone(),
                    value: Box::new(self.value(value)?),
                },
            ),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValue::new(
                ty,
                TypedValueKind::Ctor {
                    name: *name,
                    tag: *tag,
                    instantiation: instantiation.clone(),
                    fields: fields
                        .iter()
                        .map(|field| self.value(field))
                        .collect::<Option<_>>()?,
                },
            ),
            TypedValueKind::Tuple(fields) => TypedValue::new(
                ty,
                TypedValueKind::Tuple(
                    fields
                        .iter()
                        .map(|field| self.value(field))
                        .collect::<Option<_>>()?,
                ),
            ),
            _ => value.clone(),
        })
    }

    // Computations stored in values go through `go(_, context, false)`. That is
    // deliberately different from `value`, whose thunk is a new tail scope.
    // Keep the two traversals separate so the rewrite consumes fresh names in
    // the same places and order.
    fn fallback_value(&mut self, value: &TypedValue, context: bool) -> Option<TypedValue> {
        let ty = value.ty().clone();
        Some(match value.kind() {
            TypedValueKind::Thunk(body) => {
                let body = self.go(body, context, false)?;
                TypedValue::new(
                    CoreType::Thunk(Box::new(body.sig().clone())),
                    TypedValueKind::Thunk(Box::new(body)),
                )
            }
            TypedValueKind::Reinterpret(inner) => TypedValue::new(
                ty,
                TypedValueKind::Reinterpret(Box::new(self.fallback_value(inner, context)?)),
            ),
            TypedValueKind::LoweredRepr { value, proof } => TypedValue::new(
                ty,
                TypedValueKind::LoweredRepr {
                    value: Box::new(self.fallback_value(value, context)?),
                    proof: proof.clone(),
                },
            ),
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValue::new(
                ty,
                TypedValueKind::NewtypeRepr {
                    constructor: *constructor,
                    instantiation: instantiation.clone(),
                    value: Box::new(self.fallback_value(value, context)?),
                },
            ),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValue::new(
                ty,
                TypedValueKind::Ctor {
                    name: *name,
                    tag: *tag,
                    instantiation: instantiation.clone(),
                    fields: fields
                        .iter()
                        .map(|field| self.fallback_value(field, context))
                        .collect::<Option<_>>()?,
                },
            ),
            TypedValueKind::Tuple(fields) => TypedValue::new(
                ty,
                TypedValueKind::Tuple(
                    fields
                        .iter()
                        .map(|field| self.fallback_value(field, context))
                        .collect::<Option<_>>()?,
                ),
            ),
            TypedValueKind::UnboxedTuple(fields) => TypedValue::new(
                ty,
                TypedValueKind::UnboxedTuple(
                    fields
                        .iter()
                        .map(|field| self.fallback_value(field, context))
                        .collect::<Option<_>>()?,
                ),
            ),
            TypedValueKind::UnboxedRecord(fields) => TypedValue::new(
                ty,
                TypedValueKind::UnboxedRecord(
                    fields
                        .iter()
                        .map(|(name, field)| Some((*name, self.fallback_value(field, context)?)))
                        .collect::<Option<_>>()?,
                ),
            ),
            _ => value.clone(),
        })
    }

    fn go(&mut self, comp: &TypedComp, context: bool, tail: bool) -> Option<TypedComp> {
        Some(match comp.kind() {
            TypedCompKind::Return(value) => {
                let value = self.value(value)?;
                TypedComp::new(pure(value.ty().clone()), TypedCompKind::Return(value))
            }
            TypedCompKind::Bind(head, binder, rest) => {
                let head = self.go(head, context, false)?;
                let rest = self.go(rest, context, tail)?;
                TypedComp::new(
                    CompSig::new(
                        rest.sig().result().clone(),
                        super::union_effects(head.sig().effects(), rest.sig().effects()),
                    ),
                    TypedCompKind::Bind(Box::new(head), binder.clone(), Box::new(rest)),
                )
            }
            TypedCompKind::Force(value) => {
                TypedComp::new(comp.sig().clone(), TypedCompKind::Force(self.value(value)?))
            }
            TypedCompKind::Lam(parameters, body) => {
                let context = eff_tail(body, self.eff);
                let saved = std::mem::replace(&mut self.current_arity, NO_FRAME);
                let body = self.go(body, context, true);
                self.current_arity = saved;
                let body = body?;
                TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Lam(parameters.clone(), Box::new(body)),
                )
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let application = TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::App {
                        callee: Box::new(self.go(callee, context, false)?),
                        instantiation: instantiation.clone(),
                        args: args
                            .iter()
                            .map(|argument| self.value(argument))
                            .collect::<Option<_>>()?,
                    },
                );
                if tail && context {
                    bounce(application)?
                } else {
                    application
                }
            }
            TypedCompKind::If(condition, yes, no) => {
                let yes = self.go(yes, context, tail)?;
                let no = self.go(no, context, tail)?;
                TypedComp::new(
                    CompSig::new(
                        yes.sig().result().clone(),
                        super::union_effects(yes.sig().effects(), no.sig().effects()),
                    ),
                    TypedCompKind::If(condition.clone(), Box::new(yes), Box::new(no)),
                )
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                let call = TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Call {
                        callee: *callee,
                        instantiation: instantiation.clone(),
                        args: args
                            .iter()
                            .map(|argument| self.value(argument))
                            .collect::<Option<_>>()?,
                    },
                );
                if tail
                    && context
                    && self.eff.contains(callee)
                    && !self.native_tail(*callee, args.len())
                {
                    bounce(call)?
                } else {
                    call
                }
            }
            TypedCompKind::Case(scrutinee, arms) => {
                let arms = arms
                    .iter()
                    .map(|(pattern, body)| Some((pattern.clone(), self.go(body, context, tail)?)))
                    .collect::<Option<Vec<_>>>()?;
                let case_effects = arms.iter().fold(EffRow::Empty, |effects, (_, body)| {
                    super::union_effects(&effects, body.sig().effects())
                });
                let case = TypedComp::new(
                    CompSig::new(comp.sig().result().clone(), case_effects),
                    TypedCompKind::Case(scrutinee.clone(), arms.clone()),
                );
                if is_eff_case(&arms) {
                    let row = eff_row(scrutinee.ty())?;
                    let driven = TypedBinder::new(
                        Sym::from(names::lowered("drv", self.fresh.bump())),
                        scrutinee.ty().clone(),
                    );
                    let drive = drive(scrutinee.clone(), row);
                    TypedComp::new(
                        CompSig::new(
                            case.sig().result().clone(),
                            super::union_effects(drive.sig().effects(), case.sig().effects()),
                        ),
                        TypedCompKind::Bind(
                            Box::new(drive),
                            driven.clone(),
                            Box::new(TypedComp::new(
                                case.sig().clone(),
                                TypedCompKind::Case(var(&driven), arms),
                            )),
                        ),
                    )
                } else {
                    case
                }
            }
            TypedCompKind::Prim(operation, left, right) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Prim(
                    *operation,
                    self.fallback_value(left, context)?,
                    self.fallback_value(right, context)?,
                ),
            ),
            TypedCompKind::Io(operation, args) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Io(
                    *operation,
                    args.iter()
                        .map(|argument| self.fallback_value(argument, context))
                        .collect::<Option<_>>()?,
                ),
            ),
            TypedCompKind::Error(value) => {
                TypedComp::new(comp.sig().clone(), TypedCompKind::Error(self.value(value)?))
            }
            TypedCompKind::FloatBuiltin(operation, value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::FloatBuiltin(*operation, self.fallback_value(value, context)?),
            ),
            TypedCompKind::Neg(lane, value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Neg(*lane, self.fallback_value(value, context)?),
            ),
            TypedCompKind::UnboxedProject(value, field) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::UnboxedProject(self.fallback_value(value, context)?, *field),
            ),
            TypedCompKind::Do { .. } | TypedCompKind::Handle { .. } | TypedCompKind::Mask(..) => {
                return None;
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::StrBuiltin {
                    op: *op,
                    instantiation: instantiation.clone(),
                    args: args
                        .iter()
                        .map(|argument| self.fallback_value(argument, context))
                        .collect::<Option<_>>()?,
                },
            ),
            TypedCompKind::Dup(value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Dup(self.fallback_value(value, context)?),
            ),
            TypedCompKind::Drop(value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Drop(self.fallback_value(value, context)?),
            ),
            TypedCompKind::WithReuse { token, freed, body } => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::WithReuse {
                    token: token.clone(),
                    freed: self.fallback_value(freed, context)?,
                    body: Box::new(self.go(body, context, false)?),
                },
            ),
            TypedCompKind::Reuse(token, value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Reuse(token.clone(), self.fallback_value(value, context)?),
            ),
            TypedCompKind::InitAt(cell, constructor) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::InitAt(
                    self.fallback_value(cell, context)?,
                    self.fallback_value(constructor, context)?,
                ),
            ),
            TypedCompKind::RefNew(value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::RefNew(self.fallback_value(value, context)?),
            ),
            TypedCompKind::RefGet(value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::RefGet(self.fallback_value(value, context)?),
            ),
            TypedCompKind::RefSet(cell, value) => TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::RefSet(
                    self.fallback_value(cell, context)?,
                    self.fallback_value(value, context)?,
                ),
            ),
        })
    }
}

/// Bounce only tail hops that cannot already use the native same-arity fast path.
pub(super) fn trampolinize(
    functions: &[TypedCoreFn],
    fresh: &mut Fresh,
) -> Option<Vec<TypedCoreFn>> {
    let eff = eff_functions(functions);
    let arity: BTreeMap<Sym, usize> = functions
        .iter()
        .map(|function| (function.name(), function.params().len()))
        .collect();
    functions
        .iter()
        .map(|function| {
            let context = eff_tail(function.body(), &eff);
            let mut rewrite = Tr {
                eff: &eff,
                arity: &arity,
                fresh,
                current_arity: function.params().len(),
            };
            let body = rewrite.go(function.body(), context, true)?;
            Some(TypedCoreFn::new(
                function.name(),
                function.params().to_vec(),
                body,
                function.sig().clone(),
                function.dict_arity(),
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::core::cbpv::{Comp, CorePat, Value};
    use crate::core::typed::verify::{verify, VerifyEnv};
    use crate::core::typed::{EffectLowered, TypedCore};
    use crate::types::Type;

    use super::*;

    fn int() -> CoreType {
        CoreType::Source(Type::Int)
    }

    fn int_value(value: i64) -> TypedValue {
        TypedValue::new(int(), TypedValueKind::Int(value))
    }

    fn eff_signature(parameters: Vec<CoreType>) -> CoreFnSig {
        CoreFnSig::new(Vec::new(), parameters, pure(abi::eff(EffRow::Empty)))
    }

    fn eff_signature_at(parameters: Vec<CoreType>, row: EffRow) -> CoreFnSig {
        CoreFnSig::new(
            Vec::new(),
            parameters,
            CompSig::new(abi::eff(row.clone()), row),
        )
    }

    #[test]
    fn cross_arity_and_closure_hops_bounce_but_native_tail_calls_do_not() {
        let finish_body = abi::epure(abi::lowered_repr(int_value(7), abi::word()), EffRow::Empty);
        let finish = TypedCoreFn::new(
            Sym::from("finish"),
            Vec::new(),
            finish_body,
            eff_signature(Vec::new()),
            0,
        );
        let x = TypedBinder::new(Sym::from("x"), int());
        let hop_body = TypedComp::new(
            pure(abi::eff(EffRow::Empty)),
            TypedCompKind::Call {
                callee: Sym::from("finish"),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let hop = TypedCoreFn::new(
            Sym::from("hop"),
            vec![x.clone()],
            hop_body,
            eff_signature(vec![int()]),
            0,
        );
        let loop_body = TypedComp::new(
            pure(abi::eff(EffRow::Empty)),
            TypedCompKind::Call {
                callee: Sym::from("loop"),
                instantiation: Vec::new(),
                args: vec![var(&x)],
            },
        );
        let native_loop = TypedCoreFn::new(
            Sym::from("loop"),
            vec![x],
            loop_body,
            eff_signature(vec![int()]),
            0,
        );

        let closure_signature = eff_signature(Vec::new());
        let closure_ty = CoreType::Thunk(Box::new(pure(CoreType::Function(Box::new(
            closure_signature,
        )))));
        let closure = TypedBinder::new(Sym::from("closure"), closure_ty);
        let forced = TypedComp::new(
            match closure.ty() {
                CoreType::Thunk(signature) => (**signature).clone(),
                _ => unreachable!(),
            },
            TypedCompKind::Force(var(&closure)),
        );
        let apply_body = TypedComp::new(
            pure(abi::eff(EffRow::Empty)),
            TypedCompKind::App {
                callee: Box::new(forced),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let apply = TypedCoreFn::new(
            Sym::from("apply"),
            vec![closure.clone()],
            apply_body,
            CoreFnSig::new(
                Vec::new(),
                vec![closure.ty().clone()],
                pure(abi::eff(EffRow::Empty)),
            ),
            0,
        );

        let mut fresh = Fresh::new();
        let mut rewritten = trampolinize(&[finish, hop, native_loop, apply], &mut fresh)
            .expect("the typed trampoline rewrites every function");
        rewritten.push(prism_drive_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(rewritten);
        assert_eq!(verify(&typed, &env), Ok(()));
        let erased = typed.erase();

        assert!(matches!(
            erased.fns[1].body,
            Comp::Return(Value::Ctor(name, BOUNCE_TAG, _)) if name.as_str() == EBOUNCE
        ));
        assert!(matches!(
            erased.fns[2].body,
            Comp::Call(name, _) if name.as_str() == "loop"
        ));
        assert!(matches!(
            erased.fns[3].body,
            Comp::Return(Value::Ctor(name, BOUNCE_TAG, _)) if name.as_str() == EBOUNCE
        ));
    }

    #[test]
    fn a_nonempty_residual_row_survives_the_bounce_witness() {
        let row = EffRow::singleton("IO");
        let finish = TypedCoreFn::new(
            Sym::from("finish_io"),
            Vec::new(),
            abi::epure(abi::lowered_repr(int_value(7), abi::word()), row.clone()),
            eff_signature_at(Vec::new(), row.clone()),
            0,
        );
        let x = TypedBinder::new(Sym::from("x"), int());
        let hop = TypedCoreFn::new(
            Sym::from("hop_io"),
            vec![x.clone()],
            TypedComp::new(
                CompSig::new(abi::eff(row.clone()), row.clone()),
                TypedCompKind::Call {
                    callee: finish.name(),
                    instantiation: Vec::new(),
                    args: Vec::new(),
                },
            ),
            eff_signature_at(vec![x.ty().clone()], row.clone()),
            0,
        );
        let mut rewritten =
            trampolinize(&[finish, hop], &mut Fresh::new()).expect("the residual-row hop rewrites");
        let TypedCompKind::Return(TypedValue {
            kind:
                TypedValueKind::Ctor {
                    name,
                    instantiation,
                    ..
                },
            ..
        }) = rewritten[1].body().kind()
        else {
            panic!("the cross-arity tail must be an EBounce return")
        };
        assert_eq!(name.as_str(), EBOUNCE);
        assert_eq!(instantiation, &abi::row_instantiation(row));

        rewritten.push(prism_drive_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        assert_eq!(
            verify(&TypedCore::<EffectLowered>::new(rewritten), &env),
            Ok(())
        );
    }

    #[test]
    fn eff_cases_drive_first_and_the_runtime_loop_erases_exactly() {
        let current = TypedBinder::new(Sym::from("current"), abi::eff(EffRow::Empty));
        let value = TypedBinder::new(Sym::from("value"), abi::word());
        let pure_arm = (
            abi::epure_pattern(EffRow::Empty, value.clone()),
            abi::epure(var(&value), EffRow::Empty),
        );
        let case = TypedComp::new(
            pure(abi::eff(EffRow::Empty)),
            TypedCompKind::Case(
                var(&current),
                vec![
                    pure_arm,
                    (
                        TypedPattern::Wild,
                        abi::epure(abi::lowered_repr(int_value(0), abi::word()), EffRow::Empty),
                    ),
                ],
            ),
        );
        let inspect = TypedCoreFn::new(
            Sym::from("inspect"),
            vec![current.clone()],
            case,
            eff_signature(vec![current.ty().clone()]),
            0,
        );
        let mut fresh = Fresh::new();
        let mut rewritten = trampolinize(&[inspect], &mut fresh).expect("case rewrites");
        rewritten.push(prism_drive_fn());
        let mut env = VerifyEnv::new();
        abi::insert(&mut env);
        let typed = TypedCore::<EffectLowered>::new(rewritten);
        assert_eq!(verify(&typed, &env), Ok(()));
        let erased = typed.erase();
        let driven = Sym::from(names::lowered("drv", 0));
        assert!(matches!(
            &erased.fns[0].body,
            Comp::Bind(call, binder, body)
                if matches!(call.as_ref(), Comp::Call(name, _) if name.as_str() == DRIVE)
                    && *binder == driven
                    && matches!(body.as_ref(), Comp::Case(Value::Var(name), _) if *name == driven)
        ));

        let expected_drive = Comp::Case(
            Value::Var(Sym::from(names::RET)),
            vec![
                (
                    CorePat::Ctor(Sym::from(EBOUNCE), vec![Some(Sym::from(names::EBIND_FN))]),
                    Comp::Bind(
                        Box::new(Comp::App(
                            Box::new(Comp::Force(Value::Var(Sym::from(names::EBIND_FN)))),
                            Vec::new(),
                        )),
                        Sym::from(names::COMPOSE),
                        Box::new(Comp::Call(
                            Sym::from(DRIVE),
                            vec![Value::Var(Sym::from(names::COMPOSE))],
                        )),
                    ),
                ),
                (
                    CorePat::Wild,
                    Comp::Return(Value::Var(Sym::from(names::RET))),
                ),
            ],
        );
        assert_eq!(erased.fns[1].body, expected_drive);
    }

    #[test]
    fn an_eff_case_does_not_rewrite_its_stored_scrutinee() {
        let current = TypedBinder::new(Sym::from("current"), abi::eff(EffRow::Empty));
        let value = TypedBinder::new(Sym::from("value"), abi::word());
        let arms = || {
            vec![
                (
                    abi::epure_pattern(EffRow::Empty, value.clone()),
                    abi::epure(var(&value), EffRow::Empty),
                ),
                (
                    TypedPattern::Wild,
                    abi::epure(abi::lowered_repr(int_value(0), abi::word()), EffRow::Empty),
                ),
            ]
        };
        let stored_case = TypedComp::new(
            pure(abi::eff(EffRow::Empty)),
            TypedCompKind::Case(var(&current), arms()),
        );
        let bounced = bounce(stored_case).expect("the stored case returns Eff");
        let TypedCompKind::Return(scrutinee) = bounced.kind() else {
            unreachable!("bounce returns its EBounce cell")
        };
        let outer_case = TypedComp::new(
            pure(abi::eff(EffRow::Empty)),
            TypedCompKind::Case(scrutinee.clone(), arms()),
        );
        let inspect = TypedCoreFn::new(
            Sym::from("inspect_stored"),
            vec![current.clone()],
            outer_case,
            eff_signature(vec![current.ty().clone()]),
            0,
        );

        let mut fresh = Fresh::new();
        let rewritten = trampolinize(&[inspect], &mut fresh).expect("case rewrites");
        assert_eq!(fresh.bump(), 1, "only the outer drive binder is minted");
        assert!(matches!(
            rewritten[0].body().kind(),
            TypedCompKind::Bind(call, _, _)
                if matches!(
                    call.kind(),
                    TypedCompKind::Call { callee, args, .. }
                        if callee.as_str() == DRIVE && args == std::slice::from_ref(scrutinee)
                )
        ));
    }

    #[test]
    fn source_effect_nodes_cannot_reach_the_runtime_rewrite() {
        let body = TypedComp::new(
            pure(int()),
            TypedCompKind::Mask(
                Vec::new(),
                Box::new(TypedComp::new(
                    pure(int()),
                    TypedCompKind::Return(int_value(0)),
                )),
            ),
        );
        let function = TypedCoreFn::new(
            Sym::from("masked"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(int())),
            0,
        );

        assert!(trampolinize(&[function], &mut Fresh::new()).is_none());
    }
}
