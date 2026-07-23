//! Witness-preserving erasure of source `newtype` boxes.
//!
//! The legacy pass removes a constructor or an irrefutable constructor match.
//! Typed Core keeps that same rewrite explicit as [`TypedValueKind::NewtypeRepr`]:
//! the inner and outer value witnesses both survive until semantic erasure, and
//! the independent verifier checks the coercion against the declared constructor.

use std::collections::BTreeSet;

use crate::sym::Sym;
use crate::types::ty::EffRow;

use super::{
    instantiate_constructor, CompSig, TypedBinder, TypedComp, TypedCompKind, TypedCore,
    TypedCoreFn, TypedHandler, TypedPattern, TypedValue, TypedValueKind, VerifyEnv,
};

/// Rewrite counts for typed newtype erasure.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct NewtypeEraseStats {
    ticks: u64,
}

impl NewtypeEraseStats {
    /// Number of constructor boxes and irrefutable matches removed.
    pub(crate) const fn ticks(self) -> u64 {
        self.ticks
    }
}

/// Erase newtype representation nodes without erasing their type witnesses.
///
/// This is total on arbitrary typed trees. A marked constructor whose declared
/// shape is not the required one-field newtype shape is left untouched; the
/// independent verifier remains responsible for rejecting an invalid input.
pub(crate) fn erase_newtypes<P>(
    core: TypedCore<P>,
    constructors: &BTreeSet<Sym>,
    env: &VerifyEnv,
) -> (TypedCore<P>, NewtypeEraseStats) {
    if constructors.is_empty() {
        return (core, NewtypeEraseStats::default());
    }
    let mut pass = Erase {
        constructors,
        env,
        ticks: 0,
    };
    let functions = core
        .fns
        .into_iter()
        .map(|function| pass.function(function))
        .collect();
    (
        TypedCore::new(functions),
        NewtypeEraseStats { ticks: pass.ticks },
    )
}

struct Erase<'a> {
    constructors: &'a BTreeSet<Sym>,
    env: &'a VerifyEnv,
    ticks: u64,
}

impl Erase<'_> {
    fn function(&mut self, function: TypedCoreFn) -> TypedCoreFn {
        TypedCoreFn::new(
            function.name,
            function.params,
            self.comp(function.body),
            function.sig,
            function.dict_arity,
        )
    }

    fn value(&mut self, value: TypedValue) -> TypedValue {
        let ty = value.ty;
        let kind = match value.kind {
            TypedValueKind::Var {
                name,
                instantiation,
            } => TypedValueKind::Var {
                name,
                instantiation,
            },
            TypedValueKind::Int(value) => TypedValueKind::Int(value),
            TypedValueKind::I64(value) => TypedValueKind::I64(value),
            TypedValueKind::U64(value) => TypedValueKind::U64(value),
            TypedValueKind::Float(value) => TypedValueKind::Float(value),
            TypedValueKind::Bool(value) => TypedValueKind::Bool(value),
            TypedValueKind::Unit => TypedValueKind::Unit,
            TypedValueKind::Str(value) => TypedValueKind::Str(value),
            TypedValueKind::Reinterpret(value) => {
                TypedValueKind::Reinterpret(Box::new(self.value(*value)))
            }
            TypedValueKind::LoweredRepr { value, proof } => TypedValueKind::LoweredRepr {
                value: Box::new(self.value(*value)),
                proof,
            },
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value: Box::new(self.value(*value)),
            },
            TypedValueKind::Thunk(body) => TypedValueKind::Thunk(Box::new(self.comp(*body))),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => {
                let mut fields: Vec<_> =
                    fields.into_iter().map(|field| self.value(field)).collect();
                if self.constructors.contains(&name)
                    && fields.len() == 1
                    && self.newtype_shape(name, &instantiation).is_some()
                {
                    self.ticks += 1;
                    return TypedValue::new(
                        ty,
                        TypedValueKind::NewtypeRepr {
                            constructor: name,
                            instantiation,
                            value: Box::new(fields.pop().expect("one checked newtype field")),
                        },
                    );
                }
                TypedValueKind::Ctor {
                    name,
                    tag,
                    instantiation,
                    fields,
                }
            }
            TypedValueKind::Tuple(fields) => {
                TypedValueKind::Tuple(fields.into_iter().map(|field| self.value(field)).collect())
            }
            TypedValueKind::UnboxedTuple(fields) => TypedValueKind::UnboxedTuple(
                fields.into_iter().map(|field| self.value(field)).collect(),
            ),
            TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
                fields
                    .into_iter()
                    .map(|(name, field)| (name, self.value(field)))
                    .collect(),
            ),
        };
        TypedValue::new(ty, kind)
    }

    #[allow(clippy::too_many_lines)]
    fn comp(&mut self, comp: TypedComp) -> TypedComp {
        let sig = comp.sig;
        let kind = match comp.kind {
            TypedCompKind::Return(value) => TypedCompKind::Return(self.value(value)),
            TypedCompKind::Bind(first, binder, rest) => TypedCompKind::Bind(
                Box::new(self.comp(*first)),
                binder,
                Box::new(self.comp(*rest)),
            ),
            TypedCompKind::Force(value) => TypedCompKind::Force(self.value(value)),
            TypedCompKind::Lam(params, body) => {
                TypedCompKind::Lam(params, Box::new(self.comp(*body)))
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => TypedCompKind::App {
                callee: Box::new(self.comp(*callee)),
                instantiation,
                args: args.into_iter().map(|arg| self.value(arg)).collect(),
            },
            TypedCompKind::If(condition, yes, no) => TypedCompKind::If(
                self.value(condition),
                Box::new(self.comp(*yes)),
                Box::new(self.comp(*no)),
            ),
            TypedCompKind::Prim(op, lhs, rhs) => {
                TypedCompKind::Prim(op, self.value(lhs), self.value(rhs))
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => TypedCompKind::Call {
                callee,
                instantiation,
                args: args.into_iter().map(|arg| self.value(arg)).collect(),
            },
            TypedCompKind::Io(op, args) => {
                TypedCompKind::Io(op, args.into_iter().map(|arg| self.value(arg)).collect())
            }
            TypedCompKind::Error(value) => TypedCompKind::Error(self.value(value)),
            TypedCompKind::Case(scrutinee, arms) => {
                if let Some(rewritten) = self.newtype_case(&sig, scrutinee.clone(), &arms) {
                    return rewritten;
                }
                TypedCompKind::Case(
                    self.value(scrutinee),
                    arms.into_iter()
                        .map(|(pattern, body)| (pattern, self.comp(body)))
                        .collect(),
                )
            }
            TypedCompKind::FloatBuiltin(op, value) => {
                TypedCompKind::FloatBuiltin(op, self.value(value))
            }
            TypedCompKind::Neg(lane, value) => TypedCompKind::Neg(lane, self.value(value)),
            TypedCompKind::UnboxedProject(value, field) => {
                TypedCompKind::UnboxedProject(self.value(value), field)
            }
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => TypedCompKind::Do {
                operation,
                instantiation,
                args: args.into_iter().map(|arg| self.value(arg)).collect(),
            },
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => TypedCompKind::Handle {
                body: Box::new(self.comp(*body)),
                return_binder,
                return_body: return_body.map(|body| Box::new(self.comp(*body))),
                ops: TypedHandler {
                    arms: ops
                        .arms
                        .into_iter()
                        .map(|arm| super::TypedHandleOp {
                            name: arm.name,
                            instantiation: arm.instantiation,
                            params: arm.params,
                            resume: arm.resume,
                            body: self.comp(arm.body),
                        })
                        .collect(),
                    forwarded: ops.forwarded,
                },
            },
            TypedCompKind::Mask(effects, body) => {
                TypedCompKind::Mask(effects, Box::new(self.comp(*body)))
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args: args.into_iter().map(|arg| self.value(arg)).collect(),
            },
            TypedCompKind::Dup(value) => TypedCompKind::Dup(self.value(value)),
            TypedCompKind::Drop(value) => TypedCompKind::Drop(self.value(value)),
            TypedCompKind::WithReuse { token, freed, body } => TypedCompKind::WithReuse {
                token,
                freed: self.value(freed),
                body: Box::new(self.comp(*body)),
            },
            TypedCompKind::Reuse(token, value) => TypedCompKind::Reuse(token, self.value(value)),
            TypedCompKind::RefNew(value) => TypedCompKind::RefNew(self.value(value)),
            TypedCompKind::RefGet(value) => TypedCompKind::RefGet(self.value(value)),
            TypedCompKind::RefSet(cell, value) => {
                TypedCompKind::RefSet(self.value(cell), self.value(value))
            }
            TypedCompKind::InitAt(cell, ctor) => {
                TypedCompKind::InitAt(self.value(cell), self.value(ctor))
            }
        };
        TypedComp::new(sig, kind)
    }

    fn newtype_case(
        &mut self,
        sig: &CompSig,
        scrutinee: TypedValue,
        arms: &[(TypedPattern, TypedComp)],
    ) -> Option<TypedComp> {
        let [(
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            },
            body,
        )] = arms
        else {
            return None;
        };
        if !self.constructors.contains(name) || fields.len() != 1 {
            return None;
        }
        let field_ty = self.newtype_shape(*name, instantiation)?;
        let binder = fields[0]
            .clone()
            .unwrap_or_else(|| TypedBinder::new(Sym::from("_"), field_ty.clone()));
        let scrutinee = self.value(scrutinee);
        let projected = TypedValue::new(
            field_ty.clone(),
            TypedValueKind::NewtypeRepr {
                constructor: *name,
                instantiation: instantiation.clone(),
                value: Box::new(scrutinee),
            },
        );
        let first = TypedComp::new(
            CompSig::new(field_ty, EffRow::Empty),
            TypedCompKind::Return(projected),
        );
        self.ticks += 1;
        Some(TypedComp::new(
            sig.clone(),
            TypedCompKind::Bind(Box::new(first), binder, Box::new(self.comp(body.clone()))),
        ))
    }

    fn newtype_shape(
        &self,
        name: Sym,
        instantiation: &[super::CoreInstantiation],
    ) -> Option<super::CoreType> {
        let signature = self.env.constructor(name)?;
        let instantiated = instantiate_constructor(signature, instantiation).ok()?;
        let [field] = instantiated.fields.as_slice() else {
            return None;
        };
        Some(field.clone())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::core::pretty::pp_core;
    use crate::types::Type;

    use super::*;
    use crate::core::typed::{
        verify, ConstructorSig, CoreFnSig, CoreType, Elaborated, TypedCoreFn,
    };

    fn fixture(mark_newtype: bool) -> (TypedCore<Elaborated>, VerifyEnv, BTreeSet<Sym>) {
        let constructor = Sym::new("UserId");
        let newtype = CoreType::Source(Type::Con(Sym::new("Id"), Vec::new()));
        let field = CoreType::Source(Type::Int);
        let pure_int = CompSig::new(field.clone(), EffRow::Empty);
        let inner = TypedValue::new(field.clone(), TypedValueKind::Int(42));
        let wrapped = TypedValue::new(
            newtype.clone(),
            TypedValueKind::Ctor {
                name: constructor,
                tag: 0,
                instantiation: Vec::new(),
                fields: vec![inner],
            },
        );
        let binder = TypedBinder::new(Sym::new("id"), field.clone());
        let body = TypedComp::new(
            pure_int.clone(),
            TypedCompKind::Case(
                wrapped,
                vec![(
                    TypedPattern::Ctor {
                        name: constructor,
                        instantiation: Vec::new(),
                        fields: vec![Some(binder.clone())],
                    },
                    TypedComp::new(
                        pure_int.clone(),
                        TypedCompKind::Return(TypedValue::new(
                            field.clone(),
                            TypedValueKind::Var {
                                name: binder.name(),
                                instantiation: Vec::new(),
                            },
                        )),
                    ),
                )],
            ),
        );
        let typed = TypedCore::new(vec![TypedCoreFn::new(
            Sym::new("main"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure_int),
            0,
        )]);
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            constructor,
            ConstructorSig::new(Vec::new(), 0, vec![field], newtype),
        );
        if mark_newtype {
            env.mark_newtype_constructor(constructor);
        }
        (typed, env, BTreeSet::from([constructor]))
    }

    #[test]
    fn typed_erasure_removes_the_constructor_box_and_the_irrefutable_match() {
        let (typed, env, constructors) = fixture(true);
        verify(&typed, &env).expect("fixture is valid before newtype erasure");
        assert!(
            pp_core(&typed.clone().erase()).contains("UserId"),
            "the fixture must start with the newtype constructor present"
        );

        let (rewritten, stats) = erase_newtypes(typed, &constructors, &env);
        verify(&rewritten, &env).expect("newtype witnesses verify after the typed pass");
        let erased = rewritten.erase();

        // Both the constructor box and the irrefutable constructor match are
        // rewritten, and each `NewtypeRepr` erases transparently to its inner
        // witness, so no `UserId` constructor survives semantic erasure.
        assert_eq!(stats.ticks(), 2);
        assert!(
            !pp_core(&erased).contains("UserId"),
            "the erased result must carry no newtype constructor node"
        );
    }

    #[test]
    fn verifier_rejects_one_field_data_forged_as_newtype_evidence() {
        let (typed, env, constructors) = fixture(false);
        verify(&typed, &env).expect("ordinary one-field constructor is valid before coercion");

        let (forged, _) = erase_newtypes(typed, &constructors, &env);
        let violations = verify(&forged, &env)
            .expect_err("ordinary one-field data must not prove a newtype coercion");
        assert!(violations.iter().any(|violation| {
            violation
                .message()
                .contains("representation coercion names non-newtype constructor")
        }));
    }
}
