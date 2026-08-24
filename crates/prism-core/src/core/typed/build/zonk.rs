//! Final substitution and zonking after witness constraints are solved.

use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreType, LoweredType, TypedBinder, TypedComp,
    TypedCompKind, TypedForward, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind,
};
use super::super::{CORE_GROW_STACK, CORE_MIN_STACK};
use super::env::{lower_value_type, source_type};
use super::solve::Solver;

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

    pub(super) fn final_fn_sig(&self, sig: &CoreFnSig) -> CoreFnSig {
        let params: Vec<_> = sig.params().iter().map(|ty| self.final_core(ty)).collect();
        let body = self.final_sig(sig.body());
        CoreFnSig::new(sig.quantifiers().to_vec(), params, body)
    }

    pub(super) fn final_type(&self, ty: &Type) -> Type {
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

    pub(super) fn final_row(&self, row: &EffRow) -> EffRow {
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

    pub(super) fn zonk_binder(&self, binder: &TypedBinder) -> TypedBinder {
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

    pub(super) fn zonk_comp(&self, comp: TypedComp) -> TypedComp {
        // Zonking recurses per typed node; grow segments inside the recursion,
        // same discipline as `Builder::comp`.
        stacker::maybe_grow(CORE_MIN_STACK, CORE_GROW_STACK, || {
            self.zonk_comp_inner(comp)
        })
    }

    fn zonk_comp_inner(&self, comp: TypedComp) -> TypedComp {
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
