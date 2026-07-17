//! Phase-private typed signatures for the reified effect runtime.

use crate::core::builtins::Builtin;
use crate::core::effect_abi::{
    BOUNCE_TAG, EBIND, EBOUNCE, EOP, EPURE, ERESUME, OP_TAG, PURE_TAG, QAPPLY, RESUME_TAG, TQCONS,
    TQCONS_TAG, TQNIL, TQNIL_TAG,
};
use crate::names;
use crate::sym::Sym;
use crate::types::ty::EffRow;
use crate::types::Type;

use super::super::verify::{lowered_representation_conversion, ConstructorSig, VerifyEnv};
use super::super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType, TypedBinder,
    TypedComp, TypedCompKind, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind,
};

const ABI_ROW: &str = "rho_eff@";

pub(super) fn is_monadic_tail_constructor(name: Sym) -> bool {
    matches!(name.as_str(), EPURE | EOP)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LoweredReprKind {
    General,
    QueuePack,
    QueueUnpack,
}

/// Construction authority for a phase-private lowered representation node.
///
/// The type is public because typed transformations must preserve the token,
/// but its field is private so only this ABI module can create one. Queue words
/// use distinct evidence: they cross the generic `EPure`/`ebind` payload slot,
/// but are not part of the ordinary source-value representation relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredReprProof(LoweredReprKind);

impl LoweredReprProof {
    pub(in crate::core::typed) fn validates(&self, actual: &CoreType, expected: &CoreType) -> bool {
        match self.0 {
            LoweredReprKind::General => lowered_representation_conversion(actual, expected),
            LoweredReprKind::QueuePack => matches!(
                (actual, expected),
                (
                    CoreType::Lowered(LoweredType::Queue(_)),
                    CoreType::Lowered(LoweredType::Word)
                )
            ),
            LoweredReprKind::QueueUnpack => matches!(
                (actual, expected),
                (
                    CoreType::Lowered(LoweredType::Word),
                    CoreType::Lowered(LoweredType::Queue(_))
                )
            ),
        }
    }
}

const fn lowered(kind: LoweredType) -> CoreType {
    CoreType::Lowered(kind)
}

pub(super) const fn word() -> CoreType {
    lowered(LoweredType::Word)
}

pub(super) const fn eff(row: EffRow) -> CoreType {
    lowered(LoweredType::Eff(row))
}

pub(super) const fn queue(row: EffRow) -> CoreType {
    lowered(LoweredType::Queue(row))
}

const fn queue_view(row: EffRow) -> CoreType {
    lowered(LoweredType::QueueView(row))
}

const fn source(ty: Type) -> CoreType {
    CoreType::Source(ty)
}

const fn pure(result: CoreType) -> CompSig {
    CompSig::new(result, EffRow::Empty)
}

pub(super) fn kont(row: EffRow) -> CoreType {
    let result = eff(row.clone());
    CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![word()],
            CompSig::new(result, row),
        ))),
        EffRow::Empty,
    )))
}

pub(super) fn bounce(row: EffRow) -> CoreType {
    let result = eff(row.clone());
    CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            Vec::new(),
            CompSig::new(result, row),
        ))),
        EffRow::Empty,
    )))
}

fn abi_row() -> Sym {
    Sym::from(ABI_ROW)
}

pub(super) fn row_instantiation(row: EffRow) -> Vec<CoreInstantiation> {
    vec![CoreInstantiation::Row(row)]
}

pub(super) fn insert(env: &mut VerifyEnv) {
    let row = abi_row();
    let residual = EffRow::Var(row);
    env.insert_constructor(
        Sym::from(EPURE),
        ConstructorSig::new(
            vec![CoreQuantifier::Row(row)],
            PURE_TAG,
            vec![word()],
            eff(residual.clone()),
        ),
    );
    env.insert_constructor(
        Sym::from(EOP),
        ConstructorSig::new(
            vec![CoreQuantifier::Row(row)],
            OP_TAG,
            vec![
                source(Type::Int),
                source(Type::Int),
                word(),
                queue(residual.clone()),
            ],
            eff(residual.clone()),
        ),
    );
    env.insert_constructor(
        Sym::from(ERESUME),
        ConstructorSig::new(
            vec![CoreQuantifier::Row(row)],
            RESUME_TAG,
            vec![queue(residual.clone()), word()],
            eff(residual.clone()),
        ),
    );
    env.insert_constructor(
        Sym::from(EBOUNCE),
        ConstructorSig::new(
            vec![CoreQuantifier::Row(row)],
            BOUNCE_TAG,
            vec![bounce(residual.clone())],
            eff(residual.clone()),
        ),
    );
    env.insert_constructor(
        Sym::from(TQNIL),
        ConstructorSig::new(
            vec![CoreQuantifier::Row(row)],
            TQNIL_TAG,
            Vec::new(),
            queue_view(residual.clone()),
        ),
    );
    env.insert_constructor(
        Sym::from(TQCONS),
        ConstructorSig::new(
            vec![CoreQuantifier::Row(row)],
            TQCONS_TAG,
            vec![kont(residual.clone()), queue(residual.clone())],
            queue_view(residual.clone()),
        ),
    );

    env.insert_builtin_override(
        Builtin::TaqSnoc,
        CoreFnSig::new(
            vec![CoreQuantifier::Row(row)],
            vec![queue(residual.clone()), kont(residual.clone())],
            pure(queue(residual.clone())),
        ),
    );
    env.insert_builtin_override(
        Builtin::TaqConcat,
        CoreFnSig::new(
            vec![CoreQuantifier::Row(row)],
            vec![queue(residual.clone()), queue(residual.clone())],
            pure(queue(residual.clone())),
        ),
    );
    env.insert_builtin_override(
        Builtin::TaqUncons,
        CoreFnSig::new(
            vec![CoreQuantifier::Row(row)],
            vec![queue(residual.clone())],
            pure(queue_view(residual)),
        ),
    );
}

pub(super) fn binder(name: &str, ty: CoreType) -> TypedBinder {
    TypedBinder::new(Sym::from(name), ty)
}

pub(super) fn var(name: &str, ty: CoreType) -> TypedValue {
    TypedValue::new(
        ty,
        TypedValueKind::Var {
            name: Sym::from(name),
            instantiation: Vec::new(),
        },
    )
}

#[cfg(test)]
const fn int(value: i64) -> TypedValue {
    TypedValue::new(source(Type::Int), TypedValueKind::Int(value))
}

pub(super) fn lowered_repr(value: TypedValue, ty: CoreType) -> TypedValue {
    TypedValue::new(
        ty,
        TypedValueKind::LoweredRepr {
            value: Box::new(value),
            proof: LoweredReprProof(LoweredReprKind::General),
        },
    )
}

/// Retype one runtime word without changing its erased representation.
///
/// The two conversion checks are the verifier's canonical ABI rule. Keeping
/// them here makes a failed conversion an ordinary lowering decline rather
/// than constructing a node that can only fail independent verification.
pub(super) fn try_word_bridge(value: TypedValue, expected: CoreType) -> Option<TypedValue> {
    if value.ty() == &expected {
        return Some(value);
    }
    let word = word();
    if !lowered_representation_conversion(value.ty(), &word)
        || !lowered_representation_conversion(&word, &expected)
    {
        return None;
    }
    Some(lowered_repr(lowered_repr(value, word), expected))
}

pub(super) fn pack_queue_word(value: TypedValue) -> Option<TypedValue> {
    if !matches!(value.ty(), CoreType::Lowered(LoweredType::Queue(_))) {
        return None;
    }
    Some(TypedValue::new(
        word(),
        TypedValueKind::LoweredRepr {
            value: Box::new(value),
            proof: LoweredReprProof(LoweredReprKind::QueuePack),
        },
    ))
}

pub(super) fn unpack_queue_word(value: TypedValue, row: EffRow) -> Option<TypedValue> {
    if value.ty() != &word() {
        return None;
    }
    Some(TypedValue::new(
        queue(row),
        TypedValueKind::LoweredRepr {
            value: Box::new(value),
            proof: LoweredReprProof(LoweredReprKind::QueueUnpack),
        },
    ))
}

pub(super) fn empty_queue(row: EffRow) -> TypedValue {
    lowered_repr(
        TypedValue::new(source(Type::Unit), TypedValueKind::Unit),
        queue(row),
    )
}

fn ctor(
    name: &str,
    tag: usize,
    instantiation: Vec<CoreInstantiation>,
    fields: Vec<TypedValue>,
    ty: CoreType,
) -> TypedValue {
    TypedValue::new(
        ty,
        TypedValueKind::Ctor {
            name: Sym::from(name),
            tag,
            instantiation,
            fields,
        },
    )
}

pub(super) fn epure(value: TypedValue, row: EffRow) -> TypedComp {
    let result = eff(row.clone());
    TypedComp::new(
        pure(result.clone()),
        TypedCompKind::Return(ctor(
            EPURE,
            PURE_TAG,
            row_instantiation(row),
            vec![value],
            result,
        )),
    )
}

pub(super) fn eop(
    id: TypedValue,
    skip: TypedValue,
    arg: TypedValue,
    q: TypedValue,
    row: EffRow,
) -> TypedComp {
    let result = eff(row.clone());
    TypedComp::new(
        pure(result.clone()),
        TypedCompKind::Return(ctor(
            EOP,
            OP_TAG,
            row_instantiation(row),
            vec![id, skip, arg, q],
            result,
        )),
    )
}

pub(super) fn eresume(queue: TypedValue, value: TypedValue, row: EffRow) -> TypedComp {
    let result = eff(row.clone());
    TypedComp::new(
        pure(result.clone()),
        TypedCompKind::Return(ctor(
            ERESUME,
            RESUME_TAG,
            row_instantiation(row),
            vec![queue, value],
            result,
        )),
    )
}

pub(super) fn qapply(queue: TypedValue, value: TypedValue, row: EffRow) -> TypedComp {
    TypedComp::new(
        CompSig::new(eff(row.clone()), row.clone()),
        TypedCompKind::Call {
            callee: Sym::from(QAPPLY),
            instantiation: row_instantiation(row),
            args: vec![queue, value],
        },
    )
}

fn force(value: TypedValue) -> TypedComp {
    let CoreType::Thunk(signature) = value.ty().clone() else {
        unreachable!("ABI fixture only forces typed thunks")
    };
    TypedComp::new(*signature, TypedCompKind::Force(value))
}

fn apply(callee: TypedComp, args: Vec<TypedValue>, result: CoreType, row: EffRow) -> TypedComp {
    TypedComp::new(
        CompSig::new(result, row),
        TypedCompKind::App {
            callee: Box::new(callee),
            instantiation: Vec::new(),
            args,
        },
    )
}

fn ctor_pattern(
    name: &str,
    instantiation: Vec<CoreInstantiation>,
    fields: Vec<TypedBinder>,
) -> TypedPattern {
    TypedPattern::Ctor {
        name: Sym::from(name),
        instantiation,
        fields: fields.into_iter().map(Some).collect(),
    }
}

pub(super) fn epure_pattern(row: EffRow, value: TypedBinder) -> TypedPattern {
    ctor_pattern(EPURE, row_instantiation(row), vec![value])
}

pub(super) fn eop_pattern(
    row: EffRow,
    id: TypedBinder,
    skip: TypedBinder,
    argument: TypedBinder,
    continuation: TypedBinder,
) -> TypedPattern {
    ctor_pattern(
        EOP,
        row_instantiation(row),
        vec![id, skip, argument, continuation],
    )
}

pub(super) fn eresume_pattern(row: EffRow, queue: TypedBinder, value: TypedBinder) -> TypedPattern {
    ctor_pattern(ERESUME, row_instantiation(row), vec![queue, value])
}

pub(super) fn ebind_fn() -> TypedCoreFn {
    let row = abi_row();
    let residual = EffRow::Var(row);
    let r = binder(names::RET, eff(residual.clone()));
    let f = binder(names::EBIND_FN, kont(residual.clone()));

    let x = binder(names::COMPOSE, word());
    let pure_arm = (
        ctor_pattern(EPURE, row_instantiation(residual.clone()), vec![x]),
        apply(
            force(var(names::EBIND_FN, f.ty().clone())),
            vec![var(names::COMPOSE, word())],
            eff(residual.clone()),
            residual.clone(),
        ),
    );

    let id = binder(names::OP_ID, source(Type::Int));
    let skip = binder(names::OP_SKIP, source(Type::Int));
    let arg = binder(names::OP_ARG, word());
    let q = binder(names::CONT, queue(residual.clone()));
    let q2 = binder(names::RESUME_KONT, queue(residual.clone()));
    let snoc = TypedComp::new(
        pure(queue(residual.clone())),
        TypedCompKind::StrBuiltin {
            op: Builtin::TaqSnoc,
            instantiation: row_instantiation(residual.clone()),
            args: vec![
                var(names::CONT, queue(residual.clone())),
                var(names::EBIND_FN, f.ty().clone()),
            ],
        },
    );
    let rebuilt = eop(
        var(names::OP_ID, source(Type::Int)),
        var(names::OP_SKIP, source(Type::Int)),
        var(names::OP_ARG, word()),
        var(names::RESUME_KONT, queue(residual.clone())),
        residual.clone(),
    );
    let op_arm = (
        ctor_pattern(
            EOP,
            row_instantiation(residual.clone()),
            vec![id, skip, arg, q],
        ),
        TypedComp::new(
            pure(eff(residual.clone())),
            TypedCompKind::Bind(Box::new(snoc), q2, Box::new(rebuilt)),
        ),
    );

    let body = TypedComp::new(
        CompSig::new(eff(residual.clone()), residual.clone()),
        TypedCompKind::Case(
            var(names::RET, eff(residual.clone())),
            vec![pure_arm, op_arm],
        ),
    );
    TypedCoreFn::new(
        Sym::from(EBIND),
        vec![r, f.clone()],
        body,
        CoreFnSig::new(
            vec![CoreQuantifier::Row(row)],
            vec![eff(residual.clone()), f.ty().clone()],
            CompSig::new(eff(residual.clone()), residual),
        ),
        0,
    )
}

pub(super) fn qapply_fn() -> TypedCoreFn {
    let row = abi_row();
    let residual = EffRow::Var(row);
    let q = binder(names::EBIND_FN, queue(residual.clone()));
    let v = binder(names::RET, word());
    let view = binder(names::ERR, queue_view(residual.clone()));

    let nil_arm = (
        ctor_pattern(TQNIL, row_instantiation(residual.clone()), Vec::new()),
        epure(var(names::RET, word()), residual.clone()),
    );

    let g = binder(names::CONT, kont(residual.clone()));
    let rest = binder(names::RESUME_KONT, queue(residual.clone()));
    let applied = binder(names::STATE, eff(residual.clone()));
    let w = binder(names::COMPOSE, word());
    let pure_applied = (
        ctor_pattern(EPURE, row_instantiation(residual.clone()), vec![w]),
        TypedComp::new(
            CompSig::new(eff(residual.clone()), residual.clone()),
            TypedCompKind::Call {
                callee: Sym::from(QAPPLY),
                instantiation: row_instantiation(residual.clone()),
                args: vec![
                    var(names::RESUME_KONT, queue(residual.clone())),
                    var(names::COMPOSE, word()),
                ],
            },
        ),
    );

    let id = binder(names::OP_ID, source(Type::Int));
    let skip = binder(names::OP_SKIP, source(Type::Int));
    let arg = binder(names::OP_ARG, word());
    let q2 = binder(names::FWD_SKIP, queue(residual.clone()));
    let joined = binder(names::RESUME_VAL, queue(residual.clone()));
    let concat = TypedComp::new(
        pure(queue(residual.clone())),
        TypedCompKind::StrBuiltin {
            op: Builtin::TaqConcat,
            instantiation: row_instantiation(residual.clone()),
            args: vec![
                var(names::FWD_SKIP, queue(residual.clone())),
                var(names::RESUME_KONT, queue(residual.clone())),
            ],
        },
    );
    let forwarded = eop(
        var(names::OP_ID, source(Type::Int)),
        var(names::OP_SKIP, source(Type::Int)),
        var(names::OP_ARG, word()),
        var(names::RESUME_VAL, queue(residual.clone())),
        residual.clone(),
    );
    let op_applied = (
        ctor_pattern(
            EOP,
            row_instantiation(residual.clone()),
            vec![id, skip, arg, q2],
        ),
        TypedComp::new(
            pure(eff(residual.clone())),
            TypedCompKind::Bind(Box::new(concat), joined, Box::new(forwarded)),
        ),
    );

    let applied_case = TypedComp::new(
        CompSig::new(eff(residual.clone()), residual.clone()),
        TypedCompKind::Case(
            var(names::STATE, eff(residual.clone())),
            vec![pure_applied, op_applied],
        ),
    );
    let run_head = apply(
        force(var(names::CONT, g.ty().clone())),
        vec![var(names::RET, word())],
        eff(residual.clone()),
        residual.clone(),
    );
    let cons_arm = (
        ctor_pattern(TQCONS, row_instantiation(residual.clone()), vec![g, rest]),
        TypedComp::new(
            CompSig::new(eff(residual.clone()), residual.clone()),
            TypedCompKind::Bind(Box::new(run_head), applied, Box::new(applied_case)),
        ),
    );

    let uncons = TypedComp::new(
        pure(queue_view(residual.clone())),
        TypedCompKind::StrBuiltin {
            op: Builtin::TaqUncons,
            instantiation: row_instantiation(residual.clone()),
            args: vec![var(names::EBIND_FN, queue(residual.clone()))],
        },
    );
    let cases = TypedComp::new(
        CompSig::new(eff(residual.clone()), residual.clone()),
        TypedCompKind::Case(
            var(names::ERR, queue_view(residual.clone())),
            vec![nil_arm, cons_arm],
        ),
    );
    let body = TypedComp::new(
        CompSig::new(eff(residual.clone()), residual.clone()),
        TypedCompKind::Bind(Box::new(uncons), view, Box::new(cases)),
    );
    TypedCoreFn::new(
        Sym::from(QAPPLY),
        vec![q, v],
        body,
        CoreFnSig::new(
            vec![CoreQuantifier::Row(row)],
            vec![queue(residual.clone()), word()],
            CompSig::new(eff(residual.clone()), residual),
        ),
        0,
    )
}

#[cfg(test)]
mod tests {
    use super::super::super::{EffectLowered, Elaborated, TypedCore};
    use super::*;
    use crate::core::typed::verify::verify;
    use crate::core::IoOp;

    fn thunk(body: TypedComp, parameter: TypedBinder) -> TypedValue {
        let signature =
            CoreFnSig::new(Vec::new(), vec![parameter.ty().clone()], body.sig().clone());
        let lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(signature))),
            TypedCompKind::Lam(vec![parameter], Box::new(body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(lambda)),
        )
    }

    fn heterogeneous_fixture() -> TypedCoreFn {
        // Operation 0 takes Int and resumes with Bool. Its continuation performs
        // operation 1 with that Bool; operation 1 resumes with String.
        let op2_result = binder("op2_result@", word());
        let string_result = lowered_repr(var("op2_result@", word()), source(Type::Str));
        let k2 = thunk(
            epure(lowered_repr(string_result, word()), EffRow::Empty),
            op2_result,
        );

        let op1_result = binder("op1_result@", word());
        let bool_result = lowered_repr(var("op1_result@", word()), source(Type::Bool));
        let q2 = binder("hetero_q2@", queue(EffRow::Empty));
        let snoc_k2 = TypedComp::new(
            pure(queue(EffRow::Empty)),
            TypedCompKind::StrBuiltin {
                op: Builtin::TaqSnoc,
                instantiation: row_instantiation(EffRow::Empty),
                args: vec![empty_queue(EffRow::Empty), k2],
            },
        );
        let op2 = eop(
            int(1),
            int(0),
            lowered_repr(bool_result, word()),
            var("hetero_q2@", queue(EffRow::Empty)),
            EffRow::Empty,
        );
        let k1_body = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Bind(Box::new(snoc_k2), q2, Box::new(op2)),
        );
        let k1 = thunk(k1_body, op1_result);

        let q1 = binder("hetero_q1@", queue(EffRow::Empty));
        let snoc_k1 = TypedComp::new(
            pure(queue(EffRow::Empty)),
            TypedCompKind::StrBuiltin {
                op: Builtin::TaqSnoc,
                instantiation: row_instantiation(EffRow::Empty),
                args: vec![empty_queue(EffRow::Empty), k1],
            },
        );
        let op1 = eop(
            int(0),
            int(0),
            lowered_repr(int(41), word()),
            var("hetero_q1@", queue(EffRow::Empty)),
            EffRow::Empty,
        );
        let body = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Bind(Box::new(snoc_k1), q1, Box::new(op1)),
        );
        TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(eff(EffRow::Empty))),
            0,
        )
    }

    fn io_bounce_thunk(io_row: &EffRow) -> TypedValue {
        let io_binder = binder("io_result@", source(Type::Unit));
        let print = TypedComp::new(
            CompSig::new(source(Type::Unit), io_row.clone()),
            TypedCompKind::Io(IoOp::PrintNl, Vec::new()),
        );
        let after_print = epure(
            lowered_repr(
                TypedValue::new(source(Type::Unit), TypedValueKind::Unit),
                word(),
            ),
            io_row.clone(),
        );
        let bounce_body = TypedComp::new(
            CompSig::new(eff(io_row.clone()), io_row.clone()),
            TypedCompKind::Bind(Box::new(print), io_binder, Box::new(after_print)),
        );
        let bounce_signature = CoreFnSig::new(Vec::new(), Vec::new(), bounce_body.sig().clone());
        let bounce_lambda = TypedComp::new(
            pure(CoreType::Function(Box::new(bounce_signature))),
            TypedCompKind::Lam(Vec::new(), Box::new(bounce_body)),
        );
        TypedValue::new(
            CoreType::Thunk(Box::new(bounce_lambda.sig().clone())),
            TypedValueKind::Thunk(Box::new(bounce_lambda)),
        )
    }

    fn remaining_constructor_fixtures() -> Vec<TypedCoreFn> {
        let resumed = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Return(ctor(
                ERESUME,
                RESUME_TAG,
                row_instantiation(EffRow::Empty),
                vec![empty_queue(EffRow::Empty), lowered_repr(int(7), word())],
                eff(EffRow::Empty),
            )),
        );
        let resume_fn = TypedCoreFn::new(
            Sym::from("resume_fixture@"),
            Vec::new(),
            resumed,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(eff(EffRow::Empty))),
            0,
        );

        let io_row = EffRow::singleton(names::IO_EFFECT);
        let bounced = TypedComp::new(
            pure(eff(io_row.clone())),
            TypedCompKind::Return(ctor(
                EBOUNCE,
                BOUNCE_TAG,
                row_instantiation(io_row.clone()),
                vec![io_bounce_thunk(&io_row)],
                eff(io_row.clone()),
            )),
        );
        let bounce_fn = TypedCoreFn::new(
            Sym::from("bounce_fixture@"),
            Vec::new(),
            bounced,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(eff(io_row))),
            0,
        );

        vec![resume_fn, bounce_fn]
    }

    fn row_confusion_fixture() -> TypedCoreFn {
        let io_row = EffRow::singleton(names::IO_EFFECT);
        let result = binder("confused_result@", word());
        let io_binder = binder("confused_io@", source(Type::Unit));
        let print = TypedComp::new(
            CompSig::new(source(Type::Unit), io_row.clone()),
            TypedCompKind::Io(IoOp::PrintNl, Vec::new()),
        );
        let after_print = epure(var("confused_result@", word()), io_row.clone());
        let kont_body = TypedComp::new(
            CompSig::new(eff(io_row.clone()), io_row.clone()),
            TypedCompKind::Bind(Box::new(print), io_binder, Box::new(after_print)),
        );
        let effectful = thunk(kont_body, result);

        let q = binder("confused_queue@", queue(io_row.clone()));
        let snoc = TypedComp::new(
            pure(queue(io_row.clone())),
            TypedCompKind::StrBuiltin {
                op: Builtin::TaqSnoc,
                instantiation: row_instantiation(io_row.clone()),
                args: vec![empty_queue(io_row.clone()), effectful],
            },
        );
        let wrongly_pure_apply = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Call {
                callee: Sym::from(QAPPLY),
                instantiation: row_instantiation(EffRow::Empty),
                args: vec![
                    var("confused_queue@", queue(io_row)),
                    lowered_repr(int(1), word()),
                ],
            },
        );
        let body = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Bind(Box::new(snoc), q, Box::new(wrongly_pure_apply)),
        );
        TypedCoreFn::new(
            Sym::from("row_confusion@"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), pure(eff(EffRow::Empty))),
            0,
        )
    }

    fn singleton<P>(body: TypedComp) -> TypedCore<P> {
        let signature = body.sig().clone();
        TypedCore::new(vec![TypedCoreFn::new(
            Sym::from("main"),
            Vec::new(),
            body,
            CoreFnSig::new(Vec::new(), Vec::new(), signature),
            0,
        )])
    }

    #[test]
    fn runtime_templates_verify_under_the_phase_private_abi() {
        let mut env = VerifyEnv::new();
        insert(&mut env);
        let core = TypedCore::<EffectLowered>::new(vec![ebind_fn(), qapply_fn()]);
        assert_eq!(verify(&core, &env), Ok(()));
    }

    #[test]
    fn runtime_templates_erase_to_the_canonical_abi_names() {
        let erased = TypedCore::<EffectLowered>::new(vec![ebind_fn(), qapply_fn()]).erase();
        assert_eq!(
            erased
                .fns
                .iter()
                .map(|function| function.name.as_str())
                .collect::<Vec<_>>(),
            vec![EBIND, QAPPLY]
        );
        crate::core::residual_effects(&erased).expect("runtime templates contain no raw effects");
    }

    #[test]
    fn late_simplification_sees_through_lowered_evidence_exactly() {
        let x = binder("lowered_copy@", word());
        let packed = lowered_repr(int(7), word());
        let head = TypedComp::new(pure(word()), TypedCompKind::Return(packed));
        let tail = TypedComp::new(
            pure(word()),
            TypedCompKind::Return(var("lowered_copy@", word())),
        );
        let body = TypedComp::new(
            pure(word()),
            TypedCompKind::Bind(Box::new(head), x, Box::new(tail)),
        );
        let typed = singleton::<EffectLowered>(body);
        let (actual, stats) = super::super::super::simplify::simplify(typed).expect("simplifies");
        assert_eq!(stats.ticks(), 2);
        assert_eq!(
            actual.erase().fns[0].body,
            crate::core::cbpv::Comp::Return(crate::core::cbpv::Value::Int(7))
        );
    }

    #[test]
    fn heterogeneous_two_operation_chain_verifies() {
        let mut env = VerifyEnv::new();
        insert(&mut env);
        let core =
            TypedCore::<EffectLowered>::new(vec![ebind_fn(), qapply_fn(), heterogeneous_fixture()]);
        assert_eq!(verify(&core, &env), Ok(()));
    }

    #[test]
    fn resume_and_effectful_bounce_signatures_verify() {
        let mut env = VerifyEnv::new();
        insert(&mut env);
        let core = TypedCore::<EffectLowered>::new(remaining_constructor_fixtures());
        assert_eq!(verify(&core, &env), Ok(()));
    }

    #[test]
    fn queue_ambient_row_cannot_be_forged_at_apply() {
        let mut env = VerifyEnv::new();
        insert(&mut env);
        let core = TypedCore::<EffectLowered>::new(vec![qapply_fn(), row_confusion_fixture()]);
        assert!(
            verify(&core, &env).is_err(),
            "an IO-bearing queue must not typecheck at qApply<Empty>"
        );
    }

    #[test]
    fn bounce_ambient_row_cannot_hide_direct_io() {
        let mut env = VerifyEnv::new();
        insert(&mut env);
        let io_row = EffRow::singleton(names::IO_EFFECT);
        let wrongly_pure = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Return(ctor(
                EBOUNCE,
                BOUNCE_TAG,
                row_instantiation(EffRow::Empty),
                vec![io_bounce_thunk(&io_row)],
                eff(EffRow::Empty),
            )),
        );
        assert!(
            verify(&singleton::<EffectLowered>(wrongly_pure), &env).is_err(),
            "an IO-bearing bounce must not typecheck as Eff(Empty)"
        );
    }

    #[test]
    fn lowered_representation_is_rejected_before_effect_lowering() {
        let body = TypedComp::new(
            pure(word()),
            TypedCompKind::Return(lowered_repr(int(1), word())),
        );
        let errors = verify(&singleton::<Elaborated>(body), &VerifyEnv::new()).unwrap_err();
        assert!(errors.iter().any(|error| {
            error
                .message()
                .contains("lowered representation evidence is not legal")
        }));
    }

    #[test]
    fn lowered_representation_rejects_unlisted_conversion() {
        let body = TypedComp::new(
            pure(eff(EffRow::Empty)),
            TypedCompKind::Return(lowered_repr(
                TypedValue::new(source(Type::Unit), TypedValueKind::Unit),
                eff(EffRow::Empty),
            )),
        );
        let errors = verify(&singleton::<EffectLowered>(body), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("illegal lowered representation")));
    }

    #[test]
    fn lowered_representation_rejects_unboxed_products() {
        let product_ty = source(Type::UnboxedTuple(vec![Type::Int, Type::Int]));
        let product = TypedValue::new(
            product_ty,
            TypedValueKind::UnboxedTuple(vec![int(1), int(2)]),
        );
        let body = TypedComp::new(
            pure(word()),
            TypedCompKind::Return(lowered_repr(product, word())),
        );
        let errors = verify(&singleton::<EffectLowered>(body), &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("illegal lowered representation")));
    }

    #[test]
    fn lowered_representation_cannot_discard_a_queue() {
        let queue_ty = queue(EffRow::Empty);
        let q = binder("queue_to_discard@", queue_ty.clone());
        let body = TypedComp::new(
            pure(source(Type::Unit)),
            TypedCompKind::Return(lowered_repr(
                var("queue_to_discard@", queue_ty.clone()),
                source(Type::Unit),
            )),
        );
        let core = TypedCore::<EffectLowered>::new(vec![TypedCoreFn::new(
            Sym::from("main"),
            vec![q],
            body,
            CoreFnSig::new(Vec::new(), vec![queue_ty], pure(source(Type::Unit))),
            0,
        )]);
        let errors = verify(&core, &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("illegal lowered representation")));
    }

    #[test]
    fn queue_word_roundtrip_requires_the_sealed_queue_evidence() {
        let queue_ty = queue(EffRow::Empty);
        let parameter = binder("queue_word@", queue_ty.clone());
        let generic_pack = lowered_repr(var("queue_word@", queue_ty.clone()), word());
        let generic_body = TypedComp::new(pure(word()), TypedCompKind::Return(generic_pack));
        let generic = TypedCore::<EffectLowered>::new(vec![TypedCoreFn::new(
            Sym::from("generic_queue_pack@"),
            vec![parameter.clone()],
            generic_body,
            CoreFnSig::new(Vec::new(), vec![queue_ty.clone()], pure(word())),
            0,
        )]);
        assert!(
            verify(&generic, &VerifyEnv::new()).is_err(),
            "the general source-word evidence must not pack a runtime queue"
        );

        let packed = pack_queue_word(var("queue_word@", queue_ty.clone())).expect("queue packs");
        let restored = unpack_queue_word(packed, EffRow::Empty).expect("queue unpacks");
        let body = TypedComp::new(pure(queue_ty.clone()), TypedCompKind::Return(restored));
        let typed = TypedCore::<EffectLowered>::new(vec![TypedCoreFn::new(
            Sym::from("queue_roundtrip@"),
            vec![parameter],
            body,
            CoreFnSig::new(Vec::new(), vec![queue_ty], pure(queue(EffRow::Empty))),
            0,
        )]);
        assert_eq!(verify(&typed, &VerifyEnv::new()), Ok(()));
        assert!(matches!(
            typed.erase().fns[0].body,
            crate::core::cbpv::Comp::Return(crate::core::cbpv::Value::Var(name))
                if name.as_str() == "queue_word@"
        ));
    }

    #[test]
    fn lowered_representation_never_packs_reuse_tokens() {
        let token_ty = CoreType::ReuseToken(Box::new(source(Type::Int)));
        let token = binder("token@", token_ty.clone());
        let body = TypedComp::new(
            pure(word()),
            TypedCompKind::Return(lowered_repr(var("token@", token_ty.clone()), word())),
        );
        let core = TypedCore::<EffectLowered>::new(vec![TypedCoreFn::new(
            Sym::from("main"),
            vec![token],
            body,
            CoreFnSig::new(Vec::new(), vec![token_ty], pure(word())),
            0,
        )]);
        let errors = verify(&core, &VerifyEnv::new()).unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message().contains("illegal lowered representation")));
    }

    #[test]
    fn word_bridge_is_checked_and_erases_to_the_original_value() {
        let actual = CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![source(Type::Int)],
            pure(source(Type::Int)),
        )));
        let expected = CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            vec![source(Type::Bool)],
            pure(source(Type::Bool)),
        )));
        let parameter = binder("bridge_source@", actual.clone());
        let bridge = try_word_bridge(var("bridge_source@", actual.clone()), expected.clone())
            .expect("both function witnesses have one runtime-word representation");
        let body = TypedComp::new(pure(expected.clone()), TypedCompKind::Return(bridge));
        let core = TypedCore::<EffectLowered>::new(vec![TypedCoreFn::new(
            Sym::from("main"),
            vec![parameter],
            body,
            CoreFnSig::new(Vec::new(), vec![actual], pure(expected)),
            0,
        )]);

        assert_eq!(verify(&core, &VerifyEnv::new()), Ok(()));
        assert_eq!(
            core.erase().fns[0].body,
            crate::core::cbpv::Comp::Return(crate::core::cbpv::Value::Var(Sym::from(
                "bridge_source@"
            )))
        );

        let product_ty = source(Type::UnboxedTuple(vec![Type::Int, Type::Int]));
        let product = TypedValue::new(
            product_ty,
            TypedValueKind::UnboxedTuple(vec![int(1), int(2)]),
        );
        assert!(try_word_bridge(product, source(Type::Str)).is_none());
    }
}
