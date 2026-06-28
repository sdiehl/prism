//! Free-monad runtime constructors and driver builders.

use super::{EBIND, EOP, EPURE, OP_TAG, PURE_TAG, QAPPLY, TQCONS, TQNIL};
use crate::core::builtins::Builtin;
use crate::core::cbpv::{Comp, CoreFn, CorePat, Value};
use crate::names;
use crate::sym::Sym;
use crate::types::{CtorInfo, Type};

pub(super) fn epure(v: Value) -> Comp {
    Comp::Return(Value::Ctor(EPURE.into(), PURE_TAG, vec![v]))
}

// fn ebind(r, f) =
//   case r {
//     EPure(x)        => force(f)(x),
//     EOp(id,sk,a,q)  => EOp(id, sk, a, taq_snoc(q, f)),
//   }
//
// The Freer monad: binding a continuation onto a suspended op is one O(1) queue
// snoc, with no spine re-walk and no nested closure tree. `CONT` binds the op's
// queue (its 4th field) and `f` (`EBIND_FN`) is the new Kleisli arrow.
//
// Closed top-level template: its binders (`names::OP_ID`/`OP_SKIP`/`OP_ARG`/
// `CONT`/`EBIND_FN`/`RESUME_KONT`) are fixed `@`-names, disjoint from program
// names. Templates refer to one another by `Call`, never by lexical nesting, so the
// fixed binders cannot capture across templates; do not emit one template's body
// inside another. Closedness is thus structural, not checked.
pub(super) fn ebind_fn() -> CoreFn {
    let pure_arm = (
        ctor_pat(EPURE, &[names::COMPOSE.into()]),
        Comp::App(
            Box::new(Comp::Force(Value::Var(names::EBIND_FN.into()))),
            vec![Value::Var(names::COMPOSE.into())],
        ),
    );
    let q = Sym::from(names::RESUME_KONT);
    let op_arm = (
        ctor_pat(
            EOP,
            &[
                names::OP_ID.into(),
                names::OP_SKIP.into(),
                names::OP_ARG.into(),
                names::CONT.into(),
            ],
        ),
        Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::TaqSnoc,
                vec![
                    Value::Var(names::CONT.into()),
                    Value::Var(names::EBIND_FN.into()),
                ],
            )),
            q,
            Box::new(Comp::Return(Value::Ctor(
                EOP.into(),
                OP_TAG,
                vec![
                    Value::Var(names::OP_ID.into()),
                    Value::Var(names::OP_SKIP.into()),
                    Value::Var(names::OP_ARG.into()),
                    Value::Var(q),
                ],
            ))),
        ),
    );
    CoreFn {
        name: EBIND.into(),
        params: vec![names::RET.into(), names::EBIND_FN.into()],
        body: Comp::Case(Value::Var(names::RET.into()), vec![pure_arm, op_arm]),
    }
}

// fn qApply(q, v) =
//   case taq_uncons(q) {
//     TQNil          => EPure(v),
//     TQCons(g, qr)  => case force(g)(v) {
//       EPure(w)         => qApply(qr, w),                       -- musttail
//       EOp(id,sk,a,q2)  => EOp(id, sk, a, taq_concat(q2, qr)),  -- splice, O(1)
//     }
//   }
//
// Runs an op's continuation queue on a resumption value. Every arrow is dequeued
// once and concat never re-walks a passed prefix, so driving an n-snoc queue is
// O(n). The `EPure` self-call is in tail position (codegen `musttail` => O(1)
// native stack). Closed template (fixed `@`-binders), like `ebind`.
pub(super) fn qapply_fn() -> CoreFn {
    let g = Sym::from(names::CONT); // head arrow
    let qr = Sym::from(names::RESUME_KONT); // tail queue
    let w = Sym::from(names::COMPOSE);
    let id = Sym::from(names::OP_ID);
    let sk = Sym::from(names::OP_SKIP);
    let a = Sym::from(names::OP_ARG);
    let q2 = Sym::from(names::FWD_SKIP);
    let spliced = Sym::from(names::RESUME_VAL);
    let v = Sym::from(names::RET);
    let qparam = Sym::from(names::EBIND_FN);
    let u = Sym::from(names::ERR);

    // case applied { EPure(w) => qApply(qr, w), EOp(..) => EOp(.., concat(q2, qr)) }
    let applied = Comp::App(Box::new(Comp::Force(Value::Var(g))), vec![Value::Var(v)]);
    let on_op = Comp::Bind(
        Box::new(Comp::StrBuiltin(
            Builtin::TaqConcat,
            vec![Value::Var(q2), Value::Var(qr)],
        )),
        spliced,
        Box::new(Comp::Return(Value::Ctor(
            EOP.into(),
            OP_TAG,
            vec![
                Value::Var(id),
                Value::Var(sk),
                Value::Var(a),
                Value::Var(spliced),
            ],
        ))),
    );
    let inner = Comp::Bind(
        Box::new(applied),
        Sym::from(names::STATE),
        Box::new(Comp::Case(
            Value::Var(Sym::from(names::STATE)),
            vec![
                (
                    ctor_pat(EPURE, &[w]),
                    Comp::Call(QAPPLY.into(), vec![Value::Var(qr), Value::Var(w)]),
                ),
                (ctor_pat(EOP, &[id, sk, a, q2]), on_op),
            ],
        )),
    );
    let cons_arm = (ctor_pat(TQCONS, &[g, qr]), inner);
    let nil_arm = (ctor_pat(TQNIL, &[]), epure(Value::Var(v)));
    CoreFn {
        name: QAPPLY.into(),
        params: vec![qparam, v],
        body: Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::TaqUncons,
                vec![Value::Var(qparam)],
            )),
            u,
            Box::new(Comp::Case(Value::Var(u), vec![nil_arm, cons_arm])),
        ),
    }
}

pub(super) fn ctor_pat(name: &str, vars: &[Sym]) -> CorePat {
    CorePat::Ctor(Sym::from(name), vars.iter().map(|v| Some(*v)).collect())
}

pub(super) fn synth_ctor(type_name: &str, tag: usize, n: usize) -> CtorInfo {
    CtorInfo {
        type_name: type_name.into(),
        params: vec![],
        args: vec![Type::Int; n],
        tag,
        fields: vec![],
    }
}
