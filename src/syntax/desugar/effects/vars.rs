//! Local mutable `var` cells: each declaration becomes a private one-effect
//! get/put pair discharged by a parameter-passing handler right here.

use std::collections::BTreeSet;

use marginalia::Span;

use super::escape::escapes;
use super::{rw, Binding, Vars};
use crate::error::TypeError;
use crate::names::{self, CONT, RET, STATE, UNIT_ARG, VAL};
use crate::syntax::ast::{Core, EffOp, EffectDecl, Expr, Grade, HandlerArm, Ty, S};
use crate::syntax::desugar::{call, evar, lam1, sp, Cx};

pub(super) fn rw_var_decl(
    x: &str,
    init: &S<Expr>,
    rest: &S<Expr>,
    span: Span,
    env: &Vars,
    cx: &mut Cx,
) -> Result<S<Expr<Core>>, TypeError> {
    let init2 = rw(init, env, cx)?;
    let n = cx.next.bump();
    let get = names::var_get(x, n);
    let put = names::var_set(x, n);
    let st = Ty::State(n);
    cx.effects.push(EffectDecl {
        name: names::var_effect(x, n),
        params: Vec::new(),
        ops: vec![
            EffOp {
                name: get.clone(),
                params: vec![Ty::Unit],
                ret: st.clone(),
                // The parameter-passing State handler resumes exactly once in
                // tail position (`get(u,k) => \s -> k(s)(s)`), so both ops are
                // grade One.
                grade: Grade::One,
            },
            EffOp {
                name: put.clone(),
                params: vec![st],
                ret: Ty::Unit,
                grade: Grade::One,
            },
        ],
        span,
    });
    let mut env2 = env.clone();
    env2.insert(x.into(), Binding::Var(get.clone(), put.clone()));
    let rest2 = rw(rest, &env2, cx)?;
    let ops: BTreeSet<String> = [get.clone(), put.clone()].into();
    if let Some(bad) = escapes(&rest2, &ops, &cx.ctors, &mut BTreeSet::new()) {
        return Err(TypeError::Other {
            span: bad,
            msg: format!("`var {x}` escapes its block: the value here is a function that still uses `{x}` after its scope ends"),
        });
    }
    // \(s) -> k(s)(s) | \(s) -> k(())(v) | \(s) -> r
    let ks = call(
        call(evar(CONT, span), vec![evar(STATE, span)], span),
        vec![evar(STATE, span)],
        span,
    );
    let kv = call(
        call(evar(CONT, span), vec![sp(Expr::Unit, span)], span),
        vec![evar(VAL, span)],
        span,
    );
    let arms = vec![
        HandlerArm::Op(
            get,
            vec![UNIT_ARG.into()],
            CONT.into(),
            lam1(STATE, ks, span),
        ),
        HandlerArm::Op(put, vec![VAL.into()], CONT.into(), lam1(STATE, kv, span)),
        HandlerArm::Return(RET.into(), lam1(STATE, evar(RET, span), span)),
    ];
    let runner = names::var_runner(n);
    let handled = sp(Expr::Handle(Box::new(rest2), arms), span);
    let apply = call(evar(&runner, span), vec![init2], span);
    Ok(sp(
        Expr::Let(runner, Box::new(handled), Box::new(apply)),
        span,
    ))
}
