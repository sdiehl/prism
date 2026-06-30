//! Handle lowering dispatch and native closed-handle drivers.

use std::collections::BTreeSet;

use super::runtime::{ctor_pat, epure};
use super::{Lowerer, EOP, EPURE, ERESUME, OP_TAG, QAPPLY};
use crate::core::builtins::Builtin;
use crate::core::cbpv::{Comp, CoreFn, CoreOp, CorePat, HandleOp, Value};
use crate::core::fv;
use crate::error::TypeError;
use crate::names;
use crate::sym::Sym;

impl Lowerer {
    // Driver call site: reify `body` to an Eff value (`r0`), then drive it
    // through `driver`, threading the captured free vars as extra arguments.
    fn drive_from_body(
        &mut self,
        body: &Comp,
        driver: Sym,
        fvs: &[Sym],
    ) -> Result<Comp, TypeError> {
        let r0 = self.fresh("r0");
        let mut call_args = vec![Value::Var(r0)];
        call_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        Ok(Comp::Bind(
            Box::new(self.mon(body)?),
            r0,
            Box::new(Comp::Call(driver, call_args)),
        ))
    }

    pub(super) fn lower_handle(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = c
        else {
            return Ok(c.clone());
        };

        let fvs = handler_fvs(*return_var, return_body.as_deref(), ops);
        let open = self.is_open(body, ops);

        let driver = self.fresh("handle");
        let res = self.fresh("res");

        // EPure(x) => run return clause. Open drivers return Eff, so the return
        // body is monadified and a bare result is lifted with EPure.
        let x = self.fresh("x");
        let pure_body = match (return_var, return_body) {
            (Some(rv), Some(rb)) => {
                let rbody = if open {
                    self.mon(rb)?
                } else {
                    self.lower_comp(rb)?
                };
                Comp::Bind(Box::new(Comp::Return(Value::Var(x))), *rv, Box::new(rbody))
            }
            _ if open => epure(Value::Var(x)),
            _ => Comp::Return(Value::Var(x)),
        };
        let pure_arm = (ctor_pat(EPURE, &[x]), pure_body);

        // EOp(id, skip, arg, k) => dispatch on id
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");

        let mut resume_args = vec![Value::Var(names::RESUME_KONT.into())];
        resume_args.extend(fvs.iter().map(|v| Value::Var(*v)));
        // resume = \v -> drive(qApply(Q, v), fvs): run the op's continuation queue
        // `k` on `v`, then re-drive the result through this handler.
        let resume_thunk = Value::Thunk(Box::new(Comp::Lam(
            vec![names::RESUME_VAL.into()],
            Box::new(Comp::Bind(
                Box::new(Comp::Call(
                    QAPPLY.into(),
                    vec![Value::Var(k), Value::Var(names::RESUME_VAL.into())],
                )),
                names::RESUME_KONT.into(),
                Box::new(Comp::Call(driver, resume_args)),
            )),
        )));

        // Unhandled op (id not ours): closed handlers cannot reach here, open
        // handlers forward by re-emitting the EOp with a singleton queue holding a
        // continuation that re-enters this driver, so an enclosing handler
        // discharges it.
        let mut dispatch = if open {
            self.forward_eop(
                Value::Var(id),
                Value::Var(skip),
                Value::Var(arg),
                resume_thunk.clone(),
            )
        } else {
            Comp::Error(Value::Str(
                "ICE: unhandled effect op in closed handler dispatch".into(),
            ))
        };
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let rt = &resume_thunk;
        dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let op = &ops[i];
                let mut handler = if open {
                    let saved = std::mem::take(&mut me.resume_aliases);
                    me.resume_aliases.insert(op.resume);
                    let h = me.mon(&op.body);
                    me.resume_aliases = saved;
                    h?
                } else {
                    me.lower_comp(&op.body)?
                };
                // bind operation parameters from arg (tuple-unpacked when n-ary)
                handler = bind_params(&op.params, arg, handler);
                // bind resume
                let handle = Comp::Bind(
                    Box::new(Comp::Return(rt.clone())),
                    op.resume,
                    Box::new(handler),
                );
                // A closed handler's own ops always arrive at skip 0 (a masked
                // op of its effect keeps the handler open, by `is_open`), so it
                // handles directly. An open handler may receive one masked past
                // it (skip > 0): forward with one fewer level and re-enter this
                // driver on resume, mirroring the interpreter decrementing `skip`
                // on a matching handler crossing.
                if !open {
                    return Ok(handle);
                }
                let sk1 = me.fresh("sk");
                let reemit =
                    me.forward_eop(Value::Var(id), Value::Var(sk1), Value::Var(arg), rt.clone());
                let forward = Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Sub, Value::Var(skip), Value::Int(1))),
                    sk1,
                    Box::new(reemit),
                );
                let z = me.fresh("z");
                Ok(Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Eq, Value::Var(skip), Value::Int(0))),
                    z,
                    Box::new(Comp::If(Value::Var(z), Box::new(handle), Box::new(forward))),
                ))
            },
            dispatch,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let body_case = Comp::Case(Value::Var(res), vec![pure_arm, op_arm]);

        // Closed by construction: the params are `res` (the driven result) plus
        // exactly `fvs`, the `fv::comp_without` of every clause body computed
        // above. Every other name in `body_case` is a `{n}@hint` fresh binder or
        // a top-level callee, so no free occurrence can escape (no hygiene check
        // needed; see the note at the driver-append site in `lower`).
        let mut params = vec![res];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: driver,
            params,
            body: body_case,
        });

        // call site: run the monadified body, then drive it
        self.drive_from_body(body, driver, &fvs)
    }

    // A closed handle is driven natively when opted in and every clause resumes
    // only in tail position: its continuation never needs a mutually-recursive
    // driver, so a single self-recursive loop drives it in constant stack.
    pub(super) fn native_eligible(&self, c: &Comp) -> bool {
        if !self.native {
            return false;
        }
        let Comp::Handle { body, ops, .. } = c else {
            return false;
        };
        !self.is_open(body, ops) && resume_tail_only(ops)
    }

    pub(super) fn handle_closed(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        if self.native_eligible(c) {
            self.lower_handle_native(c)
        } else {
            self.lower_handle(c)
        }
    }

    // The self-recursive driver for an eligible closed handle. Mirrors
    // `lower_handle`, but the per-op continuation is the `EOp` queue itself: a
    // tail resume becomes `EResume(queue, value)`, and the loop drives the resumed
    // continuation by tail-calling itself on `qApply(queue, value)`. Because the
    // re-entry is a self-call at fixed arity it compiles to a `musttail`, so a
    // resuming loop runs in constant stack. The clauses are separate top-level
    // functions (direct calls, no per-dispatch closure), and the loop returns the
    // bare handler answer, the same call-site contract as `lower_handle` closed.
    pub(super) fn lower_handle_native(&mut self, c: &Comp) -> Result<Comp, TypeError> {
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = c
        else {
            return Ok(c.clone());
        };

        let fvs = handler_fvs(*return_var, return_body.as_deref(), ops);

        self.used_resume = true;
        let loop_name = self.fresh("region");

        // One top-level function per op: clause(arg, resume, fvs...). `resume` is
        // the op's continuation queue, so a tail resume monadifies to
        // `EResume(resume, value)`.
        let mut clause_names = Vec::new();
        for op in ops {
            let cname = self.fresh("clause");
            let arg_p = self.fresh("arg");
            let resume_p = self.fresh("res");
            let saved = std::mem::take(&mut self.resume_aliases);
            self.resume_aliases.insert(op.resume);
            let saved_native = self.native_resume;
            self.native_resume = true;
            let mbody = self.mon(&op.body);
            self.native_resume = saved_native;
            self.resume_aliases = saved;
            let with_resume = Comp::Bind(
                Box::new(Comp::Return(Value::Var(resume_p))),
                op.resume,
                Box::new(mbody?),
            );
            let cbody = bind_params(&op.params, arg_p, with_resume);
            let mut params = vec![arg_p, resume_p];
            params.extend(fvs.iter().copied());
            self.generated.push(CoreFn {
                name: cname,
                params,
                body: cbody,
            });
            clause_names.push(cname);
        }

        // EPure(x) => the body finished: run the return clause for the answer.
        let x = self.fresh("x");
        let pure_body = match (return_var, return_body) {
            (Some(rv), Some(rb)) => Comp::Bind(
                Box::new(Comp::Return(Value::Var(x))),
                *rv,
                Box::new(self.lower_comp(rb)?),
            ),
            _ => Comp::Return(Value::Var(x)),
        };
        let pure_arm = (ctor_pat(EPURE, &[x]), pure_body);

        // EOp(id, skip, arg, k) => dispatch on id. A closed handler's ops always
        // arrive at skip 0 (a masked op keeps the handler open), so `skip` is
        // unused, matching the closed `lower_handle` dispatch.
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let fail = Comp::Error(Value::Str(
            "ICE: unhandled effect op in closed native handler".into(),
        ));
        let lname = loop_name;
        let fvs_ref = &fvs;
        let dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let cname = clause_names[i];
                let mut call_args = vec![Value::Var(arg), Value::Var(k)];
                call_args.extend(fvs_ref.iter().map(|v| Value::Var(*v)));
                let cr = me.fresh("cr");
                // case cr of
                //   EResume(q, v) => region(qApply(q, v), fvs)   -- drive the resume
                //   EOp(..)       => region(cr, fvs)             -- a re-performed op
                //   EPure(ans)    => ans                         -- finished, bare answer
                let q = me.fresh("q");
                let v = me.fresh("v");
                let qa = me.fresh("qa");
                let mut resume_args = vec![Value::Var(qa)];
                resume_args.extend(fvs_ref.iter().map(|w| Value::Var(*w)));
                let resume_arm = (
                    ctor_pat(ERESUME, &[q, v]),
                    Comp::Bind(
                        Box::new(Comp::Call(
                            QAPPLY.into(),
                            vec![Value::Var(q), Value::Var(v)],
                        )),
                        qa,
                        Box::new(Comp::Call(lname, resume_args)),
                    ),
                );
                let oi = me.fresh("id");
                let os = me.fresh("sk");
                let oa = me.fresh("arg");
                let ok = me.fresh("k");
                let mut redrive_args = vec![Value::Var(cr)];
                redrive_args.extend(fvs_ref.iter().map(|w| Value::Var(*w)));
                let op_redrive = (
                    ctor_pat(EOP, &[oi, os, oa, ok]),
                    Comp::Call(lname, redrive_args),
                );
                let ans = me.fresh("ans");
                let final_arm = (ctor_pat(EPURE, &[ans]), Comp::Return(Value::Var(ans)));
                let cased = Comp::Case(Value::Var(cr), vec![resume_arm, op_redrive, final_arm]);
                Ok(Comp::Bind(
                    Box::new(Comp::Call(cname, call_args)),
                    cr,
                    Box::new(cased),
                ))
            },
            fail,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let cur = self.fresh("cur");
        let loop_body = Comp::Case(Value::Var(cur), vec![pure_arm, op_arm]);
        let mut params = vec![cur];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: loop_name,
            params,
            body: loop_body,
        });

        // Call site: reify the body to an Eff value, then drive it; the loop
        // returns the bare answer (closed).
        self.drive_from_body(body, loop_name, &fvs)
    }

    // `let f = <closed function-answer handle> in f(arg)`: the handler's answer
    // type is a function `S -> A` threaded as a state accumulator (a
    // parameter-passing handler, e.g. `rd(u, r) => \s -> r(s)(s)`). Each clause
    // resumes once and applies the result to a new state, so the driver becomes a
    // single self-tail-recursive loop `region(cur, acc, fvs)` that threads the
    // state in `acc` and `musttail`s on the resumed continuation: a
    // parameter-passing loop then runs in constant stack with no per-operation
    // frame. The boundary application `f(arg)` is folded into the initial call, so
    // the loop returns the bare answer. Returns None unless the handle is closed,
    // every clause and the return clause have the state shape, and `f` is applied
    // exactly once in tail position, so any other program falls back to the proven
    // free monad. Gated: only when natively driving effects.
    pub(super) fn try_lower_fn_answer(
        &mut self,
        m: &Comp,
        f: Sym,
        n: &Comp,
    ) -> Result<Option<Comp>, TypeError> {
        if !self.native {
            return Ok(None);
        }
        let Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } = m
        else {
            return Ok(None);
        };
        if ops.is_empty() || self.is_open(body, ops) || return_var.is_none() {
            return Ok(None);
        }
        // Pure shape check first, before any fresh-name or generated-function
        // mutation, so a non-match leaves the lowerer untouched for the fallback.
        let Some((ret_s, ret_body)) = state_return(return_body.as_deref()) else {
            return Ok(None);
        };
        let mut clauses = Vec::new();
        for op in ops {
            let Some(sc) = state_clause(op) else {
                return Ok(None);
            };
            clauses.push(sc);
        }
        if !fn_applied_once_tail(n, f) {
            return Ok(None);
        }

        let fvs = handler_fvs(*return_var, return_body.as_deref(), ops);

        let region = self.fresh("region");
        let acc = self.fresh("acc");

        // EPure(x) => run the return clause with the accumulator as its state, a
        // bare answer out.
        let x = self.fresh("x");
        let mut pbody = self.lower_comp(&ret_body)?;
        pbody = Comp::Bind(
            Box::new(Comp::Return(Value::Var(acc))),
            ret_s,
            Box::new(pbody),
        );
        let rv = return_var.expect("return_var checked present above");
        pbody = Comp::Bind(Box::new(Comp::Return(Value::Var(x))), rv, Box::new(pbody));
        let pure_arm = (ctor_pat(EPURE, &[x]), pbody);

        // EOp(id, skip, arg, k) => dispatch on id; skip is 0 for a closed
        // handler's own ops, as in the other closed dispatches.
        let id = self.fresh("id");
        let skip = self.fresh("sk");
        let arg = self.fresh("arg");
        let k = self.fresh("k");
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(op.name))
            .collect::<Result<_, _>>()?;
        let fail = Comp::Error(Value::Str(
            "ICE: unhandled effect op in closed native handler".into(),
        ));
        let fvs_ref = &fvs;
        let clauses_ref = &clauses;
        let dispatch = self.build_op_chain(
            &Value::Var(id),
            &ids,
            |me, i| {
                let sc = &clauses_ref[i];
                let op = &ops[i];
                // region(qApply(k, A), B, fvs): resume the continuation on `A`,
                // then thread `B` as the new accumulator.
                let qa = me.fresh("qa");
                let mut region_args = vec![Value::Var(qa), sc.b.clone()];
                region_args.extend(fvs_ref.iter().map(|w| Value::Var(*w)));
                let mut tail = Comp::Bind(
                    Box::new(Comp::Call(QAPPLY.into(), vec![Value::Var(k), sc.a.clone()])),
                    qa,
                    Box::new(Comp::Call(region, region_args)),
                );
                for (pm, px) in sc.prefix.iter().rev() {
                    let lm = me.lower_comp(pm)?;
                    tail = Comp::Bind(Box::new(lm), *px, Box::new(tail));
                }
                tail = Comp::Bind(
                    Box::new(Comp::Return(Value::Var(acc))),
                    sc.s,
                    Box::new(tail),
                );
                Ok(bind_params(&op.params, arg, tail))
            },
            fail,
        )?;
        let op_arm = (ctor_pat(EOP, &[id, skip, arg, k]), dispatch);

        let cur = self.fresh("cur");
        let loop_body = Comp::Case(Value::Var(cur), vec![pure_arm, op_arm]);
        let mut params = vec![cur, acc];
        params.extend(fvs.iter().copied());
        self.generated.push(CoreFn {
            name: region,
            params,
            body: loop_body,
        });

        // Call site: reify the handled computation, then drive it from `arg`. The
        // continuation `n` has its single `f(arg)` rewritten to the region call.
        let r0 = self.fresh("r0");
        let mut aliases = BTreeSet::new();
        aliases.insert(f);
        let driven = self
            .rewrite_fn_use(n, &aliases, region, r0, &fvs)?
            .ok_or_else(|| TypeError::Ice {
                msg: "function-answer use-site rewrite failed after shape check".into(),
            })?;
        Ok(Some(Comp::Bind(
            Box::new(self.mon(body)?),
            r0,
            Box::new(driven),
        )))
    }

    // Rewrite the continuation after `let f = <handle> in n` so the single tail
    // application `f(arg)` becomes `region(r0, arg, fvs)`, dropping the now-dead
    // `f` routing. Mirrors `fn_applied_once_tail`, which already verified the
    // shape, so the `None` arms are unreachable in practice.
    pub(super) fn rewrite_fn_use(
        &mut self,
        n: &Comp,
        aliases: &BTreeSet<Sym>,
        region: Sym,
        r0: Sym,
        fvs: &[Sym],
    ) -> Result<Option<Comp>, TypeError> {
        match n {
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(v)) = f.as_ref() else {
                    return Ok(None);
                };
                if !aliases.contains(v) || args.len() != 1 {
                    return Ok(None);
                }
                let mut call_args = vec![Value::Var(r0), args[0].clone()];
                call_args.extend(fvs.iter().map(|w| Value::Var(*w)));
                Ok(Some(Comp::Call(region, call_args)))
            }
            Comp::Bind(m, x, rest) => {
                if let Comp::Return(Value::Var(v)) = m.as_ref() {
                    if aliases.contains(v) {
                        let mut a2 = aliases.clone();
                        a2.insert(*x);
                        return self.rewrite_fn_use(rest, &a2, region, r0, fvs);
                    }
                }
                if mentions(&fv::comp(m), aliases) {
                    return Ok(None);
                }
                let lm = self.lower_comp(m)?;
                Ok(self
                    .rewrite_fn_use(rest, aliases, region, r0, fvs)?
                    .map(|r| Comp::Bind(Box::new(lm), *x, Box::new(r))))
            }
            _ => Ok(None),
        }
    }

    // mask<Eff> becomes a driver that handles nothing: it adds N to the id of
    // every Eff op flowing through it, so the next driver of that effect
    // misses its equality match once and forwards with id - N.
    //
    // Closed top-level template: its binders are the fixed `names::*` @-set,
    // disjoint from program names, and it never nests another template's body, so
    // the fixed binders cannot capture. Closedness is structural, not checked.
    pub(super) fn mask_driver(&mut self, ops: &[Sym]) -> Result<Sym, TypeError> {
        let driver = self.fresh("mask");
        // Queue binder for the re-emitted op (a `{n}@q` fresh name: unforgeable and
        // unique, so the template stays closed). The bump and forward arms are
        // mutually exclusive, so reusing one binder across both is sound.
        let qb = self.fresh("q");
        let resume = Value::Thunk(Box::new(Comp::Lam(
            vec![names::RESUME_VAL.into()],
            Box::new(Comp::Bind(
                Box::new(Comp::Call(
                    QAPPLY.into(),
                    vec![
                        Value::Var(names::CONT.into()),
                        Value::Var(names::RESUME_VAL.into()),
                    ],
                )),
                names::RESUME_KONT.into(),
                Box::new(Comp::Call(
                    driver,
                    vec![Value::Var(names::RESUME_KONT.into())],
                )),
            )),
        )));
        let reemit = |skipv: Value| {
            Comp::Bind(
                Box::new(Comp::StrBuiltin(
                    Builtin::TaqSnoc,
                    vec![Value::Unit, resume.clone()],
                )),
                qb,
                Box::new(Comp::Return(Value::Ctor(
                    EOP.into(),
                    OP_TAG,
                    vec![
                        Value::Var(names::OP_ID.into()),
                        skipv,
                        Value::Var(names::OP_ARG.into()),
                        Value::Var(qb),
                    ],
                ))),
            )
        };
        // An op of the masked effect gains one skip level, so the next matching
        // handler bypasses it once. Any other op passes through unchanged.
        let bump = Comp::Bind(
            Box::new(Comp::Prim(
                CoreOp::Add,
                Value::Var(names::OP_SKIP.into()),
                Value::Int(1),
            )),
            names::FWD_SKIP.into(),
            Box::new(reemit(Value::Var(names::FWD_SKIP.into()))),
        );
        let fwd = reemit(Value::Var(names::OP_SKIP.into()));
        let ids: Vec<i64> = ops
            .iter()
            .map(|op| self.op_id(*op))
            .collect::<Result<_, _>>()?;
        let dispatch = self.build_op_chain(
            &Value::Var(names::OP_ID.into()),
            &ids,
            |_, _| Ok(bump.clone()),
            fwd,
        )?;
        let pure_arm = (
            ctor_pat(EPURE, &[names::COMPOSE.into()]),
            epure(Value::Var(names::COMPOSE.into())),
        );
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
            dispatch,
        );
        self.generated.push(CoreFn {
            name: driver,
            params: vec![names::RET.into()],
            body: Comp::Case(Value::Var(names::RET.into()), vec![pure_arm, op_arm]),
        });
        Ok(driver)
    }
}

// Free variables of a handler's arms, which become extra parameters threaded
// through the driver and every resumption. The clause/return-lambda params, the
// op params and the resume are all bound within their bodies, so they fall out
// of `comp_without` already. `Sym` orders by intern id, so the result is sorted
// by name to keep the driver's parameter and resumption-argument order
// byte-stable across runs.
fn handler_fvs(return_var: Option<Sym>, return_body: Option<&Comp>, ops: &[HandleOp]) -> Vec<Sym> {
    let mut fvs = BTreeSet::new();
    if let Some(rb) = return_body {
        fvs.extend(fv::comp_without(rb, return_var.iter()));
    }
    for op in ops {
        let mut s = fv::comp_without(&op.body, &op.params);
        s.remove(&op.resume);
        fvs.extend(s);
    }
    let mut fvs: Vec<Sym> = fvs.into_iter().collect();
    fvs.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    fvs
}

fn bind_params(params: &[Sym], arg: Sym, body: Comp) -> Comp {
    match params.len() {
        0 => body,
        1 => Comp::Bind(
            Box::new(Comp::Return(Value::Var(arg))),
            params[0],
            Box::new(body),
        ),
        _ => {
            let binders = params.iter().map(|p| Some(*p)).collect();
            Comp::Case(Value::Var(arg), vec![(CorePat::Tuple(binders), body)])
        }
    }
}

// Whether every clause of a handler uses `resume` only as the head of a
// tail-position application. Such a resume can be driven by the self-recursive
// `{n}@region` loop (a tail resume is the clause's result, so it becomes
// `EResume(queue, value)`); any other occurrence (captured by a lambda, passed as
// an argument, bound and reused, returned as a value) would leave the queue where
// the loop cannot drive it, so the handler stays on the free monad.
fn resume_tail_only(ops: &[HandleOp]) -> bool {
    ops.iter().all(|op| {
        let mut aliases = BTreeSet::new();
        aliases.insert(op.resume);
        clause_resume_tail(&op.body, &aliases, true)
    })
}

fn mentions(set: &fv::Set, aliases: &BTreeSet<Sym>) -> bool {
    aliases.iter().any(|a| set.contains(a))
}

// `tail` tracks whether `c`'s value is the clause result. A resume application is
// allowed only in tail position with arguments that do not themselves mention a
// resume alias. The elaborator routes resume through `return k to x`, so a bind of
// that shape grows the alias set (and is not itself a use). Any other occurrence
// of an alias disqualifies the clause.
fn clause_resume_tail(c: &Comp, aliases: &BTreeSet<Sym>, tail: bool) -> bool {
    match c {
        Comp::App(f, args) if matches!(f.as_ref(), Comp::Force(Value::Var(v)) if aliases.contains(v)) => {
            tail && args.iter().all(|a| !mentions(&fv::value(a), aliases))
        }
        Comp::Bind(m, x, n) => {
            let routing = matches!(m.as_ref(), Comp::Return(Value::Var(v)) if aliases.contains(v));
            let mut a2 = aliases.clone();
            if let Comp::Return(Value::Var(v)) = m.as_ref() {
                if aliases.contains(v) {
                    a2.insert(*x);
                }
            }
            (routing || clause_resume_tail(m, aliases, false)) && clause_resume_tail(n, &a2, tail)
        }
        Comp::If(v, t, e) => {
            !mentions(&fv::value(v), aliases)
                && clause_resume_tail(t, aliases, tail)
                && clause_resume_tail(e, aliases, tail)
        }
        Comp::Case(v, arms) => {
            !mentions(&fv::value(v), aliases)
                && arms
                    .iter()
                    .all(|(_, b)| clause_resume_tail(b, aliases, tail))
        }
        other => !mentions(&fv::comp(other), aliases),
    }
}

// A function-answer state clause `\s -> let t = resume(A) in t(B)`: the handler's
// answer type is a function `S -> A` threaded as a state accumulator. `A` is the
// value the continuation resumes with, `B` the value its result (the next answer
// function) is applied to, so the loop becomes `region(qApply(k, A), B, fvs)`: a
// self-tail-call that threads `B` as the new accumulator. `prefix` is the pure
// routing binds that define `A`/`B` from the lambda param, op params and free
// vars; they are re-emitted verbatim. None when the clause is not of that shape.
struct StateClause {
    s: Sym,
    prefix: Vec<(Comp, Sym)>,
    a: Value,
    b: Value,
}

fn state_clause(op: &HandleOp) -> Option<StateClause> {
    let Comp::Return(Value::Thunk(t)) = &op.body else {
        return None;
    };
    let Comp::Lam(ps, inner) = t.as_ref() else {
        return None;
    };
    let [s] = ps.as_slice() else {
        return None;
    };
    let mut aliases = BTreeSet::new();
    aliases.insert(op.resume);
    let mut prefix: Vec<(Comp, Sym)> = Vec::new();
    let mut cur: &Comp = inner;
    loop {
        let Comp::Bind(m, x, n) = cur else {
            return None;
        };
        // The resume application `resume(A)` (possibly wrapped in its own pure
        // routing let-chain) bound to `x`, whose continuation applies `x` to `B`.
        if let Some((mprefix, a)) = resume_app(m, &aliases) {
            let b = state_apply_tail(n, *x)?;
            if mentions(&fv::value(&b), &aliases) {
                return None;
            }
            prefix.extend(mprefix);
            // Post-condition guard for the `\s -> let t = resume(A) in t(B)` shape:
            // a matched clause must fully consume the resume, so neither the resume
            // argument `a`, the tail argument `b`, nor any re-emitted prefix bind
            // may still reference it. An elaborator shape drift that slips past the
            // per-helper checks must NOT be threaded into the accumulator rewrite:
            // debug builds panic to surface it; release builds reject the match and
            // return None so the caller falls back to general handler lowering.
            if mentions(&fv::value(&a), &aliases)
                || mentions(&fv::value(&b), &aliases)
                || prefix
                    .iter()
                    .any(|(pm, _)| mentions(&fv::comp(pm), &aliases))
            {
                debug_assert!(
                    false,
                    "state_clause matched a clause that still references the resume: elaborated shape drifted"
                );
                super::diagnostics::report_shape_drift("state_clause");
                return None;
            }
            return Some(StateClause {
                s: *s,
                prefix,
                a,
                b,
            });
        }
        // `return r to x`: routes the resume through an ANF binder; drop the bind
        // (the resume is the queue `k`, not a value in scope) and track the alias.
        if let Comp::Return(Value::Var(v)) = m.as_ref() {
            if aliases.contains(v) {
                aliases.insert(*x);
                cur = n;
                continue;
            }
        }
        // A pure routing bind that defines part of `A`/`B`: re-emitted as-is.
        // Anything effectful or that mentions the resume is rejected.
        if !matches!(m.as_ref(), Comp::Return(_) | Comp::Prim(..))
            || mentions(&fv::comp(m), &aliases)
        {
            return None;
        }
        prefix.push(((**m).clone(), *x));
        cur = n;
    }
}

// A resume application `resume(A)`, possibly preceded by its own pure routing
// let-chain (the ANF binds the elaborator threads `s`/params and the resume
// through). Returns the pure prefix binds to preserve (resume routing dropped)
// and the value `A` the continuation resumes with. None when `m` is not a resume
// application.
fn resume_app(m: &Comp, aliases: &BTreeSet<Sym>) -> Option<(Vec<(Comp, Sym)>, Value)> {
    let mut local = aliases.clone();
    let mut prefix: Vec<(Comp, Sym)> = Vec::new();
    let mut cur = m;
    loop {
        match cur {
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(r)) = f.as_ref() else {
                    return None;
                };
                if !local.contains(r) {
                    return None;
                }
                let [a] = args.as_slice() else {
                    return None;
                };
                if mentions(&fv::value(a), &local) {
                    return None;
                }
                return Some((prefix, a.clone()));
            }
            Comp::Bind(mm, y, nn) => {
                if let Comp::Return(Value::Var(v)) = mm.as_ref() {
                    if local.contains(v) {
                        local.insert(*y);
                        cur = nn;
                        continue;
                    }
                }
                if !matches!(mm.as_ref(), Comp::Return(_) | Comp::Prim(..))
                    || mentions(&fv::comp(mm), &local)
                {
                    return None;
                }
                prefix.push(((**mm).clone(), *y));
                cur = nn;
            }
            _ => return None,
        }
    }
}

// The tail of a state clause: the resume result `t` applied once to `B`, modulo
// `return t to x` routing. Returns `B`.
fn state_apply_tail(n: &Comp, t: Sym) -> Option<Value> {
    let mut aliases = BTreeSet::new();
    aliases.insert(t);
    let mut cur = n;
    loop {
        match cur {
            Comp::App(f, args) => {
                let Comp::Force(Value::Var(v)) = f.as_ref() else {
                    return None;
                };
                if !aliases.contains(v) {
                    return None;
                }
                let [b] = args.as_slice() else {
                    return None;
                };
                if mentions(&fv::value(b), &aliases) {
                    return None;
                }
                return Some(b.clone());
            }
            Comp::Bind(m, x, rest) => {
                let Comp::Return(Value::Var(v)) = m.as_ref() else {
                    return None;
                };
                if !aliases.contains(v) {
                    return None;
                }
                aliases.insert(*x);
                cur = rest;
            }
            _ => return None,
        }
    }
}

// The return clause of a function-answer handler: `\s -> R`. Returns the lambda
// param and body, threaded with the accumulator at the loop's `EPure` arm.
fn state_return(return_body: Option<&Comp>) -> Option<(Sym, Comp)> {
    let Comp::Return(Value::Thunk(t)) = return_body? else {
        return None;
    };
    let Comp::Lam(ps, body) = t.as_ref() else {
        return None;
    };
    let [s] = ps.as_slice() else {
        return None;
    };
    Some((*s, (**body).clone()))
}

// Whether the continuation `n` after `let f = <handle> in n` applies `f` exactly
// once, as the head of a tail application with a single argument, modulo `return f
// to x` routing. A `f` used anywhere else (escaping as a value, applied twice)
// means the answer function cannot be folded into the region loop.
fn fn_applied_once_tail(n: &Comp, f: Sym) -> bool {
    let mut aliases = BTreeSet::new();
    aliases.insert(f);
    let mut cur = n;
    loop {
        match cur {
            Comp::App(fc, args) => {
                let Comp::Force(Value::Var(v)) = fc.as_ref() else {
                    return false;
                };
                return aliases.contains(v)
                    && args.len() == 1
                    && !mentions(&fv::value(&args[0]), &aliases);
            }
            Comp::Bind(m, x, rest) => {
                if let Comp::Return(Value::Var(v)) = m.as_ref() {
                    if aliases.contains(v) {
                        aliases.insert(*x);
                        cur = rest;
                        continue;
                    }
                }
                if mentions(&fv::comp(m), &aliases) {
                    return false;
                }
                cur = rest;
            }
            _ => return false,
        }
    }
}
