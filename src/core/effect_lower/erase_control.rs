//! Erase loop-control effects (`break`/`continue`/`return`) to direct control flow.
//!
//! `break`/`continue`/`return` desugar (`syntax/desugar/effects/mod.rs`) to
//! non-resumable performs of three internal one-op effects, each discharged by a
//! `final ctl` handler the desugar wraps around the loop body (`continue`), the
//! loop driver call (`break`), or the whole function body (`return`). As algebraic
//! effects those handlers fall onto the free monad: each `do` reifies an `EOp`
//! cell and the loop driver's resumption is a closure apply rather than a tail
//! call, so a control-using loop allocates per iteration and overflows the native
//! stack at scale. But every one of these handlers is a fixed template with a
//! statically known shape, so the control flow can be recovered directly.
//!
//! This pass recognizes those templates and rewrites the matched ones, leaving
//! everything else for the existing (always-sound) free-monad lowering, the same
//! recognize-or-leave discipline as [`erase_var`](super::erase_var). It runs after
//! var erasure, so a recognized body is Ref ops plus control `do`s, and before the
//! strategy cascade, so a pure imperative loop classifies as `"pure"` once its
//! control ops are gone.
//!
//! `break`/`continue` thread as an immediate `ctl:Int` (`0` = ran to the end, `1`
//! = `continue`, `2` = `break`), short-circuiting the body on any non-zero so the
//! discarded tail matches the dropped continuation of the `final ctl` handler.
//! `continue` needs no driver change (`repeat_while`/`forever` already ignore the
//! body result, so a `continue`-only body just yields `0`/`1`). `break` emits a
//! fresh tail-recursive `{n}@loopdrv` that exits on `ctl == 2`.
//!
//! `return` threads `Step` (`SMore` = no return yet, `SDone v` = a `return` is
//! propagating) through the whole function body, since it crosses loops to the
//! function boundary. A loop the `return` crosses is driven return-aware: its body
//! yields `SMore(ctl)`/`SDone(v)`, so the driver propagates an inner `SDone`
//! outward while still dispatching `break` on `ctl`. `seed_unwrap` at the function
//! tail strips the `Step` back to the bare result. Codegen `musttail` on each
//! driver self-call keeps every recognized loop constant-stack.

use std::collections::BTreeSet;

use crate::core::cbpv::{Comp, Core, CoreFn, CoreOp, CorePat, Value};
use crate::core::fv;
use crate::fresh::Fresh;
use crate::names;
use crate::sym::Sym;

use super::{DONE_TAG, MORE_TAG, SDONE, SMORE};

// The prelude tail-recursive loop drivers a `while`/`loop` desugars to.
const REPEAT_WHILE: &str = "repeat_while";
const FOREVER: &str = "forever";

// Control dispositions threaded through a loop body.
const CTL_NORMAL: i64 = 0;
const CTL_CONTINUE: i64 = 1;
const CTL_BREAK: i64 = 2;

/// Rewrite recognized `break`/`continue`/`return` control handlers in `core` to
/// direct control flow, leaving unmatched handlers for the free-monad lowering.
/// Generated `break`/`return` drivers are appended to the program. The returned
/// flag is set when a `return` handler was erased, so the caller knows to add the
/// `SMore`/`SDone` constructors to the constructor table.
pub(super) fn erase_control(core: &Core) -> (Core, bool) {
    // Functions that can perform an effect other than loop control: erasing a
    // control handler whose region reaches such an effect could change how it
    // interacts with an outer (possibly multishot) handler, so those loops are
    // left for the free monad. An un-erased `var` (when `erase_var` bailed on a
    // multishot program) surfaces here as a foreign latent effect, so the multishot
    // protection composes. The latent set is over the call graph, so a foreign
    // effect reached through a call counts too.
    let foreign: BTreeSet<Sym> = super::latent_ops(core)
        .into_iter()
        .filter(|(_, ops)| ops.iter().any(|op| !is_control_op(*op)))
        .map(|(n, _)| n)
        .collect();
    let mut er = Eraser {
        fresh: Fresh::new(),
        generated: Vec::new(),
        used_step: false,
        foreign,
    };
    let mut fns: Vec<CoreFn> = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            body: er.erase(&f.body),
        })
        .collect();
    fns.append(&mut er.generated);
    (Core { fns }, er.used_step)
}

struct Eraser {
    fresh: Fresh,
    generated: Vec<CoreFn>,
    used_step: bool,
    foreign: BTreeSet<Sym>,
}

impl Eraser {
    fn fresh(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }

    // Whether `c` can perform an effect other than loop control: a `do` of a
    // non-control op, or a call to a function with such a latent effect. Descends
    // into thunks and sub-handlers (conservative: an effect handled locally inside
    // the region still leaves the loop on the free monad rather than risk it).
    fn has_foreign_effect(&self, c: &Comp) -> bool {
        match c {
            Comp::Do(op, _) => !is_control_op(*op),
            Comp::Call(g, _) if self.foreign.contains(g) => true,
            _ => {
                let mut found = false;
                for_each_thunk_and_subcomp(c, &mut |sc| found |= self.has_foreign_effect(sc));
                found
            }
        }
    }

    // Structural descent. The control-handler templates are matched here and
    // rewritten; an unmatched node is rebuilt unchanged. The `return` handler is
    // the outermost (it wraps the whole body, loops included), so it is matched
    // first; a `break` handler (wrapping the driver call) before `continue` (its
    // own handler nests inside the body thunk).
    fn erase(&mut self, c: &Comp) -> Comp {
        // A control handler whose protected region performs a foreign effect (one
        // its own loop control does not catch) is left for the free monad, so the
        // erased direct control flow never reorders that effect against an outer
        // handler.
        if let Some(body) = match_return(c) {
            if !self.has_foreign_effect(body) {
                let mark = self.generated.len();
                if let Some(threaded) = self.thread_fn_return(body) {
                    self.used_step = true;
                    return self.seed_unwrap(threaded);
                }
                // Bail: drop any nested drivers the partial threading emitted.
                self.generated.truncate(mark);
            }
        }
        if let Some((cond, body)) = match_break(c) {
            if !self.has_foreign_effect(&body) {
                if let Some(call) = self.build_driver(Some(&cond), &body, false) {
                    return call;
                }
            }
        }
        if let Some(body) = match_continue(c) {
            if !self.has_foreign_effect(body) {
                if let Some(threaded) = self.thread_ctl(body) {
                    return threaded;
                }
            }
        }
        super::map_kids(c, &mut |k| self.erase(k))
    }

    // ----- break / continue: ctl:Int threading -------------------------------

    // Thread `ctl:Int` through a Unit-valued loop body so it yields `0` (ran to the
    // end), `1` (`continue`), or `2` (`break`). Each is an immediate, so no
    // per-iteration heap. Returns None for a shape it cannot thread (control
    // captured in a closure, or whose discarded value is used).
    fn thread_ctl(&mut self, c: &Comp) -> Option<Comp> {
        if let Some(inner) = match_continue(c) {
            return self.thread_ctl(inner);
        }
        match c {
            Comp::Do(op, _) => ctl_signal(*op).map(|v| Comp::Return(Value::Int(v))),
            Comp::Bind(m, x, n) => {
                if let Comp::Do(op, _) = m.as_ref() {
                    if let Some(v) = ctl_signal(*op) {
                        return Some(Comp::Return(Value::Int(v)));
                    }
                }
                if signals_ctl(m) {
                    if fv::comp(n).contains(x) {
                        return None;
                    }
                    let mt = self.thread_ctl(m)?;
                    let rest = self.thread_ctl(n)?;
                    let ctl = self.fresh("ctl");
                    Some(Comp::Bind(
                        Box::new(mt),
                        ctl,
                        Box::new(self.step_guard_int(ctl, rest)),
                    ))
                } else {
                    Some(Comp::Bind(
                        Box::new(self.erase(m)),
                        *x,
                        Box::new(self.thread_ctl(n)?),
                    ))
                }
            }
            Comp::If(v, t, e) => Some(Comp::If(
                v.clone(),
                Box::new(self.thread_ctl(t)?),
                Box::new(self.thread_ctl(e)?),
            )),
            Comp::Case(v, arms) => Some(Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), self.thread_ctl(b)?)))
                    .collect::<Option<_>>()?,
            )),
            _ if !signals_ctl(c) => {
                let u = self.fresh("u");
                Some(Comp::Bind(
                    Box::new(self.erase(c)),
                    u,
                    Box::new(Comp::Return(Value::Int(CTL_NORMAL))),
                ))
            }
            _ => None,
        }
    }

    // The immediate-Int analogue of `state::take::step_guard`: a non-zero `ctl`
    // (a `continue`/`break`) short-circuits, returning `ctl`; a normal result
    // (`ctl == 0`) runs `cont`.
    fn step_guard_int(&mut self, ctl: Sym, cont: Comp) -> Comp {
        let t = self.fresh("t");
        Comp::Bind(
            Box::new(Comp::Prim(
                CoreOp::Eq,
                Value::Var(ctl),
                Value::Int(CTL_NORMAL),
            )),
            t,
            Box::new(Comp::If(
                Value::Var(t),
                Box::new(cont),
                Box::new(Comp::Return(Value::Var(ctl))),
            )),
        )
    }

    // ----- return: Step threading --------------------------------------------

    // Thread `Step` through a function body so it yields `SMore(result)` (no return
    // fired; `result` is the body's normal value) or `SDone(v)` (a `return v` is
    // propagating). A loop the return crosses is replaced by a return-aware driver
    // whose `Step` result is guarded the same way. None for a shape it cannot
    // thread, leaving the whole `return` handler for the free monad.
    fn thread_fn_return(&mut self, c: &Comp) -> Option<Comp> {
        // A loop (a bare `repeat_while`/`forever` spine, or a `break` loop) the
        // return crosses: drive it return-aware so an inner `SDone` propagates out.
        if let Some((call, rest)) = self.return_loop_call(c) {
            return Some(match rest {
                // The loop is the function tail (a `forever` that only exits via
                // `return`, or a `while` whose normal value is the result): its
                // `Step` is the result.
                None => call,
                // Code follows the loop: on normal/`break` exit (`SMore`) run it; an
                // inner `SDone` propagates.
                Some(r) => {
                    let cont = self.thread_fn_return(&r)?;
                    let s = self.fresh("s");
                    let w = self.fresh("w");
                    Comp::Bind(
                        Box::new(call),
                        s,
                        Box::new(self.guard_fn_return(s, w, cont)),
                    )
                }
            });
        }
        match c {
            Comp::Do(op, args) if names::is_return_op(op.as_str()) => {
                Some(Comp::Return(sdone(ret_arg(args))))
            }
            Comp::Bind(m, x, n) => {
                if let Comp::Do(op, args) = m.as_ref() {
                    if names::is_return_op(op.as_str()) {
                        return Some(Comp::Return(sdone(ret_arg(args))));
                    }
                }
                if signals_return(m) {
                    // A compound head (an `if`/`match`) that may return; bind its
                    // normal value, propagate an `SDone`.
                    let mt = self.thread_fn_return(m)?;
                    let cont = self.thread_fn_return(n)?;
                    let s = self.fresh("s");
                    Some(Comp::Bind(
                        Box::new(mt),
                        s,
                        Box::new(self.guard_fn_return(s, *x, cont)),
                    ))
                } else {
                    Some(Comp::Bind(
                        Box::new(self.erase(m)),
                        *x,
                        Box::new(self.thread_fn_return(n)?),
                    ))
                }
            }
            Comp::If(v, t, e) => Some(Comp::If(
                v.clone(),
                Box::new(self.thread_fn_return(t)?),
                Box::new(self.thread_fn_return(e)?),
            )),
            Comp::Case(v, arms) => Some(Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), self.thread_fn_return(b)?)))
                    .collect::<Option<_>>()?,
            )),
            // A tail that cannot return: its value is the function's normal result.
            _ if !signals_return(c) => {
                let r = self.fresh("r");
                Some(Comp::Bind(
                    Box::new(self.erase(c)),
                    r,
                    Box::new(Comp::Return(smore(Value::Var(r)))),
                ))
            }
            _ => None,
        }
    }

    // Thread the combined `Step(SMore(ctl), SDone(v))` disposition through a loop
    // body that a `return` crosses: `break`/`continue` ride `SMore(2)`/`SMore(1)`,
    // a `return` becomes `SDone(v)`, a normal end is `SMore(0)`.
    fn thread_loop_combined(&mut self, c: &Comp) -> Option<Comp> {
        if let Some(inner) = match_continue(c) {
            return self.thread_loop_combined(inner);
        }
        // A nested loop the return crosses: its own `break`/`continue` are absorbed
        // by its driver, so to the enclosing loop it is just a head yielding `Step`
        // (`SMore` = it finished, `SDone` = a `return` is propagating out through it).
        if let Some((call, rest)) = self.return_loop_call(c) {
            let s = self.fresh("s");
            let w = self.fresh("w");
            return Some(match rest {
                // The nested loop is the enclosing body's tail: its normal exit means
                // this iteration completed (`ctl 0`); a `return` propagates.
                None => {
                    let v = self.fresh("v");
                    Comp::Bind(
                        Box::new(call),
                        s,
                        Box::new(Comp::Case(
                            Value::Var(s),
                            vec![
                                (
                                    ctor_pat1(SMORE, w),
                                    Comp::Return(smore(Value::Int(CTL_NORMAL))),
                                ),
                                (ctor_pat1(SDONE, v), Comp::Return(sdone(Value::Var(v)))),
                            ],
                        )),
                    )
                }
                Some(r) => {
                    let cont = self.thread_loop_combined(&r)?;
                    Comp::Bind(
                        Box::new(call),
                        s,
                        Box::new(self.guard_fn_return(s, w, cont)),
                    )
                }
            });
        }
        match c {
            Comp::Do(op, args) if names::is_return_op(op.as_str()) => {
                Some(Comp::Return(sdone(ret_arg(args))))
            }
            Comp::Do(op, _) => ctl_signal(*op).map(|v| Comp::Return(smore(Value::Int(v)))),
            Comp::Bind(m, x, n) => {
                if let Comp::Do(op, args) = m.as_ref() {
                    if names::is_return_op(op.as_str()) {
                        return Some(Comp::Return(sdone(ret_arg(args))));
                    }
                    if let Some(v) = ctl_signal(*op) {
                        return Some(Comp::Return(smore(Value::Int(v))));
                    }
                }
                if signals_loop(m) {
                    if fv::comp(n).contains(x) {
                        return None;
                    }
                    let mt = self.thread_loop_combined(m)?;
                    let rest = self.thread_loop_combined(n)?;
                    let s = self.fresh("s");
                    Some(Comp::Bind(
                        Box::new(mt),
                        s,
                        Box::new(self.step_guard_combined(s, rest)),
                    ))
                } else {
                    Some(Comp::Bind(
                        Box::new(self.erase(m)),
                        *x,
                        Box::new(self.thread_loop_combined(n)?),
                    ))
                }
            }
            Comp::If(v, t, e) => Some(Comp::If(
                v.clone(),
                Box::new(self.thread_loop_combined(t)?),
                Box::new(self.thread_loop_combined(e)?),
            )),
            Comp::Case(v, arms) => Some(Comp::Case(
                v.clone(),
                arms.iter()
                    .map(|(p, b)| Some((p.clone(), self.thread_loop_combined(b)?)))
                    .collect::<Option<_>>()?,
            )),
            _ if !signals_loop(c) => {
                let u = self.fresh("u");
                Some(Comp::Bind(
                    Box::new(self.erase(c)),
                    u,
                    Box::new(Comp::Return(smore(Value::Int(CTL_NORMAL)))),
                ))
            }
            _ => None,
        }
    }

    // `case s { SMore(ctl) => if ctl == 0 then cont else SMore(ctl), SDone(v) => SDone(v) }`:
    // a `continue`/`break` short-circuits the body carrying its disposition; a
    // `return` propagates.
    fn step_guard_combined(&mut self, s: Sym, cont: Comp) -> Comp {
        let ctl = self.fresh("ctl");
        let t = self.fresh("t");
        let v = self.fresh("v");
        let smore_arm = Comp::Bind(
            Box::new(Comp::Prim(
                CoreOp::Eq,
                Value::Var(ctl),
                Value::Int(CTL_NORMAL),
            )),
            t,
            Box::new(Comp::If(
                Value::Var(t),
                Box::new(cont),
                Box::new(Comp::Return(smore(Value::Var(ctl)))),
            )),
        );
        Comp::Case(
            Value::Var(s),
            vec![
                (ctor_pat1(SMORE, ctl), smore_arm),
                (ctor_pat1(SDONE, v), Comp::Return(sdone(Value::Var(v)))),
            ],
        )
    }

    // `case s { SMore(x) => cont, SDone(v) => SDone(v) }`: bind the normal result to
    // `x` and continue, or propagate a `return`.
    fn guard_fn_return(&mut self, s: Sym, x: Sym, cont: Comp) -> Comp {
        let v = self.fresh("v");
        Comp::Case(
            Value::Var(s),
            vec![
                (ctor_pat1(SMORE, x), cont),
                (ctor_pat1(SDONE, v), Comp::Return(sdone(Value::Var(v)))),
            ],
        )
    }

    // Unwrap the `Step` at the function tail back to the bare result.
    fn seed_unwrap(&mut self, threaded: Comp) -> Comp {
        let fin = self.fresh("fin");
        let a = self.fresh("a");
        let b = self.fresh("b");
        Comp::Bind(
            Box::new(threaded),
            fin,
            Box::new(Comp::Case(
                Value::Var(fin),
                vec![
                    (ctor_pat1(SMORE, a), Comp::Return(Value::Var(a))),
                    (ctor_pat1(SDONE, b), Comp::Return(Value::Var(b))),
                ],
            )),
        )
    }

    // ----- shared driver generation ------------------------------------------

    // Emit a fresh tail-recursive driver for a recognized loop and return the call
    // that replaces it. The driver inlines the condition and the threaded body,
    // closing over the loop's free variables (the erased `var` cells and captured
    // params) as parameters so its self-call is a plain tail `Call` (codegen
    // `musttail` => constant native stack). `return_aware` selects the disposition:
    // a plain `Int` body returning Unit, or a `Step` body returning `Step` so a
    // `return` propagates. None when the body cannot be threaded.
    fn build_driver(
        &mut self,
        cond: Option<&Comp>,
        body: &Comp,
        return_aware: bool,
    ) -> Option<Comp> {
        // Threading may emit nested drivers; on a bail, drop them so no orphan
        // function is left in the program.
        let mark = self.generated.len();
        let threaded = if return_aware {
            self.thread_loop_combined(body)
        } else {
            self.thread_ctl(body)
        };
        let Some(threaded) = threaded else {
            self.generated.truncate(mark);
            return None;
        };

        let mut set = fv::comp(&threaded);
        if let Some(c) = cond {
            set.extend(fv::comp(c));
        }
        let mut fvs: Vec<Sym> = set.into_iter().collect();
        fvs.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        let args: Vec<Value> = fvs.iter().map(|v| Value::Var(*v)).collect();

        let drv = self.fresh("loopdrv");
        let self_call = Comp::Call(drv, args.clone());
        let dispatch = if return_aware {
            self.combined_dispatch(threaded, self_call)
        } else {
            self.int_dispatch(threaded, self_call)
        };
        let exit = if return_aware {
            Comp::Return(smore(Value::Unit))
        } else {
            Comp::Return(Value::Unit)
        };
        let drv_body = match cond {
            Some(c) => {
                let b = self.fresh("b");
                Comp::Bind(
                    Box::new(c.clone()),
                    b,
                    Box::new(Comp::If(Value::Var(b), Box::new(dispatch), Box::new(exit))),
                )
            }
            None => dispatch,
        };
        self.generated.push(CoreFn {
            name: drv,
            params: fvs,
            body: drv_body,
        });
        Some(Comp::Call(drv, args))
    }

    // Recognize a loop that a `return` crosses (its body performs `do fn@return`),
    // build a return-aware driver for it, and return the driver call (which yields
    // `Step`) together with the continuation after the loop (None when the loop is
    // the tail). Covers a bare `repeat_while`/`forever` spine and a `break` loop
    // (its handler wrapping the driver call), as a tail or a statement head. None
    // when there is no return-crossing loop here.
    fn return_loop_call(&mut self, c: &Comp) -> Option<(Comp, Option<Comp>)> {
        // A bare `repeat_while`/`forever` spine.
        if let Some((cond, body, rest)) = peel_loop_spine(c) {
            if signals_return(&body) {
                let call = self.build_driver(cond.as_ref(), &body, true)?;
                return Some((call, rest));
            }
        }
        // A `break` loop as a statement head, with code following it.
        if let Comp::Bind(m, w, rest) = c {
            if let Some((cond, body)) = match_break(m) {
                if signals_return(&body) {
                    // The loop's Unit result must be discarded (it is bound to `_`).
                    if fv::comp(rest).contains(w) {
                        return None;
                    }
                    let call = self.build_driver(Some(&cond), &body, true)?;
                    return Some((call, Some((**rest).clone())));
                }
            }
        }
        // A `break` loop as the tail.
        if let Some((cond, body)) = match_break(c) {
            if signals_return(&body) {
                let call = self.build_driver(Some(&cond), &body, true)?;
                return Some((call, None));
            }
        }
        None
    }

    // `ctl == 2` (break) exits; `0`/`1` (normal/continue) tail-loop.
    fn int_dispatch(&mut self, threaded: Comp, self_call: Comp) -> Comp {
        let ctl = self.fresh("ctl");
        let z = self.fresh("z");
        Comp::Bind(
            Box::new(threaded),
            ctl,
            Box::new(Comp::Bind(
                Box::new(Comp::Prim(
                    CoreOp::Eq,
                    Value::Var(ctl),
                    Value::Int(CTL_BREAK),
                )),
                z,
                Box::new(Comp::If(
                    Value::Var(z),
                    Box::new(Comp::Return(Value::Unit)),
                    Box::new(self_call),
                )),
            )),
        )
    }

    // `case s { SMore(ctl) => if ctl == 2 then SMore(unit) else self-call, SDone(v) => SDone(v) }`:
    // a `break` exits the loop normally, a `return` propagates outward.
    fn combined_dispatch(&mut self, threaded: Comp, self_call: Comp) -> Comp {
        let s = self.fresh("s");
        let ctl = self.fresh("ctl");
        let z = self.fresh("z");
        let v = self.fresh("v");
        let smore_arm = Comp::Bind(
            Box::new(Comp::Prim(
                CoreOp::Eq,
                Value::Var(ctl),
                Value::Int(CTL_BREAK),
            )),
            z,
            Box::new(Comp::If(
                Value::Var(z),
                Box::new(Comp::Return(smore(Value::Unit))),
                Box::new(self_call),
            )),
        );
        Comp::Bind(
            Box::new(threaded),
            s,
            Box::new(Comp::Case(
                Value::Var(s),
                vec![
                    (ctor_pat1(SMORE, ctl), smore_arm),
                    (ctor_pat1(SDONE, v), Comp::Return(sdone(Value::Var(v)))),
                ],
            )),
        )
    }
}

fn smore(v: Value) -> Value {
    Value::Ctor(SMORE.into(), MORE_TAG, vec![v])
}

fn sdone(v: Value) -> Value {
    Value::Ctor(SDONE.into(), DONE_TAG, vec![v])
}

fn ctor_pat1(name: &str, var: Sym) -> CorePat {
    CorePat::Ctor(Sym::from(name), vec![Some(var)])
}

// The value `do fn@return(v)` carries (its single argument).
fn ret_arg(args: &[Value]) -> Value {
    args.first().cloned().unwrap_or(Value::Unit)
}

// Whether `op` is one of the three loop-control ops this pass erases.
fn is_control_op(op: Sym) -> bool {
    let s = op.as_str();
    names::is_break_op(s) || names::is_continue_op(s) || names::is_return_op(s)
}

// The disposition a `do` carries, or None if it is not a `break`/`continue` op.
fn ctl_signal(op: Sym) -> Option<i64> {
    if names::is_break_op(op.as_str()) {
        Some(CTL_BREAK)
    } else if names::is_continue_op(op.as_str()) {
        Some(CTL_CONTINUE)
    } else {
        None
    }
}

// Recognize the `continue` handler template the desugar wraps around a loop body:
//   handle BODY with { loop@continue(k) => return (), return r => return () }
// Match on the op name only (binders are alpha-renamed; the op name is unforgeable
// in source). Returns the wrapped BODY, or None to leave the handler.
fn match_continue(c: &Comp) -> Option<&Comp> {
    let Comp::Handle { body, ops, .. } = c else {
        return None;
    };
    let [op] = ops.as_slice() else {
        return None;
    };
    if !names::is_continue_op(op.name.as_str()) {
        return None;
    }
    Some(body)
}

// Recognize the `return` handler template the desugar wraps around a function body:
//   handle BODY with { fn@return(v) => return v, return r => return r }
// Returns the wrapped BODY, or None to leave the handler.
fn match_return(c: &Comp) -> Option<&Comp> {
    let Comp::Handle { body, ops, .. } = c else {
        return None;
    };
    let [op] = ops.as_slice() else {
        return None;
    };
    if !names::is_return_op(op.name.as_str()) {
        return None;
    }
    Some(body)
}

// Recognize the `break` handler template the desugar wraps around the loop driver:
//   handle { return thunk {\.cond} to tc
//            return thunk {\.body} to tb
//            repeat_while(tc, tb) } with { loop@break(k) => (), return r => () }
// Returns the inlined condition and body (the body with its own `continue` wrapper
// peeled, since this loop's `continue` threads into the same `ctl`).
fn match_break(c: &Comp) -> Option<(Comp, Comp)> {
    let Comp::Handle { body, ops, .. } = c else {
        return None;
    };
    let [op] = ops.as_slice() else {
        return None;
    };
    if !names::is_break_op(op.name.as_str()) {
        return None;
    }
    let (cond, body, _) = peel_loop_spine(body)?;
    cond.map(|cond| (cond, body))
}

// Recognize a bare `repeat_while`/`forever` loop spine (the thunk binds plus the
// trailing driver call), returning the inlined condition (None for `forever`), the
// body, and the continuation after the loop (None when the loop is the tail).
fn peel_loop_spine(c: &Comp) -> Option<(Option<Comp>, Comp, Option<Comp>)> {
    let mut thunks: std::collections::BTreeMap<Sym, Comp> = std::collections::BTreeMap::new();
    let mut cur = c;
    loop {
        match cur {
            Comp::Bind(m, t, rest) if nullary_thunk(m).is_some() => {
                thunks.insert(*t, nullary_thunk(m).unwrap().clone());
                cur = rest.as_ref();
            }
            // The loop call followed by more code.
            Comp::Bind(call, w, rest) if is_loop_call(call) => {
                let (cond, body) = resolve_loop_call(call, &thunks)?;
                // The loop's Unit result is bound to `w`; it must be discarded.
                if fv::comp(rest).contains(w) {
                    return None;
                }
                return Some((cond, body, Some((**rest).clone())));
            }
            // The loop call as the tail.
            _ if is_loop_call(cur) => {
                let (cond, body) = resolve_loop_call(cur, &thunks)?;
                return Some((cond, body, None));
            }
            _ => return None,
        }
    }
}

fn is_loop_call(c: &Comp) -> bool {
    matches!(c, Comp::Call(g, _) if g.as_str() == REPEAT_WHILE || g.as_str() == FOREVER)
}

// Resolve a `repeat_while(tc, tb)`/`forever(tb)` call against the peeled thunks to
// the inlined condition (None for `forever`) and body (continue wrapper peeled).
fn resolve_loop_call(
    c: &Comp,
    thunks: &std::collections::BTreeMap<Sym, Comp>,
) -> Option<(Option<Comp>, Comp)> {
    let Comp::Call(g, args) = c else {
        return None;
    };
    if g.as_str() == REPEAT_WHILE {
        let [Value::Var(tc), Value::Var(tb)] = args.as_slice() else {
            return None;
        };
        let cond = thunks.get(tc)?.clone();
        let body = peel_continue(thunks.get(tb)?.clone());
        Some((Some(cond), body))
    } else {
        let [Value::Var(tb)] = args.as_slice() else {
            return None;
        };
        let body = peel_continue(thunks.get(tb)?.clone());
        Some((None, body))
    }
}

fn peel_continue(body: Comp) -> Comp {
    match_continue(&body).cloned().unwrap_or(body)
}

// The body of `return thunk { \. body }` (a nullary-lambda thunk), or None.
fn nullary_thunk(m: &Comp) -> Option<&Comp> {
    let Comp::Return(Value::Thunk(t)) = m else {
        return None;
    };
    match t.as_ref() {
        Comp::Lam(ps, b) if ps.is_empty() => Some(b),
        _ => None,
    }
}

// Whether `c` performs a `do break`/`do continue` this loop catches. A nested loop
// absorbs its body's `break`/`continue` (they target the innermost loop), so a
// control-catching handle is opaque here.
fn signals_ctl(c: &Comp) -> bool {
    match c {
        Comp::Do(op, _) => ctl_signal(*op).is_some(),
        Comp::Handle { ops, .. } if ops.iter().any(|o| ctl_signal(o.name).is_some()) => false,
        _ => {
            let mut found = false;
            for_each_thunk_and_subcomp(c, &mut |sc| found |= signals_ctl(sc));
            found
        }
    }
}

// Whether `c` performs a `do fn@return`. Unlike `break`/`continue`, `return`
// crosses every loop to the function boundary, so this descends through loop
// handlers too.
fn signals_return(c: &Comp) -> bool {
    if matches!(c, Comp::Do(op, _) if names::is_return_op(op.as_str())) {
        return true;
    }
    let mut found = false;
    for_each_thunk_and_subcomp(c, &mut |sc| found |= signals_return(sc));
    found
}

fn signals_loop(c: &Comp) -> bool {
    signals_ctl(c) || signals_return(c)
}

fn for_each_thunk_and_subcomp<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Comp)) {
    super::each_value(c, &mut |v| {
        let mut ts = Vec::new();
        super::thunks_in_value(v, &mut ts);
        for t in ts {
            f(t);
        }
    });
    super::each_subcomp(c, f);
}
