//! Whole-program runtime trampoline (`PRISM_TRAMPOLINE`).
//!
//! In whole-program free-monad mode every monadic function returns an `Eff`
//! value, and the program advances by a chain of tail calls (`ebind`'s
//! `(force f)(x)`, a closure `(force step)(rest)`, a driver re-entry) that never
//! returns until the whole computation finishes. A parameter-passing scheduler
//! turns that chain into O(operations) native frames, because each hop is a tail
//! closure-apply the borrow convention forbids `musttail`, so a deep run
//! overflows the C stack.
//!
//! This pass gives the compiled program the interpreter's flat-CEK shape without
//! abandoning the free monad: it defers every monadic *tail* hop into a heap
//! `EBounce` cell and drives the whole computation through one self-recursive
//! loop, `prism_drive`. A tail `Call`/`App` that yields `Eff` becomes
//! `return EBounce(thunk { call })` (the hop is reified, not performed), and every
//! site that inspects an `Eff` (the `EPure`/`EOp` `case` in `ebind`, `qApply`, a
//! handler driver, the `unwrap_main` boundary) first runs `prism_drive` on the
//! scrutinee. Because the sole unbounded chain (the run-queue/answer-function
//! recursion) is all tail calls, every hop bounces back to the nearest enclosing
//! `prism_drive`, which is a self-tail-call loop codegen already `musttail`s: the
//! chain then runs in constant native stack. Non-tail calls (a resumed step, a
//! list append) run eagerly, in bounded stack. Heap stays O(operations): one
//! `EBounce` thunk per hop, reclaimed by reference counting, never fused: the
//! honest cost of a stored continuation.
//!
//! A non-yielding fast path keeps the trampoline from pessimizing hops that
//! already run in constant native stack. A saturated tail `Call` whose callee
//! arity equals the enclosing frame's is emitted by codegen as a `musttail`
//! (`lower_tail`), so it advances without growing the stack; bouncing it would
//! only add an `EBounce` per hop and, worse, turn a native tail loop (`qApply`'s
//! self-call, a same-arity self/mutual recursion) into O(hops) heap. Such a hop
//! is left un-bounced. A closure `App` and a cross-arity `Call` never `musttail`
//! under the borrow convention, so they still bounce; a bounce inside a lambda or
//! thunk (a distinct frame whose arity also counts captured free vars) is always
//! taken, since the enclosing arity is not known there. The result is a bounce on
//! exactly the hops that can grow the stack, which is what makes default-on safe.
//!
//! Only genuinely `Eff`-returning callees are bounce targets and only `Eff`-tail
//! contexts bounce their tail apply, so a bare-returning function (a closed
//! handler driver, the unwrapped entry) is never deferred: an `EBounce` can reach
//! no consumer but `prism_drive`.

use std::collections::{BTreeMap, BTreeSet};

use super::runtime::ctor_pat;
use super::{BOUNCE_TAG, DRIVE, EBOUNCE, EOP, EPURE, ERESUME};
use crate::core::cbpv::{Comp, CoreFn, CorePat, Value};
use crate::fresh::Fresh;
use crate::names;
use crate::sym::Sym;

// A lambda/thunk is a distinct codegen frame whose arity counts captured free
// vars, unknown to this pass, so the fast path uses this sentinel there: it
// matches no real callee arity, so every tail hop inside it bounces (the safe
// default). A top-level body uses the real function arity instead.
const NO_FRAME: usize = usize::MAX;

// `fn prism_drive(e) = case e { EBounce(t) => (force t)() to e2; prism_drive(e2);
//                               _ => return e }`
//
// The trampoline loop. A deferred hop is `EBounce(thunk)`; forcing and applying
// the nullary thunk runs exactly one step and yields the next `Eff` (another
// bounce, or a final `EPure`/`EOp`). The `prism_drive(e2)` self-call is at fixed
// arity, so codegen `musttail`s it and the loop runs in constant native stack.
// Any non-bounce value (a concrete `EPure`/`EOp`, or a bare value an unwrapped
// entry returns) passes straight through. Closed top-level template, like
// `ebind`/`qApply`: its binders are fixed `@`-names disjoint from program names.
pub(super) fn prism_drive_fn() -> CoreFn {
    let e = Sym::from(names::RET); // r@
    let t = Sym::from(names::EBIND_FN); // f@
    let e2 = Sym::from(names::COMPOSE); // x@
    let bounce_arm = (
        ctor_pat(EBOUNCE, &[t]),
        Comp::Bind(
            Box::new(Comp::App(Box::new(Comp::Force(Value::Var(t))), vec![])),
            e2,
            Box::new(Comp::Call(DRIVE.into(), vec![Value::Var(e2)])),
        ),
    );
    let other_arm = (CorePat::Wild, Comp::Return(Value::Var(e)));
    CoreFn {
        name: DRIVE.into(),
        params: vec![e],
        dict_arity: 0,
        body: Comp::Case(Value::Var(e), vec![bounce_arm, other_arm]),
    }
}

fn is_eff_ctor(n: Sym) -> bool {
    matches!(n.as_str(), EPURE | EOP | ERESUME | EBOUNCE)
}

// Reify `c` (a monadic hop yielding `Eff`) as a zero-arg suspension. Codegen
// only allocates a thunk from a `Lam`, so the deferred computation rides inside a
// nullary lambda; `prism_drive` forces and applies it with no arguments.
fn bounce(c: Comp) -> Comp {
    Comp::Return(Value::Ctor(
        EBOUNCE.into(),
        BOUNCE_TAG,
        vec![Value::Thunk(Box::new(Comp::Lam(vec![], Box::new(c))))],
    ))
}

// A `case` that discriminates an `Eff` value (its arms test `EPure`/`EOp`/
// `EResume`); its scrutinee must be driven to a concrete cell first. The `TQ`
// uncons case and ordinary data cases are left alone.
fn is_eff_case(arms: &[(CorePat, Comp)]) -> bool {
    arms.iter()
        .any(|(p, _)| matches!(p, CorePat::Ctor(n, _) if is_eff_ctor(*n)))
}

// Whether `c`, in tail position, yields an `Eff` value. An `App` is a monadified
// closure apply (`Eff`); a `Call` is `Eff` exactly when its callee is. A bare
// `Return` (of a non-`Eff` value), a `Prim`, an `Io`, a `StrBuiltin` yield bare
// values, which is what makes a closed handler driver and the unwrapped entry
// classify bare and stay un-bounced. `Error` diverges, so it never forces a tail
// to bare.
fn eff_tail(c: &Comp, eff: &BTreeSet<Sym>) -> bool {
    match c {
        Comp::Return(Value::Ctor(n, _, _)) => is_eff_ctor(*n),
        Comp::Call(g, _) => eff.contains(g),
        Comp::App(..) | Comp::Force(_) | Comp::Error(_) => true,
        Comp::If(_, t, e) => eff_tail(t, eff) && eff_tail(e, eff),
        Comp::Case(_, arms) => arms.iter().all(|(_, b)| eff_tail(b, eff)),
        Comp::Bind(_, _, n) => eff_tail(n, eff),
        _ => false,
    }
}

// Greatest fixpoint of the `Eff`-returning top-level functions: start assuming
// all return `Eff`, then drop any whose tail is provably bare, until stable. A
// closed handler driver (its return clause and abort clauses end in a bare
// `return r`/`return code`) and the unwrapped entry fall out; `ebind`, `qApply`,
// open drivers and monadified user functions stay in.
fn eff_fns(fns: &[CoreFn]) -> BTreeSet<Sym> {
    let mut eff: BTreeSet<Sym> = fns.iter().map(|f| f.name).collect();
    loop {
        let mut changed = false;
        for f in fns {
            if eff.contains(&f.name) && !eff_tail(&f.body, &eff) {
                eff.remove(&f.name);
                changed = true;
            }
        }
        if !changed {
            return eff;
        }
    }
}

struct Tr<'a> {
    eff: &'a BTreeSet<Sym>,
    // Every top-level function's arity, for the non-yielding fast path.
    arity: &'a BTreeMap<Sym, usize>,
    fresh: &'a mut Fresh,
    // The arity of the native frame currently being rewritten (`NO_FRAME` inside a
    // lambda/thunk body); a same-arity saturated tail `Call` in it is `musttail`ed.
    cur_arity: usize,
}

impl Tr<'_> {
    // Whether a tail `Call(g, args)` is one codegen will emit as a `musttail`: a
    // saturated call whose callee arity equals the enclosing frame's. Such a hop
    // already advances in constant native stack, so the fast path leaves it
    // un-bounced (see the module header).
    fn native_tail(&self, g: Sym, argc: usize) -> bool {
        self.arity.get(&g) == Some(&argc) && argc == self.cur_arity
    }

    // `ctx` = the enclosing tail context returns `Eff`; `tail` = `c` is itself in
    // tail position. Bounce a tail `Call`/`App` only in an `Eff` context, and
    // drive every `Eff`-discriminating `case` regardless.
    fn go(&mut self, c: &Comp, ctx: bool, tail: bool) -> Comp {
        match c {
            Comp::Bind(m, x, n) => Comp::Bind(
                Box::new(self.go(m, ctx, false)),
                *x,
                Box::new(self.go(n, ctx, tail)),
            ),
            Comp::If(v, t, e) => Comp::If(
                v.clone(),
                Box::new(self.go(t, ctx, tail)),
                Box::new(self.go(e, ctx, tail)),
            ),
            Comp::Case(scrut, arms) => {
                let arms: Vec<(CorePat, Comp)> = arms
                    .iter()
                    .map(|(p, b)| (p.clone(), self.go(b, ctx, tail)))
                    .collect();
                if is_eff_case(&arms) {
                    let v = Sym::from(names::lowered("drv", self.fresh.bump()));
                    Comp::Bind(
                        Box::new(Comp::Call(DRIVE.into(), vec![scrut.clone()])),
                        v,
                        Box::new(Comp::Case(Value::Var(v), arms)),
                    )
                } else {
                    Comp::Case(scrut.clone(), arms)
                }
            }
            Comp::App(f, args) => {
                let app = Comp::App(
                    Box::new(self.go(f, ctx, false)),
                    args.iter().map(|a| self.value(a)).collect(),
                );
                if tail && ctx {
                    bounce(app)
                } else {
                    app
                }
            }
            Comp::Call(g, args) => {
                let call = Comp::Call(*g, args.iter().map(|a| self.value(a)).collect());
                if tail && ctx && self.eff.contains(g) && !self.native_tail(*g, args.len()) {
                    bounce(call)
                } else {
                    call
                }
            }
            Comp::Return(v) => Comp::Return(self.value(v)),
            Comp::Force(v) => Comp::Force(self.value(v)),
            Comp::Error(v) => Comp::Error(self.value(v)),
            Comp::Lam(ps, b) => {
                // A new tail scope, and a distinct codegen frame whose arity counts
                // captured free vars (unknown here): recompute whether it yields
                // `Eff` and disable the fast path inside it via `NO_FRAME`.
                let ctx2 = eff_tail(b, self.eff);
                let saved = self.cur_arity;
                self.cur_arity = NO_FRAME;
                let b = self.go(b, ctx2, true);
                self.cur_arity = saved;
                Comp::Lam(ps.clone(), Box::new(b))
            }
            // The remaining forms carry no sub-computations the trampoline must
            // touch (their values are transformed for nested thunks); leaving the
            // structure intact keeps the rewrite total without a kid-walker that
            // would lose the tail/ctx threading.
            other => super::map_kids(other, &mut |k| self.go(k, ctx, false)),
        }
    }

    // Transform thunk bodies inside a value (an arrow, a stored closure): each is
    // its own tail scope.
    fn value(&mut self, v: &Value) -> Value {
        match v {
            Value::Thunk(c) => {
                // A thunk body is its own codegen frame; its arity is unknown here
                // (a `Lam` inside resets it), so disable the fast path until one does.
                let ctx = eff_tail(c, self.eff);
                let saved = self.cur_arity;
                self.cur_arity = NO_FRAME;
                let c = self.go(c, ctx, true);
                self.cur_arity = saved;
                Value::Thunk(Box::new(c))
            }
            Value::Ctor(n, t, fs) => {
                Value::Ctor(*n, *t, fs.iter().map(|x| self.value(x)).collect())
            }
            Value::Tuple(fs) => Value::Tuple(fs.iter().map(|x| self.value(x)).collect()),
            _ => v.clone(),
        }
    }
}

// Rewrite the free-monad program to drive through `prism_drive`. Every function
// is transformed (so its `Eff`-cases are driven), but only an `Eff`-tail context
// bounces its tail apply and only an `Eff`-returning callee is a bounce target,
// so a bare-returning function (a closed driver, the unwrapped entry) defers
// nothing. `prism_drive` itself is appended by the caller, after this pass.
pub(super) fn trampolinize(fns: &mut [CoreFn], fresh: &mut Fresh) {
    let eff = eff_fns(fns);
    let arity: BTreeMap<Sym, usize> = fns.iter().map(|f| (f.name, f.params.len())).collect();
    for f in fns.iter_mut() {
        let ctx = eff_tail(&f.body, &eff);
        let mut tr = Tr {
            eff: &eff,
            arity: &arity,
            fresh,
            cur_arity: f.params.len(),
        };
        f.body = tr.go(&f.body, ctx, true);
    }
}
