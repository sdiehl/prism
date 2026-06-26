//! Erase escape-checked local `var` state to mutable cells.
//!
//! `var x := e` elaborates (`syntax/desugar/effects/vars.rs`) to a private 2-op
//! State effect with a parameter-passing handler (`get(u,k) => \s -> k(s)(s)`,
//! `set(v,k) => \s -> k(())(v)`, `return r => \s -> r`) wrapped as
//! `let run@n = handle BODY with {..} in run@n(init)`. That handler is not
//! tail-resumptive and carries two ops, so it falls off both fused paths into the
//! free monad, where every `get`/`set` reifies an `EOp` cell and the resumption
//! is not a tail call: a `var` loop then allocates per iteration and overflows the
//! stack. But the escape analysis already proved the state never leaves its block,
//! so it is semantically a mutable cell. This pass recognizes the closed var/State
//! handler and rewrites it to one: `get` -> `RefGet`, `set` -> `RefSet`, the block
//! wrapped in `RefNew(init)`. With the var ops gone, the tail-recursive loop driver
//! (`repeat_while`/`forever`) compiles to a `musttail` loop, so the var loop runs
//! in constant stack with no per-operation allocation. The State effect remains
//! through type-checking (it proves purity/escape); only Core lowering erases it.
//!
//! Soundness: a mutable cell shares state across resumptions, but pure State gives
//! each resumption an independent copy. They agree iff the var's continuation is
//! never resumed more than once. So erasure is skipped entirely when the program
//! contains any multishot handler (a clause that uses its `resume` more than once);
//! the var's own single-resume parameter-passing clauses are not multishot.

use crate::core::cbpv::{Comp, Core, CoreFn, HandleOp, Value};
use crate::fresh::Fresh;
use crate::names::{self, is_var_runner};
use crate::sym::Sym;

/// Rewrite every closed local `var`/State handler in `core` to mutable-cell ops.
/// A no-op (returns a clone) when the program has a multishot handler, where the
/// shared cell would diverge from pure State.
pub(super) fn erase_local_vars(core: &Core) -> Core {
    if core.fns.iter().any(|f| has_multishot(&f.body)) {
        return core.clone();
    }
    let mut er = Eraser {
        fresh: Fresh::new(),
    };
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| CoreFn {
                name: f.name,
                params: f.params.clone(),
                body: er.erase(&f.body),
            })
            .collect(),
    }
}

struct Eraser {
    fresh: Fresh,
}

impl Eraser {
    fn erase(&mut self, c: &Comp) -> Comp {
        if let Some(vb) = match_var_block(c) {
            let cell: Sym = names::lowered("cell", self.fresh.bump()).into();
            let init = self.erase(&vb.init);
            // Erase nested vars in the body first, then this var's own ops.
            let body = self.erase(&vb.body);
            let body = erase_ops(&body, vb.get, vb.set, cell);
            // run@n(init) threaded the State and discarded it (`return r => \s -> r`),
            // so the block's value is the body's value; the cell holds the state.
            return Comp::Bind(
                Box::new(init),
                vb.init_var,
                Box::new(Comp::Bind(
                    Box::new(Comp::RefNew(Value::Var(vb.init_var))),
                    cell,
                    Box::new(body),
                )),
            );
        }
        map_kids(c, &mut |k| self.erase(k))
    }
}

struct VarBlock {
    body: Comp,
    get: Sym,
    set: Sym,
    init: Comp,
    init_var: Sym,
}

// Recognize `Bind(handle BODY with {var get/set/return}, run@n, run@n(init))`,
// the fixed shape `vars.rs` emits. The op names `get@x@n`/`set@x@n` and the
// runner `run@n` must all share the var id `n` (and the get/set the var name `x`),
// a triple-match no construct but the var desugar produces. Returns the pieces to
// rewrite, or None to leave the handler for the existing lowering (always sound).
fn match_var_block(c: &Comp) -> Option<VarBlock> {
    let Comp::Bind(m, run_sym, kont) = c else {
        return None;
    };
    if !is_var_runner(run_sym.as_str()) {
        return None;
    }
    let Comp::Handle { body, ops, .. } = m.as_ref() else {
        return None;
    };
    let [a, b] = ops.as_slice() else {
        return None;
    };
    // Identify which op is get and which is set; both must share name@id.
    let (get_op, set_op) = order_get_set(a, b)?;
    let (gx, gn) = parse_var_op(get_op.name.as_str(), "get@")?;
    let (sx, sn) = parse_var_op(set_op.name.as_str(), "set@")?;
    let rn = run_sym.as_str().strip_prefix("run@")?;
    if gx != sx || gn != sn || gn != rn {
        return None;
    }
    // kont: `Bind(<init>, it, Bind(Return(run@n), ra, (force ra)(it)))`.
    let (init, init_var) = match_runner_apply(kont, *run_sym)?;
    Some(VarBlock {
        body: (**body).clone(),
        get: get_op.name,
        set: set_op.name,
        init,
        init_var,
    })
}

fn order_get_set<'a>(a: &'a HandleOp, b: &'a HandleOp) -> Option<(&'a HandleOp, &'a HandleOp)> {
    if a.name.as_str().starts_with("get@") && b.name.as_str().starts_with("set@") {
        Some((a, b))
    } else if b.name.as_str().starts_with("get@") && a.name.as_str().starts_with("set@") {
        Some((b, a))
    } else {
        None
    }
}

// "get@x@n" / "set@x@n" with the given prefix -> (x, n).
fn parse_var_op<'a>(name: &'a str, prefix: &str) -> Option<(&'a str, &'a str)> {
    name.strip_prefix(prefix)?.rsplit_once('@')
}

// Peel `Bind(<init>, it, Bind(Return(run_sym), ra, (force ra)(it)))`, returning
// the init computation and its binder. Also accepts the init applied inline.
fn match_runner_apply(kont: &Comp, run_sym: Sym) -> Option<(Comp, Sym)> {
    let Comp::Bind(init, it, rest) = kont else {
        return None;
    };
    let Comp::Bind(run_bind, ra, app) = rest.as_ref() else {
        return None;
    };
    // `ra` aliases the runner.
    match run_bind.as_ref() {
        Comp::Return(Value::Var(rs)) if *rs == run_sym => {}
        _ => return None,
    }
    // `(force ra)(it)`.
    let Comp::App(f, args) = app.as_ref() else {
        return None;
    };
    let Comp::Force(Value::Var(fa)) = f.as_ref() else {
        return None;
    };
    if *fa != *ra {
        return None;
    }
    match args.as_slice() {
        [Value::Var(v)] if *v == *it => Some(((**init).clone(), *it)),
        _ => None,
    }
}

// Replace this var's `do get`/`do set` with cell reads/writes, recursing through
// every subterm and thunk (the loop-body thunk holds the ops). Other ops, and
// other vars' ops, are left untouched.
fn erase_ops(c: &Comp, get: Sym, set: Sym, cell: Sym) -> Comp {
    match c {
        Comp::Do(op, _) if *op == get => Comp::RefGet(Value::Var(cell)),
        Comp::Do(op, args) if *op == set => {
            // set takes one argument: the new value.
            let v = args.first().cloned().unwrap_or(Value::Unit);
            Comp::RefSet(Value::Var(cell), v)
        }
        _ => map_kids(c, &mut |k| erase_ops(k, get, set, cell)),
    }
}

// Whether a handler clause anywhere resumes more than once (a multishot handler):
// its `resume` variable occurs more than once in the clause body. The var/State
// clauses use `resume` exactly once (`k(s)(s)` is a single `force k`), so they are
// not flagged.
fn has_multishot(c: &Comp) -> bool {
    let mut found = false;
    if let Comp::Handle { ops, .. } = c {
        for op in ops {
            if var_uses(&op.body, op.resume) > 1 {
                found = true;
            }
        }
    }
    each_subterm(c, &mut |sc| found |= has_multishot(sc));
    found
}

// Count occurrences of `Value::Var(x)` in a computation (including in thunks).
// Values (and the thunks they hold, via `val_uses`) are counted by `each_value`;
// sub-computations by `each_subcomp`. The two are disjoint, so no occurrence is
// double-counted (using `each_subterm` here would recount every thunk body).
fn var_uses(c: &Comp, x: Sym) -> usize {
    let mut n = 0;
    each_value(c, &mut |v| n += val_uses(v, x));
    super::each_subcomp(c, &mut |sc| n += var_uses(sc, x));
    n
}

fn val_uses(v: &Value, x: Sym) -> usize {
    match v {
        Value::Var(y) => usize::from(*y == x),
        Value::Thunk(c) => var_uses(c, x),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().map(|f| val_uses(f, x)).sum(),
        _ => 0,
    }
}

// Visit immediate values (those directly held by `c`, not in sub-computations).
fn each_value<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Value)) {
    super::each_value(c, f);
}

// Visit immediate sub-computations and thunk bodies in immediate values.
fn each_subterm<'a>(c: &'a Comp, f: &mut impl FnMut(&'a Comp)) {
    super::each_subcomp(c, f);
    super::each_value(c, &mut |v| {
        let mut ts = Vec::new();
        super::thunks_in_value(v, &mut ts);
        for t in ts {
            f(t);
        }
    });
}

// Rebuild `c`, applying `g` to every immediate sub-computation and to every thunk
// body in immediate values. The single structural recursion both passes share.
fn map_kids<G: FnMut(&Comp) -> Comp>(c: &Comp, g: &mut G) -> Comp {
    let vals = |args: &[Value], g: &mut G| args.iter().map(|a| map_val(a, g)).collect();
    match c {
        Comp::Bind(m, x, n) => Comp::Bind(Box::new(g(m)), *x, Box::new(g(n))),
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(g(b))),
        Comp::App(f, args) => Comp::App(Box::new(g(f)), vals(args, g)),
        Comp::If(v, t, e) => Comp::If(map_val(v, g), Box::new(g(t)), Box::new(g(e))),
        Comp::Case(v, arms) => {
            let v = map_val(v, g);
            Comp::Case(v, arms.iter().map(|(p, b)| (p.clone(), g(b))).collect())
        }
        Comp::Mask(ops, b) => Comp::Mask(ops.clone(), Box::new(g(b))),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(g(body)),
            return_var: *return_var,
            return_body: return_body.as_ref().map(|rb| Box::new(g(rb))),
            ops: ops
                .iter()
                .map(|op| HandleOp {
                    name: op.name,
                    params: op.params.clone(),
                    resume: op.resume,
                    body: g(&op.body),
                })
                .collect(),
        },
        Comp::Return(v) => Comp::Return(map_val(v, g)),
        Comp::Force(v) => Comp::Force(map_val(v, g)),
        Comp::Print(v) => Comp::Print(map_val(v, g)),
        Comp::PrintF(v) => Comp::PrintF(map_val(v, g)),
        Comp::PrintS(v) => Comp::PrintS(map_val(v, g)),
        Comp::Error(v) => Comp::Error(map_val(v, g)),
        Comp::Srand(v) => Comp::Srand(map_val(v, g)),
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, map_val(v, g)),
        Comp::Dup(v) => Comp::Dup(map_val(v, g)),
        Comp::Drop(v) => Comp::Drop(map_val(v, g)),
        Comp::Prim(op, a, b) => Comp::Prim(*op, map_val(a, g), map_val(b, g)),
        Comp::Call(n, args) => Comp::Call(*n, vals(args, g)),
        Comp::Do(op, args) => Comp::Do(*op, vals(args, g)),
        Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, vals(args, g)),
        Comp::RefNew(v) => Comp::RefNew(map_val(v, g)),
        Comp::RefGet(v) => Comp::RefGet(map_val(v, g)),
        Comp::RefSet(a, b) => Comp::RefSet(map_val(a, g), map_val(b, g)),
        Comp::WithReuse { token, freed, body } => Comp::WithReuse {
            token: *token,
            freed: map_val(freed, g),
            body: Box::new(g(body)),
        },
        Comp::Reuse(tok, v) => Comp::Reuse(*tok, map_val(v, g)),
        Comp::PrintNl | Comp::ReadInt | Comp::ReadLine | Comp::Rand => c.clone(),
    }
}

fn map_val<G: FnMut(&Comp) -> Comp>(v: &Value, g: &mut G) -> Value {
    match v {
        Value::Thunk(c) => Value::Thunk(Box::new(g(c))),
        Value::Ctor(n, t, fs) => Value::Ctor(*n, *t, fs.iter().map(|f| map_val(f, g)).collect()),
        Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| map_val(f, g)).collect()),
        _ => v.clone(),
    }
}
