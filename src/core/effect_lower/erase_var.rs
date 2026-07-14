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
//! never resumed more than once. So a function's vars are erased only when no
//! genuinely multishot op is reachable from it (performed or handled, transitively
//! through calls and thunks); a multishot clause is one whose `resume` is applied
//! more than once, or escapes into a nested closure, constructor, tuple, or alias
//! (whose application count no syntactic gate can see), unless the op's declared
//! grade already caps it at single-shot. The var's own parameter-passing clauses
//! apply `resume` exactly once under the answer lambda, so they are not flagged.
//! The decision is per function, not whole program, so a multishot handler in one
//! component does not drag an unrelated var loop off the fast tier.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::cbpv::{Comp, Core, CoreFn, HandleOp, Value};
use crate::fixpoint::least_fixpoint;
use crate::fresh::Fresh;
use crate::names::{self, is_var_runner};
use crate::sym::Sym;
use crate::syntax::ast::Grade;

use super::{collect_ops, OpGrades};

/// Rewrite closed local `var`/State handlers in `core` to mutable-cell ops,
/// per function.
///
/// A mutable cell shares state across resumptions, while pure State gives each
/// resumption an independent copy; the two agree only when the var's
/// continuation is never resumed more than once. So a function is erased only
/// when no genuinely multishot op is reachable from it (performed or handled,
/// transitively through calls and thunks): otherwise an outer or local multishot
/// handler could re-run its var ops on the shared cell.
///
/// This is per function, not whole program: a multishot handler in one component
/// no longer drags an unrelated var loop off the fast tier. `grades` sharpens
/// which ops are multishot: an op graded at most `One` can never resume more than
/// once, so it never counts, and the syntactic scan stays as a debug cross-check.
pub(super) fn erase_local_vars(core: &Core, grades: &OpGrades) -> Core {
    let multishot = multishot_ops(core, grades);
    // No genuinely multishot handler anywhere: every var is safe to erase. This
    // is the common path and stays byte-identical to the prior whole-program
    // behavior (no reachability computed, no function skipped).
    let unsafe_fns: BTreeSet<Sym> = if multishot.is_empty() {
        BTreeSet::new()
    } else {
        let reach = reach_map(core);
        core.fns
            .iter()
            .filter(|f| reach[&f.name].intersection(&multishot).next().is_some())
            .map(|f| f.name)
            .collect()
    };
    let mut er = Eraser {
        fresh: Fresh::new(),
    };
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| {
                if unsafe_fns.contains(&f.name) {
                    f.clone()
                } else {
                    CoreFn {
                        name: f.name,
                        params: f.params.clone(),
                        dict_arity: f.dict_arity,
                        body: er.erase(&f.body),
                    }
                }
            })
            .collect(),
    }
}

// Ops with a genuinely multishot handler somewhere in the program. A clause is
// multishot when the syntactic scan says so and the op's declared grade permits
// it: an op graded at most `One` can never resume more than once, so it is
// excluded, and the two must agree (a graded op the scan calls multishot is a
// broken invariant the desugar check should have rejected).
fn multishot_ops(core: &Core, grades: &OpGrades) -> BTreeSet<Sym> {
    let mut out = BTreeSet::new();
    for f in &core.fns {
        collect_multishot(&f.body, grades, &mut out);
    }
    out
}

fn collect_multishot(c: &Comp, grades: &OpGrades, out: &mut BTreeSet<Sym>) {
    if let Comp::Handle { ops, .. } = c {
        // The classification is the stored fact the handler was built with
        // (`CheckedHandler::new` computes it from the clause bodies), not a
        // re-scan here.
        for (op, ru) in ops.iter_with_use() {
            match grades.get(&op.name) {
                Some(g) if *g <= Grade::Once => debug_assert!(
                    !ru.multishot,
                    "op `{}` declared grade {:?} but its clause classifies as multishot; \
                     the desugar grade check should have rejected it",
                    op.name, g
                ),
                _ if ru.multishot => {
                    out.insert(op.name);
                }
                _ => {}
            }
        }
    }
    each_subterm(c, &mut |sc| collect_multishot(sc, grades, out));
}

// Every op each function can perform or handle, transitively over calls and
// thunks: the least fixpoint of `own_ops(f) union reach(callee)` over the call
// graph. Used to decide, per function, whether a multishot op is in scope of its
// vars. `collect_ops` already descends thunks; `deep_calls` matches it so a call
// buried in a thunk is not missed.
fn reach_map(core: &Core) -> BTreeMap<Sym, BTreeSet<Sym>> {
    let own: BTreeMap<Sym, BTreeSet<Sym>> = core
        .fns
        .iter()
        .map(|f| {
            let mut ops = BTreeSet::new();
            collect_ops(&f.body, &mut ops);
            (f.name, ops)
        })
        .collect();
    let calls: BTreeMap<Sym, BTreeSet<Sym>> = core
        .fns
        .iter()
        .map(|f| {
            let mut cs = BTreeSet::new();
            deep_calls(&f.body, &mut cs);
            (f.name, cs)
        })
        .collect();
    let seed: BTreeMap<Sym, BTreeSet<Sym>> =
        core.fns.iter().map(|f| (f.name, BTreeSet::new())).collect();
    least_fixpoint(seed, |name, cur| {
        let mut s = own[name].clone();
        for callee in &calls[name] {
            if let Some(r) = cur.get(callee) {
                s.extend(r.iter().copied());
            }
        }
        s
    })
}

// Every function `Call`ed anywhere in `c`, including inside thunks (which
// `super::all_calls` does not enter), mirroring `collect_ops`'s descent.
fn deep_calls(c: &Comp, out: &mut BTreeSet<Sym>) {
    if let Comp::Call(g, _) = c {
        out.insert(*g);
    }
    super::each_value(c, &mut |v| {
        let mut ts = Vec::new();
        super::thunks_in_value(v, &mut ts);
        for t in ts {
            deep_calls(t, out);
        }
    });
    super::each_subcomp(c, &mut |sc| deep_calls(sc, out));
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
        super::map_kids(c, &mut |k| self.erase(k))
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
    let [a, b] = ops.arms() else {
        return None;
    };
    // Identify which op is get and which is set; both must share name@id.
    let (get_op, set_op) = order_get_set(a, b)?;
    let (gx, gn) = names::parse_var_get(get_op.name.as_str())?;
    let (sx, sn) = names::parse_var_set(set_op.name.as_str())?;
    let rn = names::parse_var_runner(run_sym.as_str())?;
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
    if names::is_var_get(a.name.as_str()) && names::is_var_set(b.name.as_str()) {
        Some((a, b))
    } else if names::is_var_get(b.name.as_str()) && names::is_var_set(a.name.as_str()) {
        Some((b, a))
    } else {
        None
    }
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
        _ => super::map_kids(c, &mut |k| erase_ops(k, get, set, cell)),
    }
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
