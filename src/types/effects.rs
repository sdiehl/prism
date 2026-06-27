use std::collections::BTreeMap;

use super::ty::Effects;
use crate::sym::Sym;
use crate::syntax::ast::{Core, Decl, Expr, HandlerArm, Program, Row, Ty, S};
use crate::tc::EffOpInfo;

type Ops = BTreeMap<String, EffOpInfo>;

// In-scope bindings whose value is a function carrying a (statically known)
// effect row: annotated higher-order parameters. Applying one performs its row.
type Locals = BTreeMap<String, Effects>;

// This set-pass is not a redundant twin of the DK row unifier: its result seeds
// each function's row prefix in `infer_decl`, so the unifier knows which labels
// to expect. It cannot be dropped in favour of projecting the inferred row until
// effect-row inference becomes fully principal on its own.
pub(crate) fn fixpoint(prog: &Program<Core>, ops: &Ops) -> BTreeMap<String, Effects> {
    let mut map: BTreeMap<String, Effects> = prog
        .fns
        .iter()
        .map(|d| (d.name.clone(), Effects::new()))
        .collect();
    loop {
        let mut changed = false;
        for d in &prog.fns {
            let e = of_decl(d, &map, ops);
            // An absent function legitimately means "no effects" (the
            // Effects::new() the map starts with), so fall back, never panic.
            let slot = map.entry(d.name.clone()).or_default();
            if e != *slot {
                *slot = e;
                changed = true;
            }
        }
        if !changed {
            return map;
        }
    }
}

// Effect of a declaration body, with its annotated function-typed parameters in
// scope as effect-carrying locals.
pub(crate) fn of_decl(d: &Decl<Core>, fns: &BTreeMap<String, Effects>, ops: &Ops) -> Effects {
    let mut locals = Locals::new();
    for p in &d.params {
        if let Some(ty) = &p.ty {
            if let Some(row) = fn_row(ty) {
                locals.insert(p.name.clone(), row_labels(row));
            }
        }
    }
    of_expr(&d.body, fns, ops, &locals)
}

// Peel foralls to find a function type and return its effect row.
fn fn_row(ty: &Ty) -> Option<&Row> {
    match ty {
        Ty::Forall(_, b) => fn_row(b),
        Ty::Fun(_, row, _) => Some(row),
        _ => None,
    }
}

// Concrete labels of a surface effect row. A polymorphic tail (row variable)
// contributes none: the effect surfaces where it is instantiated, which the DK
// row unifier handles during checking.
fn row_labels(row: &Row) -> Effects {
    match row {
        Row::Empty => Effects::new(),
        Row::Cons(ls, _) => ls.iter().map(|l| Sym::from(&l.name)).collect(),
    }
}

// Effect of a standalone expression (REPL), with no effect-carrying locals.
pub(crate) fn of_expr_top(
    e: &S<Expr<Core>>,
    fns: &BTreeMap<String, Effects>,
    ops: &Ops,
) -> Effects {
    of_expr(e, fns, ops, &Locals::new())
}

fn of_expr(
    e: &S<Expr<Core>>,
    fns: &BTreeMap<String, Effects>,
    ops: &Ops,
    locals: &Locals,
) -> Effects {
    match &e.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Str(_)
        | Expr::Var(_) => Effects::new(),
        Expr::Bin(_, a, b) => union(of_expr(a, fns, ops, locals), &of_expr(b, fns, ops, locals)),
        Expr::If(c, t, e2) => {
            let s = union(of_expr(c, fns, ops, locals), &of_expr(t, fns, ops, locals));
            union(s, &of_expr(e2, fns, ops, locals))
        }
        Expr::Let(_, v, b) => union(of_expr(v, fns, ops, locals), &of_expr(b, fns, ops, locals)),
        Expr::Lam(ps, b) => {
            let inner = shadow(locals, ps.iter().map(|p| p.name.as_str()));
            of_expr(b, fns, ops, &inner)
        }
        Expr::Call(f, args) => {
            let mut s = head(f, fns, ops, locals);
            s = union(s, &of_expr(f, fns, ops, locals));
            for a in args {
                s = union(s, &of_expr(a, fns, ops, locals));
            }
            s
        }
        Expr::Pipe(x, f) => {
            let mut s = union(of_expr(x, fns, ops, locals), &of_expr(f, fns, ops, locals));
            s = union(s, &head(f, fns, ops, locals));
            s
        }
        Expr::Match(s, arms) => {
            let mut acc = of_expr(s, fns, ops, locals);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    acc = union(acc, &of_expr(g, fns, ops, locals));
                }
                acc = union(acc, &of_expr(&arm.body, fns, ops, locals));
            }
            acc
        }
        Expr::List(elems) | Expr::Tuple(elems) => {
            let mut acc = Effects::new();
            for elem in elems {
                acc = union(acc, &of_expr(elem, fns, ops, locals));
            }
            acc
        }
        Expr::FieldAccess(e, _) => of_expr(e, fns, ops, locals),
        Expr::Inst(f, _) | Expr::Ann(f, _) => of_expr(f, fns, ops, locals),
        // An indexed read performs `Fail` (out of range / absent key), on top of
        // any effects of the receiver and key.
        Expr::Index(recv, key) => {
            let s = union(
                of_expr(recv, fns, ops, locals),
                &of_expr(key, fns, ops, locals),
            );
            union(s, &once(Sym::from(crate::names::FAIL_EFFECT)))
        }
        // A functional indexed write is total; its effects are just those of the
        // receiver, key, and value sub-expressions.
        Expr::IndexSet(recv, key, val) => {
            let s = union(
                of_expr(recv, fns, ops, locals),
                &of_expr(key, fns, ops, locals),
            );
            union(s, &of_expr(val, fns, ops, locals))
        }
        Expr::RecordCreate(_, fields) => {
            let mut acc = Effects::new();
            for (_, e) in fields {
                acc = union(acc, &of_expr(e, fns, ops, locals));
            }
            acc
        }
        Expr::RecordUpdate(base, _, fields) => {
            let mut acc = of_expr(base, fns, ops, locals);
            for (_, e) in fields {
                acc = union(acc, &of_expr(e, fns, ops, locals));
            }
            acc
        }
        Expr::RecordUpdatePath(base, ups) => {
            let mut acc = of_expr(base, fns, ops, locals);
            for (_, op) in ups {
                acc = union(acc, &of_expr(op.expr(), fns, ops, locals));
            }
            acc
        }
        // A handler discharges the labels of the operations it intercepts. The
        // body's residual effect is its row minus those labels, plus whatever
        // the handler arms themselves perform.
        Expr::Handle(body, arms) => {
            let mut residual = of_expr(body, fns, ops, locals);
            let mut arm_eff = Effects::new();
            for arm in arms {
                match arm {
                    HandlerArm::Return(_, e) => {
                        arm_eff = union(arm_eff, &of_expr(e, fns, ops, locals));
                    }
                    HandlerArm::Op(op_name, _, _, e) => {
                        if let Some(info) = ops.get(op_name) {
                            residual.remove(&info.effect_name);
                        }
                        arm_eff = union(arm_eff, &of_expr(e, fns, ops, locals));
                    }
                    #[expect(
                        clippy::uninhabited_references,
                        reason = "Never is uninhabited in Core; arm is unreachable"
                    )]
                    HandlerArm::Sugar(never) => match *never {},
                }
            }
            union(residual, &arm_eff)
        }
        // Sugar is unrepresentable in `Expr<Core>`; the empty match witnesses
        // that type-level guarantee.
        #[expect(
            clippy::uninhabited_references,
            reason = "Never is uninhabited in Core; arm is unreachable"
        )]
        Expr::Sugar(never) | Expr::Marker(never) => match *never {},
        // mask injects its label: the masked ops bypass the innermost handler,
        // so the row must still demand an enclosing one. Set rows cannot count
        // duplicates, so one label stands for "at least one handler".
        Expr::Mask(eff, body) => union(of_expr(body, fns, ops, locals), &once(Sym::from(eff))),
    }
}

// The effect of applying the head of a call. A function value's row is the
// single source of truth, be the callee an effect operation, a builtin, a named
// function, or an annotated higher-order parameter.
fn head(f: &S<Expr<Core>>, fns: &BTreeMap<String, Effects>, ops: &Ops, locals: &Locals) -> Effects {
    if let Expr::Inst(inner, _) = &f.node {
        return head(inner, fns, ops, locals);
    }
    if let Expr::Var(name) = &f.node {
        if let Some(eff) = locals.get(name) {
            return eff.clone();
        }
        if let Some(info) = ops.get(name) {
            return once(info.effect_name);
        }
        if let Some(eff) = crate::tc::builtin_effects().get(name) {
            return eff.clone();
        }
        return fns.get(name).cloned().unwrap_or_default();
    }
    Effects::new()
}

fn shadow<'a>(locals: &Locals, names: impl Iterator<Item = &'a str>) -> Locals {
    let mut out = locals.clone();
    for n in names {
        out.remove(n);
    }
    out
}

fn once(s: Sym) -> Effects {
    std::iter::once(s).collect()
}

fn union(mut a: Effects, b: &Effects) -> Effects {
    a.extend(b.iter().copied());
    a
}

/// The strongly-connected components of `prog.fns`'s call graph, in dependency
/// order (every component a callee belongs to precedes the components that call
/// it). Each component is a recursion group: a singleton for an acyclic
/// definition (with a self-edge for self-recursion), or several members for a
/// mutually recursive cluster. Checking a component only after its callees lets
/// a forward reference (notably one into a stdlib module merged after the
/// prelude) see a generalized type rather than a structure-free stub, and lets a
/// mutually recursive group be inferred against shared monomorphic variables.
///
/// Members within a component are returned in declaration order. A shadowing
/// local that happens to share a top-level name only adds a spurious edge, which
/// is sound (it can never drop a real dependency).
#[must_use]
pub(crate) fn dep_sccs(prog: &Program<Core>) -> Vec<Vec<usize>> {
    const UNVISITED: u32 = u32::MAX;
    let n = prog.fns.len();
    let names: std::collections::BTreeMap<&str, usize> = prog
        .fns
        .iter()
        .enumerate()
        .map(|(i, d)| (d.name.as_str(), i))
        .collect();
    // Callee indices per function, deduped and in increasing order so the DFS is
    // deterministic.
    let deps: Vec<Vec<usize>> = prog
        .fns
        .iter()
        .map(|d| {
            let mut refs = std::collections::BTreeSet::new();
            collect_refs(&d.body, &names, &mut refs);
            refs.into_iter().collect()
        })
        .collect();
    // Iterative Tarjan over the index graph. An explicit work stack avoids
    // blowing the native stack on a deep prelude call chain. Tarjan emits each
    // component when its DFS root finishes, which is after all the component's
    // callees have finished, so components come out callee-before-caller already:
    // the emission order is the processing order, no reversal needed.
    let mut index = vec![UNVISITED; n];
    let mut lowlink = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut comp_stack: Vec<usize> = Vec::new();
    let mut next_index: u32 = 0;
    let mut sccs: Vec<Vec<usize>> = Vec::new();
    for start in 0..n {
        if index[start] != UNVISITED {
            continue;
        }
        index[start] = next_index;
        lowlink[start] = next_index;
        next_index += 1;
        comp_stack.push(start);
        on_stack[start] = true;
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&mut (v, ref mut i)) = work.last_mut() {
            if let Some(&w) = deps[v].get(*i) {
                *i += 1;
                if index[w] == UNVISITED {
                    index[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    comp_stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(index[w]);
                }
            } else {
                if lowlink[v] == index[v] {
                    let mut comp = Vec::new();
                    loop {
                        let u = comp_stack.pop().expect("Tarjan stack underflow");
                        on_stack[u] = false;
                        comp.push(u);
                        if u == v {
                            break;
                        }
                    }
                    comp.sort_unstable();
                    sccs.push(comp);
                }
                let low_v = lowlink[v];
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    lowlink[parent] = lowlink[parent].min(low_v);
                }
            }
        }
    }
    sccs
}

/// Whether a declaration's body refers to its own name: direct self-recursion,
/// i.e. a singleton strongly-connected component with a self-edge. Used only to
/// decide whether a body's type error warrants the polymorphic-recursion remedy
/// hint, so the over-approximation from a same-named shadowing local is harmless.
#[must_use]
pub(crate) fn is_self_recursive(d: &Decl<Core>) -> bool {
    let names: std::collections::BTreeMap<&str, usize> =
        std::iter::once((d.name.as_str(), 0)).collect();
    let mut refs = std::collections::BTreeSet::new();
    collect_refs(&d.body, &names, &mut refs);
    !refs.is_empty()
}

// Every top-level function `e` references, by canonical name. Constructors,
// effect ops, builtins, and locals are not in `names`, so they fall out; the
// over-approximation from a same-named shadowing local is harmless.
fn collect_refs(
    e: &S<Expr<Core>>,
    names: &std::collections::BTreeMap<&str, usize>,
    out: &mut std::collections::BTreeSet<usize>,
) {
    let mut go = |e| collect_refs(e, names, out);
    match &e.node {
        Expr::Var(n) => {
            if let Some(&i) = names.get(n.as_str()) {
                out.insert(i);
            }
        }
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Str(_) => {}
        Expr::Bin(_, a, b) | Expr::Index(a, b) | Expr::Pipe(a, b) => {
            go(a);
            go(b);
        }
        Expr::If(c, t, e2) => {
            go(c);
            go(t);
            go(e2);
        }
        Expr::Let(_, v, b) => {
            go(v);
            go(b);
        }
        Expr::Lam(_, b)
        | Expr::FieldAccess(b, _)
        | Expr::Inst(b, _)
        | Expr::Ann(b, _)
        | Expr::Mask(_, b) => go(b),
        Expr::Call(f, args) => {
            go(f);
            for a in args {
                go(a);
            }
        }
        Expr::Match(s, arms) => {
            go(s);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    go(g);
                }
                go(&arm.body);
            }
        }
        Expr::List(xs) | Expr::Tuple(xs) => {
            for x in xs {
                go(x);
            }
        }
        Expr::IndexSet(a, b, c) => {
            go(a);
            go(b);
            go(c);
        }
        Expr::RecordCreate(_, fields) => {
            for (_, v) in fields {
                go(v);
            }
        }
        Expr::RecordUpdate(base, _, fields) => {
            go(base);
            for (_, v) in fields {
                go(v);
            }
        }
        Expr::RecordUpdatePath(base, ups) => {
            go(base);
            for (_, op) in ups {
                go(op.expr());
            }
        }
        Expr::Handle(body, arms) => {
            go(body);
            for arm in arms {
                match arm {
                    HandlerArm::Return(_, e2) | HandlerArm::Op(_, _, _, e2) => go(e2),
                    #[expect(
                        clippy::uninhabited_references,
                        reason = "Never is uninhabited in Core"
                    )]
                    HandlerArm::Sugar(never) => match *never {},
                }
            }
        }
        #[expect(
            clippy::uninhabited_references,
            reason = "Never is uninhabited in Core"
        )]
        Expr::Sugar(never) | Expr::Marker(never) => match *never {},
    }
}
