use std::collections::BTreeMap;

use super::ty::Effects;
use crate::sym::Sym;
use crate::syntax::ast::{Core, Decl, Expr, HandlerArm, Program, Row, Ty, S};
use crate::tc::EffOpInfo;

type Ops = BTreeMap<String, EffOpInfo>;

// In-scope bindings whose value is a function carrying a (statically known)
// effect row: annotated higher-order parameters. Applying one performs its row.
type Locals = BTreeMap<String, Effects>;

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
            // A lookup is not a panic: the map was seeded from prog.fns, but an
            // absent function legitimately means "no effects" (the same
            // Effects::new() the map starts with), so fall back rather than
            // asserting presence.
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
            for (_, e) in ups {
                acc = union(acc, &of_expr(e, fns, ops, locals));
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
