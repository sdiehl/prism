// The one free-variable computation over core terms. Binders (let, lambda
// params, pattern vars, handler return/op params, resume) are subtracted.
// Thunk bodies are walked since a closure captures its free vars.

use std::collections::BTreeSet;

use crate::sym::Sym;

use super::cbpv::{Comp, CorePat, Value};

pub type Set = BTreeSet<Sym>;

#[must_use]
pub fn comp(c: &Comp) -> Set {
    let mut s = Set::new();
    free_comp(c, &mut s);
    s
}

#[must_use]
pub fn value(v: &Value) -> Set {
    let mut s = Set::new();
    free_val(v, &mut s);
    s
}

pub fn comp_without<'a, I: IntoIterator<Item = &'a Sym>>(c: &Comp, binders: I) -> Set {
    let mut s = comp(c);
    for b in binders {
        s.remove(b);
    }
    s
}

pub fn pat_vars(p: &CorePat, out: &mut Set) {
    match p {
        CorePat::Var(x) => {
            out.insert(*x);
        }
        CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => {
            out.extend(fields.iter().flatten().copied());
        }
        CorePat::Wild => {}
    }
}

fn free_val(v: &Value, out: &mut Set) {
    match v {
        Value::Var(x) => {
            out.insert(*x);
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().for_each(|f| free_val(f, out)),
        Value::Thunk(c) => free_comp(c, out),
        _ => {}
    }
}

fn free_comp(c: &Comp, out: &mut Set) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::ReuseToken(v) => free_val(v, out),
        Comp::Reuse(t, v) => {
            free_val(t, out);
            free_val(v, out);
        }
        Comp::Bind(m, x, n) => {
            free_comp(m, out);
            out.extend(comp_without(n, [x]));
        }
        Comp::App(f, args) => {
            free_comp(f, out);
            for a in args {
                free_val(a, out);
            }
        }
        Comp::If(v, t, e) => {
            free_val(v, out);
            free_comp(t, out);
            free_comp(e, out);
        }
        Comp::Prim(_, a, b) => {
            free_val(a, out);
            free_val(b, out);
        }
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) => {
            for a in args {
                free_val(a, out);
            }
        }
        Comp::ReadInt | Comp::ReadLine | Comp::PrintNl | Comp::Rand => {}
        Comp::Lam(ps, b) => out.extend(comp_without(b, ps)),
        Comp::Case(v, arms) => {
            free_val(v, out);
            for (p, body) in arms {
                let mut pv = Set::new();
                pat_vars(p, &mut pv);
                out.extend(comp(body).difference(&pv).copied());
            }
        }
        Comp::Mask(_, b) => free_comp(b, out),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => {
            free_comp(body, out);
            if let Some(rb) = return_body {
                out.extend(comp_without(rb, return_var.iter()));
            }
            for op in ops {
                let mut s = comp_without(&op.body, &op.params);
                s.remove(&op.resume);
                out.extend(s);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{comp, value, Set};
    use crate::core::cbpv::{Comp, CoreOp, CorePat, HandleOp, Value};
    use crate::sym::Sym;

    fn s(name: &str) -> Sym {
        Sym::new(name)
    }
    fn set(names: &[&str]) -> Set {
        names.iter().map(|n| Sym::new(n)).collect()
    }
    fn var(name: &str) -> Value {
        Value::Var(s(name))
    }

    // A let binder is subtracted from its continuation, but a use of the same
    // name in the bound computation (which runs outside the binder) stays free.
    #[test]
    fn bind_subtracts_binder_not_outer_use() {
        let c = Comp::Bind(
            Box::new(Comp::Return(var("a"))),
            s("x"),
            Box::new(Comp::Prim(CoreOp::Add, var("x"), var("b"))),
        );
        assert_eq!(comp(&c), set(&["a", "b"]));
    }

    // Lambda params are subtracted; captured free vars survive.
    #[test]
    fn lam_subtracts_params_keeps_captures() {
        let c = Comp::Lam(
            vec![s("x"), s("y")],
            Box::new(Comp::App(
                Box::new(Comp::Force(var("f"))),
                vec![var("x"), var("z")],
            )),
        );
        assert_eq!(comp(&c), set(&["f", "z"]));
    }

    // A case arm subtracts the pattern's bound fields but keeps the scrutinee
    // and any free var used in the body.
    #[test]
    fn case_subtracts_pattern_vars() {
        let arm = (
            CorePat::Ctor(s("C"), vec![Some(s("a")), Some(s("b"))]),
            Comp::Prim(CoreOp::Add, var("a"), var("w")),
        );
        let c = Comp::Case(var("scrut"), vec![arm]);
        assert_eq!(comp(&c), set(&["scrut", "w"]));
    }

    // rc descends into closures, so a thunk's captures (including nested in a
    // constructor) are free vars of the enclosing value.
    #[test]
    fn thunk_and_ctor_fields_are_walked() {
        let v = Value::Ctor(
            s("C"),
            0,
            vec![var("p"), Value::Thunk(Box::new(Comp::Return(var("q"))))],
        );
        assert_eq!(value(&v), set(&["p", "q"]));
    }

    // A handle subtracts the return-clause binder, and each op clause subtracts
    // its params and its resume continuation, keeping every other free var.
    #[test]
    fn handle_subtracts_return_op_and_resume_binders() {
        let op = HandleOp {
            name: s("ask"),
            params: vec![s("oa")],
            resume: s("k"),
            // uses the bound resume `k`, the bound param `oa`, and a free `of`.
            body: Comp::App(Box::new(Comp::Force(var("k"))), vec![var("oa"), var("of")]),
        };
        let c = Comp::Handle {
            body: Box::new(Comp::Return(var("bd"))),
            return_var: Some(s("rv")),
            // uses the bound `rv` and a free `ro`.
            return_body: Some(Box::new(Comp::Prim(CoreOp::Add, var("rv"), var("ro")))),
            ops: vec![op],
        };
        assert_eq!(comp(&c), set(&["bd", "ro", "of"]));
    }
}
