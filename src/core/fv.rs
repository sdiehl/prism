// The one free-variable computation over core terms. Binders (let, lambda
// params, pattern vars, handler return/op params, resume) are subtracted.
// Thunk bodies are walked since a closure captures its free vars.

use std::collections::BTreeSet;

use crate::sym::Sym;

use super::cbpv::{Comp, CorePat, Value};
use super::traverse::Visit;

pub type Set = BTreeSet<Sym>;

#[must_use]
pub fn comp(c: &Comp) -> Set {
    let mut f = Fv::default();
    f.visit_comp(c);
    f.free
}

#[must_use]
pub fn value(v: &Value) -> Set {
    let mut f = Fv::default();
    f.visit_value(v);
    f.free
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

// A `Var` is free unless an enclosing binder shadows it. The binder stack is a
// plain `Vec` (not a set) so shadowing nests and unbinds correctly; equality of
// the resulting set with the subtractive definition is what the tests pin.
#[derive(Default)]
struct Fv {
    free: Set,
    bound: Vec<Sym>,
}

impl Fv {
    fn under(&mut self, names: &[Sym], body: &Comp) {
        self.bound.extend_from_slice(names);
        self.visit_comp(body);
        self.bound.truncate(self.bound.len() - names.len());
    }
}

impl Visit for Fv {
    fn visit_value(&mut self, v: &Value) {
        if let Value::Var(x) = v {
            if !self.bound.contains(x) {
                self.free.insert(*x);
            }
        } else {
            self.descend_value(v);
        }
    }

    fn visit_comp(&mut self, c: &Comp) {
        match c {
            Comp::Bind(m, x, n) => {
                self.visit_comp(m);
                self.under(&[*x], n);
            }
            Comp::Lam(ps, b) => self.under(ps, b),
            Comp::Case(v, arms) => {
                self.visit_value(v);
                for (p, body) in arms {
                    let mut pv = Set::new();
                    pat_vars(p, &mut pv);
                    self.under(&pv.into_iter().collect::<Vec<_>>(), body);
                }
            }
            // `token` is bound over `body`; the freed cell is named in the
            // enclosing scope, so it stays free here.
            Comp::WithReuse { token, freed, body } => {
                self.visit_value(freed);
                self.under(&[*token], body);
            }
            // The token is a free reference resolved to the `WithReuse` binder
            // (unless one is in scope, e.g. nested reuse).
            Comp::Reuse(tok, v) => {
                if !self.bound.contains(tok) {
                    self.free.insert(*tok);
                }
                self.visit_value(v);
            }
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                self.visit_comp(body);
                if let Some(rb) = return_body {
                    self.under(&return_var.iter().copied().collect::<Vec<_>>(), rb);
                }
                for op in ops {
                    let mut names = op.params.clone();
                    names.push(op.resume);
                    self.under(&names, &op.body);
                }
            }
            _ => self.descend_comp(c),
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
