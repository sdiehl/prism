// The one free-variable computation over core terms. Binders (let, lambda
// params, pattern vars, handler return/op params, resume) are subtracted.
// Thunk bodies are walked since a closure captures its free vars.

use std::collections::BTreeSet;

use prism_common::sym::Sym;

use super::cbpv::{Comp, CorePat, Value};
use super::traverse::Visit;

pub type Set = BTreeSet<Sym>;

#[must_use]
pub fn comp(c: &Comp) -> Set {
    let mut f = Fv::default();
    f.walk_comp(c);
    f.free
}

#[must_use]
pub fn value(v: &Value) -> Set {
    let mut f = Fv::default();
    f.walk_value(v);
    f.free
}

pub fn comp_without<'a, I: IntoIterator<Item = &'a Sym>>(c: &Comp, binders: I) -> Set {
    let mut s = comp(c);
    for b in binders {
        s.remove(b);
    }
    s
}

/// Collect every name bound anywhere inside `c`, regardless of scope.
///
/// This includes let and lambda binders, case patterns, reuse tokens, and
/// handler binders. A caller can conservatively retain an outer-binder fact
/// only when the name does not occur in this set.
#[must_use]
pub fn rebound(c: &Comp) -> Set {
    let mut r = Rebound::default();
    r.walk_comp(c);
    r.bound
}

// Collects binder names without scoping: the caller wants the union of every
// binding site, so shadow nesting is irrelevant here.
#[derive(Default)]
struct Rebound {
    bound: Set,
}

impl Visit for Rebound {
    fn comp(&mut self, c: &Comp) -> bool {
        match c {
            Comp::Bind(_, x, _) => {
                self.bound.insert(*x);
            }
            Comp::Lam(ps, _) => self.bound.extend(ps.iter().copied()),
            Comp::Case(_, arms) => {
                for (p, _) in arms {
                    pat_vars(p, &mut self.bound);
                }
            }
            Comp::WithReuse { token, .. } => {
                self.bound.insert(*token);
            }
            Comp::Handle {
                return_var, ops, ..
            } => {
                self.bound.extend(return_var.iter().copied());
                for op in ops {
                    self.bound.extend(op.params.iter().copied());
                    self.bound.insert(op.resume);
                }
            }
            _ => {}
        }
        true
    }
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
// the resulting set with the subtractive definition is what the tests check.
#[derive(Default)]
struct Fv {
    free: Set,
    bound: Vec<Sym>,
}

impl Visit for Fv {
    fn enter_scope(&mut self, binders: &[Sym]) {
        self.bound.extend_from_slice(binders);
    }

    fn exit_scope(&mut self, binders: &[Sym]) {
        self.bound.truncate(self.bound.len() - binders.len());
    }

    fn value(&mut self, v: &Value) -> bool {
        if let Value::Var(x) = v {
            if !self.bound.contains(x) {
                self.free.insert(*x);
            }
        }
        true
    }

    fn comp(&mut self, c: &Comp) -> bool {
        if let Comp::Reuse(token, _) = c {
            if !self.bound.contains(token) {
                self.free.insert(*token);
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::{comp, value, Set};
    use crate::core::cbpv::{CheckedHandler, Comp, CoreOp, CorePat, HandleOp, Value};
    use prism_common::sym::Sym;

    const DEEP_FREE_VARIABLE_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

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
            ops: CheckedHandler::new(vec![op]).unwrap(),
        };
        assert_eq!(comp(&c), set(&["bd", "ro", "of"]));
    }

    #[test]
    fn free_variables_handle_deep_binds_on_an_ordinary_stack() {
        let result = std::thread::Builder::new()
            .name("deep-raw-free-variables".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut body = Comp::Return(var("outside"));
                for _ in 0..DEEP_FREE_VARIABLE_DEPTH {
                    body = Comp::Bind(
                        Box::new(Comp::Return(Value::Int(0))),
                        s("shadow"),
                        Box::new(body),
                    );
                }
                assert_eq!(comp(&body), set(&["outside"]));
                std::mem::forget(body);
            })
            .expect("spawning deep raw free-variable test")
            .join();
        if let Err(payload) = result {
            std::panic::resume_unwind(payload);
        }
    }
}
