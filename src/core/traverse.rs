//! The single structural descent over Core terms.
//!
//! Every whole-term pass and analysis used to re-enumerate the ~28 `Comp`
//! variants by hand, so adding a variant meant finding every walker or getting a
//! silent bug. This module is the one place the variants are enumerated, in two
//! disciplines:
//!
//! - [`Rewrite`]: a `Comp -> Comp` / `Value -> Value` transform that threads an
//!   immutable per-node context (`Ctx`) the implementor extends at binders. A
//!   pass overrides `comp`/`value` for the variants it transforms and calls
//!   `descend_comp`/`descend_value` for the rest.
//! - [`Visit`]: a read-only walk. The implementor carries its own state (and, if
//!   it cares about scope, its own binder stack), overriding `visit_comp`/
//!   `visit_value` for the variants it observes and calling `descend_*` for the
//!   rest.
//!
//! Both descents recurse everywhere, including into thunk bodies, lambdas, and
//! handler clauses, because a closure captures and a handler clause computes.
//! A frame-local discipline (stop at thunk/lambda/handler boundaries, track tail
//! position) is deliberately not provided here: `tailrec` needs it and is the
//! only consumer, so it stays bespoke until a second one appears.

use super::cbpv::{Comp, HandleOp, Value};

/// Whole-term rewrite threading an immutable context extended at binders.
///
/// `comp`/`value` default to `descend_*`; override them for the variants a pass
/// transforms. `descend_*` is the structural recursion: it rebuilds each node
/// from `self.comp`/`self.value` of its children, threading `cx` unchanged (a
/// pass that scopes a binder overrides the relevant variant and recurses with an
/// extended `cx` itself).
pub trait Rewrite {
    type Ctx;

    fn comp(&mut self, c: &Comp, cx: &Self::Ctx) -> Comp {
        self.descend_comp(c, cx)
    }

    fn value(&mut self, v: &Value, cx: &Self::Ctx) -> Value {
        self.descend_value(v, cx)
    }

    fn descend_comp(&mut self, c: &Comp, cx: &Self::Ctx) -> Comp {
        match c {
            Comp::Return(v) => Comp::Return(self.value(v, cx)),
            Comp::Bind(a, x, b) => {
                Comp::Bind(Box::new(self.comp(a, cx)), *x, Box::new(self.comp(b, cx)))
            }
            Comp::Force(v) => Comp::Force(self.value(v, cx)),
            Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(self.comp(b, cx))),
            Comp::App(f, args) => Comp::App(
                Box::new(self.comp(f, cx)),
                args.iter().map(|a| self.value(a, cx)).collect(),
            ),
            Comp::If(c0, t, e) => Comp::If(
                self.value(c0, cx),
                Box::new(self.comp(t, cx)),
                Box::new(self.comp(e, cx)),
            ),
            Comp::Prim(op, a, b) => Comp::Prim(*op, self.value(a, cx), self.value(b, cx)),
            Comp::Call(n, args) => Comp::Call(*n, args.iter().map(|a| self.value(a, cx)).collect()),
            Comp::Io(op, args) => Comp::Io(*op, args.iter().map(|v| self.value(v, cx)).collect()),
            Comp::Error(v) => Comp::Error(self.value(v, cx)),
            Comp::Case(v, arms) => Comp::Case(
                self.value(v, cx),
                arms.iter()
                    .map(|(p, b)| (p.clone(), self.comp(b, cx)))
                    .collect(),
            ),
            Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, self.value(v, cx)),
            Comp::Neg(l, v) => Comp::Neg(*l, self.value(v, cx)),
            Comp::Do(n, args) => Comp::Do(*n, args.iter().map(|a| self.value(a, cx)).collect()),
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => Comp::Handle {
                body: Box::new(self.comp(body, cx)),
                return_var: *return_var,
                return_body: return_body.as_ref().map(|b| Box::new(self.comp(b, cx))),
                ops: ops
                    .iter()
                    .map(|o| HandleOp {
                        name: o.name,
                        params: o.params.clone(),
                        resume: o.resume,
                        body: self.comp(&o.body, cx),
                    })
                    .collect(),
            },
            Comp::Mask(es, b) => Comp::Mask(es.clone(), Box::new(self.comp(b, cx))),
            Comp::StrBuiltin(b, args) => {
                Comp::StrBuiltin(*b, args.iter().map(|a| self.value(a, cx)).collect())
            }
            Comp::Dup(v) => Comp::Dup(self.value(v, cx)),
            Comp::Drop(v) => Comp::Drop(self.value(v, cx)),
            Comp::WithReuse { token, freed, body } => Comp::WithReuse {
                token: *token,
                freed: self.value(freed, cx),
                body: Box::new(self.comp(body, cx)),
            },
            Comp::Reuse(t, v) => Comp::Reuse(*t, self.value(v, cx)),
            Comp::RefNew(v) => Comp::RefNew(self.value(v, cx)),
            Comp::RefGet(v) => Comp::RefGet(self.value(v, cx)),
            Comp::RefSet(a, b) => Comp::RefSet(self.value(a, cx), self.value(b, cx)),
        }
    }

    fn descend_value(&mut self, v: &Value, cx: &Self::Ctx) -> Value {
        match v {
            Value::Thunk(c) => Value::Thunk(Box::new(self.comp(c, cx))),
            Value::Ctor(n, t, fs) => {
                Value::Ctor(*n, *t, fs.iter().map(|f| self.value(f, cx)).collect())
            }
            Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| self.value(f, cx)).collect()),
            _ => v.clone(),
        }
    }
}

/// Read-only walk. The implementor carries its own state (and, if scope-aware,
/// its own binder stack), overriding `visit_*` for the variants it observes.
pub trait Visit {
    fn visit_comp(&mut self, c: &Comp) {
        self.descend_comp(c);
    }

    fn visit_value(&mut self, v: &Value) {
        self.descend_value(v);
    }

    fn descend_comp(&mut self, c: &Comp) {
        match c {
            Comp::Return(v)
            | Comp::Force(v)
            | Comp::Error(v)
            | Comp::FloatBuiltin(_, v)
            | Comp::Neg(_, v)
            | Comp::Dup(v)
            | Comp::Drop(v)
            | Comp::Reuse(_, v)
            | Comp::RefNew(v)
            | Comp::RefGet(v) => self.visit_value(v),
            Comp::RefSet(a, b) | Comp::Prim(_, a, b) => {
                self.visit_value(a);
                self.visit_value(b);
            }
            Comp::Bind(a, _, b) => {
                self.visit_comp(a);
                self.visit_comp(b);
            }
            Comp::App(f, args) => {
                self.visit_comp(f);
                for a in args {
                    self.visit_value(a);
                }
            }
            Comp::If(v, t, e) => {
                self.visit_value(v);
                self.visit_comp(t);
                self.visit_comp(e);
            }
            Comp::Call(_, args)
            | Comp::Do(_, args)
            | Comp::StrBuiltin(_, args)
            | Comp::Io(_, args) => {
                for a in args {
                    self.visit_value(a);
                }
            }
            Comp::Lam(_, b) | Comp::Mask(_, b) => self.visit_comp(b),
            Comp::Case(v, arms) => {
                self.visit_value(v);
                for (_, b) in arms {
                    self.visit_comp(b);
                }
            }
            Comp::WithReuse { freed, body, .. } => {
                self.visit_value(freed);
                self.visit_comp(body);
            }
            Comp::Handle {
                body,
                return_body,
                ops,
                ..
            } => {
                self.visit_comp(body);
                if let Some(rb) = return_body {
                    self.visit_comp(rb);
                }
                for op in ops {
                    self.visit_comp(&op.body);
                }
            }
        }
    }

    fn descend_value(&mut self, v: &Value) {
        match v {
            Value::Thunk(c) => self.visit_comp(c),
            Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
                for f in fs {
                    self.visit_value(f);
                }
            }
            _ => {}
        }
    }
}
