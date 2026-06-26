//! Surface lints: unused local bindings and shadowed names.
//!
//! A read-only scope walk over the resolved surface program, run regardless of
//! whether name canonicalization fired (it only does for multi-module builds).
//! It warns when a local binding is never used, or shadows one already in scope.
//!
//! Two filters keep the output signal: a binding whose name starts with `_` is
//! exempt (the conventional "intentionally unused" marker), and only bindings in
//! the user's own source are reported. The prelude is prepended, so its spans
//! fall before `user_start` and its many internal bindings never surface as
//! noise. Handler-arm binders (the continuation and op parameters, frequently
//! and legitimately unused) are walked for their uses but not themselves linted.

use marginalia::Span;

use crate::syntax::ast::{
    CatchArm, Decl, Expr, HandlerArm, Pattern, Program, Qualifier, Sugar, SugarArm, Surface, S,
};
use crate::tc::Warning;

struct Local {
    name: String,
    span: Span,
    uses: u32,
}

struct Lints {
    scope: Vec<Local>,
    warnings: Vec<Warning>,
    user_start: usize,
}

/// Collect unused-binding and shadowed-name warnings for the user's own source.
///
/// `user_start` is the byte offset where user code begins (past any prepended
/// prelude); bindings before it are the prelude's and are not reported.
#[must_use]
pub fn lint_bindings(prog: &Program, user_start: usize) -> Vec<Warning> {
    let mut l = Lints {
        scope: Vec::new(),
        warnings: Vec::new(),
        user_start,
    };
    for d in &prog.fns {
        if d.span.start >= user_start {
            l.decl(d);
        }
    }
    for inst in &prog.instances {
        for m in &inst.methods {
            if m.span.start >= user_start {
                l.decl(m);
            }
        }
    }
    l.warnings
}

impl Lints {
    const fn in_user(&self, span: Span) -> bool {
        span.start >= self.user_start
    }

    // Bind `name` at `span`. With `check_shadow`, warn first if it shadows an
    // enclosing binding (sibling scopes are already popped, so an in-scope match
    // is a true shadow). A rebind whose RHS consumes the shadowed binding
    // (`let s = f(s)`) passes `check_shadow = false`, since that is intentional.
    fn bind(&mut self, name: &str, span: Span, check_shadow: bool) {
        if check_shadow
            && !name.starts_with('_')
            && self.in_user(span)
            && self.scope.iter().any(|b| b.name == name)
        {
            self.warnings.push(Warning {
                span,
                msg: format!("`{name}` shadows an existing binding"),
            });
        }
        self.scope.push(Local {
            name: name.to_string(),
            span,
            uses: 0,
        });
    }

    fn use_name(&mut self, name: &str) {
        if let Some(b) = self.scope.iter_mut().rev().find(|b| b.name == name) {
            b.uses += 1;
        }
    }

    // Use count of the innermost binding of `name`, or 0 if none is in scope.
    // Compared across a RHS walk to tell a rebind from a fresh shadow.
    fn uses_of(&self, name: &str) -> u32 {
        self.scope
            .iter()
            .rev()
            .find(|b| b.name == name)
            .map_or(0, |b| b.uses)
    }

    // Pop bindings back to `base`, warning on any unused user binding.
    fn pop_to(&mut self, base: usize) {
        for b in self.scope.drain(base..) {
            if b.uses == 0 && !b.name.starts_with('_') && self.user_start <= b.span.start {
                self.warnings.push(Warning {
                    span: b.span,
                    msg: format!("unused binding `{}`", b.name),
                });
            }
        }
    }

    fn decl(&mut self, d: &Decl) {
        let base = self.scope.len();
        for p in &d.params {
            self.bind(&p.name, d.span, true);
        }
        // `where` bindings are let*-style: each RHS sees the ones before it.
        for (name, rhs) in &d.wheres {
            self.rebindable(name, d.span, rhs);
        }
        self.expr(&d.body);
        self.pop_to(base);
    }

    // Bind `name` for a `let`/`var`/`where` after walking its RHS, treating it as
    // a rebind (no shadow warning) when the RHS used the binding it shadows.
    fn rebindable(&mut self, name: &str, span: Span, rhs: &S<Expr>) {
        let before = self.uses_of(name);
        self.expr(rhs);
        let rebind = self.uses_of(name) > before;
        self.bind(name, span, !rebind);
    }

    fn pat(&mut self, p: &S<Pattern>) {
        match &p.node {
            Pattern::Var(x) => self.bind(x, p.span, true),
            Pattern::Ctor(_, ps) | Pattern::Tuple(ps) => {
                for q in ps {
                    self.pat(q);
                }
            }
            Pattern::Record(_, fs, _) => {
                for (_, q) in fs {
                    self.pat(q);
                }
            }
            _ => {}
        }
    }

    // A handler arm's body, walked for uses; its binders are not linted.
    fn arm_body(&mut self, a: &HandlerArm) {
        let body = match a {
            HandlerArm::Return(_, b)
            | HandlerArm::Op(_, _, _, b)
            | HandlerArm::Sugar(
                SugarArm::Fun(_, _, b) | SugarArm::Final(_, _, b) | SugarArm::Val(_, b),
            ) => b,
        };
        self.expr(body);
    }

    fn catch_arm(&mut self, a: &CatchArm) {
        let base = self.scope.len();
        for b in &a.binders {
            self.bind(b, a.span, true);
        }
        self.expr(&a.body);
        self.pop_to(base);
    }

    fn quals(&mut self, quals: &[Qualifier]) {
        for q in quals {
            match q {
                Qualifier::Guard(g) => self.expr(g),
                Qualifier::Bind(y, e) => {
                    self.expr(e);
                    self.bind(y, e.span, true);
                }
            }
        }
    }

    fn sugar(&mut self, s: &Sugar<Surface>, span: Span) {
        match s {
            Sugar::VarDecl(x, init, rest) => {
                let base = self.scope.len();
                self.rebindable(x, span, init);
                self.expr(rest);
                self.pop_to(base);
            }
            // Assigning a var counts as using it (a write-only var is not flagged).
            Sugar::Assign(x, v) => {
                self.use_name(x);
                self.expr(v);
            }
            Sugar::IndexAssign(recv, key, v) => {
                self.expr(recv);
                self.expr(key);
                self.expr(v);
            }
            Sugar::Throw(_, args) => {
                for a in args {
                    self.expr(a);
                }
            }
            Sugar::TryCatch(body, arms) => {
                self.expr(body);
                for a in arms {
                    self.catch_arm(a);
                }
            }
            Sugar::For(x, src, quals, body) => {
                self.expr(src);
                let base = self.scope.len();
                self.bind(x, span, true);
                self.quals(quals);
                self.expr(body);
                self.pop_to(base);
            }
            Sugar::Comp(head, x, src, quals) => {
                self.expr(src);
                let base = self.scope.len();
                self.bind(x, span, true);
                self.quals(quals);
                self.expr(head);
                self.pop_to(base);
            }
            Sugar::NamedHandle(name, body, arms) => {
                let base = self.scope.len();
                self.bind(name, span, true);
                self.expr(body);
                self.pop_to(base);
                for a in arms {
                    self.arm_body(a);
                }
            }
            Sugar::Default(a, b) | Sugar::Transact(a, b) | Sugar::Compose(_, a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Sugar::OptChain(e, _) | Sugar::Return(e) => self.expr(e),
            Sugar::Range(pre, hi) => {
                for x in pre {
                    self.expr(x);
                }
                self.expr(hi);
            }
            Sugar::While(cond, body) => {
                if let Some(c) = cond {
                    self.expr(c);
                }
                self.expr(body);
            }
            Sugar::Break | Sugar::Continue => {}
        }
    }

    fn expr(&mut self, e: &S<Expr>) {
        match &e.node {
            Expr::Var(x) => self.use_name(x),
            Expr::Sugar(s) => self.sugar(s, e.span),
            Expr::Let(x, v, b) => {
                let base = self.scope.len();
                self.rebindable(x, e.span, v);
                self.expr(b);
                self.pop_to(base);
            }
            Expr::Lam(ps, b) => {
                let base = self.scope.len();
                for p in ps {
                    self.bind(&p.name, e.span, true);
                }
                self.expr(b);
                self.pop_to(base);
            }
            Expr::Match(scrut, arms) => {
                self.expr(scrut);
                for a in arms {
                    let base = self.scope.len();
                    self.pat(&a.pat);
                    if let Some(g) = &a.guard {
                        self.expr(g);
                    }
                    self.expr(&a.body);
                    self.pop_to(base);
                }
            }
            Expr::Bin(_, a, b) | Expr::Pipe(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Expr::If(c, t, f) => {
                self.expr(c);
                self.expr(t);
                self.expr(f);
            }
            Expr::Call(f, args) => {
                self.expr(f);
                for a in args {
                    self.expr(a);
                }
            }
            Expr::List(es) | Expr::Tuple(es) => {
                for x in es {
                    self.expr(x);
                }
            }
            Expr::FieldAccess(b, _) | Expr::Inst(b, _) | Expr::Ann(b, _) | Expr::Mask(_, b) => {
                self.expr(b);
            }
            Expr::Index(recv, key) => {
                self.expr(recv);
                self.expr(key);
            }
            Expr::IndexSet(recv, key, val) => {
                self.expr(recv);
                self.expr(key);
                self.expr(val);
            }
            Expr::RecordCreate(_, fs) => {
                for (_, v) in fs {
                    self.expr(v);
                }
            }
            Expr::RecordUpdate(b, _, fs) => {
                self.expr(b);
                for (_, v) in fs {
                    self.expr(v);
                }
            }
            Expr::RecordUpdatePath(b, ups) => {
                self.expr(b);
                for (steps, op) in ups {
                    for s in steps {
                        if let Some(e) = s.index_expr() {
                            self.expr(e);
                        }
                    }
                    self.expr(op.expr());
                }
            }
            Expr::Handle(b, arms) => {
                self.expr(b);
                for a in arms {
                    self.arm_body(a);
                }
            }
            Expr::Int(_)
            | Expr::Float(_)
            | Expr::Char(_)
            | Expr::Bool(_)
            | Expr::Unit
            | Expr::Str(_)
            | Expr::Marker(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::lint_bindings;
    use crate::parse::parse;

    // Lint a bare program (no prelude prefix, so `user_start` is 0).
    fn lints(src: &str) -> Vec<String> {
        let prog = parse(src).expect("parses").program;
        lint_bindings(&prog, 0).into_iter().map(|w| w.msg).collect()
    }

    #[test]
    fn flags_unused_param_let_and_shadow() {
        let ws = lints("fn f(x : Int, y : Int) : Int =\n  let z = 10\n  let x = 5\n  x + 1\n");
        assert!(
            ws.iter().any(|w| w.contains("unused binding `y`")),
            "{ws:?}"
        );
        assert!(
            ws.iter().any(|w| w.contains("unused binding `z`")),
            "{ws:?}"
        );
        assert!(ws.iter().any(|w| w.contains("`x` shadows")), "{ws:?}");
    }

    #[test]
    fn quiet_on_rebind_and_underscore() {
        // `let s = s + 1` consumes the shadowed `s` (a rebind, not a fresh
        // shadow), and `_x` is the intentionally-unused marker.
        let ws = lints("fn g(s : Int, _x : Int) : Int =\n  let s = s + 1\n  s\n");
        assert!(ws.is_empty(), "{ws:?}");
    }

    #[test]
    fn flags_unused_pattern_binding() {
        let ws = lints("fn h(p : (Int, Int)) : Int =\n  match p of\n    (a, b) => a\n");
        assert!(
            ws.iter().any(|w| w.contains("unused binding `b`")),
            "{ws:?}"
        );
        assert!(!ws.iter().any(|w| w.contains("`a`")), "{ws:?}");
    }
}
