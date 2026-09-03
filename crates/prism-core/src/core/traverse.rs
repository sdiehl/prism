//! The single structural descent over Core terms.
//!
//! Every whole-term pass and analysis used to re-enumerate the ~28 `Comp`
//! variants by hand, so adding a variant meant finding every walker or getting a
//! silent bug. This module is the one place the variants are enumerated, in two
//! disciplines:
//!
//! - [`Rewrite`]: an iterative `Comp -> Comp` / `Value -> Value` transform with
//!   enter/leave hooks and an immutable context extended at binders.
//! - [`Visit`]: an iterative read-only walk with canonical binder scopes. A
//!   policy overrides node hooks and returns `false` to prune a subtree.
//!
//! Both descents reach thunk bodies, lambdas, and handler clauses, because a
//! closure captures and a handler clause computes.
//! A frame-local discipline (stop at thunk/lambda/handler boundaries, track tail
//! position) is deliberately not provided here: `tailrec` needs it and is the
//! only consumer, so it stays bespoke until a second one appears.

use std::rc::Rc;

use prism_common::sym::Sym;

use super::cbpv::{Comp, CorePat, HandleOp, Value};
use super::work;

/// Whether an enter hook replaces a node or descends into its children.
#[derive(Debug)]
pub enum RewriteControl<T> {
    Descend,
    Replace(T),
}

/// Whole-term rewrite over one explicit reconstruction worklist.
///
/// Enter hooks may replace and prune a node. Leave hooks receive the node after
/// all children have been rebuilt. Binder scopes derive a child context once,
/// when that scoped child is reached in left-to-right traversal order.
pub trait Rewrite {
    type Ctx: Clone;

    fn under_scope(&mut self, _binders: &[Sym], cx: &Self::Ctx) -> Self::Ctx {
        cx.clone()
    }

    fn enter_comp(&mut self, _comp: &Comp, _cx: &Self::Ctx) -> RewriteControl<Comp> {
        RewriteControl::Descend
    }

    fn enter_value(&mut self, _value: &Value, _cx: &Self::Ctx) -> RewriteControl<Value> {
        RewriteControl::Descend
    }

    fn leave_comp(&mut self, _source: &Comp, rewritten: Comp, _cx: &Self::Ctx) -> Comp {
        rewritten
    }

    fn leave_value(&mut self, _source: &Value, rewritten: Value, _cx: &Self::Ctx) -> Value {
        rewritten
    }

    fn rewrite_comp(&mut self, comp: &Comp, cx: &Self::Ctx) -> Comp
    where
        Self: Sized,
    {
        let root = RebuildFrame::Comp {
            source: comp,
            cx: Rc::new(cx.clone()),
            depth: 1,
            run_hook: true,
        };
        expect_comp(rewrite(self, root))
    }

    fn rewrite_value(&mut self, value: &Value, cx: &Self::Ctx) -> Value
    where
        Self: Sized,
    {
        let root = RebuildFrame::Value {
            source: value,
            cx: Rc::new(cx.clone()),
            depth: 1,
            run_hook: true,
        };
        expect_value(rewrite(self, root))
    }
}

/// Rebuild `c` by applying `g` to every immediate child.
///
/// Applies to every immediate sub-computation and, through the default value
/// descent, every thunk body a value holds. This is the
/// recognize-or-leave shape a `Comp -> Comp` pass takes for the variants it does
/// not itself transform, routed through the canonical reconstruction worklist.
pub fn map_children<G: FnMut(&Comp) -> Comp>(c: &Comp, g: &mut G) -> Comp {
    let root = RebuildFrame::Comp {
        source: c,
        cx: Rc::new(()),
        depth: 1,
        run_hook: false,
    };
    expect_comp(rewrite(&mut Kids(g), root))
}

struct Kids<'a, G>(&'a mut G);

impl<G: FnMut(&Comp) -> Comp> Rewrite for Kids<'_, G> {
    type Ctx = ();

    fn enter_comp(&mut self, comp: &Comp, _cx: &Self::Ctx) -> RewriteControl<Comp> {
        RewriteControl::Replace((self.0)(comp))
    }
}

enum Rebuilt {
    Comp(Comp),
    Value(Value),
}

enum RebuildFrame<'a, C> {
    Comp {
        source: &'a Comp,
        cx: Rc<C>,
        depth: u64,
        run_hook: bool,
    },
    Value {
        source: &'a Value,
        cx: Rc<C>,
        depth: u64,
        run_hook: bool,
    },
    ScopedComp {
        binders: Scope,
        source: &'a Comp,
        cx: Rc<C>,
        depth: u64,
    },
    LeaveComp {
        source: &'a Comp,
        cx: Rc<C>,
        mark: usize,
    },
    LeaveValue {
        source: &'a Value,
        cx: Rc<C>,
        mark: usize,
    },
}

fn rewrite<R: Rewrite>(rewriter: &mut R, root: RebuildFrame<'_, R::Ctx>) -> Rebuilt {
    let mut frames = vec![root];
    let mut rebuilt = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            RebuildFrame::Comp {
                source,
                cx,
                depth,
                run_hook,
            } => {
                if run_hook {
                    if let RewriteControl::Replace(replacement) =
                        rewriter.enter_comp(source, Rc::as_ref(&cx))
                    {
                        rebuilt.push(Rebuilt::Comp(replacement));
                        continue;
                    }
                }
                work::rebuild_at_depth(depth);
                let mark = rebuilt.len();
                frames.push(RebuildFrame::LeaveComp {
                    source,
                    cx: Rc::clone(&cx),
                    mark,
                });
                push_rebuild_comp_children(&mut frames, source, &cx, depth + 1);
            }
            RebuildFrame::Value {
                source,
                cx,
                depth,
                run_hook,
            } => {
                if run_hook {
                    if let RewriteControl::Replace(replacement) =
                        rewriter.enter_value(source, Rc::as_ref(&cx))
                    {
                        rebuilt.push(Rebuilt::Value(replacement));
                        continue;
                    }
                }
                work::rebuild_at_depth(depth);
                let mark = rebuilt.len();
                frames.push(RebuildFrame::LeaveValue {
                    source,
                    cx: Rc::clone(&cx),
                    mark,
                });
                push_rebuild_value_children(&mut frames, source, cx, depth + 1);
            }
            RebuildFrame::ScopedComp {
                binders,
                source,
                cx,
                depth,
            } => {
                let child_cx = rewriter.under_scope(&binders, Rc::as_ref(&cx));
                frames.push(RebuildFrame::Comp {
                    source,
                    cx: Rc::new(child_cx),
                    depth,
                    run_hook: true,
                });
            }
            RebuildFrame::LeaveComp { source, cx, mark } => {
                let node = rebuild_comp(source, &mut rebuilt);
                debug_assert_eq!(rebuilt.len(), mark);
                rebuilt.push(Rebuilt::Comp(rewriter.leave_comp(
                    source,
                    node,
                    Rc::as_ref(&cx),
                )));
            }
            RebuildFrame::LeaveValue { source, cx, mark } => {
                let node = rebuild_value(source, &mut rebuilt);
                debug_assert_eq!(rebuilt.len(), mark);
                rebuilt.push(Rebuilt::Value(rewriter.leave_value(
                    source,
                    node,
                    Rc::as_ref(&cx),
                )));
            }
        }
    }
    assert_eq!(rebuilt.len(), 1, "a rewrite produces exactly one root");
    rebuilt.pop().expect("the rewritten root exists")
}

fn push_rebuild_scope<'a, C>(
    frames: &mut Vec<RebuildFrame<'a, C>>,
    binders: Scope,
    source: &'a Comp,
    cx: Rc<C>,
    depth: u64,
) {
    frames.push(RebuildFrame::ScopedComp {
        binders,
        source,
        cx,
        depth,
    });
}

fn push_rebuild_comp_children<'a, C>(
    frames: &mut Vec<RebuildFrame<'a, C>>,
    comp: &'a Comp,
    cx: &Rc<C>,
    depth: u64,
) {
    let value = |source| RebuildFrame::Value {
        source,
        cx: Rc::clone(cx),
        depth,
        run_hook: true,
    };
    let child = |source| RebuildFrame::Comp {
        source,
        cx: Rc::clone(cx),
        depth,
        run_hook: true,
    };
    match comp {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::UnboxedProject(v, _)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::Reuse(_, v)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => frames.push(value(v)),
        Comp::RefSet(a, b) | Comp::Prim(_, a, b) | Comp::InitAt(a, b) => {
            frames.push(value(b));
            frames.push(value(a));
        }
        Comp::Bind(first, binder, rest) => {
            push_rebuild_scope(frames, Rc::from([*binder]), rest, Rc::clone(cx), depth);
            frames.push(child(first));
        }
        Comp::App(callee, args) => {
            for argument in args.iter().rev() {
                frames.push(value(argument));
            }
            frames.push(child(callee));
        }
        Comp::If(condition, yes, no) => {
            frames.push(child(no));
            frames.push(child(yes));
            frames.push(value(condition));
        }
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for argument in args.iter().rev() {
                frames.push(value(argument));
            }
        }
        Comp::Lam(params, body) => push_rebuild_scope(
            frames,
            scope(params.iter().copied()),
            body,
            Rc::clone(cx),
            depth,
        ),
        Comp::Mask(_, body) => frames.push(child(body)),
        Comp::Case(scrutinee, arms) => {
            for (pattern, body) in arms.iter().rev() {
                push_rebuild_scope(frames, pattern_binders(pattern), body, Rc::clone(cx), depth);
            }
            frames.push(value(scrutinee));
        }
        Comp::WithReuse { token, freed, body } => {
            push_rebuild_scope(frames, Rc::from([*token]), body, Rc::clone(cx), depth);
            frames.push(value(freed));
        }
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => {
            for op in ops.iter().rev() {
                push_rebuild_scope(
                    frames,
                    scope(op.params.iter().copied().chain([op.resume])),
                    &op.body,
                    Rc::clone(cx),
                    depth,
                );
            }
            if let Some(return_body) = return_body {
                if let Some(return_var) = return_var {
                    push_rebuild_scope(
                        frames,
                        Rc::from([*return_var]),
                        return_body,
                        Rc::clone(cx),
                        depth,
                    );
                } else {
                    frames.push(child(return_body));
                }
            }
            frames.push(child(body));
        }
    }
}

fn push_rebuild_value_children<'a, C>(
    frames: &mut Vec<RebuildFrame<'a, C>>,
    value: &'a Value,
    cx: Rc<C>,
    depth: u64,
) {
    match value {
        Value::Thunk(body) => frames.push(RebuildFrame::Comp {
            source: body,
            cx,
            depth,
            run_hook: true,
        }),
        Value::UnboxedRecord(fields) => {
            for (_, field) in fields.iter().rev() {
                frames.push(RebuildFrame::Value {
                    source: field,
                    cx: Rc::clone(&cx),
                    depth,
                    run_hook: true,
                });
            }
        }
        Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
            for field in fields.iter().rev() {
                frames.push(RebuildFrame::Value {
                    source: field,
                    cx: Rc::clone(&cx),
                    depth,
                    run_hook: true,
                });
            }
        }
        Value::Var(_)
        | Value::Int(_)
        | Value::I64(_)
        | Value::U64(_)
        | Value::Float(_)
        | Value::Bool(_)
        | Value::Unit
        | Value::Str(_) => {}
    }
}

fn rebuild_comp(source: &Comp, rebuilt: &mut Vec<Rebuilt>) -> Comp {
    match source {
        Comp::Return(_) => Comp::Return(pop_value(rebuilt)),
        Comp::Bind(_, binder, _) => {
            let rest = pop_comp(rebuilt);
            let first = pop_comp(rebuilt);
            Comp::Bind(Box::new(first), *binder, Box::new(rest))
        }
        Comp::Force(_) => Comp::Force(pop_value(rebuilt)),
        Comp::Lam(params, _) => Comp::Lam(params.clone(), Box::new(pop_comp(rebuilt))),
        Comp::App(_, args) => {
            let args = take_values(rebuilt, args.len());
            Comp::App(Box::new(pop_comp(rebuilt)), args)
        }
        Comp::If(_, _, _) => {
            let no = pop_comp(rebuilt);
            let yes = pop_comp(rebuilt);
            Comp::If(pop_value(rebuilt), Box::new(yes), Box::new(no))
        }
        Comp::Prim(op, _, _) => {
            let rhs = pop_value(rebuilt);
            Comp::Prim(*op, pop_value(rebuilt), rhs)
        }
        Comp::Call(name, args) => Comp::Call(*name, take_values(rebuilt, args.len())),
        Comp::Io(op, args) => Comp::Io(*op, take_values(rebuilt, args.len())),
        Comp::Error(_) => Comp::Error(pop_value(rebuilt)),
        Comp::Case(_, arms) => {
            let bodies = take_comps(rebuilt, arms.len());
            let scrutinee = pop_value(rebuilt);
            Comp::Case(
                scrutinee,
                arms.iter()
                    .zip(bodies)
                    .map(|((pattern, _), body)| (pattern.clone(), body))
                    .collect(),
            )
        }
        Comp::FloatBuiltin(op, _) => Comp::FloatBuiltin(*op, pop_value(rebuilt)),
        Comp::Neg(lane, _) => Comp::Neg(*lane, pop_value(rebuilt)),
        Comp::UnboxedProject(_, field) => Comp::UnboxedProject(pop_value(rebuilt), *field),
        Comp::Do(name, args) => Comp::Do(*name, take_values(rebuilt, args.len())),
        Comp::Handle {
            return_var,
            return_body,
            ops,
            ..
        } => {
            let bodies = take_comps(rebuilt, ops.len());
            let return_body = return_body.as_ref().map(|_| Box::new(pop_comp(rebuilt)));
            let body = Box::new(pop_comp(rebuilt));
            let mut bodies = bodies.into_iter();
            let ops = ops.rebuild(|op| HandleOp {
                name: op.name,
                params: op.params.clone(),
                resume: op.resume,
                body: bodies.next().expect("each handler arm has one body"),
            });
            let extra_body = bodies.next();
            debug_assert!(extra_body.is_none());
            Comp::Handle {
                body,
                return_var: *return_var,
                return_body,
                ops,
            }
        }
        Comp::Mask(effects, _) => Comp::Mask(effects.clone(), Box::new(pop_comp(rebuilt))),
        Comp::StrBuiltin(op, args) => Comp::StrBuiltin(*op, take_values(rebuilt, args.len())),
        Comp::Dup(_) => Comp::Dup(pop_value(rebuilt)),
        Comp::Drop(_) => Comp::Drop(pop_value(rebuilt)),
        Comp::WithReuse { token, .. } => {
            let body = pop_comp(rebuilt);
            Comp::WithReuse {
                token: *token,
                freed: pop_value(rebuilt),
                body: Box::new(body),
            }
        }
        Comp::Reuse(token, _) => Comp::Reuse(*token, pop_value(rebuilt)),
        Comp::InitAt(_, _) => {
            let value = pop_value(rebuilt);
            Comp::InitAt(pop_value(rebuilt), value)
        }
        Comp::RefNew(_) => Comp::RefNew(pop_value(rebuilt)),
        Comp::RefGet(_) => Comp::RefGet(pop_value(rebuilt)),
        Comp::RefSet(_, _) => {
            let value = pop_value(rebuilt);
            Comp::RefSet(pop_value(rebuilt), value)
        }
    }
}

fn rebuild_value(source: &Value, rebuilt: &mut Vec<Rebuilt>) -> Value {
    match source {
        Value::Thunk(_) => Value::Thunk(Box::new(pop_comp(rebuilt))),
        Value::Ctor(name, tag, fields) => {
            Value::Ctor(*name, *tag, take_values(rebuilt, fields.len()))
        }
        Value::Tuple(fields) => Value::Tuple(take_values(rebuilt, fields.len())),
        Value::UnboxedTuple(fields) => Value::UnboxedTuple(take_values(rebuilt, fields.len())),
        Value::UnboxedRecord(fields) => {
            let values = take_values(rebuilt, fields.len());
            Value::UnboxedRecord(
                fields
                    .iter()
                    .zip(values)
                    .map(|((name, _), value)| (*name, value))
                    .collect(),
            )
        }
        Value::Var(_)
        | Value::Int(_)
        | Value::I64(_)
        | Value::U64(_)
        | Value::Float(_)
        | Value::Bool(_)
        | Value::Unit
        | Value::Str(_) => source.clone(),
    }
}

fn pop_comp(rebuilt: &mut Vec<Rebuilt>) -> Comp {
    expect_comp(rebuilt.pop().expect("a rewritten computation child exists"))
}

fn pop_value(rebuilt: &mut Vec<Rebuilt>) -> Value {
    expect_value(rebuilt.pop().expect("a rewritten value child exists"))
}

fn take_comps(rebuilt: &mut Vec<Rebuilt>, count: usize) -> Vec<Comp> {
    let start = rebuilt
        .len()
        .checked_sub(count)
        .expect("enough rewritten computation children exist");
    rebuilt.drain(start..).map(expect_comp).collect()
}

fn take_values(rebuilt: &mut Vec<Rebuilt>, count: usize) -> Vec<Value> {
    let start = rebuilt
        .len()
        .checked_sub(count)
        .expect("enough rewritten value children exist");
    rebuilt.drain(start..).map(expect_value).collect()
}

fn expect_comp(rebuilt: Rebuilt) -> Comp {
    match rebuilt {
        Rebuilt::Comp(comp) => comp,
        Rebuilt::Value(_) => panic!("expected a rewritten computation"),
    }
}

fn expect_value(rebuilt: Rebuilt) -> Value {
    match rebuilt {
        Rebuilt::Value(value) => value,
        Rebuilt::Comp(_) => panic!("expected a rewritten value"),
    }
}

/// Iterative read-only walk over raw Core.
///
/// The implementor carries policy state and overrides [`comp`](Self::comp),
/// [`value`](Self::value), or the scope hooks. One heap worklist owns structural
/// descent, child order, and binder lifetime.
pub trait Visit {
    fn enter_scope(&mut self, _binders: &[Sym]) {}

    fn exit_scope(&mut self, _binders: &[Sym]) {}

    /// Observe `comp`. Return `false` to prune its children.
    fn comp(&mut self, _comp: &Comp) -> bool {
        true
    }

    /// Observe `value`. Return `false` to prune its children.
    fn value(&mut self, _value: &Value) -> bool {
        true
    }

    fn walk_comp(&mut self, comp: &Comp)
    where
        Self: Sized,
    {
        walk(self, Frame::Comp(comp, 1));
    }

    fn walk_value(&mut self, value: &Value)
    where
        Self: Sized,
    {
        walk(self, Frame::Value(value, 1));
    }
}

type Scope = Rc<[Sym]>;

enum Frame<'a> {
    Comp(&'a Comp, u64),
    Value(&'a Value, u64),
    EnterScope(Scope),
    ExitScope(Scope),
}

fn scope(names: impl IntoIterator<Item = Sym>) -> Scope {
    names.into_iter().collect::<Vec<_>>().into()
}

fn pattern_binders(pattern: &CorePat) -> Scope {
    match pattern {
        CorePat::Wild => Rc::from([]),
        CorePat::Var(name) => Rc::from([*name]),
        CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => {
            scope(fields.iter().flatten().copied())
        }
    }
}

fn push_scope<'a>(stack: &mut Vec<Frame<'a>>, binders: Scope, body: &'a Comp, depth: u64) {
    stack.push(Frame::ExitScope(Rc::clone(&binders)));
    stack.push(Frame::Comp(body, depth));
    stack.push(Frame::EnterScope(binders));
}

fn walk<V: Visit>(visitor: &mut V, root: Frame<'_>) {
    let mut stack = vec![root];
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::EnterScope(binders) => visitor.enter_scope(&binders),
            Frame::ExitScope(binders) => visitor.exit_scope(&binders),
            Frame::Value(value, depth) => {
                work::visit_at_depth(depth);
                if !visitor.value(value) {
                    continue;
                }
                match value {
                    Value::Thunk(body) => stack.push(Frame::Comp(body, depth + 1)),
                    Value::UnboxedRecord(fields) => {
                        for (_, field) in fields.iter().rev() {
                            stack.push(Frame::Value(field, depth + 1));
                        }
                    }
                    Value::Ctor(_, _, fields)
                    | Value::Tuple(fields)
                    | Value::UnboxedTuple(fields) => {
                        for field in fields.iter().rev() {
                            stack.push(Frame::Value(field, depth + 1));
                        }
                    }
                    Value::Var(_)
                    | Value::Int(_)
                    | Value::I64(_)
                    | Value::U64(_)
                    | Value::Float(_)
                    | Value::Bool(_)
                    | Value::Unit
                    | Value::Str(_) => {}
                }
            }
            Frame::Comp(comp, depth) => {
                work::visit_at_depth(depth);
                if !visitor.comp(comp) {
                    continue;
                }
                push_comp_children(&mut stack, comp, depth + 1);
            }
        }
    }
}

fn push_comp_children<'a>(stack: &mut Vec<Frame<'a>>, comp: &'a Comp, depth: u64) {
    match comp {
        Comp::Return(value)
        | Comp::Force(value)
        | Comp::Error(value)
        | Comp::FloatBuiltin(_, value)
        | Comp::Neg(_, value)
        | Comp::UnboxedProject(value, _)
        | Comp::Dup(value)
        | Comp::Drop(value)
        | Comp::Reuse(_, value)
        | Comp::RefNew(value)
        | Comp::RefGet(value) => stack.push(Frame::Value(value, depth)),
        Comp::RefSet(lhs, rhs) | Comp::Prim(_, lhs, rhs) | Comp::InitAt(lhs, rhs) => {
            stack.push(Frame::Value(rhs, depth));
            stack.push(Frame::Value(lhs, depth));
        }
        Comp::Bind(first, binder, rest) => {
            push_scope(stack, Rc::from([*binder]), rest, depth);
            stack.push(Frame::Comp(first, depth));
        }
        Comp::App(callee, args) => {
            for argument in args.iter().rev() {
                stack.push(Frame::Value(argument, depth));
            }
            stack.push(Frame::Comp(callee, depth));
        }
        Comp::If(condition, yes, no) => {
            stack.push(Frame::Comp(no, depth));
            stack.push(Frame::Comp(yes, depth));
            stack.push(Frame::Value(condition, depth));
        }
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for argument in args.iter().rev() {
                stack.push(Frame::Value(argument, depth));
            }
        }
        Comp::Lam(params, body) => push_scope(stack, scope(params.iter().copied()), body, depth),
        Comp::Mask(_, body) => stack.push(Frame::Comp(body, depth)),
        Comp::Case(scrutinee, arms) => {
            for (pattern, body) in arms.iter().rev() {
                push_scope(stack, pattern_binders(pattern), body, depth);
            }
            stack.push(Frame::Value(scrutinee, depth));
        }
        Comp::WithReuse { token, freed, body } => {
            push_scope(stack, Rc::from([*token]), body, depth);
            stack.push(Frame::Value(freed, depth));
        }
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => {
            for op in ops.iter().rev() {
                push_scope(
                    stack,
                    scope(op.params.iter().copied().chain([op.resume])),
                    &op.body,
                    depth,
                );
            }
            if let Some(return_body) = return_body {
                if let Some(return_var) = return_var {
                    push_scope(stack, Rc::from([*return_var]), return_body, depth);
                } else {
                    stack.push(Frame::Comp(return_body, depth));
                }
            }
            stack.push(Frame::Comp(body, depth));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{map_children, Rewrite, RewriteControl, Visit};
    use crate::core::{Comp, Value};
    use prism_common::sym::Sym;

    const DEEP_TRAVERSAL_DEPTH: usize = 20_000;
    const DEEP_REWRITE_DEPTH: usize = 50_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    fn deep_bind_chain() -> Comp {
        let mut body = Comp::Return(Value::Int(0));
        for _ in 0..DEEP_TRAVERSAL_DEPTH {
            body = Comp::Bind(
                Box::new(Comp::Return(Value::Int(0))),
                Sym::new("value"),
                Box::new(body),
            );
        }
        body
    }

    #[derive(Default)]
    struct Counter {
        comps: usize,
        values: usize,
    }

    impl Visit for Counter {
        fn comp(&mut self, _comp: &Comp) -> bool {
            self.comps += 1;
            true
        }

        fn value(&mut self, _value: &Value) -> bool {
            self.values += 1;
            true
        }
    }

    struct Rename {
        from: Sym,
        to: Sym,
    }

    impl Rewrite for Rename {
        type Ctx = bool;

        fn under_scope(&mut self, binders: &[Sym], visible: &bool) -> bool {
            *visible && !binders.contains(&self.from)
        }

        fn enter_value(&mut self, value: &Value, visible: &bool) -> RewriteControl<Value> {
            if matches!(value, Value::Var(name) if *visible && *name == self.from) {
                RewriteControl::Replace(Value::Var(self.to))
            } else {
                RewriteControl::Descend
            }
        }
    }

    fn deep_rename_chain(from: Sym, binder: Sym) -> Comp {
        let mut body = Comp::Return(Value::Var(from));
        for _ in 0..DEEP_REWRITE_DEPTH {
            body = Comp::Bind(
                Box::new(Comp::Return(Value::Var(from))),
                binder,
                Box::new(body),
            );
        }
        body
    }

    fn consume_rename_chain(mut comp: Comp, expected: Sym, binder: Sym) {
        for _ in 0..DEEP_REWRITE_DEPTH {
            let Comp::Bind(first, actual_binder, rest) = comp else {
                panic!("deep rewrite must preserve every bind");
            };
            assert_eq!(actual_binder, binder);
            assert!(matches!(*first, Comp::Return(Value::Var(name)) if name == expected));
            comp = *rest;
        }
        assert!(matches!(comp, Comp::Return(Value::Var(name)) if name == expected));
    }

    #[test]
    fn raw_visit_handles_deep_binds_on_an_ordinary_stack() {
        let result = std::thread::Builder::new()
            .name("deep-raw-traversal".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let input = deep_bind_chain();
                let mut counter = Counter::default();
                counter.walk_comp(&input);
                assert_eq!(counter.comps, 2 * DEEP_TRAVERSAL_DEPTH + 1);
                assert_eq!(counter.values, DEEP_TRAVERSAL_DEPTH + 1);
                std::mem::forget(input);
            })
            .expect("spawning deep raw-traversal test")
            .join();
        if let Err(payload) = result {
            std::panic::resume_unwind(payload);
        }
    }

    #[test]
    fn raw_rewrite_handles_deep_scopes_on_an_ordinary_stack() {
        let result = std::thread::Builder::new()
            .name("deep-raw-rewrite".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let from = Sym::new("from");
                let to = Sym::new("to");
                let binder = Sym::new("binder");
                let input = deep_rename_chain(from, binder);
                let output = Rename { from, to }.rewrite_comp(&input, &true);

                consume_rename_chain(output, to, binder);
                consume_rename_chain(input, from, binder);
            })
            .expect("spawning deep raw-rewrite test")
            .join();
        if let Err(payload) = result {
            std::panic::resume_unwind(payload);
        }
    }

    #[test]
    fn map_children_rewrites_comp_children_inside_immediate_values() {
        let input = Comp::App(
            Box::new(Comp::Return(Value::Int(0))),
            vec![Value::Thunk(Box::new(Comp::Return(Value::Int(1))))],
        );
        let mut seen = Vec::new();
        let output = map_children(&input, &mut |child| {
            seen.push(child.kind());
            Comp::Error(Value::Int(2))
        });

        assert_eq!(seen, ["Return", "Return"]);
        assert!(matches!(
            output,
            Comp::App(callee, args)
                if matches!(*callee, Comp::Error(Value::Int(2)))
                    && matches!(args.as_slice(), [Value::Thunk(body)]
                        if matches!(**body, Comp::Error(Value::Int(2))))
        ));
    }
}
