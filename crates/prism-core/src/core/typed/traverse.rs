//! Canonical witness-preserving traversal for typed Core.
//!
//! This module owns the exhaustive structural child inventory shared by typed
//! analyses and rewrites. Policy modules override node hooks; binder-sensitive
//! policies may still override a node when their context transition is semantic.

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use prism_common::sym::Sym;

use crate::core::work;

use super::verify::{
    clone_core_instantiation, clone_core_type, discard_core_instantiation, discard_core_type,
};
use super::{
    CompSig, CoreFnSig, CoreInstantiation, CoreType, TypedBinder, TypedComp, TypedCompKind,
    TypedCoreFn, TypedForward, TypedHandleOp, TypedHandler, TypedPattern, TypedValue,
    TypedValueKind,
};

/// A complete, bounded-stack read-only walk over witness-carrying typed Core.
///
/// Analyses override node hooks, then enter through [`walk_comp`](Self::walk_comp),
/// [`walk_value`](Self::walk_value), or [`walk_function`](Self::walk_function).
/// One explicit enter/leave worklist owns all child enumeration and scope
/// transitions, so a deeply nested typed term consumes heap proportional to its
/// depth rather than the invoking thread's call stack.
pub(crate) trait Visit {
    fn core_type(&mut self, _ty: &CoreType) {}

    fn comp_sig(&mut self, _sig: &CompSig) {}

    fn fn_sig(&mut self, _sig: &CoreFnSig) {}

    fn instantiation(&mut self, _instantiation: &CoreInstantiation) {}

    fn forward(&mut self, _forward: &TypedForward) {}

    fn binder(&mut self, _binder: &TypedBinder) {}

    fn pattern(&mut self, _pattern: &TypedPattern) {}

    /// Enter the lexical scope introduced by `binders`.
    fn enter_scope(&mut self, _binders: &[&TypedBinder]) {}

    /// Leave the lexical scope previously passed to [`enter_scope`](Self::enter_scope).
    fn exit_scope(&mut self, _binders: &[&TypedBinder]) {}

    /// Observe `value`. Return `false` to prune this value's children.
    fn value(&mut self, _value: &TypedValue) -> bool {
        true
    }

    /// Observe `comp`. Return `false` to prune this computation's children.
    fn comp(&mut self, _comp: &TypedComp) -> bool {
        true
    }

    /// Observe `function`. Return `false` to prune its signature and body.
    fn function(&mut self, _function: &TypedCoreFn) -> bool {
        true
    }

    fn walk_value(&mut self, value: &TypedValue)
    where
        Self: Sized,
    {
        walk(self, Frame::Value(value, 1));
    }

    fn walk_comp(&mut self, comp: &TypedComp)
    where
        Self: Sized,
    {
        walk(self, Frame::Comp(comp, 1));
    }

    fn walk_function(&mut self, function: &TypedCoreFn)
    where
        Self: Sized,
    {
        walk(self, Frame::Function(function, 1));
    }
}

type Scope<'a> = Rc<[&'a TypedBinder]>;

enum Frame<'a> {
    Function(&'a TypedCoreFn, u64),
    Comp(&'a TypedComp, u64),
    Value(&'a TypedValue, u64),
    Pattern(&'a TypedPattern, u64),
    Binder(&'a TypedBinder, u64),
    CoreType(&'a CoreType, u64),
    CompSig(&'a CompSig, u64),
    FnSig(&'a CoreFnSig, u64),
    Instantiation(&'a CoreInstantiation),
    Forward(&'a TypedForward),
    EnterScope(Scope<'a>),
    ExitScope(Scope<'a>),
}

fn scope<'a>(binders: impl IntoIterator<Item = &'a TypedBinder>) -> Scope<'a> {
    binders.into_iter().collect::<Vec<_>>().into()
}

fn pattern_binders(pattern: &TypedPattern) -> Scope<'_> {
    match pattern {
        TypedPattern::Wild => Rc::from([]),
        TypedPattern::Var(binder) => Rc::from([binder]),
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            scope(fields.iter().flatten())
        }
    }
}

fn push_scope<'a>(stack: &mut Vec<Frame<'a>>, binders: Scope<'a>, body: &'a TypedComp, depth: u64) {
    stack.push(Frame::ExitScope(Rc::clone(&binders)));
    stack.push(Frame::Comp(body, depth));
    stack.push(Frame::EnterScope(binders));
}

#[allow(clippy::too_many_lines)]
fn walk<V: Visit>(visitor: &mut V, root: Frame<'_>) {
    let mut stack = vec![root];
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::EnterScope(binders) => visitor.enter_scope(&binders),
            Frame::ExitScope(binders) => visitor.exit_scope(&binders),
            Frame::CoreType(ty, depth) => {
                visitor.core_type(ty);
                match ty {
                    CoreType::Thunk(sig) => stack.push(Frame::CompSig(sig, depth + 1)),
                    CoreType::Function(sig) => stack.push(Frame::FnSig(sig, depth + 1)),
                    CoreType::Ref(inner) | CoreType::ReuseToken(inner) => {
                        stack.push(Frame::CoreType(inner, depth + 1));
                    }
                    CoreType::Source(_) | CoreType::Lowered(_) => {}
                }
            }
            Frame::CompSig(sig, depth) => {
                visitor.comp_sig(sig);
                stack.push(Frame::CoreType(sig.result(), depth + 1));
            }
            Frame::FnSig(sig, depth) => {
                visitor.fn_sig(sig);
                stack.push(Frame::CompSig(sig.body(), depth + 1));
                for param in sig.params().iter().rev() {
                    stack.push(Frame::CoreType(param, depth + 1));
                }
            }
            Frame::Instantiation(instantiation) => visitor.instantiation(instantiation),
            Frame::Forward(forward) => visitor.forward(forward),
            Frame::Binder(binder, depth) => {
                visitor.binder(binder);
                stack.push(Frame::CoreType(binder.ty(), depth + 1));
            }
            Frame::Pattern(pattern, depth) => {
                visitor.pattern(pattern);
                match pattern {
                    TypedPattern::Wild => {}
                    TypedPattern::Var(binder) => stack.push(Frame::Binder(binder, depth + 1)),
                    TypedPattern::Ctor {
                        instantiation,
                        fields,
                        ..
                    } => {
                        for binder in fields.iter().flatten().rev() {
                            stack.push(Frame::Binder(binder, depth + 1));
                        }
                        for argument in instantiation.iter().rev() {
                            stack.push(Frame::Instantiation(argument));
                        }
                    }
                    TypedPattern::Tuple(fields) => {
                        for binder in fields.iter().flatten().rev() {
                            stack.push(Frame::Binder(binder, depth + 1));
                        }
                    }
                }
            }
            Frame::Function(function, depth) => {
                if !visitor.function(function) {
                    continue;
                }
                let binders = scope(function.params());
                stack.push(Frame::ExitScope(Rc::clone(&binders)));
                stack.push(Frame::Comp(function.body(), depth + 1));
                stack.push(Frame::EnterScope(binders));
                for binder in function.params().iter().rev() {
                    stack.push(Frame::Binder(binder, depth + 1));
                }
                stack.push(Frame::FnSig(function.sig(), depth + 1));
            }
            Frame::Value(value, depth) => {
                work::visit_at_depth(depth);
                if !visitor.value(value) {
                    continue;
                }
                match value.kind() {
                    TypedValueKind::Var { instantiation, .. } => {
                        for argument in instantiation.iter().rev() {
                            stack.push(Frame::Instantiation(argument));
                        }
                    }
                    TypedValueKind::Reinterpret(inner)
                    | TypedValueKind::LoweredRepr {
                        value: inner,
                        proof: _,
                    } => stack.push(Frame::Value(inner, depth + 1)),
                    TypedValueKind::NewtypeRepr {
                        instantiation,
                        value: inner,
                        ..
                    } => {
                        stack.push(Frame::Value(inner, depth + 1));
                        for argument in instantiation.iter().rev() {
                            stack.push(Frame::Instantiation(argument));
                        }
                    }
                    TypedValueKind::Thunk(body) => stack.push(Frame::Comp(body, depth + 1)),
                    TypedValueKind::Ctor {
                        instantiation,
                        fields,
                        ..
                    } => {
                        for field in fields.iter().rev() {
                            stack.push(Frame::Value(field, depth + 1));
                        }
                        for argument in instantiation.iter().rev() {
                            stack.push(Frame::Instantiation(argument));
                        }
                    }
                    TypedValueKind::Tuple(fields) | TypedValueKind::UnboxedTuple(fields) => {
                        for field in fields.iter().rev() {
                            stack.push(Frame::Value(field, depth + 1));
                        }
                    }
                    TypedValueKind::UnboxedRecord(fields) => {
                        for (_, field) in fields.iter().rev() {
                            stack.push(Frame::Value(field, depth + 1));
                        }
                    }
                    TypedValueKind::Int(_)
                    | TypedValueKind::I64(_)
                    | TypedValueKind::U64(_)
                    | TypedValueKind::Float(_)
                    | TypedValueKind::Bool(_)
                    | TypedValueKind::Unit
                    | TypedValueKind::Str(_) => {}
                }
                stack.push(Frame::CoreType(value.ty(), depth + 1));
            }
            Frame::Comp(comp, depth) => {
                work::visit_at_depth(depth);
                if !visitor.comp(comp) {
                    continue;
                }
                push_comp_children(&mut stack, comp, depth + 1);
                stack.push(Frame::CompSig(comp.sig(), depth + 1));
            }
        }
    }
}

#[allow(clippy::too_many_lines)]
fn push_comp_children<'a>(stack: &mut Vec<Frame<'a>>, comp: &'a TypedComp, depth: u64) {
    match comp.kind() {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => stack.push(Frame::Value(value, depth)),
        TypedCompKind::Bind(first, binder, rest) => {
            let binders = scope([binder]);
            stack.push(Frame::ExitScope(Rc::clone(&binders)));
            stack.push(Frame::Comp(rest, depth));
            stack.push(Frame::EnterScope(binders));
            stack.push(Frame::Binder(binder, depth));
            stack.push(Frame::Comp(first, depth));
        }
        TypedCompKind::Lam(params, body) => {
            let binders = scope(params);
            push_scope(stack, Rc::clone(&binders), body, depth);
            for binder in params.iter().rev() {
                stack.push(Frame::Binder(binder, depth));
            }
        }
        TypedCompKind::App {
            callee,
            instantiation,
            args,
        } => {
            for argument in args.iter().rev() {
                stack.push(Frame::Value(argument, depth));
            }
            for argument in instantiation.iter().rev() {
                stack.push(Frame::Instantiation(argument));
            }
            stack.push(Frame::Comp(callee, depth));
        }
        TypedCompKind::If(condition, yes, no) => {
            stack.push(Frame::Comp(no, depth));
            stack.push(Frame::Comp(yes, depth));
            stack.push(Frame::Value(condition, depth));
        }
        TypedCompKind::Prim(_, lhs, rhs)
        | TypedCompKind::RefSet(lhs, rhs)
        | TypedCompKind::InitAt(lhs, rhs) => {
            stack.push(Frame::Value(rhs, depth));
            stack.push(Frame::Value(lhs, depth));
        }
        TypedCompKind::Call {
            instantiation,
            args,
            ..
        }
        | TypedCompKind::Do {
            instantiation,
            args,
            ..
        }
        | TypedCompKind::StrBuiltin {
            instantiation,
            args,
            ..
        } => {
            for argument in args.iter().rev() {
                stack.push(Frame::Value(argument, depth));
            }
            for argument in instantiation.iter().rev() {
                stack.push(Frame::Instantiation(argument));
            }
        }
        TypedCompKind::Io(_, args) => {
            for argument in args.iter().rev() {
                stack.push(Frame::Value(argument, depth));
            }
        }
        TypedCompKind::Case(scrutinee, arms) => {
            for (pattern, body) in arms.iter().rev() {
                let binders = pattern_binders(pattern);
                push_scope(stack, binders, body, depth);
                stack.push(Frame::Pattern(pattern, depth));
            }
            stack.push(Frame::Value(scrutinee, depth));
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            for forward in ops.forwarded().iter().rev() {
                stack.push(Frame::Forward(forward));
            }
            for arm in ops.arms().iter().rev() {
                let binders = scope(arm.params().iter().chain([arm.resume()]));
                push_scope(stack, binders, arm.body(), depth);
                stack.push(Frame::Binder(arm.resume(), depth));
                for binder in arm.params().iter().rev() {
                    stack.push(Frame::Binder(binder, depth));
                }
                for argument in arm.instantiation().iter().rev() {
                    stack.push(Frame::Instantiation(argument));
                }
            }
            if let Some(binder) = return_binder {
                let binders = scope([binder]);
                stack.push(Frame::ExitScope(Rc::clone(&binders)));
                if let Some(return_body) = return_body {
                    stack.push(Frame::Comp(return_body, depth));
                }
                stack.push(Frame::EnterScope(binders));
                stack.push(Frame::Binder(binder, depth));
            } else if let Some(return_body) = return_body {
                stack.push(Frame::Comp(return_body, depth));
            }
            stack.push(Frame::Comp(body, depth));
        }
        TypedCompKind::Mask(_, body) => stack.push(Frame::Comp(body, depth)),
        TypedCompKind::WithReuse { token, freed, body } => {
            let binders = scope([token]);
            push_scope(stack, binders, body, depth);
            stack.push(Frame::Binder(token, depth));
            stack.push(Frame::Value(freed, depth));
        }
        TypedCompKind::Reuse(token, value) => {
            stack.push(Frame::Value(value, depth));
            stack.push(Frame::Binder(token, depth));
        }
    }
}

/// What a free-reference analysis sees at one occurrence.
pub(crate) enum FreeRef<'a> {
    Occurrence(&'a TypedValue),
    Token(&'a TypedBinder),
}

/// Policy sink for the canonical scope-aware free-reference traversal.
pub(crate) trait FreeRefs {
    fn see(&mut self, name: Sym, reference: &FreeRef<'_>);
}

impl FreeRefs for BTreeSet<Sym> {
    fn see(&mut self, name: Sym, _: &FreeRef<'_>) {
        self.insert(name);
    }
}

/// The monomorphic value occurrence denoted by a binder at its binding site.
pub(crate) fn binder_occurrence(binder: &TypedBinder) -> TypedValue {
    TypedValue::new(
        clone_core_type(binder.ty()),
        TypedValueKind::Var {
            name: binder.name(),
            instantiation: Vec::new(),
        },
    )
}

/// Copy one variable occurrence without recursing through its type evidence.
pub(crate) fn clone_reference(value: &TypedValue) -> TypedValue {
    let TypedValueKind::Var {
        name,
        instantiation,
    } = value.kind()
    else {
        panic!("free-reference witnesses are variable occurrences")
    };
    TypedValue::new(
        clone_core_type(value.ty()),
        TypedValueKind::Var {
            name: *name,
            instantiation: instantiation.iter().map(clone_core_instantiation).collect(),
        },
    )
}

/// Discard one copied variable witness without recursive type destruction.
pub(crate) fn discard_reference(value: TypedValue) {
    let TypedValue { ty, kind } = value;
    let TypedValueKind::Var {
        name: _,
        instantiation,
    } = kind
    else {
        panic!("free-reference witnesses are variable occurrences")
    };
    discard_core_type(ty);
    for argument in instantiation {
        discard_core_instantiation(argument);
    }
}

/// First live witness per free name, in deterministic traversal order.
pub(crate) fn free_comp_var_witnesses(comp: &TypedComp) -> BTreeMap<Sym, TypedValue> {
    struct First(BTreeMap<Sym, TypedValue>);
    impl FreeRefs for First {
        fn see(&mut self, name: Sym, reference: &FreeRef<'_>) {
            self.0.entry(name).or_insert_with(|| match reference {
                FreeRef::Occurrence(value) => clone_reference(value),
                FreeRef::Token(binder) => binder_occurrence(binder),
            });
        }
    }
    let mut sink = First(BTreeMap::new());
    FreeCollector::new(&mut sink).walk_comp(comp);
    sink.0
}

/// Free local/global term references in a typed computation.
pub(crate) fn free_comp_vars(comp: &TypedComp) -> BTreeSet<Sym> {
    let mut free = BTreeSet::new();
    FreeCollector::new(&mut free).walk_comp(comp);
    free
}

/// Free local/global term references in a typed value, including thunk bodies.
pub(crate) fn free_value_vars(value: &TypedValue) -> BTreeSet<Sym> {
    let mut free = BTreeSet::new();
    FreeCollector::new(&mut free).walk_value(value);
    free
}

struct FreeCollector<'a, S> {
    sink: &'a mut S,
    bound: BoundStack,
    scope_marks: Vec<usize>,
}

impl<'a, S> FreeCollector<'a, S> {
    const fn new(sink: &'a mut S) -> Self {
        Self {
            sink,
            bound: BoundStack::new(),
            scope_marks: Vec::new(),
        }
    }
}

impl<S: FreeRefs> FreeCollector<'_, S> {
    fn reference(&mut self, name: Sym, reference: &FreeRef<'_>) {
        if !self.bound.contains(name) {
            self.sink.see(name, reference);
        }
    }
}

impl<S: FreeRefs> Visit for FreeCollector<'_, S> {
    fn enter_scope(&mut self, binders: &[&TypedBinder]) {
        self.scope_marks.push(self.bound.mark());
        self.bound
            .push_all(binders.iter().map(|binder| binder.name()));
    }

    fn exit_scope(&mut self, _binders: &[&TypedBinder]) {
        let mark = self
            .scope_marks
            .pop()
            .expect("typed visitor scope exits match entries");
        self.bound.pop_to(mark);
    }

    fn value(&mut self, value: &TypedValue) -> bool {
        if let TypedValueKind::Var { name, .. } = value.kind() {
            self.reference(*name, &FreeRef::Occurrence(value));
        }
        true
    }

    fn comp(&mut self, comp: &TypedComp) -> bool {
        #[cfg(test)]
        FREE_COMP_VAR_VISITS.with(|visits| {
            if let Some(count) = visits.get() {
                visits.set(Some(count + 1));
            }
        });
        if let TypedCompKind::Reuse(token, _) = comp.kind() {
            self.reference(token.name(), &FreeRef::Token(token));
        }
        true
    }
}

/// Lexical binder stack with sublinear membership and scoped save/restore.
struct BoundStack {
    stack: Vec<Sym>,
    counts: BTreeMap<Sym, u32>,
}

impl BoundStack {
    const fn new() -> Self {
        Self {
            stack: Vec::new(),
            counts: BTreeMap::new(),
        }
    }

    const fn mark(&self) -> usize {
        self.stack.len()
    }

    fn push_all(&mut self, names: impl IntoIterator<Item = Sym>) {
        for name in names {
            self.stack.push(name);
            *self.counts.entry(name).or_insert(0) += 1;
        }
    }

    fn pop_to(&mut self, mark: usize) {
        while self.stack.len() > mark {
            let name = self.stack.pop().expect("stack is longer than the mark");
            match self.counts.get_mut(&name) {
                Some(count) if *count > 1 => *count -= 1,
                _ => {
                    self.counts.remove(&name);
                }
            }
        }
    }

    fn contains(&self, name: Sym) -> bool {
        self.counts.contains_key(&name)
    }
}

#[cfg(test)]
thread_local! {
    static FREE_COMP_VAR_VISITS: std::cell::Cell<Option<usize>> = const {
        std::cell::Cell::new(None)
    };
}

#[cfg(test)]
pub(crate) fn count_free_comp_var_visits<T>(f: impl FnOnce() -> T) -> (T, usize) {
    FREE_COMP_VAR_VISITS.with(|visits| {
        assert!(
            visits.replace(Some(0)).is_none(),
            "free-variable visit counters cannot be nested"
        );
    });
    let result = f();
    let count = FREE_COMP_VAR_VISITS.with(|visits| {
        visits
            .replace(None)
            .expect("free-variable visit counter is active")
    });
    (result, count)
}

/// One structural typed-Core rewrite.
///
/// The default descent is the exhaustive node inventory for private typed
/// passes. Implementors override only the nodes or witness leaves they change.
/// Binder-sensitive rewrites override the corresponding computation forms so
/// their context extension stays explicit.
pub(crate) trait Rewrite {
    type Ctx;

    fn core_type(&mut self, ty: &CoreType, _cx: &Self::Ctx) -> CoreType {
        ty.clone()
    }

    fn comp_sig(&mut self, sig: &CompSig, _cx: &Self::Ctx) -> CompSig {
        sig.clone()
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, _cx: &Self::Ctx) -> CoreFnSig {
        sig.clone()
    }

    fn instantiation(
        &mut self,
        instantiation: &CoreInstantiation,
        _cx: &Self::Ctx,
    ) -> CoreInstantiation {
        instantiation.clone()
    }

    fn forward(&mut self, forward: &TypedForward, _cx: &Self::Ctx) -> TypedForward {
        forward.clone()
    }

    fn binder(&mut self, binder: &TypedBinder, cx: &Self::Ctx) -> TypedBinder {
        TypedBinder::new(binder.name, self.core_type(&binder.ty, cx))
    }

    fn pattern(&mut self, pattern: &TypedPattern, cx: &Self::Ctx) -> TypedPattern {
        match pattern {
            TypedPattern::Wild => TypedPattern::Wild,
            TypedPattern::Var(binder) => TypedPattern::Var(self.binder(binder, cx)),
            TypedPattern::Ctor {
                name,
                instantiation,
                fields,
            } => TypedPattern::Ctor {
                name: *name,
                instantiation: self.instantiations(instantiation, cx),
                fields: fields
                    .iter()
                    .map(|binder| binder.as_ref().map(|binder| self.binder(binder, cx)))
                    .collect(),
            },
            TypedPattern::Tuple(fields) => TypedPattern::Tuple(
                fields
                    .iter()
                    .map(|binder| binder.as_ref().map(|binder| self.binder(binder, cx)))
                    .collect(),
            ),
        }
    }

    fn value(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        self.descend_value(value, cx)
    }

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        self.descend_comp(comp, cx)
    }

    fn function(&mut self, function: &TypedCoreFn, cx: &Self::Ctx) -> TypedCoreFn {
        TypedCoreFn::new(
            function.name,
            function
                .params
                .iter()
                .map(|binder| self.binder(binder, cx))
                .collect(),
            self.comp(&function.body, cx),
            self.fn_sig(&function.sig, cx),
            function.dict_arity,
        )
    }

    /// Rewrite a computation iteratively using only the structural witness hooks.
    ///
    /// This entry point deliberately bypasses the `value`, `comp`, and
    /// `function` overrides. It is for context-neutral policies whose only
    /// custom behavior lives in the type, signature, instantiation,
    /// forwarding, binder, or pattern hooks.
    fn rewrite_comp_from_hooks(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp
    where
        Self: Sized,
    {
        rewrite_from_hooks(self, RebuildFrame::Comp(comp, 1), cx).into_comp()
    }

    /// Rewrite a function iteratively using only the structural witness hooks.
    fn rewrite_function_from_hooks(&mut self, function: &TypedCoreFn, cx: &Self::Ctx) -> TypedCoreFn
    where
        Self: Sized,
    {
        rewrite_from_hooks(self, RebuildFrame::Function(function), cx).into_function()
    }

    fn instantiations(
        &mut self,
        instantiations: &[CoreInstantiation],
        cx: &Self::Ctx,
    ) -> Vec<CoreInstantiation> {
        instantiations
            .iter()
            .map(|instantiation| self.instantiation(instantiation, cx))
            .collect()
    }

    fn descend_value(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        // Control-sensitive hooks recurse per node; grow stack segments inside
        // the shared descent until every rewrite is worklist-driven.
        work::on_core_stack(|| self.descend_value_on_core_stack(value, cx))
    }

    #[allow(clippy::too_many_lines)]
    fn descend_value_on_core_stack(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        let _frame = work::frame();
        work::rebuild();
        let kind = match &value.kind {
            TypedValueKind::Var {
                name,
                instantiation,
            } => TypedValueKind::Var {
                name: *name,
                instantiation: self.instantiations(instantiation, cx),
            },
            TypedValueKind::Int(value) => TypedValueKind::Int(*value),
            TypedValueKind::I64(value) => TypedValueKind::I64(*value),
            TypedValueKind::U64(value) => TypedValueKind::U64(*value),
            TypedValueKind::Float(value) => TypedValueKind::Float(*value),
            TypedValueKind::Bool(value) => TypedValueKind::Bool(*value),
            TypedValueKind::Unit => TypedValueKind::Unit,
            TypedValueKind::Str(value) => TypedValueKind::Str(value.clone()),
            TypedValueKind::Reinterpret(value) => {
                TypedValueKind::Reinterpret(Box::new(self.value(value, cx)))
            }
            TypedValueKind::LoweredRepr { value, proof } => TypedValueKind::LoweredRepr {
                value: Box::new(self.value(value, cx)),
                proof: proof.clone(),
            },
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => TypedValueKind::NewtypeRepr {
                constructor: *constructor,
                instantiation: self.instantiations(instantiation, cx),
                value: Box::new(self.value(value, cx)),
            },
            TypedValueKind::Thunk(body) => TypedValueKind::Thunk(Box::new(self.comp(body, cx))),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => TypedValueKind::Ctor {
                name: *name,
                tag: *tag,
                instantiation: self.instantiations(instantiation, cx),
                fields: fields.iter().map(|field| self.value(field, cx)).collect(),
            },
            TypedValueKind::Tuple(fields) => {
                TypedValueKind::Tuple(fields.iter().map(|field| self.value(field, cx)).collect())
            }
            TypedValueKind::UnboxedTuple(fields) => TypedValueKind::UnboxedTuple(
                fields.iter().map(|field| self.value(field, cx)).collect(),
            ),
            TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, field)| (*name, self.value(field, cx)))
                    .collect(),
            ),
        };
        TypedValue::new(self.core_type(&value.ty, cx), kind)
    }

    fn descend_comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        // Same growth discipline as `descend_value`.
        work::on_core_stack(|| self.descend_comp_on_core_stack(comp, cx))
    }

    #[allow(clippy::too_many_lines)]
    fn descend_comp_on_core_stack(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        let _frame = work::frame();
        work::rebuild();
        let kind = match &comp.kind {
            TypedCompKind::Return(value) => TypedCompKind::Return(self.value(value, cx)),
            TypedCompKind::Bind(first, binder, rest) => TypedCompKind::Bind(
                Box::new(self.comp(first, cx)),
                self.binder(binder, cx),
                Box::new(self.comp(rest, cx)),
            ),
            TypedCompKind::Force(value) => TypedCompKind::Force(self.value(value, cx)),
            TypedCompKind::Lam(params, body) => TypedCompKind::Lam(
                params
                    .iter()
                    .map(|binder| self.binder(binder, cx))
                    .collect(),
                Box::new(self.comp(body, cx)),
            ),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => TypedCompKind::App {
                callee: Box::new(self.comp(callee, cx)),
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::If(condition, yes, no) => TypedCompKind::If(
                self.value(condition, cx),
                Box::new(self.comp(yes, cx)),
                Box::new(self.comp(no, cx)),
            ),
            TypedCompKind::Prim(op, lhs, rhs) => {
                TypedCompKind::Prim(*op, self.value(lhs, cx), self.value(rhs, cx))
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => TypedCompKind::Call {
                callee: *callee,
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::Io(op, args) => {
                TypedCompKind::Io(*op, args.iter().map(|arg| self.value(arg, cx)).collect())
            }
            TypedCompKind::Error(value) => TypedCompKind::Error(self.value(value, cx)),
            TypedCompKind::Case(scrutinee, arms) => TypedCompKind::Case(
                self.value(scrutinee, cx),
                arms.iter()
                    .map(|(pattern, body)| (self.pattern(pattern, cx), self.comp(body, cx)))
                    .collect(),
            ),
            TypedCompKind::FloatBuiltin(op, value) => {
                TypedCompKind::FloatBuiltin(*op, self.value(value, cx))
            }
            TypedCompKind::Neg(lane, value) => TypedCompKind::Neg(*lane, self.value(value, cx)),
            TypedCompKind::UnboxedProject(value, field) => {
                TypedCompKind::UnboxedProject(self.value(value, cx), *field)
            }
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => TypedCompKind::Do {
                operation: *operation,
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops,
            } => TypedCompKind::Handle {
                body: Box::new(self.comp(body, cx)),
                return_binder: return_binder.as_ref().map(|binder| self.binder(binder, cx)),
                return_body: return_body
                    .as_ref()
                    .map(|body| Box::new(self.comp(body, cx))),
                ops: TypedHandler {
                    arms: ops
                        .arms
                        .iter()
                        .map(|arm| TypedHandleOp {
                            name: arm.name,
                            instantiation: self.instantiations(&arm.instantiation, cx),
                            params: arm
                                .params
                                .iter()
                                .map(|binder| self.binder(binder, cx))
                                .collect(),
                            resume: self.binder(&arm.resume, cx),
                            body: self.comp(&arm.body, cx),
                        })
                        .collect(),
                    forwarded: ops
                        .forwarded
                        .iter()
                        .map(|forward| self.forward(forward, cx))
                        .collect(),
                },
            },
            TypedCompKind::Mask(effects, body) => {
                TypedCompKind::Mask(effects.clone(), Box::new(self.comp(body, cx)))
            }
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedCompKind::StrBuiltin {
                op: *op,
                instantiation: self.instantiations(instantiation, cx),
                args: args.iter().map(|arg| self.value(arg, cx)).collect(),
            },
            TypedCompKind::Dup(value) => TypedCompKind::Dup(self.value(value, cx)),
            TypedCompKind::Drop(value) => TypedCompKind::Drop(self.value(value, cx)),
            TypedCompKind::WithReuse { token, freed, body } => TypedCompKind::WithReuse {
                token: self.binder(token, cx),
                freed: self.value(freed, cx),
                body: Box::new(self.comp(body, cx)),
            },
            TypedCompKind::Reuse(token, value) => {
                TypedCompKind::Reuse(self.binder(token, cx), self.value(value, cx))
            }
            TypedCompKind::RefNew(value) => TypedCompKind::RefNew(self.value(value, cx)),
            TypedCompKind::RefGet(value) => TypedCompKind::RefGet(self.value(value, cx)),
            TypedCompKind::RefSet(cell, value) => {
                TypedCompKind::RefSet(self.value(cell, cx), self.value(value, cx))
            }
            TypedCompKind::InitAt(cell, ctor) => {
                TypedCompKind::InitAt(self.value(cell, cx), self.value(ctor, cx))
            }
        };
        TypedComp::new(self.comp_sig(&comp.sig, cx), kind)
    }
}

enum RebuildFrame<'a> {
    Function(&'a TypedCoreFn),
    Comp(&'a TypedComp, u64),
    Value(&'a TypedValue, u64),
    Pattern(&'a TypedPattern),
    Binder(&'a TypedBinder),
    Instantiation(&'a CoreInstantiation),
    Forward(&'a TypedForward),
    FinishFunction {
        function: &'a TypedCoreFn,
        result_mark: usize,
    },
    FinishComp {
        comp: &'a TypedComp,
        result_mark: usize,
    },
    FinishValue {
        value: &'a TypedValue,
        result_mark: usize,
    },
}

enum Rebuilt {
    Function(Box<TypedCoreFn>),
    Comp(Box<TypedComp>),
    Value(TypedValue),
    Pattern(TypedPattern),
    Binder(TypedBinder),
    Instantiation(CoreInstantiation),
    Forward(TypedForward),
}

impl Rebuilt {
    fn into_function(self) -> TypedCoreFn {
        let Self::Function(function) = self else {
            panic!("typed rewrite root is not a function")
        };
        *function
    }

    fn into_comp(self) -> TypedComp {
        let Self::Comp(comp) = self else {
            panic!("typed rewrite root is not a computation")
        };
        *comp
    }
}

fn next_comp(results: &mut impl Iterator<Item = Rebuilt>) -> TypedComp {
    *next_comp_box(results)
}

fn next_comp_box(results: &mut impl Iterator<Item = Rebuilt>) -> Box<TypedComp> {
    let Some(Rebuilt::Comp(comp)) = results.next() else {
        panic!("typed rewrite expected a computation result")
    };
    comp
}

fn next_value(results: &mut impl Iterator<Item = Rebuilt>) -> TypedValue {
    let Some(Rebuilt::Value(value)) = results.next() else {
        panic!("typed rewrite expected a value result")
    };
    value
}

fn next_pattern(results: &mut impl Iterator<Item = Rebuilt>) -> TypedPattern {
    let Some(Rebuilt::Pattern(pattern)) = results.next() else {
        panic!("typed rewrite expected a pattern result")
    };
    pattern
}

fn next_binder(results: &mut impl Iterator<Item = Rebuilt>) -> TypedBinder {
    let Some(Rebuilt::Binder(binder)) = results.next() else {
        panic!("typed rewrite expected a binder result")
    };
    binder
}

fn next_instantiation(results: &mut impl Iterator<Item = Rebuilt>) -> CoreInstantiation {
    let Some(Rebuilt::Instantiation(instantiation)) = results.next() else {
        panic!("typed rewrite expected an instantiation result")
    };
    instantiation
}

fn next_forward(results: &mut impl Iterator<Item = Rebuilt>) -> TypedForward {
    let Some(Rebuilt::Forward(forward)) = results.next() else {
        panic!("typed rewrite expected a forwarding result")
    };
    forward
}

fn next_values(results: &mut impl Iterator<Item = Rebuilt>, count: usize) -> Vec<TypedValue> {
    (0..count).map(|_| next_value(results)).collect()
}

fn next_binders(results: &mut impl Iterator<Item = Rebuilt>, count: usize) -> Vec<TypedBinder> {
    (0..count).map(|_| next_binder(results)).collect()
}

fn next_instantiations(
    results: &mut impl Iterator<Item = Rebuilt>,
    count: usize,
) -> Vec<CoreInstantiation> {
    (0..count).map(|_| next_instantiation(results)).collect()
}

fn push_instantiations<'a>(
    frames: &mut Vec<RebuildFrame<'a>>,
    instantiations: &'a [CoreInstantiation],
) {
    for instantiation in instantiations.iter().rev() {
        frames.push(RebuildFrame::Instantiation(instantiation));
    }
}

fn push_binders<'a>(frames: &mut Vec<RebuildFrame<'a>>, binders: &'a [TypedBinder]) {
    for binder in binders.iter().rev() {
        frames.push(RebuildFrame::Binder(binder));
    }
}

fn push_values<'a>(frames: &mut Vec<RebuildFrame<'a>>, values: &'a [TypedValue], depth: u64) {
    for value in values.iter().rev() {
        frames.push(RebuildFrame::Value(value, depth));
    }
}

fn push_rewrite_value_children<'a>(
    frames: &mut Vec<RebuildFrame<'a>>,
    value: &'a TypedValue,
    depth: u64,
) {
    match value.kind() {
        TypedValueKind::Var { instantiation, .. } => {
            push_instantiations(frames, instantiation);
        }
        TypedValueKind::Reinterpret(inner)
        | TypedValueKind::LoweredRepr {
            value: inner,
            proof: _,
        } => frames.push(RebuildFrame::Value(inner, depth)),
        TypedValueKind::NewtypeRepr {
            instantiation,
            value: inner,
            ..
        } => {
            frames.push(RebuildFrame::Value(inner, depth));
            push_instantiations(frames, instantiation);
        }
        TypedValueKind::Thunk(body) => frames.push(RebuildFrame::Comp(body, depth)),
        TypedValueKind::Ctor {
            instantiation,
            fields,
            ..
        } => {
            push_values(frames, fields, depth);
            push_instantiations(frames, instantiation);
        }
        TypedValueKind::Tuple(fields) | TypedValueKind::UnboxedTuple(fields) => {
            push_values(frames, fields, depth);
        }
        TypedValueKind::UnboxedRecord(fields) => {
            for (_, field) in fields.iter().rev() {
                frames.push(RebuildFrame::Value(field, depth));
            }
        }
        TypedValueKind::Int(_)
        | TypedValueKind::I64(_)
        | TypedValueKind::U64(_)
        | TypedValueKind::Float(_)
        | TypedValueKind::Bool(_)
        | TypedValueKind::Unit
        | TypedValueKind::Str(_) => {}
    }
}

#[allow(clippy::too_many_lines)]
fn push_rewrite_comp_children<'a>(
    frames: &mut Vec<RebuildFrame<'a>>,
    comp: &'a TypedComp,
    depth: u64,
) {
    match comp.kind() {
        TypedCompKind::Return(value)
        | TypedCompKind::Force(value)
        | TypedCompKind::Error(value)
        | TypedCompKind::FloatBuiltin(_, value)
        | TypedCompKind::Neg(_, value)
        | TypedCompKind::UnboxedProject(value, _)
        | TypedCompKind::Dup(value)
        | TypedCompKind::Drop(value)
        | TypedCompKind::RefNew(value)
        | TypedCompKind::RefGet(value) => frames.push(RebuildFrame::Value(value, depth)),
        TypedCompKind::Bind(first, binder, rest) => {
            frames.push(RebuildFrame::Comp(rest, depth));
            frames.push(RebuildFrame::Binder(binder));
            frames.push(RebuildFrame::Comp(first, depth));
        }
        TypedCompKind::Lam(params, body) => {
            frames.push(RebuildFrame::Comp(body, depth));
            push_binders(frames, params);
        }
        TypedCompKind::App {
            callee,
            instantiation,
            args,
        } => {
            push_values(frames, args, depth);
            push_instantiations(frames, instantiation);
            frames.push(RebuildFrame::Comp(callee, depth));
        }
        TypedCompKind::If(condition, yes, no) => {
            frames.push(RebuildFrame::Comp(no, depth));
            frames.push(RebuildFrame::Comp(yes, depth));
            frames.push(RebuildFrame::Value(condition, depth));
        }
        TypedCompKind::Prim(_, lhs, rhs)
        | TypedCompKind::RefSet(lhs, rhs)
        | TypedCompKind::InitAt(lhs, rhs) => {
            frames.push(RebuildFrame::Value(rhs, depth));
            frames.push(RebuildFrame::Value(lhs, depth));
        }
        TypedCompKind::Call {
            instantiation,
            args,
            ..
        }
        | TypedCompKind::Do {
            instantiation,
            args,
            ..
        }
        | TypedCompKind::StrBuiltin {
            instantiation,
            args,
            ..
        } => {
            push_values(frames, args, depth);
            push_instantiations(frames, instantiation);
        }
        TypedCompKind::Io(_, args) => push_values(frames, args, depth),
        TypedCompKind::Case(scrutinee, arms) => {
            for (pattern, body) in arms.iter().rev() {
                frames.push(RebuildFrame::Comp(body, depth));
                frames.push(RebuildFrame::Pattern(pattern));
            }
            frames.push(RebuildFrame::Value(scrutinee, depth));
        }
        TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } => {
            for forward in ops.forwarded().iter().rev() {
                frames.push(RebuildFrame::Forward(forward));
            }
            for arm in ops.arms().iter().rev() {
                frames.push(RebuildFrame::Comp(arm.body(), depth));
                frames.push(RebuildFrame::Binder(arm.resume()));
                push_binders(frames, arm.params());
                push_instantiations(frames, arm.instantiation());
            }
            if let Some(return_body) = return_body {
                frames.push(RebuildFrame::Comp(return_body, depth));
            }
            if let Some(return_binder) = return_binder {
                frames.push(RebuildFrame::Binder(return_binder));
            }
            frames.push(RebuildFrame::Comp(body, depth));
        }
        TypedCompKind::Mask(_, body) => frames.push(RebuildFrame::Comp(body, depth)),
        TypedCompKind::WithReuse { token, freed, body } => {
            frames.push(RebuildFrame::Comp(body, depth));
            frames.push(RebuildFrame::Value(freed, depth));
            frames.push(RebuildFrame::Binder(token));
        }
        TypedCompKind::Reuse(token, value) => {
            frames.push(RebuildFrame::Value(value, depth));
            frames.push(RebuildFrame::Binder(token));
        }
    }
}

fn rebuild_value<R: Rewrite>(
    rewriter: &mut R,
    value: &TypedValue,
    results: &mut impl Iterator<Item = Rebuilt>,
    cx: &R::Ctx,
) -> TypedValue {
    let kind = match value.kind() {
        TypedValueKind::Var {
            name,
            instantiation,
        } => TypedValueKind::Var {
            name: *name,
            instantiation: next_instantiations(results, instantiation.len()),
        },
        TypedValueKind::Int(value) => TypedValueKind::Int(*value),
        TypedValueKind::I64(value) => TypedValueKind::I64(*value),
        TypedValueKind::U64(value) => TypedValueKind::U64(*value),
        TypedValueKind::Float(value) => TypedValueKind::Float(*value),
        TypedValueKind::Bool(value) => TypedValueKind::Bool(*value),
        TypedValueKind::Unit => TypedValueKind::Unit,
        TypedValueKind::Str(value) => TypedValueKind::Str(value.clone()),
        TypedValueKind::Reinterpret(_) => {
            TypedValueKind::Reinterpret(Box::new(next_value(results)))
        }
        TypedValueKind::LoweredRepr { proof, .. } => TypedValueKind::LoweredRepr {
            value: Box::new(next_value(results)),
            proof: proof.clone(),
        },
        TypedValueKind::NewtypeRepr {
            constructor,
            instantiation,
            ..
        } => TypedValueKind::NewtypeRepr {
            constructor: *constructor,
            instantiation: next_instantiations(results, instantiation.len()),
            value: Box::new(next_value(results)),
        },
        TypedValueKind::Thunk(_) => TypedValueKind::Thunk(next_comp_box(results)),
        TypedValueKind::Ctor {
            name,
            tag,
            instantiation,
            fields,
        } => TypedValueKind::Ctor {
            name: *name,
            tag: *tag,
            instantiation: next_instantiations(results, instantiation.len()),
            fields: next_values(results, fields.len()),
        },
        TypedValueKind::Tuple(fields) => TypedValueKind::Tuple(next_values(results, fields.len())),
        TypedValueKind::UnboxedTuple(fields) => {
            TypedValueKind::UnboxedTuple(next_values(results, fields.len()))
        }
        TypedValueKind::UnboxedRecord(fields) => TypedValueKind::UnboxedRecord(
            fields
                .iter()
                .map(|(name, _)| (*name, next_value(results)))
                .collect(),
        ),
    };
    TypedValue::new(rewriter.core_type(value.ty(), cx), kind)
}

#[allow(clippy::too_many_lines)]
fn rebuild_comp<R: Rewrite>(
    rewriter: &mut R,
    comp: &TypedComp,
    results: &mut impl Iterator<Item = Rebuilt>,
    cx: &R::Ctx,
) -> TypedComp {
    let kind = match comp.kind() {
        TypedCompKind::Return(_) => TypedCompKind::Return(next_value(results)),
        TypedCompKind::Bind(_, _, _) => TypedCompKind::Bind(
            next_comp_box(results),
            next_binder(results),
            next_comp_box(results),
        ),
        TypedCompKind::Force(_) => TypedCompKind::Force(next_value(results)),
        TypedCompKind::Lam(params, _) => {
            TypedCompKind::Lam(next_binders(results, params.len()), next_comp_box(results))
        }
        TypedCompKind::App {
            instantiation,
            args,
            ..
        } => TypedCompKind::App {
            callee: next_comp_box(results),
            instantiation: next_instantiations(results, instantiation.len()),
            args: next_values(results, args.len()),
        },
        TypedCompKind::If(_, _, _) => TypedCompKind::If(
            next_value(results),
            next_comp_box(results),
            next_comp_box(results),
        ),
        TypedCompKind::Prim(op, _, _) => {
            TypedCompKind::Prim(*op, next_value(results), next_value(results))
        }
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } => TypedCompKind::Call {
            callee: *callee,
            instantiation: next_instantiations(results, instantiation.len()),
            args: next_values(results, args.len()),
        },
        TypedCompKind::Io(op, args) => TypedCompKind::Io(*op, next_values(results, args.len())),
        TypedCompKind::Error(_) => TypedCompKind::Error(next_value(results)),
        TypedCompKind::Case(_, arms) => TypedCompKind::Case(
            next_value(results),
            arms.iter()
                .map(|_| (next_pattern(results), next_comp(results)))
                .collect(),
        ),
        TypedCompKind::FloatBuiltin(op, _) => TypedCompKind::FloatBuiltin(*op, next_value(results)),
        TypedCompKind::Neg(lane, _) => TypedCompKind::Neg(*lane, next_value(results)),
        TypedCompKind::UnboxedProject(_, field) => {
            TypedCompKind::UnboxedProject(next_value(results), *field)
        }
        TypedCompKind::Do {
            operation,
            instantiation,
            args,
        } => TypedCompKind::Do {
            operation: *operation,
            instantiation: next_instantiations(results, instantiation.len()),
            args: next_values(results, args.len()),
        },
        TypedCompKind::Handle {
            return_binder,
            return_body,
            ops,
            ..
        } => {
            let body = next_comp_box(results);
            let return_binder = return_binder.as_ref().map(|_| next_binder(results));
            let return_body = return_body.as_ref().map(|_| next_comp_box(results));
            let arms = ops
                .arms()
                .iter()
                .map(|arm| TypedHandleOp {
                    name: arm.name(),
                    instantiation: next_instantiations(results, arm.instantiation().len()),
                    params: next_binders(results, arm.params().len()),
                    resume: next_binder(results),
                    body: next_comp(results),
                })
                .collect();
            let forwarded = ops
                .forwarded()
                .iter()
                .map(|_| next_forward(results))
                .collect();
            TypedCompKind::Handle {
                body,
                return_binder,
                return_body,
                ops: TypedHandler { arms, forwarded },
            }
        }
        TypedCompKind::Mask(effects, _) => {
            TypedCompKind::Mask(effects.clone(), next_comp_box(results))
        }
        TypedCompKind::StrBuiltin {
            op,
            instantiation,
            args,
        } => TypedCompKind::StrBuiltin {
            op: *op,
            instantiation: next_instantiations(results, instantiation.len()),
            args: next_values(results, args.len()),
        },
        TypedCompKind::Dup(_) => TypedCompKind::Dup(next_value(results)),
        TypedCompKind::Drop(_) => TypedCompKind::Drop(next_value(results)),
        TypedCompKind::WithReuse { .. } => TypedCompKind::WithReuse {
            token: next_binder(results),
            freed: next_value(results),
            body: next_comp_box(results),
        },
        TypedCompKind::Reuse(_, _) => {
            TypedCompKind::Reuse(next_binder(results), next_value(results))
        }
        TypedCompKind::RefNew(_) => TypedCompKind::RefNew(next_value(results)),
        TypedCompKind::RefGet(_) => TypedCompKind::RefGet(next_value(results)),
        TypedCompKind::RefSet(_, _) => {
            TypedCompKind::RefSet(next_value(results), next_value(results))
        }
        TypedCompKind::InitAt(_, _) => {
            TypedCompKind::InitAt(next_value(results), next_value(results))
        }
    };
    TypedComp::new(rewriter.comp_sig(comp.sig(), cx), kind)
}

fn rewrite_from_hooks<R: Rewrite>(
    rewriter: &mut R,
    root: RebuildFrame<'_>,
    cx: &R::Ctx,
) -> Rebuilt {
    let mut frames = vec![root];
    let mut results = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            RebuildFrame::Function(function) => {
                frames.push(RebuildFrame::FinishFunction {
                    function,
                    result_mark: results.len(),
                });
                frames.push(RebuildFrame::Comp(function.body(), 1));
                push_binders(&mut frames, function.params());
            }
            RebuildFrame::Comp(comp, depth) => {
                work::rebuild_at_depth(depth);
                frames.push(RebuildFrame::FinishComp {
                    comp,
                    result_mark: results.len(),
                });
                push_rewrite_comp_children(&mut frames, comp, depth + 1);
            }
            RebuildFrame::Value(value, depth) => {
                work::rebuild_at_depth(depth);
                frames.push(RebuildFrame::FinishValue {
                    value,
                    result_mark: results.len(),
                });
                push_rewrite_value_children(&mut frames, value, depth + 1);
            }
            RebuildFrame::Pattern(pattern) => {
                results.push(Rebuilt::Pattern(rewriter.pattern(pattern, cx)));
            }
            RebuildFrame::Binder(binder) => {
                results.push(Rebuilt::Binder(rewriter.binder(binder, cx)));
            }
            RebuildFrame::Instantiation(instantiation) => {
                results.push(Rebuilt::Instantiation(
                    rewriter.instantiation(instantiation, cx),
                ));
            }
            RebuildFrame::Forward(forward) => {
                results.push(Rebuilt::Forward(rewriter.forward(forward, cx)));
            }
            RebuildFrame::FinishFunction {
                function,
                result_mark,
            } => {
                let mut children = results.drain(result_mark..);
                let params = next_binders(&mut children, function.params().len());
                let body = next_comp(&mut children);
                let extra = children.next();
                debug_assert!(extra.is_none());
                drop(children);
                results.push(Rebuilt::Function(Box::new(TypedCoreFn::new(
                    function.name(),
                    params,
                    body,
                    rewriter.fn_sig(function.sig(), cx),
                    function.dict_arity(),
                ))));
            }
            RebuildFrame::FinishComp { comp, result_mark } => {
                let mut children = results.drain(result_mark..);
                let comp = rebuild_comp(rewriter, comp, &mut children, cx);
                let extra = children.next();
                debug_assert!(extra.is_none());
                drop(children);
                results.push(Rebuilt::Comp(Box::new(comp)));
            }
            RebuildFrame::FinishValue { value, result_mark } => {
                let mut children = results.drain(result_mark..);
                let value = rebuild_value(rewriter, value, &mut children, cx);
                let extra = children.next();
                debug_assert!(extra.is_none());
                drop(children);
                results.push(Rebuilt::Value(value));
            }
        }
    }

    debug_assert_eq!(results.len(), 1);
    results
        .pop()
        .expect("typed rewrite produces one root result")
}
