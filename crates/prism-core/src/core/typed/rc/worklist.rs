//! Explicit reducers for typed reference-count insertion.

use std::collections::{BTreeMap, VecDeque};

use crate::core::builtins::{Builtin, FloatOp};
use crate::core::fbip::Sigs;
use crate::core::{IoOp, NegLane};
use crate::types::ty::EffRow;
use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use super::super::specialize_support::{binder_occurrence, free_comp_vars};
use super::super::traverse::discard_reference;
use super::super::verify::{clone_comp_sig, clone_core_type};
use super::super::{
    CompSig, CoreInstantiation, EffectLowered, LoweredReprProof, Owned, TypedBinder, TypedComp,
    TypedCompKind, TypedCore, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind,
    UncheckedTypedCore,
};
use super::census::{borrowed_call_vars, leaf_census, Census};
use super::ops::{defer_call_drops, drop_, dup, dup_each, seq};
use super::scope::{bind_scope, operand, unbind_scope, Scope, ScopeUndo};
use super::spine::{alias_source, SpineLevel, SpineState, SpineStep};
use super::{
    anchored_borrow_arg, borrowed_at, by_name, pattern_binders, referenced_binding, rename, Set,
};

struct CaseState {
    sig: CompSig,
    scrutinee: TypedValue,
    arms: VecDeque<(TypedPattern, TypedComp)>,
    built: Vec<(TypedPattern, TypedComp)>,
    owned: Set,
    borrowed: Set,
    tracked: Set,
    loaned: bool,
}

enum ValueBuild {
    Reinterpret,
    Lowered(LoweredReprProof),
    Newtype(Sym, Vec<CoreInstantiation>),
    Ctor(Sym, usize, Vec<CoreInstantiation>),
    Tuple,
    UnboxedTuple,
    UnboxedRecord(Vec<Sym>),
}

enum CompBuild {
    Return,
    Force,
    Error,
    Io(IoOp),
    Float(FloatOp),
    Neg(NegLane),
    Prim(crate::core::CoreOp),
    Call(Sym, Vec<CoreInstantiation>),
    Do(Sym, Vec<CoreInstantiation>),
    Str(Builtin, Vec<CoreInstantiation>),
    App(Vec<CoreInstantiation>),
    RefNew,
    RefGet,
    RefSet,
    InitAt,
}

enum Task {
    RcComp(TypedComp, Set, Set),
    FinishIfYes(CompSig, TypedValue, TypedComp, Set, Set),
    FinishIfNo(CompSig, TypedValue, TypedComp),
    FinishLam(CompSig, Vec<TypedBinder>, ScopeUndo),
    FinishMask(CompSig, Vec<Sym>),
    CaseNext(CaseState),
    FinishCaseArm(CaseState, TypedPattern, Vec<Sym>, Vec<Sym>, ScopeUndo),
    SpineNext(SpineState),
    FinishSpineStep(
        SpineState,
        Box<SpineStep>,
        Vec<TypedValue>,
        Vec<TypedValue>,
        bool,
    ),
    FinishSpineTail(SpineState),
    FinishLeaf(Set, Set, Census, Set),
    ThunkComp(TypedComp),
    FinishThunkComp(CompSig, CompBuild, usize),
    Value(TypedValue),
    FinishValue(CoreTypeSlot, ValueBuild, usize),
    FinishThunkValue(CoreTypeSlot),
}

// Naming the slot keeps the reducers readable without giving type evidence a
// second representation.
type CoreTypeSlot = super::super::CoreType;

struct Inserter<'a> {
    sigs: &'a Sigs,
    scope: Scope,
    fresh: Fresh,
    tasks: Vec<Task>,
    comps: Vec<TypedComp>,
    values: Vec<TypedValue>,
}

impl<'a> Inserter<'a> {
    const fn new(sigs: &'a Sigs) -> Self {
        Self {
            sigs,
            scope: Scope::new(),
            fresh: Fresh::new(),
            tasks: Vec::new(),
            comps: Vec::new(),
            values: Vec::new(),
        }
    }

    fn run(&mut self, comp: TypedComp, owned: Set, borrowed: Set) -> TypedComp {
        debug_assert!(self.tasks.is_empty());
        debug_assert!(self.comps.is_empty());
        debug_assert!(self.values.is_empty());
        self.tasks.push(Task::RcComp(comp, owned, borrowed));
        while let Some(task) = self.tasks.pop() {
            self.step(task);
        }
        debug_assert!(self.values.is_empty());
        debug_assert_eq!(self.comps.len(), 1);
        self.comps
            .pop()
            .expect("RC reducer produces one computation")
    }

    #[allow(clippy::too_many_lines)]
    fn step(&mut self, task: Task) {
        match task {
            Task::RcComp(comp, owned, borrowed) => self.rc_comp(comp, owned, borrowed),
            Task::FinishIfYes(sig, condition, no, owned, borrowed) => {
                let yes = self.pop_comp();
                self.tasks.push(Task::FinishIfNo(sig, condition, yes));
                self.tasks.push(Task::RcComp(no, owned, borrowed));
            }
            Task::FinishIfNo(sig, condition, yes) => {
                let no = self.pop_comp();
                self.comps.push(TypedComp::new(
                    sig,
                    TypedCompKind::If(condition, Box::new(yes), Box::new(no)),
                ));
            }
            Task::FinishLam(sig, params, undo) => {
                let body = self.pop_comp();
                unbind_scope(&mut self.scope, undo);
                self.comps.push(TypedComp::new(
                    sig,
                    TypedCompKind::Lam(params, Box::new(body)),
                ));
            }
            Task::FinishMask(sig, effects) => {
                let body = self.pop_comp();
                self.comps.push(TypedComp::new(
                    sig,
                    TypedCompKind::Mask(effects, Box::new(body)),
                ));
            }
            Task::CaseNext(state) => self.case_next(state),
            Task::FinishCaseArm(mut state, pattern, live, dead, undo) => {
                let mut body = self.pop_comp();
                for name in dead {
                    body = drop_(name, body, &self.scope);
                }
                if !state.loaned {
                    for name in live.into_iter().rev() {
                        body = dup(operand(&self.scope, name), body);
                    }
                }
                unbind_scope(&mut self.scope, undo);
                state.built.push((pattern, body));
                self.tasks.push(Task::CaseNext(state));
            }
            Task::SpineNext(state) => self.spine_next(state),
            Task::FinishSpineStep(state, step, shared, dead, alias) => {
                let first = self.pop_comp();
                self.finish_spine_step(state, *step, first, shared, dead, alias);
            }
            Task::FinishSpineTail(state) => {
                let mut out = self.pop_comp();
                unbind_scope(&mut self.scope, state.undo);
                for level in state.levels.into_iter().rev() {
                    out = TypedComp::new(
                        level.sig,
                        TypedCompKind::Bind(Box::new(level.first), level.binder, Box::new(out)),
                    );
                    for value in level.shared_ops {
                        out = dup(value, out);
                    }
                    for value in level.dead_ops {
                        out = seq(
                            TypedComp::new(super::ops::pure_unit(), TypedCompKind::Drop(value)),
                            out,
                        );
                    }
                }
                self.comps.push(out);
            }
            Task::FinishLeaf(owned, borrowed, mut census, deferred) => {
                let mut out = self.pop_comp();
                if !deferred.is_empty() {
                    out = defer_call_drops(out, &deferred, &self.scope, &mut self.fresh);
                }
                for name in by_name(owned) {
                    let mut seen = census.remove(&name).unwrap_or_default();
                    if deferred.contains(&name) {
                        out = dup_each(seen, out);
                    } else if seen.is_empty() {
                        out = drop_(name, out, &self.scope);
                    } else {
                        discard_reference(seen.remove(0));
                        out = dup_each(seen, out);
                    }
                }
                for name in by_name(borrowed) {
                    out = dup_each(census.remove(&name).unwrap_or_default(), out);
                }
                for witnesses in census.into_values() {
                    for witness in witnesses {
                        discard_reference(witness);
                    }
                }
                self.comps.push(out);
            }
            Task::ThunkComp(comp) => self.thunk_comp(comp),
            Task::FinishThunkComp(sig, build, count) => {
                self.finish_thunk_comp(sig, build, count);
            }
            Task::Value(value) => self.value(value),
            Task::FinishValue(ty, build, count) => self.finish_value(ty, build, count),
            Task::FinishThunkValue(ty) => {
                let body = self.pop_comp();
                self.values
                    .push(TypedValue::new(ty, TypedValueKind::Thunk(Box::new(body))));
            }
        }
    }

    fn rc_comp(&mut self, comp: TypedComp, owned: Set, borrowed: Set) {
        match comp.kind {
            TypedCompKind::Bind(first, binder, rest) => {
                let comp = TypedComp::new(comp.sig, TypedCompKind::Bind(first, binder, rest));
                self.tasks
                    .push(Task::SpineNext(SpineState::new(comp, owned, borrowed)));
            }
            TypedCompKind::If(condition, yes, no) => {
                self.tasks.push(Task::FinishIfYes(
                    comp.sig,
                    condition,
                    *no,
                    owned.clone(),
                    borrowed.clone(),
                ));
                self.tasks.push(Task::RcComp(*yes, owned, borrowed));
            }
            TypedCompKind::Case(scrutinee, arms) => {
                let loaned =
                    referenced_binding(&scrutinee).is_some_and(|name| borrowed.contains(&name));
                let tracked = owned.union(&borrowed).copied().collect();
                self.tasks.push(Task::CaseNext(CaseState {
                    sig: comp.sig,
                    scrutinee,
                    arms: arms.into(),
                    built: Vec::new(),
                    owned,
                    borrowed,
                    tracked,
                    loaned,
                }));
            }
            TypedCompKind::Lam(params, body) => {
                let params_set = params.iter().map(|binder| binder.name).collect();
                let captures = free_comp_vars(&body)
                    .difference(&params_set)
                    .copied()
                    .collect();
                let undo = bind_scope(&mut self.scope, &params);
                self.tasks.push(Task::FinishLam(comp.sig, params, undo));
                self.tasks.push(Task::RcComp(*body, params_set, captures));
            }
            TypedCompKind::Mask(effects, body) => {
                self.tasks.push(Task::FinishMask(comp.sig, effects));
                self.tasks.push(Task::RcComp(*body, owned, borrowed));
            }
            TypedCompKind::Handle { .. } => {
                unreachable!("effect lowering removes every Handle before reference counting")
            }
            kind => {
                let comp = TypedComp::new(comp.sig, kind);
                match rebind_borrowed_temporaries(comp, self.sigs, &mut self.fresh) {
                    Rebind::Anchored(anchored) => {
                        self.tasks.push(Task::RcComp(anchored, owned, borrowed));
                    }
                    Rebind::Leaf(comp) => {
                        let mut census = Census::new();
                        leaf_census(&comp, &mut census, self.sigs);
                        let borrowed_call = borrowed_call_vars(&comp, self.sigs);
                        let deferred = owned.intersection(&borrowed_call).copied().collect();
                        self.tasks
                            .push(Task::FinishLeaf(owned, borrowed, census, deferred));
                        self.tasks.push(Task::ThunkComp(comp));
                    }
                }
            }
        }
    }

    fn case_next(&mut self, mut state: CaseState) {
        let Some((mut pattern, mut body)) = state.arms.pop_front() else {
            self.comps.push(TypedComp::new(
                state.sig,
                TypedCompKind::Case(state.scrutinee, state.built),
            ));
            return;
        };
        let renames = unshadow_arm(&mut pattern, &state.tracked, &mut self.fresh);
        if !renames.is_empty() {
            rename::comp(&mut body, renames);
        }
        let body_free = free_comp_vars(&body);
        let binders = pattern_binders(&pattern);
        let fields: Set = binders.iter().map(|binder| binder.name).collect();
        let live = by_name(fields.intersection(&body_free).copied());
        let dead = by_name(
            state
                .owned
                .iter()
                .filter(|name| !body_free.contains(*name))
                .copied(),
        );
        let mut body_owned: Set = state.owned.intersection(&body_free).copied().collect();
        let mut body_borrowed: Set = state.borrowed.intersection(&body_free).copied().collect();
        if state.loaned {
            body_borrowed.extend(live.iter().copied());
        } else {
            body_owned.extend(live.iter().copied());
        }
        let undo = bind_scope(&mut self.scope, binders);
        self.tasks
            .push(Task::FinishCaseArm(state, pattern, live, dead, undo));
        self.tasks
            .push(Task::RcComp(body, body_owned, body_borrowed));
    }

    #[allow(clippy::too_many_lines)]
    fn spine_next(&mut self, mut state: SpineState) {
        let Some(mut step) = state.steps.pop_front() else {
            let tail = state.tail.take().expect("spine tail is consumed once");
            let tail_owned = state.owned.clone();
            let tail_borrowed = state.borrowed.clone();
            self.tasks.push(Task::FinishSpineTail(state));
            self.tasks
                .push(Task::RcComp(tail, tail_owned, tail_borrowed));
            return;
        };
        state.remove_first_contribution(&step.first_refs);
        let first_owned: Set = state
            .owned
            .iter()
            .filter(|name| step.first_refs.contains_key(*name))
            .copied()
            .collect();
        let rest_owned: Set = state
            .owned
            .iter()
            .filter(|name| state.live.contains_key(*name))
            .copied()
            .collect();
        let shared = by_name(
            first_owned
                .iter()
                .filter(|name| rest_owned.contains(*name))
                .copied(),
        );
        let dead = by_name(
            state
                .owned
                .iter()
                .filter(|name| {
                    !step.first_refs.contains_key(*name) && !state.live.contains_key(*name)
                })
                .copied(),
        );
        let first_borrowed = state
            .borrowed
            .iter()
            .filter(|name| step.first_refs.contains_key(*name))
            .copied()
            .collect();
        let rest_borrowed: Set = state
            .borrowed
            .iter()
            .filter(|name| state.live.contains_key(*name))
            .copied()
            .collect();
        let alias = step.binder.name.as_str() != "_"
            && alias_source(step.first.as_ref().expect("spine first is present"))
                .is_some_and(|name| state.borrowed.contains(&name));
        let shared_ops = shared
            .into_iter()
            .map(|name| {
                step.first_refs
                    .remove(&name)
                    .expect("shared name has a first occurrence")
            })
            .collect();
        for witness in std::mem::take(&mut step.first_refs).into_values() {
            discard_reference(witness);
        }
        let dead_ops = dead
            .into_iter()
            .map(|name| operand(&self.scope, name))
            .collect();
        state.owned = rest_owned;
        state.borrowed = rest_borrowed;
        let first = step.first.take().expect("spine first is consumed once");
        if alias {
            self.finish_spine_step(state, step, first, shared_ops, dead_ops, true);
        } else {
            self.tasks.push(Task::FinishSpineStep(
                state,
                Box::new(step),
                shared_ops,
                dead_ops,
                false,
            ));
            self.tasks
                .push(Task::RcComp(first, first_owned, first_borrowed));
        }
    }

    fn finish_spine_step(
        &mut self,
        mut state: SpineState,
        step: SpineStep,
        first: TypedComp,
        shared_ops: Vec<TypedValue>,
        dead_ops: Vec<TypedValue>,
        alias: bool,
    ) {
        let name = step.binder.name;
        state.undo.push((
            name,
            self.scope.insert(name, binder_occurrence(&step.binder)),
        ));
        if alias {
            state.borrowed.insert(name);
        } else {
            state.owned.insert(name);
        }
        if step.prev_count > 0 {
            state.live.insert(name, step.prev_count);
        }
        state.levels.push(SpineLevel {
            sig: step.sig,
            binder: step.binder,
            first,
            shared_ops,
            dead_ops,
        });
        self.tasks.push(Task::SpineNext(state));
    }

    fn thunk_comp(&mut self, comp: TypedComp) {
        let TypedComp { sig, kind } = comp;
        match kind {
            TypedCompKind::Return(value) => self.one_value(sig, CompBuild::Return, value),
            TypedCompKind::Force(value) => self.one_value(sig, CompBuild::Force, value),
            TypedCompKind::Error(value) => self.one_value(sig, CompBuild::Error, value),
            TypedCompKind::Io(op, args) => self.many_values(sig, CompBuild::Io(op), args),
            TypedCompKind::FloatBuiltin(op, value) => {
                self.one_value(sig, CompBuild::Float(op), value);
            }
            TypedCompKind::Neg(lane, value) => {
                self.one_value(sig, CompBuild::Neg(lane), value);
            }
            TypedCompKind::Prim(op, left, right) => {
                self.many_values(sig, CompBuild::Prim(op), vec![left, right]);
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => self.many_values(sig, CompBuild::Call(callee, instantiation), args),
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => self.many_values(sig, CompBuild::Do(operation, instantiation), args),
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => self.many_values(sig, CompBuild::Str(op, instantiation), args),
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let count = args.len();
                self.tasks.push(Task::FinishThunkComp(
                    sig,
                    CompBuild::App(instantiation),
                    count,
                ));
                for argument in args.into_iter().rev() {
                    self.tasks.push(Task::Value(argument));
                }
                self.tasks.push(Task::ThunkComp(*callee));
            }
            TypedCompKind::RefNew(value) => self.one_value(sig, CompBuild::RefNew, value),
            TypedCompKind::RefGet(value) => self.one_value(sig, CompBuild::RefGet, value),
            TypedCompKind::RefSet(cell, value) => {
                self.many_values(sig, CompBuild::RefSet, vec![cell, value]);
            }
            TypedCompKind::InitAt(cell, value) => {
                self.many_values(sig, CompBuild::InitAt, vec![cell, value]);
            }
            kind => self.comps.push(TypedComp::new(sig, kind)),
        }
    }

    fn one_value(&mut self, sig: CompSig, build: CompBuild, value: TypedValue) {
        self.tasks.push(Task::FinishThunkComp(sig, build, 1));
        self.tasks.push(Task::Value(value));
    }

    fn many_values(&mut self, sig: CompSig, build: CompBuild, values: Vec<TypedValue>) {
        let count = values.len();
        self.tasks.push(Task::FinishThunkComp(sig, build, count));
        for value in values.into_iter().rev() {
            self.tasks.push(Task::Value(value));
        }
    }

    #[allow(clippy::too_many_lines)]
    fn finish_thunk_comp(&mut self, sig: CompSig, build: CompBuild, count: usize) {
        let mut values = self.take_values(count).into_iter();
        let kind = match build {
            CompBuild::Return => TypedCompKind::Return(values.next().unwrap()),
            CompBuild::Force => TypedCompKind::Force(values.next().unwrap()),
            CompBuild::Error => TypedCompKind::Error(values.next().unwrap()),
            CompBuild::Io(op) => TypedCompKind::Io(op, values.collect()),
            CompBuild::Float(op) => TypedCompKind::FloatBuiltin(op, values.next().unwrap()),
            CompBuild::Neg(lane) => TypedCompKind::Neg(lane, values.next().unwrap()),
            CompBuild::Prim(op) => {
                TypedCompKind::Prim(op, values.next().unwrap(), values.next().unwrap())
            }
            CompBuild::Call(callee, instantiation) => TypedCompKind::Call {
                callee,
                instantiation,
                args: values.collect(),
            },
            CompBuild::Do(operation, instantiation) => TypedCompKind::Do {
                operation,
                instantiation,
                args: values.collect(),
            },
            CompBuild::Str(op, instantiation) => TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args: values.collect(),
            },
            CompBuild::App(instantiation) => TypedCompKind::App {
                callee: Box::new(self.pop_comp()),
                instantiation,
                args: values.collect(),
            },
            CompBuild::RefNew => TypedCompKind::RefNew(values.next().unwrap()),
            CompBuild::RefGet => TypedCompKind::RefGet(values.next().unwrap()),
            CompBuild::RefSet => {
                TypedCompKind::RefSet(values.next().unwrap(), values.next().unwrap())
            }
            CompBuild::InitAt => {
                TypedCompKind::InitAt(values.next().unwrap(), values.next().unwrap())
            }
        };
        self.comps.push(TypedComp::new(sig, kind));
    }

    fn value(&mut self, value: TypedValue) {
        let TypedValue { ty, kind } = value;
        match kind {
            TypedValueKind::Thunk(body) => {
                let captures = free_comp_vars(&body);
                self.tasks.push(Task::FinishThunkValue(ty));
                self.tasks.push(Task::RcComp(*body, Set::new(), captures));
            }
            TypedValueKind::Reinterpret(inner) => {
                self.one_inner(ty, ValueBuild::Reinterpret, *inner);
            }
            TypedValueKind::LoweredRepr { value, proof } => {
                self.one_inner(ty, ValueBuild::Lowered(proof), *value);
            }
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => self.one_inner(ty, ValueBuild::Newtype(constructor, instantiation), *value),
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => self.value_fields(ty, ValueBuild::Ctor(name, tag, instantiation), fields),
            TypedValueKind::Tuple(fields) => {
                self.value_fields(ty, ValueBuild::Tuple, fields);
            }
            TypedValueKind::UnboxedTuple(fields) => {
                self.value_fields(ty, ValueBuild::UnboxedTuple, fields);
            }
            TypedValueKind::UnboxedRecord(fields) => {
                let (names, values) = fields.into_iter().unzip();
                self.value_fields(ty, ValueBuild::UnboxedRecord(names), values);
            }
            kind => self.values.push(TypedValue::new(ty, kind)),
        }
    }

    fn one_inner(&mut self, ty: CoreTypeSlot, build: ValueBuild, value: TypedValue) {
        self.tasks.push(Task::FinishValue(ty, build, 1));
        self.tasks.push(Task::Value(value));
    }

    fn value_fields(&mut self, ty: CoreTypeSlot, build: ValueBuild, fields: Vec<TypedValue>) {
        let count = fields.len();
        self.tasks.push(Task::FinishValue(ty, build, count));
        for field in fields.into_iter().rev() {
            self.tasks.push(Task::Value(field));
        }
    }

    fn finish_value(&mut self, ty: CoreTypeSlot, build: ValueBuild, count: usize) {
        let fields = self.take_values(count);
        let kind = match build {
            ValueBuild::Reinterpret => TypedValueKind::Reinterpret(Box::new(one(fields))),
            ValueBuild::Lowered(proof) => TypedValueKind::LoweredRepr {
                value: Box::new(one(fields)),
                proof,
            },
            ValueBuild::Newtype(constructor, instantiation) => TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value: Box::new(one(fields)),
            },
            ValueBuild::Ctor(name, tag, instantiation) => TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            },
            ValueBuild::Tuple => TypedValueKind::Tuple(fields),
            ValueBuild::UnboxedTuple => TypedValueKind::UnboxedTuple(fields),
            ValueBuild::UnboxedRecord(names) => {
                TypedValueKind::UnboxedRecord(names.into_iter().zip(fields).collect())
            }
        };
        self.values.push(TypedValue::new(ty, kind));
    }

    fn pop_comp(&mut self) -> TypedComp {
        self.comps
            .pop()
            .expect("computation continuation has a result")
    }

    fn take_values(&mut self, count: usize) -> Vec<TypedValue> {
        self.values.split_off(self.values.len() - count)
    }
}

fn one(mut values: Vec<TypedValue>) -> TypedValue {
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("unary value reducer has one result")
}

fn unshadow_arm(
    pattern: &mut TypedPattern,
    tracked: &Set,
    fresh: &mut Fresh,
) -> BTreeMap<Sym, Sym> {
    let mut renames = BTreeMap::new();
    let mut rebind = |binder: &mut TypedBinder| {
        if tracked.contains(&binder.name) {
            let shadowed = binder.name;
            binder.name = Sym::from(names::fresh_binder(names::FRESH_RC, fresh.bump()));
            renames.insert(shadowed, binder.name);
        }
    };
    match pattern {
        TypedPattern::Wild => {}
        TypedPattern::Var(binder) => rebind(binder),
        TypedPattern::Ctor { fields, .. } | TypedPattern::Tuple(fields) => {
            for binder in fields.iter_mut().flatten() {
                rebind(binder);
            }
        }
    }
    renames
}

/// Whether anchoring rewrote the leaf: an anchored call re-enters the
/// worklist, an untouched leaf goes straight to its census.
enum Rebind {
    Anchored(TypedComp),
    Leaf(TypedComp),
}

fn rebind_borrowed_temporaries(comp: TypedComp, sigs: &Sigs, fresh: &mut Fresh) -> Rebind {
    let TypedComp { sig, kind } = comp;
    let TypedCompKind::Call {
        callee,
        instantiation,
        args,
    } = kind
    else {
        return Rebind::Leaf(TypedComp::new(sig, kind));
    };
    let mask = sigs.get(&callee).map(Vec::as_slice);
    if !args
        .iter()
        .enumerate()
        .any(|(index, arg)| borrowed_at(mask, index) && !anchored_borrow_arg(arg))
    {
        return Rebind::Leaf(TypedComp::new(
            sig,
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            },
        ));
    }

    let mut anchors = Vec::new();
    let args = args
        .into_iter()
        .enumerate()
        .map(|(index, argument)| {
            if !borrowed_at(mask, index) || anchored_borrow_arg(&argument) {
                return argument;
            }
            let binder = TypedBinder::new(
                Sym::from(names::fresh_binder(names::FRESH_RC, fresh.bump())),
                clone_core_type(argument.ty()),
            );
            let anchored = binder_occurrence(&binder);
            anchors.push((binder, argument));
            anchored
        })
        .collect();
    let mut out = TypedComp::new(
        clone_comp_sig(&sig),
        TypedCompKind::Call {
            callee,
            instantiation,
            args,
        },
    );
    let mut anchors = anchors.into_iter().rev().peekable();
    let mut outer_sig = Some(sig);
    while let Some((binder, value)) = anchors.next() {
        let returned = TypedComp::new(
            CompSig::new(clone_core_type(value.ty()), EffRow::Empty),
            TypedCompKind::Return(value),
        );
        let bind_sig = if anchors.peek().is_none() {
            outer_sig
                .take()
                .expect("outer call signature is consumed once")
        } else {
            clone_comp_sig(outer_sig.as_ref().unwrap())
        };
        out = TypedComp::new(
            bind_sig,
            TypedCompKind::Bind(Box::new(returned), binder, Box::new(out)),
        );
    }
    Rebind::Anchored(out)
}

pub(super) fn insert(core: TypedCore<EffectLowered>, sigs: &Sigs) -> UncheckedTypedCore<Owned> {
    let mut inserter = Inserter::new(sigs);
    let mut functions = Vec::new();
    for function in core.into_unchecked().into_functions() {
        let mask = sigs.get(&function.name).map(Vec::as_slice);
        let owned = function
            .params
            .iter()
            .enumerate()
            .filter(|(index, _)| !borrowed_at(mask, *index))
            .map(|(_, binder)| binder.name)
            .collect();
        let borrowed = function
            .params
            .iter()
            .enumerate()
            .filter(|(index, _)| borrowed_at(mask, *index))
            .map(|(_, binder)| binder.name)
            .collect();
        let undo = bind_scope(&mut inserter.scope, &function.params);
        let body = inserter.run(function.body, owned, borrowed);
        unbind_scope(&mut inserter.scope, undo);
        functions.push(TypedCoreFn::new(
            function.name,
            function.params,
            body,
            function.sig,
            function.dict_arity,
        ));
    }
    UncheckedTypedCore::new(functions)
}
