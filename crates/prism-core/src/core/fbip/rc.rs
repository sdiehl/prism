use std::{collections::BTreeMap, rc::Rc};

use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use crate::core::cbpv::{CheckedHandler, Comp, Core, CoreFn, CorePat, HandleOp, Value};
use crate::core::fv::{comp as freev, pat_vars};
use crate::core::traverse::{Rewrite, RewriteControl};

use super::{borrow_mask, borrowed_at, count_val, scalar_without_cell, Set, Sigs};

#[must_use]
pub fn insert_rc(core: &Core, sigs: &Sigs) -> Core {
    let mut inserter = RcInserter::new(sigs);
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| {
                let mask = sigs.get(&f.name).map(Vec::as_slice);
                let owned: Set = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !borrowed_at(mask, *i))
                    .map(|(_, p)| *p)
                    .collect();
                let borrowed: Set = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| borrowed_at(mask, *i))
                    .map(|(_, p)| *p)
                    .collect();
                CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    dict_arity: f.dict_arity,
                    body: inserter.rewrite_comp(&f.body, owned, borrowed),
                }
            })
            .collect(),
    }
}

// Emit dup/drop in a name-stable order. `Sym` orders by intern id (first-seen),
// so iterating a `Set` directly would make the inserted ops depend on interning
// order. Sorting by name keeps codegen output byte-stable.
fn by_name(syms: impl IntoIterator<Item = Sym>) -> Vec<Sym> {
    let mut v: Vec<Sym> = syms.into_iter().collect();
    v.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    v
}

fn seq(op: Comp, k: Comp) -> Comp {
    Comp::Bind(Box::new(op), "_".into(), Box::new(k))
}

fn dup(v: Sym, k: Comp) -> Comp {
    seq(Comp::Dup(Value::Var(v)), k)
}

fn drop_(v: Sym, k: Comp) -> Comp {
    seq(Comp::Drop(Value::Var(v)), k)
}

fn after_borrowed_call(call: Comp, deferred: &[Sym], fresh: &mut Fresh) -> Comp {
    if deferred.is_empty() {
        return call;
    }
    let result_name = names::fresh_binder(names::FRESH_RC, fresh.bump());
    let result = Sym::from(result_name.as_str());
    let mut post = Comp::Return(Value::Var(result));
    for var in deferred {
        post = drop_(*var, post);
    }
    Comp::Bind(Box::new(call), result, Box::new(post))
}

type Renames = BTreeMap<Sym, Sym>;
type SharedSet = Rc<Set>;
type SharedRenames = Rc<Renames>;

// Case alpha-renames remain a scope context until reconstruction, avoiding a
// second deep owned tree that would immediately be discarded after RC insertion.
struct ArmInput<'a> {
    pattern: &'a CorePat,
    body: &'a Comp,
    owned: SharedSet,
    borrowed: SharedSet,
    tracked: SharedSet,
    renames: SharedRenames,
    loaned: bool,
}

enum Built {
    Comp(Comp),
    Value(Value),
    Arm(CorePat, Comp),
}

enum RcFrame<'a> {
    Comp {
        source: &'a Comp,
        owned: SharedSet,
        borrowed: SharedSet,
        renames: SharedRenames,
    },
    Value {
        source: &'a Value,
        renames: SharedRenames,
    },
    ThunkComp {
        source: &'a Comp,
        renames: SharedRenames,
    },
    Arm(ArmInput<'a>),
    FinishBind {
        binder: Sym,
        shared: Vec<Sym>,
        dead: Vec<Sym>,
    },
    FinishIf {
        condition: Value,
    },
    FinishCase {
        scrutinee: Value,
        arm_count: usize,
    },
    FinishArm {
        pattern: CorePat,
        dead: Vec<Sym>,
        live: Vec<Sym>,
        loaned: bool,
    },
    FinishLam {
        params: Vec<Sym>,
    },
    FinishMask {
        effects: Vec<Sym>,
    },
    FinishHandle {
        return_var: Option<Sym>,
        has_return_body: bool,
        ops: &'a CheckedHandler,
    },
    FinishLeaf {
        counts: BTreeMap<Sym, usize>,
        borrowed_uses: Set,
        deferred: Vec<Sym>,
        owned: Vec<Sym>,
        borrowed: Vec<Sym>,
    },
    FinishValue(&'a Value),
    FinishThunkComp(&'a Comp),
}

struct RcInserter<'a> {
    sigs: &'a Sigs,
    fresh: Fresh,
    frames: Vec<RcFrame<'a>>,
    built: Vec<Built>,
}

impl<'a> RcInserter<'a> {
    const fn new(sigs: &'a Sigs) -> Self {
        Self {
            sigs,
            fresh: Fresh::new(),
            frames: Vec::new(),
            built: Vec::new(),
        }
    }

    fn rewrite_comp(&mut self, source: &'a Comp, owned: Set, borrowed: Set) -> Comp {
        debug_assert!(self.frames.is_empty());
        debug_assert!(self.built.is_empty());
        self.frames.push(RcFrame::Comp {
            source,
            owned: Rc::new(owned),
            borrowed: Rc::new(borrowed),
            renames: Rc::new(Renames::new()),
        });
        while let Some(frame) = self.frames.pop() {
            self.step(frame);
        }
        debug_assert_eq!(self.built.len(), 1);
        pop_comp(&mut self.built)
    }

    fn step(&mut self, frame: RcFrame<'a>) {
        match frame {
            RcFrame::Comp {
                source,
                owned,
                borrowed,
                renames,
            } => self.comp(source, owned, borrowed, renames),
            RcFrame::Value { source, renames } => self.value(source, renames),
            RcFrame::ThunkComp { source, renames } => self.thunk_comp(source, renames),
            RcFrame::Arm(arm) => self.arm(&arm),
            RcFrame::FinishBind {
                binder,
                shared,
                dead,
            } => {
                let rest = pop_comp(&mut self.built);
                let first = pop_comp(&mut self.built);
                let mut out = Comp::Bind(Box::new(first), binder, Box::new(rest));
                for var in shared {
                    out = dup(var, out);
                }
                for var in dead {
                    out = drop_(var, out);
                }
                self.built.push(Built::Comp(out));
            }
            RcFrame::FinishIf { condition } => {
                let alternative = pop_comp(&mut self.built);
                let consequent = pop_comp(&mut self.built);
                self.built.push(Built::Comp(Comp::If(
                    condition,
                    Box::new(consequent),
                    Box::new(alternative),
                )));
            }
            RcFrame::FinishCase {
                scrutinee,
                arm_count,
            } => {
                let arms = take_arms(&mut self.built, arm_count);
                self.built.push(Built::Comp(Comp::Case(scrutinee, arms)));
            }
            RcFrame::FinishArm {
                pattern,
                dead,
                live,
                loaned,
            } => {
                let mut body = pop_comp(&mut self.built);
                for var in dead {
                    body = drop_(var, body);
                }
                if !loaned {
                    for var in live.into_iter().rev() {
                        body = dup(var, body);
                    }
                }
                self.built.push(Built::Arm(pattern, body));
            }
            RcFrame::FinishLam { params } => {
                let body = pop_comp(&mut self.built);
                self.built
                    .push(Built::Comp(Comp::Lam(params, Box::new(body))));
            }
            RcFrame::FinishMask { effects } => {
                let body = pop_comp(&mut self.built);
                self.built
                    .push(Built::Comp(Comp::Mask(effects, Box::new(body))));
            }
            RcFrame::FinishHandle {
                return_var,
                has_return_body,
                ops,
            } => self.finish_handle(return_var, has_return_body, ops),
            RcFrame::FinishLeaf {
                counts,
                borrowed_uses,
                deferred,
                owned,
                borrowed,
            } => {
                let mut out = pop_comp(&mut self.built);
                out = after_borrowed_call(out, &deferred, &mut self.fresh);
                for var in owned {
                    let count = counts.get(&var).copied().unwrap_or(0);
                    if borrowed_uses.contains(&var) {
                        for _ in 0..count {
                            out = dup(var, out);
                        }
                    } else {
                        match count {
                            0 => out = drop_(var, out),
                            count => {
                                for _ in 1..count {
                                    out = dup(var, out);
                                }
                            }
                        }
                    }
                }
                for var in borrowed {
                    for _ in 0..counts.get(&var).copied().unwrap_or(0) {
                        out = dup(var, out);
                    }
                }
                self.built.push(Built::Comp(out));
            }
            RcFrame::FinishValue(source) => {
                let value = rebuild_value(source, &mut self.built);
                self.built.push(Built::Value(value));
            }
            RcFrame::FinishThunkComp(source) => {
                let comp = rebuild_thunk_comp(source, &mut self.built);
                self.built.push(Built::Comp(comp));
            }
        }
    }

    fn comp(
        &mut self,
        source: &'a Comp,
        owned: SharedSet,
        borrowed: SharedSet,
        renames: SharedRenames,
    ) {
        match source {
            Comp::Bind(first, binder, rest) => {
                let rest_renames = scoped_renames(&renames, &[*binder]);
                let first_free = renamed_freev(first, &renames);
                let mut rest_free = renamed_freev(rest, &rest_renames);
                rest_free.remove(binder);
                let alias = binder.as_str() != "_"
                    && matches!(&**first, Comp::Return(Value::Var(var))
                        if borrowed.contains(&renamed(*var, &renames)));
                let owned_first: Set = owned.intersection(&first_free).copied().collect();
                let owned_rest: Set = owned.intersection(&rest_free).copied().collect();
                let shared = by_name(owned_first.intersection(&owned_rest).copied());
                let dead = by_name(
                    owned
                        .iter()
                        .filter(|var| !first_free.contains(*var) && !rest_free.contains(*var))
                        .copied(),
                );
                let borrowed_first = borrowed.intersection(&first_free).copied().collect();
                let mut borrowed_rest: Set = borrowed.intersection(&rest_free).copied().collect();
                let mut owned_rest = owned_rest;
                if alias {
                    borrowed_rest.insert(*binder);
                } else {
                    owned_rest.insert(*binder);
                }
                self.frames.push(RcFrame::FinishBind {
                    binder: *binder,
                    shared,
                    dead,
                });
                self.frames.push(RcFrame::Comp {
                    source: rest,
                    owned: Rc::new(owned_rest),
                    borrowed: Rc::new(borrowed_rest),
                    renames: rest_renames,
                });
                if alias {
                    self.built.push(Built::Comp(clone_comp(first, &renames)));
                } else {
                    self.frames.push(RcFrame::Comp {
                        source: first,
                        owned: Rc::new(owned_first),
                        borrowed: Rc::new(borrowed_first),
                        renames,
                    });
                }
            }
            Comp::If(condition, consequent, alternative) => {
                let condition = clone_value(condition, &renames);
                self.frames.push(RcFrame::FinishIf { condition });
                self.frames.push(RcFrame::Comp {
                    source: alternative,
                    owned: Rc::clone(&owned),
                    borrowed: Rc::clone(&borrowed),
                    renames: Rc::clone(&renames),
                });
                self.frames.push(RcFrame::Comp {
                    source: consequent,
                    owned,
                    borrowed,
                    renames,
                });
            }
            Comp::Case(scrutinee, arms) => {
                let scrutinee = clone_value(scrutinee, &renames);
                let loaned = matches!(scrutinee, Value::Var(var) if borrowed.contains(&var));
                let tracked = Rc::new(owned.union(&borrowed).copied().collect());
                self.frames.push(RcFrame::FinishCase {
                    scrutinee,
                    arm_count: arms.len(),
                });
                for (pattern, body) in arms.iter().rev() {
                    self.frames.push(RcFrame::Arm(ArmInput {
                        pattern,
                        body,
                        owned: Rc::clone(&owned),
                        borrowed: Rc::clone(&borrowed),
                        tracked: Rc::clone(&tracked),
                        renames: Rc::clone(&renames),
                        loaned,
                    }));
                }
            }
            Comp::Lam(params, body) => {
                let params_set: Set = params.iter().copied().collect();
                let body_renames = scoped_renames(&renames, params);
                let captures = renamed_freev(body, &body_renames)
                    .difference(&params_set)
                    .copied()
                    .collect();
                self.frames.push(RcFrame::FinishLam {
                    params: params.clone(),
                });
                self.frames.push(RcFrame::Comp {
                    source: body,
                    owned: Rc::new(params_set),
                    borrowed: Rc::new(captures),
                    renames: body_renames,
                });
            }
            Comp::Mask(effects, body) => {
                self.frames.push(RcFrame::FinishMask {
                    effects: effects.clone(),
                });
                self.frames.push(RcFrame::Comp {
                    source: body,
                    owned,
                    borrowed,
                    renames,
                });
            }
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                self.frames.push(RcFrame::FinishHandle {
                    return_var: *return_var,
                    has_return_body: return_body.is_some(),
                    ops,
                });
                for op in ops.iter().rev() {
                    let mut binders = op.params.clone();
                    binders.push(op.resume);
                    self.frames.push(RcFrame::Comp {
                        source: &op.body,
                        owned: Rc::new(op.params.iter().copied().collect()),
                        borrowed: Rc::new(Set::new()),
                        renames: scoped_renames(&renames, &binders),
                    });
                }
                if let Some(return_body) = return_body {
                    let binders: Vec<Sym> = return_var.iter().copied().collect();
                    self.frames.push(RcFrame::Comp {
                        source: return_body,
                        owned: Rc::new(binders.iter().copied().collect()),
                        borrowed: Rc::new(Set::new()),
                        renames: scoped_renames(&renames, &binders),
                    });
                }
                self.frames.push(RcFrame::Comp {
                    source: body,
                    owned: Rc::new(Set::new()),
                    borrowed: Rc::new(Set::new()),
                    renames,
                });
            }
            leaf => self.leaf(leaf, &owned, &borrowed, renames),
        }
    }

    fn leaf(
        &mut self,
        source: &'a Comp,
        owned: &SharedSet,
        borrowed: &SharedSet,
        renames: SharedRenames,
    ) {
        let mut counts = BTreeMap::new();
        leaf_counts(source, &mut counts, self.sigs, &renames);
        let borrowed_uses = match source {
            Comp::Call(name, args) => borrowed_uses(*name, args, self.sigs, &renames),
            _ => Set::new(),
        };
        self.frames.push(RcFrame::FinishLeaf {
            deferred: by_name(owned.intersection(&borrowed_uses).copied()),
            owned: by_name(owned.iter().copied()),
            borrowed: by_name(borrowed.iter().copied()),
            counts,
            borrowed_uses,
        });
        self.frames.push(RcFrame::ThunkComp { source, renames });
    }

    fn value(&mut self, source: &'a Value, renames: SharedRenames) {
        match source {
            Value::Thunk(body) => {
                self.frames.push(RcFrame::FinishValue(source));
                self.frames.push(RcFrame::Comp {
                    source: body,
                    owned: Rc::new(Set::new()),
                    borrowed: Rc::new(renamed_freev(body, &renames)),
                    renames,
                });
            }
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                self.frames.push(RcFrame::FinishValue(source));
                for field in fields.iter().rev() {
                    self.frames.push(RcFrame::Value {
                        source: field,
                        renames: Rc::clone(&renames),
                    });
                }
            }
            Value::UnboxedRecord(fields) => {
                self.frames.push(RcFrame::FinishValue(source));
                for (_, field) in fields.iter().rev() {
                    self.frames.push(RcFrame::Value {
                        source: field,
                        renames: Rc::clone(&renames),
                    });
                }
            }
            _ => self.built.push(Built::Value(clone_value(source, &renames))),
        }
    }

    fn thunk_comp(&mut self, source: &'a Comp, renames: SharedRenames) {
        match source {
            Comp::Return(value)
            | Comp::Force(value)
            | Comp::Error(value)
            | Comp::FloatBuiltin(_, value)
            | Comp::Neg(_, value)
            | Comp::RefNew(value)
            | Comp::RefGet(value) => {
                self.frames.push(RcFrame::FinishThunkComp(source));
                self.frames.push(RcFrame::Value {
                    source: value,
                    renames,
                });
            }
            Comp::RefSet(left, right) | Comp::Prim(_, left, right) | Comp::InitAt(left, right) => {
                self.frames.push(RcFrame::FinishThunkComp(source));
                self.frames.push(RcFrame::Value {
                    source: right,
                    renames: Rc::clone(&renames),
                });
                self.frames.push(RcFrame::Value {
                    source: left,
                    renames,
                });
            }
            Comp::Call(_, args)
            | Comp::Do(_, args)
            | Comp::StrBuiltin(_, args)
            | Comp::Io(_, args) => {
                self.frames.push(RcFrame::FinishThunkComp(source));
                for argument in args.iter().rev() {
                    self.frames.push(RcFrame::Value {
                        source: argument,
                        renames: Rc::clone(&renames),
                    });
                }
            }
            Comp::App(callee, args) => {
                self.frames.push(RcFrame::FinishThunkComp(source));
                for argument in args.iter().rev() {
                    self.frames.push(RcFrame::Value {
                        source: argument,
                        renames: Rc::clone(&renames),
                    });
                }
                self.frames.push(RcFrame::ThunkComp {
                    source: callee,
                    renames,
                });
            }
            _ => self.built.push(Built::Comp(clone_comp(source, &renames))),
        }
    }

    fn arm(&mut self, arm: &ArmInput<'a>) {
        let mut fields = Set::new();
        pat_vars(arm.pattern, &mut fields);
        let mut arm_renames =
            (*scoped_renames(&arm.renames, &by_name(fields.iter().copied()))).clone();
        let shadowing = by_name(fields.intersection(&arm.tracked).copied());
        let mut pattern = arm.pattern.clone();
        for from in shadowing {
            let to = Sym::from(names::fresh_binder(names::FRESH_RC, self.fresh.bump()).as_str());
            pattern = rename_pat(&pattern, from, to);
            arm_renames.insert(from, to);
        }
        let renames = Rc::new(arm_renames);
        let body_free = renamed_freev(arm.body, &renames);
        let mut output_fields = Set::new();
        pat_vars(&pattern, &mut output_fields);
        let live = by_name(output_fields.intersection(&body_free).copied());
        let dead = by_name(
            arm.owned
                .iter()
                .filter(|var| !body_free.contains(*var))
                .copied(),
        );
        let mut body_owned: Set = arm.owned.intersection(&body_free).copied().collect();
        let mut body_borrowed: Set = arm.borrowed.intersection(&body_free).copied().collect();
        if arm.loaned {
            body_borrowed.extend(live.iter().copied());
        } else {
            body_owned.extend(live.iter().copied());
        }
        self.frames.push(RcFrame::FinishArm {
            pattern,
            dead,
            live,
            loaned: arm.loaned,
        });
        self.frames.push(RcFrame::Comp {
            source: arm.body,
            owned: Rc::new(body_owned),
            borrowed: Rc::new(body_borrowed),
            renames,
        });
    }

    fn finish_handle(
        &mut self,
        return_var: Option<Sym>,
        has_return_body: bool,
        ops: &'a CheckedHandler,
    ) {
        let mut bodies = take_comps(
            &mut self.built,
            1 + usize::from(has_return_body) + ops.len(),
        )
        .into_iter();
        let body = Box::new(bodies.next().expect("a handler body was rebuilt"));
        let return_body =
            has_return_body.then(|| Box::new(bodies.next().expect("a return clause was rebuilt")));
        let ops = ops.rebuild(|op| HandleOp {
            name: op.name,
            params: op.params.clone(),
            resume: op.resume,
            body: bodies.next().expect("an operation clause was rebuilt"),
        });
        let extra_body = bodies.next();
        debug_assert!(extra_body.is_none());
        self.built.push(Built::Comp(Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        }));
    }
}

fn rename_pat(p: &CorePat, from: Sym, to: Sym) -> CorePat {
    let rebind = |name: &Sym| if *name == from { to } else { *name };
    let rebind_fields = |fields: &Vec<Option<Sym>>| {
        fields
            .iter()
            .map(|field| field.as_ref().map(&rebind))
            .collect()
    };
    match p {
        CorePat::Wild => CorePat::Wild,
        CorePat::Var(name) => CorePat::Var(rebind(name)),
        CorePat::Ctor(ctor, fields) => CorePat::Ctor(*ctor, rebind_fields(fields)),
        CorePat::Tuple(fields) => CorePat::Tuple(rebind_fields(fields)),
    }
}

fn renamed(name: Sym, renames: &Renames) -> Sym {
    renames.get(&name).copied().unwrap_or(name)
}

fn scoped_renames(renames: &SharedRenames, binders: &[Sym]) -> SharedRenames {
    if !binders.iter().any(|binder| renames.contains_key(binder)) {
        return Rc::clone(renames);
    }
    let mut scoped = (**renames).clone();
    for binder in binders {
        scoped.remove(binder);
    }
    Rc::new(scoped)
}

fn renamed_freev(comp: &Comp, renames: &Renames) -> Set {
    freev(comp)
        .into_iter()
        .map(|name| renamed(name, renames))
        .collect()
}

/// Rename free occurrences of locals, stopping each mapping where its source is
/// rebound.
///
/// Replacements are unforgeable fresh names, so no binder can capture one.
struct RenameFree;

impl Rewrite for RenameFree {
    type Ctx = BTreeMap<Sym, Sym>;

    fn under_scope(&mut self, binders: &[Sym], renames: &Self::Ctx) -> Self::Ctx {
        let mut visible = renames.clone();
        for binder in binders {
            visible.remove(binder);
        }
        visible
    }

    fn enter_value(&mut self, value: &Value, renames: &Self::Ctx) -> RewriteControl<Value> {
        match value {
            Value::Var(name) => renames
                .get(name)
                .map_or(RewriteControl::Descend, |replacement| {
                    RewriteControl::Replace(Value::Var(*replacement))
                }),
            _ => RewriteControl::Descend,
        }
    }
}

fn clone_comp(comp: &Comp, renames: &Renames) -> Comp {
    RenameFree.rewrite_comp(comp, renames)
}

fn clone_value(value: &Value, renames: &Renames) -> Value {
    RenameFree.rewrite_value(value, renames)
}

fn pop_comp(built: &mut Vec<Built>) -> Comp {
    match built.pop().expect("a rebuilt computation exists") {
        Built::Comp(comp) => comp,
        Built::Value(_) | Built::Arm(..) => panic!("expected a rebuilt computation"),
    }
}

fn pop_value(built: &mut Vec<Built>) -> Value {
    match built.pop().expect("a rebuilt value exists") {
        Built::Value(value) => value,
        Built::Comp(_) | Built::Arm(..) => panic!("expected a rebuilt value"),
    }
}

fn take_comps(built: &mut Vec<Built>, count: usize) -> Vec<Comp> {
    let start = built
        .len()
        .checked_sub(count)
        .expect("enough rebuilt computations exist");
    built
        .drain(start..)
        .map(|node| match node {
            Built::Comp(comp) => comp,
            Built::Value(_) | Built::Arm(..) => panic!("expected rebuilt computations"),
        })
        .collect()
}

fn take_values(built: &mut Vec<Built>, count: usize) -> Vec<Value> {
    let start = built
        .len()
        .checked_sub(count)
        .expect("enough rebuilt values exist");
    built
        .drain(start..)
        .map(|node| match node {
            Built::Value(value) => value,
            Built::Comp(_) | Built::Arm(..) => panic!("expected rebuilt values"),
        })
        .collect()
}

fn take_arms(built: &mut Vec<Built>, count: usize) -> Vec<(CorePat, Comp)> {
    let start = built
        .len()
        .checked_sub(count)
        .expect("enough rebuilt case arms exist");
    built
        .drain(start..)
        .map(|node| match node {
            Built::Arm(pattern, body) => (pattern, body),
            Built::Comp(_) | Built::Value(_) => panic!("expected rebuilt case arms"),
        })
        .collect()
}

fn rebuild_value(source: &Value, built: &mut Vec<Built>) -> Value {
    match source {
        Value::Thunk(_) => Value::Thunk(Box::new(pop_comp(built))),
        Value::Ctor(name, tag, fields) => {
            Value::Ctor(*name, *tag, take_values(built, fields.len()))
        }
        Value::Tuple(fields) => Value::Tuple(take_values(built, fields.len())),
        Value::UnboxedTuple(fields) => Value::UnboxedTuple(take_values(built, fields.len())),
        Value::UnboxedRecord(fields) => {
            let values = take_values(built, fields.len());
            Value::UnboxedRecord(
                fields
                    .iter()
                    .zip(values)
                    .map(|((name, _), value)| (*name, value))
                    .collect(),
            )
        }
        _ => unreachable!("only composite values receive a reconstruction frame"),
    }
}

fn rebuild_thunk_comp(source: &Comp, built: &mut Vec<Built>) -> Comp {
    match source {
        Comp::Return(_) => Comp::Return(pop_value(built)),
        Comp::Force(_) => Comp::Force(pop_value(built)),
        Comp::Error(_) => Comp::Error(pop_value(built)),
        Comp::Io(op, args) => Comp::Io(*op, take_values(built, args.len())),
        Comp::FloatBuiltin(op, _) => Comp::FloatBuiltin(*op, pop_value(built)),
        Comp::Neg(lane, _) => Comp::Neg(*lane, pop_value(built)),
        Comp::Prim(op, _, _) => {
            let right = pop_value(built);
            Comp::Prim(*op, pop_value(built), right)
        }
        Comp::Call(name, args) => Comp::Call(*name, take_values(built, args.len())),
        Comp::Do(name, args) => Comp::Do(*name, take_values(built, args.len())),
        Comp::StrBuiltin(op, args) => Comp::StrBuiltin(*op, take_values(built, args.len())),
        Comp::App(_, args) => {
            let args = take_values(built, args.len());
            Comp::App(Box::new(pop_comp(built)), args)
        }
        Comp::RefNew(_) => Comp::RefNew(pop_value(built)),
        Comp::RefGet(_) => Comp::RefGet(pop_value(built)),
        Comp::RefSet(_, _) => {
            let value = pop_value(built);
            Comp::RefSet(pop_value(built), value)
        }
        Comp::InitAt(_, _) => {
            let value = pop_value(built);
            Comp::InitAt(pop_value(built), value)
        }
        _ => unreachable!("only thunk-bearing leaves receive a reconstruction frame"),
    }
}

fn borrowed_uses(name: Sym, args: &[Value], sigs: &Sigs, renames: &Renames) -> Set {
    let mask = borrow_mask(name, sigs);
    let mut borrowed = Set::new();
    for (index, argument) in args.iter().enumerate() {
        if !borrowed_at(mask, index) {
            continue;
        }
        match argument {
            Value::Var(var) => {
                borrowed.insert(renamed(*var, renames));
            }
            value if scalar_without_cell(value) => {}
            value => panic!(
                "invalid RC input: borrowed argument to {name} is not a let-bound variable: {value:?}"
            ),
        }
    }
    borrowed
}

fn count_value(value: &Value, out: &mut BTreeMap<Sym, usize>, renames: &Renames) {
    let mut raw = BTreeMap::new();
    count_val(value, &mut raw);
    for (name, count) in raw {
        *out.entry(renamed(name, renames)).or_default() += count;
    }
}

fn leaf_counts(c: &Comp, out: &mut BTreeMap<Sym, usize>, sigs: &Sigs, renames: &Renames) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        // A `var` cell flows as an ordinary owned value: each read/write consumes
        // a reference (the rc pass dups so each use has one), and `ref_set`
        // overwrites the cell in place. So a Ref op counts its cell and value like
        // any other consuming leaf.
        | Comp::RefNew(v)
        | Comp::RefGet(v) => count_value(v, out, renames),
        Comp::RefSet(c, v) => {
            count_value(c, out, renames);
            count_value(v, out, renames);
        }
        // `InitAt` consumes its cell (moved into the result) and every
        // constructor field (moved into the cell), exactly like the `Return(Ctor)`
        // it replaced consumes its fields. Missing this would drop a field the
        // cell now owns, a double free.
        Comp::InitAt(cell, ctor) => {
            count_value(cell, out, renames);
            count_value(ctor, out, renames);
        }
        Comp::App(f, args) => {
            for x in renamed_freev(f, renames) {
                *out.entry(x).or_default() += 1;
            }
            for a in args {
                count_value(a, out, renames);
            }
        }
        Comp::Prim(_, a, b) => {
            count_value(a, out, renames);
            count_value(b, out, renames);
        }
        Comp::Call(g, args) => {
            let mask = borrow_mask(*g, sigs);
            for (i, a) in args.iter().enumerate() {
                if !borrowed_at(mask, i) {
                    count_value(a, out, renames);
                }
            }
        }
        Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for a in args {
                count_value(a, out, renames);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::super::balanced;
    use super::*;
    use crate::core::CheckedHandler;

    const DEEP_RC_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    #[test]
    fn insertion_handles_deep_computations_and_values_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-rc-insertion".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let shadowed = Sym::new("shadowed");
                let mut value = Value::Thunk(Box::new(Comp::Return(Value::Var(shadowed))));
                for _ in 0..DEEP_RC_DEPTH {
                    value = Value::Tuple(vec![value]);
                }
                let mut body = Comp::Return(value);
                for _ in 0..DEEP_RC_DEPTH {
                    body = Comp::If(
                        Value::Bool(true),
                        Box::new(body),
                        Box::new(Comp::Return(Value::Int(0))),
                    );
                }
                let body = Comp::Case(Value::Var(shadowed), vec![(CorePat::Var(shadowed), body)]);
                let input = Core {
                    fns: vec![function("deep_rc_insertion", &["shadowed"], body)],
                };
                let output = insert_rc(&input, &Sigs::new());

                assert!(matches!(
                    &output.fns[0].body,
                    Comp::Case(_, arms)
                        if matches!(arms[0].0, CorePat::Var(name) if name.as_str() == "%rc0")
                ));
                assert_eq!(balanced(&output, &Sigs::new()), Ok(()));
                mem::forget(output);
                mem::forget(input);
            })
            .expect("spawn deep RC insertion test")
            .join()
            .expect("deep RC insertion test panicked");
    }

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn function(name: &str, params: &[&str], body: Comp) -> CoreFn {
        CoreFn {
            name: sym(name),
            params: params.iter().map(|param| sym(param)).collect(),
            body,
            dict_arity: 0,
        }
    }

    fn rename_free(comp: &Comp, from: Sym, to: Sym) -> Comp {
        RenameFree.rewrite_comp(comp, &BTreeMap::from([(from, to)]))
    }

    #[test]
    fn rename_free_respects_raw_core_scopes() {
        let from = sym("from");
        let to = sym("to");
        let op = HandleOp {
            name: sym("op"),
            params: vec![from],
            resume: sym("resume"),
            body: Comp::Return(Value::Var(from)),
        };
        let handler = Comp::Handle {
            body: Box::new(Comp::Return(Value::Var(from))),
            return_var: Some(from),
            return_body: Some(Box::new(Comp::Return(Value::Var(from)))),
            ops: CheckedHandler::new(vec![op]).unwrap(),
        };
        let renamed = rename_free(&handler, from, to);
        let Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } = renamed
        else {
            panic!("rewriting a handler preserves its shape");
        };
        assert!(matches!(*body, Comp::Return(Value::Var(name)) if name == to));
        assert!(matches!(
            return_body.as_deref(),
            Some(Comp::Return(Value::Var(name))) if *name == from
        ));
        assert!(matches!(ops[0].body, Comp::Return(Value::Var(name)) if name == from));

        let bind = Comp::Bind(
            Box::new(Comp::Return(Value::Var(from))),
            from,
            Box::new(Comp::Return(Value::Var(from))),
        );
        assert!(matches!(
            rename_free(&bind, from, to),
            Comp::Bind(first, _, rest)
                if matches!(*first, Comp::Return(Value::Var(name)) if name == to)
                    && matches!(*rest, Comp::Return(Value::Var(name)) if name == from)
        ));

        let case = Comp::Case(
            Value::Var(from),
            vec![(CorePat::Var(from), Comp::Return(Value::Var(from)))],
        );
        assert!(matches!(
            rename_free(&case, from, to),
            Comp::Case(Value::Var(scrutinee), arms)
                if scrutinee == to
                    && matches!(arms[0].1, Comp::Return(Value::Var(name)) if name == from)
        ));

        let reuse = Comp::WithReuse {
            token: from,
            freed: Value::Var(from),
            body: Box::new(Comp::Reuse(from, Value::Var(from))),
        };
        assert!(matches!(
            rename_free(&reuse, from, to),
            Comp::WithReuse {
                freed: Value::Var(freed),
                body,
                ..
            } if freed == to
                && matches!(*body, Comp::Reuse(token, Value::Var(value))
                    if token == from && value == from)
        ));
    }

    #[test]
    fn last_borrow_drops_after_the_call_returns() {
        let borrowed = sym("borrowed");
        let retained = sym("retained");
        let observe = sym("observe");
        let input = Core {
            fns: vec![
                function("observe", &["borrowed"], Comp::Return(Value::Var(borrowed))),
                function(
                    "caller",
                    &["retained"],
                    Comp::Call(observe, vec![Value::Var(retained)]),
                ),
            ],
        };
        let sigs = std::iter::once((observe, vec![true])).collect();
        let output = insert_rc(&input, &sigs);

        let Comp::Bind(call, result, post) = &output.fns[1].body else {
            panic!("borrowed call result must delimit its loan cleanup");
        };
        assert_eq!(result.as_str(), "%rc0");
        assert!(matches!(
            &**call,
            Comp::Call(name, args)
                if *name == observe
                    && matches!(args.as_slice(), [Value::Var(arg)] if *arg == retained)
        ));
        assert!(matches!(
            &**post,
            Comp::Bind(drop, binder, rest)
                if binder.as_str() == "_"
                    && matches!(&**drop, Comp::Drop(Value::Var(var)) if *var == retained)
                    && matches!(&**rest, Comp::Return(Value::Var(var)) if var == result)
        ));
        assert_eq!(balanced(&output, &sigs), Ok(()));
    }

    #[test]
    fn consume_and_borrow_of_one_value_retains_a_call_lifetime_token() {
        let owned = sym("owned");
        let borrowed = sym("borrowed");
        let retained = sym("retained");
        let inspect = sym("inspect");
        let input = Core {
            fns: vec![
                function(
                    "inspect",
                    &["owned", "borrowed"],
                    Comp::Return(Value::Tuple(vec![Value::Var(owned), Value::Var(borrowed)])),
                ),
                function(
                    "caller",
                    &["retained"],
                    Comp::Call(inspect, vec![Value::Var(retained), Value::Var(retained)]),
                ),
            ],
        };
        let sigs = std::iter::once((inspect, vec![false, true])).collect();
        let output = insert_rc(&input, &sigs);

        let Comp::Bind(dup, binder, call_and_cleanup) = &output.fns[1].body else {
            panic!("owned+borrow alias must retain a loan token");
        };
        assert_eq!(binder.as_str(), "_");
        assert!(matches!(
            &**dup,
            Comp::Dup(Value::Var(var)) if *var == retained
        ));
        let Comp::Bind(call, result, post) = &**call_and_cleanup else {
            panic!("call must precede its retained-token cleanup");
        };
        assert_eq!(result.as_str(), "%rc0");
        assert!(matches!(&**call, Comp::Call(name, _) if *name == inspect));
        assert!(matches!(
            &**post,
            Comp::Bind(drop, _, rest)
                if matches!(&**drop, Comp::Drop(Value::Var(var)) if *var == retained)
                    && matches!(&**rest, Comp::Return(Value::Var(var)) if var == result)
        ));
        assert_eq!(balanced(&output, &sigs), Ok(()));
    }
}
