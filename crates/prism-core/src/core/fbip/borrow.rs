//! Borrow inference: which parameters a provably pure function only loans.
//!
//! The reference-count discipline makes borrowing any parameter of a provably
//! pure function sound (the callee dups before each consuming use and never
//! drops the loan; the caller retains ownership across the call), so this pass
//! decides profit, not safety: a parameter is inferred borrowed only when every
//! occurrence in the body is a genuine read. A read is a bare variable in a
//! scrutinee, test, or primitive operand position, or a bare variable passed to
//! a borrowed position of another call. Anything that stores the value in a
//! structure, captures it in a thunk or closure, hands it to an owned call
//! position, or reaches an effect or post-RC node disqualifies it. So does a
//! match that could recycle the parameter's cell: a loan frees nothing, so
//! when an arm destructs the value and allocates a cell the freed one could
//! service, the reuse is worth more than the saved retain and release pair
//! and the parameter stays owned.
//!
//! Elaboration rebinds every use through a value-headed let (`return r to t;
//! case t of ...`), so occurrences are tracked through aliases: a bind whose
//! head returns a bare loaned variable makes its binder carry the same loan,
//! and only a genuinely escaping occurrence, the function result, a structure
//! field, a capture, an owned argument, consumes the underlying parameter.
//!
//! The callee's body is not the only constraint: every call site must be able
//! to cover the loan with a named, retained token, so a position that any
//! caller feeds a structured temporary is forced back to owned before the
//! body walk begins.
//!
//! Nor is profit the only constraint. A loan is discharged by the frame that
//! made the call, after the call returns, and a call the backend turns into a
//! loop keeps no such frame: deferring the release past the call is exactly
//! what stops the site from being a tail call. Borrowing there would trade a
//! retain and release pair for one stack frame per iteration, which is not a
//! cost but a change of behavior, since a loop that ran in constant stack
//! begins to exhaust it on a large enough input. So a position is forced back
//! to owned when a loop-eligible call site passes it a value the calling frame
//! owns. Passing on a loan the frame itself holds stays free, because that
//! loan's owner sits further up the stack and outlives the whole loop.
//!
//! Recursion is resolved as a greatest fixpoint: every candidate starts
//! borrowed and iteration removes parameters with a consuming occurrence under
//! the current assumption, so a self-recursive read-only walk keeps its loan.
//! Declared `borrow` annotations are the source contract and are never shrunk,
//! only extended. The result is a pure function of the checked program, which
//! is why it stays out of definition identity: like a lowering tier, the
//! setting must be unobservable in program behavior.

use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use prism_common::sym::Sym;
use prism_syntax::kw;

use super::{borrowed_at, scalar_without_cell, Set, Sigs};
use crate::core::cbpv::{Comp, Core, CorePat, Value};
use crate::core::fv::{comp as freev, comp_without, pat_vars};
use crate::core::tailrec::{loops_as_tail_call, reassoc, trmc_shape};
use crate::core::traverse::Visit;

// The loans in scope during a body walk: each name that currently carries a
// loan, mapped to the parameter whose loan it carries. Parameters map to
// themselves; a let alias maps to the parameter it renames.
type Loans = BTreeMap<Sym, Sym>;

// The names the frame holds without owning: exactly the set reference-count
// insertion calls borrowed, being a loaned parameter, a field projected out of
// a loaned scrutinee, and any let alias of one. None of them carries a release
// this frame has to place, which is the one thing a looping call site needs to
// know about its arguments.
//
// Deliberately not folded into `Loans`, which answers a different question:
// which parameter an occurrence would consume. A field of a loaned scrutinee is
// unowned, but escaping it retains the field on its own and leaves the parameter
// it came from untouched, so it must not map back to that parameter.
type Unowned = BTreeSet<Sym>;

// Positions a loop-eligible call site forces back to owned, keyed by callee.
// Unlike the poison set, which names parameters of the function being walked,
// these are decided at a call site and land on someone else's signature.
type Vetoes = BTreeMap<Sym, BTreeSet<usize>>;

/// Extend `declared` with inferred masks for the provably pure functions.
///
/// `pure_fns` names the declarations whose principal body effect row solved
/// empty and closed; only those are candidates. Leading dictionary parameters
/// stay owned. Entries whose mask is all-owned are omitted, matching
/// `borrow_sigs`, so consumers keep their absent-means-owned default.
#[must_use]
pub fn infer_borrow_sigs(core: &Core, pure_fns: &Set, declared: &Sigs) -> Sigs {
    let mut candidates: Sigs = core
        .fns
        .iter()
        .filter(|f| pure_fns.contains(&f.name) && f.params.len() > f.dict_arity)
        .map(|f| {
            let mask = (0..f.params.len()).map(|i| i >= f.dict_arity).collect();
            (f.name, mask)
        })
        .collect();
    // Which call sites the backend can loop is only visible once nested bind
    // heads are flattened, so the walk reads normalized bodies. This is the
    // same normalization the tail-recursion analysis and the emitter share, and
    // it is a pure rewrite, so taking it once here serves every round.
    let bodies: Vec<Cow<'_, Comp>> = core
        .fns
        .iter()
        .map(|function| normalized_body(&function.body))
        .collect();
    let arity: BTreeMap<Sym, usize> = core.fns.iter().map(|f| (f.name, f.params.len())).collect();
    // A borrowed-position argument must reach reference-count insertion as a
    // bare variable or a literal immediate: the caller covers the loan with a
    // named, retained token it drops after the call, and a structured
    // temporary has no such name. Any call site passing a structured value at
    // a candidate position forces that position back to owned up front, so the
    // final map can never route a program into the balance checker's
    // borrowed-argument refusal. Shapes never change during the fixpoint, so
    // one pre-pass suffices.
    let mut shapes = CallShapes {
        candidates: &mut candidates,
    };
    for body in &bodies {
        shapes.walk_comp(body);
    }
    loop {
        let assumed = merged(declared, &candidates);
        let mut changed = false;
        let mut vetoes = Vetoes::new();
        for (f, body) in core.fns.iter().zip(&bodies) {
            // Loans are read from the assumed map rather than the candidate
            // one, so a declared borrow the inference never proposed still
            // counts as a loan the frame may pass on for free.
            let mask = assumed.get(&f.name).map(Vec::as_slice);
            let in_scope: Loans = f
                .params
                .iter()
                .enumerate()
                .filter(|(i, _)| borrowed_at(mask, *i))
                .map(|(_, p)| (*p, *p))
                .collect();
            let unowned: Unowned = in_scope.keys().copied().collect();
            let mut walk = Walk {
                assumed: &assumed,
                arity: &arity,
                frame: Some(f.name),
                frame_arity: f.params.len(),
                poisoned: Set::new(),
                vetoes: &mut vetoes,
            };
            walk.comp(body, &in_scope, &unowned, true);
            let poisoned = walk.poisoned;
            let Some(mask) = candidates.get(&f.name) else {
                continue;
            };
            if !poisoned.is_empty() {
                let next: Vec<bool> = f
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, p)| mask.get(i).copied().unwrap_or(false) && !poisoned.contains(p))
                    .collect();
                // Only a mask that actually lost a position counts as progress.
                // Loans are read from the assumed map, which keeps a declared
                // borrow in scope forever, so a consuming occurrence of one
                // would otherwise report the same poison every round and the
                // fixpoint would never settle.
                if next != *mask {
                    candidates.insert(f.name, next);
                    changed = true;
                }
            }
        }
        // A lambda becomes a frame of its own, so its tail calls loop or grow
        // the stack on exactly the same terms and it owes the same veto.
        let mut lams = LamFrames {
            assumed: &assumed,
            arity: &arity,
            vetoes: &mut vetoes,
        };
        for body in &bodies {
            lams.walk_comp(body);
        }
        // Applied after the round rather than during it, because a veto lands
        // on a signature some other function is being walked against: taking it
        // mid-round would make the result depend on declaration order. Every
        // veto only clears a position, so the map descends and the loop ends.
        for (callee, positions) in vetoes {
            let Some(mask) = candidates.get_mut(&callee) else {
                continue;
            };
            for index in positions {
                if let Some(slot) = mask.get_mut(index) {
                    if *slot {
                        *slot = false;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    merged(declared, &candidates)
        .into_iter()
        .filter(|(_, mask)| mask.iter().any(|b| *b))
        .collect()
}

// Reassociation is observable to loop classification only when a bind has a
// bind as its head. Borrow the original body in the common case, which also
// avoids manufacturing an owned tree merely to inspect it.
fn normalized_body(body: &Comp) -> Cow<'_, Comp> {
    struct NeedsReassociation(bool);

    impl Visit for NeedsReassociation {
        fn comp(&mut self, comp: &Comp) -> bool {
            self.0 |=
                matches!(comp, Comp::Bind(head, _, _) if matches!(head.as_ref(), Comp::Bind(..)));
            !self.0
                && matches!(
                    comp,
                    Comp::Bind(..) | Comp::If(..) | Comp::Case(..) | Comp::WithReuse { .. }
                )
        }

        fn value(&mut self, _value: &Value) -> bool {
            false
        }
    }

    let mut scan = NeedsReassociation(false);
    scan.walk_comp(body);
    if scan.0 {
        Cow::Owned(reassoc(body))
    } else {
        Cow::Borrowed(body)
    }
}

// Clears candidate positions whose call sites pass anything other than a bare
// variable or a literal immediate. The `Visit` descent reaches every call,
// including those inside thunk and closure bodies.
struct CallShapes<'a> {
    candidates: &'a mut Sigs,
}

impl Visit for CallShapes<'_> {
    fn comp(&mut self, c: &Comp) -> bool {
        if let Comp::Call(callee, args) = c {
            if let Some(mask) = self.candidates.get_mut(callee) {
                for (i, arg) in args.iter().enumerate() {
                    if !matches!(arg, Value::Var(_)) && !scalar_without_cell(arg) {
                        if let Some(slot) = mask.get_mut(i) {
                            *slot = false;
                        }
                    }
                }
            }
        }
        true
    }
}

// Walks every lambda as the separate frame the backend lifts it into, so a tail
// call inside one is judged against the frame it actually gets rather than the
// declaration it was written in. Only vetoes come out: a suspension owns its
// captures, so inside the body the captures are loans this frame never releases
// and the parameters are owned, which is the partition reference-count
// insertion already uses, and no loan of the enclosing frame reaches in to be
// poisoned. The lifted frame takes the captures ahead of the parameters, so its
// width is both together, read through the same free-variable query the closure
// layout is built from.
struct LamFrames<'a> {
    assumed: &'a Sigs,
    arity: &'a BTreeMap<Sym, usize>,
    vetoes: &'a mut Vetoes,
}

impl Visit for LamFrames<'_> {
    fn comp(&mut self, c: &Comp) -> bool {
        if let Comp::Lam(params, body) = c {
            let captures = comp_without(body, params);
            let mut walk = Walk {
                assumed: self.assumed,
                arity: self.arity,
                frame: None,
                frame_arity: captures.len() + params.len(),
                poisoned: Set::new(),
                vetoes: self.vetoes,
            };
            walk.comp(body, &Loans::new(), &captures, true);
        }
        true
    }
}

// Elementwise OR of two mask maps; a missing or short entry reads as owned.
fn merged(declared: &Sigs, inferred: &Sigs) -> Sigs {
    let mut out = declared.clone();
    for (name, mask) in inferred {
        let entry = out.entry(*name).or_default();
        if entry.len() < mask.len() {
            entry.resize(mask.len(), false);
        }
        for (i, b) in mask.iter().enumerate() {
            entry[i] = entry[i] || *b;
        }
    }
    out
}

// Every loan-carrying name free in `comp` is consumed wholesale.
fn poison_free(comp: &Comp, loans: &Loans, out: &mut Set) {
    let fv = freev(comp);
    for (name, root) in loans {
        if fv.contains(name) {
            out.insert(*root);
        }
    }
}

// Every loan-carrying name occurring anywhere inside `v` is consumed or
// escapes there.
fn poison_value(v: &Value, loans: &Loans, out: &mut Set) {
    let mut pending = vec![v];
    while let Some(value) = pending.pop() {
        match value {
            Value::Var(name) => {
                if let Some(root) = loans.get(name) {
                    out.insert(*root);
                }
            }
            // A thunk cell captures its free names, which outlives the loan.
            Value::Thunk(body) => poison_free(body, loans, out),
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                pending.extend(fields.iter().rev());
            }
            Value::UnboxedRecord(fields) => {
                pending.extend(fields.iter().rev().map(|(_, field)| field));
            }
            Value::Int(_)
            | Value::I64(_)
            | Value::U64(_)
            | Value::Float(_)
            | Value::Bool(_)
            | Value::Unit
            | Value::Str(_) => {}
        }
    }
}

// A value in a read position: a bare variable is a loan; any structured value
// allocates or captures, which consumes whatever candidates it contains.
fn read_value(v: &Value, loans: &Loans, out: &mut Set) {
    if !matches!(v, Value::Var(_)) {
        poison_value(v, loans, out);
    }
}

// One frame's body walk, which is a declaration or one lambda the backend lifts
// out of it. `poisoned` accumulates parameters of the declaration being walked;
// `vetoes` accumulates positions of whatever functions it calls, so it outlives
// the walk and is threaded in by reference. `frame` is the declaration's name,
// absent for a lambda, which has none to recurse through.
struct Walk<'a> {
    assumed: &'a Sigs,
    arity: &'a BTreeMap<Sym, usize>,
    frame: Option<Sym>,
    frame_arity: usize,
    poisoned: Set,
    vetoes: &'a mut Vetoes,
}

struct WalkFrame<'a> {
    comp: &'a Comp,
    loans: Rc<Loans>,
    unowned: Rc<Unowned>,
    tail: bool,
}

impl Walk<'_> {
    // Whether a tail-position call to `callee` with `args` arguments is one the
    // backend reuses this frame for rather than pushing a new one.
    fn loops_here(&self, callee: Sym, args: usize) -> bool {
        self.arity
            .get(&callee)
            .is_some_and(|callee_arity| loops_as_tail_call(args, *callee_arity, self.frame_arity))
    }

    // Force back to owned every borrowed position this looping call site hands
    // a value the frame owns. The frame is about to be reused, so there is
    // nowhere left to release it: the release would have to follow the call,
    // which is precisely what stops the call from reusing the frame. A loan the
    // frame is passing on costs nothing, since the owner that will release it
    // sits further up the stack and outlives every iteration, and a scalar that
    // owns no cell has no release to place at all.
    fn veto_loop_args(&mut self, callee: Sym, args: &[Value], unowned: &Unowned) {
        let mask = self.assumed.get(&callee).map(Vec::as_slice);
        for (index, arg) in args.iter().enumerate() {
            if !borrowed_at(mask, index) {
                continue;
            }
            let free_of_release = match arg {
                Value::Var(name) => unowned.contains(name),
                other => scalar_without_cell(other),
            };
            if !free_of_release {
                self.vetoes.entry(callee).or_default().insert(index);
            }
        }
    }

    fn comp(&mut self, comp: &Comp, loans: &Loans, unowned: &Unowned, tail: bool) {
        let mut pending = vec![WalkFrame {
            comp,
            loans: Rc::new(loans.clone()),
            unowned: Rc::new(unowned.clone()),
            tail,
        }];
        while let Some(frame) = pending.pop() {
            let WalkFrame {
                comp,
                loans,
                unowned,
                tail,
            } = frame;
            match comp {
                // A returned value leaves the function, so the caller's retained
                // reference alone cannot cover it. This arm only sees tail
                // positions: a bind head's `Return` is a let and is handled below.
                Comp::Return(v) | Comp::Error(v) | Comp::Force(v) => {
                    poison_value(v, &loans, &mut self.poisoned);
                }
                Comp::Bind(head, binder, rest) => {
                    // A self-call whose continuation feeds one constructor field or
                    // one addend is a tail modulo constructor step, which the
                    // backend also turns into a loop. A release deferred into that
                    // continuation takes the shape apart, so the site answers to the
                    // same rule as a bare tail call.
                    if tail {
                        if let Comp::Call(callee, args) = head.as_ref() {
                            if self.frame == Some(*callee)
                                && self.loops_here(*callee, args.len())
                                && trmc_shape(rest, binder.as_str()).is_some()
                            {
                                self.veto_loop_args(*callee, args, &unowned);
                            }
                        }
                    }
                    // The binder shadows anything of the same name the frame was
                    // already tracking, before the head can rename onto it.
                    let mut rest_loans = loans.as_ref().clone();
                    let mut rest_unowned = unowned.as_ref().clone();
                    rest_loans.remove(binder);
                    rest_unowned.remove(binder);
                    // A value head is a let, not a function result: naming a
                    // tracked variable renames it onto the binder, and a structured
                    // head stores whatever candidates it contains.
                    let visit_head = if let Comp::Return(v) = head.as_ref() {
                        match v {
                            Value::Var(x) => {
                                if let Some(root) = loans.get(x) {
                                    rest_loans.insert(*binder, *root);
                                }
                                if unowned.contains(x) {
                                    rest_unowned.insert(*binder);
                                }
                            }
                            other => poison_value(other, &loans, &mut self.poisoned),
                        }
                        false
                    } else {
                        true
                    };
                    pending.push(WalkFrame {
                        comp: rest,
                        loans: Rc::new(rest_loans),
                        unowned: Rc::new(rest_unowned),
                        tail,
                    });
                    if visit_head {
                        pending.push(WalkFrame {
                            comp: head,
                            loans: Rc::clone(&loans),
                            unowned: Rc::clone(&unowned),
                            tail: false,
                        });
                    }
                }
                Comp::App(callee, args) => {
                    poison_free(callee, &loans, &mut self.poisoned);
                    for arg in args {
                        poison_value(arg, &loans, &mut self.poisoned);
                    }
                }
                Comp::If(cond, yes, no) => {
                    read_value(cond, &loans, &mut self.poisoned);
                    pending.push(WalkFrame {
                        comp: no,
                        loans: Rc::clone(&loans),
                        unowned: Rc::clone(&unowned),
                        tail,
                    });
                    pending.push(WalkFrame {
                        comp: yes,
                        loans,
                        unowned,
                        tail,
                    });
                }
                Comp::Prim(_, lhs, rhs) => {
                    read_value(lhs, &loans, &mut self.poisoned);
                    read_value(rhs, &loans, &mut self.poisoned);
                }
                Comp::FloatBuiltin(_, operand) | Comp::Neg(_, operand) => {
                    read_value(operand, &loans, &mut self.poisoned);
                }
                Comp::Call(callee, args) => {
                    if tail && self.loops_here(*callee, args.len()) {
                        self.veto_loop_args(*callee, args, &unowned);
                    }
                    let mask = self.assumed.get(callee).map(Vec::as_slice);
                    for (index, arg) in args.iter().enumerate() {
                        if borrowed_at(mask, index) {
                            read_value(arg, &loans, &mut self.poisoned);
                        } else {
                            poison_value(arg, &loans, &mut self.poisoned);
                        }
                    }
                }
                Comp::Io(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) => {
                    for arg in args {
                        poison_value(arg, &loans, &mut self.poisoned);
                    }
                }
                Comp::Case(scrutinee, arms) => {
                    read_value(scrutinee, &loans, &mut self.poisoned);
                    let loaned_root = match scrutinee {
                        Value::Var(x) => loans.get(x).copied(),
                        _ => None,
                    };
                    let scrutinee_unowned =
                        matches!(scrutinee, Value::Var(x) if unowned.contains(x));
                    let mut arm_frames = Vec::with_capacity(arms.len());
                    for (pattern, body) in arms {
                        // A loan starves reuse: a borrowed scrutinee frees no cell
                        // in its arms, so the reuse pass finds no token to spend.
                        // When an arm could pair the freed cell with a fitting
                        // allocation, the freed-cell reuse is worth more than the
                        // saved retain and release pair, so the parameter stays
                        // owned.
                        if let (Some(root), Some(cap)) = (loaned_root, reuse_seed_arity(pattern)) {
                            if fitting_alloc(body, cap) {
                                self.poisoned.insert(root);
                            }
                        }
                        let mut binders = Set::new();
                        pat_vars(pattern, &mut binders);
                        let mut arm_loans = loans.as_ref().clone();
                        let mut arm_unowned = unowned.as_ref().clone();
                        for binder in &binders {
                            arm_loans.remove(binder);
                            arm_unowned.remove(binder);
                        }
                        // Reference-count insertion projects the fields of a loaned
                        // scrutinee as loans themselves and retains nothing for
                        // them, so a field passed on carries no release either. The
                        // field is deliberately not mapped back to the parameter it
                        // came from: escaping a field retains that field on its own
                        // and leaves the parameter untouched.
                        if scrutinee_unowned {
                            arm_unowned.extend(binders.iter().copied());
                        }
                        arm_frames.push(WalkFrame {
                            comp: body,
                            loans: Rc::new(arm_loans),
                            unowned: Rc::new(arm_unowned),
                            tail,
                        });
                    }
                    for arm in arm_frames.into_iter().rev() {
                        pending.push(arm);
                    }
                }
                Comp::UnboxedProject(v, _) => read_value(v, &loans, &mut self.poisoned),
                // A closure capture outlives the call frame the loan is scoped to,
                // and effect machinery or post-RC nodes never appear in a provably
                // pure body before lowering: in both cases every candidate the node
                // touches is conservatively consumed wholesale rather than reasoned
                // about, so the bodies need no further walk.
                Comp::Lam(_, _)
                | Comp::Handle { .. }
                | Comp::Mask(_, _)
                | Comp::WithReuse { .. }
                | Comp::Reuse(_, _)
                | Comp::Dup(_)
                | Comp::Drop(_)
                | Comp::InitAt(_, _)
                | Comp::RefNew(_)
                | Comp::RefGet(_)
                | Comp::RefSet(_, _) => poison_free(comp, &loans, &mut self.poisoned),
            }
        }
    }
}

// The patterns whose match frees a reusable cell, mirroring `reuse_arm`: a
// destructing constructor or tuple seeds a token sized by its field count, and
// the wired nullable frees no cell so it never seeds one. The two predicates
// below must stay exactly as permissive as the reuse pass, or inference loans
// away cells the pass could have recycled.
fn reuse_seed_arity(pattern: &CorePat) -> Option<usize> {
    match pattern {
        CorePat::Ctor(name, _) if kw::is_or_null_ctor(name.as_str()) => None,
        CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => Some(fields.len()),
        _ => None,
    }
}

// Whether the body holds an allocation a freed cell of `cap` slots could
// service, over the same spine `consume_alloc` walks: bind chains, branches,
// and inner reuse scopes, never thunk or handler bodies. Reaching any fitting
// allocation is enough; where the freeing drop would land depends on liveness
// the inference does not model, so this over-approximates toward owned.
fn fitting_alloc(comp: &Comp, cap: usize) -> bool {
    let mut pending = vec![comp];
    while let Some(comp) = pending.pop() {
        match comp {
            Comp::Return(Value::Ctor(name, _, fields))
                if fields.len() <= cap && !kw::is_or_null_ctor(name.as_str()) =>
            {
                return true;
            }
            Comp::Return(Value::Tuple(fields)) if fields.len() <= cap => return true,
            Comp::Bind(head, _, rest) => {
                pending.push(rest);
                pending.push(head);
            }
            Comp::If(_, yes, no) => {
                pending.push(no);
                pending.push(yes);
            }
            Comp::Case(_, arms) => {
                pending.extend(arms.iter().rev().map(|(_, body)| body));
            }
            Comp::WithReuse { body, .. } => pending.push(body),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;
    use crate::core::cbpv::{CoreFn, CorePat};

    const DEEP_WALK_DEPTH: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;
    const TEST_CTOR_TAG: usize = 0;

    fn s(name: &str) -> Sym {
        name.into()
    }

    fn f(name: &str, params: &[&str], body: Comp) -> CoreFn {
        CoreFn {
            name: s(name),
            params: params.iter().map(|p| s(p)).collect(),
            dict_arity: 0,
            body,
        }
    }

    fn core(fns: Vec<CoreFn>) -> Core {
        Core { fns }
    }

    fn pure_set(names: &[&str]) -> Set {
        names.iter().map(|n| s(n)).collect()
    }

    fn mask<'a>(sigs: &'a Sigs, name: &str) -> Option<&'a Vec<bool>> {
        sigs.get(&s(name))
    }

    #[test]
    fn inference_handles_deep_alias_value_and_reuse_walks_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-borrow-inference".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut stored = Value::Var(s("payload"));
                for _ in 0..DEEP_WALK_DEPTH {
                    stored = Value::UnboxedTuple(vec![stored]);
                }
                let mut arm = Comp::Return(Value::Ctor(s("Box"), TEST_CTOR_TAG, vec![stored]));
                for _ in 0..DEEP_WALK_DEPTH {
                    arm = Comp::Bind(
                        Box::new(Comp::Return(Value::Var(s("keep")))),
                        s("alias"),
                        Box::new(arm),
                    );
                }
                let body = Comp::Case(
                    Value::Var(s("keep")),
                    vec![(
                        CorePat::Wild,
                        Comp::Case(
                            Value::Var(s("cell")),
                            vec![(CorePat::Ctor(s("Slot"), vec![Some(s("old"))]), arm)],
                        ),
                    )],
                );
                let program = core(vec![f("deep", &["keep", "cell", "payload"], body)]);
                let sigs = infer_borrow_sigs(&program, &pure_set(&["deep"]), &Sigs::new());

                mem::forget(program);
                assert_eq!(mask(&sigs, "deep"), Some(&vec![true, false, false]));
            })
            .expect("spawn deep borrow-inference test")
            .join()
            .expect("deep borrow-inference test panicked");
    }

    #[test]
    fn inference_handles_deep_rebinding_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-borrow-rebinding".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut body = Comp::Case(
                    Value::Var(s("alias")),
                    vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
                );
                for _ in 0..DEEP_WALK_DEPTH {
                    body = Comp::Bind(
                        Box::new(Comp::Return(Value::Var(s("input")))),
                        s("alias"),
                        Box::new(body),
                    );
                }
                let program = core(vec![f("deep", &["input"], body)]);
                let sigs = infer_borrow_sigs(&program, &pure_set(&["deep"]), &Sigs::new());

                mem::forget(program);
                assert_eq!(mask(&sigs, "deep"), Some(&vec![true]));
            })
            .expect("spawn deep borrow-rebinding test")
            .join()
            .expect("deep borrow-rebinding test panicked");
    }

    #[test]
    fn scrutinee_only_param_is_borrowed() {
        let body = Comp::Case(
            Value::Var(s("xs")),
            vec![
                (CorePat::Ctor(s("Nil"), vec![]), Comp::Return(Value::Int(0))),
                (
                    CorePat::Ctor(s("Cons"), vec![None, Some(s("t"))]),
                    Comp::Call(s("len"), vec![Value::Var(s("t"))]),
                ),
            ],
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("len", &["xs"], body)]),
            &pure_set(&["len"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "len"), Some(&vec![true]));
    }

    #[test]
    fn looping_call_that_hands_over_an_owned_value_forces_owned() {
        // `driver` ends in a same-arity tail call, which the backend lowers as
        // a loop reusing the frame. The first argument is a value the frame
        // owns, so its release would have to follow the call, and a call with
        // work after it is not a tail call: the loop would become one frame per
        // iteration. The second argument is the loan the frame is passing on,
        // whose owner sits further up the stack, so that position is untouched.
        let reader = f(
            "reader",
            &["a", "b"],
            Comp::Case(
                Value::Var(s("a")),
                vec![(
                    CorePat::Wild,
                    Comp::Case(
                        Value::Var(s("b")),
                        vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
                    ),
                )],
            ),
        );
        let driver = f(
            "driver",
            &["n", "xs"],
            Comp::Bind(
                Box::new(Comp::Return(Value::Ctor(
                    s("Box"),
                    TEST_CTOR_TAG,
                    vec![Value::Var(s("n"))],
                ))),
                s("boxed"),
                Box::new(Comp::Call(
                    s("reader"),
                    vec![Value::Var(s("boxed")), Value::Var(s("xs"))],
                )),
            ),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![reader, driver]),
            &pure_set(&["reader", "driver"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "reader"), Some(&vec![false, true]));
    }

    #[test]
    fn looping_call_that_hands_over_an_immediate_keeps_the_loan() {
        // An immediate owns no cell, so it carries no release for the reused
        // frame to place and the position keeps its loan.
        let body = Comp::Case(
            Value::Var(s("xs")),
            vec![
                (
                    CorePat::Ctor(s("Nil"), vec![]),
                    Comp::Case(
                        Value::Var(s("k")),
                        vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
                    ),
                ),
                (
                    CorePat::Ctor(s("Cons"), vec![None, Some(s("t"))]),
                    Comp::Call(s("seek"), vec![Value::Int(1), Value::Var(s("t"))]),
                ),
            ],
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("seek", &["k", "xs"], body)]),
            &pure_set(&["seek"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "seek"), Some(&vec![true, true]));
    }

    #[test]
    fn left_nested_bind_is_normalized_before_the_loop_veto() {
        // Reassociation exposes the self-call as TRMC. Its argument is owned by
        // this frame, so retaining the inferred loan would turn the loop back
        // into stack-growing recursion.
        let body = Comp::Bind(
            Box::new(Comp::Bind(
                Box::new(Comp::Return(Value::Ctor(s("Box"), TEST_CTOR_TAG, vec![]))),
                s("owned"),
                Box::new(Comp::Call(s("loop"), vec![Value::Var(s("owned"))])),
            )),
            s("result"),
            Box::new(Comp::Return(Value::Ctor(
                s("Wrap"),
                TEST_CTOR_TAG,
                vec![Value::Var(s("result"))],
            ))),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("loop", &["unused"], body)]),
            &pure_set(&["loop"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "loop"), None);
    }

    #[test]
    fn arm_that_could_recycle_the_cell_forces_owned() {
        // A setter's shape: destruct the value, allocate one the freed cell
        // could service. A loan would starve the reuse pass of its token, so
        // the parameter stays owned.
        let body = Comp::Case(
            Value::Var(s("p")),
            vec![(
                CorePat::Ctor(s("P"), vec![Some(s("a")), Some(s("b"))]),
                Comp::Return(Value::Ctor(
                    s("P"),
                    TEST_CTOR_TAG,
                    vec![Value::Var(s("v")), Value::Var(s("b"))],
                )),
            )],
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("with_x", &["p", "v"], body)]),
            &pure_set(&["with_x"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "with_x"), None);
    }

    #[test]
    fn arm_allocation_too_wide_for_the_cell_keeps_the_loan() {
        // The only allocation cannot fit in the freed one-slot cell, so no
        // reuse is lost and the scrutinee-only read still earns its loan.
        let body = Comp::Case(
            Value::Var(s("p")),
            vec![(
                CorePat::Ctor(s("Wrap"), vec![Some(s("a"))]),
                Comp::Return(Value::Tuple(vec![Value::Var(s("a")), Value::Var(s("a"))])),
            )],
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("widen", &["p"], body)]),
            &pure_set(&["widen"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "widen"), Some(&vec![true]));
    }

    #[test]
    fn structured_argument_at_a_call_site_forces_owned() {
        let body = Comp::Case(
            Value::Var(s("xs")),
            vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
        );
        // The body alone would earn the loan, but a caller passes a freshly
        // built value directly at the position, which no retained token names.
        let caller = f(
            "caller",
            &["n"],
            Comp::Call(
                s("reader"),
                vec![Value::Ctor(
                    s("Node"),
                    TEST_CTOR_TAG,
                    vec![Value::Var(s("n"))],
                )],
            ),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("reader", &["xs"], body), caller]),
            &pure_set(&["reader"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "reader"), None);
    }

    #[test]
    fn self_recursive_loan_survives_the_fixpoint() {
        let body = Comp::If(
            Value::Var(s("stop")),
            Box::new(Comp::Return(Value::Int(0))),
            Box::new(Comp::Call(
                s("go"),
                vec![Value::Var(s("stop")), Value::Var(s("xs"))],
            )),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("go", &["stop", "xs"], body)]),
            &pure_set(&["go"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "go"), Some(&vec![true, true]));
    }

    #[test]
    fn returned_and_stored_params_stay_owned() {
        let ret = f("ret", &["x"], Comp::Return(Value::Var(s("x"))));
        let stored = f(
            "stored",
            &["x"],
            Comp::Return(Value::Ctor(
                s("Box"),
                TEST_CTOR_TAG,
                vec![Value::Var(s("x"))],
            )),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![ret, stored]),
            &pure_set(&["ret", "stored"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "ret"), None);
        assert_eq!(mask(&sigs, "stored"), None);
    }

    #[test]
    fn owned_position_poison_propagates_through_the_call_graph() {
        // `sink` consumes its parameter (returns it), so `relay` passing its
        // own parameter to `sink` must lose the loan one iteration later.
        let sink = f("sink", &["x"], Comp::Return(Value::Var(s("x"))));
        let relay = f(
            "relay",
            &["x"],
            Comp::Call(s("sink"), vec![Value::Var(s("x"))]),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![relay, sink]),
            &pure_set(&["sink", "relay"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "sink"), None);
        assert_eq!(mask(&sigs, "relay"), None);
    }

    #[test]
    fn borrowed_position_call_keeps_the_loan() {
        let reader = f(
            "reader",
            &["xs"],
            Comp::Case(
                Value::Var(s("xs")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(1)))],
            ),
        );
        let relay = f(
            "relay",
            &["xs"],
            Comp::Call(s("reader"), vec![Value::Var(s("xs"))]),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![relay, reader]),
            &pure_set(&["reader", "relay"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "reader"), Some(&vec![true]));
        assert_eq!(mask(&sigs, "relay"), Some(&vec![true]));
    }

    #[test]
    fn declared_masks_are_never_shrunk() {
        // The body consumes `x`, but the declared annotation is the source
        // contract, so the final mask keeps it borrowed.
        let declared: Sigs = std::iter::once((s("keep"), vec![true])).collect();
        let keep = f("keep", &["x"], Comp::Return(Value::Var(s("x"))));
        let sigs = infer_borrow_sigs(&core(vec![keep]), &pure_set(&["keep"]), &declared);
        assert_eq!(mask(&sigs, "keep"), Some(&vec![true]));
    }

    #[test]
    fn shadowed_rebinding_does_not_poison_the_param() {
        // The escaping `x` is the Bind's own binder, not the parameter.
        let body = Comp::Bind(
            Box::new(Comp::Case(
                Value::Var(s("x")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
            )),
            s("x"),
            Box::new(Comp::Return(Value::Var(s("x")))),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("shadow", &["x"], body)]),
            &pure_set(&["shadow"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "shadow"), Some(&vec![true]));
    }

    #[test]
    fn let_alias_carries_the_loan_to_its_uses() {
        // Elaboration names every use through a temp: `return r to t;
        // case t of ...` must read exactly like `case r of ...`.
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Var(s("r")))),
            s("t"),
            Box::new(Comp::Case(
                Value::Var(s("t")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
            )),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("reader", &["r"], body)]),
            &pure_set(&["reader"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "reader"), Some(&vec![true]));
    }

    #[test]
    fn returning_an_alias_escapes_the_param() {
        // The alias is the function result, so the loan cannot cover it.
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Var(s("r")))),
            s("t"),
            Box::new(Comp::Return(Value::Var(s("t")))),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![f("ident", &["r"], body)]),
            &pure_set(&["ident"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "ident"), None);
    }

    #[test]
    fn thunk_capture_and_dictionaries_stay_owned() {
        let capture = f(
            "capture",
            &["x"],
            Comp::Return(Value::Thunk(Box::new(Comp::Return(Value::Var(s("x")))))),
        );
        let mut with_dict = f(
            "method",
            &["d", "x"],
            Comp::Case(
                Value::Var(s("x")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(0)))],
            ),
        );
        with_dict.dict_arity = 1;
        let sigs = infer_borrow_sigs(
            &core(vec![capture, with_dict]),
            &pure_set(&["capture", "method"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "capture"), None);
        assert_eq!(mask(&sigs, "method"), Some(&vec![false, true]));
    }

    #[test]
    fn a_boxed_literal_call_site_declines_the_loan_but_a_static_str_keeps_it() {
        // A `Float` literal boxes a fresh cell at codegen, so a call site
        // passing one inline denies the borrowed shape; a `Str` literal names
        // a static cell and covers the loan like a tagged immediate.
        let float_reader = f(
            "float_reader",
            &["x"],
            Comp::Case(
                Value::Var(s("x")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(1)))],
            ),
        );
        let float_site = f(
            "float_site",
            &[],
            Comp::Call(s("float_reader"), vec![Value::Float(2.5)]),
        );
        let str_reader = f(
            "str_reader",
            &["x"],
            Comp::Case(
                Value::Var(s("x")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(1)))],
            ),
        );
        let str_site = f(
            "str_site",
            &[],
            Comp::Call(s("str_reader"), vec![Value::Str("static".into())]),
        );
        let sigs = infer_borrow_sigs(
            &core(vec![float_reader, float_site, str_reader, str_site]),
            &pure_set(&["float_reader", "float_site", "str_reader", "str_site"]),
            &Sigs::new(),
        );
        assert_eq!(mask(&sigs, "float_reader"), None);
        assert_eq!(mask(&sigs, "str_reader"), Some(&vec![true]));
    }

    #[test]
    fn impure_functions_are_not_candidates() {
        let reader = f(
            "reader",
            &["xs"],
            Comp::Case(
                Value::Var(s("xs")),
                vec![(CorePat::Wild, Comp::Return(Value::Int(1)))],
            ),
        );
        let sigs = infer_borrow_sigs(&core(vec![reader]), &Set::new(), &Sigs::new());
        assert!(mask(&sigs, "reader").is_none());
    }
}
