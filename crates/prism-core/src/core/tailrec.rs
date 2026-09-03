//! Shared tail-recursion / TRMC classification.
//!
//! The FBIP checker and native emitter share this classification so accepted
//! `fip` functions are exactly those codegen can make constant-stack.
//!
//! TRMC (tail recursion modulo constructor / addition): a function whose
//! recursive call feeds exactly one constructor field in tail position, like
//! `Cons(y, map(f, rest))`, or sits under an associative `1 + f(x)`, runs in
//! constant stack after hole-passing or accumulator lowering. A plain tail call
//! is the degenerate case.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use crate::core::cbpv::{Comp, Core, CoreOp, Value};
use crate::core::fv;
use crate::core::traverse::{Rewrite, RewriteControl, Visit};

// A heap tag / field index as `i64`. Mirrors `emit::idx64`: a count that large
// needs an >8-exabyte program on an LP64 host, so saturate rather than panic.
fn idx64(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

// The two ways a recursive tail loops: a constructor hole passed down the chain,
// or an integer accumulator. A function realizes at most one of them.
#[derive(Clone, Copy, Debug)]
pub enum TrmcMode {
    Hole,
    Acc,
}

// One recursive-tail site, resolved against the continuation that follows the
// call. `Ctor` carries everything codegen needs to allocate the cell and thread
// the hole; `Acc` carries the other addend.
#[derive(Debug)]
pub enum TrmcShape<'a> {
    Ctor {
        token: Option<&'a Sym>,
        tag: i64,
        fields: &'a [Value],
        hole: usize,
    },
    Acc(&'a Value),
}

fn occurs(v: &Value, x: &str) -> usize {
    let mut work = vec![v];
    let mut count = 0;
    while let Some(value) = work.pop() {
        match value {
            Value::Var(y) => count += usize::from(y.as_str() == x),
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                work.extend(fields.iter().rev());
            }
            Value::UnboxedRecord(fields) => {
                work.extend(fields.iter().rev().map(|(_, field)| field));
            }
            Value::Thunk(body) => {
                count += 2 * usize::from(fv::comp(body).iter().any(|name| name.as_str() == x));
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
    count
}

fn ctor_shape<'a>(v: &'a Value, x: &str, token: Option<&'a Sym>) -> Option<TrmcShape<'a>> {
    let (tag, fields) = match v {
        Value::Ctor(_, t, fs) => (idx64(*t), fs.as_slice()),
        Value::Tuple(fs) => (0, fs.as_slice()),
        _ => return None,
    };
    let hole = fields
        .iter()
        .position(|f| matches!(f, Value::Var(y) if y.as_str() == x))?;
    let total: usize = fields.iter().map(|f| occurs(f, x)).sum();
    (total == 1).then_some(TrmcShape::Ctor {
        token,
        tag,
        fields,
        hole,
    })
}

// Given the continuation `k` after a recursive call bound to `x`, decide which
// (if any) TRMC shape the tail realizes: `x` feeding a single constructor field
// (with or without a reuse token), or `x` as one addend of an `Int +`.
#[must_use]
pub fn trmc_shape<'a>(k: &'a Comp, x: &str) -> Option<TrmcShape<'a>> {
    match k {
        Comp::Return(v) => ctor_shape(v, x, None),
        Comp::Reuse(tok, v) if tok.as_str() != x => ctor_shape(v, x, Some(tok)),
        Comp::Prim(CoreOp::Add, a, b) => match (occurs(a, x), occurs(b, x)) {
            (1, 0) if matches!(a, Value::Var(_)) => Some(TrmcShape::Acc(b)),
            (0, 1) if matches!(b, Value::Var(_)) => Some(TrmcShape::Acc(a)),
            _ => None,
        },
        _ => None,
    }
}

fn scan_trmc(c: &Comp, name: &str, arity: usize, ctor: &mut bool, acc: &mut bool) {
    let mut work = vec![c];
    while let Some(comp) = work.pop() {
        match comp {
            Comp::Bind(first, binder, rest) => {
                if let Comp::Call(callee, args) = first.as_ref() {
                    if callee.as_str() == name && args.len() == arity {
                        match trmc_shape(rest, binder.as_str()) {
                            Some(TrmcShape::Ctor { .. }) => {
                                *ctor = true;
                                continue;
                            }
                            Some(TrmcShape::Acc(_)) => {
                                *acc = true;
                                continue;
                            }
                            None => {}
                        }
                    }
                }
                work.push(rest);
            }
            Comp::If(_, yes, no) => {
                work.push(no);
                work.push(yes);
            }
            Comp::Case(_, arms) => {
                work.extend(arms.iter().rev().map(|(_, body)| body));
            }
            Comp::WithReuse { body, .. } => work.push(body),
            _ => {}
        }
    }
}

// The whole-function decision codegen acts on: does the body's self-recursion
// loop via a constructor hole, an accumulator, or not at all? A body mixing both
// shapes returns `None` (no single loop realizes it), so codegen leaves it a
// plain recursive function and the bounded-stack check must reject it as `fip`.
#[must_use]
pub fn trmc_mode(name: &str, arity: usize, body: &Comp) -> Option<TrmcMode> {
    let (mut ctor, mut acc) = (false, false);
    scan_trmc(body, name, arity, &mut ctor, &mut acc);
    match (ctor, acc) {
        (true, false) => Some(TrmcMode::Hole),
        (false, true) => Some(TrmcMode::Acc),
        _ => None,
    }
}

// Whether the TRMC rewrite is sound against resumption for `body`.
//
// The hole rewrite threads one mutable cell through the recursion and fills it
// in place. That is sound only when no surrounding effect can resume the
// continuation more than once: a second resumption re-entering the half-built
// recursion would observe the shared cell and corrupt an earlier resumption's
// result. Effect lowering reifies every multishot handler into the free-monad
// driver before emission, so a function that reaches the direct rewrite carries
// no effect node (`Do`/`Handle`/`Mask`) at all -- those are the only nodes that
// can install or resume a continuation. This states that precondition rather
// than leaving it implicit in pass ordering: it holds today because effect
// lowering runs first, and a future reordering that ran the rewrite before
// effect lowering trips this check instead of silently miscompiling a multishot
// handler.
#[must_use]
pub fn trmc_resumption_safe(body: &Comp) -> bool {
    struct Scan(bool);
    impl Visit for Scan {
        fn comp(&mut self, c: &Comp) -> bool {
            self.0 &= !matches!(c, Comp::Do(..) | Comp::Handle { .. } | Comp::Mask(..));
            self.0
        }
    }
    let mut scan = Scan(true);
    scan.walk_comp(body);
    scan.0
}

// Elaboration nests binds to the left, hiding the recursive call from the tail
// pattern; the monad associativity law `(a to y; b) to x; k` ==
// `a to y; (b to x; k)` flattens them. Skipped when it would capture y in k.
// Codegen runs this before lowering, so the bounded-stack check runs it too: the
// classification must see the same shape the backend lowers.
#[must_use]
pub fn reassoc(c: &Comp) -> Comp {
    Reassociate.rewrite_comp(c, &())
}

struct Reassociate;

impl Rewrite for Reassociate {
    type Ctx = ();

    fn enter_comp(&mut self, comp: &Comp, _cx: &Self::Ctx) -> RewriteControl<Comp> {
        match comp {
            Comp::Bind(..) | Comp::If(..) | Comp::Case(..) | Comp::WithReuse { .. } => {
                RewriteControl::Descend
            }
            _ => RewriteControl::Replace(clone_comp(comp)),
        }
    }

    fn enter_value(&mut self, value: &Value, _cx: &Self::Ctx) -> RewriteControl<Value> {
        RewriteControl::Replace(clone_value(value))
    }

    fn leave_comp(&mut self, source: &Comp, rewritten: Comp, _cx: &Self::Ctx) -> Comp {
        if !matches!(source, Comp::Bind(..)) {
            return rewritten;
        }
        let Comp::Bind(first, binder, rest) = rewritten else {
            unreachable!("a bind rebuild remains a bind");
        };
        rebind(*first, binder, *rest)
    }
}

struct CoreClone;

impl Rewrite for CoreClone {
    type Ctx = ();
}

fn clone_comp(comp: &Comp) -> Comp {
    CoreClone.rewrite_comp(comp, &())
}

fn clone_value(value: &Value) -> Value {
    CoreClone.rewrite_value(value, &())
}

fn rebind(m: Comp, x: Sym, n: Comp) -> Comp {
    let mut head = m;
    let mut prefix = Vec::new();
    let mut free_in_rest = None;
    loop {
        match head {
            Comp::Bind(first, binder, rest)
                if binder.as_str() == "_"
                    || (binder != x
                        && !free_in_rest
                            .get_or_insert_with(|| fv::comp(&n))
                            .contains(&binder)) =>
            {
                prefix.push((first, binder));
                head = *rest;
            }
            other => {
                let mut result = Comp::Bind(Box::new(other), x, Box::new(n));
                for (first, binder) in prefix.into_iter().rev() {
                    result = Comp::Bind(first, binder, Box::new(result));
                }
                return result;
            }
        }
    }
}

// How a recursive call site sits in the stack. Tail and the two TRMC shapes all
// lower to a loop; `NonTail` is a real frame per recursive step.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TailClass {
    Tail,
    TrmcCons,
    TrmcAdd,
    NonTail,
}

/// Whether the backend lowers a tail-position call as a loop rather than a
/// frame.
///
/// A `musttail` call reuses the current frame, which the ABI permits only when
/// the two signatures agree: the call must be saturated and the callee must
/// take exactly as many parameters as the frame making the call. That covers a
/// saturated self-call and a same-arity mutual tail call alike, and it is the
/// test the emitter applies at its tail-call site.
///
/// Every pass that can perturb a tail call asks here rather than restating the
/// arithmetic, so a lowering the emitter would loop is never quietly turned
/// into a stack-growing one somewhere upstream.
#[must_use]
pub const fn loops_as_tail_call(args: usize, callee_arity: usize, frame_arity: usize) -> bool {
    args == callee_arity && callee_arity == frame_arity
}

// Classify every call to a member of `group` reachable within `body`'s own
// evaluation, in source order. Calls hidden inside a thunk, lambda, or handler
// run in a later, separate frame and do not grow THIS body's stack, so the walk
// does not descend into them; only the `Bind`/`If`/`Case` control flow of the
// current frame is followed. `self_name`/`self_arity` decide TRMC and plain-tail
// eligibility, which the backend only realizes for a saturated self-call (and a
// same-arity mutual tail call, via musttail).
#[must_use]
pub fn recursive_calls(
    body: &Comp,
    self_name: Sym,
    self_arity: usize,
    group: &BTreeSet<Sym>,
) -> Vec<(Sym, TailClass)> {
    let (nodes, root) = normalized_view(body);
    let mut out = Vec::new();
    let mut work = vec![CallFrame::Normalized(root, true)];
    while let Some(frame) = work.pop() {
        match frame {
            CallFrame::Normalized(id, tail) => match &nodes[id] {
                Normalized::Source(comp) => {
                    scan_raw_calls(
                        comp, tail, self_name, self_arity, group, &mut work, &mut out,
                    );
                }
                Normalized::Bind {
                    first,
                    binder,
                    rest,
                } => {
                    if tail {
                        if let (Some((callee, args)), Some(rest_comp)) =
                            (source_call(&nodes, *first), source_comp(&nodes, *rest))
                        {
                            if callee == self_name && args == self_arity {
                                if let Some(shape) = trmc_shape(rest_comp, binder.as_str()) {
                                    out.push((callee, tail_class(&shape)));
                                    work.push(CallFrame::Normalized(*rest, false));
                                    continue;
                                }
                            }
                        }
                    }
                    work.push(CallFrame::Normalized(*rest, tail));
                    work.push(CallFrame::Normalized(*first, false));
                }
                Normalized::If { yes, no } => {
                    work.push(CallFrame::Normalized(*no, tail));
                    work.push(CallFrame::Normalized(*yes, tail));
                }
                Normalized::Case(arms) => {
                    work.extend(
                        arms.iter()
                            .rev()
                            .map(|arm| CallFrame::Normalized(*arm, tail)),
                    );
                }
                Normalized::WithReuse(body) => {
                    work.push(CallFrame::Normalized(*body, tail));
                }
            },
            CallFrame::Raw(comp, tail) => {
                scan_raw_calls(
                    comp, tail, self_name, self_arity, group, &mut work, &mut out,
                );
            }
            CallFrame::References(names) => {
                out.extend(names.into_iter().map(|name| (name, TailClass::NonTail)));
            }
        }
    }
    out
}

fn scan_raw_calls<'a>(
    comp: &'a Comp,
    tail: bool,
    self_name: Sym,
    self_arity: usize,
    group: &BTreeSet<Sym>,
    work: &mut Vec<CallFrame<'a>>,
    out: &mut Vec<(Sym, TailClass)>,
) {
    match comp {
        Comp::Bind(first, binder, rest) => {
            if tail {
                if let Comp::Call(callee, args) = first.as_ref() {
                    if *callee == self_name && args.len() == self_arity {
                        if let Some(shape) = trmc_shape(rest, binder.as_str()) {
                            out.push((*callee, tail_class(&shape)));
                            work.push(CallFrame::Raw(rest, false));
                            return;
                        }
                    }
                }
            }
            work.push(CallFrame::Raw(rest, tail));
            work.push(CallFrame::Raw(first, false));
        }
        Comp::If(_, yes, no) => {
            work.push(CallFrame::Raw(no, tail));
            work.push(CallFrame::Raw(yes, tail));
        }
        Comp::Case(_, arms) => {
            work.extend(
                arms.iter()
                    .rev()
                    .map(|(_, body)| CallFrame::Raw(body, tail)),
            );
        }
        Comp::Call(callee, args) if group.contains(callee) => {
            let cls = if tail && args.len() == self_arity {
                TailClass::Tail
            } else {
                TailClass::NonTail
            };
            out.push((*callee, cls));
        }
        Comp::WithReuse { body, .. } => work.push(CallFrame::Raw(body, tail)),
        Comp::App(callee, _) => {
            let references = fv::comp(callee)
                .into_iter()
                .filter(|name| group.contains(name))
                .collect();
            work.push(CallFrame::References(references));
            work.push(CallFrame::Raw(callee, false));
        }
        _ => {}
    }
}

const fn tail_class(shape: &TrmcShape<'_>) -> TailClass {
    match shape {
        TrmcShape::Ctor { .. } => TailClass::TrmcCons,
        TrmcShape::Acc(_) => TailClass::TrmcAdd,
    }
}

type NormalizedId = usize;

enum Normalized<'a> {
    Source(&'a Comp),
    Bind {
        first: NormalizedId,
        binder: Sym,
        rest: NormalizedId,
    },
    If {
        yes: NormalizedId,
        no: NormalizedId,
    },
    Case(Vec<NormalizedId>),
    WithReuse(NormalizedId),
}

enum NormalizeFrame<'a> {
    Comp(&'a Comp),
    FinishBind { binder: Sym, rest: &'a Comp },
    FinishIf,
    FinishCase { arm_count: usize },
    FinishWithReuse,
}

fn normalized_view(body: &Comp) -> (Vec<Normalized<'_>>, NormalizedId) {
    let mut nodes = Vec::new();
    let mut results = Vec::new();
    let mut work = vec![NormalizeFrame::Comp(body)];
    while let Some(frame) = work.pop() {
        match frame {
            NormalizeFrame::Comp(comp) => match comp {
                Comp::Bind(first, binder, rest) => {
                    work.push(NormalizeFrame::FinishBind {
                        binder: *binder,
                        rest,
                    });
                    work.push(NormalizeFrame::Comp(rest));
                    work.push(NormalizeFrame::Comp(first));
                }
                Comp::If(_, yes, no) => {
                    work.push(NormalizeFrame::FinishIf);
                    work.push(NormalizeFrame::Comp(no));
                    work.push(NormalizeFrame::Comp(yes));
                }
                Comp::Case(_, arms) => {
                    work.push(NormalizeFrame::FinishCase {
                        arm_count: arms.len(),
                    });
                    work.extend(arms.iter().rev().map(|(_, arm)| NormalizeFrame::Comp(arm)));
                }
                Comp::WithReuse { body, .. } => {
                    work.push(NormalizeFrame::FinishWithReuse);
                    work.push(NormalizeFrame::Comp(body));
                }
                _ => results.push(push_normalized(&mut nodes, Normalized::Source(comp))),
            },
            NormalizeFrame::FinishBind { binder, rest } => {
                let rest_id = results.pop().expect("a normalized continuation exists");
                let first = results
                    .pop()
                    .expect("a normalized bound computation exists");
                results.push(rebind_view(first, binder, rest_id, rest, &mut nodes));
            }
            NormalizeFrame::FinishIf => {
                let no = results.pop().expect("a normalized else branch exists");
                let yes = results.pop().expect("a normalized then branch exists");
                results.push(push_normalized(&mut nodes, Normalized::If { yes, no }));
            }
            NormalizeFrame::FinishCase { arm_count } => {
                let start = results
                    .len()
                    .checked_sub(arm_count)
                    .expect("each case arm has a normalized body");
                let arms = results.drain(start..).collect();
                results.push(push_normalized(&mut nodes, Normalized::Case(arms)));
            }
            NormalizeFrame::FinishWithReuse => {
                let body = results.pop().expect("a normalized reuse body exists");
                results.push(push_normalized(&mut nodes, Normalized::WithReuse(body)));
            }
        }
    }
    let root = results.pop().expect("the root has a normalized view");
    debug_assert!(results.is_empty());
    (nodes, root)
}

fn rebind_view(
    mut first: NormalizedId,
    binder: Sym,
    rest: NormalizedId,
    rest_source: &Comp,
    nodes: &mut Vec<Normalized<'_>>,
) -> NormalizedId {
    let mut prefix = Vec::new();
    let mut free_in_rest = None;
    while let Normalized::Bind {
        first: inner,
        binder: inner_binder,
        rest: inner_rest,
    } = &nodes[first]
    {
        let (inner, inner_binder, inner_rest) = (*inner, *inner_binder, *inner_rest);
        let safe = inner_binder.as_str() == "_"
            || (inner_binder != binder
                && !free_in_rest
                    .get_or_insert_with(|| fv::comp(rest_source))
                    .contains(&inner_binder));
        if !safe {
            break;
        }
        prefix.push((first, inner, inner_binder));
        first = inner_rest;
    }
    let mut result = push_normalized(
        nodes,
        Normalized::Bind {
            first,
            binder,
            rest,
        },
    );
    for (id, first, binder) in prefix.into_iter().rev() {
        nodes[id] = Normalized::Bind {
            first,
            binder,
            rest: result,
        };
        result = id;
    }
    result
}

fn push_normalized<'a>(nodes: &mut Vec<Normalized<'a>>, node: Normalized<'a>) -> NormalizedId {
    let id = nodes.len();
    nodes.push(node);
    id
}

fn source_comp<'a>(nodes: &'a [Normalized<'a>], id: NormalizedId) -> Option<&'a Comp> {
    match nodes[id] {
        Normalized::Source(comp) => Some(comp),
        _ => None,
    }
}

fn source_call(nodes: &[Normalized<'_>], id: NormalizedId) -> Option<(Sym, usize)> {
    match source_comp(nodes, id)? {
        Comp::Call(callee, args) => Some((*callee, args.len())),
        _ => None,
    }
}

enum CallFrame<'a> {
    Normalized(NormalizedId, bool),
    Raw(&'a Comp, bool),
    References(Vec<Sym>),
}

// The call graph over user functions. An edge is a direct call head (`calls_in`,
// which `fv` deliberately drops) UNIONED with any first-class reference (`fv`,
// for a function flowing as a bare value). Missing a direct-call edge would
// shrink an SCC and let a mutually recursive non-tail cycle slip the
// bounded-stack check, so both sources matter; over-approximating via `fv` only
// grows an SCC, which is safe (it demands tail recursion of a few more calls).
fn call_graph(core: &Core, users: &BTreeSet<Sym>, refs: bool) -> BTreeMap<Sym, BTreeSet<Sym>> {
    core.fns
        .iter()
        .map(|f| {
            let mut heads = Vec::new();
            super::cbpv::calls_in(&f.body, &mut heads);
            let edges: BTreeSet<Sym> = if refs {
                heads
                    .into_iter()
                    .chain(fv::comp(&f.body))
                    .filter(|n| users.contains(n))
                    .collect()
            } else {
                heads.into_iter().filter(|n| users.contains(n)).collect()
            };
            (f.name, edges)
        })
        .collect()
}

fn reaches(adj: &BTreeMap<Sym, BTreeSet<Sym>>, start: Sym) -> BTreeSet<Sym> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(n) = stack.pop() {
        if seen.insert(n) {
            if let Some(es) = adj.get(&n) {
                stack.extend(es.iter().copied());
            }
        }
    }
    seen
}

/// The strongly connected component of `f` in the user-function call graph.
///
/// This is the mutual-recursion group whose members must all tail-recurse for
/// `f` to be `fip`. Always contains `f` itself (a non-recursive function gets a
/// singleton, so it has no in-group call sites to constrain).
#[must_use]
pub fn scc_of(core: &Core, users: &BTreeSet<Sym>, f: Sym) -> BTreeSet<Sym> {
    scc_in(&call_graph(core, users, true), f)
}

/// The SCC of `f` using only direct-call edges (no first-class references).
///
/// This is a subset of [`scc_of`]: a member present here recurses with `f`
/// through actual calls, whereas a member only in [`scc_of`] is tied to `f`
/// solely by a function flowing as a value. The bounded-stack rule uses the
/// sound `scc_of`; this finer view only sharpens the rejection message.
#[must_use]
pub fn scc_of_calls(core: &Core, users: &BTreeSet<Sym>, f: Sym) -> BTreeSet<Sym> {
    scc_in(&call_graph(core, users, false), f)
}

fn scc_in(adj: &BTreeMap<Sym, BTreeSet<Sym>>, f: Sym) -> BTreeSet<Sym> {
    let fwd = reaches(adj, f);
    let mut scc = BTreeSet::new();
    scc.insert(f);
    for g in fwd {
        if g != f && reaches(adj, g).contains(&f) {
            scc.insert(g);
        }
    }
    scc
}

#[cfg(test)]
mod tests {
    use std::{mem, thread};

    use super::*;
    use crate::core::cbpv::{CoreFn, CorePat};

    const DEEP_BIND_COUNT: usize = 20_000;
    const DEEP_VALUE_COUNT: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    #[test]
    fn tail_classification_handles_deep_bind_chains_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-tail-classification".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let function = Sym::new("deep_tail");
                let mut head = Comp::Return(Value::Int(0));
                for _ in 0..DEEP_BIND_COUNT {
                    head = Comp::Bind(
                        Box::new(Comp::Return(Value::Int(0))),
                        Sym::new("_"),
                        Box::new(head),
                    );
                }
                // The outer bind forces `rebind` to move the complete left
                // computation into the continuation without recursive rebuilds.
                let body = Comp::Bind(
                    Box::new(head),
                    Sym::new("result"),
                    Box::new(Comp::Return(Value::Int(0))),
                );

                assert!(trmc_mode(function.as_str(), 0, &body).is_none());
                assert!(
                    recursive_calls(&body, function, 0, &BTreeSet::from([function])).is_empty()
                );
                let reassociated = reassoc(&body);
                let mut cursor = &reassociated;
                for _ in 0..=DEEP_BIND_COUNT {
                    let Comp::Bind(_, _, rest) = cursor else {
                        panic!("reassociation shortened the deep bind spine");
                    };
                    cursor = rest;
                }
                assert!(matches!(cursor, Comp::Return(Value::Int(0))));
                mem::forget(reassociated);
                mem::forget(body);
            })
            .expect("spawn deep tail-classification test")
            .join()
            .expect("deep tail-classification test panicked");
    }

    #[test]
    fn trmc_shape_handles_deep_constructor_values_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-trmc-shape".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let mut value = Value::Int(0);
                for _ in 0..DEEP_VALUE_COUNT {
                    value = Value::Tuple(vec![value]);
                }
                let continuation =
                    Comp::Return(Value::Tuple(vec![Value::Var(Sym::new("hole")), value]));

                assert!(matches!(
                    trmc_shape(&continuation, "hole"),
                    Some(TrmcShape::Ctor { hole: 0, .. })
                ));
                mem::forget(continuation);
            })
            .expect("spawn deep TRMC-shape test")
            .join()
            .expect("deep TRMC-shape test panicked");
    }

    #[test]
    fn trmc_shape_counts_occurrences_inside_unboxed_products() {
        let hole = Sym::new("hole");
        let tuple = Comp::Return(Value::Ctor(
            Sym::new("Box"),
            0,
            vec![
                Value::Var(hole),
                Value::UnboxedTuple(vec![Value::Var(hole)]),
            ],
        ));
        assert!(trmc_shape(&tuple, hole.as_str()).is_none());

        let record = Comp::Return(Value::Ctor(
            Sym::new("Box"),
            0,
            vec![
                Value::Var(hole),
                Value::UnboxedRecord(vec![(Sym::new("field"), Value::Var(hole))]),
            ],
        ));
        assert!(trmc_shape(&record, hole.as_str()).is_none());
    }

    fn group(names: &[&str]) -> BTreeSet<Sym> {
        names.iter().map(|n| Sym::from(*n)).collect()
    }

    // f(x) bound to t, then `k`; the classic recursive-call-feeding-continuation
    // shape every TRMC tail elaborates to.
    fn bind_call(args: Vec<Value>, k: Comp) -> Comp {
        Comp::Bind(
            Box::new(Comp::Call("f".into(), args)),
            "t".into(),
            Box::new(k),
        )
    }

    fn classes(body: &Comp, arity: usize) -> Vec<TailClass> {
        recursive_calls(body, "f".into(), arity, &group(&["f"]))
            .into_iter()
            .map(|(_, c)| c)
            .collect()
    }

    #[test]
    fn bare_self_tail_call_is_tail() {
        let body = Comp::Call("f".into(), vec![Value::Var("x".into())]);
        assert_eq!(classes(&body, 1), [TailClass::Tail]);
    }

    #[test]
    fn self_call_feeding_a_prim_is_nontail() {
        // `f(x) * x` keeps the frame alive to multiply the result.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Prim(CoreOp::Mul, Value::Var("t".into()), Value::Var("x".into())),
        );
        assert_eq!(classes(&body, 1), [TailClass::NonTail]);
    }

    #[test]
    fn self_call_under_one_ctor_field_is_trmc_cons() {
        // `Cons(h, f(x))`: the result sits in exactly one constructor field.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            )),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcCons]);
    }

    #[test]
    fn self_call_under_addition_is_trmc_add() {
        // `1 + f(x)`: the result is one addend of an associative add.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Prim(CoreOp::Add, Value::Int(1), Value::Var("t".into())),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcAdd]);
    }

    #[test]
    fn reassociation_exposes_a_recursive_call_in_a_left_nested_bind() {
        let head = Comp::Bind(
            Box::new(Comp::Return(Value::Unit)),
            "prefix".into(),
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
        );
        let body = Comp::Bind(
            Box::new(head),
            "t".into(),
            Box::new(Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            ))),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcCons]);
    }

    #[test]
    fn reassociation_does_not_capture_a_left_bind() {
        let head = Comp::Bind(
            Box::new(Comp::Return(Value::Unit)),
            "captured".into(),
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
        );
        let body = Comp::Bind(
            Box::new(head),
            "t".into(),
            Box::new(Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("captured".into()), Value::Var("t".into())],
            ))),
        );
        assert_eq!(classes(&body, 1), [TailClass::NonTail]);
    }

    #[test]
    fn reuse_token_ctor_tail_is_trmc_cons() {
        // The reuse-lowered form `reuse tok as Cons(h, f(x))` is still a cons tail.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Reuse(
                "tok".into(),
                Value::Ctor(
                    "Cons".into(),
                    1,
                    vec![Value::Var("h".into()), Value::Var("t".into())],
                ),
            ),
        );
        assert_eq!(classes(&body, 1), [TailClass::TrmcCons]);
    }

    #[test]
    fn second_recursive_call_in_a_field_is_nontail() {
        // `Cons(g(x), f(x))` (g == f): only one occurrence can be the hole, so
        // the other branch of the tree is a real recursive frame.
        let inner = Comp::Bind(
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
            "h".into(),
            Box::new(Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            ))),
        );
        let body = bind_call(vec![Value::Var("x".into())], inner);
        // Inner self-call is non-tail; outer feeds the single hole (TrmcCons).
        let got = classes(&body, 1);
        assert!(got.contains(&TailClass::NonTail), "{got:?}");
        assert!(got.contains(&TailClass::TrmcCons), "{got:?}");
    }

    #[test]
    fn wrong_arity_self_call_is_nontail() {
        // A saturated self-call must match the frame's arity to musttail.
        let body = Comp::Call("f".into(), vec![Value::Var("x".into())]);
        assert_eq!(classes(&body, 2), [TailClass::NonTail]);
    }

    #[test]
    fn branches_classify_independently() {
        let then = bind_call(
            vec![Value::Var("x".into())],
            Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            )),
        );
        let els = bind_call(
            vec![Value::Var("x".into())],
            Comp::Prim(CoreOp::Add, Value::Int(1), Value::Var("t".into())),
        );
        let body = Comp::If(Value::Bool(true), Box::new(then), Box::new(els));
        assert_eq!(classes(&body, 1), [TailClass::TrmcCons, TailClass::TrmcAdd]);
    }

    #[test]
    fn case_arm_tail_call_is_tail() {
        let arm = (
            CorePat::Ctor("Cons".into(), vec![Some("h".into()), Some("t".into())]),
            Comp::Call("f".into(), vec![Value::Var("t".into())]),
        );
        let body = Comp::Case(Value::Var("xs".into()), vec![arm]);
        assert_eq!(classes(&body, 1), [TailClass::Tail]);
    }

    #[test]
    fn pure_trmc_body_is_resumption_safe() {
        // `Cons(h, f(x))` with no effect node: the in-place hole is confined to
        // one pure invocation, so the rewrite is sound.
        let body = bind_call(
            vec![Value::Var("x".into())],
            Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            )),
        );
        assert!(trmc_resumption_safe(&body));
    }

    #[test]
    fn effectful_trmc_body_trips_resumption_guard() {
        // The same cons tail, but a `perform` sits in the recursive spine: a
        // multishot handler could resume the continuation twice and observe the
        // shared hole. The rewrite precondition must reject it. This is the
        // deliberate trip: it stands in for a future pass reordering that ran
        // the rewrite before effect lowering removed the effect node.
        let tail = bind_call(
            vec![Value::Var("x".into())],
            Comp::Return(Value::Ctor(
                "Cons".into(),
                1,
                vec![Value::Var("h".into()), Value::Var("t".into())],
            )),
        );
        let body = Comp::Bind(
            Box::new(Comp::Do("op".into(), vec![])),
            "h".into(),
            Box::new(tail),
        );
        assert!(!trmc_resumption_safe(&body));
    }

    fn fnamed(name: &str, body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            params: vec![],
            dict_arity: 0,
            body,
        }
    }

    #[test]
    fn scc_is_singleton_for_nonrecursive() {
        let core = Core {
            fns: vec![fnamed("f", Comp::Return(Value::Unit))],
        };
        let scc = scc_of(&core, &group(&["f"]), "f".into());
        assert_eq!(scc, group(&["f"]));
    }

    #[test]
    fn scc_captures_mutual_recursion() {
        // f -> g -> f is one component; a lone h sharing the graph is excluded.
        let core = Core {
            fns: vec![
                fnamed("f", Comp::Call("g".into(), vec![])),
                fnamed("g", Comp::Call("f".into(), vec![])),
                fnamed("h", Comp::Call("f".into(), vec![])),
            ],
        };
        let users = group(&["f", "g", "h"]);
        assert_eq!(scc_of(&core, &users, "f".into()), group(&["f", "g"]));
        // h reaches f but f never reaches h, so h is its own component.
        assert_eq!(scc_of(&core, &users, "h".into()), group(&["h"]));
    }

    #[test]
    fn reference_only_cycle_splits_scc_views() {
        // f calls g directly; g merely returns f as a first-class value (a
        // reference, not a call). The sound `scc_of` ties them together, but the
        // direct-call view keeps them apart, which is what lets the rejection say
        // the group exists only because a function flows as a value.
        let core = Core {
            fns: vec![
                fnamed("f", Comp::Call("g".into(), vec![])),
                fnamed("g", Comp::Return(Value::Var("f".into()))),
            ],
        };
        let users = group(&["f", "g"]);
        assert_eq!(scc_of(&core, &users, "f".into()), group(&["f", "g"]));
        assert_eq!(scc_of_calls(&core, &users, "f".into()), group(&["f"]));
    }
}
