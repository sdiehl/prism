use std::collections::{BTreeMap, BTreeSet};

use crate::names;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
use crate::types::{CtorInfo, DeclInfo, Type};

use super::super::cbpv::{Comp, Core, CoreFn, CorePat, Value};
use super::super::fv::pat_vars;
use super::super::tailrec::{recursive_calls, scc_of, scc_of_calls, TailClass};
use super::super::traverse::Visit;
use super::{count_val, Set, Sigs};

// Fully-in-place static check. The three properties
// are PROVEN at the phase each is a property of:
//
// - Zero-allocation + call-graph closure (both `fip` and `fbip`), over the
//   reuse-lowered core (`check_fip` below). A bare `Value::Ctor`/`Value::Tuple`
//   is a fresh heap cell here (`prism_alloc(0)` mallocs and bumps the live count
//   even for a nullary constructor), so the only allocation-free way to build is
//   `Comp::Reuse` over a dropped cell. An annotated function may only call
//   annotated functions or allocation-free prims, else an unannotated callee's
//   allocation would silently break the guarantee: `fbip` may call `fip` or
//   `fbip`; `fip` may call only `fip`, since an `fbip` callee is allowed
//   unbounded stack.
// - Linearity (`fip` only), over the RAW pre-RC core (`check_fip_linear`):
//   each owned, non-immediate binder is consumed at most once per path.
//   Linearity is a property of the source program; the dup/drop the RC pass
//   later inserts to REALIZE linear consumption over a unique cell are an
//   implementation detail and are not counted against it. A scalar binder is
//   exempt (a `dup` on an immediate is a runtime no-op).
// - Bounded stack (`fip` only): every recursive call within the call-graph SCC
//   must be a tail call or a TRMC-eligible tail (modulo one constructor field or
//   one addition), classified by the shared `core::tailrec` so acceptance never
//   outruns what codegen loops.
//
// `fbip` is the weaker discipline: zero allocation and the callee closure only,
// so it may duplicate, recurse non-tail, and run in unbounded stack.

pub type Fips = BTreeMap<Sym, Fip>;

#[must_use]
pub fn fip_annots(prog: &Program<CorePhase>) -> Fips {
    prog.fns
        .iter()
        .filter_map(|d| {
            // `@ noalloc` is the allocation-certificate spelling of the `fbip`
            // usage check: same zero-allocation check, no linearity or
            // bounded-stack requirement.
            // An explicit `fip`/`fbip` keyword (the stronger discipline) wins.
            let want = match d.fip {
                Fip::No if d.no_alloc => Fip::Fbip,
                other => other,
            };
            (want != Fip::No).then(|| (d.name.clone().into(), want))
        })
        .collect()
}

/// The set of `replayable`-annotated functions: each must infer a row within the
/// recordable capabilities plus the deterministic builtin effects, checked in the
/// driver against the inferred effects.
#[must_use]
pub fn replayable_annots(prog: &Program<CorePhase>) -> BTreeSet<Sym> {
    prog.fns
        .iter()
        .filter(|d| d.replayable)
        .map(|d| d.name.clone().into())
        .collect()
}

// Prims and builtins that allocate no heap cell, so an annotated body may call
// them. Conservative: only arithmetic/comparison/IO primitives that the backend
// lowers to immediates or a runtime call returning an immediate. Anything that
// builds a constructor (e.g. string ops returning a boxed Str) is excluded.
fn alloc_free_prim(name: &str) -> bool {
    matches!(
        name,
        "print" | "println" | "print_float" | "print_string" | "error" | "srand"
    )
}

// The number of concrete allocation witnesses reported per rejected function. A
// body with many allocation sites yields a readable diagnostic listing the first
// few in evaluation order; the remainder is summarized as a trailing count.
const ALLOC_WITNESS_LIMIT: usize = 3;

// A concrete reason an annotated body is not allocation-free, recorded in
// evaluation order. Every rejection the allocation walk can raise maps to one of
// these; the driver renders them into the user diagnostic. The set is exactly the
// nodes that materialize a heap cell (`Ctor`/`Tuple`/`Closure`) or admit an
// uncertified callee (`UncertifiedCall`/`IndirectCall`/`Builtin`); no other Core
// node allocates under this check.
enum AllocWitness {
    // A fresh constructor cell built outside a `reuse` token.
    Ctor(Sym),
    // A fresh tuple cell.
    Tuple,
    // A closure cell for a materialized lambda/thunk value.
    Closure,
    // A call to a user function lacking the certificate the caller needs: a `fip`
    // caller needs a `fip` callee, an `@ noalloc`/`fbip` caller needs either
    // certificate. The callee may allocate inside the caller's call tree.
    UncertifiedCall(Sym),
    // An indirect call through a first-class function value: no callee
    // certificate is available at the call site.
    IndirectCall,
    // A primitive/builtin outside the allocation-free allow-list.
    Builtin(Sym),
    // A performed `alloc` (the arena allocation effect). Serviced by a
    // `with_arena` handler out of a bump region, but still a fresh cell: arena
    // allocation is cheap, not absent, so `@ noalloc` must reject it too.
    AllocOp,
}

// Collects up to `ALLOC_WITNESS_LIMIT` witnesses while counting the total, so the
// diagnostic shows the first few in evaluation order and summarizes the rest.
struct Witnesses {
    seen: Vec<AllocWitness>,
    total: usize,
}

impl Witnesses {
    const fn new() -> Self {
        Self {
            seen: Vec::new(),
            total: 0,
        }
    }

    fn push(&mut self, w: AllocWitness) {
        if self.seen.len() < ALLOC_WITNESS_LIMIT {
            self.seen.push(w);
        }
        self.total += 1;
    }

    // Witnesses beyond the reported prefix, summarized as "and N more".
    const fn extra(&self) -> usize {
        self.total - self.seen.len()
    }
}

// Record a witness for each fresh cell a value materializes. A bare constructor,
// tuple, or thunk in any non-`reuse` position allocates; scalars and variables do
// not. A value contributes a witness iff it would have failed the first-failure
// check, so the accept/reject decision is unchanged.
fn value_alloc(v: &Value, out: &mut Witnesses) {
    match v {
        Value::Ctor(name, ..) => out.push(AllocWitness::Ctor(*name)),
        Value::Tuple(_) => out.push(AllocWitness::Tuple),
        Value::Thunk(_) => out.push(AllocWitness::Closure),
        // Unboxed products carry no heap cell, so they are not an allocation
        // witness themselves; their fields still might allocate.
        Value::UnboxedTuple(fs) => fs.iter().for_each(|f| value_alloc(f, out)),
        Value::UnboxedRecord(fs) => fs.iter().for_each(|(_, f)| value_alloc(f, out)),
        _ => {}
    }
}

// The argument of a `Comp::Reuse`: the head cell reuses a dropped token, so only
// its fields can hide a fresh allocation.
fn value_alloc_under_reuse(v: &Value, out: &mut Witnesses) {
    match v {
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().for_each(|f| value_alloc(f, out)),
        other => value_alloc(other, out),
    }
}

// Walk an annotated body in evaluation order, recording every allocation witness
// (bounded by the sink). `want` selects the callee-certificate rule: a `fip`
// caller demands a `fip` callee; an `@ noalloc`/`fbip` caller accepts either
// certificate. The traversal mirrors the accepting checker exactly, so a body is
// rejected iff at least one witness is recorded.
fn comp_alloc(c: &Comp, want: Fip, fips: &Fips, users: &BTreeSet<Sym>, out: &mut Witnesses) {
    match c {
        Comp::Reuse(_, v) => value_alloc_under_reuse(v, out),
        // Freeing the dropped cell is the allocation-free shell a `Reuse` in the
        // body then spends; check the body like any other scope.
        Comp::WithReuse { freed, body, .. } => {
            value_alloc(freed, out);
            comp_alloc(body, want, fips, users, out);
        }
        Comp::Call(g, args) => {
            if users.contains(g) {
                let ok = match want {
                    Fip::Fip => matches!(fips.get(g), Some(Fip::Fip)),
                    Fip::Fbip | Fip::No => matches!(fips.get(g), Some(Fip::Fbip | Fip::Fip)),
                };
                if !ok {
                    out.push(AllocWitness::UncertifiedCall(*g));
                }
            } else if !alloc_free_prim(g.as_str()) {
                out.push(AllocWitness::Builtin(*g));
            }
            for a in args {
                value_alloc(a, out);
            }
        }
        Comp::Bind(m, _, n) => {
            comp_alloc(m, want, fips, users, out);
            comp_alloc(n, want, fips, users, out);
        }
        Comp::If(_, t, e) => {
            comp_alloc(t, want, fips, users, out);
            comp_alloc(e, want, fips, users, out);
        }
        Comp::Case(_, arms) => arms
            .iter()
            .for_each(|(_, b)| comp_alloc(b, want, fips, users, out)),
        Comp::Lam(_, b) | Comp::Mask(_, b) => comp_alloc(b, want, fips, users, out),
        Comp::App(fbody, args) => {
            comp_alloc(fbody, want, fips, users, out);
            for a in args {
                value_alloc(a, out);
            }
            out.push(AllocWitness::IndirectCall);
        }
        Comp::Prim(_, a, b) => {
            value_alloc(a, out);
            value_alloc(b, out);
        }
        // The fip check runs on the un-effect-lowered core, so a Ref op (introduced
        // only by `erase_local_vars` during effect lowering) is unreachable here;
        // check its values for completeness.
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::UnboxedProject(v, _)
        | Comp::Drop(v)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => value_alloc(v, out),
        // `InitAt` is a post-lowering (arena) node, unreachable in this
        // pre-lowering check; kept total, and its embedded constructor still
        // counts as an allocation like a `RefSet`'s stored value.
        Comp::RefSet(cell, v) | Comp::InitAt(cell, v) => {
            value_alloc(cell, out);
            value_alloc(v, out);
        }
        Comp::Do(op, args) => {
            // A performed `alloc` materializes a fresh cell (serviced from an
            // arena when one is installed, from `prism_alloc` otherwise), so it
            // is an allocation witness like a bare `Ctor`. Every other effect
            // operation is control, not allocation, and contributes no witness.
            if op.as_str() == names::ALLOC_OP {
                out.push(AllocWitness::AllocOp);
            }
            for a in args {
                value_alloc(a, out);
            }
        }
        Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for a in args {
                value_alloc(a, out);
            }
        }
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            comp_alloc(body, want, fips, users, out);
            if let Some(rb) = return_body {
                comp_alloc(rb, want, fips, users, out);
            }
            for op in ops {
                comp_alloc(&op.body, want, fips, users, out);
            }
        }
        Comp::Dup(_) => {}
    }
}

// Render the recorded witnesses into the checker's message. The wrapper keeps the
// "function `f` is marked `kw` but ..." shape the driver seam strips and reframes
// (`fip`/`fbip` as a usage check, `@ noalloc` as an allocation certificate), so
// the family stays consistent while every discipline gains the witness detail.
fn render_alloc(want: Fip, fname: &str, w: &Witnesses) -> String {
    let mut parts: Vec<String> = w.seen.iter().map(|wit| witness_clause(wit, want)).collect();
    let extra = w.extra();
    if extra > 0 {
        parts.push(format!("and {extra} more"));
    }
    format!(
        "function `{fname}` is marked `{}` but in `{fname}`, {}",
        kw(want),
        parts.join("; ")
    )
}

fn witness_clause(w: &AllocWitness, want: Fip) -> String {
    match w {
        AllocWitness::Ctor(name) => format!("constructor `{name}` is built fresh outside `reuse`"),
        AllocWitness::Tuple => "a tuple is built fresh outside `reuse`".to_string(),
        AllocWitness::Closure => "a lambda is materialized as a fresh closure cell".to_string(),
        AllocWitness::UncertifiedCall(callee) => match want {
            Fip::Fip => format!(
                "call to `{callee}` is not certified `fip`, so bounded stack and zero allocation cannot be proven"
            ),
            Fip::Fbip | Fip::No => {
                format!("call to `{callee}` may allocate (`{callee}` has no zero-allocation certificate)")
            }
        },
        AllocWitness::IndirectCall => {
            "an indirect call through a first-class function value has no callee certificate"
                .to_string()
        }
        AllocWitness::Builtin(name) => {
            format!("primitive `{name}` is not on the allocation-free allow-list")
        }
        AllocWitness::AllocOp => {
            "`alloc` carves a fresh cell from an arena, which is cheaper but not free".to_string()
        }
    }
}

/// Verify every `fip`/`fbip`-annotated function over the reuse-lowered core.
///
/// `fips` maps a function name to its annotation, `sigs` the borrow mask (a
/// `fip` function may carry no borrowed param), and `users` is the set of
/// user-defined function names (to tell a user call from a prim/builtin).
///
/// # Errors
/// Fails with a clear message when an annotated function allocates fresh, is
/// non-linear, or calls an unannotated user function.
pub fn check_fip(
    core: &Core,
    fips: &Fips,
    sigs: &Sigs,
    users: &BTreeSet<Sym>,
) -> Result<(), String> {
    for f in &core.fns {
        let Some(&want) = fips.get(&f.name) else {
            continue;
        };
        if want == Fip::Fip {
            if let Some(mask) = sigs.get(&f.name) {
                if mask.iter().any(|b| *b) {
                    return Err(format!(
                        "function `{}` is marked `fip` but is not linear (has a borrowed parameter)",
                        f.name
                    ));
                }
            }
        }
        let mut witnesses = Witnesses::new();
        comp_alloc(&f.body, want, fips, users, &mut witnesses);
        if !witnesses.seen.is_empty() {
            return Err(render_alloc(want, f.name.as_str(), &witnesses));
        }
        if want == Fip::Fip {
            bounded_stack(f, core, users)?;
        }
    }
    Ok(())
}

// Bounded-stack rule (the third FP^2 property): a `fip` function runs in O(1)
// stack iff every recursive call inside its own frame is a loop, not a frame.
// Compute the SCC (mutual recursion counts) and classify each in-group call
// with the shared `tailrec`: a `NonTail` recursive call grows the stack one
// frame per element and is rejected. Codegen lowers at most one TRMC shape per
// function and only for direct self-recursion, so a body mixing cons- and
// add-TRMC, or one that pairs TRMC with a mutual call, is rejected too: those
// are exactly the shapes the backend would leave as real recursion.
fn bounded_stack(f: &CoreFn, core: &Core, users: &BTreeSet<Sym>) -> Result<(), String> {
    let group = scc_of(core, users, f.name);
    // The direct-call SCC is a subset used only to explain a rejection: a member
    // missing from it sits in the group because a function flows as a value, not
    // because of a real call cycle.
    let call_group = scc_of_calls(core, users, f.name);
    let (mut cons, mut add, mut mutual) = (false, false, false);
    for (g, cls) in recursive_calls(&f.body, f.name, f.params.len(), &group) {
        match cls {
            TailClass::NonTail => return Err(nontail_err(f.name.as_str(), g, &call_group)),
            TailClass::TrmcCons => cons = true,
            TailClass::TrmcAdd => add = true,
            TailClass::Tail => {}
        }
        mutual |= g != f.name;
    }
    if cons && add {
        return Err(format!(
            "function `{}` is marked `fip` but mixes tail-modulo-constructor and \
             tail-modulo-addition recursion; codegen loops only one shape per function, \
             so split it or annotate it `fbip`",
            f.name
        ));
    }
    if (cons || add) && mutual {
        return Err(format!(
            "function `{}` is marked `fip` but pairs tail-modulo-constructor/addition \
             recursion with a mutually recursive call; codegen loops only direct self-TRMC, \
             so make the mutual call a plain tail call or annotate it `fbip`",
            f.name
        ));
    }
    Ok(())
}

fn nontail_err(fname: &str, callee: Sym, call_group: &BTreeSet<Sym>) -> String {
    let base = format!(
        "function `{fname}` is marked `fip` but recurses in non-tail position (one stack \
         frame per element); make the recursive call a tail call or a tail under a single \
         constructor / addition, or annotate it `fbip`"
    );
    // When the non-tail callee is in the recursion group only via a first-class
    // reference (not a direct-call cycle), the discipline can feel surprising:
    // capturing a function as a value, not calling it back, is what enlarged the
    // group. Name that so the fix (drop the capture, or annotate `fbip`) is clear.
    if callee != Sym::from(fname) && !call_group.contains(&callee) {
        format!(
            "{base}\nnote: `{callee}` is in `{fname}`'s tail-recursion group only because a \
             function flows as a first-class value somewhere in the cycle, not through direct \
             calls; if they do not actually recurse through each other, avoid capturing the \
             function as a value (call it directly) or annotate `fbip`"
        )
    } else {
        base
    }
}

/// Verify the linearity of every `fip` function over the raw (pre-RC) core.
///
/// Linearity is a property of the SOURCE term: each owned, non-immediate binder
/// (parameter, pattern field, let result) is consumed at most once on any
/// control path. `dup`/`drop` on an immediate (`Int`, `Bool`, ...) is a runtime
/// no-op under pointer tagging, so scalars are unrestricted, matching the FP^2
/// discipline (linearity constrains heap, not machine words). The RC pass later
/// inserts the dup/drop that REALIZE this linear consumption over a unique cell;
/// those are an implementation detail of a linear program and are not re-counted
/// against it (which is why this runs pre-RC, not on the `check_fip` core).
///
/// # Errors
/// Fails when a `fip` function uses an owned heap value more than once.
pub fn check_fip_linear(
    core: &Core,
    fips: &Fips,
    decls: &[DeclInfo],
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<(), String> {
    for f in &core.fns {
        if fips.get(&f.name) != Some(&Fip::Fip) {
            continue;
        }
        let arrow = decls
            .iter()
            .find(|d| d.name == f.name.as_str())
            .and_then(|d| arrow_args(&d.ty));
        // Hidden dictionary params would misalign the arrow against `f.params`,
        // so trust a per-position type only when the counts match; otherwise
        // treat every param as heap (require linear), which never under-rejects.
        let param_imm = |i: usize| {
            arrow
                .filter(|a| a.len() == f.params.len())
                .and_then(|a| a.get(i))
                .is_some_and(is_immediate)
        };
        for (i, p) in f.params.iter().enumerate() {
            if !param_imm(i) && max_uses(*p, &f.body) > 1 {
                return Err(dup_err(f.name.as_str()));
            }
        }
        lin_comp(&f.body, f.name.as_str(), ctors)?;
        // `lin_comp` checks one frame and does not cross into thunks (a closure
        // body is a separate frame). Those bodies still need checking, or a binder
        // duplicated inside a captured closure evades the `fip` linearity gate.
        let mut tl = ThunkLin {
            fname: f.name.as_str(),
            ctors,
            err: None,
        };
        tl.visit_comp(&f.body);
        if let Some(e) = tl.err {
            return Err(e);
        }
    }
    Ok(())
}

// Drives the exhaustive walk to reach every thunk (which `lin_comp` skips) and
// lin-checks each body as its own scope; short-circuits on the first failure.
struct ThunkLin<'a> {
    fname: &'a str,
    ctors: &'a BTreeMap<String, CtorInfo>,
    err: Option<String>,
}

impl Visit for ThunkLin<'_> {
    fn visit_value(&mut self, v: &Value) {
        if let Value::Thunk(c) = v {
            if self.err.is_none() {
                self.err = lin_comp(c, self.fname, self.ctors).err();
            }
        }
        self.descend_value(v);
    }
}

const fn is_immediate(t: &Type) -> bool {
    matches!(
        t,
        Type::Unit | Type::Int | Type::I64 | Type::U64 | Type::Bool | Type::Float | Type::Char
    )
}

fn arrow_args(t: &Type) -> Option<&[Type]> {
    match t {
        Type::Forall(_, b) | Type::RowForall(_, b) => arrow_args(b),
        Type::Fun(args, _, _) => Some(args.as_slice()),
        _ => None,
    }
}

fn dup_err(fname: &str) -> String {
    format!("function `{fname}` is marked `fip` but is not linear (duplicates a value)")
}

// A let/match binder is immediate when its RHS provably yields a scalar: a
// primitive (arithmetic/comparison) or a scalar literal. Anything else (a call,
// a constructor, an unknown variable) is treated as heap and must be linear.
const fn binds_immediate(m: &Comp) -> bool {
    match m {
        Comp::Prim(..) => true,
        Comp::Return(v) => matches!(
            v,
            Value::Int(_)
                | Value::I64(_)
                | Value::U64(_)
                | Value::Bool(_)
                | Value::Float(_)
                | Value::Unit
        ),
        _ => false,
    }
}

// Walk binders introduced inside the body, checking each non-immediate one is
// used at most once on any path through its scope.
fn lin_comp(c: &Comp, fname: &str, ctors: &BTreeMap<String, CtorInfo>) -> Result<(), String> {
    let recur = |c: &Comp| lin_comp(c, fname, ctors);
    match c {
        Comp::Bind(m, x, n) => {
            recur(m)?;
            if !binds_immediate(m) && max_uses(*x, n) > 1 {
                return Err(dup_err(fname));
            }
            recur(n)
        }
        Comp::If(_, t, e) => {
            recur(t)?;
            recur(e)
        }
        Comp::Case(_, arms) => arms.iter().try_for_each(|(p, body)| {
            check_fields(p, body, fname, ctors)?;
            recur(body)
        }),
        Comp::Lam(ps, b) => {
            // Closure params have no recorded type here, so require them linear.
            if ps.iter().any(|p| max_uses(*p, b) > 1) {
                return Err(dup_err(fname));
            }
            recur(b)
        }
        Comp::App(f, _) => recur(f),
        Comp::Mask(_, b) => recur(b),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            recur(body)?;
            if let Some(rb) = return_body {
                recur(rb)?;
            }
            ops.iter().try_for_each(|op| recur(&op.body))
        }
        _ => Ok(()),
    }
}

// Pattern-bound fields: a field with a concrete immediate type (e.g. the `Int`
// field of a monomorphic constructor) is unrestricted; a heap or generic field
// must be used at most once in the arm.
fn check_fields(
    p: &CorePat,
    body: &Comp,
    fname: &str,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<(), String> {
    let (arg_types, fields): (Option<&[Type]>, &[Option<Sym>]) = match p {
        CorePat::Ctor(name, fs) => (ctors.get(name.as_str()).map(|ci| ci.args.as_slice()), fs),
        CorePat::Tuple(fs) => (None, fs),
        _ => (None, &[]),
    };
    for (i, fld) in fields.iter().enumerate() {
        let Some(x) = fld else { continue };
        let imm = arg_types.and_then(|a| a.get(i)).is_some_and(is_immediate);
        if !imm && max_uses(*x, body) > 1 {
            return Err(dup_err(fname));
        }
    }
    Ok(())
}

// The maximum number of consuming occurrences of `x` along any single path. The
// two arms of an `if`/`case` are different paths (take the max); a bind chain is
// one path (sum). A binder that shadows `x` ends its scope. Occurrences inside a
// thunk count once (the capture).
fn max_uses(x: Sym, c: &Comp) -> usize {
    let occ = |v: &Value| {
        let mut m = BTreeMap::new();
        count_val(v, &mut m);
        m.get(&x).copied().unwrap_or(0)
    };
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::UnboxedProject(v, _)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => occ(v),
        Comp::RefSet(c, v) => occ(c) + occ(v),
        // `token` shadows `x` over `body`; the freed cell is named in scope.
        Comp::WithReuse { token, freed, body } => {
            occ(freed) + if *token == x { 0 } else { max_uses(x, body) }
        }
        Comp::Reuse(tok, v) => usize::from(*tok == x) + occ(v),
        Comp::InitAt(cell, v) => occ(cell) + occ(v),
        Comp::Prim(_, a, b) => occ(a) + occ(b),
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            args.iter().map(occ).sum()
        }
        Comp::Bind(m, y, n) => max_uses(x, m) + if *y == x { 0 } else { max_uses(x, n) },
        Comp::If(v, t, e) => occ(v) + max_uses(x, t).max(max_uses(x, e)),
        Comp::Case(v, arms) => {
            occ(v)
                + arms
                    .iter()
                    .map(|(p, b)| {
                        let mut pv = Set::new();
                        pat_vars(p, &mut pv);
                        if pv.contains(&x) {
                            0
                        } else {
                            max_uses(x, b)
                        }
                    })
                    .max()
                    .unwrap_or(0)
        }
        Comp::App(f, args) => max_uses(x, f) + args.iter().map(occ).sum::<usize>(),
        Comp::Lam(ps, b) => {
            if ps.contains(&x) {
                0
            } else {
                max_uses(x, b)
            }
        }
        Comp::Mask(_, b) => max_uses(x, b),
        // Pure `fip` functions never reach a handler; a conservative sum over its
        // clauses only over-counts, which stays on the safe (over-reject) side.
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            max_uses(x, body)
                + return_body.as_ref().map_or(0, |rb| max_uses(x, rb))
                + ops.iter().map(|op| max_uses(x, &op.body)).sum::<usize>()
        }
    }
}

const fn kw(f: Fip) -> &'static str {
    match f {
        Fip::Fip => "fip",
        Fip::Fbip | Fip::No => "fbip",
    }
}

// Direct coverage of `bounded_stack`'s rules. The strict no-`Dup` linearity pass
// rejects every recursive heap function before this check is reached end-to-end,
// so the mixed-mode and mutual-plus-TRMC paths can only be exercised on
// hand-built core (the linearity and allocation passes are bypassed here, which
// is exactly what isolates the stack rule).
#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::cbpv::CoreOp;

    fn users(names: &[&str]) -> BTreeSet<Sym> {
        names.iter().map(|n| Sym::from(*n)).collect()
    }

    fn one(name: &str, arity: usize, body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            dict_arity: 0,
            params: (0..arity)
                .map(|i| Sym::from(format!("p{i}").as_str()))
                .collect(),
            body,
        }
    }

    // `f(x) to t; <k>`, the recursive-call-feeding-continuation shape.
    fn rec(k: Comp) -> Comp {
        Comp::Bind(
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
            "t".into(),
            Box::new(k),
        )
    }

    fn cons_tail() -> Comp {
        rec(Comp::Return(Value::Ctor(
            "Cons".into(),
            1,
            vec![Value::Var("h".into()), Value::Var("t".into())],
        )))
    }

    fn add_tail() -> Comp {
        rec(Comp::Prim(
            CoreOp::Add,
            Value::Int(1),
            Value::Var("t".into()),
        ))
    }

    #[test]
    fn nontail_self_call_is_rejected() {
        let f = one(
            "f",
            1,
            rec(Comp::Prim(
                CoreOp::Mul,
                Value::Var("t".into()),
                Value::Var("x".into()),
            )),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = bounded_stack(&f, &core, &users(&["f"])).unwrap_err();
        assert!(err.contains("non-tail position"), "{err}");
    }

    #[test]
    fn plain_tail_and_one_trmc_mode_is_accepted() {
        // A cons-TRMC tail beside a plain self tail-call: codegen loops both.
        let body = Comp::If(
            Value::Bool(true),
            Box::new(cons_tail()),
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
        );
        let f = one("f", 1, body);
        let core = Core {
            fns: vec![f.clone()],
        };
        assert!(bounded_stack(&f, &core, &users(&["f"])).is_ok());
    }

    #[test]
    fn mixed_cons_and_add_is_rejected() {
        let body = Comp::If(
            Value::Bool(true),
            Box::new(cons_tail()),
            Box::new(add_tail()),
        );
        let f = one("f", 1, body);
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = bounded_stack(&f, &core, &users(&["f"])).unwrap_err();
        assert!(err.contains("mixes"), "{err}");
    }

    #[test]
    fn trmc_paired_with_mutual_call_is_rejected() {
        // f cons-TRMCs itself but also tail-calls g (its SCC partner); codegen
        // loops only direct self-TRMC, so the mutual call would grow the stack.
        let body = Comp::If(
            Value::Bool(true),
            Box::new(cons_tail()),
            Box::new(Comp::Call("g".into(), vec![Value::Var("x".into())])),
        );
        let f = one("f", 1, body);
        let g = one("g", 1, Comp::Call("f".into(), vec![Value::Var("x".into())]));
        let core = Core {
            fns: vec![f.clone(), g],
        };
        let err = bounded_stack(&f, &core, &users(&["f", "g"])).unwrap_err();
        assert!(err.contains("mutually recursive"), "{err}");
    }

    #[test]
    fn nonrecursive_is_trivially_bounded() {
        let f = one(
            "f",
            2,
            Comp::Prim(
                CoreOp::Add,
                Value::Var("p0".into()),
                Value::Var("p1".into()),
            ),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        assert!(bounded_stack(&f, &core, &users(&["f"])).is_ok());
    }

    // --- type-aware linearity (`check_fip_linear`) ---

    fn decl(name: &str, params: Vec<Type>) -> DeclInfo {
        DeclInfo {
            name: name.into(),
            params: (0..params.len()).map(|i| format!("p{i}")).collect(),
            ty: Type::fun(params, Type::Int),
            effects: Set::new(),
        }
    }

    fn linfn(name: &str, params: &[&str], body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            params: params.iter().map(|p| Sym::from(*p)).collect(),
            dict_arity: 0,
            body,
        }
    }

    fn fip_of(f: &CoreFn) -> Fips {
        std::iter::once((f.name, Fip::Fip)).collect()
    }

    fn fbip_of(f: &CoreFn) -> Fips {
        std::iter::once((f.name, Fip::Fbip)).collect()
    }

    fn use_var_twice(x: &str) -> Comp {
        Comp::Prim(CoreOp::Add, Value::Var(x.into()), Value::Var(x.into()))
    }

    #[test]
    fn zero_alloc_rejects_fresh_closure_value() {
        let f = one(
            "make",
            1,
            Comp::Return(Value::Thunk(Box::new(Comp::Prim(
                CoreOp::Add,
                Value::Var("p0".into()),
                Value::Var("y".into()),
            )))),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = check_fip(&core, &fbip_of(&f), &BTreeMap::new(), &users(&["make"]))
            .expect_err("fbip/without-alloc must reject closure allocation");
        assert!(
            err.contains("a lambda is materialized as a fresh closure cell"),
            "{err}"
        );
    }

    #[test]
    fn heap_param_used_twice_is_rejected() {
        // `Str` is a boxed value, so two uses need a real dup.
        let f = linfn("f", &["s"], use_var_twice("s"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Str])];
        let err = check_fip_linear(&core, &fip_of(&f), &decls, &BTreeMap::new()).unwrap_err();
        assert!(err.contains("not linear"), "{err}");
    }

    #[test]
    fn immediate_param_used_twice_is_allowed() {
        // `Int` is an immediate; `dup` is a runtime no-op, so `x + x` is linear.
        let f = linfn("f", &["x"], use_var_twice("x"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Int])];
        assert!(check_fip_linear(&core, &fip_of(&f), &decls, &BTreeMap::new()).is_ok());
    }

    fn pair_ctors(field0: Type, field1: Type) -> BTreeMap<String, CtorInfo> {
        std::iter::once((
            "Pair".to_string(),
            CtorInfo {
                type_name: "P".into(),
                params: vec![],
                param_kinds: vec![],
                args: vec![field0, field1],
                tag: 0,
                fields: vec!["a".into(), "b".into()],
            },
        ))
        .collect()
    }

    fn match_pair(field_used_twice: &str) -> Comp {
        Comp::Case(
            Value::Var("p".into()),
            vec![(
                CorePat::Ctor("Pair".into(), vec![Some("a".into()), Some("b".into())]),
                use_var_twice(field_used_twice),
            )],
        )
    }

    #[test]
    fn immediate_ctor_field_used_twice_is_allowed() {
        // Field `a` is a concrete `Int`, so reusing it is fine.
        let f = linfn("f", &["p"], match_pair("a"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Con("P".into(), vec![])])];
        let ctors = pair_ctors(Type::Int, Type::Str);
        assert!(check_fip_linear(&core, &fip_of(&f), &decls, &ctors).is_ok());
    }

    #[test]
    fn heap_ctor_field_used_twice_is_rejected() {
        // Field `b` is a boxed `Str`, so two uses need a dup.
        let f = linfn("f", &["p"], match_pair("b"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Con("P".into(), vec![])])];
        let ctors = pair_ctors(Type::Int, Type::Str);
        let err = check_fip_linear(&core, &fip_of(&f), &decls, &ctors).unwrap_err();
        assert!(err.contains("not linear"), "{err}");
    }

    #[test]
    fn branches_are_distinct_paths() {
        // `s` used once per arm is once per path: linear despite two textual uses.
        let body = Comp::If(
            Value::Bool(true),
            Box::new(Comp::Return(Value::Var("s".into()))),
            Box::new(Comp::Return(Value::Var("s".into()))),
        );
        let f = linfn("f", &["s"], body);
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Str])];
        assert!(check_fip_linear(&core, &fip_of(&f), &decls, &BTreeMap::new()).is_ok());
    }
}
