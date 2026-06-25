use std::collections::{BTreeMap, BTreeSet};

use crate::names::reuse_token;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Fip, Program};
use crate::types::{CtorInfo, DeclInfo, Type};

use super::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::fv::{comp as freev, pat_vars};
use super::tailrec::{recursive_calls, scc_of, scc_of_calls, TailClass};

// Perceus-style reference counting (Reinking et al.). Function parameters and
// every let-bound result are owned; each owned value is consumed exactly once on
// every control path. A second consuming use inserts dup; a value that dies
// unused inserts drop. Pattern-extracted fields are dup'd live at the match so
// they own a reference independent of the scrutinee, which is then dropped once
// dead (the dup precedes the drop so a freed cell never strands a live field).
// Closure captures stay owned by the closure cell, so inside a lambda body they
// are borrowed: a consuming use dups first and the body never drops them. Sound
// under pointer tagging: inc/dec are no-ops on immediates, so dup/drop on a
// non-cell is harmless. The `fbip` dump shows the ops; a run under
// PRISM_CHECK_LEAKS reports zero live cells at exit.

type Set = BTreeSet<Sym>;

// Per-function borrow mask, one bool per param in order. A borrow parameter is
// borrowed by the callee (never dropped, dup'd before any consuming use) and
// retained by the caller (not transferred at the call). Only pure functions may
// carry a borrow param, so they all go through the untouched `lower_comp` path
// and reach this pass as ordinary positional calls. Functions absent from the
// map default to all-owned.
pub type Sigs = BTreeMap<Sym, Vec<bool>>;

#[must_use]
pub fn borrow_sigs(prog: &Program<CorePhase>) -> Sigs {
    prog.fns
        .iter()
        .filter(|d| d.params.iter().any(|p| p.borrow))
        .map(|d| {
            (
                d.name.clone().into(),
                d.params.iter().map(|p| p.borrow).collect(),
            )
        })
        .collect()
}

#[must_use]
pub fn insert_rc(core: &Core, sigs: &Sigs) -> Core {
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| {
                let mask = sigs.get(&f.name);
                let owned: Set = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !mask.is_some_and(|m| m.get(*i).copied().unwrap_or(false)))
                    .map(|(_, p)| *p)
                    .collect();
                let borrowed: Set = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask.is_some_and(|m| m.get(*i).copied().unwrap_or(false)))
                    .map(|(_, p)| *p)
                    .collect();
                CoreFn {
                    name: f.name,
                    params: f.params.clone(),
                    body: rc(&f.body, &owned, &borrowed, sigs),
                }
            })
            .collect(),
    }
}

#[must_use]
pub fn reuse(core: &Core) -> Core {
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| CoreFn {
                name: f.name,
                params: f.params.clone(),
                body: reuse_comp(&f.body),
            })
            .collect(),
    }
}

fn reuse_comp(c: &Comp) -> Comp {
    match c {
        Comp::Bind(m, x, n) => Comp::Bind(Box::new(reuse_comp(m)), *x, Box::new(reuse_comp(n))),
        Comp::If(v, t, e) => Comp::If(v.clone(), Box::new(reuse_comp(t)), Box::new(reuse_comp(e))),
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(reuse_comp(b))),
        Comp::Case(scrut, arms) => Comp::Case(
            scrut.clone(),
            arms.iter()
                .map(|(p, body)| (p.clone(), reuse_arm(scrut, p, &reuse_comp(body))))
                .collect(),
        ),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(reuse_comp(body)),
            return_var: *return_var,
            return_body: return_body.as_deref().map(|rb| Box::new(reuse_comp(rb))),
            ops: ops
                .iter()
                .map(|op| HandleOp {
                    body: reuse_comp(&op.body),
                    ..op.clone()
                })
                .collect(),
        },
        other => other.clone(),
    }
}

fn reuse_arm(scrut: &Value, p: &CorePat, body: &Comp) -> Comp {
    let Value::Var(s) = scrut else {
        return body.clone();
    };
    let arity = match p {
        CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => fields.len(),
        _ => return body.clone(),
    };
    let tok: Sym = reuse_token(s.as_str()).into();
    // Reuse is a pure optimization: if the rewrite ever came back unbalanced
    // (a token freed without a matching consume on some path), decline it and
    // keep the safe no-reuse body. Same observable output, no ICE.
    try_reuse(body, *s, tok, arity)
        .filter(|out| token_balanced(out, tok))
        .unwrap_or_else(|| body.clone())
}

// Pair the `drop s` (the cell freed when the scrutinee is consumed) with a later
// constructor allocation. The drop may sit on the bind chain or, when the
// scrutinee survives down some arms, inside a branch; either way the freed cell
// becomes a token that the rest of THAT path must spend exactly once. Find the
// drop, then hand the continuation to `consume_alloc`, which fails (aborting the
// whole rewrite) unless every path from the drop allocates a fitting cell. Arms
// where the drop never appears are left untouched.
fn try_reuse(c: &Comp, s: Sym, tok: Sym, cap: usize) -> Option<Comp> {
    match c {
        Comp::Bind(m, x, n) => {
            if let Comp::Drop(Value::Var(d)) = m.as_ref() {
                if *d == s {
                    let n2 = consume_alloc(n, tok, cap)?;
                    let token = Comp::ReuseToken(Value::Var(s));
                    return Some(Comp::Bind(Box::new(token), tok, Box::new(n2)));
                }
            }
            if let Some(m2) = try_reuse(m, s, tok, cap) {
                return Some(Comp::Bind(Box::new(m2), *x, n.clone()));
            }
            Some(Comp::Bind(
                m.clone(),
                *x,
                Box::new(try_reuse(n, s, tok, cap)?),
            ))
        }
        Comp::If(cond, t, e) => {
            let (t2, e2) = (try_reuse(t, s, tok, cap), try_reuse(e, s, tok, cap));
            // The drop must live in exactly one branch (the scrutinee cannot be
            // both freed and passed through on the same conditional).
            match (t2, e2) {
                (Some(t2), None) => Some(Comp::If(cond.clone(), Box::new(t2), e.clone())),
                (None, Some(e2)) => Some(Comp::If(cond.clone(), t.clone(), Box::new(e2))),
                _ => None,
            }
        }
        Comp::Case(scrut, arms) => {
            let mut hit = false;
            let arms = arms
                .iter()
                .map(|(p, b)| {
                    try_reuse(b, s, tok, cap).map_or_else(
                        || (p.clone(), b.clone()),
                        |b2| {
                            hit = true;
                            (p.clone(), b2)
                        },
                    )
                })
                .collect();
            hit.then(|| Comp::Case(scrut.clone(), arms))
        }
        _ => None,
    }
}

// Soundness net: along every root-to-leaf path the token is freed (ReuseToken)
// and consumed (Reuse) the same number of times, so it never leaks or double
// frees. Consumes hidden inside a Lam body run later and do not count here.
// A divergent leaf (`Comp::Error`) aborts the process, which reclaims the held
// shell, so reaching it with a live token discharges the obligation rather than
// leaking: the path counts as balanced (false). Modelling divergence this way
// keeps the analysis precise (a branch that consumes on one side and crashes on
// the other still earns reuse) instead of conservatively declining.
fn token_balanced(c: &Comp, tok: Sym) -> bool {
    fn walk(c: &Comp, tok: Sym, live: bool) -> Option<bool> {
        match c {
            Comp::Error(_) => Some(false),
            Comp::Bind(m, x, n) => {
                let live = if matches!(m.as_ref(), Comp::ReuseToken(_)) && *x == tok {
                    true
                } else {
                    // `m` runs on the same path before `n`, so the credit flows
                    // through it; its exit state is what enters `n`.
                    walk(m, tok, live)?
                };
                walk(n, tok, live)
            }
            Comp::Reuse(Value::Var(t), _) if *t == tok => live.then_some(false),
            Comp::If(_, t, e) => {
                let a = walk(t, tok, live)?;
                let b = walk(e, tok, live)?;
                (a == b).then_some(a)
            }
            Comp::Case(_, arms) => {
                let mut it = arms.iter().map(|(_, b)| walk(b, tok, live));
                let first = it.next().unwrap_or(Some(live))?;
                for r in it {
                    if r? != first {
                        return None;
                    }
                }
                Some(first)
            }
            _ => Some(live),
        }
    }
    matches!(walk(c, tok, false), Some(false))
}

// Reuse credit (FP^2): a freed token feeds the first constructor allocation that
// follows the drop on every control path, not just the literal tail. Walk the
// bind chain forward and rewrite the first `return Ctor` (whose arity fits the
// freed cell, so prism_reuse_alloc never writes past the old shell) into an
// in-place `Reuse`; the token is then spent and the continuation left alone. At a
// branch every arm must spend the credit exactly once, so both sides must
// succeed. Any path reaching a non-allocating tail returns None, aborting the
// whole rewrite and falling back to the safe body.
fn consume_alloc(c: &Comp, tok: Sym, cap: usize) -> Option<Comp> {
    match c {
        Comp::Bind(m, x, n) => {
            // The bound computation `m` may itself tail-produce the allocation
            // (CBPV nests `return Ctor to x; ...` as a bind chain under one `m`),
            // so try to spend the credit there first; only if no path of `m`
            // allocates does the credit flow on into the continuation `n`.
            if let Some(m2) = consume_alloc(m, tok, cap) {
                return Some(Comp::Bind(Box::new(m2), *x, n.clone()));
            }
            Some(Comp::Bind(
                m.clone(),
                *x,
                Box::new(consume_alloc(n, tok, cap)?),
            ))
        }
        Comp::Return(v @ (Value::Ctor(..) | Value::Tuple(..))) if ctor_arity(v) <= cap => {
            Some(Comp::Reuse(Value::Var(tok), v.clone()))
        }
        Comp::If(cond, t, e) => Some(Comp::If(
            cond.clone(),
            Box::new(consume_alloc(t, tok, cap)?),
            Box::new(consume_alloc(e, tok, cap)?),
        )),
        Comp::Case(scrut, arms) => {
            let arms = arms
                .iter()
                .map(|(p, b)| Some((p.clone(), consume_alloc(b, tok, cap)?)))
                .collect::<Option<Vec<_>>>()?;
            Some(Comp::Case(scrut.clone(), arms))
        }
        _ => None,
    }
}

const fn ctor_arity(v: &Value) -> usize {
    match v {
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.len(),
        _ => 0,
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

fn rc(c: &Comp, owned: &Set, borrowed: &Set, sigs: &Sigs) -> Comp {
    match c {
        Comp::Bind(m, x, n) => {
            let fm = freev(m);
            let mut fnn = freev(n);
            fnn.remove(x);
            let owned_m: Set = owned.intersection(&fm).copied().collect();
            let owned_n: Set = owned.intersection(&fnn).copied().collect();
            let shared = by_name(owned_m.intersection(&owned_n).copied());
            let dead = by_name(
                owned
                    .iter()
                    .filter(|v| !fm.contains(*v) && !fnn.contains(*v))
                    .copied(),
            );
            let borrowed_m: Set = borrowed.intersection(&fm).copied().collect();
            let borrowed_n: Set = borrowed.intersection(&fnn).copied().collect();
            let m2 = rc(m, &owned_m, &borrowed_m, sigs);
            let mut owned_n2 = owned_n;
            owned_n2.insert(*x);
            let n2 = rc(n, &owned_n2, &borrowed_n, sigs);
            let mut out = Comp::Bind(Box::new(m2), *x, Box::new(n2));
            for v in shared {
                out = dup(v, out);
            }
            for v in dead {
                out = drop_(v, out);
            }
            out
        }
        Comp::If(v, t, e) => Comp::If(
            v.clone(),
            Box::new(rc(t, owned, borrowed, sigs)),
            Box::new(rc(e, owned, borrowed, sigs)),
        ),
        Comp::Case(scrut, arms) => Comp::Case(
            scrut.clone(),
            arms.iter()
                .map(|(p, body)| (p.clone(), rc_arm(p, body, owned, borrowed, sigs)))
                .collect(),
        ),
        Comp::Lam(ps, body) => {
            let ps_set: Set = ps.iter().copied().collect();
            let caps: Set = freev(body).difference(&ps_set).copied().collect();
            Comp::Lam(ps.clone(), Box::new(rc(body, &ps_set, &caps, sigs)))
        }
        // Reachable only via the pre-lowering `dump fbip` display path,
        // compiled pipelines always lower handles first.
        Comp::Mask(ops, b) => Comp::Mask(ops.clone(), Box::new(rc(b, owned, borrowed, sigs))),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(rc(body, &Set::new(), &Set::new(), sigs)),
            return_var: *return_var,
            return_body: return_body.as_deref().map(|rb| {
                let o = return_var.iter().copied().collect();
                Box::new(rc(rb, &o, &Set::new(), sigs))
            }),
            ops: ops
                .iter()
                .map(|op| {
                    let o = op.params.iter().copied().collect();
                    HandleOp {
                        name: op.name,
                        params: op.params.clone(),
                        resume: op.resume,
                        body: rc(&op.body, &o, &Set::new(), sigs),
                    }
                })
                .collect(),
        },
        leaf => {
            let mut counts = BTreeMap::new();
            leaf_counts(leaf, &mut counts, sigs);
            let mut out = rc_thunks(leaf, sigs);
            for v in by_name(owned.iter().copied()) {
                match counts.get(&v).copied().unwrap_or(0) {
                    0 => out = drop_(v, out),
                    k => {
                        for _ in 1..k {
                            out = dup(v, out);
                        }
                    }
                }
            }
            for v in by_name(borrowed.iter().copied()) {
                for _ in 0..counts.get(&v).copied().unwrap_or(0) {
                    out = dup(v, out);
                }
            }
            out
        }
    }
}

// A thunk is a closure: its free vars are captured by the cell and borrowed
// inside the body (the cell owns them, a consuming use dups first, the body never
// drops them). rc never descends into values, so without this the body of every
// `\..` passed as an argument would keep its raw elaborated form and consume a
// borrowed capture with no dup, freeing a shared spine out from under the caller.
// A Lam recomputes its own params/captures; a bare suspended computation borrows
// all of its free vars.
fn rc_value(v: &Value, sigs: &Sigs) -> Value {
    match v {
        Value::Thunk(c) => Value::Thunk(Box::new(rc(c, &Set::new(), &freev(c), sigs))),
        Value::Ctor(t, i, fs) => {
            Value::Ctor(*t, *i, fs.iter().map(|f| rc_value(f, sigs)).collect())
        }
        Value::Tuple(fs) => Value::Tuple(fs.iter().map(|f| rc_value(f, sigs)).collect()),
        other => other.clone(),
    }
}

fn rc_thunks(c: &Comp, sigs: &Sigs) -> Comp {
    let rv = |v: &Value| rc_value(v, sigs);
    match c {
        Comp::Return(v) => Comp::Return(rv(v)),
        Comp::Force(v) => Comp::Force(rv(v)),
        Comp::Print(v) => Comp::Print(rv(v)),
        Comp::PrintF(v) => Comp::PrintF(rv(v)),
        Comp::PrintS(v) => Comp::PrintS(rv(v)),
        Comp::Error(v) => Comp::Error(rv(v)),
        Comp::Srand(v) => Comp::Srand(rv(v)),
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, rv(v)),
        Comp::Prim(op, a, b) => Comp::Prim(*op, rv(a), rv(b)),
        Comp::Call(n, args) => Comp::Call(*n, args.iter().map(rv).collect()),
        Comp::Do(n, args) => Comp::Do(*n, args.iter().map(rv).collect()),
        Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, args.iter().map(rv).collect()),
        Comp::App(f, args) => {
            Comp::App(Box::new(rc_thunks(f, sigs)), args.iter().map(rv).collect())
        }
        other => other.clone(),
    }
}

fn rc_arm(p: &CorePat, body: &Comp, owned: &Set, borrowed: &Set, sigs: &Sigs) -> Comp {
    let fb = freev(body);
    let mut fields = Set::new();
    pat_vars(p, &mut fields);
    let live = by_name(fields.intersection(&fb).copied());
    let dead = by_name(owned.iter().filter(|v| !fb.contains(*v)).copied());
    let mut owned_b: Set = owned.intersection(&fb).copied().collect();
    owned_b.extend(live.iter().copied());
    let borrowed_b: Set = borrowed.intersection(&fb).copied().collect();
    let mut out = rc(body, &owned_b, &borrowed_b, sigs);
    for v in &dead {
        out = drop_(*v, out);
    }
    for v in live.iter().rev() {
        out = dup(*v, out);
    }
    out
}

// A borrow-position call arg is always a `Value::Var` (call sites bind every
// argument to a let before the call, so the caller's dead-variable analysis
// drops it when dead), and the caller retains ownership across the call, so it
// is not a consuming use and is skipped here.
fn borrow_mask(name: Sym, sigs: &Sigs) -> Option<&[bool]> {
    sigs.get(&name).map(Vec::as_slice)
}

fn leaf_counts(c: &Comp, out: &mut BTreeMap<Sym, usize>, sigs: &Sigs) {
    match c {
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v) => count_val(v, out),
        Comp::App(f, args) => {
            for x in freev(f) {
                *out.entry(x).or_default() += 1;
            }
            for a in args {
                count_val(a, out);
            }
        }
        Comp::Prim(_, a, b) => {
            count_val(a, out);
            count_val(b, out);
        }
        Comp::Call(g, args) => {
            let mask = borrow_mask(*g, sigs);
            for (i, a) in args.iter().enumerate() {
                if !mask.is_some_and(|m| m.get(i).copied().unwrap_or(false)) {
                    count_val(a, out);
                }
            }
        }
        Comp::Do(_, args) | Comp::StrBuiltin(_, args) => {
            for a in args {
                count_val(a, out);
            }
        }
        _ => {}
    }
}

fn count_val(v: &Value, out: &mut BTreeMap<Sym, usize>) {
    match v {
        Value::Var(x) => *out.entry(*x).or_default() += 1,
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().for_each(|f| count_val(f, out)),
        Value::Thunk(c) => {
            for x in freev(c) {
                *out.entry(x).or_default() += 1;
            }
        }
        _ => {}
    }
}

// Independent verifier: simulate the inserted ops as a linear token machine. Each
// owned variable starts with one token; dup adds one, drop and every consuming
// use remove one. A use must never drive a count below zero, every binding must
// reach zero before leaving scope, and the two sides of a branch must agree. A
// pass that under-dups, over-drops, or unbalances a branch fails here.
/// # Errors
/// Fails when refcount tokens are unbalanced.
pub fn balanced(core: &Core, sigs: &Sigs) -> Result<(), String> {
    for f in &core.fns {
        let mask = sigs.get(&f.name);
        let mut env: BTreeMap<Sym, i64> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let borrowed = mask.is_some_and(|m| m.get(i).copied().unwrap_or(false));
                (*p, i64::from(!borrowed))
            })
            .collect();
        sim(&f.body, &mut env, sigs).map_err(|e| format!("{}: {e}", f.name))?;
        for (v, n) in &env {
            if v != "_" && *n != 0 {
                return Err(format!("{}: {v} ends with {n} tokens", f.name));
            }
        }
    }
    Ok(())
}

fn use_val(v: &Value, env: &mut BTreeMap<Sym, i64>, sigs: &Sigs) -> Result<(), String> {
    let mut counts = BTreeMap::new();
    count_val(v, &mut counts);
    for (x, k) in counts {
        consume(x, i64::try_from(k).unwrap_or(i64::MAX), env)?;
    }
    verify_thunks(v, sigs)
}

// Closure bodies hide inside thunk values, so the top-level per-function walk
// never reaches them. Re-run the simulation on each thunk body: lambda params
// start owned (one token), captures start borrowed (zero, so a use without a
// preceding dup drives below zero and fails). Catches an under-dup'd capture.
fn verify_thunks(v: &Value, sigs: &Sigs) -> Result<(), String> {
    match v {
        Value::Thunk(c) => {
            let (params, body): (Set, &Comp) = match &**c {
                Comp::Lam(ps, b) => (ps.iter().copied().collect(), b),
                other => (Set::new(), other),
            };
            let mut env: BTreeMap<Sym, i64> = freev(body).into_iter().map(|x| (x, 0)).collect();
            for p in &params {
                env.insert(*p, 1);
            }
            sim(body, &mut env, sigs)?;
            for (x, n) in &env {
                if x != "_" && *n != 0 {
                    return Err(format!("thunk capture {x} ends with {n} tokens"));
                }
            }
            Ok(())
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            fs.iter().try_for_each(|f| verify_thunks(f, sigs))
        }
        _ => Ok(()),
    }
}

fn consume(x: Sym, k: i64, env: &mut BTreeMap<Sym, i64>) -> Result<(), String> {
    if x == "_" {
        return Ok(());
    }
    let e = env.entry(x).or_insert(0);
    *e -= k;
    if *e < 0 {
        return Err(format!("{x} consumed below zero"));
    }
    Ok(())
}

fn sim(c: &Comp, env: &mut BTreeMap<Sym, i64>, sigs: &Sigs) -> Result<(), String> {
    match c {
        Comp::Dup(Value::Var(x)) => {
            *env.entry(*x).or_insert(0) += 1;
            Ok(())
        }
        Comp::Drop(Value::Var(x)) => consume(*x, 1, env),
        Comp::Bind(m, x, n) => {
            sim(m, env, sigs)?;
            if *x != "_" {
                env.insert(*x, 1);
            }
            sim(n, env, sigs)
        }
        Comp::If(_, t, e) => {
            let mut et = env.clone();
            sim(t, &mut et, sigs)?;
            let mut ee = env.clone();
            sim(e, &mut ee, sigs)?;
            merge(&et, &ee, env)
        }
        Comp::Case(_, arms) => {
            let mut merged: Option<BTreeMap<Sym, i64>> = None;
            for (p, body) in arms {
                let mut ea = env.clone();
                let mut pv = Set::new();
                pat_vars(p, &mut pv);
                for v in &pv {
                    ea.insert(*v, 0);
                }
                sim(body, &mut ea, sigs)?;
                for v in &pv {
                    if ea.get(v).copied().unwrap_or(0) != 0 {
                        return Err(format!("field {v} leaks in arm"));
                    }
                    ea.remove(v);
                }
                merged = Some(match merged {
                    None => ea,
                    Some(prev) => {
                        let mut out = env.clone();
                        merge(&prev, &ea, &mut out)?;
                        out
                    }
                });
            }
            if let Some(m) = merged {
                *env = m;
            }
            Ok(())
        }
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::ReuseToken(v) => use_val(v, env, sigs),
        Comp::App(f, args) => {
            for x in freev(f) {
                consume(x, 1, env)?;
            }
            for a in args {
                use_val(a, env, sigs)?;
            }
            Ok(())
        }
        Comp::Prim(_, a, b) => {
            use_val(a, env, sigs)?;
            use_val(b, env, sigs)
        }
        Comp::Call(g, args) => {
            let mask = borrow_mask(*g, sigs);
            for (i, a) in args.iter().enumerate() {
                if !mask.is_some_and(|m| m.get(i).copied().unwrap_or(false)) {
                    use_val(a, env, sigs)?;
                }
            }
            Ok(())
        }
        Comp::Do(_, args) | Comp::StrBuiltin(_, args) => {
            for a in args {
                use_val(a, env, sigs)?;
            }
            Ok(())
        }
        Comp::Reuse(t, v) => {
            use_val(t, env, sigs)?;
            use_val(v, env, sigs)
        }
        Comp::Mask(_, b) => sim(b, env, sigs),
        Comp::Lam(..)
        | Comp::ReadInt
        | Comp::ReadLine
        | Comp::PrintNl
        | Comp::Rand
        | Comp::Handle { .. }
        | Comp::Dup(_)
        | Comp::Drop(_) => Ok(()),
    }
}

// FP^2 static check (Lorenzen/Leijen/Swierstra, ICFP 2023). The three properties
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
        .filter(|d| d.fip != Fip::No)
        .map(|d| (d.name.clone().into(), d.fip))
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
        fip_comp(&f.body, want, f.name.as_str(), fips, users)?;
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
    }
    Ok(())
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
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::ReuseToken(v) => occ(v),
        Comp::Reuse(t, v) => occ(t) + occ(v),
        Comp::Prim(_, a, b) => occ(a) + occ(b),
        Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) => {
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
        Comp::ReadInt | Comp::ReadLine | Comp::PrintNl | Comp::Rand => 0,
    }
}

fn fip_comp(
    c: &Comp,
    want: Fip,
    fname: &str,
    fips: &Fips,
    users: &BTreeSet<Sym>,
) -> Result<(), String> {
    let recur = |c: &Comp| fip_comp(c, want, fname, fips, users);
    let val = |v: &Value| fip_value(v, want, fname, fips, users);
    match c {
        Comp::Reuse(_, v) => fip_value_under_reuse(v, want, fname, fips, users),
        Comp::Call(g, args) => {
            if users.contains(g) {
                // `fbip` may call either discipline; `fip` may call only `fip`,
                // because an `fbip` callee is allowed unbounded stack and would
                // break the caller's bounded-stack guarantee.
                let ok = match want {
                    Fip::Fip => matches!(fips.get(g), Some(Fip::Fip)),
                    Fip::Fbip | Fip::No => matches!(fips.get(g), Some(Fip::Fbip | Fip::Fip)),
                };
                if !ok {
                    return Err(match want {
                        Fip::Fip => format!(
                            "a `fip` function may only call `fip` functions (bounded stack), but `{fname}` calls `{g}`"
                        ),
                        Fip::Fbip | Fip::No => format!(
                            "a `fbip` function may only call `fip`/`fbip` functions, but `{fname}` calls unannotated `{g}`"
                        ),
                    });
                }
            } else if !alloc_free_prim(g.as_str()) {
                return Err(format!(
                    "a `{}` function may only call allocation-free primitives, but `{fname}` calls `{g}`",
                    kw(want)
                ));
            }
            args.iter().try_for_each(val)
        }
        Comp::Bind(m, _, n) => {
            recur(m)?;
            recur(n)
        }
        Comp::If(_, t, e) => {
            recur(t)?;
            recur(e)
        }
        Comp::Case(_, arms) => arms.iter().try_for_each(|(_, b)| recur(b)),
        Comp::Lam(_, b) | Comp::Mask(_, b) => recur(b),
        Comp::App(fbody, args) => {
            recur(fbody)?;
            args.iter().try_for_each(val)
        }
        Comp::Prim(_, a, b) => {
            val(a)?;
            val(b)
        }
        Comp::Return(v)
        | Comp::Force(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Drop(v)
        | Comp::ReuseToken(v) => val(v),
        Comp::Do(_, args) | Comp::StrBuiltin(_, args) => args.iter().try_for_each(val),
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
        Comp::Dup(_) | Comp::ReadInt | Comp::ReadLine | Comp::PrintNl | Comp::Rand => Ok(()),
    }
}

// A value in any position other than directly under a reuse token: a bare
// constructor or tuple here is a fresh allocation and fails the check. Thunks
// carry suspended computations, so descend into them with the global maps so a
// closure body's calls resolve like any other.
fn fip_value(
    v: &Value,
    want: Fip,
    fname: &str,
    fips: &Fips,
    users: &BTreeSet<Sym>,
) -> Result<(), String> {
    match v {
        Value::Ctor(name, ..) => Err(alloc_err(want, fname, name.as_str())),
        Value::Tuple(_) => Err(alloc_err(want, fname, "tuple")),
        Value::Thunk(c) => fip_comp(c, want, fname, fips, users),
        _ => Ok(()),
    }
}

// The constructor argument of a `Comp::Reuse`: the head reuses a dropped cell,
// so it is allocation-free, but its fields may still hide a fresh allocation.
fn fip_value_under_reuse(
    v: &Value,
    want: Fip,
    fname: &str,
    fips: &Fips,
    users: &BTreeSet<Sym>,
) -> Result<(), String> {
    match v {
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs
            .iter()
            .try_for_each(|f| fip_value(f, want, fname, fips, users)),
        other => fip_value(other, want, fname, fips, users),
    }
}

fn alloc_err(want: Fip, fname: &str, ctor: &str) -> String {
    format!(
        "function `{fname}` is marked `{}` but allocates a fresh `{ctor}` (no reuse token available)",
        kw(want)
    )
}

const fn kw(f: Fip) -> &'static str {
    match f {
        Fip::Fip => "fip",
        Fip::Fbip | Fip::No => "fbip",
    }
}

fn merge(
    a: &BTreeMap<Sym, i64>,
    b: &BTreeMap<Sym, i64>,
    out: &mut BTreeMap<Sym, i64>,
) -> Result<(), String> {
    let keys: Set = a.keys().chain(b.keys()).copied().collect();
    for k in keys {
        let (va, vb) = (
            a.get(&k).copied().unwrap_or(0),
            b.get(&k).copied().unwrap_or(0),
        );
        if va != vb {
            return Err(format!("branch disagreement on {k}: {va} vs {vb}"));
        }
        out.insert(k, va);
    }
    Ok(())
}

// Direct coverage of `bounded_stack`'s rules. The strict no-`Dup` linearity pass
// rejects every recursive heap function before this check is reached end-to-end,
// so the mixed-mode and mutual-plus-TRMC paths can only be exercised on
// hand-built core (the linearity and allocation passes are bypassed here, which
// is exactly what isolates the stack rule).
#[cfg(test)]
mod tests {
    use super::super::cbpv::CoreOp;
    use super::*;

    fn users(names: &[&str]) -> BTreeSet<Sym> {
        names.iter().map(|n| Sym::from(*n)).collect()
    }

    fn one(name: &str, arity: usize, body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            params: (0..arity)
                .map(|i| Sym::from(format!("p{i}").as_str()))
                .collect(),
            body,
        }
    }

    // `f(x) to t; <k>` — the recursive-call-feeding-continuation shape.
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
            body,
        }
    }

    fn fip_of(f: &CoreFn) -> Fips {
        std::iter::once((f.name, Fip::Fip)).collect()
    }

    fn use_var_twice(x: &str) -> Comp {
        Comp::Prim(CoreOp::Add, Value::Var(x.into()), Value::Var(x.into()))
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
