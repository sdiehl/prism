use std::collections::BTreeMap;

use crate::sym::Sym;

use super::super::cbpv::{Comp, Core, Value};
use super::super::fv::{comp as freev, pat_vars};
#[cfg(debug_assertions)]
use super::super::traverse::Visit;
use super::{borrow_mask, borrowed_at, count_val, Set, Sigs};

// Independent verifier: simulate the inserted ops as a linear token machine. Each
// owned variable starts with one token; dup adds one, drop and every consuming
// use remove one. A use must never drive a count below zero, every binding must
// reach zero before leaving scope, and the two sides of a branch must agree. A
// pass that under-dups, over-drops, or unbalances a branch fails here.
/// # Errors
/// Fails when refcount tokens are unbalanced.
pub fn balanced(core: &Core, sigs: &Sigs) -> Result<(), String> {
    // This runs only on effect-lowered Core (the compiled pipeline). `sim` treats
    // a stray `Handle`/`Do`/`Mask` as a no-op, which would silently mask an RC
    // imbalance in its clauses, so assert lowering really ran first rather than
    // leave the precondition to a comment.
    // `effect_free` is itself `#[cfg(debug_assertions)]`, and `debug_assert!` still
    // compiles its body in release; gate the whole assertion so the helper is never
    // referenced outside debug builds.
    #[cfg(debug_assertions)]
    debug_assert!(
        core.fns.iter().all(|f| effect_free(&f.body)),
        "balanced: effect nodes survived to the reuse linearity check; lower_effects must run first"
    );
    for f in &core.fns {
        let mask = sigs.get(&f.name).map(Vec::as_slice);
        let mut env: BTreeMap<Sym, i64> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| (*p, i64::from(!borrowed_at(mask, i))))
            .collect();
        sim(&f.body, &mut env, sigs).map_err(|e| format!("{}: {e}", f.name))?;
        for (v, n) in &env {
            if v.as_str() != "_" && *n != 0 {
                return Err(format!("{}: {v} ends with {n} tokens", f.name));
            }
        }
    }
    Ok(())
}

// Whether `c` is free of the effect nodes that effect lowering removes. Used only
// by the debug-mode precondition of `balanced`.
#[cfg(debug_assertions)]
fn effect_free(c: &Comp) -> bool {
    struct Scan(bool);
    impl Visit for Scan {
        fn visit_comp(&mut self, c: &Comp) {
            if matches!(c, Comp::Handle { .. } | Comp::Do(..) | Comp::Mask(..)) {
                self.0 = false;
            }
            self.descend_comp(c);
        }
    }
    let mut s = Scan(true);
    s.visit_comp(c);
    s.0
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
                if x.as_str() != "_" && *n != 0 {
                    return Err(format!("thunk capture {x} ends with {n} tokens"));
                }
            }
            Ok(())
        }
        Value::Ctor(_, _, fs) | Value::Tuple(fs) | Value::UnboxedTuple(fs) => {
            fs.iter().try_for_each(|f| verify_thunks(f, sigs))
        }
        Value::UnboxedRecord(fs) => fs.iter().try_for_each(|(_, f)| verify_thunks(f, sigs)),
        _ => Ok(()),
    }
}

fn consume(x: Sym, k: i64, env: &mut BTreeMap<Sym, i64>) -> Result<(), String> {
    if x.as_str() == "_" {
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
            if x.as_str() != "_" {
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
        | Comp::Error(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Neg(_, v)
        | Comp::UnboxedProject(v, _)
        | Comp::RefNew(v)
        | Comp::RefGet(v) => use_val(v, env, sigs),
        Comp::RefSet(c, v) => {
            use_val(c, env, sigs)?;
            use_val(v, env, sigs)
        }
        // Free the dropped cell, then bind its token (one credit) over the body;
        // a `Reuse` inside the body spends it, so the body brings the token back
        // to zero on every path (enforced by the branch-merge and end-of-scope
        // checks), exactly as the threaded `bind (reuse_token ..)` form did.
        Comp::WithReuse { token, freed, body } => {
            use_val(freed, env, sigs)?;
            env.insert(*token, 1);
            sim(body, env, sigs)
        }
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
                if !borrowed_at(mask, i) {
                    use_val(a, env, sigs)?;
                }
            }
            Ok(())
        }
        Comp::Do(_, args) | Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
            for a in args {
                use_val(a, env, sigs)?;
            }
            Ok(())
        }
        Comp::Reuse(tok, v) => {
            consume(*tok, 1, env)?;
            use_val(v, env, sigs)
        }
        Comp::Mask(_, b) => sim(b, env, sigs),
        Comp::Lam(..) | Comp::Handle { .. } | Comp::Dup(_) | Comp::Drop(_) => Ok(()),
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
