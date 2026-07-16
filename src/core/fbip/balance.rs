use std::collections::BTreeMap;

use crate::sym::Sym;

use super::super::cbpv::{Comp, Core, Value};
use super::super::fv::{comp as freev, pat_vars};
#[cfg(debug_assertions)]
use super::super::traverse::Visit;
use super::{borrow_mask, borrowed_at, borrowed_call_vars, count_val, Set, Sigs};

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
        let external: Set = f
            .params
            .iter()
            .enumerate()
            .filter(|(index, _)| borrowed_at(mask, *index))
            .map(|(_, param)| *param)
            .collect();
        sim(&f.body, &mut env, sigs, &external).map_err(|e| format!("{}: {e}", f.name))?;
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
            let free = freev(body);
            let external: Set = free.difference(&params).copied().collect();
            let mut env: BTreeMap<Sym, i64> = free.into_iter().map(|x| (x, 0)).collect();
            for p in &params {
                env.insert(*p, 1);
            }
            sim(body, &mut env, sigs, &external)?;
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

fn sim(c: &Comp, env: &mut BTreeMap<Sym, i64>, sigs: &Sigs, external: &Set) -> Result<(), String> {
    match c {
        Comp::Dup(Value::Var(x)) => {
            *env.entry(*x).or_insert(0) += 1;
            Ok(())
        }
        Comp::Drop(Value::Var(x)) => consume(*x, 1, env),
        Comp::Bind(m, x, n) => {
            sim(m, env, sigs, external)?;
            if x.as_str() != "_" {
                env.insert(*x, 1);
            }
            let mut nested_external = external.clone();
            nested_external.remove(x);
            sim(n, env, sigs, &nested_external)
        }
        Comp::If(_, t, e) => {
            let mut et = env.clone();
            sim(t, &mut et, sigs, external)?;
            let mut ee = env.clone();
            sim(e, &mut ee, sigs, external)?;
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
                let mut arm_external = external.clone();
                for var in &pv {
                    arm_external.remove(var);
                }
                sim(body, &mut ea, sigs, &arm_external)?;
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
            let mut body_external = external.clone();
            body_external.remove(token);
            sim(body, env, sigs, &body_external)
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
            let borrowed = borrowed_call_vars(*g, args, sigs)?;
            let mut consumed = BTreeMap::new();
            for (index, arg) in args.iter().enumerate() {
                if !borrowed_at(mask, index) {
                    count_val(arg, &mut consumed);
                }
            }
            for var in borrowed {
                let live = env.get(&var).copied().unwrap_or(0);
                let spent =
                    i64::try_from(consumed.get(&var).copied().unwrap_or(0)).unwrap_or(i64::MAX);
                if !external.contains(&var) && live - spent < 1 {
                    return Err(format!(
                        "borrowed call argument {var} is not live through call to {g}"
                    ));
                }
            }
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
        // Post-lowering (arena) node, unreachable in this pre-lowering balance
        // check; kept total by consuming the cell and constructor values.
        Comp::InitAt(cell, v) => {
            use_val(cell, env, sigs)?;
            use_val(v, env, sigs)
        }
        Comp::Mask(_, b) => sim(b, env, sigs, external),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::cbpv::CoreFn;

    #[test]
    fn rejects_a_drop_before_the_last_borrowed_call() {
        let retained = Sym::new("retained");
        let observe = Sym::new("observe");
        let body = Comp::Bind(
            Box::new(Comp::Drop(Value::Var(retained))),
            Sym::new("_"),
            Box::new(Comp::Call(observe, vec![Value::Var(retained)])),
        );
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller"),
                params: vec![retained],
                body,
                dict_arity: 0,
            }],
        };
        let sigs = std::iter::once((observe, vec![true])).collect();

        let error = balanced(&core, &sigs).expect_err("pre-call drop must end the loan");
        assert!(error.contains("borrowed call argument retained is not live"));
    }

    #[test]
    fn a_shadowing_binder_does_not_inherit_an_external_loan() {
        let borrowed = Sym::new("borrowed");
        let observe = Sym::new("observe");
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Unit)),
            borrowed,
            Box::new(Comp::Bind(
                Box::new(Comp::Drop(Value::Var(borrowed))),
                Sym::new("_"),
                Box::new(Comp::Call(observe, vec![Value::Var(borrowed)])),
            )),
        );
        let core = Core {
            fns: vec![CoreFn {
                name: Sym::new("caller"),
                params: vec![borrowed],
                body,
                dict_arity: 0,
            }],
        };
        let sigs = [(Sym::new("caller"), vec![true]), (observe, vec![true])]
            .into_iter()
            .collect();

        let error = balanced(&core, &sigs).expect_err("inner binder owns its own loan");
        assert!(error.contains("borrowed call argument borrowed is not live"));
    }
}
