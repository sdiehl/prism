//! Bounded inliner (late pass).
//!
//! Inlines a non-recursive top-level function at its call site when doing so
//! cannot blow up code size. It inlines only a function called exactly once (a
//! single `Call` head, never referenced first-class), so its body
//! moves rather than duplicates: no size growth, and no question of duplicating a
//! side-effecting computation. The callee's binders are alpha-renamed to fresh
//! names so nothing captures or collides at the call site; its free variables are
//! top-level function names (Core Lint's invariant), in scope everywhere.
//!
//! It runs after effect lowering (a late pass) so it cannot disturb the var/State
//! fusion, on the lowered, pre-reference-counting core (so no rc nodes appear).
//! Freshened binders are named `%i{n}` from a per-compilation counter threaded
//! through the whole sweep, assigned in deterministic traversal order, so the
//! output is byte-identical across runs (the `%` prefix cannot collide with a
//! source identifier). This determinism is what lets the pass run at O1.

use std::collections::{BTreeMap, BTreeSet};

use super::super::cbpv::{calls_in, Comp, Core, CoreFn, Value};
use super::super::fv;
use super::super::traverse::Rewrite;
use super::rename;
use crate::names::{self, ENTRY_POINT};
use crate::sym::Sym;

/// Inline single-call-site non-recursive functions, returning the result and the
/// number of call sites inlined.
pub(crate) fn inline_counted(core: &Core) -> (Core, u64) {
    let names: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();

    // Per-function call-site count (Call heads) and whether it is ever used
    // first-class (as a value, e.g. a dictionary field), across all bodies.
    let mut call_count: BTreeMap<Sym, usize> = BTreeMap::new();
    let mut first_class: BTreeSet<Sym> = BTreeSet::new();
    for f in &core.fns {
        let mut heads = Vec::new();
        calls_in(&f.body, &mut heads);
        for h in heads {
            *call_count.entry(h).or_default() += 1;
        }
        for v in fv::comp(&f.body) {
            if names.contains(&v) {
                first_class.insert(v);
            }
        }
    }

    let recursive = recursive_set(core, &names);
    let entry = Sym::new(ENTRY_POINT);
    let inlinable: BTreeSet<Sym> = names
        .iter()
        .copied()
        .filter(|n| {
            *n != entry
                && !recursive.contains(n)
                && !first_class.contains(n)
                && call_count.get(n).copied() == Some(1)
        })
        .collect();
    if inlinable.is_empty() {
        return (core.clone(), 0);
    }

    let mut inl = Inliner {
        fns: core.fns.iter().map(|f| (f.name, f.clone())).collect(),
        inlinable,
        ticks: 0,
        counter: 0,
    };
    let fns = core
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name,
            params: f.params.clone(),
            dict_arity: f.dict_arity,
            body: inl.comp(&f.body, &()),
        })
        .collect();
    (Core { fns }, inl.ticks)
}

// The functions that (transitively) call themselves. Never inlined: it would not
// terminate and would reshape the spines `tailrec` and native codegen expect.
fn recursive_set(core: &Core, names: &BTreeSet<Sym>) -> BTreeSet<Sym> {
    let mut edges: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
    for f in &core.fns {
        let mut heads = Vec::new();
        calls_in(&f.body, &mut heads);
        edges.insert(
            f.name,
            heads.into_iter().filter(|h| names.contains(h)).collect(),
        );
    }
    let mut rec = BTreeSet::new();
    for &start in names {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<Sym> = edges.get(&start).into_iter().flatten().copied().collect();
        while let Some(n) = stack.pop() {
            if n == start {
                rec.insert(start);
                break;
            }
            if seen.insert(n) {
                stack.extend(edges.get(&n).into_iter().flatten().copied());
            }
        }
    }
    rec
}

struct Inliner {
    fns: BTreeMap<Sym, CoreFn>,
    inlinable: BTreeSet<Sym>,
    ticks: u64,
    // Per-compilation freshening counter, threaded across every inlined site so
    // each freshened binder gets a distinct deterministic `%i{n}` name.
    counter: u32,
}

impl Rewrite for Inliner {
    type Ctx = ();

    fn comp(&mut self, c: &Comp, cx: &()) -> Comp {
        if let Comp::Call(name, args) = c {
            if self.inlinable.contains(name) {
                let callee = self.fns[name].clone();
                if callee.params.len() == args.len() {
                    let args2: Vec<Value> = args.iter().map(|a| self.value(a, cx)).collect();
                    self.ticks += 1;
                    let spliced = inline_call(&callee, &args2, &mut self.counter);
                    // Recurse into the spliced body: a single-call-site callee
                    // it in turn calls is still single-site (its one site just
                    // moved here), so one sweep inlines the whole chain.
                    return self.comp(&spliced, cx);
                }
            }
        }
        self.descend_comp(c, cx)
    }
}

// The callee body with every binder freshened and its parameters bound to the
// argument values: `let p0' = a0 in ... let pk' = ak in <freshened body>`. The
// trivial-let copy-prop and dead-let in the simplifier then erase the parameter
// lets (arguments are ANF values). `counter` is the caller's per-compilation
// freshening counter, threaded so every binder across every site gets a distinct
// deterministic name.
fn inline_call(callee: &CoreFn, args: &[Value], counter: &mut u32) -> Comp {
    let mut ren: BTreeMap<Sym, Sym> = BTreeMap::new();
    for p in &callee.params {
        ren.insert(*p, rename::next(counter, names::FRESH_INLINE));
    }
    let mut out = rename::freshen_with(&callee.body, &ren, counter, names::FRESH_INLINE);
    for i in (0..callee.params.len()).rev() {
        let p = ren[&callee.params[i]];
        out = Comp::Bind(Box::new(Comp::Return(args[i].clone())), p, Box::new(out));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::inline_counted;
    use crate::core::cbpv::{Comp, Core, CoreFn, Value};
    use crate::sym::Sym;

    fn s(n: &str) -> Sym {
        Sym::new(n)
    }

    // A wrapper called exactly once is inlined and its parameter let-bound to the
    // argument; the wrapper call is gone, replaced by the (freshened) forwarded
    // call. `main` calls `wrap(x)`; `wrap(a) = g(a)`.
    #[test]
    fn single_call_site_wrapper_is_inlined() {
        let core = Core {
            fns: vec![
                CoreFn {
                    name: s("main"),
                    params: vec![s("x")],
                    dict_arity: 0,
                    body: Comp::Call(s("wrap"), vec![Value::Var(s("x"))]),
                },
                CoreFn {
                    name: s("wrap"),
                    params: vec![s("a")],
                    dict_arity: 0,
                    body: Comp::Call(s("g"), vec![Value::Var(s("a"))]),
                },
            ],
        };
        let (out, ticks) = inline_counted(&core);
        assert_eq!(ticks, 1);
        let main = &out.fns.iter().find(|f| f.name == s("main")).unwrap().body;
        // main no longer calls wrap; the body is now `let a' = x in g(a')`.
        match main {
            Comp::Bind(rhs, _, body) => {
                assert!(matches!(rhs.as_ref(), Comp::Return(Value::Var(v)) if *v == s("x")));
                assert!(matches!(body.as_ref(), Comp::Call(g, _) if *g == s("g")));
            }
            other => panic!("expected inlined `let a = x in g(a)`, got {other:?}"),
        }
    }

    // A recursive function is never inlined, even at a lone call site.
    #[test]
    fn recursive_function_is_not_inlined() {
        let core = Core {
            fns: vec![CoreFn {
                name: s("loop"),
                params: vec![],
                dict_arity: 0,
                body: Comp::Call(s("loop"), vec![]),
            }],
        };
        let (_, ticks) = inline_counted(&core);
        assert_eq!(ticks, 0);
    }
}
