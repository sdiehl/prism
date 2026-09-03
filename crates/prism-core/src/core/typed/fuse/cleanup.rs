//! Substitution, copy propagation, and dead-binding cleanup.

use super::{
    free_comp_vars, is_stream_comb, substitute_terms, union_effects, BTreeMap, CompSig, Cx,
    Rewrite, Sym, TypedComp, TypedCompKind, TypedValue, FRESH_FUSE,
};

pub(super) fn subst(c: &TypedComp, sub: &BTreeMap<Sym, TypedValue>, cx: &mut Cx) -> TypedComp {
    substitute_terms(c, sub, &mut cx.fresh, FRESH_FUSE)
}

// Copy-propagate every trivial `Bind(Return v, x, k)` alias throughout `c`
// (recursively, under every binder), which elaboration's per-step `return x to
// t` sequencing leaves behind. Unlike `normalize` (head-only), this descends
// everywhere, so a self-call's arguments and a transformer's arms read
// structurally.
pub(super) fn copy_prop(c: &TypedComp, cx: &mut Cx) -> TypedComp {
    CopyProp {
        counter: &mut cx.fresh,
    }
    .comp(c, &())
}

struct CopyProp<'a> {
    counter: &'a mut u32,
}

impl Rewrite for CopyProp<'_> {
    type Ctx = ();
    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        match c.kind() {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, &());
                // Inline a trivial value alias.
                if let TypedCompKind::Return(value) = first.kind() {
                    let mut sub = BTreeMap::new();
                    sub.insert(binder.name(), value.clone());
                    let rest = substitute_terms(rest, &sub, self.counter, FRESH_FUSE);
                    return self.comp(&rest, &());
                }
                // Re-associate `Bind(Bind(ia, iy, ib), x, k)` to
                // `Bind(ia, iy, Bind(ib, x, k))` (monad associativity), so the
                // whole computation is one flat bind spine and the driver reads
                // each `Call`/`Prim` at the spine. The new inner bind takes the
                // verified sig-construction rule (the continuation's result
                // over the children's row union).
                if let TypedCompKind::Bind(inner_first, inner_binder, inner_rest) = first.kind() {
                    let inner = TypedComp::new(
                        CompSig::new(
                            rest.sig().result().clone(),
                            union_effects(inner_rest.sig().effects(), rest.sig().effects()),
                        ),
                        TypedCompKind::Bind(inner_rest.clone(), binder.clone(), rest.clone()),
                    );
                    let reassoc = TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Bind(
                            inner_first.clone(),
                            inner_binder.clone(),
                            Box::new(inner),
                        ),
                    );
                    return self.comp(&reassoc, &());
                }
                TypedComp::new(
                    c.sig().clone(),
                    TypedCompKind::Bind(
                        Box::new(first),
                        binder.clone(),
                        Box::new(self.comp(rest, &())),
                    ),
                )
            }
            _ => self.descend_comp(c, &()),
        }
    }
}

// Eliminate dead pure let-bindings from `c`: a `Bind(a, x, k)` whose bound
// variable `x` is unused in the rewritten continuation and whose `a` is
// effect-free is dropped. Applied only to a function that fused, to sweep away
// the upstream pipeline the redirected consumer no longer reads. Bottom-up, so
// a binding that becomes dead only after an inner one is removed is caught in
// the same pass.
pub(super) fn dead_let_elim(c: &TypedComp, cx: &mut Cx) -> TypedComp {
    Dce { cx }.comp(c, &())
}

struct Dce<'a> {
    cx: &'a mut Cx,
}

impl Rewrite for Dce<'_> {
    type Ctx = ();
    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        match c.kind() {
            TypedCompKind::Bind(first, binder, rest) => {
                let first = self.comp(first, &());
                let rest = self.comp(rest, &());
                if !free_comp_vars(&rest).contains(&binder.name()) && self.removable(&first) {
                    rest
                } else {
                    TypedComp::new(
                        c.sig().clone(),
                        TypedCompKind::Bind(Box::new(first), binder.clone(), Box::new(rest)),
                    )
                }
            }
            _ => self.descend_comp(c, &()),
        }
    }
}

impl Dce<'_> {
    // A dead bound computation is removed only when it is obviously total,
    // never merely pure: dropping a diverging (even pure) computation would
    // turn a non-terminating program terminating, an observable change the
    // determinism contract forbids. The dead upstream pipeline is a bind-chain
    // of `Return(_)` and lazy stream-combinator calls, every step `O(1)` and
    // total; a chain of total steps is total.
    fn removable(&self, a: &TypedComp) -> bool {
        match a.kind() {
            TypedCompKind::Return(_) => true,
            TypedCompKind::Call { callee, .. } => is_stream_comb(*callee, self.cx),
            TypedCompKind::Bind(first, _, rest) => self.removable(first) && self.removable(rest),
            _ => false,
        }
    }
}
