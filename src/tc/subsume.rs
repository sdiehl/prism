use std::collections::BTreeSet;

use super::{Entry, Tc, TcErr};
use crate::coeffect::{CoeffectFact, CoeffectRow};
use crate::names::{self, ScopedEscape};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label, Type};

// Multiplicity as a level: `@ once` is 1 (restrictive), the default `@ many` is
// 0. A value fits a context iff its level does not exceed the context's.
fn mult_level(row: &CoeffectRow) -> u8 {
    u8::from(matches!(row.multiplicity(), Some(CoeffectFact::Once)))
}

// A value of multiplicity `value` used in a context requiring `context`: the
// value may be no more restrictive than the context allows, so a `@ once` value
// (level 1) in a `@ many` context (level 0) is the one rejected pairing.
fn check_mult(value: u8, context: u8) -> Result<(), TcErr> {
    if value > context {
        // `Keep` so this precise reason survives the caller's coarse
        // expected/got rewrite (a bare `Fail` would be replaced by it).
        Err(TcErr::Keep(
            "a closure marked `@ once` cannot be passed where it may be used more than once".into(),
        ))
    } else {
        Ok(())
    }
}

impl Tc<'_> {
    pub(super) fn subtype(&mut self, a: &Type, b: &Type) -> Result<(), TcErr> {
        match (a, b) {
            (Type::Var(x), Type::Var(y)) if x == y => Ok(()),
            (Type::Unit, Type::Unit)
            | (Type::Int, Type::Int)
            | (Type::Char, Type::Char)
            | (Type::Bool, Type::Bool)
            | (Type::Float, Type::Float)
            | (Type::I64, Type::I64)
            | (Type::U64, Type::U64)
            | (Type::Str, Type::Str) => Ok(()),
            (Type::Exist(x), Type::Exist(y)) if x == y => Ok(()),
            // Boxed and unboxed tuples unify structurally, each only with its own
            // kind (the OR keeps them distinct: a boxed tuple never unifies with an
            // unboxed one).
            (Type::Tuple(xs), Type::Tuple(ys))
            | (Type::UnboxedTuple(xs), Type::UnboxedTuple(ys))
                if xs.len() == ys.len() =>
            {
                for (x, y) in xs.iter().zip(ys) {
                    let x = self.apply(x);
                    let y = self.apply(y);
                    self.subtype(&x, &y)?;
                }
                Ok(())
            }
            // An unboxed record additionally requires the same fields in the same
            // order (field names are part of the type's identity).
            (Type::UnboxedRecord(xs), Type::UnboxedRecord(ys))
                if xs.len() == ys.len() && xs.iter().zip(ys).all(|((a, _), (b, _))| a == b) =>
            {
                for ((_, x), (_, y)) in xs.iter().zip(ys) {
                    let x = self.apply(x);
                    let y = self.apply(y);
                    self.subtype(&x, &y)?;
                }
                Ok(())
            }
            // Constructor arguments are matched covariantly (each `x <: y`), with no
            // separate invariant rule for mutable containers like `Array`. That is
            // sound only because every value is copy-on-write: `array_set` mutates in
            // place only when the cell is uniquely owned (rc 1) and copies otherwise,
            // so two live aliases can never share a cell across a mutation. Without
            // that, covariance on a mutable element type would be a classic hole (write
            // through a widened view, read the change back through the original). With
            // it, no such observation exists, so covariance is safe. The value-
            // semantics guarantee is pinned by `tests/cases/run/array_value_semantics.pr`.
            (Type::Con(n, xs), Type::Con(m, ys)) if n == m && xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    let x = self.apply(x);
                    let y = self.apply(y);
                    self.subtype(&x, &y)?;
                }
                Ok(())
            }
            // A nullable unifies with a nullable, covariantly on the element.
            (Type::OrNull(x), Type::OrNull(y)) => {
                let x = self.apply(x);
                let y = self.apply(y);
                self.subtype(&x, &y)
            }
            // Usage-annotated types check by their inner type plus a contravariant
            // multiplicity: a value's usage must be no more permissive than its
            // context permits. `@ many` (the default) fits a `@ once` slot, but a
            // `@ once` value used where more uses are allowed is rejected (the
            // delegation check: a once-closure cannot be handed to a many-context).
            (Type::Coeffect(a0, ra), Type::Coeffect(b0, rb)) => {
                let a = self.apply(a0);
                let b = self.apply(b0);
                self.subtype(&a, &b)?;
                check_mult(mult_level(ra), mult_level(rb))
            }
            (Type::Coeffect(a0, ra), _) => {
                let a = self.apply(a0);
                self.subtype(&a, b)?;
                check_mult(mult_level(ra), 0)
            }
            (_, Type::Coeffect(b0, _)) => {
                let b = self.apply(b0);
                self.subtype(a, &b)
            }
            // Two application spines unify head-to-head, argument-to-argument.
            (Type::App(h1, a1), Type::App(h2, a2)) => {
                let h1 = self.apply(h1);
                let h2 = self.apply(h2);
                self.subtype(&h1, &h2)?;
                let a1 = self.apply(a1);
                let a2 = self.apply(a2);
                self.subtype(&a1, &a2)
            }
            // Higher-kinded application versus a concrete constructor: peel the
            // last argument off the saturated side and match the (`* -> *`) head
            // against the partially-applied constructor. `f(a) ~ List(b)` gives
            // `f := List, a := b`; deeper spines recurse.
            (Type::App(h, a), Type::Con(m, ys)) if !ys.is_empty() => {
                let (init, last) = ys.split_at(ys.len() - 1);
                let h = self.apply(h);
                self.subtype(&h, &Type::Con(*m, init.to_vec()))?;
                let a = self.apply(a);
                let last = self.apply(&last[0]);
                self.subtype(&a, &last)
            }
            (Type::Con(m, ys), Type::App(h, a)) if !ys.is_empty() => {
                let (init, last) = ys.split_at(ys.len() - 1);
                let h = self.apply(h);
                self.subtype(&Type::Con(*m, init.to_vec()), &h)?;
                let a = self.apply(a);
                let last = self.apply(&last[0]);
                self.subtype(&last, &a)
            }
            (Type::Fun(a1, eff1, r1), Type::Fun(a2, eff2, r2)) if a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2) {
                    let x = self.apply(x);
                    let y = self.apply(y);
                    self.subtype(&y, &x)?;
                }
                let e1 = self.apply_row(eff1);
                let e2 = self.apply_row(eff2);
                // Effect rows are checked by scoped-label unification: the value's
                // row must be made equal to the expected one, so a narrower row
                // fits a wider context only by solving a row variable (its own
                // open latent tail, or the context's), never by silent widening.
                // A pure function still fits an effectful context because its
                // scheme quantifies that latent tail (`default_open_rows`), so the
                // fit is a most-general substitution rather than a subtyping step.
                self.unify_row(&e1, &e2)?;
                let r1 = self.apply(r1);
                let r2 = self.apply(r2);
                self.subtype(&r1, &r2)
            }
            (Type::Forall(n, a0), _) => {
                let m = self.fresh_id();
                self.ctx.push(Entry::Marker(m));
                let ex = self.push_ex();
                let a1 = a0.subst_var(*n, &Type::Exist(ex));
                self.subtype(&a1, b)?;
                self.drop_marker(m);
                Ok(())
            }
            (_, Type::Forall(n, b0)) => {
                // Skolemize with a fresh identity that still renders as `n`, so
                // two nested `forall a` cannot alias in the context.
                let sk = Sym::fresh_named(*n);
                let b1 = b0.subst_var(*n, &Type::Var(sk));
                self.ctx.push(Entry::Uni(sk));
                self.subtype(a, &b1)?;
                self.drop_uni(sk);
                Ok(())
            }
            (Type::RowForall(n, a0), _) => {
                let r = self.push_ex_row();
                let a1 = a0.subst_row_var(*n, &EffRow::Exist(r));
                self.subtype(&a1, b)
            }
            (_, Type::RowForall(n, b0)) => {
                let sk = Sym::fresh_named(*n);
                let b1 = b0.subst_row_var(*n, &EffRow::Var(sk));
                self.ctx.push(Entry::RowUni(sk));
                self.subtype(a, &b1)?;
                self.drop_row_uni(sk);
                Ok(())
            }
            // A `Row`-kinded argument position: unify the carried effect rows.
            (Type::Row(x), Type::Row(y)) => {
                let x = self.apply_row(x);
                let y = self.apply_row(y);
                self.unify_row(&x, &y)
            }
            // Dimension literals unify by equality only: no successor structure,
            // no arithmetic. A length clash names both dimensions plainly, the
            // whole point of the `Nat` kind over a nominal encoding. `Keep` so the
            // precise "expected N, got M" survives a caller's structural override
            // (which would otherwise bury the clash inside two whole shape types).
            (Type::Nat(x), Type::Nat(y)) => {
                if x == y {
                    Ok(())
                } else {
                    Err(TcErr::Keep(format!(
                        "length mismatch: expected length {y}, but got length {x}"
                    )))
                }
            }
            (Type::Exist(x), _) if !occurs_ex(*x, b) => self.inst_l(*x, b),
            (_, Type::Exist(x)) if !occurs_ex(*x, a) => self.inst_r(a, *x),
            (a, b) => Err(TcErr::Fail(format!(
                "type mismatch: {} is not compatible with {}",
                a.show(),
                b.show()
            ))),
        }
    }

    fn inst_l(&mut self, a: u32, b: &Type) -> Result<(), TcErr> {
        self.inst(a, b, true)
    }

    fn inst_r(&mut self, a: &Type, b: u32) -> Result<(), TcErr> {
        self.inst(b, a, false)
    }

    // InstL and InstR collapsed. `left` says the existential sits on the subtype
    // side. The rules mirror except under a binder (left keeps foralls rigid,
    // right opens them) and function arguments flip side.
    fn inst(&mut self, ex: u32, t: &Type, left: bool) -> Result<(), TcErr> {
        let t = self.apply(t);
        if t.is_mono() && self.well_formed_before(ex, &t) {
            self.solve(ex, t);
            return Ok(());
        }
        match t {
            Type::Exist(other) => {
                // Solve the younger existential (further right in the context)
                // to the older one, so a solution only references entries to its
                // left and survives later truncation at a marker. A live
                // existential is always in the context (`solve` only records
                // left-referencing solutions), so absence is a compiler bug, not
                // user-reachable.
                let oi = self
                    .index_ex(other)
                    .ok_or_else(|| TcErr::Ice(format!("inst: ^{other} escaped scope")))?;
                let ei = self
                    .index_ex(ex)
                    .ok_or_else(|| TcErr::Ice(format!("inst: ^{ex} escaped scope")))?;
                if oi > ei {
                    self.solve(other, Type::Exist(ex));
                } else {
                    self.solve(ex, Type::Exist(other));
                }
                Ok(())
            }
            Type::Fun(args, eff, r) => {
                let ret = self.fresh_id();
                let row = self.fresh_id();
                let arg_exs: Vec<u32> = args.iter().map(|_| self.fresh_id()).collect();
                self.articulate(ex, &arg_exs, row, ret)?;
                for (e, arg) in arg_exs.iter().zip(&args) {
                    let arg = self.apply(arg);
                    self.inst(*e, &arg, !left)?;
                }
                let eff2 = self.apply_row(&eff);
                self.unify_row(&EffRow::Exist(row), &eff2)?;
                let r2 = self.apply(&r);
                self.inst(ret, &r2, left)
            }
            Type::Con(name, args) => {
                let arg_exs: Vec<u32> = args.iter().map(|_| self.fresh_id()).collect();
                let con = Type::Con(name, arg_exs.iter().map(|e| Type::Exist(*e)).collect());
                self.splice_solved(ex, &arg_exs, con)?;
                for (e, arg) in arg_exs.iter().zip(&args) {
                    let arg = self.apply(arg);
                    self.inst(*e, &arg, left)?;
                }
                Ok(())
            }
            // Articulate `ex` into an application `?h(?a)` of fresh existentials,
            // each spliced to ex's left so the solution stays well-scoped, then
            // solve them against the head and argument.
            Type::App(h, a) => {
                let he = self.fresh_id();
                let ae = self.fresh_id();
                let app = Type::App(Box::new(Type::Exist(he)), Box::new(Type::Exist(ae)));
                self.splice_solved(ex, &[he, ae], app)?;
                let h = self.apply(&h);
                self.inst(he, &h, left)?;
                let a = self.apply(&a);
                self.inst(ae, &a, left)
            }
            Type::Tuple(elems) => {
                let elem_exs: Vec<u32> = elems.iter().map(|_| self.fresh_id()).collect();
                let tup = Type::Tuple(elem_exs.iter().map(|e| Type::Exist(*e)).collect());
                self.splice_solved(ex, &elem_exs, tup)?;
                for (e, elem) in elem_exs.iter().zip(&elems) {
                    let elem = self.apply(elem);
                    self.inst(*e, &elem, left)?;
                }
                Ok(())
            }
            // Unboxed products articulate exactly like their boxed counterparts:
            // splice one fresh existential per field to ex's left, then instantiate
            // each against the corresponding field type. Reachable only when a field
            // is itself a polytype (a monomorphic unboxed value takes the is_mono
            // fast path above).
            Type::UnboxedTuple(elems) => {
                let elem_exs: Vec<u32> = elems.iter().map(|_| self.fresh_id()).collect();
                let tup = Type::UnboxedTuple(elem_exs.iter().map(|e| Type::Exist(*e)).collect());
                self.splice_solved(ex, &elem_exs, tup)?;
                for (e, elem) in elem_exs.iter().zip(&elems) {
                    let elem = self.apply(elem);
                    self.inst(*e, &elem, left)?;
                }
                Ok(())
            }
            Type::UnboxedRecord(fields) => {
                let field_exs: Vec<u32> = fields.iter().map(|_| self.fresh_id()).collect();
                let rec = Type::UnboxedRecord(
                    fields
                        .iter()
                        .zip(&field_exs)
                        .map(|((n, _), e)| (*n, Type::Exist(*e)))
                        .collect(),
                );
                self.splice_solved(ex, &field_exs, rec)?;
                for (e, (_, t)) in field_exs.iter().zip(&fields) {
                    let t = self.apply(t);
                    self.inst(*e, &t, left)?;
                }
                Ok(())
            }
            // A nullable articulates through one fresh existential for its element.
            Type::OrNull(elem) => {
                let elem_ex = self.fresh_id();
                let nul = Type::OrNull(Box::new(Type::Exist(elem_ex)));
                self.splice_solved(ex, &[elem_ex], nul)?;
                let elem = self.apply(&elem);
                self.inst(elem_ex, &elem, left)
            }
            Type::Forall(n, body) if left => {
                let sk = Sym::fresh_named(n);
                let body = body.subst_var(n, &Type::Var(sk));
                self.ctx.push(Entry::Uni(sk));
                let body2 = self.apply(&body);
                self.inst(ex, &body2, true)?;
                self.drop_uni(sk);
                Ok(())
            }
            Type::Forall(n, body) => {
                let m = self.fresh_id();
                self.ctx.push(Entry::Marker(m));
                let e = self.push_ex();
                let body = body.subst_var(n, &Type::Exist(e));
                self.inst(ex, &body, false)?;
                self.drop_marker(m);
                Ok(())
            }
            Type::RowForall(n, body) if left => {
                let sk = Sym::fresh_named(n);
                let body = body.subst_row_var(n, &EffRow::Var(sk));
                self.ctx.push(Entry::RowUni(sk));
                let body2 = self.apply(&body);
                self.inst(ex, &body2, true)?;
                self.drop_row_uni(sk);
                Ok(())
            }
            Type::RowForall(n, body) => {
                let m = self.fresh_id();
                self.ctx.push(Entry::Marker(m));
                let r = self.push_ex_row();
                let body = body.subst_row_var(n, &EffRow::Exist(r));
                self.inst(ex, &body, false)?;
                self.drop_marker(m);
                Ok(())
            }
            other => Err(TcErr::Fail(format!(
                "cannot instantiate ?{ex} to {}",
                other.show()
            ))),
        }
    }

    // Scoped-label row unification. To unify `l | rest1` with
    // another row, rewrite that row to expose `l` at its head, then unify the
    // tails. A bare existential tail absorbs any missing label by extending.
    pub(super) fn unify_row(&mut self, a: &EffRow, b: &EffRow) -> Result<(), TcErr> {
        let a = dedup_row(&self.apply_row(a));
        let b = dedup_row(&self.apply_row(b));
        match (&a, &b) {
            (EffRow::Empty, EffRow::Empty) => Ok(()),
            (EffRow::Var(x), EffRow::Var(y)) if x == y => Ok(()),
            (EffRow::Exist(x), EffRow::Exist(y)) if x == y => Ok(()),
            // Two row existentials: solve the younger (further right in context)
            // to the older, so a solution only references entries to its left and
            // survives later truncation at a marker. Mirrors `inst`'s `Exist` arm.
            (EffRow::Exist(x), EffRow::Exist(y)) => {
                // Unlike the type context, the row context does not keep every
                // solution strictly left-referencing, so absence here is not
                // provably dead: keep it a defensive ICE rather than a panic.
                let xi = self
                    .index_ex_row(*x)
                    .ok_or_else(|| TcErr::Ice(format!("unify_row: ^{x} not in context")))?;
                let yi = self
                    .index_ex_row(*y)
                    .ok_or_else(|| TcErr::Ice(format!("unify_row: ^{y} not in context")))?;
                if xi > yi {
                    self.solve_row(*x, EffRow::Exist(*y))
                } else {
                    self.solve_row(*y, EffRow::Exist(*x))
                }
            }
            (EffRow::Exist(x), other) | (other, EffRow::Exist(x)) => {
                let mut fv = BTreeSet::new();
                other.free_exist_row(&mut fv);
                if fv.contains(x) {
                    return Err(TcErr::Fail("recursive effect row".into()));
                }
                self.solve_row(*x, other.clone())
            }
            (EffRow::Extend(l, rest1), _) => {
                let rest2 = self.rewrite_row(&b, l)?;
                let r1 = self.apply_row(rest1);
                let r2 = self.apply_row(&rest2);
                self.unify_row(&r1, &r2)
            }
            (EffRow::Empty | EffRow::Var(_), EffRow::Extend(l, _)) => {
                Err(TcErr::Fail(self.missing_effect(l)))
            }
            (a, b) => Err(TcErr::Fail(format!(
                "effect mismatch: {} is not compatible with {}",
                a.show(),
                b.show()
            ))),
        }
    }

    // Hoist `label` to the head of a row, returning the residual tail. Labels
    // match by effect name, then their instantiation arguments must unify, so
    // `Emit(Int)` never silently passes for `Emit(String)`. An existential
    // tail is solved to `label | fresh`, returning the fresh tail.
    fn rewrite_row(&mut self, row: &EffRow, label: &Label) -> Result<EffRow, TcErr> {
        match row {
            EffRow::Extend(l, rest) if l.name == label.name => {
                if l.args.len() != label.args.len() {
                    return Err(TcErr::Fail(format!(
                        "effect `{}` is not compatible with `{}`",
                        self.show_label(label),
                        self.show_label(l)
                    )));
                }
                for (x, y) in label.args.iter().zip(&l.args) {
                    let (lx, ly) = (label.clone(), l.clone());
                    self.equate(x, y).map_err(|e| {
                        e.or_fail(format!(
                            "effect instantiation mismatch: `{}` is not compatible with `{}`",
                            self.show_label(&lx),
                            self.show_label(&ly)
                        ))
                    })?;
                }
                Ok((**rest).clone())
            }
            EffRow::Extend(l, rest) => Ok(EffRow::Extend(
                l.clone(),
                Box::new(self.rewrite_row(rest, label)?),
            )),
            EffRow::Exist(alpha) => {
                // Open the existential tail to `label | beta`, splicing the fresh
                // `beta` in at `alpha`'s position so the solution references only
                // entries to its left (mirrors `splice_solved` for type vars);
                // appending `beta` would make `alpha` point right and strand it on
                // a later truncation.
                let beta = self.fresh_id();
                self.splice_solved_row(
                    *alpha,
                    &[beta],
                    EffRow::Extend(label.clone(), Box::new(EffRow::Exist(beta))),
                )?;
                Ok(EffRow::Exist(beta))
            }
            EffRow::Empty | EffRow::Var(_) => Err(TcErr::Fail(self.missing_effect(label))),
        }
    }

    // Add the effects of `eff` into the ambient obligation `cur_row` without
    // closing it. A closed tail is opened with a fresh existential first so the
    // accumulator stays extensible; `rewrite_row` matches an already-present
    // label rather than duplicating it; a flexible tail links into the ambient,
    // so a parameter's row variable propagates into the caller's row.
    pub(super) fn absorb_row(&mut self, eff: &EffRow) -> Result<(), TcErr> {
        let Some(scope) = &self.cur_row else {
            return Ok(());
        };
        let cur_row = scope.tail;
        let prefix = scope.prefix.clone();
        let eff = self.apply_row(eff);
        // A row that already refers to the ambient (a recursive self-call, or a
        // row already folded in) adds nothing and would only form a cycle.
        let mut fv = BTreeSet::new();
        eff.free_exist_row(&mut fv);
        if fv.contains(&cur_row) {
            return Ok(());
        }
        // Labels already in the ambient's fixed prefix need not be re-added,
        // but a parametric label's arguments must agree with the prefix's
        // instantiation before it is dropped: skipping by name alone let a
        // lambda body perform `Tag(String)` under an arrow annotated
        // `! {Tag(Int) | e}` unchecked (the named-function path errors through
        // `rewrite_row`'s argument equation; this is its prefix analogue).
        let eff = self.strip_prefix(&eff, &prefix)?;
        let opened = if matches!(eff.tail(), EffRow::Empty) {
            let fresh = self.push_ex_row();
            replace_tail(&eff, EffRow::Exist(fresh))
        } else {
            eff
        };
        let amb = EffRow::Exist(cur_row);
        self.unify_row(&opened, &amb)
    }

    // Drop the labels the fixed prefix already carries, equating a dropped
    // label's type arguments against the prefix's instantiation (first
    // name-match wins, mirroring `rewrite_row`). Labels not in the prefix pass
    // through for the tail unification in `absorb_row`.
    fn strip_prefix(&mut self, r: &EffRow, prefix: &[Label]) -> Result<EffRow, TcErr> {
        match r {
            EffRow::Extend(l, rest) => {
                let rest = self.strip_prefix(rest, prefix)?;
                let Some(p) = prefix.iter().find(|p| p.name == l.name) else {
                    return Ok(EffRow::Extend(l.clone(), Box::new(rest)));
                };
                for (x, y) in l.args.iter().zip(&p.args) {
                    let (lx, ly) = (l.clone(), p.clone());
                    self.equate(x, y).map_err(|e| {
                        e.or_fail(format!(
                            "effect instantiation mismatch: `{}` is not compatible with `{}`",
                            self.show_label(&lx),
                            self.show_label(&ly)
                        ))
                    })?;
                }
                Ok(rest)
            }
            other => Ok(other.clone()),
        }
    }

    // After a handler body accumulated into `body_row`, fold its row minus the
    // handled labels back into the enclosing ambient obligation, so a handled
    // effect vanishes from the surrounding function's row.
    pub(super) fn discharge_row(
        &mut self,
        body_row: u32,
        handled: &BTreeSet<Sym>,
    ) -> Result<(), TcErr> {
        let row = self.apply_row(&EffRow::Exist(body_row));
        let resid = without_labels(&row, handled);
        self.absorb_row(&resid)
    }

    // A row is missing `label`. When `label` is a scoped effect that leaked out
    // of its introducing scope (a named handler instance's private op, or a
    // `var` cell), name the escape route rather than the mangled label; the
    // unhandled-effect wall is exactly where such an escape is caught (see the
    // named-handler op-payload and `var`-through-call escape cases).
    fn missing_effect(&self, label: &Label) -> String {
        match names::parse_scoped_escape(label.name.as_str()) {
            Some(ScopedEscape::NamedInstance { effect, instance }) => format!(
                "handler instance `{instance}` escapes its scope: a value here still performs \
                 `{instance}`'s `{effect}` operation after its handler is gone"
            ),
            Some(ScopedEscape::Var { name }) => format!(
                "`var {name}` escapes its block: a value here still uses `{name}` after its scope ends"
            ),
            None => format!("missing effect `{}`", self.show_label(label)),
        }
    }

    pub(super) fn show_label(&self, l: &Label) -> String {
        Label {
            name: l.name,
            args: l.args.iter().map(|a| self.apply(a)).collect(),
        }
        .show()
    }

    // Equality. Existential vs monotype unifies directly through inst, so the
    // solution direction is deterministic (younger existential solves toward the
    // older, as in inst). Polytypes keep mutual subsumption, the only definition
    // of type equality under DK.
    pub(super) fn equate(&mut self, a: &Type, b: &Type) -> Result<(), TcErr> {
        let a = self.apply(a);
        let b = self.apply(b);
        match (&a, &b) {
            (Type::Exist(x), Type::Exist(y)) if x == y => return Ok(()),
            (Type::Exist(x), t) if t.is_mono() && !occurs_ex(*x, t) => {
                return self.inst_l(*x, t);
            }
            (t, Type::Exist(x)) if t.is_mono() && !occurs_ex(*x, t) => {
                return self.inst_r(t, *x);
            }
            _ => {}
        }
        self.subtype(&a, &b)?;
        let a = self.apply(&a);
        let b = self.apply(&b);
        self.subtype(&b, &a)
    }
}

fn occurs_ex(v: u32, t: &Type) -> bool {
    let mut s = BTreeSet::new();
    t.free_exist(&mut s);
    s.contains(&v)
}

// Rebuild a row's label chain over a new tail (replacing whatever tail it had).
fn replace_tail(r: &EffRow, t: EffRow) -> EffRow {
    match r {
        EffRow::Extend(l, rest) => EffRow::Extend(l.clone(), Box::new(replace_tail(rest, t))),
        _ => t,
    }
}

// Rows are sets of effect labels: an effect required twice is required once.
// Coincident labels (same name and, after zonking, identical instantiation
// arguments) arise mechanically when an op's own effect is both listed in its
// parameter row and folded into the ambient tail that row's variable binds to
// (`bind_op_rows_to_ambient` splices the just-absorbed label back in via the
// tail), so the second copy is spurious. Drop every label whose (name, args)
// already appeared earlier in the spine, keeping the first occurrence and the
// tail. Assumes `r` is already zonked, so argument equality is structural: a
// label whose args merely differ (`Async(Int)` versus an unsolved `Async(?9)`)
// is kept, so a genuine two-instantiation reconciliation still routes through
// `rewrite_row`.
fn dedup_row(r: &EffRow) -> EffRow {
    fn go(r: &EffRow, seen: &mut Vec<Label>) -> EffRow {
        match r {
            EffRow::Extend(l, rest) if seen.contains(l) => go(rest, seen),
            EffRow::Extend(l, rest) => {
                seen.push(l.clone());
                EffRow::Extend(l.clone(), Box::new(go(rest, seen)))
            }
            other => other.clone(),
        }
    }
    go(r, &mut Vec::new())
}

// Drop every label whose effect name is in `names`, keeping the tail. Used both
// to skip prefix labels when absorbing and to discharge handled effects.
pub(super) fn without_labels(r: &EffRow, names: &BTreeSet<Sym>) -> EffRow {
    match r {
        EffRow::Extend(l, rest) => {
            let rest = without_labels(rest, names);
            if names.contains(&l.name) {
                rest
            } else {
                EffRow::Extend(l.clone(), Box::new(rest))
            }
        }
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::tc::{PathRes, Tc};

    // A bare Tc with empty environments, enough to drive row rewriting.
    fn tc<'a>(
        ctors: &'a BTreeMap<String, super::super::CtorInfo>,
        data: &'a BTreeMap<String, super::super::DataInfo>,
        eff_ops: &'a BTreeMap<String, super::super::EffOpInfo>,
        classes: &'a BTreeMap<Sym, super::super::ClassInfo>,
        instances: &'a BTreeMap<Sym, super::super::InstInfo>,
        inst_keys: &'a super::super::InstKeys,
        canonical: &'a super::super::Canon,
    ) -> Tc<'a> {
        Tc {
            ctx: Vec::new(),
            next: 0,
            seeds: 0,
            ctors,
            data,
            eff_ops,
            field_res: BTreeMap::new(),
            unboxed_field: BTreeMap::new(),
            path_res: PathRes::new(),
            fixed: BTreeMap::new(),
            span_types: BTreeMap::new(),
            pending: Vec::new(),
            or_null_sites: Vec::new(),
            classes,
            instances,
            inst_keys,
            canonical,
            constrained: BTreeMap::new(),
            cur_self: None,
            wanted: Vec::new(),
            num_default: Vec::new(),
            neg_default: Vec::new(),
            index_ops: Vec::new(),
            dicts: BTreeMap::new(),
            row_ctx: Vec::new(),
            cur_row: None,
            handler_stack: Vec::new(),
        }
    }

    // occurs_ex must look through every type former so subsume refuses to solve
    // an existential against a type that mentions it (an infinite type).
    #[test]
    fn occurs_ex_sees_nested_existentials() {
        let buried = Type::Fun(
            vec![Type::Con(
                "Box".into(),
                vec![Type::Tuple(vec![Type::Exist(7)])],
            )],
            EffRow::singleton("IO"),
            Box::new(Type::Int),
        );
        assert!(occurs_ex(7, &buried));
        assert!(!occurs_ex(8, &buried));

        // Existentials hiding in a row label's instantiation args count too.
        let in_row = Type::Fun(
            Vec::new(),
            EffRow::Extend(
                Label {
                    name: "Emit".into(),
                    args: vec![Type::Exist(3)],
                },
                Box::new(EffRow::Empty),
            ),
            Box::new(Type::Unit),
        );
        assert!(occurs_ex(3, &in_row));
        assert!(!occurs_ex(7, &in_row));
    }

    // rewrite_row hoists a label out of a row no matter where it sits, leaving
    // the same residual tail. Effect rows therefore unify up to permutation.
    #[test]
    fn rewrite_row_is_order_insensitive() {
        let ctors = BTreeMap::new();
        let data = BTreeMap::new();
        let eff_ops = BTreeMap::new();
        let classes = BTreeMap::new();
        let instances = BTreeMap::new();
        let inst_keys = BTreeMap::new();
        let canonical = BTreeMap::new();
        let mut t = tc(
            &ctors, &data, &eff_ops, &classes, &instances, &inst_keys, &canonical,
        );

        let io = Label::bare("IO");
        let head = |a: &str, b: &str| {
            EffRow::Extend(
                Label::bare(a),
                Box::new(EffRow::Extend(Label::bare(b), Box::new(EffRow::Empty))),
            )
        };

        let unwrap = |r: Result<EffRow, TcErr>| match r {
            Ok(row) => row,
            Err(TcErr::Fail(m) | TcErr::Keep(m) | TcErr::Ice(m)) => {
                panic!("rewrite_row failed: {m}")
            }
        };
        let from_front = unwrap(t.rewrite_row(&head("IO", "Emit"), &io));
        let from_back = unwrap(t.rewrite_row(&head("Emit", "IO"), &io));
        assert_eq!(from_front, EffRow::singleton("Emit"));
        assert_eq!(from_front, from_back);
    }
}
