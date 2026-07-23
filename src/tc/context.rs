use std::collections::BTreeSet;
use std::ops::Deref;

use super::{Entry, Env, Tc, TcErr};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label, Type};

// Shown when an effect-row unification references a row variable that has already
// left the typing context (a row-scope escape). One canonical home, referenced by
// both `solve_row` here and `unify_row` in `subsume`.
pub(super) const ROW_ESCAPES_SCOPE: &str =
    "effect row escapes its scope: a row variable used here was introduced in an inner scope that has already closed, so its effects can no longer be determined";

/// A `Type` with every solved metavariable already resolved (see `Tc::zonk`).
///
/// Scheme construction in `generalize_zonked` relies on this: it enumerates the
/// free existentials and rigid variables of its input and renames them
/// structurally, which is only correct once no unsolved metavariable stands in
/// for a type it would otherwise have to look through. Making "already zonked"
/// a type-level fact means that work-doer cannot be handed a raw, unresolved
/// `Type`. Constructed only at the zonk boundary (`Tc::zonk`); `Deref` gives
/// read access to the wrapped `Type`.
pub(super) struct Zonked(pub Type);

impl Deref for Zonked {
    type Target = Type;
    fn deref(&self) -> &Type {
        &self.0
    }
}

impl Tc<'_> {
    // Per-declaration reset keeps the pinned `var` state existentials live;
    // each is referenced by exactly one declaration's get/put ops.
    pub(super) fn reset_ctx(&mut self) {
        self.ctx.clear();
        self.ctx.extend((0..self.seeds).map(Entry::Ex));
        self.row_ctx.clear();
    }

    pub(super) fn push_ex(&mut self) -> u32 {
        let v = self.next;
        self.next += 1;
        self.ctx.push(Entry::Ex(v));
        v
    }

    pub(super) const fn fresh_id(&mut self) -> u32 {
        let v = self.next;
        self.next += 1;
        v
    }

    pub(super) fn push_ex_row(&mut self) -> u32 {
        let v = self.next;
        self.next += 1;
        self.ctx.push(Entry::ExRow(v));
        v
    }

    // Run `f` with extra parametric-effect instantiations in scope, restoring
    // the previous scope on exit.
    pub(super) fn in_row_scope<R>(
        &mut self,
        scope: &[(Sym, Vec<Type>)],
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let depth = self.row_ctx.len();
        self.row_ctx.extend(scope.iter().cloned());
        let r = f(self);
        self.row_ctx.truncate(depth);
        r
    }

    fn solved_row(&self, v: u32) -> Option<EffRow> {
        self.ctx.iter().find_map(|e| match e {
            Entry::SolvedRow(w, r) if *w == v => Some(r.clone()),
            _ => None,
        })
    }

    pub(super) fn solve_row(&mut self, v: u32, r: EffRow) -> Result<(), TcErr> {
        // Absence of the row existential is a row-scope escape, not an internal
        // fault. Unlike the type context, the row context does not keep every
        // solution strictly left-referencing, so a later truncation can strand a
        // row variable that a unification still references. That is a real (if
        // rare) typing failure of a user program, so surface it as a user
        // diagnostic rather than a compiler ICE. `Keep` so this precise reason
        // survives a caller's coarse expected/got rewrite.
        let i = self
            .ctx
            .iter()
            .position(|e| matches!(e, Entry::ExRow(w) | Entry::SolvedRow(w, _) if *w == v))
            .ok_or_else(|| TcErr::Keep(ROW_ESCAPES_SCOPE.into()))?;
        if let Some(sk) = self.row_skolem_escaping(v, &r) {
            // A user program reaches this: a closure created outside a
            // row-polymorphic boundary whose effects can only be satisfied by
            // pinning them onto the bound row. Rejecting it here is the row
            // analogue of a skolem-escape error, not an internal fault.
            return Err(TcErr::Keep(format!(
                "effect row `{}` would capture the rigid row `{sk}`: `{sk}` is bound by an inner `forall`, and a row introduced outside that `forall` cannot depend on it",
                r.show()
            )));
        }
        self.ctx[i] = Entry::SolvedRow(v, r);
        Ok(())
    }

    // The row analogue of `splice_solved`: open row existential `a` to `solved`,
    // inserting the fresh `new_rows` at `a`'s position (not appended at the end),
    // so the solution references only entries to its left. Appending instead lets
    // `a` point at a younger row existential to its right, which a later
    // truncation can drop while `a`'s solution survives, stranding the reference
    // (the `solve_row`/`unify_row` "not in context" ICE).
    pub(super) fn splice_solved_row(
        &mut self,
        a: u32,
        new_rows: &[u32],
        solved: EffRow,
    ) -> Result<(), TcErr> {
        let pos = self
            .index_ex_row(a)
            .ok_or_else(|| TcErr::Ice(format!("splice_solved_row: ^{a} not in context")))?;
        let mut repl: Vec<Entry> = new_rows.iter().map(|r| Entry::ExRow(*r)).collect();
        repl.push(Entry::SolvedRow(a, solved));
        self.ctx.splice(pos..=pos, repl);
        Ok(())
    }

    pub(super) fn apply_row(&self, r: &EffRow) -> EffRow {
        match r {
            EffRow::Exist(v) => self
                .solved_row(*v)
                .map_or_else(|| r.clone(), |s| self.apply_row(&s)),
            EffRow::Extend(l, rest) => EffRow::Extend(
                Label {
                    name: l.name,
                    args: l.args.iter().map(|a| self.apply(a)).collect(),
                },
                Box::new(self.apply_row(rest)),
            ),
            other => other.clone(),
        }
    }

    pub(super) fn index_ex(&self, v: u32) -> Option<usize> {
        self.ctx
            .iter()
            .position(|e| matches!(e, Entry::Ex(w) | Entry::Solved(w, _) if *w == v))
    }

    pub(super) fn index_ex_row(&self, v: u32) -> Option<usize> {
        self.ctx
            .iter()
            .position(|e| matches!(e, Entry::ExRow(w) | Entry::SolvedRow(w, _) if *w == v))
    }

    // Position of a rigid type-variable (skolem) in the context, the `Uni`
    // analogue of `index_ex`. Leftmost, matching `drop_uni`'s truncation point,
    // so the scope test agrees with the entry that actually gets dropped.
    fn index_uni(&self, n: Sym) -> Option<usize> {
        self.ctx
            .iter()
            .position(|e| matches!(e, Entry::Uni(w) if *w == n))
    }

    // Position of a rigid row-variable (row skolem), the `RowUni` analogue.
    fn index_row_uni(&self, n: Sym) -> Option<usize> {
        self.ctx
            .iter()
            .position(|e| matches!(e, Entry::RowUni(w) if *w == n))
    }

    fn solved(&self, v: u32) -> Option<Type> {
        self.ctx.iter().find_map(|e| match e {
            Entry::Solved(w, t) if *w == v => Some(t.clone()),
            _ => None,
        })
    }

    pub(super) fn solve(&mut self, v: u32, t: Type) {
        if let Some(i) = self.index_ex(v) {
            // Scope guard at the origin: the solution may only reference entries
            // to the left of `v`, so truncation never strands a referenced var
            // and the downstream `index_ex` lookups can never miss. A forward or
            // out-of-scope reference here is a compiler bug, caught at its cause.
            debug_assert!(
                self.well_formed_before(v, &t),
                "solve: solution references a forward or out-of-scope variable"
            );
            self.ctx[i] = Entry::Solved(v, t);
        }
    }

    // Truncating to `i` drops every entry in `ctx[i..]`. `solve` keeps every type
    // solution strictly left-referencing (the `well_formed_before` guard), so a
    // surviving solution (in `ctx[..i]`) never names a dropped *type existential*;
    // this asserts that at the boundary, the compiler bug the downstream `index_ex`
    // `expect`s guard against. Existentials carry globally-unique fresh ids, so the
    // disjointness test is exact.
    //
    // Skolems (`Uni`/`RowUni`) are deliberately not asserted here, for the same
    // reason row existentials are not: the check would have no sound formulation at
    // this boundary. A skolem is pushed under its raw forall-bound name (see the
    // `Forall`/`RowForall` arms of `subtype`/`inst`), not a fresh one, so skolem
    // names are not globally unique. An *ambient* rigid variable a surviving
    // solution legitimately references (a class parameter, an outer signature's
    // `forall`) can share a `Sym` with an unrelated in-context skolem being dropped,
    // and a name-based disjointness test cannot tell the two apart, so it false-
    // positives. Skolem escape is prevented soundly at its origin instead:
    // `well_formed_before` checks *index positions* at solve time, while scopes are
    // correctly nested, so a re-check on names at the drop boundary adds no coverage
    // the origin guard lacks. Compiled out of release builds.
    fn assert_no_escape(&self, i: usize) {
        if !cfg!(debug_assertions) {
            return;
        }
        let mut dropped_ex = BTreeSet::new();
        for e in &self.ctx[i..] {
            if let Entry::Ex(w) | Entry::Solved(w, _) = e {
                dropped_ex.insert(*w);
            }
        }
        for e in &self.ctx[..i] {
            if let Entry::Solved(_, t) = e {
                let mut ex = BTreeSet::new();
                t.free_exist(&mut ex);
                debug_assert!(
                    ex.is_disjoint(&dropped_ex),
                    "context truncation strands a type existential referenced by a surviving solution"
                );
            }
        }
    }

    pub(super) fn drop_marker(&mut self, m: u32) {
        if let Some(i) = self
            .ctx
            .iter()
            .position(|e| matches!(e, Entry::Marker(w) if *w == m))
        {
            self.assert_no_escape(i);
            self.ctx.truncate(i);
        }
    }

    pub(super) fn drop_uni(&mut self, n: Sym) {
        if let Some(i) = self
            .ctx
            .iter()
            .position(|e| matches!(e, Entry::Uni(w) if *w == n))
        {
            self.assert_no_escape(i);
            self.ctx.truncate(i);
        }
    }

    pub(super) fn drop_row_uni(&mut self, n: Sym) {
        if let Some(i) = self
            .ctx
            .iter()
            .position(|e| matches!(e, Entry::RowUni(w) if *w == n))
        {
            self.assert_no_escape(i);
            self.ctx.truncate(i);
        }
    }

    /// The zonk boundary: resolve every solved metavariable in `t` and package
    /// the result as a `Zonked`, the one witness that this `Type` may be treated
    /// as fully resolved. The only constructor of `Zonked`.
    pub(super) fn zonk(&self, t: &Type) -> Zonked {
        Zonked(self.apply(t))
    }

    pub(super) fn apply(&self, t: &Type) -> Type {
        match t {
            Type::Exist(v) => self
                .solved(*v)
                .map_or_else(|| t.clone(), |s| self.apply(&s)),
            Type::Forall(n, b) => Type::Forall(*n, Box::new(self.apply(b))),
            Type::RowForall(n, b) => Type::RowForall(*n, Box::new(self.apply(b))),
            Type::Fun(ps, row, r) => Type::Fun(
                ps.iter().map(|p| self.apply(p)).collect(),
                self.apply_row(row),
                Box::new(self.apply(r)),
            ),
            // Re-reduce an application once its head existential resolves.
            Type::App(h, a) => Type::app(self.apply(h), self.apply(a)),
            Type::Con(n, ps) => Type::Con(*n, ps.iter().map(|p| self.apply(p)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.apply(t)).collect()),
            Type::UnboxedTuple(ts) => {
                Type::UnboxedTuple(ts.iter().map(|t| self.apply(t)).collect())
            }
            Type::UnboxedRecord(fs) => {
                Type::UnboxedRecord(fs.iter().map(|(n, t)| (*n, self.apply(t))).collect())
            }
            Type::OrNull(a) => Type::OrNull(Box::new(self.apply(a))),
            Type::Coeffect(a, r) => Type::Coeffect(Box::new(self.apply(a)), r.clone()),
            Type::Row(r) => Type::Row(self.apply_row(r)),
            other => other.clone(),
        }
    }

    // A candidate solution for existential `a` is well-scoped only if every free
    // variable it names is bound to `a`'s left, so a later truncation that drops
    // `a`'s right neighbours never strands a reference. The guard closes the whole
    // variable class, not just existentials: a `Uni`/`RowUni` skolem introduced
    // under an inner `forall` sits to `a`'s right, so solving an outer `a` to it
    // would let the skolem escape its quantifier (the fast path in `inst` trusts
    // exactly this predicate). An existential must be in the context (its absence
    // is a compiler bug, rejected). A skolem *absent* from the context is not an
    // escape: it is an ambient rigid variable bound outside every context entry
    // (a class parameter during instance-method checking, an outer signature's
    // `forall`), so it stands to the left of `a` by construction and is accepted;
    // only a skolem the context actually holds is order-checked.
    pub(super) fn well_formed_before(&self, a: u32, t: &Type) -> bool {
        let Some(ai) = self.index_ex(a) else {
            return false;
        };
        let mut exs = BTreeSet::new();
        t.free_exist(&mut exs);
        let mut uvars = BTreeSet::new();
        t.free_ty_vars(&mut uvars);
        let mut rvars = BTreeSet::new();
        t.free_row_vars(&mut rvars);
        exs.iter()
            .all(|e| self.index_ex(*e).is_some_and(|i| i < ai))
            && uvars
                .iter()
                .all(|n| self.index_uni(*n).is_none_or(|i| i < ai))
            && rvars
                .iter()
                .all(|n| self.index_row_uni(*n).is_none_or(|i| i < ai))
    }

    // The first rigid row variable in `r` that stands to the right of the
    // existential `a` in the context, if any. Solving `a` to such a row would
    // let the skolem outlive the `forall` that binds it (the skolem is dropped
    // when its binder's scope closes; `a`, introduced earlier, survives). A
    // skolem absent from the context is ambient (bound outside every entry) and
    // is never an escape, mirroring `well_formed_before`.
    pub(super) fn row_skolem_escaping(&self, a: u32, r: &EffRow) -> Option<Sym> {
        let ai = self.index_ex_row(a)?;
        let row_ty = Type::Row(r.clone());
        let mut rvars = BTreeSet::new();
        row_ty.free_row_vars(&mut rvars);
        rvars
            .into_iter()
            .find(|n| self.index_row_uni(*n).is_some_and(|i| i >= ai))
    }

    pub(super) fn articulate(
        &mut self,
        a: u32,
        arg_exs: &[u32],
        row: u32,
        ret: u32,
    ) -> Result<(), TcErr> {
        let fun = Type::Fun(
            arg_exs.iter().map(|e| Type::Exist(*e)).collect(),
            EffRow::Exist(row),
            Box::new(Type::Exist(ret)),
        );
        // `a` is the live existential `inst` is articulating; the solve invariant
        // keeps it in context, so absence is a compiler bug, not user-reachable.
        // It surfaces as a structured ICE rather than a raw panic, matching the
        // rest of the context/row machinery.
        let pos = self
            .index_ex(a)
            .ok_or_else(|| TcErr::Ice(format!("articulate: ^{a} escaped scope")))?;
        let mut repl: Vec<Entry> = arg_exs.iter().map(|e| Entry::Ex(*e)).collect();
        repl.push(Entry::ExRow(row));
        repl.push(Entry::Ex(ret));
        repl.push(Entry::Solved(a, fun));
        self.ctx.splice(pos..=pos, repl);
        Ok(())
    }

    pub(super) fn splice_solved(
        &mut self,
        a: u32,
        new_exs: &[u32],
        solved: Type,
    ) -> Result<(), TcErr> {
        // Same invariant as `articulate`: a live existential is always in
        // context, so absence is a compiler bug surfaced as a structured ICE.
        let pos = self
            .index_ex(a)
            .ok_or_else(|| TcErr::Ice(format!("splice_solved: ^{a} escaped scope")))?;
        let mut repl: Vec<Entry> = new_exs.iter().map(|e| Entry::Ex(*e)).collect();
        repl.push(Entry::Solved(a, solved));
        self.ctx.splice(pos..=pos, repl);
        Ok(())
    }

    // Generalization is unconditional: a `let` binding generalizes its inferred
    // type with no value restriction, even for a syntactic non-value such as
    // `let xs = array_empty()`. This is sound here and stays sound by design,
    // not by accident. The polymorphic-reference hazard the value restriction
    // exists to plug needs a generalizable binding that aliases a mutable cell;
    // Prism has no such thing and never will. There is no ML-style `ref`: the
    // only mutable binding is `var`, which desugars to a private, monomorphic
    // State effect (writing two element types into one `var` is a type error),
    // and `Array`/`HashMap`/`String` are copy-on-write value types with no
    // shared identity, so a functional allocator can never introduce aliasing.
    // A first-class polymorphic mutable reference is deliberately outside the
    // language, so a value restriction would only reject sound programs. Do not
    // add one (and please leave this note for the next reader who wonders).
    //
    // What generalization does NOT do: it quantifies only free type and row
    // existentials (see `generalize_map`), never class constraints. There is no
    // surface syntax for a constraint on a `let` binding (only top-level `fn`s
    // carry `given C(a)`), and no constraint inference here, so a local binding
    // whose body incurs a dictionary obligation over a variable it would
    // generalize (e.g. `let f = \(x) -> show(x)`) cannot carry that obligation in
    // its scheme. The obligation is orphaned on the pre-generalization existential
    // and surfaces at resolution as the standard unresolved-constraint diagnostic
    // ("cannot infer the type for constraint ...", `head_key` in classes.rs); a
    // parameter annotation does not rescue it, since the constraint is detached
    // from the binding's type by generalization. The remedy is to lift the binding
    // to a top-level `fn ... given C(a)`. Generalizing over constraints locally is
    // intentionally not implemented.
    pub(super) fn generalize(&self, env: &Env, ty: &Type) -> Type {
        self.generalize_map(env, ty).0
    }

    pub(super) fn generalize_map(&self, env: &Env, ty: &Type) -> (Type, Renames) {
        let t = self.zonk(ty);
        self.generalize_zonked(env, &t)
    }

    // The scheme builder proper. It only accepts a `Zonked`, so the free-variable
    // enumeration and structural renaming below can never be handed a type whose
    // meaning still hides behind an unsolved metavariable.
    fn generalize_zonked(&self, env: &Env, zt: &Zonked) -> (Type, Renames) {
        let t: &Type = zt;
        let mut exs = BTreeSet::new();
        t.free_exist(&mut exs);
        // The persistent environment indexes only bindings with free variables.
        // Expand those through current solutions; closed prelude and prior
        // top-level schemes need no visit at every local generalization point.
        let mut env_exs = BTreeSet::new();
        let mut env_row_exs = BTreeSet::new();
        let mut env_tvars = env.free_type_vars().collect::<BTreeSet<_>>();
        for exist in env.free_exists() {
            let applied = self.apply(&Type::Exist(exist));
            applied.free_exist(&mut env_exs);
            applied.free_exist_row(&mut env_row_exs);
            super::env::collect_type_vars(&applied, &mut env_tvars);
        }
        for exist in env.free_row_exists() {
            let applied = self.apply(&Type::Row(EffRow::Exist(exist)));
            applied.free_exist(&mut env_exs);
            applied.free_exist_row(&mut env_row_exs);
            super::env::collect_type_vars(&applied, &mut env_tvars);
        }
        // Rigid variables that stay FREE in this scheme (the enclosing
        // signature's variables, bound by the environment): a fresh binder must
        // never reuse one of their spellings, or the binder would capture the
        // free variable (`forall a` closing over an unrelated free `a` collapses
        // two distinct signature variables into one). Empty for every top-level
        // declaration, so the historical id-order naming below is byte-identical
        // wherever it was already correct.
        let mut rigid_seen = Vec::new();
        free_type_vars_ordered(t, &mut rigid_seen);
        let captured: BTreeSet<&str> = rigid_seen
            .iter()
            .filter(|v| env_tvars.contains(*v))
            .map(|v| v.as_str())
            .collect();
        let mut next_name = 0usize;
        let mut fresh_name = || loop {
            let name = var_name(next_name);
            next_name += 1;
            if !captured.contains(name.as_str()) {
                break name;
            }
        };
        // Generalized existentials keep their historical id-order naming, so an
        // all-existential scheme (every inferred function) prints byte-identically
        // to before rigid signature variables existed.
        let gen: Vec<u32> = exs.into_iter().filter(|e| !env_exs.contains(e)).collect();
        let mut names = Vec::new();
        let mut mapping = Vec::new();
        for e in &gen {
            let name = fresh_name();
            mapping.push((*e, name.clone()));
            names.push(name);
        }
        // Rigid signature variables this scheme introduces (free here, not bound by
        // the environment: a nested `let` inside a function sees the function's
        // signature variables in scope, so it must not quantify them) are quantified
        // after the existentials, in first-appearance order. A fully-annotated
        // polymorphic function has no existentials, so its variables are named
        // `a, b, ...` left to right, exactly as the all-existential path named them.
        let mut rigids = Vec::new();
        for v in rigid_seen
            .iter()
            .copied()
            .filter(|v| !env_tvars.contains(v))
        {
            let name = fresh_name();
            rigids.push((v, name.clone()));
            names.push(name);
        }
        // Existentials and rigid variables are renamed through one collision-safe
        // pass (rigids to placeholders first, so a canonical name reused as a
        // source name cannot clobber); `finish_decl` replays the same renaming onto
        // the declaration's constraints.
        let renames = Renames {
            exists: mapping,
            rigids,
        };
        let mut out = renames.apply(t);
        let mut row_exs = BTreeSet::new();
        out.free_exist_row(&mut row_exs);
        // `env_row_exs` was already accumulated in the single env walk above.
        let gen_rows: Vec<u32> = row_exs
            .into_iter()
            .filter(|e| !env_row_exs.contains(e))
            .collect();
        // Skip row names already in the type, else a user-written `e0` binder
        // would capture the substituted occurrences.
        let mut taken = BTreeSet::new();
        collect_row_names(&out, &mut taken);
        let mut row_names = Vec::new();
        let mut next = 0;
        for e in &gen_rows {
            let name = loop {
                let cand = format!("e{next}");
                next += 1;
                if !taken.contains(&cand) {
                    break cand;
                }
            };
            out = out.subst_row_exist(*e, &EffRow::Var(Sym::from(&name)));
            row_names.push(name);
        }
        // Type quantifiers wrap innermost and row quantifiers outermost. When such
        // a scheme is instantiated left to right (`subtype`/`app_synth`), the row
        // existentials enter the context before the type-`forall` marker, so a
        // solution that legitimately refers to one survives the marker's drop
        // instead of being stranded (the `splice_solved_row: not in context` ICE
        // that opening latent rows can otherwise trigger).
        for name in names.into_iter().rev() {
            out = Type::Forall(Sym::from(&name), Box::new(out));
        }
        for name in row_names.into_iter().rev() {
            out = Type::RowForall(Sym::from(&name), Box::new(out));
        }
        (out, renames)
    }
}

// The variable renaming `generalize_map` used to build an exported scheme:
// generalized existentials and rigid signature variables, each mapped to its
// canonical name. `finish_decl` replays it onto the declaration's class
// constraints so a `given C(a)` names the same variable the scheme quantifies.
pub(super) struct Renames {
    exists: Vec<(u32, String)>,
    rigids: Vec<(Sym, String)>,
}

impl Renames {
    pub(super) fn apply(&self, t: &Type) -> Type {
        let target_names: BTreeSet<Sym> = self
            .exists
            .iter()
            .map(|(_, name)| Sym::from(name))
            .chain(self.rigids.iter().map(|(_, name)| Sym::from(name)))
            .collect();
        // Rigid source variables move to fresh placeholders before existentials
        // claim their canonical letters, so a source that names a variable `a`
        // cannot be conflated with a generalized existential also named `a`.
        let mut out = avoid_forall_capture(t, &target_names);
        let mut placeholders = Vec::with_capacity(self.rigids.len());
        for (src, name) in &self.rigids {
            let ph = Sym::fresh();
            out = out.subst_var(*src, &Type::Var(ph));
            placeholders.push((ph, name));
        }
        for (e, name) in &self.exists {
            out = out.subst_exist(*e, &Type::Var(Sym::from(name)));
        }
        for (ph, name) in placeholders {
            out = out.subst_var(ph, &Type::Var(Sym::from(name)));
        }
        out
    }
}

fn avoid_forall_capture(t: &Type, target_names: &BTreeSet<Sym>) -> Type {
    match t {
        Type::Forall(n, body) if target_names.contains(n) => {
            let mut taken = target_names.clone();
            collect_type_names(body, &mut taken);
            let fresh = fresh_type_name(&taken);
            let renamed = body.subst_var(*n, &Type::Var(fresh));
            Type::Forall(
                fresh,
                Box::new(avoid_forall_capture(&renamed, target_names)),
            )
        }
        Type::Forall(n, body) => {
            Type::Forall(*n, Box::new(avoid_forall_capture(body, target_names)))
        }
        Type::RowForall(n, body) => {
            Type::RowForall(*n, Box::new(avoid_forall_capture(body, target_names)))
        }
        Type::Fun(params, row, ret) => Type::Fun(
            params
                .iter()
                .map(|param| avoid_forall_capture(param, target_names))
                .collect(),
            row.map_args(&|arg| avoid_forall_capture(arg, target_names)),
            Box::new(avoid_forall_capture(ret, target_names)),
        ),
        Type::Con(n, params) => Type::Con(
            *n,
            params
                .iter()
                .map(|param| avoid_forall_capture(param, target_names))
                .collect(),
        ),
        Type::App(head, arg) => Type::app(
            avoid_forall_capture(head, target_names),
            avoid_forall_capture(arg, target_names),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .iter()
                .map(|item| avoid_forall_capture(item, target_names))
                .collect(),
        ),
        Type::UnboxedTuple(items) => Type::UnboxedTuple(
            items
                .iter()
                .map(|item| avoid_forall_capture(item, target_names))
                .collect(),
        ),
        Type::UnboxedRecord(fs) => Type::UnboxedRecord(
            fs.iter()
                .map(|(n, t)| (*n, avoid_forall_capture(t, target_names)))
                .collect(),
        ),
        Type::OrNull(a) => Type::OrNull(Box::new(avoid_forall_capture(a, target_names))),
        Type::Coeffect(a, r) => {
            Type::Coeffect(Box::new(avoid_forall_capture(a, target_names)), r.clone())
        }
        Type::Row(row) => Type::Row(row.map_args(&|arg| avoid_forall_capture(arg, target_names))),
        other => other.clone(),
    }
}

fn fresh_type_name(taken: &BTreeSet<Sym>) -> Sym {
    let mut next = 0;
    loop {
        let cand = Sym::from(&var_name(next));
        if !taken.contains(&cand) {
            return cand;
        }
        next += 1;
    }
}

// The generalizer's name collectors used to be four independent structural
// walks that disagreed on which `Type`/`EffRow` variants they descend (three
// skipped `Coeffect`; the row-name walk also skipped `App`/`OrNull`/the unboxed
// products), so a variable reachable only through one of those wrappers could be
// seen by one collector and missed by another. That mismatch is a latent
// capture/under-quantification bug, so every collector now rides one shared
// walker (`walk_gen`), which descends exactly the variant set the canonical
// `Type::free_ty_vars` does. A collector implements only the hooks it needs.
trait GenVisit {
    /// A type-variable occurrence; `bound` is set when an enclosing `Forall`
    /// within the walked term binds it.
    fn ty_var(&mut self, _n: Sym, _bound: bool) {}
    /// A `Forall` binder name.
    fn ty_binder(&mut self, _n: Sym) {}
    /// A `RowForall` binder name.
    fn row_binder(&mut self, _n: Sym) {}
    /// A row's tail variable.
    fn row_tail(&mut self, _n: Sym) {}
}

// One pre-order walk descending every `Type` variant (mirrors `walk_ty_vars` in
// `types::ty`): parameters, result, then row arguments, so first-appearance
// ordering stays stable for the ordered collector. `bound` tracks the enclosing
// `Forall` binders so free and bound type-variable occurrences are distinguished.
fn walk_gen(t: &Type, bound: &mut Vec<Sym>, v: &mut impl GenVisit) {
    match t {
        Type::Var(n) => v.ty_var(*n, bound.contains(n)),
        Type::Forall(n, b) => {
            v.ty_binder(*n);
            bound.push(*n);
            walk_gen(b, bound, v);
            bound.pop();
        }
        Type::RowForall(n, b) => {
            v.row_binder(*n);
            walk_gen(b, bound, v);
        }
        Type::Fun(ps, row, r) => {
            for p in ps {
                walk_gen(p, bound, v);
            }
            walk_gen(r, bound, v);
            walk_gen_row(row, bound, v);
        }
        Type::Con(_, ps) | Type::Tuple(ps) | Type::UnboxedTuple(ps) => {
            for p in ps {
                walk_gen(p, bound, v);
            }
        }
        Type::UnboxedRecord(fs) => {
            for (_, t) in fs {
                walk_gen(t, bound, v);
            }
        }
        Type::App(h, a) => {
            walk_gen(h, bound, v);
            walk_gen(a, bound, v);
        }
        Type::OrNull(a) | Type::Coeffect(a, _) => walk_gen(a, bound, v),
        Type::Row(r) => walk_gen_row(r, bound, v),
        _ => {}
    }
}

// A row descends into its label arguments (types) and reports a tail row
// variable; rows carry no binders of their own.
fn walk_gen_row(row: &EffRow, bound: &mut Vec<Sym>, v: &mut impl GenVisit) {
    row.for_each_arg(&mut |a| walk_gen(a, bound, v));
    if let EffRow::Var(n) = row.tail() {
        v.row_tail(*n);
    }
}

// Every type-variable name and every `Forall` binder appearing in a type, for
// the capture-avoidance freshness set (a superset is safe: it only makes a
// generated name more conservative).
struct TypeNames<'a>(&'a mut BTreeSet<Sym>);
impl GenVisit for TypeNames<'_> {
    fn ty_var(&mut self, n: Sym, _bound: bool) {
        self.0.insert(n);
    }
    fn ty_binder(&mut self, n: Sym) {
        self.0.insert(n);
    }
}

fn collect_type_names(t: &Type, out: &mut BTreeSet<Sym>) {
    walk_gen(t, &mut Vec::new(), &mut TypeNames(out));
}

// Free type variables of a type, in first-appearance order, deduped. A variable
// bound by an enclosing `forall` is excluded (rank-n bound variables stay bound);
// a variable free under such a `forall` is still collected. It reaches type
// arguments carried by an effect row (a parametric effect like `Async(a)`), so a
// signature variable appearing only in a row (e.g. `! {Async(a)}`) is still
// re-quantified.
struct OrderedFreeVars<'a>(&'a mut Vec<Sym>);
impl GenVisit for OrderedFreeVars<'_> {
    fn ty_var(&mut self, n: Sym, bound: bool) {
        if !bound && !self.0.contains(&n) {
            self.0.push(n);
        }
    }
}

fn free_type_vars_ordered(t: &Type, out: &mut Vec<Sym>) {
    walk_gen(t, &mut Vec::new(), &mut OrderedFreeVars(out));
}

fn var_name(i: usize) -> String {
    let c = char::from(b"abcdefghijklmnopqrstuvwxyz"[i % 26]);
    if i < 26 {
        c.to_string()
    } else {
        format!("{c}{}", i / 26)
    }
}

// Every row-variable name in a type: each row tail variable and each `RowForall`
// binder. Used to keep a freshly generated row name from capturing an existing
// one, so (as with the type names above) collecting extra names is safe.
struct RowNames<'a>(&'a mut BTreeSet<String>);
impl GenVisit for RowNames<'_> {
    fn row_binder(&mut self, n: Sym) {
        self.0.insert(n.to_string());
    }
    fn row_tail(&mut self, n: Sym) {
        self.0.insert(n.to_string());
    }
}

fn collect_row_names(t: &Type, out: &mut BTreeSet<String>) {
    walk_gen(t, &mut Vec::new(), &mut RowNames(out));
}

#[cfg(test)]
mod tests {
    use super::{collect_row_names, collect_type_names, free_type_vars_ordered};
    use crate::sym::Sym;
    use crate::types::coeffect::CoeffectRow;
    use crate::types::ty::{EffRow, Type};
    use std::collections::BTreeSet;

    // A type variable reachable only through a `T @ {once}` (Coeffect) wrapper
    // must still be enumerated for generalization; before the collectors shared
    // one walker, the Coeffect arm was skipped and the variable was never
    // quantified.
    #[test]
    fn coeffect_hidden_var_is_generalizable() {
        let once = CoeffectRow::new(&["once"]).unwrap();
        let ty = Type::Coeffect(Box::new(Type::Var(Sym::from("a"))), once);
        let mut ordered = Vec::new();
        free_type_vars_ordered(&ty, &mut ordered);
        assert_eq!(ordered, vec![Sym::from("a")]);
        let mut names = BTreeSet::new();
        collect_type_names(&ty, &mut names);
        assert!(names.contains(&Sym::from("a")));
    }

    // A row variable buried inside `App(f, Row{..})` must count as taken, so a
    // freshly generated row name cannot capture it. The row-name walk used to
    // skip `App`, missing exactly this occurrence.
    #[test]
    fn row_var_under_app_is_taken() {
        let ty = Type::App(
            Box::new(Type::Var(Sym::from("f"))),
            Box::new(Type::Row(EffRow::Var(Sym::from("e")))),
        );
        let mut rows = BTreeSet::new();
        collect_row_names(&ty, &mut rows);
        assert!(rows.contains("e"));
    }
}
