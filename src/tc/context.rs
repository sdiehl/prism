use std::collections::BTreeSet;
use std::ops::Deref;

use super::{Entry, Env, Tc, TcErr};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label, Type};

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
        let i = self
            .ctx
            .iter()
            .position(|e| matches!(e, Entry::ExRow(w) | Entry::SolvedRow(w, _) if *w == v))
            .ok_or_else(|| TcErr::Ice(format!("solve_row: ^{v} not in context")))?;
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
        // One zonk per env binding feeds the existential, row-existential, and
        // free-type-variable sets; the env is often the whole prelude, so walking
        // it once rather than three times is the cheaper of identical passes.
        let mut env_exs = BTreeSet::new();
        let mut env_row_exs = BTreeSet::new();
        let mut env_tvars = BTreeSet::new();
        for v in env.values() {
            let av = self.apply(v);
            av.free_exist(&mut env_exs);
            av.free_exist_row(&mut env_row_exs);
            super::env::collect_type_vars(&av, &mut env_tvars);
        }
        // Generalized existentials keep their historical id-order naming, so an
        // all-existential scheme (every inferred function) prints byte-identically
        // to before rigid signature variables existed.
        let gen: Vec<u32> = exs.into_iter().filter(|e| !env_exs.contains(e)).collect();
        let mut names = Vec::new();
        let mut mapping = Vec::new();
        for (i, e) in gen.iter().enumerate() {
            let name = var_name(i);
            mapping.push((*e, name.clone()));
            names.push(name);
        }
        // Rigid signature variables this scheme introduces (free here, not bound by
        // the environment: a nested `let` inside a function sees the function's
        // signature variables in scope, so it must not quantify them) are quantified
        // after the existentials, in first-appearance order. A fully-annotated
        // polymorphic function has no existentials, so its variables are named
        // `a, b, ...` left to right, exactly as the all-existential path named them.
        let mut rigid_seen = Vec::new();
        free_type_vars_ordered(t, &mut rigid_seen);
        let mut rigids = Vec::new();
        for v in rigid_seen.into_iter().filter(|v| !env_tvars.contains(v)) {
            let name = var_name(names.len());
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

fn collect_type_names(t: &Type, out: &mut BTreeSet<Sym>) {
    match t {
        Type::Var(n) | Type::Forall(n, _) => {
            out.insert(*n);
            if let Type::Forall(_, body) = t {
                collect_type_names(body, out);
            }
        }
        Type::RowForall(_, body) => collect_type_names(body, out),
        Type::Fun(params, row, ret) => {
            for param in params {
                collect_type_names(param, out);
            }
            row.for_each_arg(&mut |arg| collect_type_names(arg, out));
            collect_type_names(ret, out);
        }
        Type::Con(_, params) | Type::Tuple(params) | Type::UnboxedTuple(params) => {
            for param in params {
                collect_type_names(param, out);
            }
        }
        Type::UnboxedRecord(fs) => {
            for (_, t) in fs {
                collect_type_names(t, out);
            }
        }
        Type::App(head, arg) => {
            collect_type_names(head, out);
            collect_type_names(arg, out);
        }
        Type::OrNull(a) => collect_type_names(a, out),
        Type::Row(row) => row.for_each_arg(&mut |arg| collect_type_names(arg, out)),
        _ => {}
    }
}

// Free type variables of a type, in first-appearance order, deduped. It does not
// descend a `forall`, so a rank-n bound variable is correctly excluded
// (consistent with the environment set the caller filters against). It reaches
// type arguments carried by an effect row (a parametric effect like `Async(a)`),
// as `free_exist` does, so a signature variable appearing only in a row (e.g.
// `! {Async(a)}`) is still re-quantified. The arrow order is parameters, result,
// then row arguments, matching the order `seed_decl` allocates them, so an
// all-existential scheme's historical names are reproduced.
fn free_type_vars_ordered(t: &Type, out: &mut Vec<Sym>) {
    match t {
        Type::Var(n) => {
            if !out.contains(n) {
                out.push(*n);
            }
        }
        Type::Fun(ps, row, r) => {
            for p in ps {
                free_type_vars_ordered(p, out);
            }
            free_type_vars_ordered(r, out);
            row.for_each_arg(&mut |a| free_type_vars_ordered(a, out));
        }
        Type::Con(_, ps) | Type::Tuple(ps) | Type::UnboxedTuple(ps) => {
            for p in ps {
                free_type_vars_ordered(p, out);
            }
        }
        Type::UnboxedRecord(fs) => {
            for (_, t) in fs {
                free_type_vars_ordered(t, out);
            }
        }
        Type::App(h, a) => {
            free_type_vars_ordered(h, out);
            free_type_vars_ordered(a, out);
        }
        Type::OrNull(a) => free_type_vars_ordered(a, out),
        Type::Row(r) => r.for_each_arg(&mut |a| free_type_vars_ordered(a, out)),
        _ => {}
    }
}

fn var_name(i: usize) -> String {
    let c = char::from(b"abcdefghijklmnopqrstuvwxyz"[i % 26]);
    if i < 26 {
        c.to_string()
    } else {
        format!("{c}{}", i / 26)
    }
}

fn collect_row_names(t: &Type, out: &mut BTreeSet<String>) {
    match t {
        Type::Fun(ps, row, r) => {
            for p in ps {
                collect_row_names(p, out);
            }
            if let EffRow::Var(n) = row.tail() {
                out.insert(n.to_string());
            }
            collect_row_names(r, out);
        }
        Type::RowForall(n, b) => {
            out.insert(n.to_string());
            collect_row_names(b, out);
        }
        Type::Forall(_, b) => collect_row_names(b, out),
        Type::Con(_, ps) | Type::Tuple(ps) => {
            for p in ps {
                collect_row_names(p, out);
            }
        }
        Type::Row(r) => {
            if let EffRow::Var(n) = r.tail() {
                out.insert(n.to_string());
            }
        }
        _ => {}
    }
}
