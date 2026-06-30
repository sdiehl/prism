use std::collections::BTreeSet;

use super::{Entry, Env, Tc, TcErr};
use crate::sym::Sym;
use crate::types::ty::{EffRow, Label, Type};

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

    // Truncating to `i` drops every existential in `ctx[i..]`. `solve` keeps every
    // type solution strictly left-referencing (the `well_formed_before` guard), so
    // a surviving solution (in `ctx[..i]`) never names a dropped *type* existential;
    // this asserts that at the boundary, the compiler-bug the downstream `index_ex`
    // `expect`s guard against. Row existentials are deliberately not asserted: the
    // row context keeps no such ordering invariant (see `unify_row`), so its lookups
    // stay defensive ICEs. Compiled out of release builds.
    fn assert_no_escape(&self, i: usize) {
        if !cfg!(debug_assertions) {
            return;
        }
        let mut dropped_ty = BTreeSet::new();
        for e in &self.ctx[i..] {
            if let Entry::Ex(w) | Entry::Solved(w, _) = e {
                dropped_ty.insert(*w);
            }
        }
        for e in &self.ctx[..i] {
            if let Entry::Solved(_, t) = e {
                let mut ty = BTreeSet::new();
                t.free_exist(&mut ty);
                debug_assert!(
                    ty.is_disjoint(&dropped_ty),
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
            other => other.clone(),
        }
    }

    pub(super) fn well_formed_before(&self, a: u32, t: &Type) -> bool {
        let Some(ai) = self.index_ex(a) else {
            return false;
        };
        let mut exs = BTreeSet::new();
        t.free_exist(&mut exs);
        exs.iter()
            .all(|e| self.index_ex(*e).is_some_and(|i| i < ai))
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
    pub(super) fn generalize(&self, env: &Env, ty: &Type) -> Type {
        self.generalize_map(env, ty).0
    }

    pub(super) fn generalize_map(&self, env: &Env, ty: &Type) -> (Type, Vec<(u32, String)>) {
        let t = self.apply(ty);
        let mut exs = BTreeSet::new();
        t.free_exist(&mut exs);
        // One zonk per env binding feeds both the existential and the row-existential
        // free-variable sets; the env is often the whole prelude, so walking it once
        // rather than twice is the cheaper of two identical passes.
        let mut env_exs = BTreeSet::new();
        let mut env_row_exs = BTreeSet::new();
        for v in env.values() {
            let av = self.apply(v);
            av.free_exist(&mut env_exs);
            av.free_exist_row(&mut env_row_exs);
        }
        let gen: Vec<u32> = exs.into_iter().filter(|e| !env_exs.contains(e)).collect();
        let mut out = t;
        let mut names = Vec::new();
        let mut mapping = Vec::new();
        for (i, e) in gen.iter().enumerate() {
            let name = var_name(i);
            out = out.subst_exist(*e, &Type::Var(Sym::from(&name)));
            mapping.push((*e, name.clone()));
            names.push(name);
        }
        let mut row_exs = BTreeSet::new();
        out.free_exist_row(&mut row_exs);
        let mut env_row_exs = BTreeSet::new();
        for v in env.values() {
            self.apply(v).free_exist_row(&mut env_row_exs);
        }
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
        for name in row_names.into_iter().rev() {
            out = Type::RowForall(Sym::from(&name), Box::new(out));
        }
        for name in names.into_iter().rev() {
            out = Type::Forall(Sym::from(&name), Box::new(out));
        }
        (out, mapping)
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
        _ => {}
    }
}
