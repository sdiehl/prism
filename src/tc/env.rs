use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::{CtorInfo, DataInfo, EffOpInfo, Env, Tc};
use crate::error::TypeError;
use crate::lex::lex_raw;
use crate::names;
use crate::sym::Sym;
use crate::syntax::ast::{self, Core, Decl, Program};
use crate::syntax::TypeSigParser;
use crate::types::ty::{EffRow, Kind, Label, Type};

// Effects the compiler knows without an `effect` declaration: the IO/Exn
// builtins, the indexing/`??` `Fail`, and the internal loop/return control
// effects desugaring injects. Anything else named in a row must be declared.
pub(super) fn is_builtin_effect(name: &str) -> bool {
    name == names::IO_EFFECT
        || name == names::EXN_EFFECT
        || name == names::FAIL_EFFECT
        || name == names::BREAK_EFFECT
        || name == names::CONTINUE_EFFECT
        || name == names::RETURN_EFFECT
}

pub(super) struct Annot<'a> {
    ty_ex: &'a mut BTreeMap<String, u32>,
    row_ex: &'a mut BTreeMap<String, u32>,
    rigid_ty: &'a BTreeSet<String>,
    rigid_row: &'a BTreeSet<String>,
}

impl<'a> Annot<'a> {
    pub(super) const fn new(
        ty_ex: &'a mut BTreeMap<String, u32>,
        row_ex: &'a mut BTreeMap<String, u32>,
        empty: &'a BTreeSet<String>,
    ) -> Self {
        Self {
            ty_ex,
            row_ex,
            rigid_ty: empty,
            rigid_row: empty,
        }
    }

    // Convert against a supplied rigid type-variable set (and a separate, usually
    // empty, rigid row set). Used to seed a top-level function body where the bare
    // signature type variables are rigid (an implicit `forall`), so the body
    // cannot silently narrow one to a concrete type.
    pub(super) const fn with_rigid(
        ty_ex: &'a mut BTreeMap<String, u32>,
        row_ex: &'a mut BTreeMap<String, u32>,
        rigid_ty: &'a BTreeSet<String>,
        rigid_row: &'a BTreeSet<String>,
    ) -> Self {
        Self {
            ty_ex,
            row_ex,
            rigid_ty,
            rigid_row,
        }
    }
}

impl Tc<'_> {
    // A label written with arguments must match the effect's declared parameter
    // count; a bare mention stays legal as an unapplied row label.
    pub(super) fn check_annot_rows(&self, t: &ast::Ty, span: Span) -> Result<(), TypeError> {
        match t {
            ast::Ty::Forall(_, b) => self.check_annot_rows(b, span),
            ast::Ty::Fun(ps, row, r) => {
                for p in ps {
                    self.check_annot_rows(p, span)?;
                }
                if let ast::Row::Cons(ls, _) = row {
                    self.check_labels(ls, span)?;
                }
                self.check_annot_rows(r, span)
            }
            ast::Ty::Con(n, ts) => {
                // Impredicativity is a structural property of the written type,
                // independent of whether the head constructor is declared, so it
                // is reported before the existence check.
                no_polytype_args(ts, n, span)?;
                let Some(info) = self.data.get(n) else {
                    return Err(TypeError::Other {
                        span,
                        msg: format!("unknown type `{n}`"),
                    });
                };
                // Kind-check the application against the constructor's kind. The
                // constructor's kind is the arrow `Kind::arrow(param_kinds)` (for
                // `Vec(a, n : Nat)`, `Type -> Nat -> Type`); each argument peels one
                // domain off, so a mis-kinded or over-supplied argument is a clear
                // message here rather than a downstream unification failure. A
                // syntactically-unknown argument (a bare variable or application) is
                // accepted at any domain: its kind is pinned by inference.
                let mut con_kind = Kind::arrow(&info.param_kinds);
                for (i, arg) in ts.iter().enumerate() {
                    let Kind::Fun(dom, rest) = con_kind else {
                        return Err(TypeError::Other {
                            span,
                            msg: format!(
                                "`{n}` is applied to too many arguments: it takes {}, but {} were given",
                                info.param_kinds.len(),
                                ts.len()
                            ),
                        });
                    };
                    if let Some(actual) = syntactic_kind(arg) {
                        if actual != *dom {
                            return Err(TypeError::Other {
                                span,
                                msg: format!(
                                    "kind mismatch: parameter {} of `{n}` has kind `{}`, but a `{}` was given",
                                    i + 1,
                                    dom.show(),
                                    actual.show(),
                                ),
                            });
                        }
                    }
                    con_kind = *rest;
                }
                ts.iter().try_for_each(|x| self.check_annot_rows(x, span))
            }
            ast::Ty::App(v, ts) => {
                no_polytype_args(ts, v, span)?;
                ts.iter().try_for_each(|x| self.check_annot_rows(x, span))
            }
            ast::Ty::Tuple(ts) => ts.iter().try_for_each(|x| self.check_annot_rows(x, span)),
            // A `{..}` row literal in argument position: its labels are validated
            // like any other effect row.
            ast::Ty::RowLit(ast::Row::Cons(ls, _)) => self.check_labels(ls, span),
            _ => Ok(()),
        }
    }

    pub(super) fn check_labels(
        &self,
        labels: &[ast::EffLabel],
        span: Span,
    ) -> Result<(), TypeError> {
        for l in labels {
            let known = self
                .eff_ops
                .values()
                .find(|i| i.effect_name == l.name)
                .map(|i| i.eff_params.len());
            match known {
                Some(want) => {
                    if !l.args.is_empty() && l.args.len() != want {
                        return Err(TypeError::Other {
                            span,
                            msg: format!(
                                "effect `{}` expects {} type argument(s), got {}",
                                l.name,
                                want,
                                l.args.len()
                            ),
                        });
                    }
                }
                None if !is_builtin_effect(&l.name) => {
                    return Err(TypeError::Other {
                        span,
                        msg: format!("unknown effect `{}`", l.name),
                    });
                }
                None => {}
            }
            for arg in &l.args {
                self.check_annot_rows(arg, span)?;
            }
        }
        Ok(())
    }

    // Convert one annotation against fresh (per-annotation) tyvar/row maps. Use
    // when an annotation stands alone; sites that share named tyvars across
    // several annotations build the maps once and reuse `convert_annot`.
    pub(super) fn convert_annot_fresh(&mut self, t: &ast::Ty) -> Type {
        let mut ty_ex = BTreeMap::new();
        let mut row_ex = BTreeMap::new();
        let no_rigid = BTreeSet::new();
        let mut a = Annot::new(&mut ty_ex, &mut row_ex, &no_rigid);
        self.convert_annot(t, &mut a)
    }

    pub(super) fn convert_annot(&mut self, t: &ast::Ty, a: &mut Annot<'_>) -> Type {
        match t {
            ast::Ty::Int => Type::Int,
            ast::Ty::I64 => Type::I64,
            ast::Ty::U64 => Type::U64,
            ast::Ty::Bool => Type::Bool,
            ast::Ty::Unit => Type::Unit,
            ast::Ty::Float => Type::Float,
            ast::Ty::Char => Type::Char,
            ast::Ty::Str => Type::Str,
            ast::Ty::Var(n) => {
                if a.rigid_ty.contains(n) {
                    Type::Var(Sym::from(n))
                } else if let Some(e) = a.ty_ex.get(n) {
                    Type::Exist(*e)
                } else {
                    let e = self.push_ex();
                    a.ty_ex.insert(n.clone(), e);
                    Type::Exist(e)
                }
            }
            // A `var` state cell reuses the pinned existential id it was desugared to;
            // see the canonical note on `ast::Ty::State`.
            ast::Ty::State(n) => Type::Exist(*n),
            ast::Ty::Forall(names, body) => {
                let mut rows = BTreeSet::new();
                ty_row_vars(body, &mut rows);
                let (row_names, ty_names): (Vec<_>, Vec<_>) =
                    names.iter().cloned().partition(|n| rows.contains(n));
                let mut rigid_ty = a.rigid_ty.clone();
                rigid_ty.extend(ty_names.iter().cloned());
                let mut rigid_row = a.rigid_row.clone();
                rigid_row.extend(row_names.iter().cloned());
                let mut a2 = Annot {
                    ty_ex: a.ty_ex,
                    row_ex: a.row_ex,
                    rigid_ty: &rigid_ty,
                    rigid_row: &rigid_row,
                };
                let inner = self.convert_annot(body, &mut a2);
                let mut out = inner;
                for n in row_names.iter().rev() {
                    out = Type::RowForall(Sym::from(n), Box::new(out));
                }
                for n in ty_names.iter().rev() {
                    out = Type::Forall(Sym::from(n), Box::new(out));
                }
                out
            }
            ast::Ty::Fun(ps, row, r) => Type::fun_eff(
                ps.iter().map(|p| self.convert_annot(p, a)).collect(),
                self.convert_row(row, a),
                self.convert_annot(r, a),
            ),
            ast::Ty::Con(n, args) => {
                // A `Row`-kinded parameter position takes an effect row, not a
                // type, so its argument is lowered as a row (`Cmd(a, e)`).
                let kinds = self.data.get(n).map(|d| d.param_kinds.clone());
                let mut conv: Vec<Type> = args
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        let is_row = kinds
                            .as_ref()
                            .and_then(|ks| ks.get(i))
                            .is_some_and(|k| *k == Kind::Row);
                        if is_row {
                            Type::Row(self.row_annot_arg(x, a))
                        } else {
                            self.convert_annot(x, a)
                        }
                    })
                    .collect();
                // Trailing phantom parameters may be left off: `Map(k, v)` names
                // the arity-3 `Map(k, v, ord)` with a fresh brand for the omitted
                // `ord` (so pre-brand source keeps checking). Only a partial (not
                // empty: a bare `Map` is a higher-kinded head) application fills,
                // each missing position a fresh existential of its declared kind.
                if let Some(ks) = &kinds {
                    if !conv.is_empty() && conv.len() < ks.len() {
                        for k in &ks[conv.len()..] {
                            conv.push(match k {
                                Kind::Row => Type::Row(EffRow::Exist(self.push_ex_row())),
                                _ => Type::Exist(self.push_ex()),
                            });
                        }
                    }
                }
                Type::Con(Sym::from(n), conv)
            }
            ast::Ty::App(v, args) => {
                // The head is a type variable (rigid or to-be-unified), applied.
                let head = self.convert_annot(&ast::Ty::Var(v.clone()), a);
                Type::apps(
                    head,
                    args.iter().map(|x| self.convert_annot(x, a)).collect(),
                )
            }
            ast::Ty::Tuple(ts) => {
                Type::Tuple(ts.iter().map(|x| self.convert_annot(x, a)).collect())
            }
            ast::Ty::RowLit(row) => Type::Row(self.convert_row(row, a)),
            ast::Ty::Nat(n) => Type::Nat(*n),
        }
    }

    // Lower a type argument sitting at a `Row`-kinded position of a constructor
    // (`Cmd(a, e)`): only a row variable can be written there, rigid under an
    // enclosing `forall`, otherwise a fresh row existential shared by name with
    // any other mention (so `Cmd(a, e)` and a `! {e}` tail unify).
    fn row_annot_arg(&mut self, x: &ast::Ty, a: &mut Annot<'_>) -> EffRow {
        match x {
            ast::Ty::RowLit(row) => self.convert_row(row, a),
            ast::Ty::Var(m) if a.rigid_row.contains(m) => EffRow::Var(Sym::from(m)),
            ast::Ty::Var(m) => {
                if let Some(e) = a.row_ex.get(m) {
                    EffRow::Exist(*e)
                } else {
                    let e = self.push_ex_row();
                    a.row_ex.insert(m.clone(), e);
                    EffRow::Exist(e)
                }
            }
            _ => EffRow::Empty,
        }
    }

    fn convert_row(&mut self, row: &ast::Row, a: &mut Annot<'_>) -> EffRow {
        let (labels, tail) = match row {
            ast::Row::Empty => return EffRow::Empty,
            ast::Row::Cons(ls, tl) => (ls, tl),
        };
        let base = match tail {
            None => EffRow::Empty,
            Some(v) if a.rigid_row.contains(v) => EffRow::Var(Sym::from(v)),
            Some(v) => {
                if let Some(e) = a.row_ex.get(v) {
                    EffRow::Exist(*e)
                } else {
                    let e = self.push_ex_row();
                    a.row_ex.insert(v.clone(), e);
                    EffRow::Exist(e)
                }
            }
        };
        let labels: Vec<Label> = labels
            .iter()
            .map(|l| Label {
                name: Sym::from(&l.name),
                args: l.args.iter().map(|t| self.convert_annot(t, a)).collect(),
            })
            .collect();
        labels
            .into_iter()
            .rev()
            .fold(base, |acc, l| EffRow::Extend(l, Box::new(acc)))
    }
}

// Predicativity at the source: a type-constructor argument ranges over
// monotypes, so a polytype written directly as one (`List(forall a. ...)`) is
// impredicative. Foralls nested under a function arrow (a rank-N argument or
// result) or declared as a data field stay legal, since those are not a type
// argument. The check is syntactic, so it fires before inference and points at
// the annotation rather than surfacing later as a leaked rigid variable.
fn no_polytype_args(args: &[ast::Ty], head: &str, span: Span) -> Result<(), TypeError> {
    if args.iter().any(|a| matches!(a, ast::Ty::Forall(..))) {
        return Err(TypeError::Other {
            span,
            msg: format!(
                "impredicative type: a polymorphic type cannot be a type argument to `{head}` \
                 (a type parameter ranges over monomorphic types). Higher-rank types are \
                 allowed as function arguments, results, and declared data fields; wrap the \
                 polymorphic type in a data type with a polymorphic field to carry it here."
            ),
        });
    }
    Ok(())
}

// The kind a written type argument commits to by its syntax alone: a `{..}` row
// literal is `Row`, a natural literal is `Nat`, and any concrete type
// constructor or scalar is `Type`. A bare variable or higher-kinded application
// returns `None` (its kind is not fixed by syntax, so the kind checker defers to
// inference and accepts it at any domain).
const fn syntactic_kind(t: &ast::Ty) -> Option<Kind> {
    match t {
        ast::Ty::RowLit(_) => Some(Kind::Row),
        ast::Ty::Nat(_) => Some(Kind::Nat),
        ast::Ty::Var(_) | ast::Ty::App(..) | ast::Ty::State(_) => None,
        _ => Some(Kind::Type),
    }
}

fn ty_row_vars(t: &ast::Ty, out: &mut BTreeSet<String>) {
    // A row's tail variable, wherever a row occurs (a function arrow or a
    // `Row`-kinded `{.. | r}` literal). The tail var is row-position data the
    // child spine does not yield, so match it explicitly; the spine then recurses
    // every nested type (App args and label-argument types the old match skipped).
    match t {
        ast::Ty::Fun(_, ast::Row::Cons(_, Some(v)), _)
        | ast::Ty::RowLit(ast::Row::Cons(_, Some(v))) => {
            out.insert(v.clone());
        }
        _ => {}
    }
    t.each_child(&mut |c| ty_row_vars(c, out));
}

// Lower a data-field row, given the current declaration's `Row`-kinded
// parameters. A label whose name is one of those parameters is not a concrete
// effect but the row variable itself, so it moves to the tail: both `! {e}` and
// `! {IO | e}` yield a row ending in `Var(e)`. Concrete labels stay in the
// prefix, their args lowered with the same row-parameter awareness.
fn data_row_rp(row: &ast::Row, rp: &BTreeSet<Sym>) -> EffRow {
    let ast::Row::Cons(ls, tl) = row else {
        return EffRow::Empty;
    };
    let mut base = tl
        .as_ref()
        .map_or(EffRow::Empty, |v| EffRow::Var(Sym::from(v)));
    let mut concrete = Vec::new();
    for l in ls {
        let name = Sym::from(&l.name);
        if rp.contains(&name) {
            // A row parameter mentioned bare acts as the row tail.
            if base == EffRow::Empty {
                base = EffRow::Var(name);
            }
        } else {
            concrete.push(Label {
                name,
                args: l.args.iter().map(|t| convert_data_rp(t, rp)).collect(),
            });
        }
    }
    concrete
        .into_iter()
        .rev()
        .fold(base, |acc, l| EffRow::Extend(l, Box::new(acc)))
}

pub(super) fn convert_data(t: &ast::Ty) -> Type {
    convert_data_rp(t, &BTreeSet::new())
}

// Saturate an under-applied constructor spine: `Map(k, v)` names the arity-3
// `Map(k, v, ord)`, filling each omitted trailing parameter with a fresh
// variable of its declared kind. This is the exported-scheme twin of the fill in
// `convert_annot` (which mints existentials for the body check); the fresh names
// here are quantified into the scheme by the caller's `collect_*_vars`. Only a
// partial application fills: a bare `Map` head is a higher-kinded operand and is
// left untouched, and a fully applied spine is unchanged.
fn saturate_cons(t: Type, data: &BTreeMap<String, super::DataInfo>) -> Type {
    let go = |x: Type| saturate_cons(x, data);
    match t {
        Type::Con(n, args) => {
            let mut conv: Vec<Type> = args.into_iter().map(go).collect();
            if let Some(info) = data.get(n.as_str()) {
                if !conv.is_empty() {
                    for k in info.param_kinds.iter().skip(conv.len()) {
                        conv.push(match k {
                            Kind::Row => Type::Row(EffRow::Var(Sym::fresh())),
                            _ => Type::Var(Sym::fresh()),
                        });
                    }
                }
            }
            Type::Con(n, conv)
        }
        Type::Fun(ps, row, r) => Type::Fun(
            ps.into_iter().map(go).collect(),
            row,
            Box::new(saturate_cons(*r, data)),
        ),
        Type::Tuple(xs) => Type::Tuple(xs.into_iter().map(go).collect()),
        Type::App(h, a) => Type::App(
            Box::new(saturate_cons(*h, data)),
            Box::new(saturate_cons(*a, data)),
        ),
        Type::Forall(v, b) => Type::Forall(v, Box::new(saturate_cons(*b, data))),
        Type::RowForall(v, b) => Type::RowForall(v, Box::new(saturate_cons(*b, data))),
        other => other,
    }
}

// The core of `convert_data`, aware of the current declaration's `Row`-kinded
// parameters `rp`. A variable named in `rp` is an effect row, so it lowers to
// `Type::Row(Var(..))` wherever it appears (notably as the argument at a
// `Row`-kinded position of a `Con`, `Cmd(a, e)`); every other name is a type
// variable, exactly as before. `rp` is empty for all non-data-field callers.
pub(super) fn convert_data_rp(t: &ast::Ty, rp: &BTreeSet<Sym>) -> Type {
    match t {
        ast::Ty::Int => Type::Int,
        ast::Ty::I64 => Type::I64,
        ast::Ty::U64 => Type::U64,
        ast::Ty::Bool => Type::Bool,
        ast::Ty::Unit => Type::Unit,
        ast::Ty::Float => Type::Float,
        ast::Ty::Char => Type::Char,
        ast::Ty::Str => Type::Str,
        ast::Ty::Var(n) => {
            let s = Sym::from(n);
            if rp.contains(&s) {
                Type::Row(EffRow::Var(s))
            } else {
                Type::Var(s)
            }
        }
        // A `var` state cell reuses the pinned existential id it was desugared to;
        // see the canonical note on `ast::Ty::State`.
        ast::Ty::State(n) => Type::Exist(*n),
        ast::Ty::Forall(names, body) => wrap_forall(
            &names.iter().map(Sym::from).collect::<Vec<_>>(),
            convert_data_rp(body, rp),
        ),
        ast::Ty::Fun(ps, row, r) => Type::fun_eff(
            ps.iter().map(|p| convert_data_rp(p, rp)).collect(),
            data_row_rp(row, rp),
            convert_data_rp(r, rp),
        ),
        ast::Ty::Con(n, args) => Type::Con(
            Sym::from(n),
            args.iter().map(|x| convert_data_rp(x, rp)).collect(),
        ),
        ast::Ty::App(v, args) => Type::apps(
            Type::Var(Sym::from(v)),
            args.iter().map(|x| convert_data_rp(x, rp)).collect(),
        ),
        ast::Ty::Tuple(ts) => Type::Tuple(ts.iter().map(|x| convert_data_rp(x, rp)).collect()),
        ast::Ty::RowLit(row) => Type::Row(data_row_rp(row, rp)),
        ast::Ty::Nat(v) => Type::Nat(*v),
    }
}

// Normalize a declaration's parallel `param_kinds` to a full-length vector: an
// empty annotation means every parameter has kind `Type` (the common case).
fn normalize_kinds(params: &[String], kinds: &[Kind]) -> Vec<Kind> {
    if kinds.len() == params.len() {
        kinds.to_vec()
    } else {
        vec![Kind::Type; params.len()]
    }
}

pub(super) fn wrap_forall(params: &[Sym], body: Type) -> Type {
    let mut out = body;
    for p in params.iter().rev() {
        out = Type::Forall(*p, Box::new(out));
    }
    out
}

// Quantify a constructor scheme over its parameters, each with the right binder
// for its kind: a `Row`-kinded parameter becomes a `RowForall` (opened to a
// fresh row existential at each use), every other a `Forall`.
fn wrap_scheme(params: &[String], kinds: &[Kind], body: Type) -> Type {
    let mut out = body;
    for (p, k) in params.iter().zip(kinds).rev() {
        let s = Sym::from(p);
        out = match k {
            Kind::Row => Type::RowForall(s, Box::new(out)),
            _ => Type::Forall(s, Box::new(out)),
        };
    }
    out
}

pub(super) fn collect_type_vars(t: &Type, out: &mut BTreeSet<Sym>) {
    match t {
        Type::Var(n) => {
            out.insert(*n);
        }
        Type::Fun(ps, _row, r) => {
            for p in ps {
                collect_type_vars(p, out);
            }
            collect_type_vars(r, out);
        }
        Type::Con(_, ps) | Type::Tuple(ps) => {
            for p in ps {
                collect_type_vars(p, out);
            }
        }
        Type::App(h, a) => {
            collect_type_vars(h, out);
            collect_type_vars(a, out);
        }
        Type::Row(r) => r.for_each_arg(&mut |a| collect_type_vars(a, out)),
        _ => {}
    }
}

// Free effect-row variables in a type, so a class method's signature can be
// generalized over its row variables (an effect-polymorphic method like `fmap`).
pub(super) fn collect_row_vars(t: &Type, out: &mut BTreeSet<Sym>) {
    match t {
        Type::Fun(ps, row, r) => {
            for p in ps {
                collect_row_vars(p, out);
            }
            if let EffRow::Var(v) = row.tail() {
                out.insert(*v);
            }
            row.for_each_arg(&mut |a| collect_row_vars(a, out));
            collect_row_vars(r, out);
        }
        Type::Con(_, ps) | Type::Tuple(ps) => {
            for p in ps {
                collect_row_vars(p, out);
            }
        }
        Type::App(h, a) => {
            collect_row_vars(h, out);
            collect_row_vars(a, out);
        }
        Type::Forall(_, b) | Type::RowForall(_, b) => collect_row_vars(b, out),
        Type::Row(r) => {
            if let EffRow::Var(v) = r.tail() {
                out.insert(*v);
            }
            r.for_each_arg(&mut |a| collect_row_vars(a, out));
        }
        _ => {}
    }
}

// True when a declaration carries a full type signature (every parameter and
// the return type annotated, not a constant): the condition under which
// `annotation_scheme` yields a scheme, which is what keeps annotated polymorphic
// recursion decidable.
pub(super) fn fully_annotated(d: &Decl<Core>) -> bool {
    !d.konst && d.params.iter().all(|p| p.ty.is_some()) && d.ret.is_some()
}

// The names an annotation uses at a *row* position: an arrow tail `{.. | e}` or
// a `Row`-kinded constructor slot (`Cmd(a, e)`). Those are effect-row variables;
// every other name in the annotation is a type variable. Needs the data map to
// know which constructor slots are `Row`-kinded.
fn ann_row_var_names(
    t: &ast::Ty,
    data: &BTreeMap<String, super::DataInfo>,
    out: &mut BTreeSet<Sym>,
) {
    // Node-specific: a `Con`'s `Row`-kinded slots naming a bare variable, and a
    // row tail variable on an arrow or a `{.. | r}` row literal. Everything else
    // recurses through the spine, which reaches App args, label-argument types,
    // and the row-literal labels the old match skipped.
    match t {
        ast::Ty::Con(n, args) => {
            if let Some(info) = data.get(n) {
                for (i, arg) in args.iter().enumerate() {
                    if matches!(info.param_kinds.get(i), Some(Kind::Row)) {
                        if let ast::Ty::Var(m) = arg {
                            out.insert(Sym::from(m));
                        }
                    }
                }
            }
        }
        ast::Ty::Fun(_, ast::Row::Cons(_, Some(v)), _)
        | ast::Ty::RowLit(ast::Row::Cons(_, Some(v))) => {
            out.insert(Sym::from(v));
        }
        _ => {}
    }
    t.each_child(&mut |c| ann_row_var_names(c, data, out));
}

// Type-variable names appearing free (not bound by a nested `forall`) in an
// annotation. A name at a `Row`-kinded position is an effect-row variable, not a
// type variable, so `signature_ty_vars` subtracts those; this walk alone does
// not distinguish them.
fn ann_free_ty_vars(t: &ast::Ty, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    match t {
        ast::Ty::Var(n) => {
            if !bound.iter().any(|b| b == n) {
                out.insert(n.clone());
            }
        }
        ast::Ty::App(v, args) => {
            if !bound.iter().any(|b| b == v) {
                out.insert(v.clone());
            }
            for a in args {
                ann_free_ty_vars(a, bound, out);
            }
        }
        ast::Ty::Forall(names, body) => {
            let k = names.len();
            bound.extend(names.iter().cloned());
            ann_free_ty_vars(body, bound, out);
            bound.truncate(bound.len() - k);
        }
        _ => t.each_child(&mut |c| ann_free_ty_vars(c, bound, out)),
    }
}

// The bare type variables of a top-level function's signature (parameters,
// return, `given` constraints, and parametric-effect arguments), excluding any
// bound by a nested `forall` and any that sit at a row position. Each is an
// implicit `forall a`: it enters the body check rigid so the body cannot narrow
// it, and generalization re-quantifies it into the exported scheme. A constant
// has no signature arrow to quantify, so it yields nothing.
pub(super) fn signature_ty_vars(
    d: &Decl<Core>,
    data: &BTreeMap<String, super::DataInfo>,
) -> BTreeSet<String> {
    if d.konst {
        return BTreeSet::new();
    }
    let mut out = BTreeSet::new();
    let mut bound = Vec::new();
    for p in &d.params {
        if let Some(t) = &p.ty {
            ann_free_ty_vars(t, &mut bound, &mut out);
        }
    }
    if let Some(t) = &d.ret {
        ann_free_ty_vars(t, &mut bound, &mut out);
    }
    for c in &d.constraints {
        ann_free_ty_vars(&c.ty, &mut bound, &mut out);
    }
    if let Some(ls) = &d.eff {
        for al in ls {
            for a in &al.args {
                ann_free_ty_vars(a, &mut bound, &mut out);
            }
        }
    }
    let mut rows = BTreeSet::new();
    for p in &d.params {
        if let Some(t) = &p.ty {
            ann_row_var_names(t, data, &mut rows);
        }
    }
    if let Some(t) = &d.ret {
        ann_row_var_names(t, data, &mut rows);
    }
    for c in &d.constraints {
        ann_row_var_names(&c.ty, data, &mut rows);
    }
    for r in &rows {
        out.remove(r.as_str());
    }
    out
}

pub(super) fn annotation_scheme(
    d: &Decl<Core>,
    data: &BTreeMap<String, super::DataInfo>,
) -> Option<Type> {
    if d.konst {
        return None;
    }
    let annots: Vec<&ast::Ty> = d
        .params
        .iter()
        .map(|p| p.ty.as_ref())
        .collect::<Option<_>>()?;
    let ret = d.ret.as_ref()?;
    // Classify the annotation's free names into row variables and type variables
    // by where they appear, then convert with that row-variable set so a name at
    // a row position lowers to a row uniformly (an arrow tail and a `Cmd(a, e)`
    // slot agree). Quantify each with the binder for its sort.
    let mut row_names = BTreeSet::new();
    for t in &annots {
        ann_row_var_names(t, data, &mut row_names);
    }
    ann_row_var_names(ret, data, &mut row_names);
    let pt: Vec<Type> = annots
        .into_iter()
        .map(|t| saturate_cons(convert_data_rp(t, &row_names), data))
        .collect();
    let rt = saturate_cons(convert_data_rp(ret, &row_names), data);
    let mut tvars = BTreeSet::new();
    let mut rvars = BTreeSet::new();
    for t in &pt {
        collect_type_vars(t, &mut tvars);
        collect_row_vars(t, &mut rvars);
    }
    collect_type_vars(&rt, &mut tvars);
    collect_row_vars(&rt, &mut rvars);
    let mut out = wrap_forall(&tvars.into_iter().collect::<Vec<_>>(), Type::fun(pt, rt));
    for v in rvars.into_iter().rev() {
        out = Type::RowForall(v, Box::new(out));
    }
    Some(out)
}

pub(super) fn fn_stub(d: &Decl<Core>, data: &BTreeMap<String, super::DataInfo>) -> Type {
    // A constant's stub is its value type: the annotation if given, else a
    // fresh monovar refined when the body is inferred.
    if d.konst {
        return d.ret.as_ref().map_or_else(
            || Type::Var(Sym::fresh()),
            |ann| {
                let t = saturate_cons(convert_data(ann), data);
                let mut vars = BTreeSet::new();
                collect_type_vars(&t, &mut vars);
                wrap_forall(&vars.into_iter().collect::<Vec<_>>(), t)
            },
        );
    }
    if let Some(scheme) = annotation_scheme(d, data) {
        return scheme;
    }
    // Fresh, unforgeable placeholder type vars for the stub scheme, minted from
    // the interner rather than manufactured as `s@{i}` text.
    let n = d.params.len();
    let vars: Vec<Sym> = (0..=n).map(|_| Sym::fresh()).collect();
    let pt: Vec<Type> = vars[..n].iter().map(|v| Type::Var(*v)).collect();
    let rt = Type::Var(vars[n]);
    wrap_forall(&vars, Type::fun(pt, rt))
}

const BUILTINS: &[(&str, &str)] = &[
    ("print", "forall a. (a) -> Unit ! {IO}"),
    ("println", "forall a. (a) -> Unit ! {IO}"),
    ("prim_print", "forall a. (a) -> Unit ! {IO}"),
    ("prim_println", "forall a. (a) -> Unit ! {IO}"),
    ("prim_read_int", "() -> Int ! {IO}"),
    ("prim_read_line", "() -> String ! {IO}"),
    ("prim_rand", "() -> Int ! {IO}"),
    ("srand", "(Int) -> Unit ! {IO}"),
    ("error", "forall a. (Int) -> a ! {Exn}"),
    ("fatal", "forall a. (String) -> a ! {Exn}"),
    ("to_float", "(Int) -> Float"),
    ("truncate", "(Float) -> Int"),
    ("floor_to_int", "(Float) -> Int"),
    ("ceil_to_int", "(Float) -> Int"),
    ("abs_float", "(Float) -> Float"),
    ("sqrt", "(Float) -> Float"),
    ("floor", "(Float) -> Float"),
    ("ceil", "(Float) -> Float"),
    ("round", "(Float) -> Float"),
    ("trunc", "(Float) -> Float"),
    ("sin", "(Float) -> Float"),
    ("cos", "(Float) -> Float"),
    ("tan", "(Float) -> Float"),
    ("asin", "(Float) -> Float"),
    ("acos", "(Float) -> Float"),
    ("atan", "(Float) -> Float"),
    ("sinh", "(Float) -> Float"),
    ("cosh", "(Float) -> Float"),
    ("tanh", "(Float) -> Float"),
    ("exp", "(Float) -> Float"),
    ("exp2", "(Float) -> Float"),
    ("expm1", "(Float) -> Float"),
    ("ln", "(Float) -> Float"),
    ("log2", "(Float) -> Float"),
    ("log10", "(Float) -> Float"),
    ("log1p", "(Float) -> Float"),
    ("cbrt", "(Float) -> Float"),
    ("pow_float", "(Float, Float) -> Float"),
    ("atan2", "(Float, Float) -> Float"),
    ("hypot", "(Float, Float) -> Float"),
    ("fmod", "(Float, Float) -> Float"),
    ("parse_float", "(String) -> Float"),
    ("show_float_prec", "(Float, Int) -> String"),
    ("probe_enabled", "(String) -> Bool"),
    ("concat", "(String, String) -> String"),
    ("str_len", "(String) -> Int"),
    ("str_eq", "(String, String) -> Bool"),
    ("str_cmp", "(String, String) -> Int"),
    // The interpolation display printer (`names::DISPLAY_FN`); total and
    // type-directed, elaborated by the display intercept rather than dispatched.
    ("__display", "forall a. (a) -> String"),
    ("show_int", "(Int) -> String"),
    ("show_i64", "(I64) -> String"),
    ("show_u64", "(U64) -> String"),
    ("show_bool", "(Bool) -> String"),
    ("show_float", "(Float) -> String"),
    ("substring", "(String, Int, Int) -> String"),
    ("char_at", "(String, Int) -> Int"),
    ("ord", "(Char) -> Int"),
    ("chr", "(Int) -> Char"),
    ("show_char", "(Char) -> String"),
    ("blake3", "(String) -> String"),
    ("parse_int", "(String) -> Option(Int)"),
    ("prim_getenv", "(String) -> String ! {IO}"),
    ("prim_read_file", "(String) -> String ! {IO}"),
    ("prim_read_bytes", "(String) -> Buf ! {IO}"),
    (
        "prim_write_bytes",
        "(String, Buf) -> Result(Unit, String) ! {IO}",
    ),
    (
        "write_file",
        "(String, String) -> Result(Unit, String) ! {IO}",
    ),
    ("prim_file_exists", "(String) -> Bool ! {IO}"),
    (
        "append_file",
        "(String, String) -> Result(Unit, String) ! {IO}",
    ),
    ("remove_file", "(String) -> Unit ! {IO}"),
    ("prim_store_get", "(String, String) -> String ! {IO}"),
    ("prim_store_put", "(String, String, String) -> Unit ! {IO}"),
    ("prim_store_has", "(String, String) -> Bool ! {IO}"),
    ("exit", "forall a. (Int) -> a"),
    ("system", "(String) -> Int ! {IO}"),
    ("eprint", "(String) -> Unit ! {IO}"),
    ("prim_args_count", "() -> Int ! {IO}"),
    ("prim_arg", "(Int) -> String ! {IO}"),
    ("prim_wall_now", "() -> Int ! {IO}"),
    ("prim_mono_now", "() -> Int ! {IO}"),
    ("to_i64", "(Int) -> I64"),
    ("to_u64", "(Int) -> U64"),
    ("int_of_i64", "(I64) -> Int"),
    ("int_of_u64", "(U64) -> Int"),
    ("i64_and", "(I64, I64) -> I64"),
    ("i64_or", "(I64, I64) -> I64"),
    ("i64_xor", "(I64, I64) -> I64"),
    ("i64_shl", "(I64, I64) -> I64"),
    ("i64_shr", "(I64, I64) -> I64"),
    ("u64_and", "(U64, U64) -> U64"),
    ("u64_or", "(U64, U64) -> U64"),
    ("u64_xor", "(U64, U64) -> U64"),
    ("u64_shl", "(U64, U64) -> U64"),
    ("u64_shr", "(U64, U64) -> U64"),
    ("array_new", "forall a. (Int, a) -> Array(a)"),
    ("array_empty", "forall a. () -> Array(a)"),
    ("array_len", "forall a. (Array(a)) -> Int"),
    ("array_get", "forall a. (Array(a), Int) -> a"),
    ("array_set", "forall a. (Array(a), Int, a) -> Array(a)"),
    ("array_push", "forall a. (Array(a), a) -> Array(a)"),
    ("array_pop", "forall a. (Array(a)) -> Array(a)"),
    ("string_of_array", "(Array(String)) -> String"),
    ("buf_empty", "() -> Buf"),
    ("buf_new", "(Int, Int) -> Buf"),
    ("buf_len", "(Buf) -> Int"),
    ("buf_get", "(Buf, Int) -> Int"),
    ("buf_set", "(Buf, Int, Int) -> Buf"),
    ("buf_push", "(Buf, Int) -> Buf"),
    ("buf_slice", "(Buf, Int, Int) -> Buf"),
    ("buf_cat", "(Buf, Buf) -> Buf"),
    ("buf_eq", "(Buf, Buf) -> Bool"),
    ("buf_cmp", "(Buf, Buf) -> Int"),
    ("buf_hash", "(Buf) -> String"),
    ("buf_of_string", "(String) -> Buf"),
    ("string_of_buf", "(Buf) -> String"),
    ("buf_utf8_valid", "(Buf) -> Bool"),
    ("string_of_bytes", "(Array(Int)) -> String"),
    ("byte_at", "(String, Int) -> Int"),
    ("byte_len", "(String) -> Int"),
    ("i64_add", "(I64, I64) -> I64"),
    ("i64_sub", "(I64, I64) -> I64"),
    ("i64_mul", "(I64, I64) -> I64"),
    ("u64_add", "(U64, U64) -> U64"),
    ("u64_sub", "(U64, U64) -> U64"),
    ("u64_mul", "(U64, U64) -> U64"),
    ("i64_div", "(I64, I64) -> I64"),
    ("i64_rem", "(I64, I64) -> I64"),
    ("i64_cmp", "(I64, I64) -> Int"),
    ("u64_div", "(U64, U64) -> U64"),
    ("u64_rem", "(U64, U64) -> U64"),
    ("u64_cmp", "(U64, U64) -> Int"),
];

// A builtin signature carries its latent effects on the arrow, and the env type
// keeps that row: a builtin is a function whose effects inference must attribute
// at every call site, exactly like a surface function's inferred row. The
// returned label list is the parsed row, checked by the signature-parsing tests.
fn parse_sig(name: &str, sig: &str) -> Result<(Type, Vec<String>), TypeError> {
    let (tokens, _) = lex_raw(sig).map_err(|e| TypeError::Ice {
        msg: format!("builtin `{name}` signature `{sig}`: {e}"),
    })?;
    let ty = TypeSigParser::new()
        .parse(tokens)
        .map_err(|e| TypeError::Ice {
            msg: format!("builtin `{name}` signature `{sig}`: {e:?}"),
        })?;
    let effs = sig_row(&ty);
    Ok((convert_data(&ty), effs))
}

fn sig_row(t: &ast::Ty) -> Vec<String> {
    match t {
        ast::Ty::Forall(_, b) => sig_row(b),
        ast::Ty::Fun(_, ast::Row::Cons(ls, _), _) => ls.iter().map(|l| l.name.clone()).collect(),
        _ => vec![],
    }
}

fn base_env() -> Result<Env, TypeError> {
    BUILTINS
        .iter()
        .map(|(n, s)| Ok((Sym::from(*n), parse_sig(n, s)?.0)))
        .collect()
}

type BuildDataResult = (
    BTreeMap<String, DataInfo>,
    BTreeMap<String, CtorInfo>,
    BTreeMap<String, EffOpInfo>,
    Env,
);

pub(super) fn build_data(prog: &Program<Core>) -> Result<BuildDataResult, TypeError> {
    let mut data = BTreeMap::new();
    let mut ctors = BTreeMap::new();
    let mut env = base_env()?;
    // When the record/replay/durable machinery is imported, `print`/`println`
    // route through the interceptable `Output` capability instead of the ambient
    // `IO`, so the replay handlers can drop output during a replayed prefix (and
    // the incremental trace engine can capture a memo's output onto its trace).
    // Without it they keep their `{IO}` row, so the rest of the corpus (and any
    // `!{IO}` annotation) is untouched and a reified-handler body is never wrapped
    // in a world handler it cannot fuse through. This gate must stay in lockstep
    // with the desugarer and elaborator, which key output routing on the same two
    // driver families.
    if prog.fns.iter().any(|f| {
        names::REPLAY_DRIVERS.contains(&f.name.as_str())
            || names::INCR_REPLAY_DRIVERS.contains(&f.name.as_str())
    }) {
        for n in ["print", "println"] {
            env.insert(
                Sym::from(n),
                parse_sig(n, "forall a. (a) -> Unit ! {Output}")?.0,
            );
        }
    }
    // `Array(a)` is a built-in 1-parameter type: a heap cell with no surface
    // constructors, manipulated only through the `array_*` builtins.
    data.insert(
        "Array".to_string(),
        DataInfo {
            params: vec!["a".to_string()],
            param_kinds: vec![Kind::Type],
            ctors: vec![],
        },
    );
    // `Buf` is a built-in 0-parameter type: an unboxed byte buffer (a heap cell
    // with a raw-u8 payload, `runtime/prism_buffer.c`) with no surface
    // constructors, manipulated only through the `buf_*` builtins. It is the
    // storage under the stdlib `Bytes` type.
    data.insert(
        "Buf".to_string(),
        DataInfo {
            params: vec![],
            param_kinds: vec![],
            ctors: vec![],
        },
    );
    for dd in &prog.types {
        let kinds = normalize_kinds(&dd.params, &dd.param_kinds);
        // The `Row`-kinded parameters of this declaration; a field row that
        // names one of them refers to that row variable rather than an effect.
        let row_params: BTreeSet<Sym> = dd
            .params
            .iter()
            .zip(&kinds)
            .filter(|(_, k)| **k == Kind::Row)
            .map(|(p, _)| Sym::from(p))
            .collect();
        data.insert(
            dd.name.clone(),
            DataInfo {
                params: dd.params.clone(),
                param_kinds: kinds.clone(),
                ctors: dd.ctors.iter().map(|c| c.name.clone()).collect(),
            },
        );
        // The applied head `Cmd(a, e)`: a `Row`-kinded parameter rides in the
        // spine as `Type::Row(Var(..))`, matching how fields refer to it.
        let head_args: Vec<Type> = dd
            .params
            .iter()
            .zip(&kinds)
            .map(|(p, k)| match k {
                Kind::Row => Type::Row(EffRow::Var(Sym::from(p))),
                _ => Type::Var(Sym::from(p)),
            })
            .collect();
        for (tag, c) in dd.ctors.iter().enumerate() {
            let args: Vec<Type> = c
                .args
                .iter()
                .map(|t| convert_data_rp(t, &row_params))
                .collect();
            let fields: Vec<Sym> = c
                .fields
                .as_ref()
                .map(|fs| fs.iter().map(|(n, _)| Sym::from(n)).collect())
                .unwrap_or_default();
            ctors.insert(
                c.name.clone(),
                CtorInfo {
                    type_name: Sym::from(&dd.name),
                    params: dd.params.iter().map(Sym::from).collect(),
                    param_kinds: kinds.clone(),
                    args: args.clone(),
                    tag,
                    fields,
                },
            );
            let result = Type::Con(Sym::from(&dd.name), head_args.clone());
            let body = if args.is_empty() {
                result
            } else {
                Type::fun(args, result)
            };
            env.insert(Sym::from(&c.name), wrap_scheme(&dd.params, &kinds, body));
        }
    }
    let mut eff_ops = BTreeMap::new();
    for eff_decl in &prog.effects {
        for op in &eff_decl.ops {
            let params: Vec<Type> = op.params.iter().map(convert_data).collect();
            let ret = convert_data(&op.ret);
            eff_ops.insert(
                op.name.clone(),
                EffOpInfo {
                    effect_name: Sym::from(&eff_decl.name),
                    eff_params: eff_decl.params.iter().map(Sym::from).collect(),
                    params: params.clone(),
                    ret: ret.clone(),
                    grade: op.grade,
                },
            );
            // A var in the return type but in no parameter is instantiated fresh
            // per perform site. Desugar restricts such ops to final ctl arms.
            let mut pv = BTreeSet::new();
            for p in &params {
                collect_type_vars(p, &mut pv);
            }
            let mut rv = BTreeSet::new();
            collect_type_vars(&ret, &mut rv);
            let mut poly: Vec<Sym> = eff_decl.params.iter().map(Sym::from).collect();
            let extra: Vec<Sym> = rv
                .into_iter()
                .filter(|v| !pv.contains(v) && !poly.contains(v))
                .collect();
            poly.extend(extra);
            env.insert(
                Sym::from(&op.name),
                wrap_forall(&poly, Type::fun(params, ret)),
            );
        }
    }
    Ok((data, ctors, eff_ops, env))
}

// `var` state markers were lowered straight to existentials `Exist(0..)` by
// `convert_data`, so every read, write, handler, and initial value of one var
// already shares its existential. Return the high-water mark to reserve a pinned
// context slot for each; unused slots in any gap are harmless.
pub(super) fn seed_var_states(eff_ops: &BTreeMap<String, EffOpInfo>) -> u32 {
    let mut hi = None;
    for info in eff_ops.values() {
        for t in info.params.iter().chain(std::iter::once(&info.ret)) {
            max_state_ex(t, &mut hi);
        }
    }
    hi.map_or(0, |m| m + 1)
}

fn max_state_ex(t: &Type, hi: &mut Option<u32>) {
    match t {
        Type::Exist(n) => *hi = Some(hi.map_or(*n, |m: u32| m.max(*n))),
        Type::Forall(_, b) | Type::RowForall(_, b) => max_state_ex(b, hi),
        Type::Fun(ps, _, r) => {
            for p in ps {
                max_state_ex(p, hi);
            }
            max_state_ex(r, hi);
        }
        Type::Con(_, ps) | Type::Tuple(ps) => {
            for p in ps {
                max_state_ex(p, hi);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn builtin_signatures_parse() {
        for (name, sig) in super::BUILTINS {
            let (_, effs) = super::parse_sig(name, sig).expect("builtin signature parses");
            let want: &[&str] = match *name {
                "print" | "println" | "prim_print" | "prim_println" | "prim_read_int"
                | "prim_read_line" | "prim_rand" | "srand" | "system" | "eprint"
                | "prim_getenv" | "prim_read_file" | "prim_read_bytes" | "prim_write_bytes"
                | "write_file" | "prim_file_exists" | "append_file" | "remove_file"
                | "prim_store_get" | "prim_store_put" | "prim_store_has" | "prim_args_count"
                | "prim_arg" | "prim_wall_now" | "prim_mono_now" => &["IO"],
                "error" | "fatal" => &["Exn"],
                _ => &[],
            };
            assert_eq!(effs, want, "builtin {name} effect row drifted");
        }
    }

    #[test]
    fn forall_prefix_squashes() {
        let multi = super::parse_sig("t", "forall a b c. (a, b) -> c")
            .expect("signature parses")
            .0;
        assert_eq!(multi.show(), "forall a b c. (a, b) -> c");
        let nested = super::parse_sig("t", "forall a. forall b. (a, b) -> a")
            .expect("signature parses")
            .0;
        assert_eq!(nested.show(), "forall a b. (a, b) -> a");
    }
}
