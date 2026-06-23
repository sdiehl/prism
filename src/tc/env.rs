use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::{CtorInfo, DataInfo, EffOpInfo, Env, Tc};
use crate::error::TypeError;
use crate::lex::lex_raw;
use crate::sym::Sym;
use crate::syntax::ast::{self, Core, Decl, Program};
use crate::syntax::TypeSigParser;
use crate::types::ty::{EffRow, Effects, Label, Type};

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
            ast::Ty::Con(_, ts) | ast::Ty::Tuple(ts) => {
                ts.iter().try_for_each(|x| self.check_annot_rows(x, span))
            }
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
            if let Some(want) = known {
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
            for arg in &l.args {
                self.check_annot_rows(arg, span)?;
            }
        }
        Ok(())
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
            ast::Ty::Con(n, args) => Type::Con(
                Sym::from(n),
                args.iter().map(|x| self.convert_annot(x, a)).collect(),
            ),
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

fn ty_row_vars(t: &ast::Ty, out: &mut BTreeSet<String>) {
    match t {
        ast::Ty::Forall(_, b) => ty_row_vars(b, out),
        ast::Ty::Fun(ps, row, r) => {
            for p in ps {
                ty_row_vars(p, out);
            }
            if let ast::Row::Cons(_, Some(v)) = row {
                out.insert(v.clone());
            }
            ty_row_vars(r, out);
        }
        ast::Ty::Con(_, args) => args.iter().for_each(|a| ty_row_vars(a, out)),
        ast::Ty::Tuple(ts) => ts.iter().for_each(|t| ty_row_vars(t, out)),
        _ => {}
    }
}

fn data_row(row: &ast::Row) -> EffRow {
    match row {
        ast::Row::Empty => EffRow::Empty,
        ast::Row::Cons(ls, tl) => {
            let base = tl
                .as_ref()
                .map_or(EffRow::Empty, |v| EffRow::Var(Sym::from(v)));
            ls.iter().rev().fold(base, |acc, l| {
                let lab = Label {
                    name: Sym::from(&l.name),
                    args: l.args.iter().map(convert_data).collect(),
                };
                EffRow::Extend(lab, Box::new(acc))
            })
        }
    }
}

pub(super) fn convert_data(t: &ast::Ty) -> Type {
    match t {
        ast::Ty::Int => Type::Int,
        ast::Ty::I64 => Type::I64,
        ast::Ty::U64 => Type::U64,
        ast::Ty::Bool => Type::Bool,
        ast::Ty::Unit => Type::Unit,
        ast::Ty::Float => Type::Float,
        ast::Ty::Char => Type::Char,
        ast::Ty::Str => Type::Str,
        ast::Ty::Var(n) => Type::Var(Sym::from(n)),
        ast::Ty::State(n) => Type::Exist(*n),
        ast::Ty::Forall(names, body) => wrap_forall(
            &names.iter().map(Sym::from).collect::<Vec<_>>(),
            convert_data(body),
        ),
        ast::Ty::Fun(ps, row, r) => Type::fun_eff(
            ps.iter().map(convert_data).collect(),
            data_row(row),
            convert_data(r),
        ),
        ast::Ty::Con(n, args) => Type::Con(Sym::from(n), args.iter().map(convert_data).collect()),
        ast::Ty::App(v, args) => Type::apps(
            Type::Var(Sym::from(v)),
            args.iter().map(convert_data).collect(),
        ),
        ast::Ty::Tuple(ts) => Type::Tuple(ts.iter().map(convert_data).collect()),
    }
}

pub(super) fn wrap_forall(params: &[Sym], body: Type) -> Type {
    let mut out = body;
    for p in params.iter().rev() {
        out = Type::Forall(*p, Box::new(out));
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
        Type::Forall(_, b) | Type::RowForall(_, b) => collect_row_vars(b, out),
        _ => {}
    }
}

pub(super) fn fn_stub(d: &Decl<Core>) -> Type {
    // A constant's stub is its value type: the annotation if given, else a
    // fresh monovar refined when the body is inferred.
    if d.konst {
        return d.ret.as_ref().map_or_else(
            || Type::Var(Sym::fresh()),
            |ann| {
                let t = convert_data(ann);
                let mut vars = BTreeSet::new();
                collect_type_vars(&t, &mut vars);
                wrap_forall(&vars.into_iter().collect::<Vec<_>>(), t)
            },
        );
    }
    let n = d.params.len();
    let annots: Option<Vec<_>> = d.params.iter().map(|p| p.ty.as_ref()).collect();
    if let Some(annots) = annots {
        if let Some(ret) = &d.ret {
            let pt: Vec<Type> = annots.into_iter().map(convert_data).collect();
            let rt = convert_data(ret);
            let mut vars = BTreeSet::new();
            for t in &pt {
                collect_type_vars(t, &mut vars);
            }
            collect_type_vars(&rt, &mut vars);
            let sorted: Vec<Sym> = vars.into_iter().collect();
            return wrap_forall(&sorted, Type::fun(pt, rt));
        }
    }
    // Fresh, unforgeable placeholder type vars for the stub scheme, minted from
    // the interner rather than manufactured as `s@{i}` text.
    let vars: Vec<Sym> = (0..=n).map(|_| Sym::fresh()).collect();
    let pt: Vec<Type> = vars[..n].iter().map(|v| Type::Var(*v)).collect();
    let rt = Type::Var(vars[n]);
    wrap_forall(&vars, Type::fun(pt, rt))
}

const BUILTINS: &[(&str, &str)] = &[
    ("print", "forall a. (a) -> Unit ! {IO}"),
    ("println", "forall a. (a) -> Unit ! {IO}"),
    ("read_int", "() -> Int ! {IO}"),
    ("read_line", "() -> String ! {IO}"),
    ("rand", "() -> Int ! {IO}"),
    ("srand", "(Int) -> Unit ! {IO}"),
    ("error", "forall a. (Int) -> a ! {Exn}"),
    ("to_float", "(Int) -> Float"),
    ("truncate", "(Float) -> Int"),
    ("floor_to_int", "(Float) -> Int"),
    ("ceil_to_int", "(Float) -> Int"),
    ("abs_float", "(Float) -> Float"),
    ("sqrt", "(Float) -> Float"),
    ("sin", "(Float) -> Float"),
    ("cos", "(Float) -> Float"),
    ("exp", "(Float) -> Float"),
    ("ln", "(Float) -> Float"),
    ("pow_float", "(Float, Float) -> Float"),
    ("parse_float", "(String) -> Float"),
    ("show_float_prec", "(Float, Int) -> String"),
    ("concat", "(String, String) -> String"),
    ("str_len", "(String) -> Int"),
    ("str_eq", "(String, String) -> Bool"),
    ("str_cmp", "(String, String) -> Int"),
    ("show", "forall a. (a) -> String"),
    ("show_int", "(Int) -> String"),
    ("show_bool", "(Bool) -> String"),
    ("show_float", "(Float) -> String"),
    ("substring", "(String, Int, Int) -> String"),
    ("char_at", "(String, Int) -> Int"),
    ("ord", "(Char) -> Int"),
    ("chr", "(Int) -> Char"),
    ("show_char", "(Char) -> String"),
    ("parse_int", "(String) -> Option(Int)"),
    ("getenv", "(String) -> String"),
    ("read_file", "(String) -> String"),
    ("write_file", "(String, String) -> Result(Unit, String)"),
    ("file_exists", "(String) -> Bool"),
    ("append_file", "(String, String) -> Result(Unit, String)"),
    ("remove_file", "(String) -> Unit"),
    ("exit", "forall a. (Int) -> a"),
    ("system", "(String) -> Int ! {IO}"),
    ("eprint", "(String) -> Unit ! {IO}"),
    ("args_count", "() -> Int"),
    ("arg", "(Int) -> String"),
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

// A builtin signature carries its latent effects on the arrow. The row feeds
// the attribution table below; the env keeps the bare arrow, matching how
// surface fn annotations split the declared row from the type.
fn parse_sig(name: &str, sig: &str) -> Result<(Type, Vec<String>), TypeError> {
    let (tokens, _) = lex_raw(sig).map_err(|e| TypeError::Ice {
        msg: format!("builtin `{name}` signature `{sig}`: {e}"),
    })?;
    let mut ty = TypeSigParser::new()
        .parse(tokens)
        .map_err(|e| TypeError::Ice {
            msg: format!("builtin `{name}` signature `{sig}`: {e:?}"),
        })?;
    let effs = take_sig_row(&mut ty);
    Ok((convert_data(&ty), effs))
}

fn take_sig_row(t: &mut ast::Ty) -> Vec<String> {
    match t {
        ast::Ty::Forall(_, b) => take_sig_row(b),
        ast::Ty::Fun(_, row, _) => match std::mem::replace(row, ast::Row::Empty) {
            ast::Row::Empty => vec![],
            ast::Row::Cons(ls, _) => ls.into_iter().map(|l| l.name).collect(),
        },
        _ => vec![],
    }
}

fn base_env() -> Result<Env, TypeError> {
    BUILTINS
        .iter()
        .map(|(n, s)| Ok((Sym::from(*n), parse_sig(n, s)?.0)))
        .collect()
}

pub(crate) fn builtin_effects() -> &'static BTreeMap<String, Effects> {
    static MAP: std::sync::OnceLock<BTreeMap<String, Effects>> = std::sync::OnceLock::new();
    MAP.get_or_init(|| {
        BUILTINS
            .iter()
            .filter_map(|(n, s)| {
                // A malformed signature is reported by `base_env` during
                // `check`; here we cannot return through the static, so we skip.
                let effs = parse_sig(n, s).ok()?.1;
                (!effs.is_empty())
                    .then(|| ((*n).to_string(), effs.into_iter().map(Sym::from).collect()))
            })
            .collect()
    })
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
    // `Array(a)` is a built-in 1-parameter type: a heap cell with no surface
    // constructors, manipulated only through the `array_*` builtins.
    data.insert(
        "Array".to_string(),
        DataInfo {
            params: vec!["a".to_string()],
            ctors: vec![],
        },
    );
    for dd in &prog.types {
        data.insert(
            dd.name.clone(),
            DataInfo {
                params: dd.params.clone(),
                ctors: dd.ctors.iter().map(|c| c.name.clone()).collect(),
            },
        );
        for (tag, c) in dd.ctors.iter().enumerate() {
            let args: Vec<Type> = c.args.iter().map(convert_data).collect();
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
                    args: args.clone(),
                    tag,
                    fields,
                },
            );
            let result = Type::Con(
                Sym::from(&dd.name),
                dd.params.iter().map(|p| Type::Var(Sym::from(p))).collect(),
            );
            let body = if args.is_empty() {
                result
            } else {
                Type::fun(args, result)
            };
            env.insert(
                Sym::from(&c.name),
                wrap_forall(&dd.params.iter().map(Sym::from).collect::<Vec<_>>(), body),
            );
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
                "print" | "println" | "read_int" | "read_line" | "rand" | "srand" | "system"
                | "eprint" => &["IO"],
                "error" => &["Exn"],
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
