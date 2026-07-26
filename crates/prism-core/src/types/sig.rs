//! Builtin-signature parsing: the registry signature strings (`"(Float) ->
//! F32x4"`) lexed, parsed through the type-signature grammar, and converted
//! structurally into [`Type`]. Pure and environment-free, so the typed-Core
//! builder and verifier can parse intrinsic signatures without the checker.

use std::collections::BTreeSet;

use prism_common::sym::Sym;
use prism_syntax::ast;
use prism_syntax::error::TypeError;
use prism_syntax::kw;
use prism_syntax::lex::lex_raw;
use prism_syntax::TypeSigParser;

use crate::types::ty::{EffRow, Label};
use crate::types::Type;

/// [`parse_sig`] returning only the type, the shape the typed-Core intrinsic
/// tables consume.
///
/// # Errors
/// Fails when the signature does not lex, parse, or convert.
pub fn parse_checked_signature(name: &str, signature: &str) -> Result<Type, TypeError> {
    parse_sig(name, signature).map(|(ty, _)| ty)
}

pub fn convert_data(t: &ast::Ty) -> Type {
    convert_data_rp(t, &BTreeSet::new())
}

// The core of `convert_data`, aware of the current declaration's `Row`-kinded
// parameters `rp`. A variable named in `rp` is an effect row, so it lowers to
// `Type::Row(Var(..))` wherever it appears (notably as the argument at a
// `Row`-kinded position of a `Con`, `Cmd(a, e)`); every other name is a type
// variable, exactly as before. `rp` is empty for all non-data-field callers.
pub fn convert_data_rp(t: &ast::Ty, rp: &BTreeSet<Sym>) -> Type {
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
        // Usage rows are rejected in desugar before any annotation reaches
        // conversion; convert through the underlying type defensively.
        ast::Ty::Coeffect(inner, _) => convert_data_rp(inner, rp),
        ast::Ty::Forall(names, body) => wrap_forall(
            &names.iter().map(Sym::from).collect::<Vec<_>>(),
            convert_data_rp(body, rp),
        ),
        ast::Ty::Fun(ps, row, r) => Type::fun_eff(
            ps.iter().map(|p| convert_data_rp(p, rp)).collect(),
            data_row_rp(row, rp),
            convert_data_rp(r, rp),
        ),
        ast::Ty::Con(n, args) if n == kw::TY_OR_NULL && args.len() == 1 => {
            Type::OrNull(Box::new(convert_data_rp(&args[0], rp)))
        }
        ast::Ty::Con(n, args) => Type::Con(
            Sym::from(n),
            args.iter().map(|x| convert_data_rp(x, rp)).collect(),
        ),
        ast::Ty::App(v, args) => Type::apps(
            Type::Var(Sym::from(v)),
            args.iter().map(|x| convert_data_rp(x, rp)).collect(),
        ),
        ast::Ty::Tuple(ts) => Type::Tuple(ts.iter().map(|x| convert_data_rp(x, rp)).collect()),
        ast::Ty::UnboxedTuple(ts) => {
            Type::UnboxedTuple(ts.iter().map(|x| convert_data_rp(x, rp)).collect())
        }
        ast::Ty::UnboxedRecord(fs) => Type::UnboxedRecord(
            fs.iter()
                .map(|(n, x)| (Sym::from(n.as_str()), convert_data_rp(x, rp)))
                .collect(),
        ),
        ast::Ty::RowLit(row) => Type::Row(data_row_rp(row, rp)),
        ast::Ty::Nat(v) => Type::Nat(*v),
    }
}

// A builtin signature carries its latent effects on the arrow, and the env type
// keeps that row: a builtin is a function whose effects inference must attribute
// at every call site, exactly like a surface function's inferred row. The
// returned label list is the parsed row, checked by the signature-parsing tests.
pub fn parse_sig(name: &str, sig: &str) -> Result<(Type, Vec<String>), TypeError> {
    let (tokens, _) = lex_raw(sig).map_err(|e| TypeError::InternalInvariant {
        msg: format!("builtin `{name}` signature `{sig}`: {e}"),
    })?;
    let ty = TypeSigParser::new()
        .parse(tokens)
        .map_err(|e| TypeError::InternalInvariant {
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

pub fn wrap_forall(params: &[Sym], body: Type) -> Type {
    let mut out = body;
    for p in params.iter().rev() {
        out = Type::Forall(*p, Box::new(out));
    }
    out
}

// Lower a data-field row, given the current declaration's `Row`-kinded
// parameters. A label whose name is one of those parameters is not a concrete
// effect but the row variable itself, so it moves to the tail: both `! {e}` and
// `! {IO | e}` yield a row ending in `Var(e)`. Concrete labels stay in the
// prefix, their args lowered with the same row-parameter awareness.
pub fn data_row_rp(row: &ast::Row, rp: &BTreeSet<Sym>) -> EffRow {
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
    EffRow::canonical(concrete, base)
}
