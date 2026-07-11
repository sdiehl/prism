use super::ops::low_prec_operand;
use crate::syntax::ast::{Expr, Marker, Sugar, S};

pub(super) const fn is_with_call(args: &[S<Expr>]) -> bool {
    matches!(args.last(), Some(a) if matches!(a.node, Expr::Lam(..)) && a.synth)
}

// A `Marker::Try` call head restores `e?`: the receiver is its single argument.
fn try_recv<'a>(f: &S<Expr>, args: &'a [S<Expr>]) -> Option<&'a S<Expr>> {
    match (&f.node, args) {
        (Expr::Marker(Marker::Try), [recv]) => Some(recv),
        _ => None,
    }
}

// UFCS dot calls carry the synthetic-span marker on the callee var. That is
// how the formatter restores `recv.f(args)` instead of `f(recv, args)`.
pub(super) type DotCall<'a> = (&'a str, &'a S<Expr>, &'a [S<Expr>]);

pub(super) fn dot_parts<'a>(f: &'a S<Expr>, args: &'a [S<Expr>]) -> Option<DotCall<'a>> {
    match &f.node {
        Expr::Var(name) if f.synth && !args.is_empty() => Some((name, &args[0], &args[1..])),
        _ => None,
    }
}

// The structural shape of a call `f(args)` once its head is decoded. Both the
// flat/break printer (`fmt_call_flat`) and the inline printer decode through
// this one classifier so they can never disagree on how a call head reads; a
// missing arm here once let the break path drop a `using` clause, re-emitting
// `f(a, using I)` as `f(using I)(a)` and breaking format round-trip.
pub(super) enum CallShape<'a> {
    Recv(&'a S<Expr>),                              // `recv?`
    Dot(DotCall<'a>),                               // `recv.name(rest)`
    Inst(&'a S<Expr>, &'a [String], &'a [S<Expr>]), // `inner(args, using names)`
    Plain(&'a S<Expr>, &'a [S<Expr>]),              // `f(args)`
}

// Decode a call head into its `CallShape`. Ordering is priority: a `?` receiver,
// then a UFCS dot call, then explicit instance selection, then a plain call.
pub(super) fn call_shape<'a>(f: &'a S<Expr>, args: &'a [S<Expr>]) -> CallShape<'a> {
    if let Some(recv) = try_recv(f, args) {
        return CallShape::Recv(recv);
    }
    if let Some(dot) = dot_parts(f, args) {
        return CallShape::Dot(dot);
    }
    if let Expr::Inst(inner, names) = &f.node {
        return CallShape::Inst(inner, names, args);
    }
    CallShape::Plain(f, args)
}

// A dot receiver must stay postfix-tight. Anything looser is parenthesized.
pub(super) const fn dot_recv_parens(e: &Expr) -> bool {
    low_prec_operand(e)
        || matches!(
            e,
            Expr::Bin(..) | Expr::Handle(..) | Expr::Sugar(Sugar::Assign(..))
        )
}

// `(b.f)(1)` calls the field closure. Bare `b.f(1)` reparses as UFCS f(b, 1).
pub(super) const fn callee_parens(e: &Expr) -> bool {
    low_prec_operand(e) || matches!(e, Expr::Handle(..) | Expr::FieldAccess(..))
}

// Wrap an already-rendered operand in parens when the surrounding precedence
// demands it.
pub(super) fn paren_if(parens: bool, s: String) -> String {
    if parens {
        format!("({s})")
    } else {
        s
    }
}
