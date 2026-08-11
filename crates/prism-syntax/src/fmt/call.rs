use super::ops::low_prec_operand;
use crate::ast::{Expr, Marker, Param, PathOp, PathStep, Sugar, Ty, S};
use crate::kw;
use crate::names;

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

// The field chain a lambda of the shape the path literal's getter takes reads
// off its own parameter, or `false` for any other body.
fn getter_fields<'a>(body: &'a Expr, out: &mut Vec<&'a str>) -> bool {
    match body {
        Expr::Var(v) => v == names::PATH_WHOLE,
        Expr::FieldAccess(base, f) => {
            if !getter_fields(&base.node, out) {
                return false;
            }
            out.push(f);
            true
        }
        _ => false,
    }
}

// The field steps a `#path a.b.c` literal expanded to, or `None` if this call is
// an ordinary one. The literal lowers to a `lens` call over two lambdas binding
// the whole and the part; those two binders carry the `@` sigil and so cannot be
// written in source, which is what makes the shape unforgeable and lets the
// formatter restore the literal without a marker node. Both halves are decoded
// and required to agree, so a call that merely resembles one is left alone.
fn path_steps<'a>(f: &S<Expr>, args: &'a [S<Expr>]) -> Option<(Anchor<'a>, Vec<&'a str>)> {
    let (Expr::Var(callee), [get, set]) = (&f.node, args) else {
        return None;
    };
    if callee != names::LENS_FN {
        return None;
    }
    let (Expr::Lam(gp, read), Expr::Lam(stp, write)) = (&get.node, &set.node) else {
        return None;
    };
    if gp.len() != 1
        || gp[0].name != names::PATH_WHOLE
        || stp.len() != 2
        || stp[0].name != names::PATH_WHOLE
        || stp[1].name != names::PATH_PART
        || stp[1].ty.is_some()
    {
        return None;
    }
    // An anchored literal (`#path Type.a.b`) annotates both `whole@` binders
    // with the bare anchor type; both halves must agree for the decode to hold.
    let anchor = param_anchor(&gp[0])?;
    if param_anchor(&stp[0])? != anchor {
        return None;
    }
    let mut fields = Vec::new();
    if !getter_fields(&read.node, &mut fields) || fields.is_empty() {
        return None;
    }
    let Expr::RecordUpdatePath(base, updates) = &write.node else {
        return None;
    };
    if !matches!(&base.node, Expr::Var(v) if v == names::PATH_WHOLE) {
        return None;
    }
    let [(steps, PathOp::Set(part))] = updates.as_slice() else {
        return None;
    };
    if !matches!(&part.node, Expr::Var(v) if v == names::PATH_PART) {
        return None;
    }
    let written: Vec<&str> = steps
        .iter()
        .map(|s| match s {
            PathStep::Field(f) => Some(f.as_str()),
            _ => None,
        })
        .collect::<Option<_>>()?;
    (written == fields).then_some((anchor, fields))
}

// `get().a.b := e` / `get().a.b <op>= e` restored from the synth
// `put({ get() | ... })` the ambient-state statement parses to. The callee and
// base must be the bare `put`/`get` the sugar spells; any other call, and any
// hand-written `put({ get() | ... })` (non-synth brace), is left alone.
pub(super) fn state_assign_parts<'a>(
    f: &S<Expr>,
    args: &'a [S<Expr>],
) -> Option<(&'a [PathStep], &'a PathOp)> {
    let (Expr::Var(callee), [arg]) = (&f.node, args) else {
        return None;
    };
    if callee != names::STATE_PUT || !arg.synth {
        return None;
    }
    let Expr::RecordUpdatePath(base, ups) = &arg.node else {
        return None;
    };
    let Expr::Call(g, g_args) = &base.node else {
        return None;
    };
    if !g_args.is_empty() || !matches!(&g.node, Expr::Var(n) if n == names::STATE_GET) {
        return None;
    }
    let [(steps, op)] = ups.as_slice() else {
        return None;
    };
    Some((steps, op))
}

// The annotation shapes a literal's `whole@` binder can carry: none (a plain
// literal) or the bare anchor type (`#path Type.a.b`). Anything else is not a
// literal's and fails the decode.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Anchor<'a> {
    Plain,
    Ty(&'a str),
}

fn param_anchor(p: &Param) -> Option<Anchor<'_>> {
    match &p.ty {
        None => Some(Anchor::Plain),
        Some(Ty::Con(name, args)) if args.is_empty() => Some(Anchor::Ty(name)),
        Some(_) => None,
    }
}

// `#path a.b.c` / `#path Type.a.b` as it is written in source.
fn fmt_path_lit(f: &S<Expr>, args: &[S<Expr>]) -> Option<String> {
    let (anchor, fs) = path_steps(f, args)?;
    let path = match anchor {
        Anchor::Ty(t) => format!("{t}{}{}", kw::DOT, fs.join(kw::DOT)),
        Anchor::Plain => fs.join(kw::DOT),
    };
    Some(format!("{}{} {path}", kw::HASH, kw::PATH))
}

// The structural shape of a call `f(args)` once its head is decoded. Both the
// flat/break printer (`fmt_call_flat`) and the inline printer decode through
// this one classifier so they can never disagree on how a call head reads; a
// missing arm here once let the break path drop a `using` clause, re-emitting
// `f(a, using I)` as `f(using I)(a)` and breaking format round-trip.
pub(super) enum CallShape<'a> {
    Path(String),                                   // `#path a.b.c`
    Recv(&'a S<Expr>),                              // `recv?`
    Dot(DotCall<'a>),                               // `recv.name(rest)`
    Inst(&'a S<Expr>, &'a [String], &'a [S<Expr>]), // `inner(args, using names)`
    Plain(&'a S<Expr>, &'a [S<Expr>]),              // `f(args)`
}

// Decode a call head into its `CallShape`. Ordering is priority: the optic
// literal (the most specific shape), then a `?` receiver, then a UFCS dot call,
// then explicit instance selection, then a plain call.
pub(super) fn call_shape<'a>(f: &'a S<Expr>, args: &'a [S<Expr>]) -> CallShape<'a> {
    if let Some(lit) = fmt_path_lit(f, args) {
        return CallShape::Path(lit);
    }
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
