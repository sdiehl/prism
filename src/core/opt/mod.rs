//! Mid-level Core-to-Core optimization tier.
//!
//! Each pass preserves observable behavior (the parity oracle gates it) and runs
//! above the interpreter/native fork, so a rewrite here lands identically on
//! every backend.
//!
//! `erase_newtypes`: a `newtype N = MkN(T)` is representationally identical to
//! `T`, so its one-field box is erased. Construction `MkN(v)` becomes `v`, and a
//! match `MkN(x) => body` becomes a plain rebind of `x` to the scrutinee (a
//! newtype is single-constructor, so its match is one irrefutable arm). The
//! surrounding logic, such as a derived `show` that prints `MkN(...)`, is
//! untouched, so only the representation changes, never the meaning.

use std::collections::BTreeSet;

use super::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program};

/// The constructor symbol of every `newtype` in the program (each a single-field
/// wrapper whose box this tier erases).
#[must_use]
pub fn newtype_ctors(prog: &Program<CorePhase>) -> BTreeSet<Sym> {
    prog.types
        .iter()
        .filter(|d| d.newtype)
        .filter_map(|d| d.ctors.first())
        .map(|c| Sym::from(&c.name))
        .collect()
}

/// Erase every newtype box from `core` (see module docs). A no-op when the
/// program declares no newtypes.
#[must_use]
pub fn erase_newtypes(core: &Core, nt: &BTreeSet<Sym>) -> Core {
    if nt.is_empty() {
        return core.clone();
    }
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| CoreFn {
                name: f.name,
                params: f.params.clone(),
                body: erase_comp(&f.body, nt),
            })
            .collect(),
    }
}

fn erase_value(v: &Value, nt: &BTreeSet<Sym>) -> Value {
    match v {
        // The newtype box is its single field: drop the wrapper.
        Value::Ctor(name, _, fields) if nt.contains(name) && fields.len() == 1 => {
            erase_value(&fields[0], nt)
        }
        Value::Ctor(name, tag, fields) => Value::Ctor(
            *name,
            *tag,
            fields.iter().map(|f| erase_value(f, nt)).collect(),
        ),
        Value::Tuple(fields) => Value::Tuple(fields.iter().map(|f| erase_value(f, nt)).collect()),
        Value::Thunk(c) => Value::Thunk(Box::new(erase_comp(c, nt))),
        _ => v.clone(),
    }
}

fn is_newtype_match(arms: &[(CorePat, Comp)], nt: &BTreeSet<Sym>) -> bool {
    arms.len() == 1 && matches!(&arms[0].0, CorePat::Ctor(n, bs) if nt.contains(n) && bs.len() == 1)
}

fn erase_comp(c: &Comp, nt: &BTreeSet<Sym>) -> Comp {
    let ev = |v: &Value| erase_value(v, nt);
    let ec = |c: &Comp| erase_comp(c, nt);
    let eb = |c: &Comp| Box::new(erase_comp(c, nt));
    match c {
        // A newtype match is one irrefutable arm: rebind the matched value (now
        // the inner value) and run the body.
        Comp::Case(v, arms) if is_newtype_match(arms, nt) => {
            let CorePat::Ctor(_, binders) = &arms[0].0 else {
                unreachable!("is_newtype_match")
            };
            let binder = binders[0].unwrap_or_else(|| Sym::from("_"));
            Comp::Bind(Box::new(Comp::Return(ev(v))), binder, eb(&arms[0].1))
        }
        Comp::Return(v) => Comp::Return(ev(v)),
        Comp::Bind(a, x, b) => Comp::Bind(eb(a), *x, eb(b)),
        Comp::Force(v) => Comp::Force(ev(v)),
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), eb(b)),
        Comp::App(f, args) => Comp::App(eb(f), args.iter().map(ev).collect()),
        Comp::If(c0, t, e) => Comp::If(ev(c0), eb(t), eb(e)),
        Comp::Prim(op, a, b) => Comp::Prim(*op, ev(a), ev(b)),
        Comp::Call(n, args) => Comp::Call(*n, args.iter().map(ev).collect()),
        Comp::Print(v) => Comp::Print(ev(v)),
        Comp::PrintF(v) => Comp::PrintF(ev(v)),
        Comp::PrintS(v) => Comp::PrintS(ev(v)),
        Comp::PrintNl => Comp::PrintNl,
        Comp::ReadInt => Comp::ReadInt,
        Comp::ReadLine => Comp::ReadLine,
        Comp::Rand => Comp::Rand,
        Comp::Srand(v) => Comp::Srand(ev(v)),
        Comp::Error(v) => Comp::Error(ev(v)),
        Comp::Case(v, arms) => Comp::Case(
            ev(v),
            arms.iter().map(|(p, b)| (p.clone(), ec(b))).collect(),
        ),
        Comp::FloatBuiltin(op, v) => Comp::FloatBuiltin(*op, ev(v)),
        Comp::Do(n, args) => Comp::Do(*n, args.iter().map(ev).collect()),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: eb(body),
            return_var: *return_var,
            return_body: return_body.as_ref().map(|b| eb(b)),
            ops: ops
                .iter()
                .map(|o| HandleOp {
                    name: o.name,
                    params: o.params.clone(),
                    resume: o.resume,
                    body: ec(&o.body),
                })
                .collect(),
        },
        Comp::Mask(es, b) => Comp::Mask(es.clone(), eb(b)),
        Comp::StrBuiltin(b, args) => Comp::StrBuiltin(*b, args.iter().map(ev).collect()),
        Comp::Dup(v) => Comp::Dup(ev(v)),
        Comp::Drop(v) => Comp::Drop(ev(v)),
        Comp::WithReuse { token, freed, body } => Comp::WithReuse {
            token: *token,
            freed: ev(freed),
            body: eb(body),
        },
        Comp::Reuse(t, v) => Comp::Reuse(*t, ev(v)),
        Comp::RefNew(v) => Comp::RefNew(ev(v)),
        Comp::RefGet(v) => Comp::RefGet(ev(v)),
        Comp::RefSet(a, b) => Comp::RefSet(ev(a), ev(b)),
    }
}
