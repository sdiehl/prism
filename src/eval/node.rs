//! The lowered interpreter IR: Core compiled once into Rc-linked nodes, plus the
//! lowering from `core` values and computations into that graph.

use std::collections::BTreeMap;
use std::rc::Rc;

use crate::core::builtins::{Builtin, FloatOp};
use crate::core::{Comp, CoreOp, CorePat, IoOp, NegLane, Value};
use crate::sym::Sym;

pub type Cmp = Rc<Node>;

// Core lowered once into Rc-linked nodes so the machine can hold subterms in
// heap frames without deep-cloning them on every step.
#[derive(Debug)]
pub enum Node {
    Return(Atom),
    Bind(Cmp, Sym, Cmp),
    Force(Atom),
    Lam(Rc<[Sym]>, Cmp),
    App(Cmp, Rc<[Atom]>),
    If(Atom, Cmp, Cmp),
    Prim(CoreOp, Atom, Atom),
    Call(Sym, Vec<Atom>),
    Print(Atom),
    PrintNl,
    ReadInt,
    ReadLine,
    Rand,
    Srand(Atom),
    Error(Atom),
    Case(Atom, Vec<(CorePat, Cmp)>),
    FloatBuiltin(FloatOp, Atom),
    Neg(NegLane, Atom),
    Do(Sym, Vec<Atom>),
    Handle(Rc<HandleInfo>),
    Mask(Rc<[Sym]>, Cmp),
    StrBuiltin(Builtin, Vec<Atom>),
    // Verification-only semantics for Core forms that exist after effect
    // lowering / RC / reuse. Ordinary source interpretation never constructs
    // these nodes; `lower_runtime` is the explicit opt-in seam.
    RcNoop(Atom),
    WithReuse { token: Sym, freed: Atom, body: Cmp },
    Reuse(Sym, Atom),
    InitAt(Atom, Atom),
    RefNew(Atom),
    RefGet(Atom),
    RefSet(Atom, Atom),
    Bump(Vec<Atom>),
    ArenaEnter,
    ArenaExit(Vec<Atom>),
}

#[derive(Debug)]
pub enum Atom {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Thunk(Cmp),
    Ctor(Sym, Vec<Self>),
    Tuple(Vec<Self>),
}

#[derive(Debug)]
pub struct HandleInfo {
    pub(super) body: Cmp,
    pub(super) ops: BTreeMap<Sym, (Vec<Sym>, Sym, Cmp)>,
    pub(super) return_var: Option<Sym>,
    pub(super) return_body: Option<Cmp>,
}

pub(super) fn lower(c: &Comp) -> Cmp {
    lower_with_runtime(c, false)
}

/// Lower Core for the verification-only post-lowering evaluator.
pub(super) fn lower_runtime(c: &Comp) -> Cmp {
    lower_with_runtime(c, true)
}

fn lower_with_runtime(c: &Comp, runtime: bool) -> Cmp {
    let mut binds = Vec::new();
    let mut cur = c;
    while let Comp::Bind(m, x, n) = cur {
        binds.push((lower_with_runtime(m, runtime), *x));
        cur = n;
    }
    let mut acc = Rc::new(node(cur, runtime));
    for (m, x) in binds.into_iter().rev() {
        acc = Rc::new(Node::Bind(m, x, acc));
    }
    acc
}

fn node(c: &Comp, runtime: bool) -> Node {
    match c {
        Comp::Return(v) => Node::Return(atom_of(v, runtime)),
        Comp::Bind(m, x, n) => Node::Bind(
            lower_with_runtime(m, runtime),
            *x,
            lower_with_runtime(n, runtime),
        ),
        Comp::Force(v) => Node::Force(atom_of(v, runtime)),
        Comp::Lam(ps, b) => Node::Lam(Rc::from(ps.as_slice()), lower_with_runtime(b, runtime)),
        Comp::App(m, args) => Node::App(
            lower_with_runtime(m, runtime),
            args.iter().map(|value| atom_of(value, runtime)).collect(),
        ),
        Comp::If(v, t, e) => Node::If(
            atom_of(v, runtime),
            lower_with_runtime(t, runtime),
            lower_with_runtime(e, runtime),
        ),
        Comp::Prim(op, a, b) => Node::Prim(*op, atom_of(a, runtime), atom_of(b, runtime)),
        Comp::Call(n, args) => Node::Call(
            *n,
            args.iter().map(|value| atom_of(value, runtime)).collect(),
        ),
        Comp::Io(op, args) => match op {
            IoOp::Print | IoOp::PrintF | IoOp::PrintS => Node::Print(atom_of(&args[0], runtime)),
            IoOp::PrintNl => Node::PrintNl,
            IoOp::ReadInt => Node::ReadInt,
            IoOp::ReadLine => Node::ReadLine,
            IoOp::Rand => Node::Rand,
            IoOp::Srand => Node::Srand(atom_of(&args[0], runtime)),
        },
        Comp::Error(v) => Node::Error(atom_of(v, runtime)),
        Comp::Case(v, arms) => Node::Case(
            atom_of(v, runtime),
            arms.iter()
                .map(|(pattern, body)| (pattern.clone(), lower_with_runtime(body, runtime)))
                .collect(),
        ),
        Comp::FloatBuiltin(n, v) => Node::FloatBuiltin(*n, atom_of(v, runtime)),
        Comp::Neg(l, v) => Node::Neg(*l, atom_of(v, runtime)),
        Comp::UnboxedProject(_, _) => unreachable!("unboxed record projection is not lowered yet"),
        Comp::Do(op, args) => Node::Do(
            *op,
            args.iter().map(|value| atom_of(value, runtime)).collect(),
        ),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Node::Handle(Rc::new(HandleInfo {
            body: lower_with_runtime(body, runtime),
            ops: ops
                .iter()
                .map(|op| {
                    (
                        op.name,
                        (
                            op.params.clone(),
                            op.resume,
                            lower_with_runtime(&op.body, runtime),
                        ),
                    )
                })
                .collect(),
            return_var: *return_var,
            return_body: return_body
                .as_deref()
                .map(|body| lower_with_runtime(body, runtime)),
        })),
        Comp::Mask(ops, b) => Node::Mask(Rc::from(ops.as_slice()), lower_with_runtime(b, runtime)),
        Comp::StrBuiltin(Builtin::Bump, args) if runtime => {
            Node::Bump(args.iter().map(|value| atom_of(value, runtime)).collect())
        }
        // The region brackets the arena pass emits around a `with_arena`
        // activation. The verifier has no regions (values are Rust data), so
        // enter yields a placeholder token and exit passes the result through;
        // both are unobservable, exactly the native contract.
        Comp::StrBuiltin(Builtin::ArenaEnter, _) if runtime => Node::ArenaEnter,
        Comp::StrBuiltin(Builtin::ArenaExit, args) if runtime => {
            Node::ArenaExit(args.iter().map(|value| atom_of(value, runtime)).collect())
        }
        Comp::StrBuiltin(n, args) => Node::StrBuiltin(
            *n,
            args.iter().map(|value| atom_of(value, runtime)).collect(),
        ),
        // The interpreter runs un-lowered core; Dup/Drop/WithReuse/Reuse and the
        // mutable-cell Ref ops are injected only by codegen-side lowering (RC
        // reuse, var erasure) and must never reach here. Masking them to a silent
        // sink would hide the invariant breaking.
        Comp::Dup(value) | Comp::Drop(value) if runtime => Node::RcNoop(atom_of(value, runtime)),
        Comp::WithReuse { token, freed, body } if runtime => Node::WithReuse {
            token: *token,
            freed: atom_of(freed, runtime),
            body: lower_with_runtime(body, runtime),
        },
        Comp::Reuse(token, value) if runtime => Node::Reuse(*token, atom_of(value, runtime)),
        Comp::InitAt(cell, value) if runtime => {
            Node::InitAt(atom_of(cell, runtime), atom_of(value, runtime))
        }
        Comp::RefNew(value) if runtime => Node::RefNew(atom_of(value, runtime)),
        Comp::RefGet(value) if runtime => Node::RefGet(atom_of(value, runtime)),
        Comp::RefSet(cell, value) if runtime => {
            Node::RefSet(atom_of(cell, runtime), atom_of(value, runtime))
        }
        Comp::Dup(_)
        | Comp::Drop(_)
        | Comp::WithReuse { .. }
        | Comp::Reuse(..)
        | Comp::InitAt(..)
        | Comp::RefNew(_)
        | Comp::RefGet(_)
        | Comp::RefSet(..) => unreachable!(
            "lowering-only node reached the interpreter; use the explicit lowered verifier"
        ),
    }
}

fn atom_of(v: &Value, runtime: bool) -> Atom {
    match v {
        Value::Var(x) => Atom::Var(*x),
        Value::Int(n) => Atom::Int(*n),
        Value::I64(n) => Atom::I64(*n),
        Value::U64(n) => Atom::U64(*n),
        Value::Float(f) => Atom::Float(*f),
        Value::Bool(b) => Atom::Bool(*b),
        Value::Unit => Atom::Unit,
        Value::Str(s) => Atom::Str(s.clone()),
        Value::Thunk(c) => Atom::Thunk(lower_with_runtime(c, runtime)),
        Value::Ctor(n, _, vs) => {
            Atom::Ctor(*n, vs.iter().map(|value| atom_of(value, runtime)).collect())
        }
        // An unboxed tuple is a tuple to the interpreter: the reference semantics
        // are identical; only native code generation realizes the heap-cell-free
        // layout.
        Value::Tuple(vs) | Value::UnboxedTuple(vs) => {
            Atom::Tuple(vs.iter().map(|value| atom_of(value, runtime)).collect())
        }
        // Unboxed records and their projection are not lowered past elaboration
        // yet (elaboration rejects them), so no such Core value reaches the
        // interpreter.
        Value::UnboxedRecord(_) => unreachable!("unboxed records are not lowered yet"),
    }
}
