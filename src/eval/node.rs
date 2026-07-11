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
    let mut binds = Vec::new();
    let mut cur = c;
    while let Comp::Bind(m, x, n) = cur {
        binds.push((lower(m), *x));
        cur = n;
    }
    let mut acc = Rc::new(node(cur));
    for (m, x) in binds.into_iter().rev() {
        acc = Rc::new(Node::Bind(m, x, acc));
    }
    acc
}

fn node(c: &Comp) -> Node {
    match c {
        Comp::Return(v) => Node::Return(atom_of(v)),
        Comp::Bind(m, x, n) => Node::Bind(lower(m), *x, lower(n)),
        Comp::Force(v) => Node::Force(atom_of(v)),
        Comp::Lam(ps, b) => Node::Lam(Rc::from(ps.as_slice()), lower(b)),
        Comp::App(m, args) => Node::App(lower(m), args.iter().map(atom_of).collect()),
        Comp::If(v, t, e) => Node::If(atom_of(v), lower(t), lower(e)),
        Comp::Prim(op, a, b) => Node::Prim(*op, atom_of(a), atom_of(b)),
        Comp::Call(n, args) => Node::Call(*n, args.iter().map(atom_of).collect()),
        Comp::Io(op, args) => match op {
            IoOp::Print | IoOp::PrintF | IoOp::PrintS => Node::Print(atom_of(&args[0])),
            IoOp::PrintNl => Node::PrintNl,
            IoOp::ReadInt => Node::ReadInt,
            IoOp::ReadLine => Node::ReadLine,
            IoOp::Rand => Node::Rand,
            IoOp::Srand => Node::Srand(atom_of(&args[0])),
        },
        Comp::Error(v) => Node::Error(atom_of(v)),
        Comp::Case(v, arms) => Node::Case(
            atom_of(v),
            arms.iter().map(|(p, b)| (p.clone(), lower(b))).collect(),
        ),
        Comp::FloatBuiltin(n, v) => Node::FloatBuiltin(*n, atom_of(v)),
        Comp::Neg(l, v) => Node::Neg(*l, atom_of(v)),
        Comp::UnboxedProject(_, _) => unreachable!("unboxed record projection is not lowered yet"),
        Comp::Do(op, args) => Node::Do(*op, args.iter().map(atom_of).collect()),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Node::Handle(Rc::new(HandleInfo {
            body: lower(body),
            ops: ops
                .iter()
                .map(|op| (op.name, (op.params.clone(), op.resume, lower(&op.body))))
                .collect(),
            return_var: *return_var,
            return_body: return_body.as_deref().map(lower),
        })),
        Comp::Mask(ops, b) => Node::Mask(Rc::from(ops.as_slice()), lower(b)),
        Comp::StrBuiltin(n, args) => Node::StrBuiltin(*n, args.iter().map(atom_of).collect()),
        // The interpreter runs un-lowered core; Dup/Drop/WithReuse/Reuse and the
        // mutable-cell Ref ops are injected only by codegen-side lowering (RC
        // reuse, var erasure) and must never reach here. Masking them to a silent
        // sink would hide the invariant breaking.
        Comp::Dup(_)
        | Comp::Drop(_)
        | Comp::WithReuse { .. }
        | Comp::Reuse(..)
        | Comp::RefNew(_)
        | Comp::RefGet(_)
        | Comp::RefSet(..) => {
            unreachable!("lowering-only node reached the interpreter; it runs un-lowered core")
        }
    }
}

fn atom_of(v: &Value) -> Atom {
    match v {
        Value::Var(x) => Atom::Var(*x),
        Value::Int(n) => Atom::Int(*n),
        Value::I64(n) => Atom::I64(*n),
        Value::U64(n) => Atom::U64(*n),
        Value::Float(f) => Atom::Float(*f),
        Value::Bool(b) => Atom::Bool(*b),
        Value::Unit => Atom::Unit,
        Value::Str(s) => Atom::Str(s.clone()),
        Value::Thunk(c) => Atom::Thunk(lower(c)),
        Value::Ctor(n, _, vs) => Atom::Ctor(*n, vs.iter().map(atom_of).collect()),
        // An unboxed tuple is a tuple to the interpreter: the reference semantics
        // are identical; only native code generation realizes the heap-cell-free
        // layout.
        Value::Tuple(vs) | Value::UnboxedTuple(vs) => Atom::Tuple(vs.iter().map(atom_of).collect()),
        // Unboxed records and their projection are not lowered past elaboration
        // yet (elaboration rejects them), so no such Core value reaches the
        // interpreter.
        Value::UnboxedRecord(_) => unreachable!("unboxed records are not lowered yet"),
    }
}
