use std::collections::{BTreeMap, BTreeSet};

use super::builtins::{Builtin, FloatOp};
use crate::names::ENTRY_POINT;
use crate::sym::Sym;
use crate::syntax::ast::BinOp;

// Primitive operators that survive elaboration. Short-circuit `&&`/`||` lower to
// `If` and never reach a `Prim`, so they have no variant here: a downstream pass
// cannot observe one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Addf,
    Subf,
    Mulf,
    Divf,
    Eqf,
    Nef,
    Ltf,
    Lef,
    Gtf,
    Gef,
}

impl CoreOp {
    // `None` for `&&`/`||`, which elaboration lowers to `If` rather than a `Prim`.
    #[must_use]
    pub const fn from_binop(op: BinOp) -> Option<Self> {
        Some(match op {
            BinOp::Add => Self::Add,
            BinOp::Sub => Self::Sub,
            BinOp::Mul => Self::Mul,
            BinOp::Div => Self::Div,
            BinOp::Rem => Self::Rem,
            BinOp::Eq => Self::Eq,
            BinOp::Ne => Self::Ne,
            BinOp::Lt => Self::Lt,
            BinOp::Le => Self::Le,
            BinOp::Gt => Self::Gt,
            BinOp::Ge => Self::Ge,
            BinOp::Addf => Self::Addf,
            BinOp::Subf => Self::Subf,
            BinOp::Mulf => Self::Mulf,
            BinOp::Divf => Self::Divf,
            BinOp::Eqf => Self::Eqf,
            BinOp::Nef => Self::Nef,
            BinOp::Ltf => Self::Ltf,
            BinOp::Lef => Self::Lef,
            BinOp::Gtf => Self::Gtf,
            BinOp::Gef => Self::Gef,
            // `And`/`Or` short-circuit and `Pow` lowers to a class method call;
            // none is a primitive core op.
            BinOp::And | BinOp::Or | BinOp::Pow => return None,
        })
    }
}

// Pattern shapes that survive match compilation. Literals, booleans, and record
// patterns are compiled away into `If`/`Prim` tests and ctor patterns upstream,
// so a `Case` arm can only test a ctor or tuple (or bind/ignore the whole
// scrutinee). Field positions are plain binders (`Some` names it, `None` ignores
// it); nested sub-patterns are always flattened out, so they cannot appear here.
#[derive(Clone, Debug)]
pub enum CorePat {
    Wild,
    Var(Sym),
    Ctor(Sym, Vec<Option<Sym>>),
    Tuple(Vec<Option<Sym>>),
}

#[derive(Clone, Debug)]
pub enum Value {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Thunk(Box<Comp>),
    Ctor(Sym, usize, Vec<Self>),
    Tuple(Vec<Self>),
}

#[derive(Clone, Debug)]
pub struct HandleOp {
    pub name: Sym,
    pub params: Vec<Sym>,
    pub resume: Sym,
    pub body: Comp,
}

#[derive(Clone, Debug)]
pub enum Comp {
    Return(Value),
    Bind(Box<Self>, Sym, Box<Self>),
    Force(Value),
    Lam(Vec<Sym>, Box<Self>),
    App(Box<Self>, Vec<Value>),
    If(Value, Box<Self>, Box<Self>),
    Prim(CoreOp, Value, Value),
    Call(Sym, Vec<Value>),
    Print(Value),
    PrintF(Value),
    PrintS(Value),
    PrintNl,
    ReadInt,
    ReadLine,
    Rand,
    Srand(Value),
    Error(Value),
    Case(Value, Vec<(CorePat, Self)>),
    FloatBuiltin(FloatOp, Value),
    Do(Sym, Vec<Value>),
    Handle {
        body: Box<Self>,
        return_var: Option<Sym>,
        return_body: Option<Box<Self>>,
        ops: Vec<HandleOp>,
    },
    Mask(Vec<Sym>, Box<Self>),
    StrBuiltin(Builtin, Vec<Value>),
    Dup(Value),
    Drop(Value),
    ReuseToken(Value),
    Reuse(Value, Value),
}

impl Comp {
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Return(_) => "Return",
            Self::Bind(..) => "Bind",
            Self::Force(_) => "Force",
            Self::Lam(..) => "Lam",
            Self::App(..) => "App",
            Self::If(..) => "If",
            Self::Prim(..) => "Prim",
            Self::Call(..) => "Call",
            Self::Print(_) => "Print",
            Self::PrintF(_) => "PrintF",
            Self::PrintS(_) => "PrintS",
            Self::PrintNl => "PrintNl",
            Self::ReadInt => "ReadInt",
            Self::ReadLine => "ReadLine",
            Self::Rand => "Rand",
            Self::Srand(_) => "Srand",
            Self::Error(_) => "Error",
            Self::Case(..) => "Case",
            Self::FloatBuiltin(..) => "FloatBuiltin",
            Self::Do(..) => "Do",
            Self::Handle { .. } => "Handle",
            Self::Mask(..) => "Mask",
            Self::StrBuiltin(..) => "StrBuiltin",
            Self::Dup(_) => "Dup",
            Self::Drop(_) => "Drop",
            Self::ReuseToken(_) => "ReuseToken",
            Self::Reuse(..) => "Reuse",
        }
    }
}

#[derive(Clone, Debug)]
pub struct CoreFn {
    pub name: Sym,
    pub params: Vec<Sym>,
    pub body: Comp,
}

#[derive(Clone, Debug)]
pub struct Core {
    pub fns: Vec<CoreFn>,
}

// Functions reachable from main. Dead code must not steer whole-program
// decisions (effect lowering inspects every body for ops), so lowering and
// emission both restrict themselves to this set. Free variables are unioned in
// because a function can flow first-class as a bare name (a dictionary field)
// without appearing as a call head.
#[must_use]
pub fn reachable_fns(core: &Core) -> BTreeSet<Sym> {
    let fn_map: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();
    let mut visited: BTreeSet<Sym> = BTreeSet::new();
    let mut queue = vec![Sym::new(ENTRY_POINT)];
    while let Some(name) = queue.pop() {
        if visited.contains(&name) {
            continue;
        }
        visited.insert(name);
        if let Some(f) = fn_map.get(&name) {
            calls_in(&f.body, &mut queue);
            queue.extend(
                super::fv::comp(&f.body)
                    .into_iter()
                    .filter(|n| fn_map.contains_key(n)),
            );
        }
    }
    visited
}

pub(crate) fn calls_in_val(v: &Value, out: &mut Vec<Sym>) {
    match v {
        Value::Thunk(c) => calls_in(c, out),
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => {
            for f in fs {
                calls_in_val(f, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn calls_in(c: &Comp, out: &mut Vec<Sym>) {
    match c {
        Comp::Call(name, args) => {
            out.push(*name);
            for a in args {
                calls_in_val(a, out);
            }
        }
        Comp::Return(v)
        | Comp::Print(v)
        | Comp::PrintF(v)
        | Comp::PrintS(v)
        | Comp::Error(v)
        | Comp::Force(v)
        | Comp::Srand(v)
        | Comp::FloatBuiltin(_, v)
        | Comp::Dup(v)
        | Comp::Drop(v)
        | Comp::ReuseToken(v) => {
            calls_in_val(v, out);
        }
        Comp::Bind(m, _, n) => {
            calls_in(m, out);
            calls_in(n, out);
        }
        Comp::If(v, t, e) => {
            calls_in_val(v, out);
            calls_in(t, out);
            calls_in(e, out);
        }
        Comp::Case(v, arms) => {
            calls_in_val(v, out);
            for (_, body) in arms {
                calls_in(body, out);
            }
        }
        Comp::Lam(_, body) => calls_in(body, out),
        Comp::App(f, args) => {
            calls_in(f, out);
            for a in args {
                calls_in_val(a, out);
            }
        }
        Comp::Prim(_, a, b) => {
            calls_in_val(a, out);
            calls_in_val(b, out);
        }
        Comp::Reuse(t, v) => {
            calls_in_val(t, out);
            calls_in_val(v, out);
        }
        Comp::StrBuiltin(_, args) | Comp::Do(_, args) => {
            for a in args {
                calls_in_val(a, out);
            }
        }
        Comp::ReadInt | Comp::ReadLine | Comp::PrintNl | Comp::Rand => {}
        Comp::Mask(_, b) => calls_in(b, out),
        Comp::Handle {
            body,
            return_body,
            ops,
            ..
        } => {
            calls_in(body, out);
            if let Some(rb) = return_body {
                calls_in(rb, out);
            }
            for op in ops {
                calls_in(&op.body, out);
            }
        }
    }
}
