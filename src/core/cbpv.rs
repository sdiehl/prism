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
    // Free `freed` (a cell the matched scrutinee owned and that is now dead) and
    // bind its shell as a reuse `token` scoped over `body`. The token is a binder,
    // so the cell is freed at exactly one point; only `Reuse` can name the token,
    // and it spends it building a constructor in place. Freed-once and
    // spent-at-an-allocation are thus structural properties of the term, not a
    // post-hoc check. Built by the reuse pass from a `drop` paired with a later
    // allocation; lowers to the same `prism_reuse_token` call the threaded form
    // did (it is just the `drop`+`bind` fused into one scoped node).
    WithReuse {
        token: Sym,
        freed: Value,
        body: Box<Self>,
    },
    // Build `ctor` in place over the cell held by reuse `token` (a binder of an
    // enclosing `WithReuse`). Allocation-free: it overwrites the freed shell
    // instead of calling the allocator. The token is the only operand position
    // that may name a reuse token.
    Reuse(Sym, Value),
    // A local mutable cell, the runtime form of an escape-checked `var`. The
    // effect-lowering pass `erase_local_vars` rewrites a closed var/State handler
    // into these, so a `var` loop runs as a real loop (constant stack, no
    // per-operation reification) instead of the free monad.
    //   RefNew(v)      allocate a one-field cell holding v; result owns the cell
    //   RefGet(c)      read the cell's field (an owned snapshot; c is borrowed)
    //   RefSet(c, v)   overwrite the cell's field with v in place (c borrowed, v
    //                  moved in); yields Unit
    RefNew(Value),
    RefGet(Value),
    RefSet(Value, Value),
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
            Self::WithReuse { .. } => "WithReuse",
            Self::Reuse(..) => "Reuse",
            Self::RefNew(_) => "RefNew",
            Self::RefGet(_) => "RefGet",
            Self::RefSet(..) => "RefSet",
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

// Every direct call head anywhere in `c` (including inside thunks, lambdas, and
// handler clauses), in occurrence order. A bare function name flowing
// first-class (a dictionary field) is not a call head; `reachable_fns` unions
// those in via `fv`.
pub(crate) fn calls_in(c: &Comp, out: &mut Vec<Sym>) {
    struct Calls<'a>(&'a mut Vec<Sym>);
    impl super::traverse::Visit for Calls<'_> {
        fn visit_comp(&mut self, c: &Comp) {
            if let Comp::Call(name, args) = c {
                self.0.push(*name);
                for a in args {
                    self.visit_value(a);
                }
            } else {
                self.descend_comp(c);
            }
        }
    }
    super::traverse::Visit::visit_comp(&mut Calls(out), c);
}
