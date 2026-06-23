use std::collections::BTreeSet;

use crate::sym::Sym;

pub type Effects = BTreeSet<Sym>;

// Wired-in nominal names. The prelude defines them and the compiler special-
// cases them (list literals, `deriving`, built-in equality), so they go through
// these constants rather than scattered string literals.
pub const LIST: &str = "List";
pub const CONS: &str = "Cons";
pub const NIL: &str = "Nil";
pub const EQ_CLASS: &str = "Eq";
pub const ORD_CLASS: &str = "Ord";
pub const SHOW_CLASS: &str = "Show";

// A row label: an effect name plus its instantiation arguments (zero for
// non-parametric effects). `Emit(Int)` and `Emit(String)` are distinct labels
// while `IO` stays bare. The name is an interned `Sym`, re-encoded as text only
// at an output edge.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label {
    pub name: Sym,
    pub args: Vec<Type>,
}

impl Label {
    pub fn bare(name: impl Into<Sym>) -> Self {
        Self {
            name: name.into(),
            args: Vec::new(),
        }
    }

    #[must_use]
    pub fn show(&self) -> String {
        if self.args.is_empty() {
            self.name.to_string()
        } else {
            let args: Vec<_> = self.args.iter().map(Type::show).collect();
            format!("{}({})", self.name, args.join(", "))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EffRow {
    Empty,
    Extend(Label, Box<Self>),
    Var(Sym),
    Exist(u32),
}

impl EffRow {
    pub fn singleton(l: impl Into<Sym>) -> Self {
        Self::Extend(Label::bare(l), Box::new(Self::Empty))
    }

    pub fn from_set(labels: &Effects) -> Self {
        labels.iter().rev().fold(Self::Empty, |acc, l| {
            Self::Extend(Label::bare(*l), Box::new(acc))
        })
    }

    #[must_use]
    pub fn map_args(&self, f: &impl Fn(&Type) -> Type) -> Self {
        match self {
            Self::Extend(l, r) => Self::Extend(
                Label {
                    name: l.name,
                    args: l.args.iter().map(f).collect(),
                },
                Box::new(r.map_args(f)),
            ),
            other => other.clone(),
        }
    }

    pub fn for_each_arg(&self, f: &mut impl FnMut(&Type)) {
        if let Self::Extend(l, r) = self {
            l.args.iter().for_each(&mut *f);
            r.for_each_arg(f);
        }
    }

    pub fn free_exist_row(&self, acc: &mut BTreeSet<u32>) {
        match self {
            Self::Exist(v) => {
                acc.insert(*v);
            }
            Self::Extend(l, r) => {
                for a in &l.args {
                    a.free_exist_row(acc);
                }
                r.free_exist_row(acc);
            }
            _ => {}
        }
    }

    pub fn subst_row_exist(&self, v: u32, with: &Self) -> Self {
        match self {
            Self::Exist(w) if *w == v => with.clone(),
            Self::Extend(l, r) => Self::Extend(
                Label {
                    name: l.name,
                    args: l.args.iter().map(|a| a.subst_row_exist(v, with)).collect(),
                },
                Box::new(r.subst_row_exist(v, with)),
            ),
            other => other.clone(),
        }
    }

    pub fn subst_row_var(&self, name: Sym, with: &Self) -> Self {
        match self {
            Self::Var(n) if *n == name => with.clone(),
            Self::Extend(l, r) => Self::Extend(
                Label {
                    name: l.name,
                    args: l.args.iter().map(|a| a.subst_row_var(name, with)).collect(),
                },
                Box::new(r.subst_row_var(name, with)),
            ),
            other => other.clone(),
        }
    }

    pub fn is_mono_row(&self) -> bool {
        match self {
            Self::Var(_) => false,
            Self::Empty | Self::Exist(_) => true,
            Self::Extend(_, r) => r.is_mono_row(),
        }
    }

    pub fn labels(&self) -> Vec<&Label> {
        let mut v = Vec::new();
        let mut cur = self;
        while let Self::Extend(l, r) = cur {
            v.push(l);
            cur = r;
        }
        v
    }

    pub fn tail(&self) -> &Self {
        let mut cur = self;
        loop {
            match cur {
                Self::Extend(_, r) => cur = r,
                other => return other,
            }
        }
    }

    pub fn show(&self) -> String {
        let labels = self.labels();
        let tail_s = match self.tail() {
            Self::Empty => String::new(),
            Self::Var(v) => v.to_string(),
            Self::Exist(v) => format!("?r{v}"),
            Self::Extend(..) => unreachable!(),
        };
        let mut parts: Vec<String> = labels.into_iter().map(Label::show).collect();
        if !tail_s.is_empty() {
            parts.push(tail_s);
        }
        format!("{{{}}}", parts.join(", "))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Unit,
    Int,
    I64,
    U64,
    Bool,
    Float,
    Char,
    Str,
    Var(Sym),
    Exist(u32),
    Forall(Sym, Box<Self>),
    RowForall(Sym, Box<Self>),
    Fun(Vec<Self>, EffRow, Box<Self>),
    Con(Sym, Vec<Self>),
    // Higher-kinded application of a not-yet-resolved head (a type variable or
    // existential) to one argument: `f(a)` is `App(Var f, a)`, and `f(a, b)`
    // curries to `App(App(Var f, a), b)`. The smart constructor `app` reduces an
    // application the instant its head becomes a concrete `Con`, so a surviving
    // `App` always has a flexible head.
    App(Box<Self>, Box<Self>),
    Tuple(Vec<Self>),
}

impl Type {
    /// The wired-in scalar types, so callers recognize builtin type names by
    /// their canonical `show()` spelling rather than hardcoded literals.
    pub const SCALARS: [Self; 8] = [
        Self::Unit,
        Self::Int,
        Self::I64,
        Self::U64,
        Self::Bool,
        Self::Float,
        Self::Char,
        Self::Str,
    ];

    /// Apply a (possibly higher-kinded) type to one argument, reducing when the
    /// head is a concrete constructor: `app(List, a) = List(a)`, but
    /// `app(f, a) = App(f, a)` while `f` is still a variable/existential.
    #[must_use]
    pub fn app(head: Self, arg: Self) -> Self {
        match head {
            Self::Con(n, mut xs) => {
                xs.push(arg);
                Self::Con(n, xs)
            }
            other => Self::App(Box::new(other), Box::new(arg)),
        }
    }

    /// Apply a head to several arguments left-to-right.
    #[must_use]
    pub fn apps(head: Self, args: Vec<Self>) -> Self {
        args.into_iter().fold(head, Self::app)
    }

    // Flatten an application spine `App(App(h, a1), a2)` into `(h, [a1, a2])` so
    // a higher-kinded application prints and reduces in its n-ary form.
    fn spine(&self) -> (&Self, Vec<&Self>) {
        let mut args = Vec::new();
        let mut head = self;
        while let Self::App(h, a) = head {
            args.push(a.as_ref());
            head = h;
        }
        args.reverse();
        (head, args)
    }

    #[must_use]
    pub fn fun(params: Vec<Self>, ret: Self) -> Self {
        Self::Fun(params, EffRow::Empty, Box::new(ret))
    }

    #[must_use]
    pub fn fun_eff(params: Vec<Self>, eff: EffRow, ret: Self) -> Self {
        Self::Fun(params, eff, Box::new(ret))
    }

    pub fn free_exist(&self, acc: &mut BTreeSet<u32>) {
        match self {
            Self::Exist(v) => {
                acc.insert(*v);
            }
            Self::Forall(_, t) | Self::RowForall(_, t) => t.free_exist(acc),
            Self::Fun(ps, row, r) => {
                for p in ps {
                    p.free_exist(acc);
                }
                row.for_each_arg(&mut |a| a.free_exist(acc));
                r.free_exist(acc);
            }
            Self::Con(_, ps) | Self::Tuple(ps) => {
                for p in ps {
                    p.free_exist(acc);
                }
            }
            Self::App(h, a) => {
                h.free_exist(acc);
                a.free_exist(acc);
            }
            _ => {}
        }
    }

    pub fn free_exist_row(&self, acc: &mut BTreeSet<u32>) {
        match self {
            Self::Fun(ps, row, r) => {
                for p in ps {
                    p.free_exist_row(acc);
                }
                row.free_exist_row(acc);
                r.free_exist_row(acc);
            }
            Self::Forall(_, t) | Self::RowForall(_, t) => t.free_exist_row(acc),
            Self::Con(_, ps) | Self::Tuple(ps) => {
                for p in ps {
                    p.free_exist_row(acc);
                }
            }
            Self::App(h, a) => {
                h.free_exist_row(acc);
                a.free_exist_row(acc);
            }
            _ => {}
        }
    }

    #[must_use]
    pub fn subst_exist(&self, v: u32, with: &Self) -> Self {
        match self {
            Self::Exist(w) if *w == v => with.clone(),
            Self::Forall(n, t) => Self::Forall(*n, Box::new(t.subst_exist(v, with))),
            Self::RowForall(n, t) => Self::RowForall(*n, Box::new(t.subst_exist(v, with))),
            Self::Fun(ps, row, r) => Self::Fun(
                ps.iter().map(|p| p.subst_exist(v, with)).collect(),
                row.map_args(&|a| a.subst_exist(v, with)),
                Box::new(r.subst_exist(v, with)),
            ),
            Self::Con(n, ps) => Self::Con(*n, ps.iter().map(|p| p.subst_exist(v, with)).collect()),
            // Re-reduce after substitution: the head may have become concrete.
            Self::App(h, a) => Self::app(h.subst_exist(v, with), a.subst_exist(v, with)),
            Self::Tuple(ts) => Self::Tuple(ts.iter().map(|t| t.subst_exist(v, with)).collect()),
            other => other.clone(),
        }
    }

    #[must_use]
    pub fn subst_row_exist(&self, v: u32, with: &EffRow) -> Self {
        match self {
            Self::Fun(ps, row, r) => Self::Fun(
                ps.iter().map(|p| p.subst_row_exist(v, with)).collect(),
                row.subst_row_exist(v, with),
                Box::new(r.subst_row_exist(v, with)),
            ),
            Self::Forall(n, t) => Self::Forall(*n, Box::new(t.subst_row_exist(v, with))),
            Self::RowForall(n, t) => Self::RowForall(*n, Box::new(t.subst_row_exist(v, with))),
            Self::Con(n, ps) => {
                Self::Con(*n, ps.iter().map(|p| p.subst_row_exist(v, with)).collect())
            }
            Self::App(h, a) => Self::app(h.subst_row_exist(v, with), a.subst_row_exist(v, with)),
            Self::Tuple(ts) => Self::Tuple(ts.iter().map(|t| t.subst_row_exist(v, with)).collect()),
            other => other.clone(),
        }
    }

    #[must_use]
    pub fn subst_var(&self, name: Sym, with: &Self) -> Self {
        match self {
            Self::Var(n) if *n == name => with.clone(),
            Self::Forall(n, t) if *n != name => Self::Forall(*n, Box::new(t.subst_var(name, with))),
            Self::RowForall(n, t) => Self::RowForall(*n, Box::new(t.subst_var(name, with))),
            Self::Fun(ps, row, r) => Self::Fun(
                ps.iter().map(|p| p.subst_var(name, with)).collect(),
                row.map_args(&|a| a.subst_var(name, with)),
                Box::new(r.subst_var(name, with)),
            ),
            Self::Con(n, ps) => Self::Con(*n, ps.iter().map(|p| p.subst_var(name, with)).collect()),
            Self::App(h, a) => Self::app(h.subst_var(name, with), a.subst_var(name, with)),
            Self::Tuple(ts) => Self::Tuple(ts.iter().map(|t| t.subst_var(name, with)).collect()),
            other => other.clone(),
        }
    }

    #[must_use]
    pub fn subst_row_var(&self, name: Sym, with: &EffRow) -> Self {
        match self {
            Self::Fun(ps, row, r) => Self::Fun(
                ps.iter().map(|p| p.subst_row_var(name, with)).collect(),
                row.subst_row_var(name, with),
                Box::new(r.subst_row_var(name, with)),
            ),
            Self::Forall(n, t) => Self::Forall(*n, Box::new(t.subst_row_var(name, with))),
            Self::RowForall(n, t) if *n != name => {
                Self::RowForall(*n, Box::new(t.subst_row_var(name, with)))
            }
            Self::Con(n, ps) => {
                Self::Con(*n, ps.iter().map(|p| p.subst_row_var(name, with)).collect())
            }
            Self::App(h, a) => Self::app(h.subst_row_var(name, with), a.subst_row_var(name, with)),
            Self::Tuple(ts) => {
                Self::Tuple(ts.iter().map(|t| t.subst_row_var(name, with)).collect())
            }
            other => other.clone(),
        }
    }

    pub fn is_mono(&self) -> bool {
        match self {
            Self::Forall(..) | Self::RowForall(..) => false,
            Self::Fun(ps, row, r) => {
                ps.iter().all(Self::is_mono) && row.is_mono_row() && r.is_mono()
            }
            Self::Con(_, ps) | Self::Tuple(ps) => ps.iter().all(Self::is_mono),
            Self::App(h, a) => h.is_mono() && a.is_mono(),
            _ => true,
        }
    }

    pub fn show(&self) -> String {
        match self {
            Self::Unit => "Unit".into(),
            Self::Int => "Int".into(),
            Self::I64 => "I64".into(),
            Self::U64 => "U64".into(),
            Self::Bool => "Bool".into(),
            Self::Float => "Float".into(),
            Self::Char => "Char".into(),
            Self::Str => "String".into(),
            Self::Var(n) => n.to_string(),
            Self::Exist(v) => format!("?{v}"),
            Self::Forall(..) | Self::RowForall(..) => {
                let mut vs = Vec::new();
                let mut cur = self;
                while let Self::Forall(n, t) | Self::RowForall(n, t) = cur {
                    vs.push(n.as_str());
                    cur = t;
                }
                format!("forall {}. {}", vs.join(" "), cur.show())
            }
            Self::Fun(ps, row, r) => {
                let ps: Vec<_> = ps.iter().map(Self::show).collect();
                let row_s = if *row == EffRow::Empty {
                    String::new()
                } else {
                    format!(" ! {}", row.show())
                };
                format!("({}) -> {}{}", ps.join(", "), r.show(), row_s)
            }
            // A higher-kinded application spine prints in n-ary form `head(a, b)`.
            Self::App(..) => {
                let (head, args) = self.spine();
                let args: Vec<_> = args.iter().map(|a| a.show()).collect();
                format!("{}({})", head.show(), args.join(", "))
            }
            Self::Con(n, ps) if ps.is_empty() => n.to_string(),
            Self::Con(n, ps) => {
                let ps: Vec<_> = ps.iter().map(Self::show).collect();
                format!("{n}({})", ps.join(", "))
            }
            Self::Tuple(ts) => {
                let ts: Vec<_> = ts.iter().map(Self::show).collect();
                format!("({})", ts.join(", "))
            }
        }
    }
}

#[must_use]
pub fn show_effects(e: &Effects) -> String {
    if e.is_empty() {
        "{}".into()
    } else {
        let v: Vec<String> = e.iter().map(Sym::to_string).collect();
        format!("{{{}}}", v.join(", "))
    }
}
