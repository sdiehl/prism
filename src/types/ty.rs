use std::collections::BTreeSet;

use crate::kw;
use crate::sym::Sym;

pub type Effects = BTreeSet<Sym>;

// The kind (sort) of a type-level parameter. Most parameters have kind `Type`
// (`*`); a parameter annotated `: Row` ranges over effect rows, so a data-type
// field may reference it in a `! {..}` position (`type Cmd(a, e : Row)`). `Fun`
// is reserved for a future higher-kinded checker: today HKT (`f(a)`) is handled
// structurally by `App`/`Con` unification and needs no kind annotation, so an
// unannotated parameter defaults to `Type` and the whole existing corpus is
// unchanged.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Kind {
    #[default]
    Type,
    Row,
    Fun(Box<Self>, Box<Self>),
}

// Wired-in nominal names. The prelude defines them and the compiler special-
// cases them (list literals, `deriving`, built-in equality), so they go through
// these constants rather than scattered string literals.
pub const LIST: &str = "List";
pub const CONS: &str = "Cons";
pub const NIL: &str = "Nil";
pub const EQ_CLASS: &str = "Eq";
pub const ORD_CLASS: &str = "Ord";
pub const SHOW_CLASS: &str = "Show";
// The content-addressed structural hash class, in the prelude beside `Eq`/`Ord`.
pub const HASH_CLASS: &str = "Hash";
// The opt-in wire classes, defined in `lib/std/Wire.pr` (out of the prelude), and
// the property-generator class in `lib/std/Test.pr`. `deriving` resolves each of
// these bare names to its imported canonical form.
pub const SERIALIZE_CLASS: &str = "Serialize";
pub const STABLE_CLASS: &str = "Stable";
pub const ARBITRARY_CLASS: &str = "Arbitrary";

// `deriving (Identifiable)` is surface sugar, not a class: it expands to the
// identity starter pack, the classes that make a value usable as an ID. The set
// is exactly those derivable with zero imports (all four live in the prelude),
// so an ID newtype in an ordinary program compiles as written. `Arbitrary` is
// deliberately absent: its class lives behind `import Test`, and random
// generation is a testing concern, not part of a value's identity; a program
// that wants it writes `deriving (Identifiable, Arbitrary)`.
pub const IDENTIFIABLE: &str = "Identifiable";
pub const IDENTIFIABLE_BUNDLE: [&str; 4] = [EQ_CLASS, ORD_CLASS, HASH_CLASS, SHOW_CLASS];

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

    // Free rigid row-variable (row skolem) names of the row, the `RowUni`-kind
    // dual of `free_exist_row`. Rows carry no binders of their own; label
    // arguments are types, walked for the row skolems nested inside them. Drives
    // `Type::free_row_vars` through the type/row alternation.
    fn walk_vars(&self, bound: &mut Vec<Sym>, acc: &mut BTreeSet<Sym>) {
        match self {
            Self::Var(n) => {
                if !bound.contains(n) {
                    acc.insert(*n);
                }
            }
            Self::Extend(l, rest) => {
                for a in &l.args {
                    a.walk_row_vars(bound, acc);
                }
                rest.walk_vars(bound, acc);
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

    // The bare label names of the row (dropping any args), as a set.
    pub fn label_names(&self) -> Effects {
        let mut v = Effects::new();
        let mut cur = self;
        while let Self::Extend(l, r) = cur {
            v.insert(l.name);
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
        // A row is a set, so render its labels in a canonical (name-sorted)
        // order rather than the order inference happened to absorb them; the
        // absorb order is not stable across runs (it follows interner state), and
        // an unstable signature display would make snapshots flaky. The tail row
        // variable, if any, stays last.
        let mut parts: Vec<String> = labels.into_iter().map(Label::show).collect();
        parts.sort();
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
    // An effect row carried in type-argument position: the argument supplied
    // for a `Row`-kinded parameter (`Cmd(Int, {IO})`), and what a rigid row
    // parameter `Var(e)` becomes once embedded in a `Con` spine. It only ever
    // appears at a `Row`-kinded position; unification of `Row(a) ~ Row(b)`
    // defers to `unify_row`, and row-variable substitution recurses through it.
    Row(EffRow),
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
            Self::Row(r) => r.for_each_arg(&mut |a| a.free_exist(acc)),
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
            Self::Row(r) => r.free_exist_row(acc),
            _ => {}
        }
    }

    // Free rigid type-variable (skolem) names, the `Uni`-kind dual of
    // `free_exist`. A variable bound by an enclosing `Forall` in `self` is not
    // free, so a well-formed generalized scheme collects the empty set; a name
    // left over here is a skolem that escaped its quantifier.
    pub fn free_ty_vars(&self, acc: &mut BTreeSet<Sym>) {
        self.walk_ty_vars(&mut Vec::new(), acc);
    }

    // Free rigid row-variable (row skolem) names, the `RowUni`-kind dual of
    // `free_exist_row`; a variable bound by an enclosing `RowForall` is excluded.
    pub fn free_row_vars(&self, acc: &mut BTreeSet<Sym>) {
        self.walk_row_vars(&mut Vec::new(), acc);
    }

    fn walk_ty_vars(&self, bound: &mut Vec<Sym>, acc: &mut BTreeSet<Sym>) {
        match self {
            Self::Var(n) => {
                if !bound.contains(n) {
                    acc.insert(*n);
                }
            }
            Self::Forall(n, t) => {
                bound.push(*n);
                t.walk_ty_vars(bound, acc);
                bound.pop();
            }
            Self::RowForall(_, t) => t.walk_ty_vars(bound, acc),
            Self::Fun(ps, row, r) => {
                for p in ps {
                    p.walk_ty_vars(bound, acc);
                }
                row.for_each_arg(&mut |a| a.walk_ty_vars(bound, acc));
                r.walk_ty_vars(bound, acc);
            }
            Self::Con(_, ps) | Self::Tuple(ps) => {
                for p in ps {
                    p.walk_ty_vars(bound, acc);
                }
            }
            Self::App(h, a) => {
                h.walk_ty_vars(bound, acc);
                a.walk_ty_vars(bound, acc);
            }
            Self::Row(r) => r.for_each_arg(&mut |a| a.walk_ty_vars(bound, acc)),
            _ => {}
        }
    }

    fn walk_row_vars(&self, bound: &mut Vec<Sym>, acc: &mut BTreeSet<Sym>) {
        match self {
            Self::Fun(ps, row, r) => {
                for p in ps {
                    p.walk_row_vars(bound, acc);
                }
                row.walk_vars(bound, acc);
                r.walk_row_vars(bound, acc);
            }
            Self::RowForall(n, t) => {
                bound.push(*n);
                t.walk_row_vars(bound, acc);
                bound.pop();
            }
            Self::Forall(_, t) => t.walk_row_vars(bound, acc),
            Self::Con(_, ps) | Self::Tuple(ps) => {
                for p in ps {
                    p.walk_row_vars(bound, acc);
                }
            }
            Self::App(h, a) => {
                h.walk_row_vars(bound, acc);
                a.walk_row_vars(bound, acc);
            }
            Self::Row(r) => r.walk_vars(bound, acc),
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
            Self::Row(r) => Self::Row(r.map_args(&|a| a.subst_exist(v, with))),
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
            Self::Row(r) => Self::Row(r.subst_row_exist(v, with)),
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
            Self::Row(r) => Self::Row(r.map_args(&|a| a.subst_var(name, with))),
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
            Self::Row(r) => Self::Row(r.subst_row_var(name, with)),
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
            Self::Row(r) => r.is_mono_row(),
            _ => true,
        }
    }

    pub fn show(&self) -> String {
        match self {
            Self::Unit => kw::TY_UNIT.into(),
            Self::Int => kw::TY_INT.into(),
            Self::I64 => kw::TY_I64.into(),
            Self::U64 => kw::TY_U64.into(),
            Self::Bool => kw::TY_BOOL.into(),
            Self::Float => kw::TY_FLOAT.into(),
            Self::Char => kw::TY_CHAR.into(),
            Self::Str => kw::TY_STRING.into(),
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
                format!("({}) {} {}{}", ps.join(", "), kw::ARROW, r.show(), row_s)
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
            Self::Row(r) => r.show(),
        }
    }
}

#[must_use]
pub fn show_effects(e: &Effects) -> String {
    if e.is_empty() {
        "{}".into()
    } else {
        let mut v: Vec<String> = e.iter().map(Sym::to_string).collect();
        v.sort();
        format!("{{{}}}", v.join(", "))
    }
}
