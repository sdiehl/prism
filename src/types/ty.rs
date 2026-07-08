use std::collections::{BTreeMap, BTreeSet};

use crate::kw;
use crate::sym::Sym;

pub type Effects = BTreeSet<Sym>;

// The kind (sort) of a type-level parameter. Most parameters have kind `Type`
// (`*`); a parameter annotated `: Row` ranges over effect rows, so a data-type
// field may reference it in a `! {..}` position (`type Cmd(a, e : Row)`); a
// parameter annotated `: Nat` ranges over type-level natural literals (a
// dimension position, `type Vec(a, n : Nat)`), inhabited by `0`, `1`, `2`, ...
// with unification by literal equality only (no dimension arithmetic). `Fun`
// is the kind of a type constructor once it is applied: `Vec : Type -> Nat ->
// Type` is `Fun(Type, Fun(Nat, Type))`. HKT of a variable head (`f(a)`) is still
// handled structurally by `App`/`Con` unification; an unannotated parameter
// defaults to `Type` so the whole existing corpus is unchanged.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Kind {
    #[default]
    Type,
    Row,
    Nat,
    Fun(Box<Self>, Box<Self>),
}

impl Kind {
    // The arrow kind of a constructor whose parameters have kinds `params` and
    // whose result is `Type`: `[Type, Nat]` becomes `Type -> Nat -> Type`. This
    // is the sole constructor of `Kind::Fun`; the kind checker builds a
    // constructor's kind here and checks each applied argument against the
    // domain it peels off, so an over- or mis-applied constructor is a kind
    // error rather than a downstream unification failure.
    #[must_use]
    pub fn arrow(params: &[Self]) -> Self {
        params.iter().rev().fold(Self::Type, |acc, k| {
            Self::Fun(Box::new(k.clone()), Box::new(acc))
        })
    }

    #[must_use]
    pub fn show(&self) -> String {
        match self {
            Self::Type => "Type".into(),
            Self::Row => "Row".into(),
            Self::Nat => "Nat".into(),
            Self::Fun(a, b) => format!("{} -> {}", a.show(), b.show()),
        }
    }
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
// The numeric operator classes: `Num` carries `+`/`-`/`*`/unary negate, `Div`
// carries `/`/`%`. Both have `Int`/`I64`/`U64`/`Float` prelude instances. A
// monomorphic operand keeps the direct lane primitive (byte-identical Core); only
// a `given Num(a)`/`given Div(a)` operand dispatches through the dictionary, which
// the specializer erases.
pub const NUM_CLASS: &str = "Num";
pub const DIV_CLASS: &str = "Div";
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

// `deriving (Lens)` is surface sugar, not a class: it synthesizes field accessor
// functions directly.
pub const LENS: &str = "Lens";

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
        // One label over the empty tail is canonical by construction.
        Self::Extend(Label::bare(l), Box::new(Self::Empty))
    }

    pub fn from_set(labels: &Effects) -> Self {
        Self::canonical(labels.iter().map(|l| Label::bare(*l)), Self::Empty)
    }

    // A row's canonical form: its labels appear in strictly increasing
    // `Label::show` order, so no label repeats, terminated by the non-`Extend`
    // tail. This is exactly the normal form the row display (`show`/`show_row_p`)
    // reduces every row to, and, through the shown type/row strings, the one the
    // content hash commits to. Two set-equal rows that are both canonical are
    // therefore structurally identical. `Var`/`Exist` carry no labels and are
    // trivially canonical.
    //
    // The type checker does not keep stored rows canonical: substitution can
    // reintroduce a duplicate label (`apply_row` on `IO | e` with `e := IO | r`)
    // and effects are absorbed in inference order, so `unify_row` dedups and
    // matches labels by name rather than by position, and both display paths sort
    // on the fly. A `debug_assert` on the *input* of unify/display/hash would thus
    // fire on legitimate intermediates; the teeth live in the constructors below,
    // which guarantee their *output* is canonical.
    #[must_use]
    pub fn is_canonical(&self) -> bool {
        self.labels().windows(2).all(|w| w[0].show() < w[1].show())
    }

    // Build a canonical row: the effects `labels` over a terminal `tail`
    // (`Empty`, `Var`, or `Exist`), sorted by `Label::show` with duplicate labels
    // dropped. The constructor to reach for when the intent is "the row whose
    // effects are exactly these"; the raw `Extend` variant stays for the
    // structure-preserving passes (substitution, unification rewrites) that must
    // keep an existing row's shape.
    #[must_use]
    pub fn canonical(labels: impl IntoIterator<Item = Label>, tail: Self) -> Self {
        debug_assert!(
            matches!(tail, Self::Empty | Self::Var(_) | Self::Exist(_)),
            "row tail must be terminal, got {tail:?}"
        );
        let mut ls: Vec<Label> = labels.into_iter().collect();
        ls.sort_by_key(Label::show);
        ls.dedup_by(|a, b| a.show() == b.show());
        let row = ls
            .into_iter()
            .rev()
            .fold(tail, |acc, l| Self::Extend(l, Box::new(acc)));
        debug_assert!(
            row.is_canonical(),
            "canonical produced a non-canonical row: {row:?}"
        );
        row
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
    // A type-level natural literal in a dimension position (a `Nat`-kinded
    // argument, `Vec(Int, 3)`). It is an opaque atom: unification is literal
    // equality (`Nat(3) ~ Nat(4)` fails, naming both lengths), with no successor
    // structure and no arithmetic, so a dimension variable solves only to a
    // literal it is already forced to equal. Erased before Core; it never
    // reaches codegen.
    Nat(u64),
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
            // A surviving `App` always has a flexible head (a type variable, an
            // existential, or a further `App`): a concrete `Con` head is reduced
            // by the arm above, so the head class is enforced structurally here.
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

    #[must_use]
    pub fn show(&self) -> String {
        self.show_p(&self.phantom_rows())
    }

    // The row variables this scheme keeps open only for unification: a
    // `RowForall`-bound variable that occurs exactly once, as one arrow's effect
    // tail. That is a function's own latent row, quantified so a pure value fits
    // an effectful context by solving it (`default_open_rows`); it carries no
    // information a reader needs, so the display suppresses both its binder and
    // its `! {..}` tail (rendering the arrow as pure, exactly as before rows were
    // checked by unification). A variable shared across arrows (genuine effect
    // polymorphism) or threaded through a `Row`-kinded data type (`Cmd(a, {e})`)
    // occurs more than once, or not as a bare tail, so it is never suppressed.
    // The structural type is untouched; only the rendering drops these.
    fn phantom_rows(&self) -> BTreeSet<Sym> {
        // Only the scheme's own outermost quantifier prefix carries auto-opened
        // latent tails. An inner (rank-N) `forall e. (Int) -> Int ! {e}` the user
        // wrote on a parameter is a real constraint (the argument must be effect
        // polymorphic), so it is never a candidate for suppression.
        let mut prefix = BTreeSet::new();
        let mut cur = self;
        loop {
            match cur {
                Self::RowForall(n, t) => {
                    prefix.insert(*n);
                    cur = t;
                }
                Self::Forall(_, t) => cur = t,
                _ => break,
            }
        }
        let mut total = BTreeMap::new();
        let mut tail = BTreeMap::new();
        self.row_var_stats(&mut total, &mut tail);
        prefix
            .into_iter()
            .filter(|v| {
                total.get(v).copied().unwrap_or(0) == 1 && tail.get(v).copied().unwrap_or(0) == 1
            })
            .collect()
    }

    // `total`: every appearance of each row variable. `tail`: only appearances as
    // the trailing variable of an arrow's effect row. See `phantom_rows`.
    fn row_var_stats(&self, total: &mut BTreeMap<Sym, usize>, tail: &mut BTreeMap<Sym, usize>) {
        match self {
            Self::Forall(_, t) | Self::RowForall(_, t) => t.row_var_stats(total, tail),
            Self::Fun(ps, row, r) => {
                for p in ps {
                    p.row_var_stats(total, tail);
                }
                count_row_vars(row, total);
                if let EffRow::Var(v) = row.tail() {
                    *tail.entry(*v).or_default() += 1;
                }
                r.row_var_stats(total, tail);
            }
            Self::Con(_, ps) | Self::Tuple(ps) => {
                for p in ps {
                    p.row_var_stats(total, tail);
                }
            }
            Self::App(h, a) => {
                h.row_var_stats(total, tail);
                a.row_var_stats(total, tail);
            }
            Self::Row(r) => count_row_vars(r, total),
            _ => {}
        }
    }

    fn show_p(&self, phantom: &BTreeSet<Sym>) -> String {
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
                    if !phantom.contains(n) {
                        vs.push(n.as_str());
                    }
                    cur = t;
                }
                if vs.is_empty() {
                    cur.show_p(phantom)
                } else {
                    format!("forall {}. {}", vs.join(" "), cur.show_p(phantom))
                }
            }
            Self::Fun(ps, row, r) => {
                let ps: Vec<_> = ps.iter().map(|p| p.show_p(phantom)).collect();
                let row_s =
                    show_row_p(row, phantom).map_or_else(String::new, |s| format!(" ! {s}"));
                format!(
                    "({}) {} {}{}",
                    ps.join(", "),
                    kw::ARROW,
                    r.show_p(phantom),
                    row_s
                )
            }
            // A higher-kinded application spine prints in n-ary form `head(a, b)`.
            Self::App(..) => {
                let (head, args) = self.spine();
                let args: Vec<_> = args.iter().map(|a| a.show_p(phantom)).collect();
                format!("{}({})", head.show_p(phantom), args.join(", "))
            }
            Self::Con(n, ps) if ps.is_empty() => n.to_string(),
            Self::Con(n, ps) => {
                let ps: Vec<_> = ps.iter().map(|p| p.show_p(phantom)).collect();
                format!("{n}({})", ps.join(", "))
            }
            Self::Tuple(ts) => {
                let ts: Vec<_> = ts.iter().map(|t| t.show_p(phantom)).collect();
                format!("({})", ts.join(", "))
            }
            Self::Row(r) => r.show(),
            Self::Nat(n) => n.to_string(),
        }
    }
}

// Add every row variable of `row` (its trailing variable, and any inside a
// label's type arguments) to `total`.
fn count_row_vars(row: &EffRow, total: &mut BTreeMap<Sym, usize>) {
    for l in row.labels() {
        for a in &l.args {
            let mut t = BTreeMap::new();
            a.row_var_stats(total, &mut t);
        }
    }
    if let EffRow::Var(v) = row.tail() {
        *total.entry(*v).or_default() += 1;
    }
}

// Render an effect row, dropping a trailing phantom row variable. Returns `None`
// when nothing is left to show (an empty row, or a bare phantom tail), so the
// arrow prints with no `! {..}` annotation.
fn show_row_p(row: &EffRow, phantom: &BTreeSet<Sym>) -> Option<String> {
    let mut parts: Vec<String> = row.labels().into_iter().map(Label::show).collect();
    parts.sort();
    let tail_s = match row.tail() {
        EffRow::Empty => String::new(),
        EffRow::Var(v) if phantom.contains(v) => String::new(),
        EffRow::Var(v) => v.to_string(),
        EffRow::Exist(v) => format!("?r{v}"),
        EffRow::Extend(..) => unreachable!(),
    };
    if !tail_s.is_empty() {
        parts.push(tail_s);
    }
    if parts.is_empty() {
        None
    } else {
        Some(format!("{{{}}}", parts.join(", ")))
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
