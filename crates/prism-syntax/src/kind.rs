//! The kind vocabulary of type parameters.
//!
//! The classifier the surface grammar parses and the kind checker consumes.
//! Ground kinds classify types, rows, and type-level naturals; `Fun` is the
//! kind of a type constructor.

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
