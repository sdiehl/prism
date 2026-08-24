//! Runtime representation authority.
//!
//! [`TypeLayout`] keeps facts that must not be inferred from one overloaded
//! enum separate: local storage, boundary ABI adaptation, zero-word behavior,
//! and reference-count behavior. In particular, `Unit` and `Bool` are both
//! immediate words but only `Unit` is zero, while an unboxed product is
//! multiword locally and boxed when it crosses the current native ABI.

use std::fmt;

use super::ty::Type;
use prism_common::sym::Sym;

const REPR_MIN_STACK: usize = 64 * 1024;
const REPR_GROW_STACK: usize = 2 * 1024 * 1024;

/// How a value is stored in its local representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Repr {
    /// An ordinary runtime value word whose nullability is not known from the
    /// storage class alone.
    Value,
    /// A runtime value word guaranteed not to be the machine zero word.
    NonNullValue,
    /// A tagged or reserved non-pointer word.
    Immediate,
    /// An unboxed 64-bit payload with no GC traversal.
    Bits64,
    /// An unboxed IEEE-754 double.
    Float64,
    /// An unboxed 128-bit SIMD payload (two words).
    Vec128,
    /// An unboxed product whose fields retain their component layouts.
    Product(Vec<Self>),
    /// An unresolved or non-value layout. It is never executable.
    Any,
}

impl Repr {
    /// Whether this representation occupies one ordinary runtime value word.
    #[must_use]
    pub const fn is_gc_value(&self) -> bool {
        matches!(self, Self::Value | Self::NonNullValue | Self::Immediate)
    }

    /// Whether this representation names a concrete, finite local layout.
    #[must_use]
    pub fn is_representable(&self) -> bool {
        self.field_width_words().is_some()
    }

    /// Storage width in machine words.
    ///
    /// Returns `None` for `Any`, for a product containing `Any`, or if the sum
    /// overflows. The iterative walk also avoids recursive stack growth for an
    /// adversarially deep product.
    #[must_use]
    pub fn field_width_words(&self) -> Option<usize> {
        let mut width = 0usize;
        let mut pending = vec![self];
        while let Some(repr) = pending.pop() {
            match repr {
                Self::Any => return None,
                Self::Vec128 => width = width.checked_add(2)?,
                Self::Product(fields) => pending.extend(fields),
                _ => width = width.checked_add(1)?,
            }
        }
        Some(width)
    }

    /// Required alignment in machine words.
    ///
    /// Products use the strictest field alignment. Undefined layouts return
    /// `None` rather than silently acquiring word alignment.
    #[must_use]
    pub fn alignment_words(&self) -> Option<usize> {
        let mut alignment = 1usize;
        let mut pending = vec![self];
        while let Some(repr) = pending.pop() {
            match repr {
                Self::Any => return None,
                Self::Vec128 => alignment = alignment.max(2),
                Self::Product(fields) => pending.extend(fields),
                _ => {}
            }
        }
        Some(alignment)
    }
}

impl fmt::Display for Repr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value => f.write_str("runtime value word"),
            Self::NonNullValue => f.write_str("non-null value word"),
            Self::Immediate => f.write_str("immediate word"),
            Self::Bits64 => f.write_str("unboxed i64"),
            Self::Float64 => f.write_str("unboxed f64"),
            Self::Vec128 => f.write_str("128-bit vector"),
            Self::Product(_) => f.write_str("unboxed product"),
            Self::Any => f.write_str("unknown representation"),
        }
    }
}

/// How a local representation crosses the current function ABI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbiLayout {
    /// Local and boundary representations are identical.
    Direct(Repr),
    /// A locally unboxed product is allocated as one non-null value word.
    BoxedProduct,
    /// A polymorphic boundary requires an explicit opaque value-word contract.
    OpaqueWord,
    /// A nominal value needs declaration evidence before its ABI is known.
    ///
    /// Mandatory newtype erasure may make the source wrapper transparent, so
    /// type syntax alone cannot decide whether the boundary carries a cell or
    /// the wrapped value.
    DeferredNominal,
    /// Rows, type-level naturals, or unresolved product fields cannot cross.
    Invalid,
}

impl AbiLayout {
    /// Concrete boundary representation, if this layout may cross the ABI.
    #[must_use]
    pub fn repr(&self) -> Option<Repr> {
        match self {
            Self::Direct(repr) => Some(repr.clone()),
            Self::BoxedProduct => Some(Repr::NonNullValue),
            Self::OpaqueWord => Some(Repr::Value),
            Self::DeferredNominal | Self::Invalid => None,
        }
    }
}

/// Whether the machine zero word can encode a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZeroPossibility {
    Always,
    Never,
    Maybe,
    NotAWord,
    Unknown,
}

/// Reference-count action required by a local value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcBehavior {
    /// The value cannot own a heap cell.
    Trivial,
    /// The value is always a managed heap cell.
    Managed,
    /// The runtime word may be immediate, null, or a managed cell.
    RuntimeWord,
    /// Ownership is the composition of product fields.
    Fields,
    /// No executable ownership fact is available.
    Unknown,
}

/// Where a literal of the type keeps its backing cell, when it has one.
///
/// The axis a scalar-literal consumer needs beyond storage, zero, and
/// ownership: a managed cell class alone cannot say whether a literal mints a
/// cell per use or shares one interned into the program image.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralCell {
    /// The literal is a machine word; no cell exists.
    NoCell,
    /// One static cell interned into the program image, shared by every use.
    Interned,
    /// A fresh cell allocated at each materialized literal.
    Boxed,
    /// No literal encoding fact is available.
    Unknown,
}

/// Authoritative representation facts for one semantic type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeLayout {
    local: Repr,
    abi: AbiLayout,
    zero: ZeroPossibility,
    rc: RcBehavior,
    literal: LiteralCell,
}

impl TypeLayout {
    /// Representation used inside a function body.
    #[must_use]
    pub const fn local(&self) -> &Repr {
        &self.local
    }

    /// Representation plan at a function boundary.
    #[must_use]
    pub const fn abi(&self) -> &AbiLayout {
        &self.abi
    }

    /// Local zero-word behavior.
    #[must_use]
    pub const fn zero(&self) -> ZeroPossibility {
        self.zero
    }

    /// Local reference-count behavior.
    #[must_use]
    pub const fn rc(&self) -> RcBehavior {
        self.rc
    }

    /// Where a literal of the type keeps its backing cell.
    #[must_use]
    pub const fn literal(&self) -> LiteralCell {
        self.literal
    }

    /// True only when a value is exactly one known non-zero local word.
    #[must_use]
    pub fn is_non_zero_word(&self) -> bool {
        self.local.is_gc_value() && self.zero == ZeroPossibility::Never
    }
}

fn direct(local: Repr, zero: ZeroPossibility, rc: RcBehavior, literal: LiteralCell) -> TypeLayout {
    TypeLayout {
        abi: AbiLayout::Direct(local.clone()),
        local,
        zero,
        rc,
        literal,
    }
}

fn product_layout(fields: Vec<Repr>) -> TypeLayout {
    let local = Repr::Product(fields);
    let concrete = local.is_representable();
    TypeLayout {
        local,
        abi: if concrete {
            AbiLayout::BoxedProduct
        } else {
            AbiLayout::Invalid
        },
        zero: ZeroPossibility::NotAWord,
        rc: if concrete {
            RcBehavior::Fields
        } else {
            RcBehavior::Unknown
        },
        literal: LiteralCell::Unknown,
    }
}

fn layout_inner(ty: &Type) -> TypeLayout {
    match ty {
        Type::Unit => direct(
            Repr::Immediate,
            ZeroPossibility::Always,
            RcBehavior::Trivial,
            LiteralCell::NoCell,
        ),
        Type::Bool | Type::Char => direct(
            Repr::Immediate,
            ZeroPossibility::Never,
            RcBehavior::Trivial,
            LiteralCell::NoCell,
        ),
        // These values are allocated cells. In particular, fixed-width integer
        // and float literals are boxed by both native emitters, not immediates.
        Type::I64 | Type::U64 | Type::Float | Type::Fun(..) | Type::Tuple(_) => direct(
            Repr::NonNullValue,
            ZeroPossibility::Never,
            RcBehavior::Managed,
            LiteralCell::Boxed,
        ),
        // `Str` shares the managed-cell class but its literals are interned
        // into the program image, one static cell shared by every use.
        Type::Str => direct(
            Repr::NonNullValue,
            ZeroPossibility::Never,
            RcBehavior::Managed,
            LiteralCell::Interned,
        ),
        // `Int` is either a tagged immediate or a boxed bignum, but never zero.
        // Its literals are range-checked and encoded as tagged words.
        Type::Int => direct(
            Repr::NonNullValue,
            ZeroPossibility::Never,
            RcBehavior::RuntimeWord,
            LiteralCell::NoCell,
        ),
        // A nominal source type may become representation-transparent during
        // mandatory newtype erasure. Type syntax alone cannot distinguish that
        // from an allocated datatype, so its ABI is deferred until declaration
        // evidence arrives.
        Type::Con(..) => TypeLayout {
            local: Repr::Any,
            abi: AbiLayout::DeferredNominal,
            zero: ZeroPossibility::Unknown,
            rc: RcBehavior::Unknown,
            literal: LiteralCell::Unknown,
        },
        // Rows and naturals are not value types at all.
        Type::Row(_) | Type::Nat(_) => TypeLayout {
            local: Repr::Any,
            abi: AbiLayout::Invalid,
            zero: ZeroPossibility::Unknown,
            rc: RcBehavior::Unknown,
            literal: LiteralCell::Unknown,
        },
        Type::OrNull(_) => direct(
            Repr::Value,
            ZeroPossibility::Maybe,
            RcBehavior::RuntimeWord,
            LiteralCell::Unknown,
        ),
        Type::Forall(_, inner) | Type::RowForall(_, inner) | Type::Coeffect(inner, _) => {
            layout_of_type(inner)
        }
        Type::UnboxedTuple(fields) => product_layout(
            fields
                .iter()
                .map(|field| layout_of_type(field).local)
                .collect(),
        ),
        Type::UnboxedRecord(fields) => product_layout(
            fields
                .iter()
                .map(|(_, field)| layout_of_type(field).local)
                .collect(),
        ),
        // A flexible head might later become a multiword unboxed product. The
        // local layout therefore stays unknown; a boundary may use a boxed-word
        // convention only as an explicit ABI decision.
        Type::Var(_) | Type::Exist(_) | Type::App(..) => TypeLayout {
            local: Repr::Any,
            abi: AbiLayout::OpaqueWord,
            zero: ZeroPossibility::Unknown,
            rc: RcBehavior::Unknown,
            literal: LiteralCell::Unknown,
        },
    }
}

/// Compute the authoritative representation facts for `ty`.
///
/// Recursive type syntax re-enters through this grown-stack boundary, while
/// width and alignment queries use iterative walks.
#[must_use]
pub fn layout_of_type(ty: &Type) -> TypeLayout {
    stacker::maybe_grow(REPR_MIN_STACK, REPR_GROW_STACK, || layout_inner(ty))
}

/// Compute representation facts with declaration evidence for nominal types.
///
/// The callback may claim an allocated wrapper only when that wrapper survives
/// mandatory representation passes. A false answer retains the context-free,
/// fail-closed nominal layout. The evidence is threaded through schemes,
/// coeffects, and product fields rather than being consulted only at the head.
#[must_use]
pub fn layout_of_type_in(ty: &Type, nominal_is_boxed: impl Fn(Sym) -> bool) -> TypeLayout {
    fn with_evidence<F>(ty: &Type, nominal_is_boxed: &F) -> TypeLayout
    where
        F: Fn(Sym) -> bool,
    {
        stacker::maybe_grow(REPR_MIN_STACK, REPR_GROW_STACK, || match ty {
            // A nominal type has no scalar literal, so no literal-cell fact is
            // claimed even once the wrapper is known to be boxed.
            Type::Con(name, _) if nominal_is_boxed(*name) => direct(
                Repr::NonNullValue,
                ZeroPossibility::Never,
                RcBehavior::Managed,
                LiteralCell::Unknown,
            ),
            Type::Forall(_, inner) | Type::RowForall(_, inner) | Type::Coeffect(inner, _) => {
                with_evidence(inner, nominal_is_boxed)
            }
            Type::UnboxedTuple(fields) => product_layout(
                fields
                    .iter()
                    .map(|field| with_evidence(field, nominal_is_boxed).local)
                    .collect(),
            ),
            Type::UnboxedRecord(fields) => product_layout(
                fields
                    .iter()
                    .map(|(_, field)| with_evidence(field, nominal_is_boxed).local)
                    .collect(),
            ),
            _ => layout_inner(ty),
        })
    }

    with_evidence(ty, &nominal_is_boxed)
}

/// Local runtime representation of a type.
///
/// Kept as the compact compatibility query for existing verifier callers; new
/// consumers should use [`layout_of_type`] so they do not conflate local and ABI
/// layouts or infer zero/ownership behavior from storage alone.
#[must_use]
pub fn repr_of_type(ty: &Type) -> Repr {
    let layout = layout_of_type(ty);
    match layout.abi {
        // The question this query answers is boundary word-ness, asked before
        // erasure. A variable/application crosses polymorphically as one opaque
        // word, while a nominal source value occupies one Core slot pending
        // declaration-aware erasure. Reading both from explicit ABI states
        // keeps the compatibility query from inventing another layout table.
        AbiLayout::OpaqueWord | AbiLayout::DeferredNominal => Repr::Value,
        _ => layout.local,
    }
}

/// How a scalar literal is encoded as its one runtime word.
///
/// A derived view of the layout facts: the storage, zero, and ownership axes
/// pick the word shape, and [`LiteralCell`] says where a cell-carrying
/// literal's cell lives. `Str` literals are interned into the program image as
/// static cells, so no use site owns one and no release ever frees one, while
/// fixed-width integer and float literals allocate a fresh box at each
/// materialization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarPlan {
    /// The machine zero word.
    ZeroWord,
    /// A tagged non-pointer word: the payload is stored as `(n << 1) | 1`.
    TaggedImmediate,
    /// One static cell in the program image, shared by every use.
    StaticCell,
    /// A freshly allocated cell per materialized literal.
    FreshCell,
}

impl ScalarPlan {
    /// Whether a literal with this plan materializes a fresh heap cell its
    /// use site must own. Zero and tagged words carry no cell at all, and a
    /// static cell is owned by the program image, not the use site.
    #[must_use]
    pub const fn owns_fresh_cell(self) -> bool {
        matches!(self, Self::FreshCell)
    }
}

/// Encoding plan for a scalar literal of type `ty`, derived from the layout
/// facts rather than re-decided inside each consumer.
///
/// Fail-closed: layout facts that match no known scalar encoding are an
/// error, never a guess. `Int` reads as tagged because the native emitters
/// range-check each literal first; a wider literal reaches codegen boxed as
/// `I64` or a bignum.
///
/// # Errors
///
/// Returns the offending layout facts when they name no known scalar
/// encoding, so a consumer refuses the type instead of guessing a width.
pub fn scalar_plan(ty: &Type) -> Result<ScalarPlan, String> {
    let layout = layout_of_type(ty);
    match (layout.local(), layout.zero(), layout.rc(), layout.literal()) {
        (Repr::Immediate, ZeroPossibility::Always, RcBehavior::Trivial, LiteralCell::NoCell) => {
            Ok(ScalarPlan::ZeroWord)
        }
        (Repr::Immediate, ZeroPossibility::Never, RcBehavior::Trivial, LiteralCell::NoCell)
        | (
            Repr::NonNullValue,
            ZeroPossibility::Never,
            RcBehavior::RuntimeWord,
            LiteralCell::NoCell,
        ) => Ok(ScalarPlan::TaggedImmediate),
        (
            Repr::NonNullValue,
            ZeroPossibility::Never,
            RcBehavior::Managed,
            LiteralCell::Interned,
        ) => Ok(ScalarPlan::StaticCell),
        (Repr::NonNullValue, ZeroPossibility::Never, RcBehavior::Managed, LiteralCell::Boxed) => {
            Ok(ScalarPlan::FreshCell)
        }
        (local, zero, rc, literal) => Err(format!(
            "no scalar literal encoding for a layout of {local} / {zero:?} / {rc:?} / {literal:?}"
        )),
    }
}

/// Whether `a` is admitted as an `OrNull(a)` element.
///
/// This deliberately combines source-language policy with the physical proof:
/// the type must be on the supported policy list and the representation authority
/// must prove it is exactly one non-zero word. A flexible application is not
/// guessed to be boxed.
#[must_use]
pub fn is_or_null_element(a: &Type) -> bool {
    is_or_null_element_in(a, |_| false)
}

/// Declaration-aware `OrNull` element check.
///
/// `nominal_is_boxed` must return true only when the named type is known to keep
/// an allocated, non-zero wrapper after mandatory representation passes. This
/// proof is required because a `Type::Con` may name a transparent newtype.
#[must_use]
pub fn is_or_null_element_in(a: &Type, nominal_is_boxed: impl Fn(Sym) -> bool) -> bool {
    matches!(
        a,
        Type::Con(..) | Type::Int | Type::Bool | Type::I64 | Type::U64 | Type::Str | Type::Tuple(_)
    ) && layout_of_type_in(a, nominal_is_boxed).is_non_zero_word()
}

#[cfg(test)]
mod tests {
    use super::{
        is_or_null_element, is_or_null_element_in, layout_of_type, layout_of_type_in, repr_of_type,
        scalar_plan, AbiLayout, LiteralCell, RcBehavior, Repr, ScalarPlan, ZeroPossibility,
    };
    use crate::types::Type;
    use prism_common::sym::Sym;

    #[test]
    fn scalar_facts_distinguish_storage_zero_and_ownership() {
        let unit = layout_of_type(&Type::Unit);
        let boolean = layout_of_type(&Type::Bool);
        let i64_layout = layout_of_type(&Type::I64);

        assert_eq!(unit.local(), &Repr::Immediate);
        assert_eq!(unit.zero(), ZeroPossibility::Always);
        assert_eq!(boolean.local(), &Repr::Immediate);
        assert_eq!(boolean.zero(), ZeroPossibility::Never);
        assert_eq!(i64_layout.local(), &Repr::NonNullValue);
        assert_eq!(i64_layout.rc(), RcBehavior::Managed);
        assert_eq!(repr_of_type(&Type::U64), Repr::NonNullValue);

        // The literal-cell axis is what separates the managed scalars: same
        // storage/zero/ownership triple, different literal homes.
        assert_eq!(i64_layout.literal(), LiteralCell::Boxed);
        assert_eq!(layout_of_type(&Type::Str).literal(), LiteralCell::Interned);
        assert_eq!(layout_of_type(&Type::Int).literal(), LiteralCell::NoCell);
        assert_eq!(
            layout_of_type(&Type::Con(Sym::from("Box"), vec![])).literal(),
            LiteralCell::Unknown
        );
    }

    #[test]
    fn local_products_and_boundary_products_are_distinct() {
        let layout = layout_of_type(&Type::UnboxedTuple(vec![Type::Int, Type::Bool]));
        assert_eq!(
            layout.local(),
            &Repr::Product(vec![Repr::NonNullValue, Repr::Immediate])
        );
        assert_eq!(layout.local().field_width_words(), Some(2));
        assert_eq!(layout.abi(), &AbiLayout::BoxedProduct);
        assert_eq!(layout.abi().repr(), Some(Repr::NonNullValue));
    }

    #[test]
    fn undefined_layouts_fail_closed() {
        assert_eq!(Repr::Any.field_width_words(), None);
        assert_eq!(Repr::Any.alignment_words(), None);
        assert!(!Repr::Any.is_representable());

        let unresolved = layout_of_type(&Type::Var(Sym::from("a")));
        assert_eq!(unresolved.local(), &Repr::Any);
        assert_eq!(unresolved.abi(), &AbiLayout::OpaqueWord);

        let product = layout_of_type(&Type::UnboxedTuple(vec![Type::Exist(1)]));
        assert_eq!(product.abi(), &AbiLayout::Invalid);
        assert_eq!(product.local().field_width_words(), None);

        let type_level_nat = layout_of_type(&Type::Nat(1));
        assert_eq!(type_level_nat.abi(), &AbiLayout::Invalid);
    }

    #[test]
    fn or_null_requires_policy_and_a_non_zero_word_proof() {
        assert!(is_or_null_element(&Type::I64));
        assert!(is_or_null_element(&Type::Tuple(vec![Type::Unit])));
        assert!(!is_or_null_element(&Type::Unit));
        assert!(!is_or_null_element(&Type::Float));
        assert!(!is_or_null_element(&Type::App(
            Box::new(Type::Var(Sym::from("f"))),
            Box::new(Type::Int),
        )));

        let nominal = Type::Con(Sym::from("Box"), vec![Type::Unit]);
        assert!(!is_or_null_element(&nominal));
        assert!(is_or_null_element_in(&nominal, |_| true));
        assert_eq!(layout_of_type(&nominal).local(), &Repr::Any);
        assert_eq!(layout_of_type(&nominal).abi(), &AbiLayout::DeferredNominal);
        assert_eq!(layout_of_type(&nominal).abi().repr(), None);
        assert_eq!(repr_of_type(&nominal), Repr::Value);
        assert_eq!(
            layout_of_type_in(&nominal, |_| true).local(),
            &Repr::NonNullValue
        );

        let quantified = Type::Forall(Sym::from("a"), Box::new(nominal.clone()));
        assert_eq!(
            layout_of_type_in(&quantified, |_| true).local(),
            &Repr::NonNullValue
        );
        let product = Type::UnboxedTuple(vec![nominal]);
        assert_eq!(
            layout_of_type_in(&product, |_| true).abi(),
            &AbiLayout::BoxedProduct
        );
    }

    #[test]
    fn scalar_plans_follow_the_layout_facts() {
        assert_eq!(scalar_plan(&Type::Unit), Ok(ScalarPlan::ZeroWord));
        for ty in [Type::Int, Type::Bool, Type::Char] {
            assert_eq!(scalar_plan(&ty), Ok(ScalarPlan::TaggedImmediate));
        }
        assert_eq!(scalar_plan(&Type::Str), Ok(ScalarPlan::StaticCell));
        for ty in [Type::I64, Type::U64, Type::Float] {
            assert_eq!(scalar_plan(&ty), Ok(ScalarPlan::FreshCell));
        }
        // Only a fresh cell must be owned by the site that materializes it.
        assert!(ScalarPlan::FreshCell.owns_fresh_cell());
        for plan in [
            ScalarPlan::ZeroWord,
            ScalarPlan::TaggedImmediate,
            ScalarPlan::StaticCell,
        ] {
            assert!(!plan.owns_fresh_cell());
        }
        // No scalar encoding exists for a non-word or flexible layout; the
        // plan must refuse rather than guess.
        assert!(scalar_plan(&Type::Var(Sym::from("a"))).is_err());
        assert!(scalar_plan(&Type::UnboxedTuple(vec![Type::Int, Type::Bool])).is_err());
    }

    #[test]
    fn widths_and_alignment_are_checked_iteratively() {
        let repr = Repr::Product(vec![Repr::Bits64, Repr::Vec128]);
        assert_eq!(repr.field_width_words(), Some(3));
        assert_eq!(repr.alignment_words(), Some(2));
    }
}
