//! Runtime representation facts (`Repr`).
//!
//! A `Repr` records how a value is laid out and moved at runtime, independent of
//! its `Kind` (which classifies it at the type level). Every existing Prism value
//! is `Repr::Value`; the unboxed-values work (behind `PRISM_UNBOXED`) introduces
//! the non-`Value` reprs and the types that carry them. This module is the fact
//! table and the `Type -> Repr` query; nothing here yet drives lowering, so until
//! the unboxed front end lands every program observes `repr_of_type == Value` (or
//! `Immediate`) and behaves and hashes exactly as before.

use std::fmt;

use super::ty::Type;

/// How a value is represented at runtime.
///
/// A lattice ordered from the most general boxed form (`Value`) down to concrete
/// unboxed payloads, with `Any` the internal top used for abstract declarations
/// and signatures.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Repr {
    /// An ordinary boxed Prism value (a heap cell or a tagged immediate). The
    /// default for everything until a type opts into an unboxed representation.
    Value,
    /// A `Value` that is guaranteed not to be the null word, so it may back an
    /// `OrNull` slot. Heap pointers and tagged immediates qualify; `OrNull` does
    /// not.
    NonNullValue,
    /// A non-pointer word that `dup`/`drop` treat as a no-op (`Unit`, `Bool`,
    /// `Char`, the fixed-width `I64`/`U64`).
    Immediate,
    /// An unboxed 64-bit payload with no GC traversal.
    Bits64,
    /// An unboxed IEEE-754 double.
    Float64,
    /// An unboxed 128-bit SIMD payload (two words).
    Vec128,
    /// An unboxed product whose fields are carried as their component reprs.
    Product(Vec<Self>),
    /// The internal upper bound for signatures and abstract declarations. Not
    /// executable: a value of `Any` cannot be bound, passed, returned, matched,
    /// or stored until its concrete representation is known.
    Any,
}

impl Repr {
    /// Whether this repr occupies an ordinary GC-scanned value slot. True for the
    /// boxed and immediate forms; false for the raw unboxed payloads and `Any`.
    #[must_use]
    pub const fn is_gc_value(&self) -> bool {
        matches!(self, Self::Value | Self::NonNullValue | Self::Immediate)
    }

    /// Whether a value of this repr can be the null word. Only the plain boxed
    /// `Value` form is nullable; `NonNullValue` and the unboxed forms are not.
    #[must_use]
    pub const fn is_nullable(&self) -> bool {
        matches!(self, Self::Value)
    }

    /// Whether this repr names a concrete runtime layout. Everything except `Any`
    /// is representable; `Any` must be resolved before a value can exist.
    #[must_use]
    pub fn is_representable(&self) -> bool {
        match self {
            Self::Any => false,
            Self::Product(fields) => fields.iter().all(Self::is_representable),
            _ => true,
        }
    }

    /// The storage width in machine words. Word-sized forms are one word, `Vec128`
    /// is two, and a `Product` is the sum of its fields. `Any` has no defined
    /// layout: asking is a caller bug the representability check must catch
    /// first, so it trips a debug assertion (a hard failure everywhere tests
    /// run) rather than silently shaping an ABI around a placeholder width.
    #[must_use]
    pub fn field_width_words(&self) -> usize {
        debug_assert!(
            !matches!(self, Self::Any),
            "field_width_words on Repr::Any: check is_representable first"
        );
        match self {
            Self::Vec128 => 2,
            Self::Product(fields) => fields.iter().map(Self::field_width_words).sum(),
            _ => 1,
        }
    }
}

impl fmt::Display for Repr {
    /// A user-facing name for a representation, for diagnostics ("expected a boxed
    /// value, found an unboxed product").
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value => f.write_str("boxed value"),
            Self::NonNullValue => f.write_str("non-null value"),
            Self::Immediate => f.write_str("immediate word"),
            Self::Bits64 => f.write_str("unboxed i64"),
            Self::Float64 => f.write_str("unboxed f64"),
            Self::Vec128 => f.write_str("128-bit vector"),
            Self::Product(_) => f.write_str("unboxed product"),
            Self::Any => f.write_str("abstract representation"),
        }
    }
}

/// The runtime representation of a type.
///
/// Reads the scalar built-ins and, once the unboxed forms exist, the product and
/// null-option types; everything else is the boxed `Value` (or `Immediate` for the
/// non-pointer words). Type variables and abstract heads default to `Value`,
/// matching the pre-unboxed world.
#[must_use]
pub fn repr_of_type(ty: &Type) -> Repr {
    match ty {
        // Non-pointer words: dup/drop no-ops.
        Type::Unit | Type::Bool | Type::Char | Type::I64 | Type::U64 => Repr::Immediate,
        // A scheme's representation is its body's.
        Type::Forall(_, inner) | Type::RowForall(_, inner) => repr_of_type(inner),
        // Unboxed products carry their fields as component reprs.
        Type::UnboxedTuple(fields) => Repr::Product(fields.iter().map(repr_of_type).collect()),
        Type::UnboxedRecord(fields) => {
            Repr::Product(fields.iter().map(|(_, t)| repr_of_type(t)).collect())
        }
        // Rows and type-level nats are not value types; asking for their runtime
        // representation is a category error, so answer the non-executable top.
        Type::Row(_) | Type::Nat(_) => Repr::Any,
        // Everything else is an ordinary boxed value: arbitrary-precision `Int`,
        // `Float`, `Str`, functions, datatypes, and the existing boxed `Tuple`. A
        // non-allocating nullable (`OrNull`) also lands here: it sits in a value
        // slot but may hold the null word, so it is the plain (nullable) `Value`.
        // Unannotated variables and abstract heads default here too.
        _ => Repr::Value,
    }
}

/// Whether `a` is a sound element type for `OrNull(a)`: its runtime word is a
/// single value slot that is never the machine zero word.
///
/// So `Null` (the zero word) can never be confused with a present `This(v)`. Heap
/// pointers are non-zero by construction and tagged immediates are odd, so both
/// qualify. `Unit` is the zero word, `Float` and `Char` are excluded, an unboxed
/// product spans multiple words, and a bare type variable may instantiate to
/// `Unit`; only concrete, single-word, non-zero types are admitted. Nested
/// `OrNull` is rejected because the null word would be ambiguous.
#[must_use]
pub const fn is_or_null_element(a: &Type) -> bool {
    matches!(
        a,
        Type::Int
            | Type::Bool
            | Type::I64
            | Type::U64
            | Type::Str
            | Type::Con(..)
            | Type::App(..)
            | Type::Tuple(_)
    )
}

#[cfg(test)]
mod tests {
    use super::{repr_of_type, Repr};
    use crate::types::Type;

    #[test]
    fn scalars_and_boxed_have_expected_reprs() {
        assert_eq!(repr_of_type(&Type::Unit), Repr::Immediate);
        assert_eq!(repr_of_type(&Type::Bool), Repr::Immediate);
        assert_eq!(repr_of_type(&Type::I64), Repr::Immediate);
        // Arbitrary-precision `Int` and the boxed `Tuple` stay boxed values.
        assert_eq!(repr_of_type(&Type::Int), Repr::Value);
        assert_eq!(repr_of_type(&Type::Tuple(vec![Type::Int])), Repr::Value);
        // A scheme reports its body's representation.
        assert_eq!(
            repr_of_type(&Type::Forall("a".into(), Box::new(Type::Bool))),
            Repr::Immediate
        );
    }

    #[test]
    fn predicates() {
        assert!(Repr::Value.is_gc_value() && Repr::Value.is_nullable());
        assert!(Repr::Immediate.is_gc_value() && !Repr::Immediate.is_nullable());
        assert!(!Repr::Bits64.is_gc_value());
        assert!(!Repr::Any.is_representable());
        assert!(Repr::Product(vec![Repr::Bits64, Repr::Float64]).is_representable());
        assert_eq!(Repr::Vec128.field_width_words(), 2);
        assert_eq!(
            Repr::Product(vec![Repr::Bits64, Repr::Vec128]).field_width_words(),
            3
        );
    }
}
