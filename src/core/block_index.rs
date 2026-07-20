//! Block-index encoding: the `Bits64` packing for `IdxImm`/`IdxMut`.
//!
//! A block index is a typed offset into a boxed aggregate or a nested unboxed
//! field. At runtime it is a single unboxed word (`Repr::Bits64`,
//! `src/types/repr.rs`) with two packed fields:
//!
//! * the low [`OFFSET_BITS`] bits are the byte offset from the aggregate's base;
//! * the high [`GAP_BITS`] bits are the *gap*, the distance between the
//!   GC-scanned value region and the non-GC payload region of a mixed boxed
//!   record. The gap is zero whenever the index does not cross a mixed-product
//!   boundary, in which case all 64 bits read back as the byte offset (a zero gap
//!   contributes nothing to the packed word).
//!
//! Mutability (`IdxImm` versus `IdxMut`) is a compile-time distinction carried by
//! the type head and by which Core node consumes the index (`IdxGetImm` versus
//! `IdxGetMut`/`IdxSetMut`); it is never a runtime bit, so it does not appear in
//! the packed word. The whole point of a single `Bits64` word is that the
//! representation is invisible except through cost: two programs that differ only
//! in which lowering fired produce the same word.
//!
//! This module is the one canonical home for the packing layout. Every consumer
//! (elaboration that builds an index, codegen that emits the load/store, the
//! interpreter oracle) references these constants rather than re-deriving the bit
//! positions.

use std::fmt;

/// Bit width of the byte-offset field (the low bits of the word).
pub const OFFSET_BITS: u32 = 48;
/// Bit width of the gap field (the high bits of the word).
pub const GAP_BITS: u32 = 16;

// The two fields tile the whole 64-bit word with no spare bits: a byte offset and
// a region gap and nothing else. Asserting it here means a future re-split cannot
// silently drop bits.
const _: () = assert!(OFFSET_BITS + GAP_BITS == 64, "block index must tile a u64");

/// Bit position where the gap field starts (immediately above the offset field).
pub const GAP_SHIFT: u32 = OFFSET_BITS;

/// Mask selecting the byte-offset field.
pub const OFFSET_MASK: u64 = (1u64 << OFFSET_BITS) - 1;
/// Mask selecting the gap field once shifted down to bit 0.
pub const GAP_MASK: u64 = (1u64 << GAP_BITS) - 1;

/// Largest representable byte offset.
pub const MAX_OFFSET: u64 = OFFSET_MASK;
/// Largest representable region gap.
pub const MAX_GAP: u64 = GAP_MASK;

/// Whether a block index may be written, the compile-time `IdxImm`/`IdxMut`
/// distinction.
///
/// `Imm` indices come from immutable paths and only feed `IdxGetImm`; `Mut`
/// indices come from a mutable field, mutable array, or mutable deepening step and
/// feed `IdxGetMut`/`IdxSetMut`. The kind travels on the index value so the Core
/// Lint can reject an `IdxSetMut` reached through an `Imm` index. It is erased
/// before runtime: it never reaches the packed [`pack`] word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IdxKind {
    /// An immutable index; read-only.
    Imm,
    /// A mutable index; read or write.
    Mut,
}

impl IdxKind {
    /// Stable content-hash tag, byte-identical to the variant spelling and
    /// independent of the enum name. The one home for these two spellings, which
    /// the type heads (`IdxImm`/`IdxMut`), the Core nodes, and any content hash of
    /// an index all commit to.
    #[must_use]
    pub const fn hash_tag(self) -> &'static str {
        match self {
            Self::Imm => "Imm",
            Self::Mut => "Mut",
        }
    }

    /// Whether an index of this kind may back a write (`IdxSetMut`). Only `Mut`
    /// qualifies; the Core Lint reads this to flag a write through an `Imm` index.
    #[must_use]
    pub const fn is_writable(self) -> bool {
        matches!(self, Self::Mut)
    }
}

/// A field that overflowed its packed width, so [`pack`] refused the index.
///
/// Reported when an aggregate is too large to address with the fixed encoding, so
/// index creation is rejected rather than silently truncated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Overflow {
    /// The byte offset exceeded [`MAX_OFFSET`].
    Offset(u64),
    /// The region gap exceeded [`MAX_GAP`].
    Gap(u64),
}

impl fmt::Display for Overflow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Offset(n) => write!(
                f,
                "block-index byte offset {n} exceeds the {MAX_OFFSET}-byte encoding limit"
            ),
            Self::Gap(n) => write!(
                f,
                "block-index region gap {n} exceeds the {MAX_GAP}-word encoding limit"
            ),
        }
    }
}

/// Pack a byte offset and a region gap into a single `Bits64` word, or report the
/// field that overflowed the fixed encoding.
///
/// # Errors
/// Returns [`Overflow`] naming the field (offset or gap) that did not fit.
pub const fn pack(offset: u64, gap: u64) -> Result<u64, Overflow> {
    if offset > MAX_OFFSET {
        return Err(Overflow::Offset(offset));
    }
    if gap > MAX_GAP {
        return Err(Overflow::Gap(gap));
    }
    Ok(offset | (gap << GAP_SHIFT))
}

/// The byte offset packed into `word`.
#[must_use]
pub const fn offset_of(word: u64) -> u64 {
    word & OFFSET_MASK
}

/// The region gap packed into `word`.
#[must_use]
pub const fn gap_of(word: u64) -> u64 {
    (word >> GAP_SHIFT) & GAP_MASK
}

#[cfg(test)]
mod tests {
    use super::{gap_of, offset_of, pack, IdxKind, Overflow, MAX_GAP, MAX_OFFSET};

    #[test]
    fn idx_kind_tags_are_frozen_and_distinct() {
        // The content hash commits to these spellings; freezing them here turns a
        // rename that also touched the tag into a test failure.
        assert_eq!(IdxKind::Imm.hash_tag(), "Imm");
        assert_eq!(IdxKind::Mut.hash_tag(), "Mut");
        assert_ne!(IdxKind::Imm.hash_tag(), IdxKind::Mut.hash_tag());
        // Only a mutable index may back a write; the Core Lint reads this.
        assert!(!IdxKind::Imm.is_writable());
        assert!(IdxKind::Mut.is_writable());
    }

    #[test]
    fn round_trips_offset_and_gap() {
        for (offset, gap) in [(0, 0), (8, 0), (24, 1), (MAX_OFFSET, MAX_GAP), (4096, 3)] {
            let word = pack(offset, gap).expect("in range");
            assert_eq!(offset_of(word), offset);
            assert_eq!(gap_of(word), gap);
        }
    }

    #[test]
    fn a_zero_gap_leaves_the_whole_word_as_the_offset() {
        // The common case: an index that crosses no mixed-product boundary reads
        // back as a bare byte offset, no gap bits set.
        let word = pack(1234, 0).expect("in range");
        assert_eq!(word, 1234);
        assert_eq!(offset_of(word), 1234);
        assert_eq!(gap_of(word), 0);
    }

    #[test]
    fn rejects_out_of_range_fields() {
        assert_eq!(
            pack(MAX_OFFSET + 1, 0),
            Err(Overflow::Offset(MAX_OFFSET + 1))
        );
        assert_eq!(pack(0, MAX_GAP + 1), Err(Overflow::Gap(MAX_GAP + 1)));
    }
}
