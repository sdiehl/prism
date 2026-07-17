//! The registry-only SIMD operation set: names, identity, and shape.
//!
//! Each row is the single home for a vector op's stable enum variant, surface
//! name, content-hash tag, append-only wire index, arity, and lane type. The
//! elaborator, backends, and interpreter do not recognize these operations, so
//! programs cannot execute them. Tests freeze the hash tags and require the wire
//! indices to be dense and unique.
//!
//! The op set is the SSE2-compatible 128-bit baseline only: two f64 lanes or two
//! i64 lanes per vector (`Repr::Vec128`, two words). It excludes wider vectors,
//! runtime CPU dispatch, and float32 lanes.

/// The 128-bit lane interpretation of a vector operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lane {
    /// Two IEEE-754 doubles.
    F64x2,
    /// Two 64-bit integers.
    I64x2,
}

impl Lane {
    /// The lane count; the element width is always 64 bits in the baseline.
    #[must_use]
    pub const fn count(self) -> usize {
        2
    }
}

// One declarative registry for the baseline vector ops. The macro fans a row out
// to the enum and the accessors exactly as `float_ops!` does; adding an op is one
// row, and the wire index is explicit and append-only.
macro_rules! simd_ops {
    ( $(
        $variant:ident $name:literal $tag:literal $wire:literal $arity:literal $lane:ident ;
    )* ) => {
        /// A baseline 128-bit vector operation. Registry-only: unavailable to
        /// elaboration and backend lowering.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum SimdOp { $( $variant, )* }

        impl SimdOp {
            pub const ALL: &'static [Self] = &[ $( Self::$variant, )* ];

            /// Surface name the elaborator will key off when the ops are wired.
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self { $( Self::$variant => $name, )* }
            }

            /// Stable content-hash tag, independent of the enum variant name.
            #[must_use]
            pub const fn hash_tag(self) -> &'static str {
                match self { $( Self::$variant => $tag, )* }
            }

            /// Stable, append-only wire number for the store and kont codecs.
            #[must_use]
            pub const fn wire(self) -> u64 {
                match self { $( Self::$variant => $wire, )* }
            }

            /// Inverse of [`SimdOp::wire`]; `None` on an unknown index.
            #[must_use]
            pub const fn from_wire(n: u64) -> Option<Self> {
                match n { $( $wire => Some(Self::$variant), )* _ => None }
            }

            /// Surface arity.
            #[must_use]
            pub const fn arity(self) -> usize {
                match self { $( Self::$variant => $arity, )* }
            }

            /// Lane interpretation of the operands.
            #[must_use]
            pub const fn lane(self) -> Lane {
                match self { $( Self::$variant => Lane::$lane, )* }
            }

            #[must_use]
            pub fn from_name(s: &str) -> Option<Self> {
                Self::ALL.iter().copied().find(|o| o.name() == s)
            }
        }
    };
}

simd_ops! {
    FSplat "simd_fsplat" "SimdFSplat" 0 1 F64x2;
    FExtract "simd_fextract" "SimdFExtract" 1 2 F64x2;
    FAdd "simd_fadd" "SimdFAdd" 2 2 F64x2;
    FSub "simd_fsub" "SimdFSub" 3 2 F64x2;
    FMul "simd_fmul" "SimdFMul" 4 2 F64x2;
    FMin "simd_fmin" "SimdFMin" 5 2 F64x2;
    FMax "simd_fmax" "SimdFMax" 6 2 F64x2;
    ISplat "simd_isplat" "SimdISplat" 7 1 I64x2;
    IExtract "simd_iextract" "SimdIExtract" 8 2 I64x2;
    IAdd "simd_iadd" "SimdIAdd" 9 2 I64x2;
    ISub "simd_isub" "SimdISub" 10 2 I64x2;
    IAnd "simd_iand" "SimdIAnd" 11 2 I64x2;
    IOr "simd_ior" "SimdIOr" 12 2 I64x2;
    IXor "simd_ixor" "SimdIXor" 13 2 I64x2;
}

// Ops in wire order: the compile-time guard that the wire space is dense and
// unique from zero, the same discipline as `BUILTINS_BY_WIRE`.
const SIMD_OPS_BY_WIRE_ARR: [SimdOp; SimdOp::ALL.len()] = {
    let mut arr = [SimdOp::ALL[0]; SimdOp::ALL.len()];
    let mut i = 0;
    while i < arr.len() {
        arr[i] = match SimdOp::from_wire(i as u64) {
            Some(op) => op,
            None => panic!("simd op wire indices must be dense and unique from zero"),
        };
        i += 1;
    }
    arr
};

/// Ops in wire order, the single source a codec will number from.
pub const SIMD_OPS_BY_WIRE: &[SimdOp] = &SIMD_OPS_BY_WIRE_ARR;

#[cfg(test)]
mod tests {
    use super::{SimdOp, SIMD_OPS_BY_WIRE};

    // The hash tags are content-addressing identity: a rename of a variant or
    // surface name must not move them. Frozen exactly as the builtin and float
    // registries freeze theirs.
    #[test]
    fn simd_hash_tags_are_frozen() {
        let frozen = [
            (SimdOp::FSplat, "SimdFSplat"),
            (SimdOp::FExtract, "SimdFExtract"),
            (SimdOp::FAdd, "SimdFAdd"),
            (SimdOp::FSub, "SimdFSub"),
            (SimdOp::FMul, "SimdFMul"),
            (SimdOp::FMin, "SimdFMin"),
            (SimdOp::FMax, "SimdFMax"),
            (SimdOp::ISplat, "SimdISplat"),
            (SimdOp::IExtract, "SimdIExtract"),
            (SimdOp::IAdd, "SimdIAdd"),
            (SimdOp::ISub, "SimdISub"),
            (SimdOp::IAnd, "SimdIAnd"),
            (SimdOp::IOr, "SimdIOr"),
            (SimdOp::IXor, "SimdIXor"),
        ];
        assert_eq!(frozen.len(), SimdOp::ALL.len());
        for (op, tag) in frozen {
            assert_eq!(op.hash_tag(), tag);
        }
    }

    #[test]
    fn simd_wire_order_and_names_round_trip() {
        for (i, op) in SIMD_OPS_BY_WIRE.iter().enumerate() {
            assert_eq!(op.wire(), i as u64);
            assert_eq!(SimdOp::from_name(op.name()), Some(*op));
        }
    }

    #[test]
    fn baseline_lanes_are_two_wide() {
        for op in SimdOp::ALL {
            assert_eq!(op.lane().count(), 2);
        }
    }
}
