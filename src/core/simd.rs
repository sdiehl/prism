//! The SIMD operation registry: names, identity, and shape.
//!
//! Each row is the single home for a vector op's stable enum variant, surface
//! name, content-hash tag, append-only wire index, arity, and lane type; the
//! wired builtins mirror these rows for execution. Tests freeze the hash tags
//! and require the wire indices to be dense and unique.
//!
//! The op set is the SSE2-compatible 128-bit vector (`Repr::Vec128`, two
//! words) in four lane interpretations: two f64/i64 lanes or four f32/i32
//! lanes. It excludes wider vectors and runtime CPU dispatch.

/// The 128-bit lane interpretation of a vector operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lane {
    /// Two IEEE-754 doubles.
    F64x2,
    /// Two 64-bit integers.
    I64x2,
    /// Four IEEE-754 singles.
    F32x4,
    /// Four 32-bit integers.
    I32x4,
}

impl Lane {
    /// The lane count: two 64-bit or four 32-bit elements per 128-bit vector.
    #[must_use]
    pub const fn count(self) -> usize {
        match self {
            Self::F64x2 | Self::I64x2 => 2,
            Self::F32x4 | Self::I32x4 => 4,
        }
    }

    /// The element width in bits; `count * width` is always 128.
    #[must_use]
    pub const fn width_bits(self) -> usize {
        match self {
            Self::F64x2 | Self::I64x2 => 64,
            Self::F32x4 | Self::I32x4 => 32,
        }
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
    F32Splat "simd_fsplat4" "SimdF32Splat" 14 1 F32x4;
    F32Extract "simd_fextract4" "SimdF32Extract" 15 2 F32x4;
    F32Add "simd_fadd4" "SimdF32Add" 16 2 F32x4;
    F32Sub "simd_fsub4" "SimdF32Sub" 17 2 F32x4;
    F32Mul "simd_fmul4" "SimdF32Mul" 18 2 F32x4;
    F32Min "simd_fmin4" "SimdF32Min" 19 2 F32x4;
    F32Max "simd_fmax4" "SimdF32Max" 20 2 F32x4;
    I32Splat "simd_isplat4" "SimdI32Splat" 21 1 I32x4;
    I32Extract "simd_iextract4" "SimdI32Extract" 22 2 I32x4;
    I32Add "simd_iadd4" "SimdI32Add" 23 2 I32x4;
    I32Sub "simd_isub4" "SimdI32Sub" 24 2 I32x4;
    I32And "simd_iand4" "SimdI32And" 25 2 I32x4;
    I32Or "simd_ior4" "SimdI32Or" 26 2 I32x4;
    I32Xor "simd_ixor4" "SimdI32Xor" 27 2 I32x4;
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
            (SimdOp::F32Splat, "SimdF32Splat"),
            (SimdOp::F32Extract, "SimdF32Extract"),
            (SimdOp::F32Add, "SimdF32Add"),
            (SimdOp::F32Sub, "SimdF32Sub"),
            (SimdOp::F32Mul, "SimdF32Mul"),
            (SimdOp::F32Min, "SimdF32Min"),
            (SimdOp::F32Max, "SimdF32Max"),
            (SimdOp::I32Splat, "SimdI32Splat"),
            (SimdOp::I32Extract, "SimdI32Extract"),
            (SimdOp::I32Add, "SimdI32Add"),
            (SimdOp::I32Sub, "SimdI32Sub"),
            (SimdOp::I32And, "SimdI32And"),
            (SimdOp::I32Or, "SimdI32Or"),
            (SimdOp::I32Xor, "SimdI32Xor"),
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

    // Lane geometry is the invariant every consumer packs and unpacks by:
    // count times width is one 128-bit vector for every lane interpretation.
    #[test]
    fn lanes_fill_the_vector() {
        for op in SimdOp::ALL {
            let lane = op.lane();
            assert_eq!(lane.count() * lane.width_bits(), 128);
        }
    }
}
