//! Single source of truth for builtins: surface name, arity, lowering kind.
//!
//! Consumed by the elaborator (arity map, head dispatch), the REPL session,
//! and the backend preludes (runtime declares).

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinKind {
    Print,
    Println,
    ReadInt,
    ReadLine,
    Error,
    Rand,
    Srand,
    Float,
    Str,
    Int,
    Coerce,
}

// Every inline float op is surface-callable at this arity with this dispatch
// kind, so the two facts are uniform across the family and generated once here
// rather than repeated on every registry row.
const FLOAT_ARITY: usize = 1;
const FLOAT_KIND: BuiltinKind = BuiltinKind::Float;

// One declarative registry for the inline floating-point op family the elaborator
// emits as `Comp::FloatBuiltin`. Each row is the single home for a float op's
// variant, surface name, content-hash tag, stable wire index, type signature, and
// (for a transcendental) its owned-libm runtime symbol. The macro fans a row out
// to the enum, the accessors, the codec wire number, and the signature the type
// checker seeds; adding a float op is one row.
//
// Three lowering classes, distinguished by [`FloatOp::runtime_sym`] and the
// exhaustive match in codegen:
// - int/float conversions (`to_float`, `truncate`, `floor_to_int`, `ceil_to_int`):
//   int<->float casts with pinned saturating rounding;
// - exact float->float ops (`abs_float`, `sqrt`, `floor`, `ceil`, `round`,
//   `trunc`): correctly rounded / exact on every IEEE-754 platform, so they lower
//   to hardware intrinsics and carry no runtime symbol;
// - transcendentals (the rest): platform libm would diverge in the last bit, so
//   each carries the owned vendored-libm symbol (`sym "prism_m_*"`), the one
//   canonical place that `prism_m_*` ABI contract lives, the analogue of
//   [`Builtin::sym`]; codegen and the interpreter both dispatch off it.
//
// Binary math (`pow`, `atan2`, `hypot`, `fmod`) is not here: those take two
// arguments and ride the boxed-float [`Builtin`] path instead.
//
// The wire index is EXPLICIT per row and decoupled from both enum and row order:
// it is the store's append-only content-format tag, guarded dense-and-unique from
// zero by `FLOAT_OPS_BY_WIRE`. The hash tag stays byte-identical across renames
// (frozen by `float_op_hash_tags_are_frozen`) because the content hash commits to
// it.
macro_rules! float_ops {
    ( $(
        $variant:ident $name:literal $tag:literal $wire:literal $sig:literal
            $( sym $sym:literal )? ;
    )* ) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
        pub enum FloatOp { $( $variant, )* }

        impl FloatOp {
            pub(crate) const ALL: &'static [Self] = &[ $( Self::$variant, )* ];

            /// Surface name; the single string source the IR, interpreter
            /// dispatch, and codegen all key off.
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

            /// Inverse of [`FloatOp::wire`]; `None` on an unknown index.
            #[must_use]
            pub const fn from_wire(n: u64) -> Option<Self> {
                match n { $( $wire => Some(Self::$variant), )* _ => None }
            }

            /// The type signature the checker seeds for this op.
            #[must_use]
            pub const fn signature(self) -> &'static str {
                match self { $( Self::$variant => $sig, )* }
            }

            /// The owned-libm C symbol a transcendental routes to on native and
            /// via FFI in the interpreter, or `None` for the conversions and exact
            /// ops (which lower to casts/intrinsics with no owned implementation).
            #[must_use]
            pub const fn runtime_sym(self) -> Option<&'static str> {
                match self { $( Self::$variant => float_ops!(@sym $($sym)?), )* }
            }

            #[must_use]
            pub fn from_name(s: &str) -> Option<Self> {
                Self::ALL.iter().copied().find(|o| o.name() == s)
            }
        }
    };
    (@sym $sym:literal) => { Some($sym) };
    (@sym) => { None };
}

float_ops! {
    ToFloat "to_float" "ToFloat" 0 "(Int) -> Float";
    Truncate "truncate" "Truncate" 1 "(Float) -> Int";
    FloorToInt "floor_to_int" "FloorToInt" 2 "(Float) -> Int";
    CeilToInt "ceil_to_int" "CeilToInt" 3 "(Float) -> Int";
    AbsFloat "abs_float" "AbsFloat" 4 "(Float) -> Float";
    Sqrt "sqrt" "Sqrt" 5 "(Float) -> Float";
    Floor "floor" "Floor" 10 "(Float) -> Float";
    Ceil "ceil" "Ceil" 11 "(Float) -> Float";
    Round "round" "Round" 12 "(Float) -> Float";
    Trunc "trunc" "Trunc" 13 "(Float) -> Float";
    Sin "sin" "Sin" 6 "(Float) -> Float" sym "prism_m_sin";
    Cos "cos" "Cos" 7 "(Float) -> Float" sym "prism_m_cos";
    Tan "tan" "Tan" 14 "(Float) -> Float" sym "prism_m_tan";
    Asin "asin" "Asin" 15 "(Float) -> Float" sym "prism_m_asin";
    Acos "acos" "Acos" 16 "(Float) -> Float" sym "prism_m_acos";
    Atan "atan" "Atan" 17 "(Float) -> Float" sym "prism_m_atan";
    Sinh "sinh" "Sinh" 18 "(Float) -> Float" sym "prism_m_sinh";
    Cosh "cosh" "Cosh" 19 "(Float) -> Float" sym "prism_m_cosh";
    Tanh "tanh" "Tanh" 20 "(Float) -> Float" sym "prism_m_tanh";
    Exp "exp" "Exp" 8 "(Float) -> Float" sym "prism_m_exp";
    Exp2 "exp2" "Exp2" 21 "(Float) -> Float" sym "prism_m_exp2";
    Expm1 "expm1" "Expm1" 22 "(Float) -> Float" sym "prism_m_expm1";
    Ln "ln" "Ln" 9 "(Float) -> Float" sym "prism_m_log";
    Log2 "log2" "Log2" 23 "(Float) -> Float" sym "prism_m_log2";
    Log10 "log10" "Log10" 24 "(Float) -> Float" sym "prism_m_log10";
    Log1p "log1p" "Log1p" 25 "(Float) -> Float" sym "prism_m_log1p";
    Cbrt "cbrt" "Cbrt" 26 "(Float) -> Float" sym "prism_m_cbrt";
}

// Float ops in wire order: index `i` holds the op whose [`FloatOp::wire`] is `i`.
// Built from the per-row wire numbers so it cannot drift, the analogue of
// [`BUILTINS_BY_WIRE`]. The const evaluation panics if the wire numbers are not
// dense and unique from zero, the compile-time guard that the append-only float
// wire space stays intact.
const FLOAT_OPS_BY_WIRE_ARR: [FloatOp; FloatOp::ALL.len()] = {
    let mut arr = [FloatOp::ALL[0]; FloatOp::ALL.len()];
    let mut i = 0;
    while i < arr.len() {
        arr[i] = match FloatOp::from_wire(i as u64) {
            Some(f) => f,
            None => panic!("float op wire indices must be dense and unique from zero"),
        };
        i += 1;
    }
    arr
};

/// Float ops in wire order, the single source the store and kont codecs number
/// from. See [`FloatOp::wire`].
pub const FLOAT_OPS_BY_WIRE: &[FloatOp] = &FLOAT_OPS_BY_WIRE_ARR;

/// Every inline float op with its uniform surface arity and dispatch kind, for the
/// elaborator's arity map and head dispatch. Sourced from the one registry so the
/// name set cannot drift from the enum.
#[must_use]
pub fn float_surface(name: &str) -> Option<(usize, BuiltinKind)> {
    FloatOp::from_name(name).map(|_| (FLOAT_ARITY, FLOAT_KIND))
}

/// Representation of one runtime-call argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(feature = "native")]
pub(crate) enum AbiArg {
    Raw,
    Immediate,
    BoxedFloat,
}

/// Representation of a runtime-call result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(feature = "native")]
pub(crate) enum AbiResult {
    Raw,
    RetagImmediate,
}

/// Calling convention for one `prism_*` runtime builtin.
///
/// Construction checks that an argument cannot be both immediate and boxed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(feature = "native")]
pub(crate) struct AbiSpec {
    immediate: &'static [usize],
    boxed_float: &'static [usize],
    result: AbiResult,
}

#[cfg(feature = "native")]
impl AbiSpec {
    const fn new(
        immediate: &'static [usize],
        boxed_float: &'static [usize],
        result: AbiResult,
    ) -> Self {
        let mut i = 0;
        while i < immediate.len() {
            let mut j = 0;
            while j < boxed_float.len() {
                assert!(
                    immediate[i] != boxed_float[j],
                    "conflicting builtin ABI argument"
                );
                j += 1;
            }
            i += 1;
        }
        Self {
            immediate,
            boxed_float,
            result,
        }
    }

    #[must_use]
    pub(crate) fn arg(self, index: usize) -> AbiArg {
        if self.immediate.contains(&index) {
            AbiArg::Immediate
        } else if self.boxed_float.contains(&index) {
            AbiArg::BoxedFloat
        } else {
            AbiArg::Raw
        }
    }

    #[must_use]
    pub(crate) const fn result(self) -> AbiResult {
        self.result
    }

    #[cfg(test)]
    pub(crate) fn args_within(self, arity: usize) -> bool {
        self.immediate
            .iter()
            .chain(self.boxed_float)
            .all(|i| *i < arity)
    }
}

// The calling conventions the runtime builtins use, named once so each registry
// row states its convention by name instead of an inline tuple.
//
// Default: every argument passes raw and the result is a cell or already-tagged
// word (string ops, fixed-width arithmetic on boxed cells, elaborator-only ops).
#[cfg(feature = "native")]
const RAW: AbiSpec = AbiSpec::new(&[], &[], AbiResult::Raw);
// Bare-integer result to retag (predicates, lengths, exit codes).
#[cfg(feature = "native")]
const RETAG: AbiSpec = AbiSpec::new(&[], &[], AbiResult::RetagImmediate);
// Index arg raw; bare-integer (char/byte) result to retag.
#[cfg(feature = "native")]
const IDX1_RETAG: AbiSpec = AbiSpec::new(&[1], &[], AbiResult::RetagImmediate);
// Index arg raw; element/array result (cell or polymorphic) passes through.
#[cfg(feature = "native")]
const IDX1: AbiSpec = AbiSpec::new(&[1], &[], AbiResult::Raw);
// Single immediate arg (bool/char/index/exit/capacity); raw result.
#[cfg(feature = "native")]
const IMM0: AbiSpec = AbiSpec::new(&[0], &[], AbiResult::Raw);
// Two immediate args (length and init byte); cell result.
#[cfg(feature = "native")]
const IMM01: AbiSpec = AbiSpec::new(&[0, 1], &[], AbiResult::Raw);
// One boxed-float arg; raw result.
#[cfg(feature = "native")]
const F0: AbiSpec = AbiSpec::new(&[], &[0], AbiResult::Raw);
// Float arg 0, immediate arg 1; raw result.
#[cfg(feature = "native")]
const F0_IMM1: AbiSpec = AbiSpec::new(&[1], &[0], AbiResult::Raw);
// Two boxed-float args; boxed-float result.
#[cfg(feature = "native")]
const F01: AbiSpec = AbiSpec::new(&[], &[0, 1], AbiResult::Raw);
// Two immediate index/length args; cell result (a fresh string or buffer).
#[cfg(feature = "native")]
const IDX12: AbiSpec = AbiSpec::new(&[1, 2], &[], AbiResult::Raw);
// Immediate length arg 0, boxed-float init arg 1; cell result (a typed buffer).
#[cfg(feature = "native")]
const IMM0_F1: AbiSpec = AbiSpec::new(&[0], &[1], AbiResult::Raw);
// Buffer arg raw, immediate index arg 1, boxed-float value arg 2; cell result.
#[cfg(feature = "native")]
const IDX1_F2: AbiSpec = AbiSpec::new(&[1], &[2], AbiResult::Raw);
// Two buffer args raw, immediate index/length args 1, 3, 4; cell result (blit).
#[cfg(feature = "native")]
const IDX134: AbiSpec = AbiSpec::new(&[1, 3, 4], &[], AbiResult::Raw);

// Platform facts a builtin can carry. `OffPlatform` touches the host OS (file IO,
// env, process, args), so it has no implementation in a browser build and is
// rejected up front. `NativeDeferred` has a full interpreter implementation but no
// C runtime symbol yet, so native codegen refuses to lower it rather than emitting
// a call to an undefined `prism_*` symbol that would only surface as a link error.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Flag {
    OffPlatform,
    NativeDeferred,
}

// One declarative registry for the runtime-call builtin family. Each row is the
// single home for a builtin's variant, surface name, content-hash tag, stable wire
// index, calling convention, optional platform flags, and (for a surface-callable
// builtin) its arity, dispatch kind, and type signature. Adding a builtin is one
// row; the macro fans it out to the enum, the accessors, the codec wire number,
// the surface arity/kind table, and the signature the type checker seeds. The
// `non_enum_surface` block lists the surface builtins that are not members of this
// enum (output, float ops, coercions) and so carry only an arity and a kind.
//
// The wire index is EXPLICIT per row and decoupled from both enum order and row
// order: it is the store's append-only content-format tag and feeds nothing but
// the codec. A new row takes the next free index; a reorder would corrupt every
// serialized program. `wire_indices_are_dense_and_unique` guards that. The hash tag
// likewise stays byte-identical across renames (frozen by
// `builtin_hash_tags_are_frozen`) because the content hash commits to it.
macro_rules! builtins {
    (
        non_enum_surface: [ $( ($ne_name:literal, $ne_arity:literal, $ne_kind:ident) ),* $(,)? ],
        registry: [ $(
            $variant:ident $name:literal $tag:literal $wire:literal $abi:ident
                $( surface $arity:literal $kind:ident $sig:literal )?
                $( flags [ $( $flag:ident ),* ] )?
            ;
        )* ]
    ) => {
        /// Runtime-call builtin the elaborator emits as `Comp::StrBuiltin`.
        ///
        /// Lowered to a `prism_*` C call. Spans surface builtins (`concat`,
        /// `show_int`, ...) and compiler-internal ops never surface-callable
        /// (`show_i64`/`show_u64`, fixed-width arithmetic). `name()` is the single
        /// string source; the IR, interpreter dispatch, and codegen all key off
        /// the enum so a name can never drift.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
        pub enum Builtin { $( $variant, )* }

        impl Builtin {
            pub(crate) const ALL: &'static [Self] = &[ $( Self::$variant, )* ];

            /// Surface name; the single string source the IR, interpreter
            /// dispatch, and codegen all key off.
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self { $( Self::$variant => $name, )* }
            }

            /// Stable content-hash tag, independent of the enum variant name.
            #[must_use]
            pub const fn hash_tag(self) -> &'static str {
                match self { $( Self::$variant => $tag, )* }
            }

            /// Calling convention for the runtime call this builtin lowers to.
            #[cfg(feature = "native")]
            #[must_use]
            pub(crate) const fn abi(self) -> AbiSpec {
                match self { $( Self::$variant => $abi, )* }
            }

            /// Stable, append-only wire number for the store codec.
            #[must_use]
            pub const fn wire(self) -> u64 {
                match self { $( Self::$variant => $wire, )* }
            }

            /// Inverse of [`Builtin::wire`]; `None` on an unknown index.
            #[must_use]
            pub const fn from_wire(n: u64) -> Option<Self> {
                match n { $( $wire => Some(Self::$variant), )* _ => None }
            }

            const fn flags(self) -> &'static [Flag] {
                match self { $( Self::$variant => &[ $( $( Flag::$flag ),* )? ], )* }
            }

            /// Touches the host OS, so it has no browser implementation.
            #[must_use]
            pub fn off_platform(self) -> bool {
                self.flags().contains(&Flag::OffPlatform)
            }

            /// Has an interpreter implementation but no C runtime symbol yet, so
            /// native codegen refuses to lower it.
            #[must_use]
            pub fn native_deferred(self) -> bool {
                self.flags().contains(&Flag::NativeDeferred)
            }

            /// Surface arity and dispatch kind, or `None` for an elaborator-only
            /// builtin that is never surface-callable.
            #[must_use]
            pub const fn surface(self) -> Option<(usize, BuiltinKind)> {
                match self {
                    $( $( Self::$variant => Some(($arity, BuiltinKind::$kind)), )? )*
                    _ => None,
                }
            }

            /// The type signature the checker seeds for a surface builtin.
            #[must_use]
            pub const fn signature(self) -> Option<&'static str> {
                match self {
                    $( $( Self::$variant => Some($sig), )? )*
                    _ => None,
                }
            }
        }

        /// Surface builtins with their arity and dispatch kind.
        ///
        /// The members of this enum that are surface-callable, plus the non-enum
        /// surface builtins, in one table for the elaborator's arity map and head
        /// dispatch.
        pub const BUILTINS: &[(&str, usize, BuiltinKind)] = &[
            $( ($ne_name, $ne_arity, BuiltinKind::$ne_kind), )*
            $( $( ($name, $arity, BuiltinKind::$kind), )? )*
        ];
    };
}

builtins! {
    non_enum_surface: [
        ("print", 1, Print),
        ("println", 1, Println),
        ("prim_print", 1, Print),
        ("prim_println", 1, Println),
        ("prim_read_int", 0, ReadInt),
        ("prim_read_line", 0, ReadLine),
        ("error", 1, Error),
        ("fatal", 1, Error),
        ("prim_rand", 0, Rand),
        ("srand", 1, Srand),
        ("ord", 1, Coerce),
        ("chr", 1, Coerce),
    ],
    registry: [
    Concat "concat" "Concat" 0 RAW surface 2 Str "(String, String) -> String";
    StrLen "str_len" "StrLen" 1 RETAG surface 1 Str "(String) -> Int";
    StrEq "str_eq" "StrEq" 2 RETAG surface 2 Str "(String, String) -> Bool";
    StrCmp "str_cmp" "StrCmp" 3 RETAG surface 2 Str "(String, String) -> Int";
    Substring "substring" "Substring" 4 IDX12 surface 3 Str "(String, Int, Int) -> String";
    CharAt "char_at" "CharAt" 5 IDX1_RETAG surface 2 Str "(String, Int) -> Int";
    ShowChar "show_char" "ShowChar" 6 IMM0 surface 1 Str "(Char) -> String";
    Blake3 "blake3" "Blake3" 7 RAW surface 1 Str "(String) -> String";
    ParseInt "parse_int" "ParseInt" 8 RAW surface 1 Str "(String) -> Option(Int)";
    BigLit "big_lit" "BigLit" 9 RAW;
    ParseFloat "parse_float" "ParseFloat" 10 RAW surface 1 Str "(String) -> Float";
    PowFloat "pow_float" "PowFloat" 11 F01 surface 2 Str "(Float, Float) -> Float";
    Atan2 "atan2" "Atan2" 70 F01 surface 2 Str "(Float, Float) -> Float";
    Hypot "hypot" "Hypot" 71 F01 surface 2 Str "(Float, Float) -> Float";
    Fmod "fmod" "Fmod" 72 F01 surface 2 Str "(Float, Float) -> Float";
    ShowFloatPrec "show_float_prec" "ShowFloatPrec" 12 F0_IMM1 surface 2 Str "(Float, Int) -> String";
    ProbeEnabled "probe_enabled" "ProbeEnabled" 94 RETAG surface 1 Str "(String) -> Bool";
    Getenv "prim_getenv" "Getenv" 13 RAW surface 1 Str "(String) -> String ! {IO}";
    ReadFile "prim_read_file" "ReadFile" 14 RAW surface 1 Str "(String) -> String ! {IO}";
    ReadBytesFile "prim_read_bytes" "ReadBytesFile" 73 RAW surface 1 Str "(String) -> Buf ! {IO}";
    WriteBytesFile "prim_write_bytes" "WriteBytesFile" 74 RAW surface 2 Str "(String, Buf) -> Result(Unit, String) ! {IO}" flags [OffPlatform];
    WriteFile "write_file" "WriteFile" 15 RAW surface 2 Str "(String, String) -> Result(Unit, String) ! {IO}" flags [OffPlatform];
    FileExists "prim_file_exists" "FileExists" 16 RETAG surface 1 Str "(String) -> Bool ! {IO}";
    AppendFile "append_file" "AppendFile" 17 RAW surface 2 Str "(String, String) -> Result(Unit, String) ! {IO}" flags [OffPlatform];
    RemoveFile "remove_file" "RemoveFile" 18 RAW surface 1 Str "(String) -> Unit ! {IO}" flags [OffPlatform];
    StoreGet "prim_store_get" "StoreGet" 75 RAW surface 2 Str "(String, String) -> String ! {IO}" flags [NativeDeferred];
    StorePut "prim_store_put" "StorePut" 76 RAW surface 3 Str "(String, String, String) -> Unit ! {IO}" flags [OffPlatform, NativeDeferred];
    StoreHas "prim_store_has" "StoreHas" 77 RETAG surface 2 Str "(String, String) -> Bool ! {IO}" flags [NativeDeferred];
    Exit "exit" "Exit" 19 IMM0 surface 1 Str "forall a. (Int) -> a" flags [OffPlatform];
    System "system" "System" 20 RETAG surface 1 Str "(String) -> Int ! {IO}" flags [OffPlatform];
    Eprint "eprint" "Eprint" 21 RAW surface 1 Str "(String) -> Unit ! {IO}" flags [OffPlatform];
    ArgsCount "prim_args_count" "ArgsCount" 22 RETAG surface 0 Str "() -> Int ! {IO}";
    Arg "prim_arg" "Arg" 23 IMM0 surface 1 Str "(Int) -> String ! {IO}";
    WallNow "prim_wall_now" "WallNow" 92 RETAG surface 0 Str "() -> Int ! {IO}";
    MonoNow "prim_mono_now" "MonoNow" 93 RETAG surface 0 Str "() -> Int ! {IO}";
    Entropy "prim_entropy" "Entropy" 122 RETAG surface 0 Str "() -> Int ! {IO}";
    ShowInt "show_int" "ShowInt" 24 RAW surface 1 Str "(Int) -> String";
    ShowI64 "show_i64" "ShowI64" 25 RAW surface 1 Str "(I64) -> String";
    ShowU64 "show_u64" "ShowU64" 26 RAW surface 1 Str "(U64) -> String";
    ShowBool "show_bool" "ShowBool" 27 IMM0 surface 1 Str "(Bool) -> String";
    ShowFloat "show_float" "ShowFloat" 28 F0 surface 1 Str "(Float) -> String";
    ToI64 "to_i64" "ToI64" 29 RAW surface 1 Int "(Int) -> I64";
    ToU64 "to_u64" "ToU64" 30 RAW surface 1 Int "(Int) -> U64";
    IntOfI64 "int_of_i64" "IntOfI64" 31 RAW surface 1 Int "(I64) -> Int";
    IntOfU64 "int_of_u64" "IntOfU64" 32 RAW surface 1 Int "(U64) -> Int";
    I64Add "i64_add" "I64Add" 33 RAW;
    I64Sub "i64_sub" "I64Sub" 34 RAW;
    I64Mul "i64_mul" "I64Mul" 35 RAW;
    I64Div "i64_div" "I64Div" 36 RAW;
    U64Div "u64_div" "U64Div" 37 RAW;
    I64Rem "i64_rem" "I64Rem" 38 RAW;
    U64Rem "u64_rem" "U64Rem" 39 RAW;
    I64Cmp "i64_cmp" "I64Cmp" 40 RETAG surface 2 Str "(I64, I64) -> Int";
    U64Cmp "u64_cmp" "U64Cmp" 41 RETAG surface 2 Str "(U64, U64) -> Int";
    U64Add "u64_add" "U64Add" 42 RAW;
    U64Sub "u64_sub" "U64Sub" 43 RAW;
    U64Mul "u64_mul" "U64Mul" 44 RAW;
    ByteAt "byte_at" "ByteAt" 45 IDX1_RETAG surface 2 Str "(String, Int) -> Int";
    ByteLen "byte_len" "ByteLen" 46 RETAG surface 1 Str "(String) -> Int";
    StringOfBytes "string_of_bytes" "StringOfBytes" 47 RAW;
    ArrayPop "array_pop" "ArrayPop" 48 RAW surface 1 Str "forall a. (Array(a)) -> Array(a)";
    I64And "i64_and" "I64And" 49 RAW surface 2 Str "(I64, I64) -> I64";
    I64Or "i64_or" "I64Or" 50 RAW surface 2 Str "(I64, I64) -> I64";
    I64Xor "i64_xor" "I64Xor" 51 RAW surface 2 Str "(I64, I64) -> I64";
    I64Shl "i64_shl" "I64Shl" 52 RAW surface 2 Str "(I64, I64) -> I64";
    I64Shr "i64_shr" "I64Shr" 53 RAW surface 2 Str "(I64, I64) -> I64";
    U64And "u64_and" "U64And" 54 RAW surface 2 Str "(U64, U64) -> U64";
    U64Or "u64_or" "U64Or" 55 RAW surface 2 Str "(U64, U64) -> U64";
    U64Xor "u64_xor" "U64Xor" 56 RAW surface 2 Str "(U64, U64) -> U64";
    U64Shl "u64_shl" "U64Shl" 57 RAW surface 2 Str "(U64, U64) -> U64";
    U64Shr "u64_shr" "U64Shr" 58 RAW surface 2 Str "(U64, U64) -> U64";
    ArrayNew "array_new" "ArrayNew" 59 IMM0 surface 2 Str "forall a. (Int, a) -> Array(a)";
    ArrayEmpty "array_empty" "ArrayEmpty" 60 RAW surface 0 Str "forall a. () -> Array(a)";
    ArrayLen "array_len" "ArrayLen" 61 RETAG surface 1 Str "forall a. (Array(a)) -> Int";
    ArrayGet "array_get" "ArrayGet" 62 IDX1 surface 2 Str "forall a. (Array(a), Int) -> a";
    ArraySet "array_set" "ArraySet" 63 IDX1 surface 3 Str "forall a. (Array(a), Int, a) -> Array(a)";
    ArrayPush "array_push" "ArrayPush" 64 RAW surface 2 Str "forall a. (Array(a), a) -> Array(a)";
    StringOfArray "string_of_array" "StringOfArray" 65 RAW surface 1 Str "(Array(String)) -> String";
    BufEmpty "buf_empty" "BufEmpty" 78 RAW surface 0 Str "() -> Buf";
    BufNew "buf_new" "BufNew" 79 IMM01 surface 2 Str "(Int, Int) -> Buf";
    BufLen "buf_len" "BufLen" 80 RETAG surface 1 Str "(Buf) -> Int";
    BufGet "buf_get" "BufGet" 81 IDX1_RETAG surface 2 Str "(Buf, Int) -> Int";
    BufSet "buf_set" "BufSet" 82 IDX12 surface 3 Str "(Buf, Int, Int) -> Buf";
    BufPush "buf_push" "BufPush" 83 IDX1 surface 2 Str "(Buf, Int) -> Buf";
    BufSlice "buf_slice" "BufSlice" 84 IDX12 surface 3 Str "(Buf, Int, Int) -> Buf";
    BufCat "buf_cat" "BufCat" 85 RAW surface 2 Str "(Buf, Buf) -> Buf";
    BufEq "buf_eq" "BufEq" 86 RETAG surface 2 Str "(Buf, Buf) -> Bool";
    BufCmp "buf_cmp" "BufCmp" 87 RETAG surface 2 Str "(Buf, Buf) -> Int";
    BufHash "buf_hash" "BufHash" 88 RAW surface 1 Str "(Buf) -> String";
    BufOfString "buf_of_string" "BufOfString" 89 RAW surface 1 Str "(String) -> Buf";
    StringOfBuf "string_of_buf" "StringOfBuf" 90 RAW surface 1 Str "(Buf) -> String";
    BufUtf8Valid "buf_utf8_valid" "BufUtf8Valid" 91 RETAG surface 1 Str "(Buf) -> Bool";
    TbufNew "tbuf_new" "TbufNew" 95 IMM0_F1 surface 2 Str "(Int, Float) -> FloatBuf";
    TbufLen "tbuf_len" "TbufLen" 96 RETAG surface 1 Str "(FloatBuf) -> Int";
    TbufGet "tbuf_get" "TbufGet" 97 IDX1 surface 2 Str "(FloatBuf, Int) -> Float";
    TbufSet "tbuf_set" "TbufSet" 98 IDX1_F2 surface 3 Str "(FloatBuf, Int, Float) -> FloatBuf";
    TbufBlit "tbuf_blit" "TbufBlit" 99 IDX134 surface 5 Str "(FloatBuf, Int, FloatBuf, Int, Int) -> FloatBuf";
    IbufNew "ibuf_new" "IbufNew" 100 IMM0_F1 surface 2 Str "(Int, I64) -> IntBuf";
    IbufLen "ibuf_len" "IbufLen" 101 RETAG surface 1 Str "(IntBuf) -> Int";
    IbufGet "ibuf_get" "IbufGet" 102 IDX1 surface 2 Str "(IntBuf, Int) -> I64";
    IbufSet "ibuf_set" "IbufSet" 103 IDX1_F2 surface 3 Str "(IntBuf, Int, I64) -> IntBuf";
    IbufBlit "ibuf_blit" "IbufBlit" 104 IDX134 surface 5 Str "(IntBuf, Int, IntBuf, Int, Int) -> IntBuf";
    SortPrim "sort_prim" "SortPrim" 66 RAW;
    TaqSnoc "taq_snoc" "TaqSnoc" 67 RAW;
    TaqConcat "taq_concat" "TaqConcat" 68 RAW;
    TaqUncons "taq_uncons" "TaqUncons" 69 RAW;
    // Arena bump: hand out a raw cell for a constructor the arena-lowering pass
    // split into `alloc` + `init_at`. The `with_arena` handler discharges the
    // `alloc` operation into this call. `IMM0` untags the word count; the result
    // is the raw cell pointer. Native-only (no interpreter allocation): it appears
    // only in effect-lowered Core, which the interpreter never runs.
    Bump "prim_arena_bump" "Bump" 105 IMM0 surface 1 Int "(Int) -> Arena.Cell";
    // Region brackets around a `with_arena` handler activation, emitted only by
    // the arena-lowering pass (never surface-callable: user code reaching them
    // could unbalance the region stack). `arena_enter` opens a region and
    // returns its activation depth; `arena_exit` threads that token plus the
    // handler's result, so the pair is data-dependent and can never be
    // separated or dropped by a simplification that respects data flow. Their
    // verifier signatures are overrides seeded by the arena pass
    // (`() -> Int` and `forall a. (Int, a) -> a`).
    ArenaEnter "arena_enter" "ArenaEnter" 106 RETAG;
    ArenaExit "arena_exit" "ArenaExit" 107 IMM0;
    // Baseline 128-bit SIMD (the `src/core/simd.rs` registry, wired to execution).
    // The hash tags are exactly the frozen `SimdOp::hash_tag`s, so content identity
    // matches the pinned registry (`simd_builtin_tags_match_registry` guards it).
    // The interpreter defines the bit-exact semantics; native lowers each to its
    // `prism_simd_*` runtime symbol over a two-word vector cell. A `splat` unboxes
    // its scalar (`F0`/`RAW`); `extract` untags its lane index (`IDX1`); the
    // lane-wise binary ops thread two vector cells raw.
    SimdFSplat "simd_fsplat" "SimdFSplat" 108 F0 surface 1 Str "(Float) -> F64x2";
    SimdFExtract "simd_fextract" "SimdFExtract" 109 IDX1 surface 2 Str "(F64x2, Int) -> Float";
    SimdFAdd "simd_fadd" "SimdFAdd" 110 RAW surface 2 Str "(F64x2, F64x2) -> F64x2";
    SimdFSub "simd_fsub" "SimdFSub" 111 RAW surface 2 Str "(F64x2, F64x2) -> F64x2";
    SimdFMul "simd_fmul" "SimdFMul" 112 RAW surface 2 Str "(F64x2, F64x2) -> F64x2";
    SimdFMin "simd_fmin" "SimdFMin" 113 RAW surface 2 Str "(F64x2, F64x2) -> F64x2";
    SimdFMax "simd_fmax" "SimdFMax" 114 RAW surface 2 Str "(F64x2, F64x2) -> F64x2";
    SimdISplat "simd_isplat" "SimdISplat" 115 RAW surface 1 Str "(I64) -> I64x2";
    SimdIExtract "simd_iextract" "SimdIExtract" 116 IDX1 surface 2 Str "(I64x2, Int) -> I64";
    SimdIAdd "simd_iadd" "SimdIAdd" 117 RAW surface 2 Str "(I64x2, I64x2) -> I64x2";
    SimdISub "simd_isub" "SimdISub" 118 RAW surface 2 Str "(I64x2, I64x2) -> I64x2";
    SimdIAnd "simd_iand" "SimdIAnd" 119 RAW surface 2 Str "(I64x2, I64x2) -> I64x2";
    SimdIOr "simd_ior" "SimdIOr" 120 RAW surface 2 Str "(I64x2, I64x2) -> I64x2";
    SimdIXor "simd_ixor" "SimdIXor" 121 RAW surface 2 Str "(I64x2, I64x2) -> I64x2";
    // The four-lane 32-bit interpretations of the same two-word vector cell.
    // `simd_fsplat4` narrows its double to f32 (round-to-nearest) and
    // `simd_isplat4` truncates its i64 to i32; `extract` widens back exactly
    // (f32 -> f64, i32 sign-extended), so a splat-extract round trip is the
    // narrowing alone. Arithmetic is per-lane in true single precision or
    // wrapping 32-bit, defined bit-exactly by the interpreter oracle.
    SimdF32Splat "simd_fsplat4" "SimdF32Splat" 123 F0 surface 1 Str "(Float) -> F32x4";
    SimdF32Extract "simd_fextract4" "SimdF32Extract" 124 IDX1 surface 2 Str "(F32x4, Int) -> Float";
    SimdF32Add "simd_fadd4" "SimdF32Add" 125 RAW surface 2 Str "(F32x4, F32x4) -> F32x4";
    SimdF32Sub "simd_fsub4" "SimdF32Sub" 126 RAW surface 2 Str "(F32x4, F32x4) -> F32x4";
    SimdF32Mul "simd_fmul4" "SimdF32Mul" 127 RAW surface 2 Str "(F32x4, F32x4) -> F32x4";
    SimdF32Min "simd_fmin4" "SimdF32Min" 128 RAW surface 2 Str "(F32x4, F32x4) -> F32x4";
    SimdF32Max "simd_fmax4" "SimdF32Max" 129 RAW surface 2 Str "(F32x4, F32x4) -> F32x4";
    SimdI32Splat "simd_isplat4" "SimdI32Splat" 130 RAW surface 1 Str "(I64) -> I32x4";
    SimdI32Extract "simd_iextract4" "SimdI32Extract" 131 IDX1 surface 2 Str "(I32x4, Int) -> I64";
    SimdI32Add "simd_iadd4" "SimdI32Add" 132 RAW surface 2 Str "(I32x4, I32x4) -> I32x4";
    SimdI32Sub "simd_isub4" "SimdI32Sub" 133 RAW surface 2 Str "(I32x4, I32x4) -> I32x4";
    SimdI32And "simd_iand4" "SimdI32And" 134 RAW surface 2 Str "(I32x4, I32x4) -> I32x4";
    SimdI32Or "simd_ior4" "SimdI32Or" 135 RAW surface 2 Str "(I32x4, I32x4) -> I32x4";
    SimdI32Xor "simd_ixor4" "SimdI32Xor" 136 RAW surface 2 Str "(I32x4, I32x4) -> I32x4";
    ]
}

// Builtins in wire order: index `i` holds the builtin whose [`Builtin::wire`] is
// `i`. Built from the per-row wire numbers so it cannot drift from them, and the
// store codec numbers builtins by position in this table (which equals their wire
// number). The const evaluation panics if the wire numbers are not dense and
// unique from zero, since a gap or a duplicate leaves some index unfilled: that is
// the compile-time guard that the append-only wire space stays intact.
const BUILTINS_BY_WIRE_ARR: [Builtin; Builtin::ALL.len()] = {
    let mut arr = [Builtin::ALL[0]; Builtin::ALL.len()];
    let mut i = 0;
    while i < arr.len() {
        arr[i] = match Builtin::from_wire(i as u64) {
            Some(b) => b,
            None => panic!("builtin wire indices must be dense and unique from zero"),
        };
        i += 1;
    }
    arr
};

/// Builtins in wire order, the single source the store and kont codecs number
/// from. See [`Builtin::wire`].
pub const BUILTINS_BY_WIRE: &[Builtin] = &BUILTINS_BY_WIRE_ARR;

impl Builtin {
    /// Runtime C symbol. `concat` maps to `prism_str_concat`; the rest are
    /// `prism_<name>`.
    #[must_use]
    pub fn sym(self) -> String {
        match self {
            Self::Concat => "prism_str_concat".into(),
            // Surface `prim_arena_bump`, one C symbol `prism_bump` shared with
            // the region substrate later. Keeping the surface name clear of user
            // names is not what stops a user's `fn bump` from colliding with this
            // symbol; the disjoint native namespaces are (see `codegen`).
            Self::Bump => "prism_bump".into(),
            // The typed-buffer C runtime (`runtime/prism_tbuf.c`) moves raw 8-byte
            // words and is element-kind-agnostic, so the i64-element builtins call
            // the same symbols as the f64-element ones; only the surface types and
            // interpreter arms differ.
            Self::IbufNew => "prism_tbuf_new".into(),
            Self::IbufLen => "prism_tbuf_len".into(),
            Self::IbufGet => "prism_tbuf_get".into(),
            Self::IbufSet => "prism_tbuf_set".into(),
            Self::IbufBlit => "prism_tbuf_blit".into(),
            _ => format!("prism_{}", self.name()),
        }
    }

    #[must_use]
    pub fn from_name(s: &str) -> Option<Self> {
        Self::ALL.iter().copied().find(|b| b.name() == s)
    }
}

#[must_use]
pub fn builtin(name: &str) -> Option<(usize, BuiltinKind)> {
    BUILTINS
        .iter()
        .find(|(n, ..)| *n == name)
        .map(|&(_, arity, kind)| (arity, kind))
        .or_else(|| float_surface(name))
}

/// The surface output builtins (`print`/`println`).
///
/// Their calls route through the interceptable `Output` capability when the
/// `Replay` machinery is in scope. Lives here, with the rest of the builtin name
/// knowledge, so the desugarer's world-handler decision does not re-spell them.
pub const OUTPUT_BUILTINS: &[&str] = &["print", "println"];

#[cfg(test)]
mod tag_tests {
    use super::{Builtin, FloatOp};
    use std::collections::BTreeSet;

    // Assert a frozen `variant -> tag` table: every entry's `hash_tag` reproduces
    // its frozen spelling, no two variants share one, and the table covers every
    // variant (its length equals `ALL`). The content hash commits to these
    // strings, so freezing them turns a rename that also touched the tag method
    // (which would silently move affected definition hashes) into a test failure.
    fn frozen_all<T: Copy>(all_len: usize, table: &[(T, &str)], tag: impl Fn(T) -> &'static str) {
        assert_eq!(
            table.len(),
            all_len,
            "frozen tag table is missing a variant present in ALL",
        );
        let mut seen = BTreeSet::new();
        for &(variant, spelling) in table {
            assert_eq!(
                tag(variant),
                spelling,
                "hash tag drifted from frozen spelling"
            );
            assert!(
                seen.insert(spelling),
                "two variants share the hash tag {spelling}"
            );
        }
    }

    #[test]
    fn float_op_hash_tags_are_frozen() {
        frozen_all(
            FloatOp::ALL.len(),
            &[
                (FloatOp::ToFloat, "ToFloat"),
                (FloatOp::Truncate, "Truncate"),
                (FloatOp::FloorToInt, "FloorToInt"),
                (FloatOp::CeilToInt, "CeilToInt"),
                (FloatOp::AbsFloat, "AbsFloat"),
                (FloatOp::Sqrt, "Sqrt"),
                (FloatOp::Floor, "Floor"),
                (FloatOp::Ceil, "Ceil"),
                (FloatOp::Round, "Round"),
                (FloatOp::Trunc, "Trunc"),
                (FloatOp::Sin, "Sin"),
                (FloatOp::Cos, "Cos"),
                (FloatOp::Tan, "Tan"),
                (FloatOp::Asin, "Asin"),
                (FloatOp::Acos, "Acos"),
                (FloatOp::Atan, "Atan"),
                (FloatOp::Sinh, "Sinh"),
                (FloatOp::Cosh, "Cosh"),
                (FloatOp::Tanh, "Tanh"),
                (FloatOp::Exp, "Exp"),
                (FloatOp::Exp2, "Exp2"),
                (FloatOp::Expm1, "Expm1"),
                (FloatOp::Ln, "Ln"),
                (FloatOp::Log2, "Log2"),
                (FloatOp::Log10, "Log10"),
                (FloatOp::Log1p, "Log1p"),
                (FloatOp::Cbrt, "Cbrt"),
            ],
            FloatOp::hash_tag,
        );
    }

    #[test]
    fn builtin_hash_tags_are_frozen() {
        frozen_all(
            Builtin::ALL.len(),
            &[
                (Builtin::Concat, "Concat"),
                (Builtin::StrLen, "StrLen"),
                (Builtin::StrEq, "StrEq"),
                (Builtin::StrCmp, "StrCmp"),
                (Builtin::Substring, "Substring"),
                (Builtin::CharAt, "CharAt"),
                (Builtin::ShowChar, "ShowChar"),
                (Builtin::Blake3, "Blake3"),
                (Builtin::ParseInt, "ParseInt"),
                (Builtin::BigLit, "BigLit"),
                (Builtin::ParseFloat, "ParseFloat"),
                (Builtin::PowFloat, "PowFloat"),
                (Builtin::Atan2, "Atan2"),
                (Builtin::Hypot, "Hypot"),
                (Builtin::Fmod, "Fmod"),
                (Builtin::ShowFloatPrec, "ShowFloatPrec"),
                (Builtin::ProbeEnabled, "ProbeEnabled"),
                (Builtin::Getenv, "Getenv"),
                (Builtin::ReadFile, "ReadFile"),
                (Builtin::ReadBytesFile, "ReadBytesFile"),
                (Builtin::WriteBytesFile, "WriteBytesFile"),
                (Builtin::WriteFile, "WriteFile"),
                (Builtin::FileExists, "FileExists"),
                (Builtin::AppendFile, "AppendFile"),
                (Builtin::RemoveFile, "RemoveFile"),
                (Builtin::StoreGet, "StoreGet"),
                (Builtin::StorePut, "StorePut"),
                (Builtin::StoreHas, "StoreHas"),
                (Builtin::Exit, "Exit"),
                (Builtin::System, "System"),
                (Builtin::Eprint, "Eprint"),
                (Builtin::ArgsCount, "ArgsCount"),
                (Builtin::Arg, "Arg"),
                (Builtin::WallNow, "WallNow"),
                (Builtin::MonoNow, "MonoNow"),
                (Builtin::Entropy, "Entropy"),
                (Builtin::ShowInt, "ShowInt"),
                (Builtin::ShowI64, "ShowI64"),
                (Builtin::ShowU64, "ShowU64"),
                (Builtin::ShowBool, "ShowBool"),
                (Builtin::ShowFloat, "ShowFloat"),
                (Builtin::ToI64, "ToI64"),
                (Builtin::ToU64, "ToU64"),
                (Builtin::IntOfI64, "IntOfI64"),
                (Builtin::IntOfU64, "IntOfU64"),
                (Builtin::I64Add, "I64Add"),
                (Builtin::I64Sub, "I64Sub"),
                (Builtin::I64Mul, "I64Mul"),
                (Builtin::I64Div, "I64Div"),
                (Builtin::U64Div, "U64Div"),
                (Builtin::I64Rem, "I64Rem"),
                (Builtin::U64Rem, "U64Rem"),
                (Builtin::I64Cmp, "I64Cmp"),
                (Builtin::U64Cmp, "U64Cmp"),
                (Builtin::U64Add, "U64Add"),
                (Builtin::U64Sub, "U64Sub"),
                (Builtin::U64Mul, "U64Mul"),
                (Builtin::ByteAt, "ByteAt"),
                (Builtin::ByteLen, "ByteLen"),
                (Builtin::StringOfBytes, "StringOfBytes"),
                (Builtin::ArrayPop, "ArrayPop"),
                (Builtin::I64And, "I64And"),
                (Builtin::I64Or, "I64Or"),
                (Builtin::I64Xor, "I64Xor"),
                (Builtin::I64Shl, "I64Shl"),
                (Builtin::I64Shr, "I64Shr"),
                (Builtin::U64And, "U64And"),
                (Builtin::U64Or, "U64Or"),
                (Builtin::U64Xor, "U64Xor"),
                (Builtin::U64Shl, "U64Shl"),
                (Builtin::U64Shr, "U64Shr"),
                (Builtin::ArrayNew, "ArrayNew"),
                (Builtin::ArrayEmpty, "ArrayEmpty"),
                (Builtin::ArrayLen, "ArrayLen"),
                (Builtin::ArrayGet, "ArrayGet"),
                (Builtin::ArraySet, "ArraySet"),
                (Builtin::ArrayPush, "ArrayPush"),
                (Builtin::StringOfArray, "StringOfArray"),
                (Builtin::BufEmpty, "BufEmpty"),
                (Builtin::BufNew, "BufNew"),
                (Builtin::BufLen, "BufLen"),
                (Builtin::BufGet, "BufGet"),
                (Builtin::BufSet, "BufSet"),
                (Builtin::BufPush, "BufPush"),
                (Builtin::BufSlice, "BufSlice"),
                (Builtin::BufCat, "BufCat"),
                (Builtin::BufEq, "BufEq"),
                (Builtin::BufCmp, "BufCmp"),
                (Builtin::BufHash, "BufHash"),
                (Builtin::BufOfString, "BufOfString"),
                (Builtin::StringOfBuf, "StringOfBuf"),
                (Builtin::BufUtf8Valid, "BufUtf8Valid"),
                (Builtin::TbufNew, "TbufNew"),
                (Builtin::TbufLen, "TbufLen"),
                (Builtin::TbufGet, "TbufGet"),
                (Builtin::TbufSet, "TbufSet"),
                (Builtin::TbufBlit, "TbufBlit"),
                (Builtin::IbufNew, "IbufNew"),
                (Builtin::IbufLen, "IbufLen"),
                (Builtin::IbufGet, "IbufGet"),
                (Builtin::IbufSet, "IbufSet"),
                (Builtin::IbufBlit, "IbufBlit"),
                (Builtin::SortPrim, "SortPrim"),
                (Builtin::TaqSnoc, "TaqSnoc"),
                (Builtin::TaqConcat, "TaqConcat"),
                (Builtin::TaqUncons, "TaqUncons"),
                (Builtin::Bump, "Bump"),
                (Builtin::ArenaEnter, "ArenaEnter"),
                (Builtin::ArenaExit, "ArenaExit"),
                (Builtin::SimdFSplat, "SimdFSplat"),
                (Builtin::SimdFExtract, "SimdFExtract"),
                (Builtin::SimdFAdd, "SimdFAdd"),
                (Builtin::SimdFSub, "SimdFSub"),
                (Builtin::SimdFMul, "SimdFMul"),
                (Builtin::SimdFMin, "SimdFMin"),
                (Builtin::SimdFMax, "SimdFMax"),
                (Builtin::SimdISplat, "SimdISplat"),
                (Builtin::SimdIExtract, "SimdIExtract"),
                (Builtin::SimdIAdd, "SimdIAdd"),
                (Builtin::SimdISub, "SimdISub"),
                (Builtin::SimdIAnd, "SimdIAnd"),
                (Builtin::SimdIOr, "SimdIOr"),
                (Builtin::SimdIXor, "SimdIXor"),
                (Builtin::SimdF32Splat, "SimdF32Splat"),
                (Builtin::SimdF32Extract, "SimdF32Extract"),
                (Builtin::SimdF32Add, "SimdF32Add"),
                (Builtin::SimdF32Sub, "SimdF32Sub"),
                (Builtin::SimdF32Mul, "SimdF32Mul"),
                (Builtin::SimdF32Min, "SimdF32Min"),
                (Builtin::SimdF32Max, "SimdF32Max"),
                (Builtin::SimdI32Splat, "SimdI32Splat"),
                (Builtin::SimdI32Extract, "SimdI32Extract"),
                (Builtin::SimdI32Add, "SimdI32Add"),
                (Builtin::SimdI32Sub, "SimdI32Sub"),
                (Builtin::SimdI32And, "SimdI32And"),
                (Builtin::SimdI32Or, "SimdI32Or"),
                (Builtin::SimdI32Xor, "SimdI32Xor"),
            ],
            Builtin::hash_tag,
        );
    }

    // The wired SIMD builtins carry exactly the frozen `SimdOp::hash_tag`s, so
    // executing the registry never moves a content hash relative to its pinned
    // identity. Keyed by surface name, the one string both registries agree on.
    #[test]
    fn simd_builtin_tags_match_registry() {
        use crate::core::simd::SimdOp;
        for op in SimdOp::ALL {
            let b = Builtin::from_name(op.name())
                .unwrap_or_else(|| panic!("simd op `{}` has no wired builtin", op.name()));
            assert_eq!(
                b.hash_tag(),
                op.hash_tag(),
                "wired builtin for `{}` must reuse the frozen registry tag",
                op.name()
            );
        }
    }

    // Wire indices are dense and unique from zero (also enforced at compile time by
    // the `BUILTINS_BY_WIRE` const), and `wire`/`from_wire` round-trip. The wire
    // space is the store's append-only content format, so a gap, a duplicate, or a
    // broken inverse is corruption.
    #[test]
    fn wire_indices_are_dense_and_unique() {
        let mut seen = BTreeSet::new();
        for b in Builtin::ALL {
            assert!(seen.insert(b.wire()), "two builtins share a wire index");
            assert_eq!(Builtin::from_wire(b.wire()), Some(*b), "wire round-trip");
        }
        assert_eq!(seen, (0..Builtin::ALL.len() as u64).collect());
        assert_eq!(super::BUILTINS_BY_WIRE.len(), Builtin::ALL.len());
    }

    // A builtin is surface-callable exactly when it carries an arity/kind and a
    // signature: both projections must agree, so a new surface builtin cannot land
    // with a signature but no dispatch entry (or the reverse). The compiler-internal
    // ops (the fixed-width arithmetic the operator lowering emits, the taq/sort
    // primitives, `big_lit`) carry neither.
    #[test]
    fn surface_and_signature_agree() {
        for b in Builtin::ALL {
            assert_eq!(
                b.surface().is_some(),
                b.signature().is_some(),
                "surface/signature presence disagree for {}",
                b.name()
            );
        }
    }
}
