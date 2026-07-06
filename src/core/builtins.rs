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

/// Inline unary floating-point op the elaborator emits as `Comp::FloatBuiltin`.
///
/// Three lowering classes, distinguished by [`FloatOp::runtime_sym`] and the
/// exhaustive match in codegen:
/// - int/float conversions (`to_float`, `truncate`, `floor_to_int`,
///   `ceil_to_int`): int<->float casts with pinned saturating rounding;
/// - exact float->float ops (`floor`, `ceil`, `round`, `trunc`, `abs_float`,
///   `sqrt`): correctly rounded / exact on every IEEE-754 platform, so they lower
///   to hardware intrinsics and need no owned implementation;
/// - transcendentals (the rest): platform libm would diverge in the last bit, so
///   each routes through the owned vendored libm ([`FloatOp::runtime_sym`]).
///
/// Binary math (`pow`, `atan2`, `hypot`, `fmod`) is not here: those take two
/// arguments and ride the boxed-float [`Builtin`] path instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatOp {
    // int<->float conversions.
    ToFloat,
    Truncate,
    FloorToInt,
    CeilToInt,
    // Exact float->float.
    AbsFloat,
    Sqrt,
    Floor,
    Ceil,
    Round,
    Trunc,
    // Transcendentals, owned by the vendored libm.
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Sinh,
    Cosh,
    Tanh,
    Exp,
    Exp2,
    Expm1,
    Ln,
    Log2,
    Log10,
    Log1p,
    Cbrt,
}

impl FloatOp {
    pub(crate) const ALL: &'static [Self] = &[
        Self::ToFloat,
        Self::Truncate,
        Self::FloorToInt,
        Self::CeilToInt,
        Self::AbsFloat,
        Self::Sqrt,
        Self::Floor,
        Self::Ceil,
        Self::Round,
        Self::Trunc,
        Self::Sin,
        Self::Cos,
        Self::Tan,
        Self::Asin,
        Self::Acos,
        Self::Atan,
        Self::Sinh,
        Self::Cosh,
        Self::Tanh,
        Self::Exp,
        Self::Exp2,
        Self::Expm1,
        Self::Ln,
        Self::Log2,
        Self::Log10,
        Self::Log1p,
        Self::Cbrt,
    ];

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::ToFloat => "to_float",
            Self::Truncate => "truncate",
            Self::FloorToInt => "floor_to_int",
            Self::CeilToInt => "ceil_to_int",
            Self::AbsFloat => "abs_float",
            Self::Sqrt => "sqrt",
            Self::Floor => "floor",
            Self::Ceil => "ceil",
            Self::Round => "round",
            Self::Trunc => "trunc",
            Self::Sin => "sin",
            Self::Cos => "cos",
            Self::Tan => "tan",
            Self::Asin => "asin",
            Self::Acos => "acos",
            Self::Atan => "atan",
            Self::Sinh => "sinh",
            Self::Cosh => "cosh",
            Self::Tanh => "tanh",
            Self::Exp => "exp",
            Self::Exp2 => "exp2",
            Self::Expm1 => "expm1",
            Self::Ln => "ln",
            Self::Log2 => "log2",
            Self::Log10 => "log10",
            Self::Log1p => "log1p",
            Self::Cbrt => "cbrt",
        }
    }

    /// The owned-libm C symbol a transcendental routes to on native and via FFI
    /// in the interpreter, or `None` for the conversions and exact ops (which
    /// lower to casts/intrinsics with no owned implementation). This is the one
    /// canonical place the `prism_m_*` ABI contract for the unary ops lives, the
    /// analogue of [`Builtin::sym`]; codegen and the interpreter both dispatch
    /// off it, so a variant cannot be added without wiring both.
    #[must_use]
    pub const fn runtime_sym(self) -> Option<&'static str> {
        match self {
            Self::ToFloat
            | Self::Truncate
            | Self::FloorToInt
            | Self::CeilToInt
            | Self::AbsFloat
            | Self::Sqrt
            | Self::Floor
            | Self::Ceil
            | Self::Round
            | Self::Trunc => None,
            Self::Sin => Some("prism_m_sin"),
            Self::Cos => Some("prism_m_cos"),
            Self::Tan => Some("prism_m_tan"),
            Self::Asin => Some("prism_m_asin"),
            Self::Acos => Some("prism_m_acos"),
            Self::Atan => Some("prism_m_atan"),
            Self::Sinh => Some("prism_m_sinh"),
            Self::Cosh => Some("prism_m_cosh"),
            Self::Tanh => Some("prism_m_tanh"),
            Self::Exp => Some("prism_m_exp"),
            Self::Exp2 => Some("prism_m_exp2"),
            Self::Expm1 => Some("prism_m_expm1"),
            Self::Ln => Some("prism_m_log"),
            Self::Log2 => Some("prism_m_log2"),
            Self::Log10 => Some("prism_m_log10"),
            Self::Log1p => Some("prism_m_log1p"),
            Self::Cbrt => Some("prism_m_cbrt"),
        }
    }

    #[must_use]
    pub fn from_name(s: &str) -> Option<Self> {
        Self::ALL.iter().copied().find(|o| o.name() == s)
    }
}

/// Runtime-call builtin the elaborator emits as `Comp::StrBuiltin`.
///
/// Lowered to a `prism_*` C call. Spans surface builtins (`concat`, `show_int`,
/// ...) and compiler-internal ops never surface-callable (`show_i64`/`show_u64`,
/// fixed-width arithmetic). `name()` is the single string source; the IR,
/// interpreter dispatch, and codegen all key off the enum so a name can never
/// drift.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    Concat,
    StrLen,
    StrEq,
    StrCmp,
    Substring,
    CharAt,
    ShowChar,
    // blake3 of a string's bytes, returned as lowercase hex. The one runtime hash
    // primitive, shared by every derived `Hash` instance: the interpreter calls
    // the `blake3` crate, the native runtime a portable in-repo blake3, and the
    // two must agree byte-for-byte (gated by `tests/hash_value_parity.rs`).
    Blake3,
    ParseInt,
    // Materializes a bignum literal that overflows the 63-bit immediate from its
    // decimal text. Not surface-callable; emitted only by the elaborator, where
    // the input is always valid digits, so unlike `parse_int` it returns the raw
    // `Integer` cell rather than an `Option`.
    BigLit,
    ParseFloat,
    // Binary float transcendentals: boxed-float args in, boxed float out, routed
    // through the owned vendored libm (see prism_float.c's `prism_float_binop`).
    // The unary transcendentals ride `FloatOp` instead; these need two arguments.
    PowFloat,
    Atan2,
    Hypot,
    Fmod,
    ShowFloatPrec,
    // Runtime source instrumentation gate. `probe "name" do body` lowers to an
    // if over this builtin, so disabled probes skip the whole body.
    ProbeEnabled,
    Getenv,
    ReadFile,
    ReadBytesFile,
    WriteBytesFile,
    WriteFile,
    FileExists,
    AppendFile,
    RemoveFile,
    // The content-addressed store bridge: a named blob rides the real store
    // (immutable object keyed by its content hash, plus a mutable ref keyed by a
    // caller tag) instead of a snapshot file. `StoreGet`/`StoreHas` read, so they
    // are input prims reached through the world handler; `StorePut` writes, so it
    // is off-platform like `WriteFile`. Interpreter-only for now: the native path
    // has no C runtime symbol yet (see `native_deferred`).
    StoreGet,
    StorePut,
    StoreHas,
    Exit,
    System,
    Eprint,
    ArgsCount,
    Arg,
    // Real-time clock reads (nanoseconds): `WallNow` is the system clock (Unix
    // epoch, UTC), `MonoNow` a monotonic counter. Both are input prims reached
    // through a `Clock` handler and recorded as trace entries, so a time-reading
    // program replays byte-identically.
    WallNow,
    MonoNow,
    ShowInt,
    ShowI64,
    ShowU64,
    ShowBool,
    ShowFloat,
    ToI64,
    ToU64,
    IntOfI64,
    IntOfU64,
    I64Add,
    I64Sub,
    I64Mul,
    I64Div,
    U64Div,
    I64Rem,
    U64Rem,
    I64Cmp,
    U64Cmp,
    // Wrapping fixed-width add/sub/mul (the I64 variants already exist below for
    // the elaborator; both lanes are surface-exposed so a userland hash can do
    // fixed-width arithmetic without bignum promotion).
    U64Add,
    U64Sub,
    U64Mul,
    // O(1) byte access and byte-wise string building (UTF-8 unaware), so a lexer
    // or hash scans raw bytes in linear time rather than walking codepoints.
    ByteAt,
    ByteLen,
    StringOfBytes,
    // Pop last element, in place when uniquely owned.
    ArrayPop,
    // Fixed-width bitwise and shift ops, one runtime call each, both lanes (the
    // and/or/xor bit patterns coincide across signedness; `i64_shr` is arithmetic
    // and `u64_shr` logical). Shift counts are taken modulo 64.
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64Shr,
    U64And,
    U64Or,
    U64Xor,
    U64Shl,
    U64Shr,
    // Fixed-size polymorphic array, an ordinary heap cell (so reference counting
    // recurses into its elements for free). `array_set` writes in place when the
    // array is uniquely owned (FBIP), else copies.
    ArrayNew,
    ArrayEmpty,
    ArrayLen,
    ArrayGet,
    ArraySet,
    ArrayPush,
    // Concatenate every string in an array into one fresh string with a single
    // allocation: the O(n) string builder that replaces a chain of `concat`.
    StringOfArray,
    // Unboxed byte buffer, the storage under `Bytes` (`runtime/prism_buffer.c`): a
    // contiguous refcounted u8 region, header-compatible with the cell layout, so
    // Perceus, the leak balance, and the rc==1 in-place / shared-copy discipline
    // apply unchanged. `buf_set`/`buf_push` mutate in place when uniquely owned
    // (FBIP) and copy when shared, exactly like `array_set`. `string_of_buf` is the
    // total lossy decode; `buf_utf8_valid` gates the `String`/`Bytes` boundary.
    BufEmpty,
    BufNew,
    BufLen,
    BufGet,
    BufSet,
    BufPush,
    BufSlice,
    BufCat,
    BufEq,
    BufCmp,
    BufHash,
    BufOfString,
    StringOfBuf,
    BufUtf8Valid,
    // Stable sort of a `List` of a primitive element, chosen at the call site
    // when a `sort`/`sort_by_ord` use resolves to a canonical primitive `Ord`
    // instance. Not surface-callable; emitted only by the elaborator. Args are
    // `(kind, list)` where kind selects the key (see `prism_sort_prim`).
    SortPrim,
    // Type-aligned continuation queue ops, the Freer representation of an `EOp`'s
    // continuation. Emitted only by the free-monad effect lowering; never
    // surface-callable. `snoc(q, arrow)` appends, `concat(q1, q2)` joins, both
    // O(1); `uncons(q)` returns `TQNil`/`TQCons(head, tail)` for the Core `qApply`
    // template to match. The empty queue is `Unit`.
    TaqSnoc,
    TaqConcat,
    TaqUncons,
}

impl Builtin {
    pub(crate) const ALL: &'static [Self] = &[
        Self::Concat,
        Self::StrLen,
        Self::StrEq,
        Self::StrCmp,
        Self::Substring,
        Self::CharAt,
        Self::ShowChar,
        Self::Blake3,
        Self::ParseInt,
        Self::BigLit,
        Self::ParseFloat,
        Self::PowFloat,
        Self::Atan2,
        Self::Hypot,
        Self::Fmod,
        Self::ShowFloatPrec,
        Self::ProbeEnabled,
        Self::Getenv,
        Self::ReadFile,
        Self::ReadBytesFile,
        Self::WriteBytesFile,
        Self::WriteFile,
        Self::FileExists,
        Self::AppendFile,
        Self::RemoveFile,
        Self::StoreGet,
        Self::StorePut,
        Self::StoreHas,
        Self::Exit,
        Self::System,
        Self::Eprint,
        Self::ArgsCount,
        Self::Arg,
        Self::WallNow,
        Self::MonoNow,
        Self::ShowInt,
        Self::ShowI64,
        Self::ShowU64,
        Self::ShowBool,
        Self::ShowFloat,
        Self::ToI64,
        Self::ToU64,
        Self::IntOfI64,
        Self::IntOfU64,
        Self::I64Add,
        Self::I64Sub,
        Self::I64Mul,
        Self::I64Div,
        Self::U64Div,
        Self::I64Rem,
        Self::U64Rem,
        Self::I64Cmp,
        Self::U64Cmp,
        Self::U64Add,
        Self::U64Sub,
        Self::U64Mul,
        Self::ByteAt,
        Self::ByteLen,
        Self::StringOfBytes,
        Self::ArrayPop,
        Self::I64And,
        Self::I64Or,
        Self::I64Xor,
        Self::I64Shl,
        Self::I64Shr,
        Self::U64And,
        Self::U64Or,
        Self::U64Xor,
        Self::U64Shl,
        Self::U64Shr,
        Self::ArrayNew,
        Self::ArrayEmpty,
        Self::ArrayLen,
        Self::ArrayGet,
        Self::ArraySet,
        Self::ArrayPush,
        Self::StringOfArray,
        Self::BufEmpty,
        Self::BufNew,
        Self::BufLen,
        Self::BufGet,
        Self::BufSet,
        Self::BufPush,
        Self::BufSlice,
        Self::BufCat,
        Self::BufEq,
        Self::BufCmp,
        Self::BufHash,
        Self::BufOfString,
        Self::StringOfBuf,
        Self::BufUtf8Valid,
        Self::SortPrim,
        Self::TaqSnoc,
        Self::TaqConcat,
        Self::TaqUncons,
    ];

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Concat => "concat",
            Self::StrLen => "str_len",
            Self::StrEq => "str_eq",
            Self::StrCmp => "str_cmp",
            Self::Substring => "substring",
            Self::CharAt => "char_at",
            Self::ShowChar => "show_char",
            Self::Blake3 => "blake3",
            Self::ParseInt => "parse_int",
            Self::BigLit => "big_lit",
            Self::ParseFloat => "parse_float",
            Self::PowFloat => "pow_float",
            Self::Atan2 => "atan2",
            Self::Hypot => "hypot",
            Self::Fmod => "fmod",
            Self::ShowFloatPrec => "show_float_prec",
            Self::ProbeEnabled => "probe_enabled",
            Self::Getenv => "prim_getenv",
            Self::ReadFile => "prim_read_file",
            Self::ReadBytesFile => "prim_read_bytes",
            Self::WriteBytesFile => "prim_write_bytes",
            Self::WriteFile => "write_file",
            Self::FileExists => "prim_file_exists",
            Self::AppendFile => "append_file",
            Self::RemoveFile => "remove_file",
            Self::StoreGet => "prim_store_get",
            Self::StorePut => "prim_store_put",
            Self::StoreHas => "prim_store_has",
            Self::Exit => "exit",
            Self::System => "system",
            Self::Eprint => "eprint",
            Self::ArgsCount => "prim_args_count",
            Self::Arg => "prim_arg",
            Self::WallNow => "prim_wall_now",
            Self::MonoNow => "prim_mono_now",
            Self::ShowInt => "show_int",
            Self::ShowI64 => "show_i64",
            Self::ShowU64 => "show_u64",
            Self::ShowBool => "show_bool",
            Self::ShowFloat => "show_float",
            Self::ToI64 => "to_i64",
            Self::ToU64 => "to_u64",
            Self::IntOfI64 => "int_of_i64",
            Self::IntOfU64 => "int_of_u64",
            Self::I64Add => "i64_add",
            Self::I64Sub => "i64_sub",
            Self::I64Mul => "i64_mul",
            Self::I64Div => "i64_div",
            Self::U64Div => "u64_div",
            Self::I64Rem => "i64_rem",
            Self::U64Rem => "u64_rem",
            Self::I64Cmp => "i64_cmp",
            Self::U64Cmp => "u64_cmp",
            Self::U64Add => "u64_add",
            Self::U64Sub => "u64_sub",
            Self::U64Mul => "u64_mul",
            Self::ByteAt => "byte_at",
            Self::ByteLen => "byte_len",
            Self::StringOfBytes => "string_of_bytes",
            Self::ArrayPop => "array_pop",
            Self::I64And => "i64_and",
            Self::I64Or => "i64_or",
            Self::I64Xor => "i64_xor",
            Self::I64Shl => "i64_shl",
            Self::I64Shr => "i64_shr",
            Self::U64And => "u64_and",
            Self::U64Or => "u64_or",
            Self::U64Xor => "u64_xor",
            Self::U64Shl => "u64_shl",
            Self::U64Shr => "u64_shr",
            Self::ArrayNew => "array_new",
            Self::ArrayEmpty => "array_empty",
            Self::ArrayLen => "array_len",
            Self::ArrayGet => "array_get",
            Self::ArraySet => "array_set",
            Self::ArrayPush => "array_push",
            Self::StringOfArray => "string_of_array",
            Self::BufEmpty => "buf_empty",
            Self::BufNew => "buf_new",
            Self::BufLen => "buf_len",
            Self::BufGet => "buf_get",
            Self::BufSet => "buf_set",
            Self::BufPush => "buf_push",
            Self::BufSlice => "buf_slice",
            Self::BufCat => "buf_cat",
            Self::BufEq => "buf_eq",
            Self::BufCmp => "buf_cmp",
            Self::BufHash => "buf_hash",
            Self::BufOfString => "buf_of_string",
            Self::StringOfBuf => "string_of_buf",
            Self::BufUtf8Valid => "buf_utf8_valid",
            Self::SortPrim => "sort_prim",
            Self::TaqSnoc => "taq_snoc",
            Self::TaqConcat => "taq_concat",
            Self::TaqUncons => "taq_uncons",
        }
    }

    /// Runtime C symbol. `concat` maps to `prism_str_concat`; the rest are
    /// `prism_<name>`.
    #[must_use]
    pub fn sym(self) -> String {
        match self {
            Self::Concat => "prism_str_concat".into(),
            _ => format!("prism_{}", self.name()),
        }
    }

    #[must_use]
    pub fn from_name(s: &str) -> Option<Self> {
        Self::ALL.iter().copied().find(|b| b.name() == s)
    }

    /// Per-argument calling convention for the `prism_*` runtime call this
    /// builtin lowers to, read by codegen at `Comp::StrBuiltin`. `imm_args` are
    /// pointer-tagged immediates (int/bool) untagged before the call,
    /// `float_args` are boxed doubles unboxed before the call; every other
    /// argument passes raw (string cell, boxed 64-bit cell, or tagged Int word).
    /// `imm_res` is true when the result is a bare integer to retag.
    ///
    /// The match is exhaustive with no wildcard, so a new `Builtin` variant
    /// cannot ship without declaring its convention here: the compiler rejects
    /// the omission rather than letting a typo silently desync codegen untagging
    /// from the C runtime (the footgun the old string-keyed table carried).
    #[must_use]
    pub const fn abi(self) -> (&'static [usize], &'static [usize], bool) {
        match self {
            // Bare-integer result to retag (predicates, lengths, exit codes).
            Self::StrLen
            | Self::StrEq
            | Self::StrCmp
            | Self::ProbeEnabled
            | Self::ArgsCount
            | Self::WallNow
            | Self::MonoNow
            | Self::I64Cmp
            | Self::U64Cmp
            | Self::FileExists
            | Self::StoreHas
            | Self::System
            | Self::ArrayLen
            | Self::ByteLen
            | Self::BufLen
            | Self::BufEq
            | Self::BufCmp
            | Self::BufUtf8Valid => (&[], &[], true),
            // Index arg raw; bare-integer (char/byte) result to retag.
            Self::CharAt | Self::ByteAt | Self::BufGet => (&[1], &[], true),
            // Index arg raw; element/array result (cell or polymorphic) passes through.
            Self::ArrayGet | Self::ArraySet | Self::BufPush => (&[1], &[], false),
            // Single immediate arg (bool/char/index/exit/capacity); raw result.
            Self::ShowBool | Self::ShowChar | Self::Arg | Self::Exit | Self::ArrayNew => {
                (&[0], &[], false)
            }
            // Two immediate args (length and init byte); cell result.
            Self::BufNew => (&[0, 1], &[], false),
            Self::ShowFloat => (&[], &[0], false),
            Self::ShowFloatPrec => (&[1], &[0], false),
            Self::PowFloat | Self::Atan2 | Self::Hypot | Self::Fmod => (&[], &[0, 1], false),
            // Two immediate index/length args; cell result (a fresh string or buffer).
            Self::Substring | Self::BufSet | Self::BufSlice => (&[1, 2], &[], false),
            // Default: every argument passes raw and the result is a cell or an
            // already-tagged word. String ops, fixed-width arithmetic on boxed
            // 64-bit cells, and the elaborator-only ops all sit here.
            Self::Concat
            | Self::Blake3
            | Self::ParseInt
            | Self::BigLit
            | Self::ParseFloat
            | Self::Getenv
            | Self::ReadFile
            | Self::WriteFile
            | Self::AppendFile
            | Self::RemoveFile
            | Self::StoreGet
            | Self::StorePut
            | Self::Eprint
            | Self::ShowInt
            | Self::ShowI64
            | Self::ShowU64
            | Self::ToI64
            | Self::ToU64
            | Self::IntOfI64
            | Self::IntOfU64
            | Self::I64Add
            | Self::I64Sub
            | Self::I64Mul
            | Self::I64Div
            | Self::U64Div
            | Self::I64Rem
            | Self::U64Rem
            | Self::U64Add
            | Self::U64Sub
            | Self::U64Mul
            | Self::StringOfBytes
            | Self::ArrayPop
            | Self::I64And
            | Self::I64Or
            | Self::I64Xor
            | Self::I64Shl
            | Self::I64Shr
            | Self::U64And
            | Self::U64Or
            | Self::U64Xor
            | Self::U64Shl
            | Self::U64Shr
            | Self::ArrayEmpty
            | Self::ArrayPush
            | Self::StringOfArray
            | Self::BufEmpty
            | Self::BufCat
            | Self::BufHash
            | Self::BufOfString
            | Self::StringOfBuf
            | Self::ReadBytesFile
            | Self::WriteBytesFile
            | Self::SortPrim
            // Queue ops: arguments (queue cells, the Unit-typed empty, arrow
            // thunks) pass raw, result is a cell.
            | Self::TaqSnoc
            | Self::TaqConcat
            | Self::TaqUncons => (&[], &[], false),
        }
    }

    // Touches the host OS (file IO, env, process, args), so it has no
    // implementation in a browser build. Used to reject a snippet up front. The
    // input prims (read_file, file_exists, getenv, args_count, arg) are reached
    // only through the always-installed world handler, so their off-platform use
    // is detected from the surface wrappers instead (see `off_platform_builtins`).
    #[must_use]
    pub const fn off_platform(self) -> bool {
        matches!(
            self,
            Self::WriteFile
                | Self::WriteBytesFile
                | Self::AppendFile
                | Self::RemoveFile
                | Self::StorePut
                | Self::Exit
                | Self::System
                | Self::Eprint
        )
    }

    // The store-bridge prims have a full interpreter implementation but no C
    // runtime symbol yet, so native codegen refuses to lower them rather than
    // emitting a call to an undefined `prism_*` symbol that would only surface as
    // a link failure. Flip these off here once the C runtime grows the three
    // `prism_prim_store_*` functions (see the store bridge notes).
    #[must_use]
    pub const fn native_deferred(self) -> bool {
        matches!(self, Self::StoreGet | Self::StorePut | Self::StoreHas)
    }
}

pub const BUILTINS: &[(&str, usize, BuiltinKind)] = &[
    ("print", 1, BuiltinKind::Print),
    ("println", 1, BuiltinKind::Println),
    ("prim_print", 1, BuiltinKind::Print),
    ("prim_println", 1, BuiltinKind::Println),
    ("prim_read_int", 0, BuiltinKind::ReadInt),
    ("prim_read_line", 0, BuiltinKind::ReadLine),
    ("error", 1, BuiltinKind::Error),
    ("fatal", 1, BuiltinKind::Error),
    ("prim_rand", 0, BuiltinKind::Rand),
    ("srand", 1, BuiltinKind::Srand),
    ("to_float", 1, BuiltinKind::Float),
    ("truncate", 1, BuiltinKind::Float),
    ("floor_to_int", 1, BuiltinKind::Float),
    ("ceil_to_int", 1, BuiltinKind::Float),
    ("abs_float", 1, BuiltinKind::Float),
    ("sqrt", 1, BuiltinKind::Float),
    ("floor", 1, BuiltinKind::Float),
    ("ceil", 1, BuiltinKind::Float),
    ("round", 1, BuiltinKind::Float),
    ("trunc", 1, BuiltinKind::Float),
    ("sin", 1, BuiltinKind::Float),
    ("cos", 1, BuiltinKind::Float),
    ("tan", 1, BuiltinKind::Float),
    ("asin", 1, BuiltinKind::Float),
    ("acos", 1, BuiltinKind::Float),
    ("atan", 1, BuiltinKind::Float),
    ("sinh", 1, BuiltinKind::Float),
    ("cosh", 1, BuiltinKind::Float),
    ("tanh", 1, BuiltinKind::Float),
    ("exp", 1, BuiltinKind::Float),
    ("exp2", 1, BuiltinKind::Float),
    ("expm1", 1, BuiltinKind::Float),
    ("ln", 1, BuiltinKind::Float),
    ("log2", 1, BuiltinKind::Float),
    ("log10", 1, BuiltinKind::Float),
    ("log1p", 1, BuiltinKind::Float),
    ("cbrt", 1, BuiltinKind::Float),
    ("concat", 2, BuiltinKind::Str),
    ("str_len", 1, BuiltinKind::Str),
    ("str_eq", 2, BuiltinKind::Str),
    ("str_cmp", 2, BuiltinKind::Str),
    ("show_int", 1, BuiltinKind::Str),
    ("show_i64", 1, BuiltinKind::Str),
    ("show_u64", 1, BuiltinKind::Str),
    ("show_bool", 1, BuiltinKind::Str),
    ("show_float", 1, BuiltinKind::Str),
    ("show_float_prec", 2, BuiltinKind::Str),
    ("pow_float", 2, BuiltinKind::Str),
    ("atan2", 2, BuiltinKind::Str),
    ("hypot", 2, BuiltinKind::Str),
    ("fmod", 2, BuiltinKind::Str),
    ("parse_float", 1, BuiltinKind::Str),
    ("probe_enabled", 1, BuiltinKind::Str),
    ("substring", 3, BuiltinKind::Str),
    ("char_at", 2, BuiltinKind::Str),
    ("show_char", 1, BuiltinKind::Str),
    ("blake3", 1, BuiltinKind::Str),
    ("ord", 1, BuiltinKind::Coerce),
    ("chr", 1, BuiltinKind::Coerce),
    ("parse_int", 1, BuiltinKind::Str),
    ("prim_getenv", 1, BuiltinKind::Str),
    ("prim_read_file", 1, BuiltinKind::Str),
    ("prim_read_bytes", 1, BuiltinKind::Str),
    ("prim_write_bytes", 2, BuiltinKind::Str),
    ("write_file", 2, BuiltinKind::Str),
    ("prim_file_exists", 1, BuiltinKind::Str),
    ("append_file", 2, BuiltinKind::Str),
    ("remove_file", 1, BuiltinKind::Str),
    ("prim_store_get", 2, BuiltinKind::Str),
    ("prim_store_put", 3, BuiltinKind::Str),
    ("prim_store_has", 2, BuiltinKind::Str),
    ("exit", 1, BuiltinKind::Str),
    ("system", 1, BuiltinKind::Str),
    ("eprint", 1, BuiltinKind::Str),
    ("prim_args_count", 0, BuiltinKind::Str),
    ("prim_wall_now", 0, BuiltinKind::Str),
    ("prim_mono_now", 0, BuiltinKind::Str),
    ("prim_arg", 1, BuiltinKind::Str),
    ("to_i64", 1, BuiltinKind::Int),
    ("to_u64", 1, BuiltinKind::Int),
    ("int_of_i64", 1, BuiltinKind::Int),
    ("int_of_u64", 1, BuiltinKind::Int),
    ("array_new", 2, BuiltinKind::Str),
    ("array_empty", 0, BuiltinKind::Str),
    ("array_len", 1, BuiltinKind::Str),
    ("array_get", 2, BuiltinKind::Str),
    ("array_set", 3, BuiltinKind::Str),
    ("array_push", 2, BuiltinKind::Str),
    ("array_pop", 1, BuiltinKind::Str),
    ("string_of_array", 1, BuiltinKind::Str),
    ("buf_empty", 0, BuiltinKind::Str),
    ("buf_new", 2, BuiltinKind::Str),
    ("buf_len", 1, BuiltinKind::Str),
    ("buf_get", 2, BuiltinKind::Str),
    ("buf_set", 3, BuiltinKind::Str),
    ("buf_push", 2, BuiltinKind::Str),
    ("buf_slice", 3, BuiltinKind::Str),
    ("buf_cat", 2, BuiltinKind::Str),
    ("buf_eq", 2, BuiltinKind::Str),
    ("buf_cmp", 2, BuiltinKind::Str),
    ("buf_hash", 1, BuiltinKind::Str),
    ("buf_of_string", 1, BuiltinKind::Str),
    ("string_of_buf", 1, BuiltinKind::Str),
    ("buf_utf8_valid", 1, BuiltinKind::Str),
    ("string_of_bytes", 1, BuiltinKind::Str),
    ("byte_at", 2, BuiltinKind::Str),
    ("byte_len", 1, BuiltinKind::Str),
    ("i64_add", 2, BuiltinKind::Str),
    ("i64_sub", 2, BuiltinKind::Str),
    ("i64_mul", 2, BuiltinKind::Str),
    ("u64_add", 2, BuiltinKind::Str),
    ("u64_sub", 2, BuiltinKind::Str),
    ("u64_mul", 2, BuiltinKind::Str),
    ("i64_div", 2, BuiltinKind::Str),
    ("i64_rem", 2, BuiltinKind::Str),
    ("i64_cmp", 2, BuiltinKind::Str),
    ("u64_div", 2, BuiltinKind::Str),
    ("u64_rem", 2, BuiltinKind::Str),
    ("u64_cmp", 2, BuiltinKind::Str),
    ("i64_and", 2, BuiltinKind::Str),
    ("i64_or", 2, BuiltinKind::Str),
    ("i64_xor", 2, BuiltinKind::Str),
    ("i64_shl", 2, BuiltinKind::Str),
    ("i64_shr", 2, BuiltinKind::Str),
    ("u64_and", 2, BuiltinKind::Str),
    ("u64_or", 2, BuiltinKind::Str),
    ("u64_xor", 2, BuiltinKind::Str),
    ("u64_shl", 2, BuiltinKind::Str),
    ("u64_shr", 2, BuiltinKind::Str),
];

#[must_use]
pub fn builtin(name: &str) -> Option<(usize, BuiltinKind)> {
    BUILTINS
        .iter()
        .find(|(n, ..)| *n == name)
        .map(|&(_, arity, kind)| (arity, kind))
}

/// The surface output builtins (`print`/`println`).
///
/// Their calls route through the interceptable `Output` capability when the
/// `Replay` machinery is in scope. Lives here, with the rest of the builtin name
/// knowledge, so the desugarer's world-handler decision does not re-spell them.
pub const OUTPUT_BUILTINS: &[&str] = &["print", "println"];
