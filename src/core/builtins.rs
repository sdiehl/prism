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

/// Inline floating-point op the elaborator emits as `Comp::FloatBuiltin`;
/// lowered to an FP intrinsic in codegen rather than a runtime call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatOp {
    ToFloat,
    Truncate,
    FloorToInt,
    CeilToInt,
    AbsFloat,
    Sqrt,
    Sin,
    Cos,
    Exp,
    Ln,
}

impl FloatOp {
    const ALL: &'static [Self] = &[
        Self::ToFloat,
        Self::Truncate,
        Self::FloorToInt,
        Self::CeilToInt,
        Self::AbsFloat,
        Self::Sqrt,
        Self::Sin,
        Self::Cos,
        Self::Exp,
        Self::Ln,
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
            Self::Sin => "sin",
            Self::Cos => "cos",
            Self::Exp => "exp",
            Self::Ln => "ln",
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
    ParseInt,
    // Materializes a bignum literal that overflows the 63-bit immediate from its
    // decimal text. Not surface-callable; emitted only by the elaborator, where
    // the input is always valid digits, so unlike `parse_int` it returns the raw
    // `Integer` cell rather than an `Option`.
    BigLit,
    ParseFloat,
    PowFloat,
    ShowFloatPrec,
    Getenv,
    ReadFile,
    WriteFile,
    FileExists,
    AppendFile,
    RemoveFile,
    Exit,
    System,
    Eprint,
    ArgsCount,
    Arg,
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
    // Stable sort of a `List` of a primitive element, chosen at the call site
    // when a `sort`/`sort_by_ord` use resolves to a canonical primitive `Ord`
    // instance. Not surface-callable; emitted only by the elaborator. Args are
    // `(kind, list)` where kind selects the key (see `prism_sort_prim`).
    SortPrim,
}

impl Builtin {
    const ALL: &'static [Self] = &[
        Self::Concat,
        Self::StrLen,
        Self::StrEq,
        Self::StrCmp,
        Self::Substring,
        Self::CharAt,
        Self::ShowChar,
        Self::ParseInt,
        Self::BigLit,
        Self::ParseFloat,
        Self::PowFloat,
        Self::ShowFloatPrec,
        Self::Getenv,
        Self::ReadFile,
        Self::WriteFile,
        Self::FileExists,
        Self::AppendFile,
        Self::RemoveFile,
        Self::Exit,
        Self::System,
        Self::Eprint,
        Self::ArgsCount,
        Self::Arg,
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
        Self::SortPrim,
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
            Self::ParseInt => "parse_int",
            Self::BigLit => "big_lit",
            Self::ParseFloat => "parse_float",
            Self::PowFloat => "pow_float",
            Self::ShowFloatPrec => "show_float_prec",
            Self::Getenv => "getenv",
            Self::ReadFile => "read_file",
            Self::WriteFile => "write_file",
            Self::FileExists => "file_exists",
            Self::AppendFile => "append_file",
            Self::RemoveFile => "remove_file",
            Self::Exit => "exit",
            Self::System => "system",
            Self::Eprint => "eprint",
            Self::ArgsCount => "args_count",
            Self::Arg => "arg",
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
            Self::SortPrim => "sort_prim",
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

    // Touches the host OS (file IO, env, process, args), so it has no
    // implementation in a browser build. Used to reject a snippet up front.
    #[must_use]
    pub const fn off_platform(self) -> bool {
        matches!(
            self,
            Self::Getenv
                | Self::ReadFile
                | Self::WriteFile
                | Self::FileExists
                | Self::AppendFile
                | Self::RemoveFile
                | Self::Exit
                | Self::System
                | Self::Eprint
                | Self::ArgsCount
                | Self::Arg
        )
    }
}

pub const BUILTINS: &[(&str, usize, BuiltinKind)] = &[
    ("print", 1, BuiltinKind::Print),
    ("println", 1, BuiltinKind::Println),
    ("read_int", 0, BuiltinKind::ReadInt),
    ("read_line", 0, BuiltinKind::ReadLine),
    ("error", 1, BuiltinKind::Error),
    ("rand", 0, BuiltinKind::Rand),
    ("srand", 1, BuiltinKind::Srand),
    ("to_float", 1, BuiltinKind::Float),
    ("truncate", 1, BuiltinKind::Float),
    ("floor_to_int", 1, BuiltinKind::Float),
    ("ceil_to_int", 1, BuiltinKind::Float),
    ("abs_float", 1, BuiltinKind::Float),
    ("sqrt", 1, BuiltinKind::Float),
    ("sin", 1, BuiltinKind::Float),
    ("cos", 1, BuiltinKind::Float),
    ("exp", 1, BuiltinKind::Float),
    ("ln", 1, BuiltinKind::Float),
    ("concat", 2, BuiltinKind::Str),
    ("str_len", 1, BuiltinKind::Str),
    ("str_eq", 2, BuiltinKind::Str),
    ("str_cmp", 2, BuiltinKind::Str),
    ("show_int", 1, BuiltinKind::Str),
    ("show_bool", 1, BuiltinKind::Str),
    ("show_float", 1, BuiltinKind::Str),
    ("show_float_prec", 2, BuiltinKind::Str),
    ("pow_float", 2, BuiltinKind::Str),
    ("parse_float", 1, BuiltinKind::Str),
    ("substring", 3, BuiltinKind::Str),
    ("char_at", 2, BuiltinKind::Str),
    ("show_char", 1, BuiltinKind::Str),
    ("ord", 1, BuiltinKind::Coerce),
    ("chr", 1, BuiltinKind::Coerce),
    ("parse_int", 1, BuiltinKind::Str),
    ("getenv", 1, BuiltinKind::Str),
    ("read_file", 1, BuiltinKind::Str),
    ("write_file", 2, BuiltinKind::Str),
    ("file_exists", 1, BuiltinKind::Str),
    ("append_file", 2, BuiltinKind::Str),
    ("remove_file", 1, BuiltinKind::Str),
    ("exit", 1, BuiltinKind::Str),
    ("system", 1, BuiltinKind::Str),
    ("eprint", 1, BuiltinKind::Str),
    ("args_count", 0, BuiltinKind::Str),
    ("arg", 1, BuiltinKind::Str),
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
