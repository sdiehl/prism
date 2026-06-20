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
    ("args_count", 0, BuiltinKind::Str),
    ("arg", 1, BuiltinKind::Str),
    ("to_i64", 1, BuiltinKind::Int),
    ("to_u64", 1, BuiltinKind::Int),
    ("int_of_i64", 1, BuiltinKind::Int),
    ("int_of_u64", 1, BuiltinKind::Int),
];

#[must_use]
pub fn builtin(name: &str) -> Option<(usize, BuiltinKind)> {
    BUILTINS
        .iter()
        .find(|(n, ..)| *n == name)
        .map(|&(_, arity, kind)| (arity, kind))
}
