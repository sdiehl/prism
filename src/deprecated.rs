//! The compiler-owned deprecation registry.
//!
//! Deprecated builtins warn at their use sites (`resolve::lints`, emitted through
//! the typechecker warning channel), each paired with the replacement the warning
//! names. Two families live here: definitions superseded by the numerical tower
//! (`Num`/`Div`/`Ord`) - the float dot-operators (`+.` `-.` `*.` `/.` `<.` ...),
//! now that the plain operators are lane-polymorphic, and the fixed-width
//! arithmetic builtins (`i64_add`, `u64_mul`, ...) that duplicate an operator - and
//! byte-seam builtins superseded by the `Data.Bytes` conversions. A use of any of
//! them keeps compiling; the warning names the successor.
//!
//! This is the single home for the fact "X is deprecated in favor of Y". A
//! definition marked with the surface `deprecated "..."` annotation carries its
//! own suggestion in `Program::deprecated` instead; this module is only for the
//! compiler builtins and operators, which have no declaration to annotate.

use crate::kw;
use crate::syntax::ast::BinOp;

/// The `Data.Bytes` conversion that supersedes the lossy `string_of_bytes` builtin.
///
/// It validates, reporting ill-formed UTF-8 honestly as `None` rather than
/// repairing it to U+FFFD. The lossy behavior, when genuinely wanted, is still
/// reachable as `string_of_buf` over a `Buf`.
pub const BYTES_TO_STRING: &str = "bytes_to_string";

/// The builtins superseded by a replacement the warning names, each paired with
/// its successor.
///
/// The fixed-width arithmetic names map to the tower operator that now covers them
/// (only the operator-duplicating names appear: the bitwise `_and`/`_or`/`_xor`,
/// shift `_shl`/`_shr`, comparison `_cmp`, and conversion builtins stay, because no
/// operator supersedes them); `string_of_bytes` maps to its `Data.Bytes` successor.
pub const BUILTIN_DEPRECATED: &[(&str, &str)] = &[
    ("i64_add", kw::PLUS),
    ("i64_sub", kw::MINUS),
    ("i64_mul", kw::STAR),
    ("i64_div", kw::SLASH),
    ("i64_rem", kw::PERCENT),
    ("u64_add", kw::PLUS),
    ("u64_sub", kw::MINUS),
    ("u64_mul", kw::STAR),
    ("u64_div", kw::SLASH),
    ("u64_rem", kw::PERCENT),
    ("string_of_bytes", BYTES_TO_STRING),
];

/// The replacement operator for a deprecated arithmetic builtin, or `None` if
/// `name` is not a deprecated builtin.
#[must_use]
pub fn builtin_replacement(name: &str) -> Option<&'static str> {
    BUILTIN_DEPRECATED
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, repl)| *repl)
}

/// The tower operator a deprecated float dot-operator maps to, or `None` if
/// `op` is not deprecated.
///
/// The dot-operators were the Float-only spellings before the plain operators
/// unified the lanes.
#[must_use]
pub const fn operator_replacement(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Addf => Some(BinOp::Add),
        BinOp::Subf => Some(BinOp::Sub),
        BinOp::Mulf => Some(BinOp::Mul),
        BinOp::Divf => Some(BinOp::Div),
        BinOp::Eqf => Some(BinOp::Eq),
        BinOp::Nef => Some(BinOp::Ne),
        BinOp::Ltf => Some(BinOp::Lt),
        BinOp::Lef => Some(BinOp::Le),
        BinOp::Gtf => Some(BinOp::Gt),
        BinOp::Gef => Some(BinOp::Ge),
        _ => None,
    }
}
