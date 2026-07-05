//! The compiler-owned deprecation registry.
//!
//! Two kinds of definition are superseded by the numerical tower (`Num`/`Div`)
//! and warn at their use sites (`resolve::lints`, emitted through the typechecker
//! warning channel): the float dot-operators (`+.` `-.` `*.` `/.`), now that the
//! plain operators are lane-polymorphic, and the fixed-width arithmetic builtins
//! (`i64_add`, `u64_mul`, ...) that duplicate an operator. A use of either keeps
//! compiling; the warning names the replacement.
//!
//! This is the single home for the fact "X is deprecated in favor of Y". A
//! definition marked with the surface `deprecated "..."` annotation carries its
//! own suggestion in `Program::deprecated` instead; this module is only for the
//! compiler builtins and operators, which have no declaration to annotate.

use crate::kw;
use crate::syntax::ast::BinOp;

/// The fixed-width arithmetic builtins the tower's `+ - * / %` replace.
///
/// Each is paired with the operator to use instead (`NUM.md` migration section).
/// Only the operator-duplicating names appear: the bitwise (`_and`/`_or`/`_xor`),
/// shift (`_shl`/`_shr`), comparison (`_cmp`), and conversion builtins stay,
/// because no operator supersedes them.
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
/// The dot-operators were the Float-only spellings before
/// the plain operators unified the lanes; the comparison dot-operators
/// (`==.` `<.` ...) are intentionally absent, as no unified spelling exists yet.
#[must_use]
pub const fn operator_replacement(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Addf => Some(BinOp::Add),
        BinOp::Subf => Some(BinOp::Sub),
        BinOp::Mulf => Some(BinOp::Mul),
        BinOp::Divf => Some(BinOp::Div),
        _ => None,
    }
}
