// Every compiler-synthesized name lives here. The scheme is unforgeable:
// identifiers lex as [a-z_][A-Za-z0-9_]* or [A-Z][A-Za-z0-9_]*, so no source
// program can contain `@` or `#` in a name, and `_D`-prefixed dictionary
// constructors cannot clash because user constructors must start uppercase.

pub const ENTRY_POINT: &str = "main";

// The builtin failure effect: `fail()` is the anonymous, recoverable twin of an
// `error`. Reserved surface names (not `@`-mangled), so `fail()` is an ordinary
// call and the row tracks it as `Fail`. User redeclaration is rejected.
pub const FAIL_EFFECT: &str = "Fail";
pub const FAIL_OP: &str = "fail";

pub const DICT_PREFIX: &str = "_D";

// Hygienic binders for synthesized handler and match arms.
pub const CONT: &str = "k@";
pub const STATE: &str = "s@";
pub const VAL: &str = "v@";
pub const UNIT_ARG: &str = "u@";
pub const RET: &str = "r@";
pub const ERR: &str = "e@";
pub const COMPOSE: &str = "x@";

#[must_use]
pub fn var_get(x: &str, n: u32) -> String {
    format!("get@{x}@{n}")
}

#[must_use]
pub fn var_set(x: &str, n: u32) -> String {
    format!("set@{x}@{n}")
}

#[must_use]
pub fn var_effect(x: &str, n: u32) -> String {
    format!("Var@{x}@{n}")
}

#[must_use]
pub fn named_op(op: &str, inst: &str, n: u32) -> String {
    format!("{op}@{inst}@{n}")
}

#[must_use]
pub fn named_effect(eff: &str, inst: &str, n: u32) -> String {
    format!("{eff}@{inst}@{n}")
}

// The single op of the effect synthesized for `error Name(..)`.
#[must_use]
pub fn throw_op(name: &str) -> String {
    format!("throw@{name}")
}

// Install-time binding for a `val` handler clause.
#[must_use]
pub fn val_tmp(n: u32) -> String {
    format!("val@{n}")
}

const VAR_RUNNER_PREFIX: &str = "run@";

#[must_use]
pub fn var_runner(n: u32) -> String {
    format!("{VAR_RUNNER_PREFIX}{n}")
}

#[must_use]
pub fn is_var_runner(name: &str) -> bool {
    name.starts_with(VAR_RUNNER_PREFIX)
}

#[must_use]
pub fn dict_ctor(class: &str) -> String {
    format!("{DICT_PREFIX}{class}")
}

// FBIP reuse token bound to the scrutinee variable it recycles.
#[must_use]
pub fn reuse_token(s: &str) -> String {
    format!("reuse#{s}")
}

// Hidden functions lowered from a `pattern` declaration's clauses.
#[must_use]
pub fn pat_view(name: &str) -> String {
    format!("view@{name}")
}

#[must_use]
pub fn pat_make(name: &str) -> String {
    format!("make@{name}")
}

// Scrutinee binder for the catchall arm a view pattern rewrites into.
#[must_use]
pub fn pat_tmp(n: u32) -> String {
    format!("scrut@{n}")
}

// Snapshot binder for a live `var` saved at the start of a `transact` block.
#[must_use]
pub fn snapshot(n: u32) -> String {
    format!("snap@{n}")
}

// Binders of a partial-application closure stub: the captured given arguments
// and the remaining parameters the closure still expects.
#[must_use]
pub fn closure_cap(i: usize) -> String {
    format!("cap@{i}")
}

#[must_use]
pub fn closure_rem(i: usize) -> String {
    format!("rem@{i}")
}

// A binder synthesized while elaborating surface syntax into core.
#[must_use]
pub fn elab_tmp(n: u32) -> String {
    format!("t@{n}")
}

// A binder synthesized while lowering effects (handler drivers, evidence
// threading, dispatch scratch). The id leads so the name starts with a digit,
// which no source identifier and no other synthesized name does: its own
// namespace, colliding with neither (the `hint` is for readability only).
#[must_use]
pub fn lowered(hint: &str, n: u32) -> String {
    format!("{n}@{hint}")
}

// Opaque rigid type variable standing in for an untyped local binder when
// print/show dispatch re-infers an argument's type. Keyed by position so its
// identity is its own (never derived from the term variable it shadows): the
// binder is present-but-opaque, so it shadows any same-named global and dispatch
// falls back to the integer printer.
#[must_use]
pub fn local_shadow(n: u32) -> String {
    format!("shadow@{n}")
}
