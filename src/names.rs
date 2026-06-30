// Every compiler-synthesized name lives here. The scheme is unforgeable:
// identifiers lex as [a-z_][A-Za-z0-9_]* or [A-Z][A-Za-z0-9_]*, so no source
// program can contain `@` or `#` in a name, and `_D`-prefixed dictionary
// constructors cannot clash because user constructors must start uppercase.

pub const ENTRY_POINT: &str = "main";

// The two ambient builtin effects, available without an `effect` declaration:
// console I/O and the `error`/`throw` exception channel.
pub const IO_EFFECT: &str = "IO";
pub const EXN_EFFECT: &str = "Exn";

// The builtin failure effect: `fail()` is the anonymous, recoverable twin of an
// `error`. Reserved surface names (not `@`-mangled), so `fail()` is an ordinary
// call and the row tracks it as `Fail`. User redeclaration is rejected.
pub const FAIL_EFFECT: &str = "Fail";
pub const FAIL_OP: &str = "fail";

// The internal loop-control effects. `break`/`continue` desugar to non-resumable
// performs of these, discharged by the loop's own handlers so the labels never
// surface. The effect names follow the error convention (clean, for a row that
// should never leak); the op names are `@`-mangled so no source program can
// perform or handle them directly. Injected only when a program uses the keywords.
pub const BREAK_EFFECT: &str = "Break";
pub const CONTINUE_EFFECT: &str = "Continue";
pub const BREAK_OP: &str = "loop@break";
pub const CONTINUE_OP: &str = "loop@continue";

// Recognizers for the loop-control ops, used by `erase_control` to match the
// handler templates the desugar emits (op names only; binders are alpha-renamed).
#[must_use]
pub fn is_break_op(name: &str) -> bool {
    name == BREAK_OP
}

#[must_use]
pub fn is_continue_op(name: &str) -> bool {
    name == CONTINUE_OP
}

// Early `return e` desugars to a non-resumable perform of this one-op effect,
// discharged by a handler the fn-body desugar installs, so it never surfaces. The
// op carries the returned value: a polymorphic param (`RETURN_VAL`, instantiated
// to the function's result type per site) and a never-resume result (THROW_RET).
pub const RETURN_EFFECT: &str = "Return";
pub const RETURN_OP: &str = "fn@return";
pub const RETURN_VAL: &str = "a@retval";

#[must_use]
pub fn is_return_op(name: &str) -> bool {
    name == RETURN_OP
}

pub const DICT_PREFIX: &str = "_D";

// The module path encoded in a canonical name: everything before the final `.`
// (an exported name like `Data.Map.insert`) or `@` (a private name like
// `Data.Map@helper`). A bare name belongs to the root module and yields "".
#[must_use]
pub fn module_of(canon: &str) -> &str {
    canon.rsplit_once(['.', '@']).map_or("", |(m, _)| m)
}

// A module-private top-level name (e.g. `Data.Map@helper`). The `@` is
// unforgeable in source so it cannot clash with a user name, and codegen
// rewrites it to a dot. `module_of` is the inverse.
#[must_use]
pub fn private(module: &str, name: &str) -> String {
    format!("{module}@{name}")
}

// Hygienic binders for synthesized handler and match arms.
pub const CONT: &str = "k@";
pub const STATE: &str = "s@";
pub const VAL: &str = "v@";
pub const UNIT_ARG: &str = "u@";
pub const RET: &str = "r@";
pub const ERR: &str = "e@";
pub const COMPOSE: &str = "x@";

// Fixed binders of the free-monad driver templates (the per-handle driver,
// `mask_driver`, `ebind`, and the resume thunks they emit). Each template is a
// closed top-level function and the templates never nest one inside another, so
// these fixed binders cannot capture across templates; the `@` keeps them clear
// of user names. `CONT`/`RET`/`COMPOSE` above are reused for `k@`/`r@`/`x@`.
pub const OP_ID: &str = "id@";
pub const OP_SKIP: &str = "sk@";
pub const OP_ARG: &str = "a@";
pub const RESUME_VAL: &str = "y@";
pub const RESUME_KONT: &str = "kr@";
pub const FWD_SKIP: &str = "sk1@";
pub const EBIND_FN: &str = "f@";

// Evidence binder holding the active clause of the op with the given id.
#[must_use]
pub fn ev(id: i64) -> String {
    format!("ev@{id}")
}

const VAR_GET_PREFIX: &str = "get@";
const VAR_SET_PREFIX: &str = "set@";

#[must_use]
pub fn var_get(x: &str, n: u32) -> String {
    format!("{VAR_GET_PREFIX}{x}@{n}")
}

#[must_use]
pub fn var_set(x: &str, n: u32) -> String {
    format!("{VAR_SET_PREFIX}{x}@{n}")
}

#[must_use]
pub fn is_var_get(name: &str) -> bool {
    name.starts_with(VAR_GET_PREFIX)
}

#[must_use]
pub fn is_var_set(name: &str) -> bool {
    name.starts_with(VAR_SET_PREFIX)
}

// "get@x@n" -> (x, n); the inverse of `var_get`.
#[must_use]
pub fn parse_var_get(name: &str) -> Option<(&str, &str)> {
    name.strip_prefix(VAR_GET_PREFIX)?.rsplit_once('@')
}

// "set@x@n" -> (x, n); the inverse of `var_set`.
#[must_use]
pub fn parse_var_set(name: &str) -> Option<(&str, &str)> {
    name.strip_prefix(VAR_SET_PREFIX)?.rsplit_once('@')
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

// "run@n" -> n; the inverse of `var_runner`.
#[must_use]
pub fn parse_var_runner(name: &str) -> Option<&str> {
    name.strip_prefix(VAR_RUNNER_PREFIX)
}

#[must_use]
pub fn dict_ctor(class: &str) -> String {
    format!("{DICT_PREFIX}{class}")
}

// The top-level function lowered from instance `inst`'s method `method`
// (e.g. `i@Show_Int@show`), called from that instance's dictionary thunks.
#[must_use]
pub fn instance_method(inst: &str, method: &str) -> String {
    format!("i@{inst}@{method}")
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

// Per-element binder for an `each` path step desugared to `map`.
#[must_use]
pub fn path_each(n: u32) -> String {
    format!("each@{n}")
}

// The base of a path update, bound once so an `each` step's `map` reads it
// without re-evaluating the (possibly effectful) base expression.
#[must_use]
pub fn path_base(n: u32) -> String {
    format!("base@{n}")
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
