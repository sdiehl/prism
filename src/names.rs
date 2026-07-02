// Every compiler-synthesized name lives here. The scheme is unforgeable:
// identifiers lex as [a-z_][A-Za-z0-9_]* or [A-Z][A-Za-z0-9_]*, so no source
// program can contain `@` or `#` in a name, and `_D`-prefixed dictionary
// constructors cannot clash because user constructors must start uppercase.

pub const ENTRY_POINT: &str = "main";

// The internal function a string-interpolation hole lowers to. It renders its
// value through the total, type-directed display printer (raw for a top-level
// string) rather than the quoting `Show` method, so `"{s}"` inserts `s` verbatim.
pub const DISPLAY_FN: &str = "__display";

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

// The reserved capability effects (the IO-as-effects surface). `Console`/
// `FileSystem`/`Random`/`Env` route the nondeterministic input primitives; the
// separate `Output` effect routes `print`/`println`. The effect declarations
// themselves live in the prelude; this is the single source of truth for the set
// of names, so the `replayable` row check reads it rather than re-spelling the
// literal list.
pub const OUTPUT_EFFECT: &str = "Output";
pub const INPUT_CAPABILITY_EFFECTS: &[&str] = &["Console", "FileSystem", "Random", "Env"];

// The concurrency preemption seam. `Preempt` is the row label a preemptive
// scheduler will discharge, gating the yield-safepoint pass; it is reserved not
// shipped, so a user `effect Preempt` is rejected and the name stays free for
// that release without a later breaking change. It is deliberately absent from
// the `replayable` allowed set, so a preemptive program is non-replayable by the
// existing row-subset check with no new rule. (`Clock`, the logical-time
// capability, shipped in the `Concurrent` stdlib, so it is an ordinary effect and
// no longer reserved.)
pub const PREEMPT_EFFECT: &str = "Preempt";
pub const RESERVED_SEAM_EFFECTS: &[&str] = &[PREEMPT_EFFECT];

// The `Concurrent` scheduler entry points. `run_cooperative` is the policy-neutral
// wrap that the `--scheduler` flag retargets; `run_async` (FIFO) and `run_lifo`
// (LIFO) name a concrete policy and are never rewritten. Resolved (module-qualified)
// form, matched after name resolution.
pub const RUN_COOPERATIVE: &str = "Concurrent.run_cooperative";
pub const RUN_LIFO: &str = "Concurrent.run_lifo";

// The prelude surface wrappers that opt a program into the default `run_io` world
// handler: each performs a capability effect without handling it, so a `main`
// that reaches one needs the handler installed. This is the opt-in trigger, which
// is why it keys off the wrapper names rather than the raw capability operations:
// a program that performs a capability directly (and installs its own handler,
// e.g. `run_io(\() -> rng_rand(()))`) is deliberately left unwrapped. These are
// load-bearing prelude names like `main`/`run_io`; a drift guard test asserts each
// resolves to a prelude function so a rename fails loudly instead of silently
// changing codegen.
pub const CAP_WRAPPERS: &[&str] = &[
    "read_int",
    "read_line",
    "read_file",
    "file_exists",
    "rand",
    "getenv",
    "args_count",
    "arg",
    "args",
];

// The public `Replay` drivers. Their presence is what switches `print`/`println`
// onto the interceptable `Output` capability (so a durable resume can suppress
// already-emitted output); everywhere else printing lowers directly. Read by both
// the desugarer (world-handler decision) and the elaborator (output routing), so
// the two stay in lockstep from one definition.
pub const REPLAY_DRIVERS: &[&str] = &["Replay.record", "Replay.replay", "Replay.durable"];

// The prelude tail-recursive loop drivers a `while`/`loop` desugars to.
// `erase_control` recognizes calls to them by name to lower a recognized loop to
// direct control flow, so a prelude rename without a matching edit here would
// silently drop loop erasure onto the free-monad tier (a perf cliff, not a
// miscompile). Pinned by the drift-guard test below.
pub const REPEAT_WHILE: &str = "repeat_while";
pub const FOREVER: &str = "forever";

// The prelude class methods that operator elaboration and `deriving` call by
// name: `==`/`!=` dispatch through `eq`, `<`/`<=`/`>`/`>=` through `cmp`, and
// derived Show instances through `show`. One definition here keeps `derive.rs`,
// `tc`, and `elaborate` in lockstep with the prelude class declarations; the
// drift-guard test pins each to its class signature.
pub const EQ_METHOD: &str = "eq";
pub const ORD_METHOD: &str = "cmp";
pub const SHOW_METHOD: &str = "show";

// The plain prelude helper derived Ord instances lean on to order constructor
// tags. Pinned like `CAP_WRAPPERS` by the drift-guard test. (Derived Show's
// `concat` is a compiler builtin, canonical in `core::builtins`, not here.)
pub const INT_CMP: &str = "int_cmp";

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

// The top-level function a `without alloc { .. }` block lifts to. The `@` keeps
// it out of the source-identifier namespace; the block's captured locals become
// its parameters, and it carries the zero-allocation certificate.
#[must_use]
pub fn without_alloc_block(n: u32) -> String {
    format!("noalloc@{n}")
}

// Whether a name is a lifted `without alloc { .. }` block (so a diagnostic can
// name it "block" rather than leak the synthetic function name).
#[must_use]
pub fn is_without_alloc_block(name: &str) -> bool {
    name.starts_with("noalloc@")
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

// Fresh-binder prefixes, one per duplicating pass. The `%` lead is unforgeable
// (no source identifier or other synthesized name contains it), so a freshened
// binder collides with nothing in its surrounding context; the distinct suffix
// keeps two passes that freshen the same function from minting the same name, so
// binders stay globally unique across the pipeline.
pub const FRESH_INLINE: &str = "%i";
pub const FRESH_SPECIALIZE: &str = "%sp";

// A binder alpha-renamed to a fresh name by a duplicating pass (the inliner
// splicing a callee body, the specializer materializing a shared method body).
// `n` is a caller-threaded counter, so freshening is deterministic across a
// compilation. `prefix` is one of the `FRESH_*` constants above.
#[must_use]
pub fn fresh_binder(prefix: &str, n: u32) -> String {
    format!("{prefix}{n}")
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

#[cfg(test)]
mod tests {
    use super::{
        CAP_WRAPPERS, EQ_METHOD, FOREVER, INT_CMP, ORD_METHOD, REPEAT_WHILE, REPLAY_DRIVERS,
        SHOW_METHOD,
    };

    // The capability wrappers and Replay drivers are load-bearing prelude names
    // the desugarer and elaborator match by string to decide the world-handler
    // wrapping and output routing. A rename in the prelude without a matching edit
    // here would silently change codegen, so pin each name to its definition: a
    // drift fails the build instead of miscompiling.
    #[test]
    fn capability_names_resolve_to_prelude_functions() {
        let prelude = include_str!("../lib/prelude.pr");
        for w in CAP_WRAPPERS {
            assert!(
                prelude.contains(&format!("fn {w}(")),
                "capability wrapper `{w}` (names::CAP_WRAPPERS) has no `fn {w}(` in the prelude"
            );
        }
        let replay = include_str!("../lib/std/Replay.pr");
        for d in REPLAY_DRIVERS {
            let short = d.strip_prefix("Replay.").unwrap_or(d);
            assert!(
                replay.contains(&format!("fn {short}(")),
                "Replay driver `{d}` (names::REPLAY_DRIVERS) has no `fn {short}(` in Replay.pr"
            );
        }
    }

    // The loop drivers, class methods, and derive helpers are the remaining
    // string contracts between the compiler and the prelude: `erase_control`
    // matches the loop drivers, operator elaboration and `deriving` call the
    // methods and helpers. Pin each to its prelude definition so a rename fails
    // the build instead of silently degrading a tier or breaking deriving.
    #[test]
    fn prelude_hook_names_resolve_to_prelude_definitions() {
        let prelude = include_str!("../lib/prelude.pr");
        for w in [REPEAT_WHILE, FOREVER] {
            assert!(
                prelude.contains(&format!("fn {w}(")),
                "loop driver `{w}` (names) has no `fn {w}(` in the prelude"
            );
        }
        for m in [EQ_METHOD, ORD_METHOD, SHOW_METHOD] {
            assert!(
                prelude.contains(&format!("{m} :")),
                "class method `{m}` (names) has no `{m} :` signature in the prelude"
            );
        }
        assert!(
            prelude.contains(&format!("fn {INT_CMP}(")),
            "derive helper `{INT_CMP}` (names) has no `fn {INT_CMP}(` in the prelude"
        );
    }
}
