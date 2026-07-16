// Every compiler-synthesized name lives here. The scheme is unforgeable:
// identifiers lex as [a-z_][A-Za-z0-9_]* or [A-Z][A-Za-z0-9_]*, so no source
// program can contain `@` or `#` in a name, and `_D`-prefixed dictionary
// constructors cannot clash because user constructors must start uppercase.
//
// `@` is now also a surface token (the usage-row sigil, `T @ noalloc`). That
// does not weaken the scheme: unforgeability rests on the identifier charset,
// not on `@` being unlexable, and the identifier rule above must never admit
// `@`. A mangled name like `op@f@n` remains unspellable as a source name.

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

// The arena allocation effect (`Arena` stdlib module). `alloc(n)` is the single
// algebraic operation a `with_arena` handler services out of a bump region; it is
// graded `once` (single-shot resumption across the arena boundary) and never
// enters the recordable set (addresses are not reproducible). This is the single
// source of truth for the op name, read by the allocation-certificate check so an
// `@ noalloc` function that performs `alloc` is rejected like a fresh `Ctor`.
pub const ALLOC_EFFECT: &str = "Alloc";
pub const ALLOC_OP: &str = "alloc";

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
// `Clock` (declared in `Concurrent`, not the prelude) joins the replayable set:
// its real reads (`wall_now`/`mono_now`) are recorded observations like the other
// capabilities, and its virtual reads (`now`/`sleep` under `run_clock`) are pure,
// so a `replayable` function may perform `Clock`.
pub const INPUT_CAPABILITY_EFFECTS: &[&str] = &["Console", "FileSystem", "Random", "Env", "Clock"];

// The concurrency preemption seam. `Preempt` is the row label a preemptive
// scheduler will discharge, gating the yield-safepoint pass; it is reserved not
// shipped, so a user `effect Preempt` is rejected and the name remains available
// without a breaking change. It is deliberately absent from
// the `replayable` allowed set, so a preemptive program is non-replayable by the
// existing row-subset check with no new rule. (`Clock`, the logical-time
// capability, shipped in the `Concurrent` stdlib, so it is an ordinary effect and
// no longer reserved.)
pub const PREEMPT_EFFECT: &str = "Preempt";
// The boundary capabilities that are reserved but unshipped: `Net` (network)
// and `Entropy` (real randomness beyond the replayable `Random`). Reserving the
// effect names now means no package can give them an incompatible meaning
// before their capability protocols (and provenance event kinds) are designed;
// `Process` is deliberately absent because its observation label is already
// live. Each entry carries the reason its rejection diagnostic names.
pub const NET_EFFECT: &str = "Net";
pub const ENTROPY_EFFECT: &str = "Entropy";
pub const RESERVED_SEAM_EFFECTS: &[(&str, &str)] = &[
    (PREEMPT_EFFECT, "the concurrency preemption seam"),
    (NET_EFFECT, "the network boundary capability"),
    (ENTROPY_EFFECT, "the entropy boundary capability"),
];

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
// e.g. `run_io(\() -> rng_rand())`) is deliberately left unwrapped. These are
// required prelude names like `main`/`run_io`; a drift guard test asserts each
// resolves to a prelude function so a rename fails loudly instead of silently
// changing codegen.
pub const CAP_WRAPPERS: &[&str] = &[
    "read_int",
    "read_line",
    "read_file",
    "read_file_bytes",
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

// The `Incr` trace-replay drivers. Like `REPLAY_DRIVERS`, their presence switches
// `print`/`println` onto the interceptable `Output` capability, so an effectful
// memo's output can be recorded on a miss and replayed on a durable hit. Read by
// the same desugarer and elaborator sites, and validated against `Incr.pr`.
pub const INCR_REPLAY_DRIVERS: &[&str] =
    &["Incr.run_incr_durable_replay", "Incr.run_incr_store_replay"];

// The prelude tail-recursive loop drivers a `while`/`loop` desugars to.
// `erase_control` recognizes calls to them by name to lower a recognized loop to
// direct control flow, so a prelude rename without a matching edit here would
// silently drop loop erasure onto the free-monad tier (a perf cliff, not a
// miscompile). Guarded by the drift-guard test below.
pub const REPEAT_WHILE: &str = "repeat_while";
pub const FOREVER: &str = "forever";

// The prelude helper functions and stream op the desugarer and elaborator emit
// calls to by name while lowering surface sugar: `run_io` is the default IO world
// handler that `wrap_main_world` wraps `main` in; `force` is the `?.`/`??` Option
// forcer; `guard`/`succeeds` are list-comprehension qualifier tests; `scollect`
// collects a comprehension's `emit`s into a list; `smap` maps a function over a
// stream, the fusing collector a guard-free comprehension lowers through;
// `concat_map` flattens a mapped stream; `emit` is the `Stream` effect op a
// comprehension head performs; and
// `str_escape` renders a `String` as a quoted literal in a derived `Show`. Each is
// a compiler<->prelude string contract with no other home, so the drift-guard test
// checks every one to its prelude definition, exactly as the loop drivers above are
// pinned: a rename fails the build instead of silently breaking the sugar.
pub const RUN_IO: &str = "run_io";
pub const FORCE_FN: &str = "force";
pub const GUARD_FN: &str = "guard";
pub const SUCCEEDS_FN: &str = "succeeds";
pub const SCOLLECT_FN: &str = "scollect";
pub const SMAP_FN: &str = "smap";
pub const CONCAT_MAP_FN: &str = "concat_map";
pub const EMIT_OP: &str = "emit";
pub const STR_ESCAPE_FN: &str = "str_escape";

// The prelude class methods that operator elaboration and `deriving` call by
// name: `==`/`!=` dispatch through `eq`, `<`/`<=`/`>`/`>=` through `cmp`, and
// derived Show instances through `show`. One definition here keeps `derive.rs`,
// `tc`, and `elaborate` in lockstep with the prelude class declarations; the
// drift-guard test checks each to its class signature.
pub const EQ_METHOD: &str = "eq";
pub const ORD_METHOD: &str = "cmp";
pub const SHOW_METHOD: &str = "show";
// The prelude `Hash` method a derived instance folds fields through; its body
// leans on the `blake3` builtin (canonical in `core::builtins`), so only the
// method name is a prelude contract pinned here.
pub const HASH_METHOD: &str = "hash";
// The prelude `Functor` method the optic-path lowering (`each`) rewrites to, and
// the `Pow` method the `^` operator desugars to. The desugarer calls both by
// name like the operator methods above, so they are pinned to their prelude class
// signatures by the same drift guard.
pub const FMAP_METHOD: &str = "fmap";
pub const POW_METHOD: &str = "pow";
// The numeric operator methods: the arithmetic operators dispatch
// through these when an operand is `Num`/`Div`-polymorphic, and the prelude
// instance bodies define them. Names deliberately avoid `add`/`mul`/`negate`,
// which ordinary corpus programs define as free functions; a collision would make
// a class method shadow user code (the `eq_pair` lesson). Pinned to the prelude
// class signatures by the same drift guard as the methods above.
pub const NUM_ADD_METHOD: &str = "plus";
pub const NUM_SUB_METHOD: &str = "minus";
pub const NUM_MUL_METHOD: &str = "times";
pub const NUM_NEG_METHOD: &str = "negated";
pub const DIV_QUOT_METHOD: &str = "quotient";
pub const DIV_MOD_METHOD: &str = "modulo";
// The literal-injection method: a bare integer literal used at a `Num`
// polymorphic type elaborates through `from_int`, so generic `given Num(a)` code
// may write `x + 1`. It is the compile-time-erased analogue of `fromInteger`:
// monomorphic literals never reach it (they carry their lane's constant
// directly), and where a generic function is specialized to a concrete lane the
// call collapses to that lane's conversion of the constant.
pub const NUM_FROMINT_METHOD: &str = "from_int";
// The wire (`lib/std/Wire.pr`) and property-generator (`lib/std/Test.pr`) methods
// a derived instance emits by name. Pinned to those modules' class signatures by
// the drift-guard test, exactly as the prelude methods above are pinned to the
// prelude.
pub const ENCODE_METHOD: &str = "encode";
pub const DECODE_METHOD: &str = "decode";
pub const ARBITRARY_METHOD: &str = "arbitrary";
// The `Stable` class's sole method: a per-type constant string, the type's shape
// contract digest. A derived `Stable` instance's body is this digest injected by
// the compiler from the one shape-digest computation (`core::contract_digest`), so
// ordinary code never hand-threads a magic digest into the wire envelope.
pub const SHAPE_DIGEST_METHOD: &str = "shape_digest_of";
// The codec combinators a derived `Serialize` body threads a `Bytes` through:
// the encoder appends a constructor tag and joins field encodings, the decoder
// peels a tag off the front. Their bodies live in the wire library (built
// separately); these are the names the derivation and that library agree on, so
// they have one home here rather than a bare string re-typed at each use.
pub const WIRE_TAG: &str = "wire_tag";
pub const WIRE_CAT: &str = "wire_cat";
pub const WIRE_EMPTY: &str = "wire_empty";
pub const WIRE_GET_TAG: &str = "wire_get_tag";
pub const WIRE_IS_EMPTY: &str = "wire_is_empty";
// The wire envelope helpers a `stable` block's generated frame functions thread a
// value through: the explicit-digest value-frame encode/decode escape hatches (the
// block already knows each rung's compiler-computed digest, so it passes it in),
// and the digest-agnostic opener the ladder dispatch reads an older frame with.
// Their bodies live in the wire library; these are the names the desugar and that
// library agree on, one home rather than a bare string re-typed at each site.
pub const WIRE_ENCODE_VALUE_WITH_DIGEST: &str = "wire_encode_value_with_digest";
pub const WIRE_DECODE_VALUE_WITH_DIGEST: &str = "wire_decode_value_with_digest";
pub const WIRE_OPEN_VALUE_ANY: &str = "wire_open_value_any";

// The `stable`-block version ladder. A stable type
// desugars to one frozen rung type per version and a set of plain adjacent
// converter functions; these helpers are the single home for the generated
// names, so the desugar that emits a converter and the ladder-composition that
// calls it agree without either re-typing a string. The grammar has no
// two-parameter `Migrate` class syntax, so the converters are plain functions,
// not instances. The names are only ever
// generated, never parsed back to recover a fact, so this is name synthesis, not
// a cross-phase string contract.

/// The frozen rung type minted for version `ver` of stable type `ty`.
///
/// (`Order`, `V1` -> `Order.V1`.) The newest rung keeps the bare type name, so a
/// program builds and matches the current version as the type itself; a shipped
/// predecessor wears the dotted version tag.
#[must_use]
pub fn stable_rung(ty: &str, ver: &str) -> String {
    format!("{ty}.{ver}")
}

/// The generated total upgrade between two adjacent rungs (`V1 -> V2`).
#[must_use]
pub fn stable_upgrade(ty: &str, from: &str, to: &str) -> String {
    format!("upgrade_{ty}_{from}_{to}")
}

/// The generated partial downgrade between two adjacent rungs (`V2 -> V1`),
/// returning `(older, Loss)`.
#[must_use]
pub fn stable_downgrade(ty: &str, from: &str, to: &str) -> String {
    format!("downgrade_{ty}_{from}_{to}")
}

/// The ladder-composition decode dispatch for a stable type: given a source
/// version index and a body, decode that rung and walk it up to the current type.
#[must_use]
pub fn stable_decode_ladder(ty: &str) -> String {
    format!("decode_ladder_{ty}")
}

/// The generated current-rung frame encoder for a stable type.
///
/// Wraps a value in a `value` frame carrying the compiler-known current-rung
/// contract digest, so user code stops hand-threading a magic digest string.
#[must_use]
pub fn stable_wire_encode(ty: &str) -> String {
    format!("wire_encode_{ty}")
}

/// The generated current-rung frame decoder for a stable type: the inverse of
/// `stable_wire_encode`, checking the current-rung digest before the body.
#[must_use]
pub fn stable_wire_decode(ty: &str) -> String {
    format!("wire_decode_{ty}")
}

/// A converter's single parameter, the lowercased source rung tag (`V2` -> `v2`),
/// so a hand-written `{ ..v2, .. }` body binds it.
#[must_use]
pub fn stable_param(ver: &str) -> String {
    ver.to_lowercase()
}
// The property-generator combinators a derived `Arbitrary` composes: the runner
// (`gen_run`), the applicative pieces (`gen_const`/`gen_bind`), the sum picker
// (`gen_choose`), and the depth control (`gen_resize`) from `Quickcheck`, plus
// `arb_gen` from `Test` that wraps a field's instance back into a generator. A
// derived body suspends its recursion inside these so its own effect stays flat.
pub const QC_GEN_RUN: &str = "gen_run";
pub const QC_GEN_CONST: &str = "gen_const";
pub const QC_GEN_BIND: &str = "gen_bind";
pub const QC_GEN_CHOOSE: &str = "gen_choose";
pub const QC_GEN_RESIZE: &str = "gen_resize";
pub const QC_ARB_GEN: &str = "arb_gen";

// The plain prelude helper derived Ord instances lean on to order constructor
// tags. Pinned like `CAP_WRAPPERS` by the drift-guard test. (Derived Show's
// `concat` is a compiler builtin, canonical in `core::builtins`, not here.)
pub const INT_CMP: &str = "int_cmp";

// The two prelude entry points whose call on a canonical primitive `Ord` lowers
// to the native sort kernel (`SortPrim`); any other function keeps the generic
// merge sort. Matched by name in the elaborator, pinned to the prelude by the
// drift guard.
pub const SORT_FN: &str = "sort";
pub const SORT_BY_ORD_FN: &str = "sort_by_ord";

// The kind tag the native sort kernel (`prism_sort_prim`, `runtime/prism_sort.c`)
// switches on to pick a comparison: this table is the elaborator's half of that
// cross-phase contract, so a tag here that disagrees with the C `switch` silently
// misorders one element type. The pairing is pinned end-to-end by the native
// sort test (`tests/sort_kind.rs`), which sorts a sign-distinguishing list of
// each type and diffs native against the interpreter; the names are pinned to
// their prelude instances by the drift guard.
pub const SORT_KIND_INTEGER: i64 = 0;
pub const SORT_KIND_I64: i64 = 1;
pub const SORT_KIND_U64: i64 = 2;
pub const SORT_KIND_FLOAT: i64 = 3;
pub const SORT_PRIM_INSTANCES: &[(&str, i64)] = &[
    ("ordInt", SORT_KIND_INTEGER),
    ("ordI64", SORT_KIND_I64),
    ("ordU64", SORT_KIND_U64),
    ("ordFloat", SORT_KIND_FLOAT),
];

// The native sort kind for a canonical primitive `Ord` instance, or `None` to
// keep the generic merge sort (a user instance, or a non-primitive type). The
// inverse-ish lookup into `SORT_PRIM_INSTANCES`, so the elaborator never respells
// the tag literals.
#[must_use]
pub fn sort_prim_kind(inst: &str) -> Option<i64> {
    SORT_PRIM_INSTANCES
        .iter()
        .find(|(n, _)| *n == inst)
        .map(|(_, k)| *k)
}

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

#[must_use]
pub fn dict_param(i: usize) -> String {
    format!("_c{i}")
}

#[must_use]
pub fn generated_param(i: usize) -> String {
    format!("_p{i}")
}

pub const OUTPUT_PRINT_OP: &str = "out_print";
pub const OUTPUT_PRINTLN_OP: &str = "out_println";

#[must_use]
pub const fn output_op(newline: bool) -> &'static str {
    if newline {
        OUTPUT_PRINTLN_OP
    } else {
        OUTPUT_PRINT_OP
    }
}

// The module path encoded in a canonical name: everything before the final `.`
// (an exported name like `Data.Map.insert`) or `@` (a private name like
// `Data.Map@helper`). A bare name belongs to the root module and yields "".
#[must_use]
pub fn module_of(canon: &str) -> &str {
    canon.rsplit_once(['.', '@']).map_or("", |(m, _)| m)
}

// The unqualified tail of a canonical name: everything after the final `.` or
// `@` (`Data.Map.insert` -> `insert`, `Wire.Serialize` -> `Serialize`), a root
// name unchanged. The inverse of `module_of`; `deriving (C)` and rung derivation
// use it to recover the token the surface wrote for an in-scope class.
#[must_use]
pub fn bare_name(canon: &str) -> &str {
    canon.rsplit_once(['.', '@']).map_or(canon, |(_, n)| n)
}

// A module-private top-level name (e.g. `Data.Map@helper`). The `@` is
// unforgeable in source so it cannot clash with a user name. Native codegen
// preserves the distinction from the exported `Data.Map.helper` through its
// reversible name encoding. `module_of` is the structural inverse here.
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

// The threaded accumulator parameter every state-mode producer gains, trailing
// its evidence parameters. It sits beside `ev` because the two are laid out
// together on every fused producer, and one home keeps the state passes from
// drifting on a binder they must agree on by name.
pub const STATE_ACC: &str = "st@";

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

// The head sigil of the private effect a `var` cell desugars to: `Var@{x}@{n}`.
const VAR_EFFECT_HEAD: &str = "Var";

#[must_use]
pub fn var_effect(x: &str, n: u32) -> String {
    format!("{VAR_EFFECT_HEAD}@{x}@{n}")
}

#[must_use]
pub fn named_op(op: &str, inst: &str, n: u32) -> String {
    format!("{op}@{inst}@{n}")
}

// "op@inst@n" -> (op, inst); the tested inverse of `named_op`, recovering that a
// core `do` targets a named handler instance's private operation rather than a
// bare (globally handled or ambient) effect op. A `var` cell's `get@x@n`/
// `set@x@n` share this three-part shape, so a caller that also cares about var
// cells must try `parse_var_get`/`parse_var_set` first. The one home for the
// inverse, so a diagnostic never re-parses the `@` layout at a use site.
#[must_use]
pub fn parse_named_op(name: &str) -> Option<(&str, &str)> {
    let (op, rest) = name.split_once('@')?;
    let (inst, tail) = rest.rsplit_once('@')?;
    (!op.is_empty()
        && !inst.is_empty()
        && !tail.is_empty()
        && tail.bytes().all(|b| b.is_ascii_digit()))
    .then_some((op, inst))
}

// Whether a name was minted by the compiler rather than written in source. Every
// synthesized name carries a sigil the identifier charset forbids (`@` mangling,
// `#` reuse tokens, a `%` freshening lead; see the module header), so a name free
// of all three is a source-level binding. Diagnostic passes use this to report a
// program's own captures and skip lowering scratch (`t@n`, resume/state binders).
#[must_use]
pub fn is_synthesized(name: &str) -> bool {
    name.contains(['@', '#', '%'])
}

#[must_use]
pub fn named_effect(eff: &str, inst: &str, n: u32) -> String {
    format!("{eff}@{inst}@{n}")
}

// A compiler-synthesized scoped effect that has leaked into an inferred row
// because a value carrying it escaped its introducing scope. Recovering the
// origin lets a "missing effect" diagnostic name the escape route instead of
// exposing the mangled label; the `@` sigil is unforgeable from source, so the
// two spellings never collide with a user effect. This is the tested inverse of
// `var_effect` and `named_effect` (facts travel as data, not by re-parsing a
// name at a use site: the one home is here, with a round-trip test).
#[derive(Debug, PartialEq, Eq)]
pub enum ScopedEscape<'a> {
    /// A named handler instance `inst` handling effect `effect` (`named_effect`).
    NamedInstance { effect: &'a str, instance: &'a str },
    /// A `var` cell named `name` (`var_effect`).
    Var { name: &'a str },
}

#[must_use]
pub fn parse_scoped_escape(label: &str) -> Option<ScopedEscape<'_>> {
    let (head, rest) = label.split_once('@')?;
    let (mid, tail) = rest.rsplit_once('@')?;
    if mid.is_empty() || tail.is_empty() || !tail.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if head == VAR_EFFECT_HEAD {
        Some(ScopedEscape::Var { name: mid })
    } else {
        Some(ScopedEscape::NamedInstance {
            effect: head,
            instance: mid,
        })
    }
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

// Prefix marking a top-level function lowered from an instance method. The `@`
// is unforgeable in source, so no user function can collide with one.
pub const INSTANCE_METHOD_PREFIX: &str = "i@";

// The top-level function lowered from instance `inst`'s method `method`
// (e.g. `i@Show_Int@show`), called from that instance's dictionary thunks.
#[must_use]
pub fn instance_method(inst: &str, method: &str) -> String {
    format!("{INSTANCE_METHOD_PREFIX}{inst}@{method}")
}

// The shared prefix of every top-level function lowered from instance `inst`'s
// methods (`i@<inst>@`). Both the stdlib fingerprint and the store's coherence
// binding recover an instance's method hashes by stripping this from the lowered
// names, so the sigil has one home rather than a re-typed `i@{}@` at each site.
#[must_use]
pub fn instance_method_prefix(inst: &str) -> String {
    format!("{INSTANCE_METHOD_PREFIX}{inst}@")
}

// Whether a lowered top-level name is an instance method (minted by
// `instance_method`). Its effect discipline is enforced against the class
// signature at `check_instance`, so passes keyed on top-level `fn` rows treat it
// separately.
#[must_use]
pub fn is_instance_method(name: &str) -> bool {
    name.starts_with(INSTANCE_METHOD_PREFIX)
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

// Fresh-binder prefixes, one per pass that synthesizes local binders. The `%` lead is unforgeable
// (no source identifier or other synthesized name contains it), so a freshened
// binder collides with nothing in its surrounding context; the distinct suffix
// keeps two passes that freshen the same function from minting the same name, so
// binders stay globally unique across the pipeline.
pub const FRESH_INLINE: &str = "%i";
pub const FRESH_SPECIALIZE: &str = "%sp";
/// Typed witness name used to sequence inserted reference-count operations.
pub const RC_SEQUENCE_BINDER: &str = "%rcs";
/// Result binders introduced so an owned loan can be dropped after a borrowed call.
pub const FRESH_RC: &str = "%rc";
/// Type/row quantifiers introduced while retaining generic dictionary builders
/// in a specialized clone. This namespace never reaches compatibility Core.
pub const FRESH_SPECIALIZE_QUANTIFIER: &str = "%spq";
pub const FRESH_FUSE: &str = "%fu";
/// The ambient residual-row quantifier evidence passing appends to each
/// callable that gains evidence parameters.
///
/// A witness-only namespace with its own counter: it never reaches
/// compatibility Core, so it must not consume the term `Fresh` counter that
/// fixes generated term names and tick order.
pub const FRESH_EVIDENCE_ROW: &str = "%evr";
/// The ambient direct-effect row shared by declarations translated to the
/// free-monad calling convention. It is witness-only and never reaches
/// compatibility Core.
pub const FREE_MONAD_ROW: &str = "%fmr";
/// The accumulator-type quantifier state fusion appends to a producer whose
/// accumulator no clause observes. Witness-only, like [`FRESH_EVIDENCE_ROW`].
pub const FRESH_STATE_TYPE: &str = "%stt";

/// The ambient residual-row quantifier bound *inside* an evidence-carrying
/// thunk's own type, named by the operations it carries evidence for.
///
/// A callable's ambient row is instantiated away at each call site, so its name
/// is private and a counter suffices. A thunk's is not: the quantifier lives
/// inside a parameter type, so the caller's thunk and the callee's declared
/// parameter must agree on it by name, and the two are minted in different
/// passes that share no counter. Deriving the name from the operation ids is
/// what makes them agree without one, since both sides already agree on that
/// set. `ids` must be ascending and deduplicated, which is the one order
/// evidence is ever laid out in.
#[must_use]
pub fn evidence_row(ids: &[i64]) -> String {
    qualified_by_ops(FRESH_EVIDENCE_ROW, ids)
}

/// The accumulator-type quantifier a state-fused producer gains when no clause
/// pins the accumulator to a concrete type, named by the operations fused into
/// it.
///
/// Derived from the operation ids for the same reason [`evidence_row`] is, and
/// the reason is sharper here: a producer's declared accumulator parameter and
/// the producer thunk type nested in a caller's parameter are rewritten at
/// different sites, and Core subtyping compares quantifier lists by exact
/// equality with no alpha-renaming, so a private counter cannot make the two
/// agree. `ids` must be ascending and deduplicated.
#[must_use]
pub fn state_type(ids: &[i64]) -> String {
    qualified_by_ops(FRESH_STATE_TYPE, ids)
}

// A witness-only quantifier name derived from the fused operation ids, so that
// two sites minting it in different passes agree without sharing a counter.
fn qualified_by_ops(namespace: &str, ids: &[i64]) -> String {
    let mut name = String::from(namespace);
    for id in ids {
        name.push('@');
        name.push_str(&id.to_string());
    }
    name
}

// The top-level clone emitted when dictionary specialization fixes a constrained
// function's leading dictionaries. `n` is the specializer's deterministic
// request-order counter. Keeping this beside the other synthesized-name schemes
// prevents the typed and legacy passes from drifting on clone identity.
#[must_use]
pub fn specialized_clone(function: &str, n: usize) -> String {
    format!("{function}$sp{n}")
}

// The top-level join function stream fusion emits when it ties a driven pipeline's
// knot. `n` is a compilation-deterministic counter so two fused pipelines in one
// program get distinct names; the `%` lead is unforgeable, so the join collides
// with no source function and no other synthesized name.
#[must_use]
pub fn fused_join(n: u32) -> String {
    format!("%fuse${n}")
}

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
        is_synthesized, is_var_get, is_var_runner, is_var_set, module_of, named_effect, named_op,
        parse_named_op, parse_scoped_escape, parse_var_get, parse_var_runner, parse_var_set,
        private, sort_prim_kind, throw_op, var_effect, var_get, var_runner, var_set, ScopedEscape,
        ARBITRARY_METHOD, CAP_WRAPPERS, CONCAT_MAP_FN, DECODE_METHOD, DIV_MOD_METHOD,
        DIV_QUOT_METHOD, EMIT_OP, ENCODE_METHOD, EQ_METHOD, FMAP_METHOD, FORCE_FN, FOREVER,
        GUARD_FN, HASH_METHOD, INCR_REPLAY_DRIVERS, INT_CMP, NUM_ADD_METHOD, NUM_FROMINT_METHOD,
        NUM_MUL_METHOD, NUM_NEG_METHOD, NUM_SUB_METHOD, ORD_METHOD, POW_METHOD, QC_ARB_GEN,
        QC_GEN_BIND, QC_GEN_CHOOSE, QC_GEN_CONST, QC_GEN_RESIZE, QC_GEN_RUN, REPEAT_WHILE,
        REPLAY_DRIVERS, RUN_IO, SCOLLECT_FN, SHAPE_DIGEST_METHOD, SHOW_METHOD, SMAP_FN,
        SORT_BY_ORD_FN, SORT_FN, SORT_PRIM_INSTANCES, STR_ESCAPE_FN, SUCCEEDS_FN, WIRE_CAT,
        WIRE_DECODE_VALUE_WITH_DIGEST, WIRE_EMPTY, WIRE_ENCODE_VALUE_WITH_DIGEST, WIRE_GET_TAG,
        WIRE_IS_EMPTY, WIRE_OPEN_VALUE_ANY, WIRE_TAG,
    };

    #[test]
    fn specialization_clone_names_use_the_canonical_scheme() {
        assert_eq!(super::specialized_clone("map", 7), "map$sp7");
    }

    // Both schemes name a quantifier that two passes must agree on by name
    // without sharing a counter, so the operation ids alone must determine the
    // name, and the two families must never collide: a producer's accumulator
    // type and its ambient residual row sit on the same signature, and Core
    // subtyping compares quantifiers by exact equality.
    #[test]
    fn op_derived_quantifier_names_are_determined_and_disjoint() {
        assert_eq!(super::evidence_row(&[3, 12]), "%evr@3@12");
        assert_eq!(super::state_type(&[3, 12]), "%stt@3@12");
        assert_ne!(super::state_type(&[3, 12]), super::evidence_row(&[3, 12]));
        assert_ne!(super::state_type(&[3, 12]), super::state_type(&[3, 1, 2]));
        assert!(is_synthesized(&super::state_type(&[3])));
    }

    // The capability wrappers and Replay drivers are required prelude names
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
        let incr = include_str!("../lib/std/Incr.pr");
        for d in INCR_REPLAY_DRIVERS {
            let short = d.strip_prefix("Incr.").unwrap_or(d);
            assert!(
                incr.contains(&format!("fn {short}(")),
                "Incr driver `{d}` (names::INCR_REPLAY_DRIVERS) has no `fn {short}(` in Incr.pr"
            );
        }
    }

    // The loop drivers, class methods, and desugar helpers are the string
    // contracts between the compiler and the prelude: `erase_control` matches the
    // loop drivers, operator/optic elaboration and `deriving` call the methods, and
    // the desugarer emits calls to the helper functions and the `emit` op while
    // lowering sugar. Each name now has a single home in `names`, referenced from
    // both its emit and its match site, so those two directions agree by
    // construction; this guard checks the remaining direction, name<->prelude, so a
    // prelude rename fails the build instead of silently degrading a tier or
    // breaking deriving or a comprehension.
    #[test]
    fn prelude_hook_names_resolve_to_prelude_definitions() {
        let prelude = include_str!("../lib/prelude.pr");
        for w in [REPEAT_WHILE, FOREVER] {
            assert!(
                prelude.contains(&format!("fn {w}(")),
                "loop driver `{w}` (names) has no `fn {w}(` in the prelude"
            );
        }
        for m in [
            EQ_METHOD,
            ORD_METHOD,
            SHOW_METHOD,
            HASH_METHOD,
            FMAP_METHOD,
            POW_METHOD,
            NUM_ADD_METHOD,
            NUM_SUB_METHOD,
            NUM_MUL_METHOD,
            NUM_NEG_METHOD,
            NUM_FROMINT_METHOD,
            DIV_QUOT_METHOD,
            DIV_MOD_METHOD,
        ] {
            assert!(
                prelude.contains(&format!("{m} :")),
                "class method `{m}` (names) has no `{m} :` signature in the prelude"
            );
        }
        // The free helper functions the desugarer emits calls to while lowering
        // sugar: the IO world handler, the Option forcer, and the comprehension
        // qualifier/collector helpers.
        for f in [
            RUN_IO,
            FORCE_FN,
            GUARD_FN,
            SUCCEEDS_FN,
            SCOLLECT_FN,
            SMAP_FN,
            CONCAT_MAP_FN,
            STR_ESCAPE_FN,
        ] {
            assert!(
                prelude.contains(&format!("fn {f}(")),
                "prelude helper `{f}` (names) has no `fn {f}(` in the prelude"
            );
        }
        // The `Stream` effect op a comprehension head performs. Declared bare
        // (grade `many`, the default), so anchor on the full op signature.
        assert!(
            prelude.contains(&format!("{EMIT_OP}(a) : Unit")),
            "stream op `{EMIT_OP}` (names) has no `{EMIT_OP}(a) : Unit` declaration in the prelude"
        );
        assert!(
            prelude.contains(&format!("fn {INT_CMP}(")),
            "derive helper `{INT_CMP}` (names) has no `fn {INT_CMP}(` in the prelude"
        );
    }

    // The opt-in wire/property classes and combinators a derived `Serialize` or
    // `Arbitrary` calls by name live outside the prelude (`Wire`/`Test`/
    // `Quickcheck`). Pin each name the derivation emits to the module signature it
    // resolves to, so a rename in either half fails the build rather than breaking
    // deriving silently, exactly as the prelude hooks above are pinned.
    #[test]
    fn library_hook_names_resolve_to_module_definitions() {
        let wire = include_str!("../lib/std/Wire.pr");
        for m in [ENCODE_METHOD, DECODE_METHOD, SHAPE_DIGEST_METHOD] {
            assert!(
                wire.contains(&format!("{m} :")),
                "class method `{m}` (names) has no `{m} :` signature in Wire.pr"
            );
        }
        // The byte builders a derived `Serialize` body threads a `Bytes` through:
        // `wire_cat`/`wire_tag`/`wire_get_tag` are functions, `wire_empty` a value
        // binding. Pin each to its Wire.pr definition, as the methods above are.
        for f in [WIRE_CAT, WIRE_TAG, WIRE_GET_TAG] {
            assert!(
                wire.contains(&format!("fn {f}(")),
                "wire builder `{f}` (names) has no `fn {f}(` in Wire.pr"
            );
        }
        // The envelope helpers a `stable` block's generated frame functions call by
        // name: `wire_is_empty` (the trailing-byte check), the value-frame
        // encode/decode, and the digest-agnostic opener the ladder dispatches with.
        // Pin each to its Wire.pr definition, as the builders above are.
        for f in [
            WIRE_IS_EMPTY,
            WIRE_ENCODE_VALUE_WITH_DIGEST,
            WIRE_DECODE_VALUE_WITH_DIGEST,
            WIRE_OPEN_VALUE_ANY,
        ] {
            assert!(
                wire.contains(&format!("fn {f}(")),
                "wire envelope helper `{f}` (names) has no `fn {f}(` in Wire.pr"
            );
        }
        assert!(
            wire.contains(&format!("let {WIRE_EMPTY} :")),
            "wire builder `{WIRE_EMPTY}` (names) has no `let {WIRE_EMPTY} :` in Wire.pr"
        );
        // The wire envelope's scheme tag is the one home of the hash scheme string
        // on the Prism side; it must match the compiler constant it mirrors, so a
        // scheme bump moves both together.
        assert!(
            wire.contains(&format!("\"{}\"", crate::core::hash::SCHEME)),
            "Wire.pr scheme tag drifted from `hash::SCHEME` ({})",
            crate::core::hash::SCHEME
        );
        let test = include_str!("../lib/std/Test.pr");
        assert!(
            test.contains(&format!("{ARBITRARY_METHOD} :")),
            "class method `{ARBITRARY_METHOD}` (names) has no signature in Test.pr"
        );
        assert!(
            test.contains(&format!("fn {QC_ARB_GEN}(")),
            "generator bridge `{QC_ARB_GEN}` (names) has no `fn {QC_ARB_GEN}(` in Test.pr"
        );
        let qc = include_str!("../lib/std/Quickcheck.pr");
        for f in [
            QC_GEN_RUN,
            QC_GEN_CONST,
            QC_GEN_BIND,
            QC_GEN_CHOOSE,
            QC_GEN_RESIZE,
        ] {
            assert!(
                qc.contains(&format!("fn {f}(")),
                "generator combinator `{f}` (names) has no `fn {f}(` in Quickcheck.pr"
            );
        }
    }

    // The `var_*` name codecs are string inverses the `erase_var` pass and the
    // handler desugar consume: `var_get`/`var_set` mint `get@x@n`/`set@x@n` that
    // `parse_var_get`/`parse_var_set` must recover, and `var_runner`/
    // `parse_var_runner` likewise. Round-trip every constructor through its
    // parser and predicate, and confirm each parser rejects a name it never
    // mints (the `#hash`-file model demands tested inverses, not comments).
    #[test]
    fn var_name_codecs_round_trip() {
        for (x, n) in [("x", 0u32), ("acc", 7), ("s", u32::MAX)] {
            let ns = n.to_string();
            let g = var_get(x, n);
            assert!(is_var_get(&g) && !is_var_set(&g) && !is_var_runner(&g));
            assert_eq!(parse_var_get(&g), Some((x, ns.as_str())));
            assert_eq!(parse_var_set(&g), None);

            let s = var_set(x, n);
            assert!(is_var_set(&s) && !is_var_get(&s) && !is_var_runner(&s));
            assert_eq!(parse_var_set(&s), Some((x, ns.as_str())));
            assert_eq!(parse_var_get(&s), None);

            let r = var_runner(n);
            assert!(is_var_runner(&r) && !is_var_get(&r) && !is_var_set(&r));
            assert_eq!(parse_var_runner(&r), Some(ns.as_str()));
        }
        // Non-matching strings: wrong prefix, and a prefixed name missing the
        // `@n` tail the constructor always appends.
        assert_eq!(parse_var_get("set@x@1"), None);
        assert_eq!(parse_var_get("get@notail"), None);
        assert_eq!(parse_var_set("plain"), None);
        assert_eq!(parse_var_runner("nope"), None);
        assert!(!is_var_get("plain") && !is_var_set("plain") && !is_var_runner("plain"));
    }

    // `parse_scoped_escape` recovers the origin of a leaked scoped effect so a
    // diagnostic can name it. Round-trip both spellings and pin that a user
    // effect (no `@`), a throw op (one `@`), and a non-numeric tail all miss.
    #[test]
    fn scoped_escape_round_trips() {
        for (eff, inst, n) in [("Ask", "f", 0u32), ("Emit", "conf", 42)] {
            let e = named_effect(eff, inst, n);
            assert_eq!(
                parse_scoped_escape(&e),
                Some(ScopedEscape::NamedInstance {
                    effect: eff,
                    instance: inst
                })
            );
        }
        for (x, n) in [("x", 0u32), ("acc", 7)] {
            let v = var_effect(x, n);
            assert_eq!(parse_scoped_escape(&v), Some(ScopedEscape::Var { name: x }));
        }
        assert_eq!(parse_scoped_escape("Ask"), None);
        assert_eq!(parse_scoped_escape(&throw_op("NotFound")), None);
        assert_eq!(parse_scoped_escape("Eff@f@x"), None);
    }

    // `parse_named_op` recovers a named handler instance's private op so a
    // capture diagnostic can name the instance. Round-trip `named_op`, and pin
    // that a bare op and a non-numeric tail miss. `is_synthesized` flags every
    // mangled or freshened name and passes a plain source identifier.
    #[test]
    fn named_op_and_synthesized_predicates() {
        for (op, inst, n) in [("get", "cell", 0u32), ("emit", "log", 3)] {
            let name = named_op(op, inst, n);
            assert_eq!(parse_named_op(&name), Some((op, inst)));
            assert!(is_synthesized(&name));
        }
        assert_eq!(parse_named_op("ask"), None);
        assert_eq!(parse_named_op("op@inst@x"), None);
        for src in ["total", "helper", "_underscore", "Color"] {
            assert!(!is_synthesized(src));
        }
        assert!(is_synthesized("t@7") && is_synthesized("reuse#s") && is_synthesized("%i$1"));
    }

    // `module_of` is the inverse of `private`: the module of a private name is
    // whatever preceded the `@`. Round-trip both a root and a nested module, and
    // pin the two boundary behaviors (an exported `.`-name and a bare root name).
    #[test]
    fn module_name_codec_round_trips() {
        for m in ["Data", "Data.Map"] {
            assert_eq!(module_of(&private(m, "helper")), m);
        }
        assert_eq!(module_of("Data.Map.insert"), "Data.Map");
        assert_eq!(module_of("bare"), "");
    }

    // `sort_prim_kind` maps each canonical primitive `Ord` instance to the tag
    // the native kernel switches on, and returns `None` (generic merge sort) for
    // anything else. Check the mapping and the fail-safe, and confirm the tags are
    // distinct so no two element types collapse onto one comparison.
    #[test]
    fn sort_prim_kind_maps_canonical_instances() {
        let mut tags = Vec::new();
        for (name, tag) in SORT_PRIM_INSTANCES {
            assert_eq!(sort_prim_kind(name), Some(*tag));
            tags.push(*tag);
        }
        tags.sort_unstable();
        tags.dedup();
        assert_eq!(
            tags.len(),
            SORT_PRIM_INSTANCES.len(),
            "sort kind tags collide"
        );
        // A real `Ord` instance with no native kernel, and a non-instance, both
        // fall back to the generic path.
        assert_eq!(sort_prim_kind("ordStr"), None);
        assert_eq!(sort_prim_kind("nope"), None);
    }

    // The sort entry points and the native-kernel instance names are string
    // contracts with the prelude, like the class methods above; pin each so a
    // prelude rename fails the build instead of silently dropping specialization.
    #[test]
    fn sort_hook_names_resolve_to_prelude_definitions() {
        let prelude = include_str!("../lib/prelude.pr");
        for f in [SORT_FN, SORT_BY_ORD_FN] {
            assert!(
                prelude.contains(&format!("fn {f}(")),
                "sort entry `{f}` (names) has no `fn {f}(` in the prelude"
            );
        }
        for (inst, _) in SORT_PRIM_INSTANCES {
            assert!(
                prelude.contains(&format!("instance {inst} :")),
                "sort instance `{inst}` (names::SORT_PRIM_INSTANCES) has no \
                 `instance {inst} :` in the prelude"
            );
        }
    }
}
