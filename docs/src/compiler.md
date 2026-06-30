# The Prism Compiler {#the-prism-compiler}

This document describes the `prism` compiler, from source text to native binary across its three backends.

## 1. Architecture {#architecture}

Compilation is a pipeline from source text to a native binary. Each phase is a total function over the program, and there are no per-module artifacts.

| Phase                                                 | Role                                                                                                                          | Owner                                      |
| ----------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------ |
| [Lex](#lexing-and-layout)                             | text to tokens, then layout                                                                                                   | `src/lex/`                                 |
| [Parse](#parsing)                                     | tokens to surface AST                                                                                                         | `src/parse/`, `src/syntax/grammar.lalrpop` |
| [Resolve](#name-resolution-and-modules)               | load imports, canonicalize names, merge                                                                                       | `src/resolve/`                             |
| [Desugar](#desugaring)                                | surface sugar to core surface                                                                                                 | `src/syntax/desugar/`                      |
| [Check](#type-and-effect-inference)                   | type and effect inference                                                                                                     | `src/tc/`                                  |
| Elaborate                                             | surface to [CBPV / ANF core](#the-core-calculus) (match compilation, [pattern-match compilation](#pattern-match-compilation)) | `src/core/elaborate/`                      |
| [Optimize](#optimization)                             | Core-to-Core passes, in two stages around effect lowering                                                                     | `src/core/opt/`                            |
| [Effect lower](#effect-lowering)                      | remove handlers and operations                                                                                                | `src/core/effect_lower/`                   |
| [Reference count](#reference-counting-and-fbip-reuse) | insert `dup`/`drop`, then reuse                                                                                               | `src/core/fbip.rs`                         |
| [Codegen](#backends)                                  | core to interpreter, LLVM, or MLIR                                                                                            | `src/eval/`, `src/codegen/`                |

The driver (`src/driver/`) exposes these as subcommands: a bare `prism <file.pr>` compiles a single file to a native binary named after the source (override with `-o`), `prism build` compiles the enclosing project (the nearest `prism.toml`) and fails outside one, `prism run` interprets, `prism check` runs the front end only, `prism fmt` formats, and `prism dump <phase>` prints an intermediate form, where `<phase>` is `tokens`, `ast`, `types`, `core`, `core-json` (the core as a JSON tree the Lean model reads, covered under [verification](#verification)), `core-hash` (a content-addressed hash of each definition's elaborated core, `src/core/hash.rs`), `fbip` (core after reference-count insertion and reuse), `lowered` (after effect lowering), `llvm`, or `mlir` (the last gated on the MLIR backend feature).

A project build writes its output rustc-style into a `target/` directory at the package root (the binary and its codegen intermediates) rather than dropping the binary in the current directory; an explicit `-o`/`--out` still wins, and single-file `prism <file.pr>` builds are unaffected. `prism clean` removes that `target/` directory, resolved at the nearest enclosing `prism.toml` (or the given path outside a project); an already-absent `target/` is a no-op success.

The Core-to-Core optimizer (see [optimization](#optimization)) is driven from the driver too: `-O`/`--opt` selects an optimization level (default `-O1`) and `--passes` supplies an explicit pass list, the two being mutually exclusive. `--mlir` selects the MLIR backend over the default LLVM one.

Every phase returns its result into one `thiserror` enum (`src/error.rs`) whose variants are the phases that can fail (lex, parse, resolve, type, codegen, runtime, IO) plus an `Ice` variant for an internal invariant violation, and a diagnostic is rendered with a source caret through `ariadne`, mapping spans back through the prepended prelude to the user's own text. An internal invariant is reported by constructing an `Ice` (around sixty such sites across elaboration, checking, effect lowering, and codegen, the last through a non-panicking `ice` helper that records the first message and returns a poison value so emission stays total) rather than by panicking, so a malformed source program always yields a diagnostic. The crate forbids `unsafe` (`unsafe_code = "forbid"`) and contains none, and of the handful of `panic!`s in the tree all but one are test assertions, the exception being a `PRISM_CORE_LINT`-gated sanity check on the compiler's own IR (see [lint, telemetry, and parity](#lint-telemetry-and-parity)).

## 2. Lexing and Layout {#lexing-and-layout}

The lexer produces a token stream and trivia (comments and spacing) that the formatter uses to reproduce source faithfully. An interpolated string is lexed by re-lexing each `{ ... }` hole at its absolute source offset, so spans inside holes remain accurate. A layout pass then rewrites the stream, inserting virtual block-open, block-close, and separator tokens according to the offside rule of the [layout](./spec.md#layout) specification, which the grammar consumes as ordinary terminals.

## 3. Parsing {#parsing}

The grammar is an LALR(1) grammar in LALRPOP (`src/syntax/grammar.lalrpop`), with two entry points: a whole program, and a single expression for the REPL. Parsing produces the surface AST of `src/syntax/ast.rs`. Type and parse errors are rendered with a source caret.

## 4. Name Resolution and Modules {#name-resolution-and-modules}

Resolution loads every transitively imported module, rewrites each top-level definition to a globally unique canonical symbol (an export as `Data.Map.insert`, a private as `Data.Map@helper`), resolves qualified and re-exported references to those symbols, and merges all modules into one flat program. This is a whole-program renamer: the entire program is checked and compiled from source on every build. The canonical-symbol scheme makes the merge sound, since two modules can export the same short name without collision.

Moving to incremental, per-module compilation is planned but not implemented; the interprocedural analyses below (effect lowering, borrow signatures, instance coherence) are what make it nontrivial, since each crosses module boundaries.

## 5. Desugaring {#desugaring}

Desugaring rewrites surface sugar into the smaller core-surface language the checker and elaborator handle (`src/syntax/desugar/`), each rule shown as surface form and the form it lowers to.

The surface tree is parameterized by its compilation _phase_ (`src/syntax/ast.rs`). An `Expr<P>` holds its sugar-only forms, its parse-time markers, and its surface-only handler clauses in fields whose types are associated types of the phase `P`: in the `Surface` phase those are the real sugar payloads, and in the `Core` phase, desugar's output, they are the uninhabited type `Never`. Because `Never` has no values, a sugar node cannot be constructed in the core phase at all, so a missed desugaring is a type error in the compiler rather than a runtime `unreachable!`, and every later pass over `Expr<Core>` is statically excused from matching the sugar cases.

Function composition lowers to a lambda, kept as sugar only so the operator survives formatting.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/compose_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/compose_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

An arithmetic sequence lowers to a prelude enumeration call.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/range_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/range_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A list comprehension (and the statement `for`) lowers to a stream (a producer performing the `Emit` effect, see [effect lowering](#effect-lowering)) that emits each surviving element, collected with `scollect` (a stream consumer that gathers the emissions into a list), so it fuses with no intermediate list.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/comp_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/comp_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A record update rebuilds the constructor along the named fields; on a uniquely owned value the rebuild is the in-place write of [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse).

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/record_update_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/record_update_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

`deriving (Lens)` synthesizes a getter and a functional setter per field.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/lens_derive.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/lens_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

The failure fallback `a ?? b` runs `a` under a `Fail` handler that yields `b` if `a` fails.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/default_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/default_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A method call `e.m(args)` is uniform-function-call sugar: the receiver becomes the first argument.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/ufcs_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/ufcs_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A string with interpolation holes becomes a concatenation of its literal pieces and the `show` of each hole.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/interp_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/interp_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

`try`/`catch`/`throw` is subtractive handler sugar: one nested `final ctl` clause (the non-resumable handler clause of [clause sugar](./spec.md#clause-sugar)) per arm, each discharging one error label.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/trycatch_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/trycatch_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

`transact body else fallback` snapshots every live `var`, runs the body under a `Fail` handler, and restores the snapshots on failure, so a failed attempt leaves observable state unchanged.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/transact.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/transact_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

Optional chaining `a?.b` is `force(a).b`, where `force` raises `fail()` on `None`, so a path short-circuits at the first `None` and an enclosing `??` supplies the default.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/optionals.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/optchain_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A `with f <- handler { .. }` block binds a first-class handler instance over a fresh private effect; `f.op(..)` targets it by name.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/with_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/with_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A trailing block argument is appended as the call's last argument.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/trailingblock_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/trailingblock_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A bidirectional pattern synonym desugars to a `view` call in match position and a `make` call in expression position.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/pattern_syn_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/pattern_syn_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

A nested path update rebuilds the single-constructor spine (the chain of nested constructor cells) along the path.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/pathupdate_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/pathupdate_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

`deriving (Eq, Ord, Show)` generates one structural instance per class.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/deriving_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/deriving_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

The postfix `e?` unwraps `Ok` and short-circuits on `Err`.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/postfix_try_sugar.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/postfix_try_desugared.txt}}
```

{{#endtab }}

{{#endtabs }}

The `var` desugaring is shown with full Source / Desugared / Core stage tabs in [local mutation](./spec.md#local-mutation); default and named arguments lower to positional ones in the same pass.

## 6. Type and Effect Inference {#type-and-effect-inference}

Type inference is the bidirectional, higher-rank algorithm of [Dunfield & Krishnaswami (2013)](bibliography.md#dunfield-krishnaswami-2013) (`src/tc/`); the surface rules are in [types and kinds](./spec.md#types-and-kinds). Type classes elaborate to dictionary-passing: a constraint becomes a hidden parameter, resolved to a global instance, a passed dictionary, or a projection of a superclass dictionary.

Instances are global, but each records its defining module, so coherence is checked by provenance (`src/tc/classes.rs`). Resolution is coherent: for each `(class, type-head)` there is exactly one canonical instance, and implicit resolution always selects it. A single instance for a head is canonical automatically. When two or more instances share a head, one must be designated with a top-level `canonical Class(Head) = name` declaration (see [coherence and resolution](./spec.md#coherence-and-resolution)). An undesignated overlap is a hard error reported at definition, naming the candidates and their modules, with a source caret when they point into the program being compiled. An orphan instance (defined apart from both its class and its head type) is reported as a warning. An explicit override is written at the use site as a trailing `using` argument, `f(args, using name)`, which changes nothing else's resolution.

Indexing (`a[i]`, `a[i] := v`) is resolved the same way the `Show` and `^` lowerings are, by type-directed dispatch at elaboration: the checker records each sub-expression's type in a span-keyed table, and the elaborator reads the receiver's head type back and emits the matching builtin or accessor (`Array` to `at_array`/`array_set`, `HashMap` to `at_hashmap`/`hm_insert`, `String` to `at_byte`, `List` to `at_list`). A receiver whose type is still an unsolved existential when first synthesized (a `var` indexed before its initializer fixes its state type) defers to one pass at the end of the declaration, after the initializer has constrained it. No class or type-system extension is involved, so concrete indexing ships today; the desugar target is `index`/`index_set`, leaving room for a user-extensible `Index` class later.

Effect-row inference is _principal_: each declaration infers its most general row from its body alone. The row unifier in `src/tc/subsume.rs` discovers every label on its own (a _row_ is a function's effect set; see [types and kinds](./spec.md#types-and-kinds)) from direct performs, applied effect-carrying callees, builtin rows, and `mask`. At a call it adds the callee's row to the caller's _ambient row_ (the effect set accumulated for the body so far), and a handler removes the operations it discharges. The row is the single source of truth: there is no separate set-pass seed and no subset reconciliation against one.

A syntactic _set-pass_ (a pass that computes a _set_ of operation labels by a call-graph fixpoint, `src/types/effects.rs`) still runs, but only to feed the syntactic purity checks: it confirms a `konst` declaration and a declared-pure instance method perform nothing. It no longer seeds the row. After lowering, `reconcile_effects` checks the operations the lowered code actually performs against the inferred row, and the interpreter parity oracle (see [verification](#verification)) is the final backstop. Effect lowering computes its own per-function _latent_ operation set by an independent call-graph fixpoint (see [effect lowering](#effect-lowering)), so the two phases no longer share the set-pass result.

## 7. The Core Calculus {#the-core-calculus}

Elaboration lowers the surface language to a call-by-push-value core ([Levy, 2004](bibliography.md#levy-2004); `src/core/cbpv.rs`) in A-normal form. CBPV separates _values_, which are inert, from _computations_, which can be run; `Thunk` freezes a computation into a value and `Force` runs it. A-normal form names every intermediate result with a `Bind`, making evaluation order explicit and each operation and allocation syntactically distinguished, enabling the later effect and reference-counting passes. The grammar below is the elaborated core; the reference-count pass (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)) later adds `dup`, `drop`, and reuse nodes to it.

```text
{{#include ../examples/cbpv-grammar.txt}}
```

For example, a constructor applied to a call elaborates so the call is named before the constructor is built:

```text
{{#include ../examples/anf-example.txt}}
```

This calculus is modeled in Lean 4 ([de Moura & Ullrich, 2021](bibliography.md#demoura-ullrich-2021)): `models/Prism.lean` mirrors the core one variant at a time with a substitution small-step relation, on top of which the model adds an executable abstract machine that mirrors the interpreter and is proved to agree with it. The chapter on [verification](#verification) describes the model and how it is run as a third differential oracle.

## 8. Pattern-Match Compilation {#pattern-match-compilation}

A `match` is compiled to a decision tree (`src/core/elaborate/match_compile.rs`). The arms form a matrix whose rows are arms and columns are argument positions. The compiler selects a column, partitions the arms by the head of that column's patterns, and emits a test: a `Case` on the constructor tag of the scrutinee (the value being matched) for a constructor column, or a chain of equality tests for a scalar column. Wildcard rows form a default sub-matrix shared by the branches that fall through. A guarded arm compiles to a conditional that re-enters the remaining arms when the guard fails. Exhaustiveness, proven by the checker (see [patterns](./spec.md#patterns)), guarantees every scrutinee reaches an arm.

## 9. Effect Lowering {#effect-lowering}

Effect lowering compiles away the `Handle`, `Do`, and `Mask` nodes of the core. An operation is delimited control (an effect suspended and resumed within a handler's scope): `Handle` is the delimiter, and the resumption `k` is the continuation captured between a perform site and its handler (see [effects and handlers](./spec.md#effects-and-handlers)). Lowering is a cascade of five strategies tried in a fixed order, each of which either lowers the whole program and succeeds or declines and returns `None`: a trivial **pure** tier when no effect construct remains, **evidence passing**, **state threading and stream fusion**, **local monadification**, and the **free-monad fallback**. They are five compilations of that one mechanism, differing in how much of `k` they make manifest, from nothing to a heap-allocated tree; the compiler takes the first that applies, so it reifies as little of the continuation as the program allows. A check then confirms no effect construct survives.

Two erasure pre-passes run before the strategy cascade, each recognizing a statically fixed handler shape and rewriting it to direct code, leaving everything else for the strategies. **Var erasure** (`src/core/effect_lower/erase_var.rs`) rewrites an escape-checked local `var` (a closed two-operation `State` handler, see [local mutation](./spec.md#local-mutation)) to a mutable cell: `get` becomes a cell read, `set` a cell write, and the block is wrapped in a fresh-cell allocation. It is sound exactly because the escape analysis proved the var's continuation is never resumed more than once, so the shared cell and pure-state copies agree; a multishot use disables it. **Control erasure** (`src/core/effect_lower/erase_control.rs`) rewrites the internal `break`/`continue`/`return` effects (see [imperative control flow](./spec.md#imperative-control-flow)), whose `final ctl` handlers have fixed templates, back to direct control flow. It runs after var erasure, so a pure imperative loop has lost all of its effect operations by the time the cascade classifies it and falls into the trivial **pure** path (no effect constructs remain), compiling to a `musttail` loop with no per-iteration allocation.

**Evidence passing** is the fast path for tail-resumptive handlers (every clause calls `k` exactly once, in tail position, so the continuation need never be captured at all). Each operation is assigned a stable numeric id by sorting the operation names, and a call-graph fixpoint computes each function's _latent_ set, the operations still performed anywhere in its call-graph closure. An effectful function then gains one extra parameter per latent operation, `ev@<id>`, a thunk holding the active handler clause. Performing an operation forces its evidence thunk directly; a `handle` binds fresh evidence for its body's latent operations; and every call site appends the callee's evidence, in ascending id order, so the convention is positional and stable. A first-class thunk that escapes carries evidence parameters for its own latent operations, threaded at each force site. No continuation is reified and no per-operation cell is allocated. What evidence to thread where is computed by an interprocedural least-fixpoint flow analysis (`src/core/effect_lower/flow.rs`) that derives, for every function, the operation signature of the thunk it returns and of each thunk-valued parameter.

**State threading and stream fusion** is the path for a uniform single-operation handler, the shape a stream consumer takes: a handler that folds every `emit` into an accumulator. Such a handler clause is rewritten to an accumulator transformer `\acc -> acc'`, and the producer it wraps becomes a loop that threads the accumulator through each emission instead of allocating a value per step. A consumer that can stop early, like `stake`, returns a two-state tag (continue or done) that the producer checks, so the loop exits without unwinding. This reifies one small tag cell per early-terminating handler and, like evidence passing, no free-monad cell, so a `smap`/`skeep`/`stake`/`ssum` pipeline allocates neither an intermediate list nor a per-operation cell.

```prism
{{#include ../examples/streams.pr}}
```

**The free-monad fallback** applies when an effect escapes static tracking: buried in data, dynamically applied, masked, genuinely multishot (a clause that resumes `k` more than once), or self-referential (a handler whose own body performs the effect it handles). A multishot handler forces this path because the two fast paths erase `k`, and a continuation invoked more than once must exist as a reusable value. Here the delimited continuation is reified in full: each computation becomes a tree of `EPure` and `EOp` cells threaded by `ebind` (shown below), and the continuation each `EOp` still owes is an explicit field a clause can hold, drop, or apply repeatedly. That continuation is held as a _type-aligned queue_ (the Freer representation, [Kiselyov & Ishii, 2015](bibliography.md#kiselyov-ishii-2015)): a persistent catenable tree of Kleisli arrows whose append (`snoc`, one `ebind`) and join (`concat`, the splice at a forwarded operation) are O(1), and whose `uncons` re-associates the left spine, so a continuation extended by repeated `ebind` drains in amortized O(1) per step rather than the quadratic re-association a trampoline would redo on every bounce. The tree is never mutated, only rebuilt sharing its leaves, so a captured continuation stays cloneable for a multishot resume. A `handle` becomes a generated driver function that case-dispatches the reified tree: an `EPure` runs the return clause, an `EOp` whose id the handler names and whose skip count is zero runs the matching clause, and any other `EOp` is re-emitted outward with a re-entry continuation, which is how an inner handler forwards an operation it does not catch. An `EOp` carries a `skip` field, its mask depth, the number of matching handlers it must still bypass; a `mask` driver increments it and the handler driver only fires when it is zero. This is exactly the interpreter's dispatch (see [backends](#backends)), so the two agree by construction. Each `EOp` allocation bumps the `PRISM_EFFOP_STATS` counter, so the fallback's cost is observable, and a default-on warning (silenceable with `PRISM_QUIET`) names the functions that lost fusion and the cause when a program takes this path, so a pipeline meant to stay fused can be steered back. The generated drivers are closed by construction: a per-handler driver takes exactly its clauses' captured free variables as parameters, and the fixed-binder templates (`ebind`, the mask drivers) use a reserved binder band and never nest, so a binder cannot capture a free occurrence. Lowering is kept as local as possible, the **local monadification** tier above the whole-program fallback: when an effectful thunk escapes, only the connected component entangled with it (closed over the call graph, but leaving pure closure-inert helpers shared, and over shared operations) is converted to the free-monad form, while unrelated functions stay on their fused paths, provided the component's operations are disjoint from the rest; when the split is not clean lowering falls back to converting every effectful function together. A convention-boundary check, run in both modes, validates the split and turns a missed monadic/direct boundary into a compile-time internal error.

**Constant-stack driving** changes how a closed handler on this fallback is run, not what it reifies. By default such a handler is driven by a single self-tail-recursive loop, `{n}@region`, rather than a pair of mutually recursive driver functions: the loop case-dispatches the same `EPure`/`EOp` tree but re-enters itself by a `musttail` self-call on the resumed continuation, so an iterative or deeply nested resumption runs in constant native stack where the mutually recursive driver grew it per step. Two clause shapes qualify. A tail-resumptive clause (every `resume` is the head of a tail application) re-drives the operation's continuation queue with `qApply`. A function-answer state clause, the parameter-passing pattern whose answer is a function `S -> A` (`rd(u, r) => \s -> r(s)(s)`, `wr(v, r) => \s -> r(())(v)`) applied once at the handler's use site, threads the state in an accumulator parameter and folds that use-site application into the loop's entry, so the pending-apply chain that would otherwise grow the stack per iteration lives in the accumulator instead. The reification is unchanged, so the per-operation `EOp` cost stays and the only zero-cell routes remain the evidence and state paths above; the gain is purely that a parameter-passing loop no longer overflows (the bounded-stack performance gate pins a million-iteration `State` loop completing in a 2 MB stack). An open handler, a multishot or escaping resume, or any clause outside these shapes keeps the mutually recursive driver, whose `qApply` the loop reuses, so the free-monad machinery is the substrate it drives rather than a thing it replaces. This is on by default and reverts under `PRISM_NATIVE_EFFECTS=0`; the interpreter oracle's whole-corpus parity holds byte-for-byte either way.

```text
{{#include ../examples/free-monad.txt}}
```

The example below exercises this path: an inner handler catches `Log` and forwards `raise` outward to an `Exn` handler, the two effects interleaving across the nesting.

```prism
{{#include ../examples/eff_forward.pr}}
```

The fallback reifies one cell per pending operation, so its cost is proportional to the operations in flight; the fast paths avoid it where they apply.

## 10. Reference Counting and FBIP Reuse {#reference-counting-and-fbip-reuse}

Reference counting runs after effect lowering, over the handler-free core, so it counts evidence parameters and any reified cells as ordinary values. Memory is managed by Perceus-style reference counting ([Reinking et al., 2021](bibliography.md#reinking-2021); `src/core/fbip.rs`): every parameter and binding is owned and consumed exactly once on every control-flow path from its binding to the end of its scope; a second use inserts a `dup` and an unused value inserts a `drop`. Perceus places these operations precisely rather than conservatively at scope exit, which frees a cell at the earliest point the reuse pass below can claim it. Closure captures are borrowed (read without being consumed) and duplicated before a consuming use, as is a `borrow` parameter (see [declarations and programs](./spec.md#declarations-and-programs)). The parameters a function borrows are recorded as a per-function bit vector, its interprocedural _borrow signature_, which every caller consults to place its `dup`/`drop` correctly. Because that signature crosses call sites, it is one of the analyses that complicates the move to separate compilation (see [name resolution and modules](#name-resolution-and-modules)).

The reuse pass then turns drops into in-place updates. When a uniquely owned scrutinee is dropped and the continuation rebuilds a constructor of the same or smaller size, the `drop` becomes a scoped reuse node, `WithReuse { token, freed, body }`: it frees the cell once and binds a _reuse token_ over the continuation, and the rebuild spends that token with an in-place `Reuse(token, ctor)`, so `map` and tree rebuilds mutate the spine in place. The token is a binder that only a `Reuse` may name, and the rewrite spends it on every control path or declines wholesale (keeping the safe no-reuse body), so freeing a cell once and spending its token at exactly one allocation are well-formedness properties of the term rather than a condition checked afterward.

An independent verifier re-checks that output. `fbip::balanced` re-simulates the inserted `dup`, `drop`, and reuse operations as a linear-token machine: each owned binding starts with one token, a `dup` adds one and a `drop` or consuming use removes one, a use may never drive the count below zero, every binding must reach zero before leaving scope, the two arms of a branch must agree, and a `WithReuse` grants its token exactly one credit the body must spend. It runs over the reference-counted core on every interpreter entry and across the whole example and test corpus, so an under-`dup`, an over-`drop`, or an unbalanced branch left by the insertion pass surfaces as an internal error rather than a leak or a double free at run time. Core Lint adds the dual direction under `PRISM_CORE_LINT` (see [lint, telemetry, and parity](#lint-telemetry-and-parity)): it rejects a reuse token spent more than once on any path, the over-spend the balance check does not see.

The `fip`/`fbip` annotations (see [declarations and programs](./spec.md#declarations-and-programs)) are the fully-in-place discipline of [Lorenzen et al. (2023)](bibliography.md#lorenzen-fp2-2023), here static checks layered on these passes. `fbip` proves zero fresh allocation and a call-graph closure over annotated, allocation-free callees. `fip` adds two further properties: linearity (each owned binding is consumed at most once, checked on the source term, with scalars exempt because adjusting the count of an unboxed word costs nothing) and bounded stack. The tail-call and tail-modulo-cons (a tail call whose result is wrapped in one constructor) classification (`src/core/tailrec.rs`) is shared with codegen, so an accepted `fip` function always lowers to a loop; acceptance never outruns what the backend emits.

```prism
{{#include ../examples/fip_list.pr}}
```

## 11. Backends {#backends}

Prism has three backends over one core: a tree-walking interpreter that is the reference oracle, and two native backends that must match it byte for byte. The native backends share a single generic emitter, so the differences below are narrow.

### 11.1 The Interpreter {#the-interpreter}

The tree-walking interpreter (`src/eval/`) is a flat CEK (control, environment, continuation-stack) machine. Pending work lives on an explicit heap stack of frames rather than the host call stack, so object-program recursion never overflows it. A frame is one of: `Bind` (await a result, then continue with the rest of a sequence), `Args` (await a function before applying it), `Handle` (an installed handler), `Mask` (a masking frame), and `Restore` (unwind a name binding; a `Restore` already on top marks tail position, which is where the machine recognizes a tail call).

This machine makes the delimited continuation of [effects and handlers](./spec.md#effects-and-handlers) concrete: performing an operation searches the frame stack outward for a matching `Handle`, decrementing the skip count past masked frames, and the _captured continuation_ is exactly the slice of frames between the `do` and that handler, the handler included. Resuming pushes a clone of that slice back onto the stack, so the same resumption can be pushed again, which makes `k` multishot. The native backends realize this same frame stack in the runtime as a chain of counted frame cells (`prism_rt.c`) linked by a `next` field, one cell per `Bind`, `Handle`, and `Mask` frame; resuming splices a clone of the delimited slice onto the current chain with `prism_kont_splice`, which copies and relinks the slice in two iterative passes, so a deep continuation is captured and re-entered in O(1) C stack regardless of its depth, and an abandoned continuation is freed through the same iterative refcount worklist (see [reference counting](#reference-counting)). The free-monad backend reifies this same frame slice as the `k` closure of an `EOp` (see [effect lowering](#effect-lowering)); evidence passing never materializes it.

### 11.2 The Shared Emitter {#the-shared-emitter}

Both native backends drive one generic emitter (`src/codegen/emit.rs`) behind an `Isa` trait that abstracts instruction emission, so they differ only in instruction spelling. The emitter owns case dispatch, constructor allocation and reuse, and tail-call lowering: a self-tail call of equal arity becomes a `musttail` loop, and a constructor- or accumulator-shaped tail call (one whose result feeds a constructor or an integer accumulator) becomes a destination-passing loop, one that writes its result into an address passed as a hidden parameter rather than returning it, using the same classification the `fip` check reads (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)).

### 11.3 LLVM {#llvm}

The LLVM backend (`src/codegen/llvm.rs`) implements `Isa` over inkwell, emitting LLVM IR that `clang` compiles and links against the runtime. This is the default native path.

Prism runs no LLVM optimization passes itself: it verifies the module, writes bitcode, and hands the rest to `clang -O2 -flto=thin`, compiling the emitted bitcode and the C runtime in one invocation so ThinLTO inlines the runtime into the generated code. Every emitted function carries `nounwind` (Prism has no exceptions and this backend emits no invokes or landingpads), which lets the `-O2` pipeline drop unwind tables and treat each call as non-throwing. Three knobs tune this last step, all distinct from the Core-to-Core `-O` of [optimization](#optimization): `--backend-opt <0|1|2|3|s|z>` (or the `PRISM_BACKEND_OPT` env var) sets the `clang -O` level, defaulting to `2`; `PRISM_CC` picks the compiler (default `clang`); and `PRISM_CC_FLAGS` appends arbitrary flags after the defaults, so a trailing `-O0` wins or `-march=native`/`-g` can be added. ThinLTO stays on at every level, since it is what folds the runtime into the program.

### 11.4 MLIR {#mlir}

The MLIR backend (`src/codegen/mlir.rs`) implements the same `Isa` by writing textual MLIR in the `llvm` dialect. Sharing the emitter makes its output byte-identical to the LLVM backend's, which the parity gate (see [verification](#verification)) enforces.

### 11.5 WebAssembly {#webassembly}

The compiler front end and the interpreter also compile to WebAssembly (`src/wasm.rs`), so Prism type-checks and runs in the browser. This target hosts the interpreter, not the native code generators; the LLVM and MLIR backends are absent there.

## 12. The Runtime {#the-runtime}

The C runtime (`runtime/prism_rt.c`) is linked with the code each backend emits. It assumes an LP64 target (64-bit pointers and `long`) and uses `mimalloc` when available. The data representation below is shared by the backends and the runtime.

### 12.1 Value Representation {#value-representation}

Every value occupies one 64-bit word, tagged by its low bit so that a single representation serves both scalars and pointers under polymorphism.

```text
{{#include ../examples/value-repr.txt}}
```

A float does not fit the immediate scheme, so it is _boxed_: wrapped in a one-field cell holding the raw double bits, which are read back out (unboxed) at every float operation. Boxing makes a float field self-describing, so the collector frees it without interpreting its payload.

### 12.2 Cell Layout {#cell-layout}

A heap cell is a three-word header followed by its fields.

```text
{{#include ../examples/cell-layout.txt}}
```

Constructor tags follow declaration order (for `Option(a) = None | Some(a)`, `None` is 0 and `Some` is 1). Two tag values are reserved, `0x53545200` for a string and `0x42494700` for a bignum (see [integers](#integers)), marking cells whose payload is raw bytes or limbs rather than child values; the collector and the reuse pass (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)) read the tag to avoid recursing into them.

Every cell allocation routes its size through one overflow-checked chokepoint, `prism_cell_bytes`, which rejects a negative field count and aborts (via `__builtin_add_overflow`/`__builtin_mul_overflow`) if the header-plus-payload word count, or its conversion to bytes, would overflow `size_t`, so a corrupt or oversized arity can never produce an undersized allocation.

### 12.3 Reference Counting {#reference-counting}

`prism_rc_inc` and `prism_rc_dec` take the raw value word and return immediately on an immediate or unit, so counting is a no-op on non-cell values. Decrement to a nonzero count just decrements. Decrement to zero frees the cell, but freeing is _iterative_, not recursive: the dead cell's now-zero refcount word is reused as a link field in an intrusive worklist of cells pending free, so a structure of any depth is reclaimed in constant auxiliary space without growing the C stack. A string or bignum tag short-circuits the child traversal.

### 12.4 In-Place Reuse {#in-place-reuse}

The reuse pass of [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse) emits two runtime calls. `prism_reuse_token(v)` inspects a cell about to be dropped: if it is uniquely owned (refcount 1), it drops the cell's children and returns the shell as a token, leaving the live-cell count untouched; otherwise it decrements and returns null. `prism_reuse_alloc(token, n)` overwrites the token's header for the new constructor when the token is non-null, and falls back to a fresh allocation when it is null. A uniquely owned spine is therefore mutated in place, and a shared one transparently copies.

### 12.5 Integers {#integers}

A small integer is an immediate, `(n << 1) | 1`. An operation whose fixed-width result would overflow promotes to a _bignum_: a cell tagged `0x42494700` storing the value in sign-magnitude form (sign and magnitude kept separate). Its header word is a signed limb count whose sign is the value's sign; the magnitude follows as that many little-endian `u64` limbs (base-2^64 digits) with no leading zero limb. Zero is a count of zero with no limbs. Each surface arithmetic operation takes a fast path on two immediates with a checked-overflow primitive and falls back to magnitude routines (add, subtract, multiply, and a shift-subtract long division) that renormalize the result, demoting back to an immediate when it again fits. The surface `Int` is this unbounded integer. The `I64` and `U64` lanes are raw machine words and wrap rather than promote.

### 12.6 Strings {#strings}

A string is a cell tagged `0x53545200` whose field words hold its UTF-8 bytes inline, length-prefixed by the arity word and NUL-terminated for C interop. Each string the program builds, including a literal at each use, is a counted cell, so the leak counter (see [instrumentation](#instrumentation)) accounts for strings like any other allocation. Two indexing families coexist: `char_at`, `substring`, and `str_len` work in Unicode codepoints, walking the UTF-8 encoding (and so are O(n)), while `byte_at` and `byte_len` give O(1) raw-byte access for a scanner or hash.

### 12.7 Instrumentation {#instrumentation}

Three environment-gated counters report to stderr at exit, leaving stdout (the parity-checked channel) untouched. `PRISM_CHECK_LEAKS` reports the live-cell balance, which a clean run drives to zero. `PRISM_REUSE_STATS` reports how many cells the reuse pass rewrote in place. `PRISM_EFFOP_STATS` reports how many free-monad `EOp` cells were allocated, which the performance gate asserts is zero on the fusion corpus.

### 12.8 Growable Arrays {#growable-arrays}

The growable `Array(a)` (see [the standard prelude](./spec.md#the-standard-prelude)) is an ordinary cell, `{ rc, tag 0, arity cap+1, len, elem0 .. }`, with the length word stored odd-tagged (low bit set, so the collector skips it as an immediate per [value representation](#value-representation)) and unused slots held at zero. Because it is a normal cell, reference counting recurses into its live elements with no special case. Every array operation borrows its array argument. `array_get` returns a counted element; `array_set`, `array_push`, and `array_pop` write in place when the array is uniquely owned (refcount 1) and copy otherwise, so functional array code runs as mutation exactly when ownership permits. `array_push` doubles the capacity when full, making appends amortized O(1). The prelude's `HashMap` is a separate-chaining hash table layered on this array, with an FNV-1a hash written in Prism (so iteration order is a deterministic function of the inserts); it is library code, not a runtime primitive.

### 12.9 Primitive Sort {#primitive-sort}

`sort` is a runtime primitive (`prism_sort_prim`) that borrows a list and returns it sorted, dispatched on a key kind. Arbitrary-precision `Int` keys use a bignum-aware stable bottom-up merge sort, ping-ponging between two buffers; fixed-width keys use a radix sort over a derived key. When the input spine is uniquely owned, the sorted heads are written back into the existing cells with no allocation; a shared spine is copied with its elements shared. The `Cons` and `Nil` tags are read off the input spine, so no list layout is baked into the runtime.

### 12.10 Input, Output, and Randomness {#input-output-and-randomness}

The runtime provides the impure primitives. The nondeterministic _inputs_ are no longer untracked builtins: they are the raw `prim_*` calls (`prim_read_int`, `prim_read_line`, `prim_read_file`, `prim_file_exists`, `prim_rand`, `prim_getenv`, `prim_args_count`, `prim_arg`) that the prelude reaches only from the handler arms of the [capability effects and IO](./spec.md#capability-effects-and-io). The surface names `read_int`/`read_line` read stdin, `read_file`/`file_exists` read files, `getenv` reads the environment, `rand` draws a random word, and `args_count`/`arg` (wrapped by the prelude's `args`) read the command line; each is a prelude wrapper that performs the matching `Console`/`FileSystem`/`Random`/`Env` operation, which the default `run_io` world handler discharges by calling the corresponding `prim_*`. The output primitives stay direct builtins carrying `! {IO}`: `write_file`, `append_file`, and `remove_file` operate on files, `system` runs a shell command and returns its exit code, and `eprint`/`eprintln` write to stderr, leaving the parity-checked stdout untouched. Randomness is a SplitMix64 generator: `prim_rand` advances it and `srand` seeds it, so a seeded run is deterministic and reproducible. Because these touch the world, the parity harness (see [verification](#verification)) runs only the programs that avoid them.

## 13. Verification {#verification}

Several gates hold the implementation to its claims. The parity harness (`tests/parity.rs`) is differential testing with the interpreter as the reference: it runs every example on the interpreter and each native backend and asserts byte-identical output, and with `PRISM_CHECK_LEAKS` set, zero leaked cells.

The performance gate (`tests/perf_gate.rs`) asserts that the optimizations actually fire, so a regression that leaves output unchanged is still caught. With `PRISM_EFFOP_STATS` set, it requires zero free-monad cells allocated on the fusion corpus (the stream and multi-handler programs such as `streams.pr`), confirming that the evidence and state paths of [effect lowering](#effect-lowering) reify nothing. It also pins local monadification: a program that pairs an escaping effectful closure with an unrelated fused pipeline must allocate no more cells than the escape alone, so the pipeline stays fused despite the escape. That check is anti-vacuous: it first asserts the escaping component does allocate a nonzero number of cells, so the gate cannot pass by everything being zero. An asymptotic check runs the constant-space programs at n=1000 and n=10000 and fails if allocation grows with n, and a set of constant-stack checks run a pure tail recursion, a `var` loop, the internal control effects, and a parameter-passing `State` loop at a million iterations each under a 2 MB stack (`ulimit -s`), so a lost `musttail` or a regression into the free monad overflows the stack and fails the test. With `PRISM_REUSE_STATS` set, it requires in-place reuse to fire on the reuse corpus (`list.pr`), confirming the reuse pass of [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse) rewrites drops into in-place updates. A coverage gate (`optimization_coverage` in `tests/snapshots.rs`) recomputes the lowering strategy each corpus program takes, by the same decision the compiler makes, and fails if any named fast path (`evidence`, `state-fusion`, `local-partial`) is left with no live witness, so silently losing a whole optimization is caught even when output and counters are unchanged.

A layout test (`src/codegen/emit.rs`) pins the cell ABI: it reads the runtime source at compile time, parses the `#define`s for the tag offset, the header size, and the reserved string and bignum tags, and asserts each equals the constant the code generator emits against, so the runtime and the backends cannot drift apart without failing the build.

A static bar is enforced across the tree. It carries no `todo!`, `unimplemented!`, `FIXME`, or `allow(dead_code)` markers (a CI grep rejects them) and no `unsafe`; `cargo clippy` runs clean with the `pedantic`, `nursery`, and `cargo` groups as warnings under `-D warnings`; and the C runtime compiles under `-Werror` with a broad warning set plus `clang-tidy`. Continuous integration (`.github/workflows/ci.yml`) runs every gate on every commit on every branch: formatting, the two lint passes, the full test suite (the parity and performance gates included), a re-run of the native parity corpus with the C runtime built under AddressSanitizer and UndefinedBehaviorSanitizer, the formatter checking its own corpus (`prism fmt --check`), a `PRISM_CORE_LINT` compile of every example, the WebAssembly playground (lint and type-check), the MLIR backend's parity test, and the Lean model (`lake build --wfail`).

### 13.1 The Lean Model {#the-lean-model}

Beyond the differential gates, the core calculus is mechanized in Lean 4 (the `models/` directory, built with `lake`). `Prism.lean` defines the syntax and a substitution-based small-step relation `Step` with its determinism theorem (`Step.deterministic`). `CEK.lean` then defines the abstract machine the compiler actually runs (see [the interpreter](#the-interpreter)): an environment machine with a continuation stack, `Rv` runtime values carrying closures and thunks, curried application, and the deep, mask-aware handler capture that makes `resume` multishot. The machine is a total, executable `step` function, so it is deterministic by construction and runnable.

The model's central theorem connects the two. A big-step natural semantics specifies what a program evaluates to, and `bigstep_runs` proves the machine implements it (a forward simulation under any continuation stack), so the abstract machine is a faithful realization of the specification rather than an independent artifact. `Meta.lean` adds the supporting metatheory: a unique-normal-form corollary, substitution lemmas, and a progress trichotomy (every computation is a value, takes a step, or is an explicit `Stuck` error, with `stuckNoStep` confirming the classification is a genuine partition). `Dynamics.lean` covers the effect machinery, proving the machine reaches a handler exactly when one is in scope (`effect_progress`) and is stuck on an unhandled operation otherwise (`effect_unhandled`). Every theorem is `sorry`-free; the proofs depend only on `propext`/`Quot.sound`, with `Classical.choice` added only where the model evaluates IEEE floats (whose arithmetic Lean defines non-constructively).

### 13.2 The Model as a Differential Oracle {#the-model-as-a-differential-oracle}

The Lean machine is run as a third oracle alongside the interpreter and native backends. `prism dump core-json <file>` serializes the elaborated core to a JSON tree (`src/core/json.rs`), which `models/Json.lean` decodes back into the Lean syntax, and the `oracle` executable (`models/Oracle.lean`) runs the verified machine on it and prints the result, rendering floats through a port of the runtime's `fmt_g` shortest-round-trip formatter so output is byte-identical. Because Lean cannot call the C and Rust `printf` machinery the other two backends use, that formatter is reimplemented from the raw IEEE-754 bits in exact arbitrary-precision integer arithmetic, choosing the fewest significant digits (one to seventeen) that round-trip back to the same double; the round-trip check is the one place the otherwise constructive model uses `Classical.choice`. `models/diff_against_rust.sh` pipes each fixture through `prism dump core-json | oracle` and compares against `prism run`, so the verified model is checked against the interpreter on the compiler's actual core, not a hand-transcription. `models/Certificates.lean` records the same agreements as kernel-checked `rfl` theorems for the curated set. The grammar in [the specification](spec.md) is itself single-sourced from `models/grammar.ebnf`.

## 14. Optimization {#optimization}

The mid-level Core-to-Core tier is a composable pass framework in the spirit of GHC's `[CoreToDo]` pipeline. One shared traversal (`Rewrite`/`Visit`) replaces the hand-rolled Core walkers, so newtype erasure, dictionary specialization, free-variable collection, call collection, and substitution all ride a single visitor (the canonical hasher from [architecture](#architecture) and the tail-recursion classifier from [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse) stay bespoke by design). Each pass is a `CorePass` keyed by a `PassStage`, and the whole pipeline runs from one ordered, level-keyed list through a single `opt::run` entry.

The pipeline spans two stages around effect lowering, so passes are not freely reorderable across it. _Pre-lowering_ passes run in the front end on the elaborated core (see [the core calculus](#the-core-calculus)); _late_ passes run on the lowered core, after [effect lowering](#effect-lowering) has fixed the fusion strategy. The split is load-bearing for performance. The simplifier runs in the late stage on purpose: run before effect lowering it rewrote the Core shapes the var/State fusion analysis depends on and degraded that fusion (a regression bisected to copy-propagation), so it runs after lowering, where it cannot defeat the fusion.

### 14.1 Optimization Levels {#optimization-levels}

The `-O`/`--opt` flag selects a level; the default is `-O1`.

| Level | Passes                                                                                                                                                                                                                                           |
| ----- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `-O0` | Representation only: newtype erasure, which both backends depend on.                                                                                                                                                                             |
| `-O1` | Adds dictionary specialization (pre-lowering) and a gentle simplifier run to a fixed point in the late stage: case-of-known-constructor, trivial copy-propagation, dead-let elimination, integer constant folding, and used-once-thunk inlining. |
| `-O2` | Adds a bounded inliner (single-call-site non-recursive functions, with every callee binder alpha-renamed) and a conservative scalar common-subexpression elimination over pure, non-trapping `Prim`s.                                            |

### 14.2 Explicit Pass Lists {#explicit-pass-lists}

`--passes` drives the tier with an explicit ordered pass list, the LLVM `opt -passes=` / GHC `[CoreToDo]` analogue. It overrides the `-O` level rather than augmenting it, and the two are mutually exclusive. The syntax is `[pre:<names>][;late:<names>]`, where `<names>` is a comma-separated list of pass names; a bare comma-list with no marker is the pre stage. The pass names are `EraseNewtypes` and `Specialize` in the pre stage and `Simplify`, `Inline`, and `Cse` in the late stage. Each section is exactly the passes named, in run order, with no level defaults filled in, so explicit means explicit: `--passes 'pre:EraseNewtypes,Specialize;late:Simplify'` reproduces the `-O1` pipeline.

The parser rejects an unknown name (suggesting the closest known one), a pass placed in the wrong stage, a pre section that orders `Specialize` before `EraseNewtypes`, and an empty spec.

### 14.3 Lint, Telemetry, and Parity {#lint-telemetry-and-parity}

A Core Lint well-formedness check, pipeline idempotence, and per-pass tick telemetry gate every pass, alongside the triple-backend parity oracle (see [verification](#verification)). Parity is the invariant: compiled behavior at every level, and under any `--passes` spec, is byte-identical under the oracle, so optimization can only change cost, never meaning.

Several environment knobs aid debugging, all off by default.

| Variable | Effect |
| -------- | ------ |
| `PRISM_OPT_STATS` | dumps per-pass rewrite counts |
| `PRISM_CORE_LINT` | lints between passes |
| `PRISM_DUMP_CORE` | writes the Core after each pass to a stream or to run-namespaced files under `target/` |
| `PRISM_OPT_LEVEL` | overrides the level when no `-O` flag is given |
| `PRISM_NO_SPECIALIZE` | disables dictionary specialization |

## 15. The Interactive Shell {#the-interactive-shell}

Running `prism` with no arguments starts a read-eval-print loop (`src/repl/`) backed by the interpreter described under [backends](#backends). It is a _typed_ REPL: an entered expression is parsed through the expression entry point of [parsing](#parsing), inferred, elaborated, and evaluated, and its type and effect row are shown above the value.

A session accumulates state. An expression is evaluated and its result bound to `it`; a `let` binds a name for reuse; and a top-level `fn`, `type`, `class`, `instance`, or `effect` declaration is added to the session so later input sees it. Declarations entered for a name shadow earlier ones.

Commands begin with `:`; any unambiguous prefix resolves to its command, GHCi-style, so `:r` is `:reload` and `:lo` is `:load`.

| Command          | Action                                                       |
| ---------------- | ------------------------------------------------------------ |
| `:type e`        | show the type and effect row of expression `e`               |
| `:kind T`        | show the kind of a type constructor                          |
| `:info n`        | describe a binding, type, or class                           |
| `:browse`        | list the bindings this session has added over the prelude    |
| `:core`          | dump the lowered core IR of the session                      |
| `:load f`        | load declarations from a file, making it the active file     |
| `:reload`        | re-read the active file from disk                            |
| `:edit [f]`      | open a file (or a scratch buffer) in `$EDITOR`, then load it |
| `:set [+-]flags` | toggle options; bare `:set` lists them                       |
| `:quit`          | leave the shell                                              |

Two `:set` toggles exist: `t` (`types`) shows the inferred type and effect row of each result, on by default, and `s` (`timing`) reports evaluation time. A multi-line block runs between `:{` and `:}`, or is auto-detected when a line opens a layout block that is not yet closed.

## 16. The Formatter {#the-formatter}

`prism fmt` parses a file to the surface AST and prints that tree back to text. It is not a token reflow: parsing discards whitespace, so the printer reconstructs all layout from scratch, and the only things carried across from the original are the trivia the lexer recorded during [lexing and layout](#lexing-and-layout) and, as a last resort, raw byte ranges. An already-formatted file is a fixed point, which is what `prism fmt --check` verifies by comparing the printed output to the input byte for byte. The implementation lives in `src/fmt/`, with `mod.rs` driving expression and block layout, `decl.rs` and `pat.rs` handling declarations and patterns, and `ops.rs` the operator-precedence parenthesization.

**Trivia reattachment.** Comments and blank lines are not nodes in the AST. The lexer records them in marginalia's `TriviaTable`, a side table keyed by byte offset that the parser fills alongside the token stream. The printer queries that table by source range: `between(lo, hi)` yields the trivia events lying in a gap and `after(end)` yields whatever trails the final declaration. Because every AST node carries its source span, "the comment above this arm" or "the blank line between these two statements" is recovered as the trivia lying in the gap between one node's end offset and the next node's start offset. This is why trivia survives not just between top-level declarations but inside function bodies, handler arms, and match arms, each printer threads the byte offset where the previous construct ended and re-emits the comments found before the next one begins. Line comments and deliberate blank-line grouping round-trip; block comments carry no placeable layout and are dropped.

**Two layout engines.** Expressions use a hand-rolled width model: each node is first rendered inline by `fmt_expr_inline`, and if that string fits the 80-column budget at the current indent it is kept, otherwise the node falls back to a broken multi-line form via `fmt_expr_break`. Patterns instead reuse marginalia's `Doc` combinator engine (`block`, `concat`, `comma`, `pretty_at`), which makes the same fit-or-break choice generically over their nested constructor, tuple, and record structure. The two coexist because expression breaking is context-sensitive (statement position, offside blocks, trailing-lambda calls, operator precedence) in ways the generic combinators do not capture, whereas patterns are purely structural and a stock pretty-printer suffices.

**Layout versus flat.** A `Mode` is threaded through every printer. `Layout` emits Prism's offside blocks, the indentation-significant `let` chains and `match`/`handle`/`if`/`for` bodies. `Flat` is for bracketed contexts (tuples, argument lists, an inline `match { ... }`) where the virtual layout tokens are suppressed, so only inline `let ... in` and braced arms are legal there. In statement position `match` and `if` always lay out across lines even when they would fit on one, since stacked arms and branches read better, matching how those forms are written in other languages.

**Surface restoration.** [Desugaring](#desugaring) rewrites several surface forms into a smaller core before formatting ever sees them: UFCS `recv.f(x)` becomes `f(recv, x)`, `e?` and string interpolation become marker calls, and pattern-`let` and `?`-binding become single-arm matches. The parser tags each lowered node with a synthetic span or a `synth` flag, and the formatter keys off those flags to reprint the original surface rather than the lowered shape. This is what makes formatting idempotent: the printed output desugars back to the same core, so a second pass changes nothing.

**Never destroy code.** The formatter borrows the original source for one purpose, a verbatim fallback: any node it cannot otherwise print is emitted as its exact original byte range. Together with parse-or-fail (an unparseable file yields an error, never a mangled rewrite), this guarantees `prism fmt` is information-preserving even on constructs the printer does not yet model.
