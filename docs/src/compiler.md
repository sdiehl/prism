# The Prism Compiler

This document describes the `prism` compiler, from source text to native binary across its three backends.

## 1. Architecture

Compilation is a pipeline from source text to a native binary. Each phase is a total function over the program, and there are no per-module artifacts.

| Phase                                                    | Role                                                                                                              | Owner                                      |
| -------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- | ------------------------------------------ |
| [Lex](#2-lexing-and-layout)                              | text to tokens, then layout                                                                                       | `src/lex/`                                 |
| [Parse](#3-parsing)                                      | tokens to surface AST                                                                                             | `src/parse/`, `src/syntax/grammar.lalrpop` |
| [Resolve](#4-name-resolution-and-modules)                | load imports, canonicalize names, merge                                                                           | `src/resolve/`                             |
| [Desugar](#5-desugaring)                                 | surface sugar to core surface                                                                                     | `src/syntax/desugar/`                      |
| [Check](#6-type-and-effect-inference)                    | type and effect inference                                                                                         | `src/tc/`                                  |
| Elaborate                                                | surface to [CBPV / ANF core](#7-the-core-calculus) (match compilation, Section [8](#8-pattern-match-compilation)) | `src/core/elaborate/`                      |
| [Effect lower](#9-effect-lowering)                       | remove handlers and operations                                                                                    | `src/core/effect_lower/`                   |
| [Reference count](#10-reference-counting-and-fbip-reuse) | insert `dup`/`drop`, then reuse                                                                                   | `src/core/fbip.rs`                         |
| [Codegen](#11-backends)                                  | core to interpreter, LLVM, or MLIR                                                                                | `src/eval/`, `src/codegen/`                |

The driver (`src/driver/`) exposes these as subcommands: `prism run` interprets, `prism build` compiles to a native binary, `prism check` runs the front end only, `prism fmt` formats, and `prism dump <phase>` prints an intermediate form, where `<phase>` is `tokens`, `ast`, `types`, `core`, `fbip` (core after reference-count insertion and reuse), `lowered` (after effect lowering), `llvm`, or `mlir` (the last gated on the MLIR backend feature).

## 2. Lexing and Layout

The lexer produces a token stream and trivia (comments and spacing) that the formatter uses to reproduce source faithfully. An interpolated string is lexed by re-lexing each `{ ... }` hole at its absolute source offset, so spans inside holes remain accurate. A layout pass then rewrites the stream, inserting virtual block-open, block-close, and separator tokens according to the offside rule of [Spec 3.6](./spec.md#36-layout), which the grammar consumes as ordinary terminals.

## 3. Parsing

The grammar is an LALR(1) grammar in LALRPOP (`src/syntax/grammar.lalrpop`), with two entry points: a whole program, and a single expression for the REPL. Parsing produces the surface AST of `src/syntax/ast.rs`. Type and parse errors are rendered with a source caret.

## 4. Name Resolution and Modules

Resolution loads every transitively imported module, rewrites each top-level definition to a globally unique canonical symbol (an export as `Data.Map.insert`, a private as `Data.Map@helper`), resolves qualified and re-exported references to those symbols, and merges all modules into one flat program. This is a whole-program renamer: the entire program is checked and compiled from source on every build. The canonical-symbol scheme makes the merge sound, since two modules can export the same short name without collision.

Moving to incremental, per-module compilation is planned but not implemented; the interprocedural analyses below (effect lowering, borrow signatures, instance coherence) are what make it nontrivial, since each crosses module boundaries.

## 5. Desugaring

Desugaring rewrites surface sugar into the smaller core-surface language the checker and elaborator handle (`src/syntax/desugar/`), each rule shown as surface form and the form it lowers to.

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

A list comprehension (and the statement `for`) lowers to a stream (a producer performing the `Emit` effect, Section [9](#9-effect-lowering)) that emits each surviving element, collected with `scollect` (a stream consumer that gathers the emissions into a list), so it fuses with no intermediate list.

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

A record update rebuilds the constructor along the named fields; on a uniquely owned value the rebuild is the in-place write of Section [10](#10-reference-counting-and-fbip-reuse).

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

`try`/`catch`/`throw` is subtractive handler sugar: one nested `final ctl` clause (the non-resumable handler clause of [Spec 7.2](./spec.md#72-clause-sugar)) per arm, each discharging one error label.

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

The `var` desugaring is shown with full Source / Desugared / Core stage tabs in [Spec 7.4](./spec.md#74-local-mutation); default and named arguments lower to positional ones in the same pass.

## 6. Type and Effect Inference

Type inference is the bidirectional, higher-rank algorithm of [Dunfield & Krishnaswami (2013)](bibliography.md#dunfield-krishnaswami-2013) (`src/tc/`); the surface rules are in [Spec 5](./spec.md#5-types-and-kinds). Type classes elaborate to dictionary-passing: a constraint becomes a hidden parameter, resolved to a global instance, a passed dictionary, or a projection of a superclass dictionary.

Instances are global, but each records its defining module, so coherence is checked by provenance (`src/tc/classes.rs`). An orphan instance (defined apart from both its class and its head type) and instances that overlap across modules are reported as warnings, with a source caret when they point into the program being compiled, and an ambiguous use reports each candidate's module. Ambiguity is resolved at the use site with `f[name]` rather than by Haskell-style global single-instance coherence.

Effect inference currently runs two engines, a known piece of debt. A syntactic _set-pass_ (a pass that computes a _set_ of operation labels, `src/types/effects.rs`) walks the call graph to a fixpoint, computing the operations each function may perform, and seeds each function's row before checking. The row unifier in `src/tc/subsume.rs` then infers the row proper (a _row_ is a function's effect set; [Spec 5](./spec.md#5-types-and-kinds)): at a call it adds the callee's row to the caller's _ambient row_ (the effect set accumulated for the body so far), and a handler removes the operations it discharges. After checking, the set-pass result must be a subset of the inferred row, or the compiler raises an internal error.

The seed is necessary because the unifier cannot yet discover an operation label from a perform site alone. The same per-function operation set also drives effect lowering's strategy choice (Section [9](#9-effect-lowering)), so it serves both phases. Making inference _principal_ (each declaration inferring its most general row from its body alone) would eliminate the set-pass and the reconciliation; that is planned.

## 7. The Core Calculus

Elaboration lowers the surface language to a call-by-push-value core ([Levy, 2004](bibliography.md#levy-2004); `src/core/cbpv.rs`) in A-normal form. CBPV separates _values_, which are inert, from _computations_, which can be run; `Thunk` freezes a computation into a value and `Force` runs it. A-normal form names every intermediate result with a `Bind`, making evaluation order explicit and each operation and allocation syntactically distinguished, enabling the later effect and reference-counting passes. The grammar below is the elaborated core; the reference-count pass (Section [10](#10-reference-counting-and-fbip-reuse)) later adds `dup`, `drop`, and reuse nodes to it.

```text
{{#include ../examples/cbpv-grammar.txt}}
```

For example, a constructor applied to a call elaborates so the call is named before the constructor is built:

```text
{{#include ../examples/anf-example.txt}}
```

A subset of this calculus is modeled in `models/Prism.lean` (Lean 4; [de Moura & Ullrich, 2021](bibliography.md#demoura-ullrich-2021)), which mirrors the core one variant at a time and proves a small-step determinism theorem (`Step.deterministic`).

## 8. Pattern-Match Compilation

A `match` is compiled to a decision tree (`src/core/elaborate/match_compile.rs`). The arms form a matrix whose rows are arms and columns are argument positions. The compiler selects a column, partitions the arms by the head of that column's patterns, and emits a test: a `Case` on the constructor tag of the scrutinee (the value being matched) for a constructor column, or a chain of equality tests for a scalar column. Wildcard rows form a default sub-matrix shared by the branches that fall through. A guarded arm compiles to a conditional that re-enters the remaining arms when the guard fails. Exhaustiveness, proven by the checker ([Spec 9](./spec.md#9-patterns)), guarantees every scrutinee reaches an arm.

## 9. Effect Lowering

Effect lowering compiles away the `Handle`, `Do`, and `Mask` nodes of the core. An operation is delimited control (an effect suspended and resumed within a handler's scope): `Handle` is the delimiter, and the resumption `k` is the continuation captured between a perform site and its handler ([Spec 7](./spec.md#7-effects-and-handlers)). The three strategies are three compilations of that one mechanism, differing in how much of `k` they make manifest, from nothing to a heap-allocated tree. The compiler tries them in that order and takes the first that applies, so it reifies as little of the continuation as the program allows; a check then confirms no effect construct survives.

**Evidence passing** is the fast path for tail-resumptive handlers (every clause calls `k` exactly once, in tail position, so the continuation need never be captured at all). Each operation is assigned a stable numeric id by sorting the operation names, and a call-graph fixpoint computes each function's _latent_ set, the operations still performed anywhere in its call-graph closure. An effectful function then gains one extra parameter per latent operation, `ev@<id>`, a thunk holding the active handler clause. Performing an operation forces its evidence thunk directly; a `handle` binds fresh evidence for its body's latent operations; and every call site appends the callee's evidence, in ascending id order, so the convention is positional and stable. A first-class thunk that escapes carries evidence parameters for its own latent operations, threaded at each force site. No continuation is reified and no per-operation cell is allocated. What evidence to thread where is computed by an interprocedural least-fixpoint flow analysis (`src/core/effect_lower/flow.rs`) that derives, for every function, the operation signature of the thunk it returns and of each thunk-valued parameter.

**State threading and stream fusion** is the path for a uniform single-operation handler, the shape a stream consumer takes: a handler that folds every `emit` into an accumulator. Such a handler clause is rewritten to an accumulator transformer `\acc -> acc'`, and the producer it wraps becomes a loop that threads the accumulator through each emission instead of allocating a value per step. A consumer that can stop early, like `stake`, returns a two-state tag (continue or done) that the producer checks, so the loop exits without unwinding. This reifies one small tag cell per early-terminating handler and, like evidence passing, no free-monad cell, so a `smap`/`skeep`/`stake`/`ssum` pipeline allocates neither an intermediate list nor a per-operation cell.

```prism
{{#include ../examples/streams.pr}}
```

**The free-monad fallback** applies when an effect escapes static tracking: buried in data, dynamically applied, masked, genuinely multishot (a clause that resumes `k` more than once), or self-referential (a handler whose own body performs the effect it handles). A multishot handler forces this path because the two fast paths erase `k`, and a continuation invoked more than once must exist as a reusable value. Here the delimited continuation is reified in full: each computation becomes a tree of `EPure` and `EOp` cells threaded by `ebind` (shown below), and `k` is an explicit closure field of each `EOp`, so a clause can hold it, drop it, or apply it repeatedly. A `handle` becomes a generated driver function that case-dispatches the reified tree: an `EPure` runs the return clause, an `EOp` whose id the handler names and whose skip count is zero runs the matching clause, and any other `EOp` is re-emitted outward with a re-entry continuation, which is how an inner handler forwards an operation it does not catch. An `EOp` carries a `skip` field, its mask depth, the number of matching handlers it must still bypass; a `mask` driver increments it and the handler driver only fires when it is zero. This is exactly the interpreter's dispatch (Section [11](#11-backends)), so the two agree by construction. Each `EOp` allocation bumps the `PRISM_EFFOP_STATS` counter, so the fallback's cost is observable. Lowering is whole-program: if any effectful thunk escapes, every effectful function is converted to the free-monad form (monadified) together; otherwise only the functions that perform effects are.

```text
{{#include ../examples/free-monad.txt}}
```

The example below exercises this path: an inner handler catches `Log` and forwards `raise` outward to an `Exn` handler, the two effects interleaving across the nesting.

```prism
{{#include ../examples/eff_forward.pr}}
```

The fallback reifies one cell per pending operation, so its cost is proportional to the operations in flight; the fast paths avoid it where they apply.

## 10. Reference Counting and FBIP Reuse

Reference counting runs after effect lowering, over the handler-free core, so it counts evidence parameters and any reified cells as ordinary values. Memory is managed by Perceus-style reference counting ([Reinking et al., 2021](bibliography.md#reinking-2021); `src/core/fbip.rs`): every parameter and binding is owned and consumed exactly once on every control-flow path from its binding to the end of its scope; a second use inserts a `dup` and an unused value inserts a `drop`. Perceus places these operations precisely rather than conservatively at scope exit, which frees a cell at the earliest point the reuse pass below can claim it. Closure captures are borrowed (read without being consumed) and duplicated before a consuming use, as is a `borrow` parameter ([Spec 10](./spec.md#10-declarations-and-programs)). The parameters a function borrows are recorded as a per-function bit vector, its interprocedural _borrow signature_, which every caller consults to place its `dup`/`drop` correctly. Because that signature crosses call sites, it is one of the analyses that complicates the move to separate compilation (Section [4](#4-name-resolution-and-modules)).

The reuse pass then turns drops into in-place updates. When a uniquely owned scrutinee is dropped and the continuation rebuilds a constructor of the same or smaller size, the `drop` becomes a _reuse token_ (the freed cell, held for reuse) and the rebuild writes into it, so `map` and tree rebuilds mutate the spine in place. An independent token-balancing verifier rejects any rewrite where a token is not freed and consumed the same number of times on every path.

The `fip`/`fbip` annotations ([Spec 10](./spec.md#10-declarations-and-programs)) are the fully-in-place discipline of [Lorenzen et al. (2023)](bibliography.md#lorenzen-fp2-2023), here static checks layered on these passes. `fbip` proves zero fresh allocation and a call-graph closure over annotated, allocation-free callees. `fip` adds two further properties: linearity (each owned binding is consumed at most once, checked on the source term, with scalars exempt because adjusting the count of an unboxed word costs nothing) and bounded stack. The tail-call and tail-modulo-cons (a tail call whose result is wrapped in one constructor) classification (`src/core/tailrec.rs`) is shared with codegen, so an accepted `fip` function always lowers to a loop; acceptance never outruns what the backend emits.

```prism
{{#include ../examples/fip_list.pr}}
```

## 11. Backends

Prism has three backends over one core: a tree-walking interpreter that is the reference oracle, and two native backends that must match it byte for byte. The native backends share a single generic emitter, so the differences below are narrow.

### 11.1 The Interpreter

The tree-walking interpreter (`src/eval/`) is a flat CEK (control, environment, continuation-stack) machine. Pending work lives on an explicit heap stack of frames rather than the host call stack, so object-program recursion never overflows it. A frame is one of: `Bind` (await a result, then continue with the rest of a sequence), `Args` (await a function before applying it), `Handle` (an installed handler), `Mask` (a masking frame), and `Restore` (unwind a name binding; a `Restore` already on top marks tail position, which is where the machine recognizes a tail call).

This machine makes the delimited continuation of [Spec 7](./spec.md#7-effects-and-handlers) concrete: performing an operation searches the frame stack outward for a matching `Handle`, decrementing the skip count past masked frames, and the _captured continuation_ is exactly the slice of frames between the `do` and that handler, the handler included. Resuming pushes a clone of that slice back onto the stack, so the same resumption can be pushed again, which makes `k` multishot. The free-monad backend reifies this same frame slice as the `k` closure of an `EOp` (Section [9](#9-effect-lowering)); evidence passing never materializes it.

### 11.2 The Shared Emitter

Both native backends drive one generic emitter (`src/codegen/emit.rs`) behind an `Isa` trait that abstracts instruction emission, so they differ only in instruction spelling. The emitter owns case dispatch, constructor allocation and reuse, and tail-call lowering: a self-tail call of equal arity becomes a `musttail` loop, and a constructor- or accumulator-shaped tail call (one whose result feeds a constructor or an integer accumulator) becomes a destination-passing loop, one that writes its result into an address passed as a hidden parameter rather than returning it, using the same classification the `fip` check reads (Section [10](#10-reference-counting-and-fbip-reuse)).

### 11.3 LLVM

The LLVM backend (`src/codegen/llvm.rs`) implements `Isa` over inkwell, emitting LLVM IR that `clang` compiles and links against the runtime. This is the default native path.

### 11.4 MLIR

The MLIR backend (`src/codegen/mlir.rs`) implements the same `Isa` by writing textual MLIR in the `llvm` dialect. Sharing the emitter makes its output byte-identical to the LLVM backend's, which the parity gate (Section [13](#13-verification)) enforces.

### 11.5 WebAssembly

The compiler front end and the interpreter also compile to WebAssembly (`src/wasm.rs`), so Prism type-checks and runs in the browser. This target hosts the interpreter, not the native code generators; the LLVM and MLIR backends are absent there.

## 12. The Runtime

The C runtime (`runtime/prism_rt.c`) is linked with the code each backend emits. It assumes an LP64 target (64-bit pointers and `long`) and uses `mimalloc` when available. The data representation below is shared by the backends and the runtime.

### 12.1 Value Representation

Every value occupies one 64-bit word, tagged by its low bit so that a single representation serves both scalars and pointers under polymorphism.

```text
{{#include ../examples/value-repr.txt}}
```

A float does not fit the immediate scheme, so it is _boxed_: wrapped in a one-field cell holding the raw double bits, which are read back out (unboxed) at every float operation. Boxing makes a float field self-describing, so the collector frees it without interpreting its payload.

### 12.2 Cell Layout

A heap cell is a three-word header followed by its fields.

```text
{{#include ../examples/cell-layout.txt}}
```

Constructor tags follow declaration order (for `Option(a) = None | Some(a)`, `None` is 0 and `Some` is 1). Two tag values are reserved, `0x53545200` for a string and `0x42494700` for a bignum (Section [12.5](#125-integers)), marking cells whose payload is raw bytes or limbs rather than child values; the collector and the reuse pass (Section [10](#10-reference-counting-and-fbip-reuse)) read the tag to avoid recursing into them.

### 12.3 Reference Counting

`prism_rc_inc` and `prism_rc_dec` take the raw value word and return immediately on an immediate or unit, so counting is a no-op on non-cell values. Decrement to a nonzero count just decrements. Decrement to zero frees the cell, but freeing is _iterative_, not recursive: the dead cell's now-zero refcount word is reused as a link field in an intrusive worklist of cells pending free, so a structure of any depth is reclaimed in constant auxiliary space without growing the C stack. A string or bignum tag short-circuits the child traversal.

### 12.4 In-Place Reuse

The reuse pass of Section [10](#10-reference-counting-and-fbip-reuse) emits two runtime calls. `prism_reuse_token(v)` inspects a cell about to be dropped: if it is uniquely owned (refcount 1), it drops the cell's children and returns the shell as a token, leaving the live-cell count untouched; otherwise it decrements and returns null. `prism_reuse_alloc(token, n)` overwrites the token's header for the new constructor when the token is non-null, and falls back to a fresh allocation when it is null. A uniquely owned spine is therefore mutated in place, and a shared one transparently copies.

### 12.5 Integers

A small integer is an immediate, `(n << 1) | 1`. An operation whose fixed-width result would overflow promotes to a _bignum_: a cell tagged `0x42494700` storing the value in sign-magnitude form (sign and magnitude kept separate). Its header word is a signed limb count whose sign is the value's sign; the magnitude follows as that many little-endian `u64` limbs (base-2^64 digits) with no leading zero limb. Zero is a count of zero with no limbs. Each surface arithmetic operation takes a fast path on two immediates with a checked-overflow primitive and falls back to magnitude routines (add, subtract, multiply, and a shift-subtract long division) that renormalize the result, demoting back to an immediate when it again fits. The surface `Int` is this unbounded integer. The `I64` and `U64` lanes are raw machine words and wrap rather than promote.

### 12.6 Strings

A string is a cell tagged `0x53545200` whose field words hold its UTF-8 bytes inline, length-prefixed by the arity word and NUL-terminated for C interop. Each string the program builds, including a literal at each use, is a counted cell, so the leak counter (Section [12.7](#127-instrumentation)) accounts for strings like any other allocation. Two indexing families coexist: `char_at`, `substring`, and `str_len` work in Unicode codepoints, walking the UTF-8 encoding (and so are O(n)), while `byte_at` and `byte_len` give O(1) raw-byte access for a scanner or hash.

### 12.7 Instrumentation

Three environment-gated counters report to stderr at exit, leaving stdout (the parity-checked channel) untouched. `PRISM_CHECK_LEAKS` reports the live-cell balance, which a clean run drives to zero. `PRISM_REUSE_STATS` reports how many cells the reuse pass rewrote in place. `PRISM_EFFOP_STATS` reports how many free-monad `EOp` cells were allocated, which the performance gate asserts is zero on the fusion corpus.

### 12.8 Growable Arrays

The growable `Array(a)` ([Spec 12](./spec.md#12-the-standard-prelude)) is an ordinary cell, `{ rc, tag 0, arity cap+1, len, elem0 .. }`, with the length word stored odd-tagged (low bit set, so the collector skips it as an immediate per Section [12.1](#121-value-representation)) and unused slots held at zero. Because it is a normal cell, reference counting recurses into its live elements with no special case. Every array operation borrows its array argument. `array_get` returns a counted element; `array_set`, `array_push`, and `array_pop` write in place when the array is uniquely owned (refcount 1) and copy otherwise, so functional array code runs as mutation exactly when ownership permits. `array_push` doubles the capacity when full, making appends amortized O(1). The prelude's `HashMap` is a separate-chaining hash table layered on this array, with an FNV-1a hash written in Prism (so iteration order is a deterministic function of the inserts); it is library code, not a runtime primitive.

### 12.9 Primitive Sort

`sort` is a runtime primitive (`prism_sort_prim`) that borrows a list and returns it sorted, dispatched on a key kind. Arbitrary-precision `Int` keys use a bignum-aware stable bottom-up merge sort, ping-ponging between two buffers; fixed-width keys use a radix sort over a derived key. When the input spine is uniquely owned, the sorted heads are written back into the existing cells with no allocation; a shared spine is copied with its elements shared. The `Cons` and `Nil` tags are read off the input spine, so no list layout is baked into the runtime.

### 12.10 Input, Output, and Randomness

The runtime provides the impure builtins. `read_int` and `read_line` read stdin; `read_file`, `write_file`, `append_file`, and `file_exists` operate on files; `getenv` reads the environment; `system` runs a shell command and returns its exit code; `eprint` and `eprintln` write to stderr, leaving the parity-checked stdout untouched; and `args_count` and `arg` (wrapped by the prelude's `args`) read the command line. Randomness is a SplitMix64 generator: `rand` advances it and `srand` seeds it, so a seeded run is deterministic and reproducible. Because these touch the world, the parity harness (Section [13](#13-verification)) runs only the programs that avoid them.

## 13. Verification

Two test gates hold the implementation to its claims. The parity harness (`tests/parity.rs`) is differential testing with the interpreter as the reference: it runs every example on the interpreter and each native backend and asserts byte-identical output, and with `PRISM_CHECK_LEAKS` set, zero leaked cells.

The performance gate (`tests/perf_gate.rs`) asserts that the optimizations actually fire, so a regression that leaves output unchanged is still caught. With `PRISM_EFFOP_STATS` set, it requires zero free-monad cells allocated on the fusion corpus (the stream and multi-handler programs such as `streams.pr`), confirming that the evidence and state paths of Section [9](#9-effect-lowering) reify nothing. With `PRISM_REUSE_STATS` set, it requires in-place reuse to fire on the reuse corpus (`list.pr`), confirming the reuse pass of Section [10](#10-reference-counting-and-fbip-reuse) rewrites drops into in-place updates.

## 14. The Interactive Shell

Running `prism` with no arguments starts a read-eval-print loop (`src/repl/`) backed by the interpreter of Section [11](#11-backends). It is a _typed_ REPL: an entered expression is parsed through the expression entry point of Section [3](#3-parsing), inferred, elaborated, and evaluated, and its type and effect row are shown above the value.

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

## 15. The Formatter

`prism fmt` reformats a source file using the trivia the lexer preserves (Section [2](#2-lexing-and-layout)), so comments and blank-line grouping survive a round trip. It separates top-level declarations with a blank line and prints `>>`/`<<` composition as the surface operator rather than expanding it to a lambda, so an already-formatted file is a fixed point.
