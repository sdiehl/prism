# The Prism Compiler {#the-prism-compiler}

This document describes the `prism` compiler, from source text to native binary across its three backends. The chapter on [verification](#verification) describes the model and how the Lean 4 kernel anchors the compiler's verification chain.

## 1. Architecture {#architecture}

Compilation is a pipeline from source text to a native binary. Each phase is a total function over the program, and there are no per-module artifacts.

| Phase                                                 | Role                                                                                                                          | Owner                                      |
| ----------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------ |
| [Lex](#lexing-and-layout)                             | text to tokens, then layout                                                                                                   | `src/lex/`                                 |
| [Parse](#parsing)                                     | tokens to surface AST                                                                                                         | `src/parse/`, `src/syntax/grammar.lalrpop` |
| [Resolve](#name-resolution-and-modules)               | load imports, canonicalize names, merge                                                                                       | `src/resolve/`                             |
| [Desugar](#desugaring)                                | surface sugar to core surface                                                                                                 | `src/syntax/desugar/`                      |
| [Check](#type-and-effect-inference)                   | type and effect inference                                                                                                     | `src/tc/`                                  |
| [Elaborate](#elaboration)                             | surface to [CBPV / ANF core](#the-core-calculus) (match compilation, [pattern-match compilation](#pattern-match-compilation)) | `src/core/elaborate/`                      |
| [Optimize](#optimization)                             | Core-to-Core passes, in two stages around effect lowering                                                                     | `src/core/opt/`                            |
| [Effect lower](#effect-lowering)                      | remove handlers and operations                                                                                                | `src/core/effect_lower/`                   |
| [Reference count](#reference-counting-and-fbip-reuse) | insert `dup`/`drop`, then reuse                                                                                               | `src/core/fbip.rs`                         |
| [Codegen](#backends)                                  | core to interpreter, LLVM, or MLIR                                                                                            | `src/eval/`, `src/codegen/`                |

The driver (`src/driver/`) exposes these as subcommands:

| subcommand           | does                                                                        |
| -------------------- | --------------------------------------------------------------------------- |
| `prism <file.pr>`    | compile one file to a native binary named after the source (`-o` overrides) |
| `prism build`        | compile the enclosing project, the nearest `prism.toml`; fails outside one  |
| `prism run`          | interpret                                                                   |
| `prism check`        | run the front end only                                                      |
| `prism fmt`          | format in place                                                             |
| `prism dump <phase>` | print an intermediate form                                                  |

The dump phases walk the pipeline in order:

| `<phase>`               | prints                                                        |
| ----------------------- | ------------------------------------------------------------- |
| `tokens`                | the token stream                                              |
| `ast`                   | the parsed syntax tree                                        |
| `types`                 | inferred types and effect rows                                |
| `core`                  | the elaborated core                                           |
| `core-json`             | the core as a JSON tree the Lean model reads                  |
| `core-hash`             | a content-addressed hash of each definition's elaborated core |
| `native-kont-table`     | the native-symbol-to-definition-hash table                    |
| `native-kont-state-map` | the entry ABI-word state map                                  |
| `fbip`                  | core after reference-count insertion and reuse                |
| `lowered`               | core after effect lowering                                    |
| `captures`              | closure-capture portability facts                             |
| `usage-summary`         | a per-definition allocation, `fip`, borrow, and effect table  |
| `llvm`                  | the LLVM IR                                                   |
| `mlir`                  | the MLIR form                                                 |

`core-json` is covered under [verification](#verification), and `core-hash` is computed in `src/core/hash.rs`. The two kont tables are what native LLVM builds embed as `prism_native_kont_table` and `prism_native_kont_state_map`. `usage-summary` has `usage-summary-md` and `usage-summary-json` projections of the same facts, and `mlir` is gated on the MLIR backend feature.

A project build writes its output rustc-style into a `target/` directory at the package root (the binary and its codegen intermediates) rather than dropping the binary in the current directory; an explicit `-o`/`--out` still wins, and single-file `prism <file.pr>` builds are unaffected. `prism clean` removes that `target/` directory, resolved at the nearest enclosing `prism.toml` (or the given path outside a project); an already-absent `target/` is a no-op success.

The Core-to-Core optimizer (see [optimization](#optimization)) is driven from the driver too: `-O`/`--opt` selects an optimization level (default `-O1`) and `--passes` supplies an explicit pass list, the two being mutually exclusive. `--mlir` selects the MLIR backend over the default LLVM one. The complete set of subcommands, flags, environment variables, dump phases, and REPL commands is tabulated under [command-line interface](#command-line-interface).

Every phase returns its result into one `thiserror` enum (`src/error.rs`) whose variants are the phases that can fail (lex, parse, resolve, type, codegen, runtime, IO) plus an `Ice` variant for an internal invariant violation, and a diagnostic is rendered with a source caret through `ariadne`, mapping spans back through the prepended prelude to the user's own text. An internal invariant is reported by constructing an `Ice` rather than by panicking, so a malformed source program always yields a diagnostic.[^ice-sites] The crate denies `unsafe` by default (`unsafe_code = "deny"`) and carries two audited exception sites: LLVM's dynamic byte-offset `getelementptr` builder and the interpreter's FFI calls into the vendored libm. Of the handful of `panic!`s in the tree all but one are test assertions, the exception being a `PRISM_CORE_LINT`-gated sanity check on the compiler's own IR (see [lint, telemetry, and parity](#lint-telemetry-and-parity)).

[^ice-sites]: Around sixty such sites across elaboration, checking, effect lowering, and codegen, the last through a non-panicking `ice` helper that records the first message and returns a poison value so emission stays total.

One invariant sits under all of it: a program's observable output is a pure function of its source and its pinned inputs, and nothing below the source may leak into it. The effect-lowering tier (see [effect lowering](#effect-lowering)), the optimization level, and the backend (see [backends](#backends)) are cost choices, not semantic ones, so they must be byte-invisible, and two oracles hold them to it: the interpreter every native backend must match, and the `tier_parity` check that forces each program onto a slower tier and diffs its output against the fast one. Replay, content addressing, and cross-backend attestation are then corollaries of that single property rather than features bolted on.

## 2. Lexing and Layout {#lexing-and-layout}

The lexer produces a token stream and **trivia** (comments and spacing) that the formatter uses to reproduce source faithfully. An interpolated string is lexed by re-lexing each `{ ... }` hole at its absolute source offset, so spans inside holes remain accurate. A layout pass then rewrites the stream, inserting virtual block-open, block-close, and separator tokens according to the offside rule of the [layout](./spec.md#layout) specification, which the grammar consumes as ordinary terminals. One shape needs care: a `class`, `instance`, or `effect` body is bare-indented with no keyword (like `of` or `=`) for the offside rule to anchor on, so on the header the lexer emits a synthetic opener, `VHead`, that starts the block; this lets an empty body and an indented one share a single grammar rule, and it is why those bodies became layout-sensitive when braces were retired. Layout is suspended inside brackets, so a parenthesized expression spans lines freely. Both are the layout pass's concern, never the grammar's, which sees only the virtual tokens.

Comments are one form only: `--` to the end of the line. There are no block comments. This is, on purpose, the least interesting decision in the language, because the lexical syntax of comments is by long observation the most bikeshed-prone corner of language design:

> In any language design, the total time spent discussing a feature in this list is proportional to two raised to the power of its position:
>
> 0. Semantics
> 1. Syntax
> 2. Lexical syntax
> 3. Lexical syntax of comments

Lexical syntax is a notoriously fraught topic, in functional languages especially. Every engineer is certain they alone know what "readable" is, and not one can tell you why; it is governed by fashion more than science. So Prism does not care: things are spelled the Prism way, and a reader who finds that unreadable is warmly reminded that many other languages exist. Prism is the honey badger of unused functional languages; Prism does not care what you think is readable.

## 3. Parsing {#parsing}

The grammar is an LALR(1) grammar in LALRPOP (`src/syntax/grammar.lalrpop`), with two entry points: a whole program, and a single expression for the REPL. Parsing produces the surface AST of `src/syntax/ast.rs`. Type and parse errors are rendered with a source caret.

## 4. Name Resolution and Modules {#name-resolution-and-modules}

Resolution loads every transitively imported module, rewrites each top-level definition to a globally unique canonical symbol (an export as `Data.Map.insert`, a private as `Data.Map@helper`), resolves qualified and re-exported references to those symbols, and merges all modules into one flat program. This is a whole-program renamer: the entire program is checked and compiled from source on every build. The canonical-symbol scheme makes the merge sound, since two modules can export the same short name without collision.

Moving to incremental, per-module compilation is planned but not implemented; the interprocedural analyses below (effect lowering, borrow signatures, instance coherence) are what make it nontrivial, since each crosses module boundaries.

## 5. Desugaring {#desugaring}

Desugaring rewrites surface sugar into the smaller core-surface language the checker and elaborator handle (`src/syntax/desugar/`). Each rule below shows its surface form beside the elaborated Core the compiler prints for it (`prism dump core`, prelude elided), so the target is read off the real artifact rather than a hand-drawn approximation; the binder ids (`t@733`) are the compiler's own.

The surface tree is parameterized by its compilation _phase_ (`src/syntax/ast.rs`). An `Expr<P>` holds its sugar-only forms, its parse-time markers, and its surface-only handler clauses in fields whose types are associated types of the phase `P`: in the `Surface` phase those are the real sugar payloads, and in the `Core` phase, desugar's output, they are the uninhabited type `Never`. Because `Never` has no values, a sugar node cannot be constructed in the core phase at all, so a missed desugaring is a type error in the compiler rather than a runtime `unreachable!`, and every later pass over `Expr<Core>` is statically excused from matching the sugar cases.

Function composition lowers to a lambda, kept as sugar only so the operator survives formatting.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/compose_sugar.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/compose.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/range.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/comp.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/record_update.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/lens.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/default.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/ufcs.core.txt}}
```

{{#endtab }}

{{#endtabs }}

A string with interpolation holes becomes a concatenation of its literal pieces and the type-directed display of each hole; a top-level string is spliced in raw, not quoted the way the `Show` method renders it.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/interp_sugar.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/interp.core.txt}}
```

{{#endtab }}

{{#endtabs }}

`try`/`catch`/`throw` is subtractive handler sugar: one nested `never` clause (the non-resumable handler clause of [clause sugar](./spec.md#clause-sugar)) per arm, each discharging one error label.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/trycatch_sugar.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/trycatch.core.txt}}
```

{{#endtab }}

{{#endtabs }}

`transact body else fallback` snapshots every live `var`, runs the body under a `Fail` handler, and restores the snapshots on failure, so a failed attempt leaves observable state unchanged.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/transact_sugar.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/transact.core.txt}}
```

{{#endtab }}

{{#endtabs }}

Optional chaining `a?.b` is `force(a).b`, where `force` raises `fail()` on `None`, so a path short-circuits at the first `None` and an enclosing `??` supplies the default.

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/optchain_sugar.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/optchain.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/with.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/trailingblock.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/pattern_syn.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/pathupdate.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/deriving.core.txt}}
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

{{#tab name="Core" }}

```text
{{#include ../examples/postfix_try.core.txt}}
```

{{#endtab }}

{{#endtabs }}

The `var` desugaring is shown with full Source / Desugared / Core stage tabs in [local mutation](./spec.md#local-mutation); default and named arguments lower to positional ones in the same pass.

The [`stable` block](./spec.md#stable-blocks) is also pure desugar: each rung becomes an ordinary record type (the current rung under the bare name, each frozen predecessor under its dotted rung name), each adjacent version pair becomes a plain `upgrade_T_Vn_Vm` / `downgrade_T_Vm_Vn` function pair (generated for an additive change with an inline default, taken verbatim from the block for a hand-written converter), and the block derives the current rung's `Serialize` and `Stable` instances against the `Wire` classes. A rung's `frozen "<digest>"` badge is checked during elaboration against the rung's structural shape digest, so nothing downstream of desugar knows the block existed. Structural derivation itself (`src/syntax/desugar/derive.rs`) covers `Eq`, `Ord`, `Show`, `Lens`, `Hash`, `Serialize`, `Stable`, and `Arbitrary`.[^derive-classes]

[^derive-classes]: A derived instance is synthesized surface code elaborated like any hand-written one, `Hash` folds through the runtime `blake3` builtin with the same constructor tokens the [content-addressed core](#content-addressed-core) uses, `Serialize` writes the compact positional body against byte builders pinned by name in `names.rs`, `Stable` is a marker derivable only when every component is `Stable` (the failure is a compile error naming the offending field), and `Arbitrary` composes the `Quickcheck` generator combinators with recursion fuel so generation of a recursive type terminates.

## 6. Type and Effect Inference {#type-and-effect-inference}

Type inference is the bidirectional, higher-rank algorithm of [Dunfield & Krishnaswami (2013)](bibliography.md#dunfield-krishnaswami-2013) (`src/tc/`); the surface rules are in [types and kinds](./spec.md#types-and-kinds). Type classes elaborate to dictionary-passing: a constraint becomes a hidden parameter, resolved to a global instance, a passed dictionary, or a projection of a superclass dictionary.

Instances are global, but each records its defining module, so coherence is checked by provenance (`src/tc/classes.rs`). Resolution is coherent: for each `(class, type-head)` there is exactly one canonical instance, and implicit resolution always selects it. A single instance for a head is canonical automatically. When two or more instances share a head, one must be designated with a top-level `canonical Class(Head) = name` declaration (see [coherence and resolution](./spec.md#coherence-and-resolution)). An undesignated overlap is a hard error reported at definition, naming the candidates and their modules, with a source caret when they point into the program being compiled. An orphan instance (defined apart from both its class and its head type) is reported as a warning. An explicit override is written at the use site as a trailing `using` argument, `f(args, using name)`, which changes nothing else's resolution.

Indexing (`a[i]`, `a[i] := v`) is resolved the same way the `print`/interpolation display and `^` lowerings are, by type-directed dispatch at elaboration: the checker records each sub-expression's type in a span-keyed table, and the elaborator reads the receiver's head type back and emits the matching builtin or accessor through one wired classifier (`src/wired.rs`), the single home for the container names and their getter/setter functions: `Array` to `at_array`/`array_set`, `HashMap` to `at_hashmap`/`hm_insert`, `String` to `at_byte`, `List` to `at_list`, and `Tensor` to `at_tensor`/`tensor_set` (a bracket with two or more indices lowers to a list-keyed index for the tensor's strided lookup). A receiver whose type is still an unsolved existential when first synthesized (a `var` indexed before its initializer fixes its state type) defers to one pass at the end of the declaration, after the initializer has constrained it. No class or type-system extension is involved, so concrete indexing ships today; the desugar target is `index`/`index_set`, leaving room for a user-extensible `Index` class later.

Effect-row inference is _principal_: each declaration infers its most general row from its body alone. The row unifier in `src/tc/subsume.rs` discovers every label on its own (a _row_ is a function's effect set; see [types and kinds](./spec.md#types-and-kinds)) from direct performs, applied effect-carrying callees, builtin rows, and `mask`. At a call it adds the callee's row to the caller's _ambient row_ (the effect set accumulated for the body so far), and a handler removes the operations it discharges. The row is the single source of truth: there is no separate set-pass seed and no subset reconciliation against one.

A syntactic _set-pass_ (a pass that computes a _set_ of operation labels by a call-graph fixpoint, `src/types/effects.rs`) still runs, but only to feed the syntactic purity checks: it confirms a `konst` declaration and a declared-pure instance method perform nothing. It no longer seeds the row. After lowering, `reconcile_effects` checks the operations the lowered code actually performs against the inferred row, and the interpreter parity oracle (see [verification](#verification)) is the final backstop. Effect lowering computes its own per-function _latent_ operation set by an independent call-graph fixpoint (see [effect lowering](#effect-lowering)), so the two phases no longer share the set-pass result.

### 6.1 Kinds and Row-Kinded Type Parameters {#kinds-and-rows}

Type parameters carry a _kind_ (`src/types/ty.rs`, `Kind`). Almost every parameter has kind `Type` (`*`), and an unannotated parameter defaults to it, so the kind system is invisible to ordinary code and higher-kinded types stay structural (an applied variable `f(a)` is resolved by `App`/`Con` unification, not by a kind assignment). The one kind that changes inference is `Row`: a parameter annotated `: Row` ranges over effect rows rather than types.

A `Row`-kinded parameter lets a data type _store_ an effectful computation. In

```prism
type Box(a, e : Row) = Box(() -> a ! {e})
```

the field `() -> a ! {e}` mentions the row parameter `e` (a data field may name it either bare, `! {e}`, or in tail position, `! {IO | e}`). The constructor scheme quantifies `e` with a `RowForall` binder instead of a `Forall`, and the applied head `Box(a, e)` carries the row in its spine as a dedicated `Type::Row(EffRow)` argument. Row unification then threads through the same places type unification does (instantiation, substitution, zonking, pattern matching, and record construction), so opening `Box(f)` in a match instantiates `e` to a fresh row existential exactly as `a` is instantiated to a fresh type existential.

At a use site a `Row`-kinded argument is an effect row: a row variable (`Box(a, e)`) or a `{ .. }` row literal (`Box(Int, {IO})`, `Box(Int, {IO | e})`). Supplying a type where a row is wanted, or a row where a type is wanted, is a _kind mismatch_ reported at the annotation (`check_annot_rows`) rather than surfacing later as a row-versus-type unification failure.

This is the type-system half of effect-polymorphic concurrency: it is what makes an effect-polymorphic scheduler storable and, together with the ambient-row discipline for operations, sound. See [concurrency](#concurrency) for the whole story.

## 7. The Core Calculus {#the-core-calculus}

Elaboration lowers the surface language to a call-by-push-value core ([Levy, 2004](bibliography.md#levy-2004); `src/core/cbpv.rs`) in A-normal form. CBPV separates _values_, which are inert, from _computations_, which can be run; `Thunk` freezes a computation into a value and `Force` runs it. A-normal form names every intermediate result with a `Bind`, making evaluation order explicit and each operation and allocation syntactically distinguished, enabling the later effect and reference-counting passes. The grammar below is the elaborated core; the reference-count pass (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)) later adds `dup`, `drop`, and reuse nodes to it.

This follows GHC's discipline for Haskell: desugar and elaborate the entire surface language into one small, explicitly typed core, and make that core the single place every later pass operates. The surface may grow new sugar freely, but effect lowering, reference counting, optimization, and the Lean model all see only the handful of forms in the grammar below, so their complexity does not scale with surface syntax. Prism's core is smaller still than GHC's [System FC](bibliography.md#sulzmann-2007): call-by-push-value already makes evaluation order syntactic and A-normal form already names every intermediate result, leaving a pass little to re-derive.

```text
{{#include ../examples/cbpv-grammar.txt}}
```

For example, a constructor applied to a call elaborates so the call is named before the constructor is built: every intermediate result is named by a `Bind`, and arguments are values.

{{#tabs }}

{{#tab name="Surface" }}

```prism,ignore
fn f(y) = Cons(g(y), Nil)
```

{{#endtab }}

{{#tab name="Core" }}

```text
Lam [y]
  (Bind (Call g [Var y]) x
        (Return (Ctor Cons 1 [Var x, Ctor Nil 0 []])))
```

{{#endtab }}

{{#endtabs }}

A `match` compiles to a `Case` on an already-named value, each arm binding its constructor's fields and carrying a computation body:

{{#tabs }}

{{#tab name="Surface" }}

```prism,ignore
fn area(s) =
  match s of
    Circle(r) => r * r
    Square(w) => w + w
```

{{#endtab }}

{{#tab name="Core" }}

```text
Lam [s]
  (Case (Var s)
     [Circle [r] => (Prim Mul (Var r) (Var r)),
      Square [w] => (Prim Add (Var w) (Var w))])
```

{{#endtab }}

{{#endtabs }}

A function parameter is a thunk value: calling it is `Force` then `App`, kept distinct from the direct `Call` to a top-level name, and the inner call's result must be named before the outer call consumes it:

{{#tabs }}

{{#tab name="Surface" }}

```prism,ignore
fn twice(f, x) = f(f(x))
```

{{#endtab }}

{{#tab name="Core" }}

```text
Lam [f, x]
  (Bind (App (Force (Var f)) [Var x]) y
        (App (Force (Var f)) [Var y]))
```

{{#endtab }}

{{#endtabs }}

And a lambda in argument position is a computation frozen into a value with `Thunk`; its free variables are ordinary `Var` occurrences, which is all a closure capture is:

{{#tabs }}

{{#tab name="Surface" }}

```prism,ignore
fn scaled(y) = twice(\(n) -> n + y, y)
```

{{#endtab }}

{{#tab name="Core" }}

```text
Lam [y]
  (Call twice [Thunk (Lam [n]
                 (Prim Add (Var n) (Var y))),
               Var y])
```

{{#endtab }}

{{#endtabs }}

### Core Nodes {#core-nodes}

The core has two syntactic categories. A **value** (`Value` in `src/core/cbpv.rs`) is inert: it can be named, copied, and stored, but not run. A **computation** (`Comp`) can be run to produce a value or perform an effect. `Thunk` freezes a computation into a value and `Force`/`Return` cross back, so the two categories are bridged by exactly those nodes. The tables below name every node the backend passes see.

#### Values

| Node    | Description                                                                                |
| ------- | ------------------------------------------------------------------------------------------ |
| `Var`   | Reference to a bound variable, by its resolved symbol.                                     |
| `Int`   | A machine-word integer literal (the default `Int`).                                        |
| `I64`   | A fixed-width 64-bit signed integer literal.                                               |
| `U64`   | A fixed-width 64-bit unsigned integer literal.                                             |
| `Float` | A double-precision floating-point literal.                                                 |
| `Bool`  | A boolean literal.                                                                         |
| `Unit`  | The unit value `()`.                                                                       |
| `Str`   | A string literal.                                                                          |
| `Thunk` | A computation frozen as a value; `Force` runs it later. The value-from-computation bridge. |
| `Ctor`  | A fully applied data constructor: its symbol, its integer tag, and its field values.       |
| `Tuple` | An anonymous product of values.                                                            |

#### Computations

| Node           | Description                                                                                                                                        |
| -------------- | -------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Return`       | Lift a value into a (trivial) computation. The computation-from-value bridge.                                                                      |
| `Bind`         | Run a computation, name its result, and continue. A-normal-form sequencing, the only sequencer.                                                    |
| `Force`        | Run a thunk value.                                                                                                                                 |
| `Lam`          | A function abstraction over parameters with a computation body.                                                                                    |
| `App`          | Apply a computation (typically a forced closure) to value arguments.                                                                               |
| `Call`         | A direct call to a top-level function by name, kept distinct from `App` for direct-call codegen.                                                   |
| `If`           | Branch on a boolean value.                                                                                                                         |
| `Prim`         | A primitive arithmetic or comparison operator on two values (see Operators).                                                                       |
| `Case`         | Scrutinize a value against constructor and tuple patterns (see Patterns). The compiled form of `match`.                                            |
| `FloatBuiltin` | A unary floating-point or numeric-conversion builtin on one value (see Float builtins).                                                            |
| `StrBuiltin`   | A string, array, or map builtin applied to value operands.                                                                                         |
| `Io`           | A builtin IO operation and its operands: the output family, the input family, and RNG seeding (see IO operations).                                 |
| `Error`        | Raise a runtime error carrying a value. The panic and unrecoverable-failure surface.                                                               |
| `Do`           | Perform an effect operation: the operation symbol and its argument values. Algebraic-effect `perform`.                                             |
| `Handle`       | Install an effect handler: a body, per-operation clauses (each binding its parameters and a `resume` continuation), and an optional return clause. |
| `Mask`         | Bypass the innermost matching handlers for the named operations while running the body (effect tunnelling).                                        |

#### Reference-counting and reuse nodes

Elaboration does not produce these; the reference-counting pass inserts them (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)).

| Node        | Description                                                                                                                |
| ----------- | -------------------------------------------------------------------------------------------------------------------------- |
| `Dup`       | Increment a value's reference count to share an owned reference.                                                           |
| `Drop`      | Decrement a value's reference count, freeing the cell at zero.                                                             |
| `WithReuse` | Free a now-dead owned cell and bind its shell as a reuse token scoped over a body; the cell is freed at exactly one point. |
| `Reuse`     | Build a constructor in place over a reuse token's cell, without calling the allocator (in-place FBIP update).              |

#### Local-mutation nodes

Produced by effect lowering when it rewrites a closed, escape-checked `var` into a real mutable cell (see [effect lowering](#effect-lowering)), so a `var` loop runs in constant stack rather than through the free monad.

| Node     | Description                                                                  |
| -------- | ---------------------------------------------------------------------------- |
| `RefNew` | Allocate a one-field mutable cell holding a value; the result owns the cell. |
| `RefGet` | Read a mutable cell's field as an owned snapshot; the cell is borrowed.      |
| `RefSet` | Overwrite a mutable cell's field in place; yields `Unit`.                    |

#### Operators (`Prim`)

| Operation             | Integer | Float  |
| --------------------- | ------- | ------ |
| Addition              | `Add`   | `Addf` |
| Subtraction           | `Sub`   | `Subf` |
| Multiplication        | `Mul`   | `Mulf` |
| Division              | `Div`   | `Divf` |
| Remainder             | `Rem`   |        |
| Equality              | `Eq`    | `Eqf`  |
| Inequality            | `Ne`    | `Nef`  |
| Less than             | `Lt`    | `Ltf`  |
| Less than or equal    | `Le`    | `Lef`  |
| Greater than          | `Gt`    | `Gtf`  |
| Greater than or equal | `Ge`    | `Gef`  |

Short-circuiting `&&` and `||` lower to `If`, and `^` lowers to a class-method call, so none of the three reaches a `Prim`.

#### Patterns (`Case` arms)

| Pattern | Description                                                                    |
| ------- | ------------------------------------------------------------------------------ |
| `Var`   | Bind the whole scrutinee to a name (or ignore it).                             |
| `Ctor`  | Test the scrutinee's constructor tag, binding or ignoring each field position. |
| `Tuple` | Destructure a product, binding or ignoring each component.                     |

Literal, boolean, and record patterns are compiled away upstream into `If` and `Prim` tests, so only these three shapes survive into a `Case`.

#### IO operations (`Io`)

| Node       | Description                                                                      |
| ---------- | -------------------------------------------------------------------------------- |
| `Print`    | Print an integer value (the output family, performing the `Output`/`IO` effect). |
| `PrintF`   | Print a floating-point value (output family).                                    |
| `PrintS`   | Print a string value (output family).                                            |
| `PrintNl`  | Print a newline (output family).                                                 |
| `ReadInt`  | Read an integer from input (the input family, reading the world).                |
| `ReadLine` | Read a line of input as a string (input family).                                 |
| `Rand`     | Draw a pseudo-random integer (input family).                                     |
| `Srand`    | Seed the random-number generator.                                                |

Folding the family under one node keeps each structural pass to a single arm; the interpreter, codegen, and serializer switch on the operation where behavior differs.

#### Float builtins (`FloatBuiltin`)

| Node         | Description                                             |
| ------------ | ------------------------------------------------------- |
| `ToFloat`    | Convert an integer to a float.                          |
| `Truncate`   | Convert a float to an integer, discarding the fraction. |
| `FloorToInt` | Round a float down to the nearest integer.              |
| `CeilToInt`  | Round a float up to the nearest integer.                |
| `AbsFloat`   | Absolute value.                                         |
| `Sqrt`       | Square root.                                            |
| `Sin`        | Sine.                                                   |
| `Cos`        | Cosine.                                                 |
| `Exp`        | The exponential function `e^x`.                         |
| `Ln`         | Natural logarithm.                                      |

#### Program structure

| Node       | Description                                                                                             |
| ---------- | ------------------------------------------------------------------------------------------------------- |
| `Core`     | A whole program: the list of its top-level functions.                                                   |
| `CoreFn`   | One top-level function: its name, parameters, and computation body.                                     |
| `HandleOp` | One clause of a `Handle`: the operation name, its parameters, the `resume` binder, and the clause body. |

This calculus is modeled in Lean 4 ([de Moura & Ullrich, 2021](bibliography.md#demoura-ullrich-2021)): `models/Prism.lean` mirrors the core one variant at a time with a substitution small-step relation, on top of which the model adds an executable abstract machine that mirrors the interpreter and is proved to agree with it. The chapter on [verification](#verification) describes the model and how it anchors the compiler's verification chain.

## 8. Elaborator {#elaboration}

Elaboration is the surface-to-core translation (`src/core/elaborate/`): it turns the type- and effect-checked surface tree into the [call-by-push-value core](#the-core-calculus) above, making explicit everything the surface left implicit. The checker already did the deciding and recorded each result in a side table keyed by a stable `NodeId` (assigned after desugar), so elaboration is a second traversal that reads those tables and emits, rather than re-deriving anything: the checker decides, the elaborator builds.

Three things are made explicit here. Type-class constraints become dictionary-passing: each constraint the checker discharged is emitted as a global instance dictionary, a hidden dictionary parameter, or a projection of a superclass dictionary, and every method call becomes a field access on the resolved dictionary (see [type and effect inference](#type-and-effect-inference)). The `show` method itself is dictionary-dispatched like any other class method; separately, a few type-directed lowerings are resolved against the checker's span-keyed type table: the `print`/`println` and interpolation display, exponentiation (`^`), and indexing (`a[i]`) each read their operand's head type back and emit the matching builtin. And a `match` is lowered to a decision tree, the one part of elaboration large enough to be its own pass, below.

The output is `Expr<Core>`, the sugar-free phase in which the surface's sugar constructors are uninhabited (see [desugaring](#desugaring)), so a construct elaboration fails to translate is a compile-time type error in the compiler rather than a runtime fallthrough.

### Pattern-Match Compilation {#pattern-match-compilation}

A `match` is compiled to a decision tree (`src/core/elaborate/match_compile.rs`). The arms form a matrix whose rows are arms and columns are argument positions. The compiler selects a column, partitions the arms by the head of that column's patterns, and emits a test: a `Case` on the constructor tag of the scrutinee (the value being matched) for a constructor column, or a chain of equality tests for a scalar column. Wildcard rows form a default sub-matrix shared by the branches that fall through. A guarded arm compiles to a conditional that re-enters the remaining arms when the guard fails. Exhaustiveness, proven by the checker (see [patterns](./spec.md#patterns)), guarantees every scrutinee reaches an arm.

The splitting is easiest to see on a two-column match. Three rows, but the tree tests each component once: splitting on the first component partitions the rows, the wildcard row `(_, Nil)` falls through into the `Cons` branch as its default sub-matrix, and no pattern is ever examined twice:

{{#tabs }}

{{#tab name="Surface" }}

```prism,ignore
fn both_ready(a, b) =
  match (a, b) of
    (Nil, _) => False
    (_, Nil) => False
    (Cons(_, _), Cons(_, _)) => True
```

{{#endtab }}

{{#tab name="Decision Tree" }}

```text
case a of
  Nil  => False              -- row 1 wins; row 2's wildcard is dominated here
  Cons =>                    -- rows 2 and 3 remain: split on column b
    case b of
      Nil  => False          -- row 2, the wildcard row, as the default
      Cons => True           -- row 3
```

{{#endtab }}

{{#endtabs }}

## 9. Effect Lowering {#effect-lowering}

Effect lowering compiles away the `Handle`, `Do`, and `Mask` nodes of the core. An operation is delimited control (an effect suspended and resumed within a handler's scope): `Handle` is the delimiter, and the resumption `k` is the continuation captured between a perform site and its handler (see [effects and handlers](./spec.md#effects-and-handlers)). Lowering is a cascade of five strategies tried in a fixed order, each of which either lowers the whole program and succeeds or declines and returns `None`; the compiler takes the first that applies, so it reifies as little of the continuation as the program allows.

| pathway                           | applies when                                                                     | how much of `k` becomes manifest                               |
| --------------------------------- | -------------------------------------------------------------------------------- | -------------------------------------------------------------- |
| pure                              | no effect construct remains                                                      | nothing                                                        |
| evidence passing                  | every handler is tail-resumptive                                                 | nothing; operations force handler-clause thunks                |
| state threading and stream fusion | a uniform single-operation fold handler                                          | one small tag cell per early-terminating handler               |
| local monadification              | an effectful thunk escapes but its entangled component splits cleanly            | a reified tree inside that component only                      |
| free-monad fallback               | the effect escapes static tracking: dynamic, masked, multishot, self-referential | the whole continuation, as a heap-allocated `EPure`/`EOp` tree |

They are five compilations of that one mechanism, differing in how much of `k` they make manifest, from nothing to a heap-allocated tree. A check then confirms no effect construct survives. The chosen strategy is a pure cost decision, never observable in output, and it is pinned: `prism dump tier` prints a program's classification, and a committed manifest (`tests/tier_manifest.txt`) records the tier of every corpus program, so a refactor that silently defeats a fast path corpus-wide fails the perf gate by name rather than shipping as an invisible performance collapse. A tier change in either direction updates the manifest loudly, like a snapshot.

Two erasure pre-passes run before the strategy cascade, each recognizing a statically fixed handler shape and rewriting it to direct code, leaving everything else for the strategies. **Var erasure** (`src/core/effect_lower/erase_var.rs`) rewrites an escape-checked local `var` (a closed two-operation `State` handler, see [local mutation](./spec.md#local-mutation)) to a mutable cell: `get` becomes a cell read, `set` a cell write, and the block is wrapped in a fresh-cell allocation. It is sound exactly because the escape analysis proved the var's continuation is never resumed more than once, so the shared cell and pure-state copies agree; a multishot use disables it. **Control erasure** (`src/core/effect_lower/erase_control.rs`) rewrites the internal `break`/`continue`/`return` effects (see [imperative control flow](./spec.md#imperative-control-flow)), whose `never` handlers have fixed templates, back to direct control flow. It runs after var erasure, so a pure imperative loop has lost all of its effect operations by the time the cascade classifies it and falls into the trivial **pure** path (no effect constructs remain), compiling to a `musttail` loop with no per-iteration allocation.

**Evidence passing** is the fast path for tail-resumptive handlers (every clause calls `k` exactly once, in tail position, so the continuation need never be captured at all). Each operation is assigned a stable numeric id by sorting the operation names, and a call-graph fixpoint computes each function's _latent_ set, the operations still performed anywhere in its call-graph closure. An effectful function then gains one extra parameter per latent operation, `ev@<id>`, a thunk holding the active handler clause. Performing an operation forces its evidence thunk directly; a `handle` binds fresh evidence for its body's latent operations; and every call site appends the callee's evidence, in ascending id order, so the convention is positional and stable. A first-class thunk that escapes carries evidence parameters for its own latent operations, threaded at each force site. No continuation is reified and no per-operation cell is allocated. What evidence to thread where is computed by an interprocedural least-fixpoint flow analysis (`src/core/effect_lower/flow.rs`) that derives, for every function, the operation signature of the thunk it returns and of each thunk-valued parameter.

**State threading and stream fusion** is the path for a uniform single-operation handler, the shape a [stream](./spec.md#streams) consumer takes: a handler that folds every `emit` into an accumulator. Such a handler clause is rewritten to an accumulator transformer `\acc -> acc'`, and the producer it wraps becomes a loop that threads the accumulator through each emission instead of allocating a value per step. A consumer that can stop early, like `stake`, returns a two-state tag (continue or done) that the producer checks, so the loop exits without unwinding. This reifies one small tag cell per early-terminating handler and, like evidence passing, no free-monad cell, so a `smap`/`skeep`/`stake`/`ssum` pipeline allocates neither an intermediate list nor a per-operation cell.

```prism
{{#include ../examples/streams.pr}}
```

**The free-monad fallback** applies when an effect escapes static tracking: buried in data, dynamically applied, masked, genuinely multishot (a clause that resumes `k` more than once), or self-referential (a handler whose own body performs the effect it handles). A multishot handler forces this path because the two fast paths erase `k`, and a continuation invoked more than once must exist as a reusable value. Here the delimited continuation is reified in full: each computation becomes a tree of `EPure` and `EOp` cells threaded by `ebind` (shown below), and the continuation each `EOp` still owes is an explicit field a clause can hold, drop, or apply repeatedly.

That continuation is held as a _type-aligned queue_ (the Freer representation, [Kiselyov & Ishii, 2015](bibliography.md#kiselyov-ishii-2015)): a persistent catenable tree of Kleisli arrows whose append (`snoc`, one `ebind`) and join (`concat`, the splice at a forwarded operation) are O(1), and whose `uncons` re-associates the left spine, so a continuation extended by repeated `ebind` drains in amortized O(1) per step rather than the quadratic re-association a trampoline would redo on every bounce. The tree is never mutated, only rebuilt sharing its leaves, so a captured continuation stays cloneable for a multishot resume.

A `handle` becomes a generated driver function that case-dispatches the reified tree: an `EPure` runs the return clause, an `EOp` whose id the handler names and whose skip count is zero runs the matching clause, and any other `EOp` is re-emitted outward with a re-entry continuation, which is how an inner handler forwards an operation it does not catch.[^eop-skip] This is exactly the interpreter's dispatch (see [backends](#backends)), so the two agree by construction.

[^eop-skip]: An `EOp` carries a `skip` field, its mask depth, the number of matching handlers it must still bypass; a `mask` driver increments it and the handler driver only fires when it is zero.

Each `EOp` allocation bumps the `PRISM_EFFOP_STATS` counter, so the fallback's cost is observable, and a default-on warning (silenceable with `PRISM_QUIET`) names the functions that lost fusion and the cause when a program takes this path, so a pipeline meant to stay fused can be steered back. The generated drivers are closed by construction: a per-handler driver takes exactly its clauses' captured free variables as parameters, and the fixed-binder templates (`ebind`, the mask drivers) use a reserved binder band and never nest, so a binder cannot capture a free occurrence.

Lowering is kept as local as possible, the **local monadification** tier above the whole-program fallback: when an effectful thunk escapes, only the connected component entangled with it (closed over the call graph, but leaving pure closure-inert helpers shared, and over shared operations) is converted to the free-monad form, while unrelated functions stay on their fused paths, provided the component's operations are disjoint from the rest; when the split is not clean lowering falls back to converting every effectful function together. A convention-boundary check, run in both modes, validates the split and turns a missed monadic/direct boundary into a compile-time internal error.

**Constant-stack driving** changes how a closed handler on this fallback is run, not what it reifies. By default such a handler is driven by a single self-tail-recursive loop, `{n}@region`, rather than a pair of mutually recursive driver functions: the loop case-dispatches the same `EPure`/`EOp` tree but re-enters itself by a `musttail` self-call on the resumed continuation, so an iterative or deeply nested resumption runs in constant native stack where the mutually recursive driver grew it per step. Two clause shapes qualify. A tail-resumptive clause (every `resume` is the head of a tail application) re-drives the operation's continuation queue with `qApply`.[^fn-answer-state] The reification is unchanged, so the per-operation `EOp` cost stays and the only zero-cell routes remain the evidence and state paths above; the gain is purely that a parameter-passing loop no longer overflows (the bounded-stack performance gate pins a million-iteration `State` loop completing in a 2 MB stack). An open handler, a multishot or escaping resume, or any clause outside these shapes keeps the mutually recursive driver, whose `qApply` the loop reuses, so the free-monad machinery is the substrate it drives rather than a thing it replaces. This is on by default and reverts under `PRISM_NATIVE_EFFECTS=0`; the interpreter oracle's whole-corpus parity holds byte-for-byte either way.

[^fn-answer-state]: A function-answer state clause, the parameter-passing pattern whose answer is a function `S -> A` (`rd(u, r) => \s -> r(s)(s)`, `wr(v, r) => \s -> r(())(v)`) applied once at the handler's use site, threads the state in an accumulator parameter and folds that use-site application into the loop's entry, so the pending-apply chain that would otherwise grow the stack per iteration lives in the accumulator instead.

```text
{{#include ../examples/free-monad.txt}}
```

The example below exercises this path: an inner handler catches `Log` and forwards `raise` outward to an `Exn` handler, the two effects interleaving across the nesting.

```prism
{{#include ../examples/eff_forward.pr}}
```

The fallback reifies one cell per pending operation, so its cost is proportional to the operations in flight; the fast paths avoid it where they apply.

### 9.1 Concurrency {#concurrency}

Prism has no built-in threads, event loop, or async runtime. Concurrency is this free-monad fallback applied to one handler: the `Concurrent` standard library (`lib/std/Concurrent.pr`) defines an `Async` effect and a handler, `run_async`, that schedules fibers cooperatively. The schedule is deterministic (fixed by the program's structure, not a clock), the scheduler keeps no mutable state, and it runs in constant native stack. The full API is the [`Concurrent`](./stdlib/concurrent.md) reference; this section is how the pieces above realize it.

The `Async(a)` effect is parametric in the fibers' shared result type `a`, with operations `fork(() -> a ! {Async(a) | e}) : Fiber`, `yield`, `await(Fiber) : a`, `cancel(Fiber)`, and a buffered FIFO `channel`/`send`/`recv`; sharing one result type is what lets a single run queue hold every fiber without existentials. With no shared mutable cell the handler cannot poke a run queue in place, so it reifies each step instead: a `step` function runs a fiber body to its next `Async` operation and returns a `Cmd` (`Forked`, `Yielded`, `Awaited`, `Cancelled`, `Opened`, `Sent`, `Recving`, or `Finished`) with the fiber's continuation captured inside, and a pure `drive` loop interprets one `Cmd` at a time, threading an immutable `Sched` record that holds the run queue, the finished results, the parked awaiters, the cancelled set, and the channel buffers. A fiber blocks by having its continuation parked in `Sched` and wakes by being moved back onto the queue; because every continuation escapes into `Sched` the program takes the free-monad path above, and under constant-stack driving the loop runs an unbounded number of steps without growing the native stack.

A fiber performs more than `Async`, so the reified `Cmd` must store continuations that perform arbitrary effects, and its effect row is therefore a [row-kinded parameter](#kinds-and-rows), `type Cmd(a, e : Row)`, threaded through `Cmd`, `Sched`, and the scheduler functions to make the whole library polymorphic in the fibers' effects. The handler's type is `run_async : forall a e. (() -> a ! {Async(a) | e}) -> a ! {e}`, discharging `Async` and leaving `e`, so fibers that perform `IO` yield a run that performs `IO` and fibers that perform a capability `E` yield a run that performs `E`, written once for every row. This stays sound through the ambient-row discipline of the type checker: at a `fork` the fiber's row variable is tied to the caller's ambient row rather than opened fresh, so forking a fiber that performs `E` forces `E` into the caller's row and out through `run_async`, and a fiber cannot perform an effect no handler was demanded for. It is the same forwarding the `eff_forward.pr` example shows for nested handlers, now through the scheduler, a fiber's capability tunnelling past the non-handling scheduler to an outer handler exactly as an `EOp` the driver does not name is re-emitted outward; that is the capabilities-as-handlers pattern, where a capability is granted with an ordinary `handle` around `run_async`.

The structured wrappers are ordinary functions over these operations: `scope(tasks)` forks a list of fibers and joins them all so none outlives the call, `cancel(f)` records the fiber id in `Sched` so `run_next` skips it when it would next be dequeued, and a `channel` carries the shared type `a` with `send` handing its value to a waiting receiver or buffering it and `recv` taking the buffer head or parking the fiber, the same reify-and-thread machinery as `await` keyed by a channel id rather than a fiber id. Because the schedule is a pure function of the program a run is reproducible, and composed with the [`Replay`](./stdlib/replay.md) handlers a concurrent run that draws randomness or reads input records into a trace and replays to the identical result, its capability effects tunnelling out of `run_async` and into `record`/`replay` like any other. The worked programs are [`examples/async.pr`](https://github.com/sdiehl/prism/blob/main/examples/async.pr), [`examples/channels.pr`](https://github.com/sdiehl/prism/blob/main/examples/channels.pr), [`examples/async_capability.pr`](https://github.com/sdiehl/prism/blob/main/examples/async_capability.pr), the map-reduce pipeline in [`examples/pipeline.pr`](https://github.com/sdiehl/prism/blob/main/examples/pipeline.pr), and [`examples/replay_concurrent.pr`](https://github.com/sdiehl/prism/blob/main/examples/replay_concurrent.pr).

## 10. Reference Counting and FBIP Reuse {#reference-counting-and-fbip-reuse}

Reference counting runs after effect lowering, over the handler-free core, so it counts evidence parameters and any reified cells as ordinary values. Memory is managed by Perceus-style reference counting ([Reinking et al., 2021](bibliography.md#reinking-2021); `src/core/fbip.rs`): every parameter and binding is owned and consumed exactly once on every control-flow path from its binding to the end of its scope; a second use inserts a `dup` and an unused value inserts a `drop`. Perceus places these operations precisely rather than conservatively at scope exit, which frees a cell at the earliest point the reuse pass below can claim it. Closure captures are borrowed (read without being consumed) and duplicated before a consuming use, as is a `borrow` parameter (see [declarations and programs](./spec.md#declarations-and-programs)). The parameters a function borrows are recorded as a per-function bit vector, its interprocedural _borrow signature_, which every caller consults to place its `dup`/`drop` correctly. Because that signature crosses call sites, it is one of the analyses that complicates the move to separate compilation (see [name resolution and modules](#name-resolution-and-modules)).

The reuse pass then turns drops into in-place updates. When a uniquely owned scrutinee is dropped and the continuation rebuilds a constructor of the same or smaller size, the `drop` becomes a scoped reuse node, `WithReuse { token, freed, body }`: it frees the cell once and binds a _reuse token_ over the continuation, and the rebuild spends that token with an in-place `Reuse(token, ctor)`, so `map` and tree rebuilds mutate the spine in place. The token is a binder that only a `Reuse` may name, and the rewrite spends it on every control path or declines wholesale (keeping the safe no-reuse body), so freeing a cell once and spending its token at exactly one allocation are well-formedness properties of the term rather than a condition checked afterward.

An independent verifier re-checks that output. `fbip::balanced` re-simulates the inserted `dup`, `drop`, and reuse operations as a linear-token machine: each owned binding starts with one token, a `dup` adds one and a `drop` or consuming use removes one, a use may never drive the count below zero, every binding must reach zero before leaving scope, the two arms of a branch must agree, and a `WithReuse` grants its token exactly one credit the body must spend. It runs over the reference-counted core on every interpreter entry and across the whole example and test corpus, so an under-`dup`, an over-`drop`, or an unbalanced branch left by the insertion pass surfaces as an internal error rather than a leak or a double free at run time. Core Lint adds the dual direction under `PRISM_CORE_LINT` (see [lint, telemetry, and parity](#lint-telemetry-and-parity)): it rejects a reuse token spent more than once on any path, the over-spend the balance check does not see.

The `fip`/`fbip` annotations (see [declarations and programs](./spec.md#declarations-and-programs)) are the fully-in-place discipline of [Lorenzen et al. (2023)](bibliography.md#lorenzen-fp2-2023), here static checks layered on these passes. `fbip` proves zero fresh allocation and a call-graph closure over annotated, allocation-free callees. `fip` adds two further properties: linearity (each owned binding is consumed at most once, checked on the source term, with scalars exempt because adjusting the count of an unboxed word costs nothing) and bounded stack. The tail-call and tail-modulo-cons (a tail call whose result is wrapped in one constructor) classification (`src/core/tailrec.rs`) is shared with codegen, so an accepted `fip` function always lowers to a loop; acceptance never outruns what the backend emits.

```prism
{{#include ../examples/fip_list.pr}}
```

This turns a familiar library idiom into a checked one. A mutable structure presented behind a pure interface, a buffer or array updated in place under an API that appears to return a fresh value, is written by hand throughout functional libraries (OCaml's Base and Core are full of such in-place blits), and its correctness rests on the author having reasoned that no other reference can observe the mutation. Prism derives the idiom from ownership rather than trusting it: the reuse pass updates in place exactly when the scrutinee is uniquely owned, and the independent `fbip::balanced` verifier re-establishes that on every control path before anything runs. The hand-written version hopes the aliasing is safe; here the safety is a property of the term the compiler has already proved.

## 11. Backends {#backends}

Prism has three backends over one core: a tree-walking interpreter that is the reference oracle, and two native backends that must match it byte for byte. The native backends share a single generic emitter, so the differences below are narrow.

### 11.1 The Interpreter {#the-interpreter}

The tree-walking interpreter (`src/eval/`) is a flat CEK (control, environment, continuation-stack) machine. Pending work lives on an explicit heap stack of frames rather than the host call stack, so object-program recursion never overflows it. A frame is one of: `Bind` (await a result, then continue with the rest of a sequence), `Args` (await a function before applying it), `Handle` (an installed handler), `Mask` (a masking frame), and `Restore` (unwind a name binding; a `Restore` already on top marks tail position, which is where the machine recognizes a tail call).

This machine makes the delimited continuation of [effects and handlers](./spec.md#effects-and-handlers) concrete: performing an operation searches the frame stack outward for a matching `Handle`, decrementing the skip count past masked frames, and the _captured continuation_ is exactly the slice of frames between the `do` and that handler, the handler included. Resuming pushes a clone of that slice back onto the stack, so the same resumption can be pushed again, which makes `k` multishot. The native backends realize this same frame stack in the runtime as a chain of counted frame cells (`runtime/prism_kont.c`) linked by a `next` field, one cell per `Bind`, `Handle`, and `Mask` frame; resuming splices a clone of the delimited slice onto the current chain with `prism_kont_splice`, which copies and relinks the slice in two iterative passes, so a deep continuation is captured and re-entered in O(1) C stack regardless of its depth, and an abandoned continuation is freed through the same iterative refcount worklist (see [reference counting](#reference-counting)). The free-monad backend reifies this same frame slice as the `k` closure of an `EOp` (see [effect lowering](#effect-lowering)); evidence passing never materializes it.

### 11.2 The Shared Emitter {#the-shared-emitter}

Both native backends drive one generic emitter (`src/codegen/emit.rs`); the whole of its dependence on the target is a single Rust trait, `Isa` (instruction set architecture), the abstract backend interface. The emitter owns every decision with semantic content: case dispatch, closure and constructor allocation and reuse, reference-count placement, and tail-call lowering.[^tailcall-variants] `Isa` itself is only instruction _spelling_: about forty leaf methods (`const_int`, `bin`, `load`, `store`, `call`, `switch`, `ret`, and so on) that know nothing of what a Prism program means. The LLVM backend spells them through inkwell; the MLIR backend writes them as textual `llvm`-dialect ops. The two targets are structurally identical but for one point, how control flow merges: LLVM joins branches with `phi` nodes (a value chosen by which predecessor arrived), MLIR with block arguments (the value passed to the successor block). The emitter abstracts that single difference behind `jump_merge` (hand a value to a merge point) and `open_merge` (open the block that receives it), so the shared Core walk is oblivious to which discipline the backend below it uses.

[^tailcall-variants]: A self-tail call of equal arity becomes a `musttail` loop, and a constructor- or accumulator-shaped tail call, one whose result feeds a constructor or an integer accumulator, becomes a destination-passing loop that writes its result into an address passed as a hidden parameter rather than returning it, using the same classification the `fip` check reads (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)).

The layering is worth stating explicitly, because it is where the design's leverage lives. The emitter walks the fully-lowered Core (after effect lowering and reference counting) and, node by node, mints an SSA operand _name_ for each result and drives `Isa` with those names; `Isa` never sees a Core node, and no third IR sits between the two. So codegen is a single Core walk that emits a stream of instruction calls: `Comp`/`Value` in, `String` operand names threaded through a register map, `Isa` calls out, target text at the leaves. Every Core-level judgment (evaluation order, allocation, reference counting, tail-call and reuse classification) is made once in that walk, above `Isa`, which is why a backend inherits all of it and spells only instructions.

A new target is therefore a Rust `impl Isa` and nothing else. Retargeting Prism to some other machine, a real ISA or perhaps a 6502 or a Minecraft redstone computer, is writing those forty methods and inheriting the calling convention, reference counting, pattern-match trees, tail-call loops, and in-place reuse unchanged, never restating what the language does. The split earns two things: the two shipped backends come out byte-identical by construction, so the parity gate (see [verification](#verification)) holds for free rather than by reconciling two hand-written code generators, and a backend becomes an afternoon of instruction spelling rather than a second implementation of the compiler.

### 11.3 LLVM {#llvm}

The LLVM backend (`src/codegen/llvm.rs`) implements `Isa` over inkwell, emitting LLVM IR that `clang` compiles and links against the runtime. This is the default native path.

Prism runs no LLVM optimization passes itself: it verifies the module, writes bitcode, and hands the rest to `clang -O2 -flto=thin`, compiling the emitted bitcode and the C runtime in one invocation so ThinLTO inlines the runtime into the generated code. Every emitted function carries `nounwind` (Prism has no exceptions and this backend emits no invokes or landingpads), which lets the `-O2` pipeline drop unwind tables and treat each call as non-throwing. Three knobs tune this last step, all distinct from the Core-to-Core `-O` of [optimization](#optimization): `--backend-opt <0|1|2|3|s|z>` (or the `PRISM_BACKEND_OPT` env var) sets the `clang -O` level, defaulting to `2`; `PRISM_CC` picks the compiler (default `clang`); and `PRISM_CC_FLAGS` appends arbitrary flags after the defaults, so a trailing `-O0` wins or `-march=native`/`-g` can be added. ThinLTO stays on at every level, since it is what folds the runtime into the program.

One store bridge gap remains. `StoreGet`, `StorePut`, and `StoreHas` are interpreter-only today; the native backend rejects them with a diagnostic instead of emitting unresolved runtime calls. Native store calls wait on the runtime store ABI.

Native LLVM builds also retain the metadata needed to name generated code by the same content identity the interpreter's [kont envelope](#the-kont-envelope) uses. The shipped pieces are a `prism_native_kont_table` section with scheme, bundle digest, and symbol-to-definition-hash rows; an exact function-pointer table for reachable functions; and a `prism_native_kont_state_map` keyed by native symbol, definition hash, Core name, and arity.[^abi-word-slots]

[^abi-word-slots]: State-map version 1 uses `slot-format prism-native-abi-word-v1`: each row names the logical entry ABI words (`arg0=%a0:word`, `arg1=%a1:word`, ...), matching the backend convention that every Prism value crosses generated function boundaries as one `i64` word.

When `PRISM_NATIVE_KONT_FRAMES` is enabled, generated functions also maintain a bounded thread-local shadow stack of those entry ABI words, and musttail calls retarget the top shadow frame before the LLVM `musttail` call so the instrumentation does not invalidate the verifier's tail-call shape. The runtime can expose raw state-map bytes, resolve a known entry pointer or captured program counter back to a definition hash, walk native frames into stable symbol-plus-PC-offset anchors, and format any shadowed entry values in a native-kont manifest. A restricted resume primitive can re-enter an exact generated function entry by native symbol and captured ABI words through the retained pointer table, refusing arity mismatches and arities outside the small fixed C-call family.

What does not ship is arbitrary native continuation resume. The frame metadata identifies code positions and entry values; it does not serialize mid-basic-block locals, stack slots, or registers. Mid-basic-block stack/register resume remains deliberately unsupported.

The instruction-level mapping this backend drives `Isa` through, worked node by node, is [its own section](#lowering-core-to-llvm), since the MLIR backend emits the identical shape and the mapping is worth reading independent of either target.

### 11.4 MLIR {#mlir}

The MLIR backend (`src/codegen/mlir.rs`) implements the same `Isa` by writing textual MLIR in the `llvm` dialect. Sharing the emitter makes its output byte-identical to the LLVM backend's, which the parity gate (see [verification](#verification)) enforces.

It is deliberately second-class: it emits textual `llvm`-dialect MLIR and stops there, touching none of MLIR's other dialects, passes, or its C++ builder infrastructure, so it is really a parity check on the shared emitter rather than a distinct code path with its own leverage. A first-class MLIR backend, one that builds real ops through the C++ API and lowers through the dialect pipeline, waits on one of two things, whichever comes first: Rust bindings to the MLIR C++ API mature enough to link against the exact LLVM version Prism pins, or a concrete reason to want the dialects at all, most likely emitting Prism to GPU kernels (a CUDA or `gpu`-dialect target). Until one of those lands, textual output is enough to keep the seam honest.

### 11.5 WebAssembly {#webassembly}

The compiler front end and the interpreter also compile to WebAssembly (`src/wasm.rs`), so Prism type-checks and runs in the browser. This target hosts the interpreter, not the native code generators; the LLVM and MLIR backends are absent there. The web bundle serves the playground, the in-browser REPL, and the gallery residents from this one target: the boids scrubber, double pendulum, branching timelines, chaos counter, schedule map, teleport demo, content-addressed Merkle graph, and incremental graph. The Determinism Machine residents are not separate semantics. Each is a small wasm export over ordinary Prism examples: scrubbers replay a deterministic trace to frame `N`, branching continues from a serialized boids frame, chaos batches seeded schedules and checks one final-state hash, the schedule map renders individual seeded interleavings as navigable nodes over that same export, and teleport moves a `kont` envelope only over same-origin browser contexts, with receiver readiness, transfer ids, and code-hash agreement checked before resume.

That same-origin boundary is intentional. The demo proves migration of a running computation between contexts that already share the same origin and bundle; it does not claim cross-origin or cross-stranger execution. Running an envelope from an untrusted peer is deferred to a typed `Mobile` envelope with explicit receiver capabilities and a distribution trust model.

## 12. Lowering Core to LLVM {#lowering-core-to-llvm}

The translation from core to instructions is narrow because the machine underneath it is narrow. By the time the backend runs, effect lowering has erased every `Handle` and `Do` (see [effect lowering](#effect-lowering)), reference counting has inserted every `Dup` and `Drop` (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)), and the [value representation](#value-representation) has collapsed every type to one machine word. So the emitter faces only two things to lower: data laid out in cells, and computation as straight-line calls and branches over `i64` words. It emits no struct types and no read barriers; one `i64` is the type of every value, and `inttoptr`/`ptrtoint` reinterpret that word as a cell pointer only where a field must be reached. Because this is the shared emitter's mapping, the MLIR backend emits the identical shape in the `llvm` dialect, byte for byte.

A **value** is an immediate or a pointer, both an `i64`. An `Int` literal is the immediate `(n << 1) | 1`, so the literal `0` is the constant `1`; `Bool`, `Unit`, and the fixed-width words are immediates too. A `Ctor` allocates: `prism_alloc(arity)` returns a cell whose header the emitter fills by storing the tag at offset 8, then storing each field from offset 24 upward, and the cell's `ptrtoint` is the value word. A `Case` is the inverse and asks for exactly one shape: reinterpret the scrutinee as a pointer, `load` its tag from offset 8, and `switch`, one block per constructor plus a default that calls `prism_match_error` and falls into `unreachable` (the exhaustiveness the checker already proved, made a hard trap rather than a silent fallthrough). Each arm reaches its bound fields by `getelementptr` and `load`, and drops or retains them as the surrounding reference-count nodes direct. All of `unwrap` is one such switch (the LLVM tab is the emitter's own output at `-O0`, unoptimized so the function survives as its own definition; with optimization the backend inlines a leaf this small into its caller):

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/lower_unwrap.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/lower_core.txt}}
```

{{#endtab }}

{{#tab name="LLVM" }}

```llvm
{{#include ../examples/lower_llvm.txt}}
```

{{#endtab }}

{{#endtabs }}

The arms _are_ the reference-count discipline written into the instruction stream: the `Som` arm retains the field it returns, which now escapes its cell, and releases the scrutinee it consumed; the `Non` arm returns an immediate the collector ignores, so it only releases the scrutinee. `prism_rc_inc`/`prism_rc_dec` are no-ops on an immediate (checked in the runtime), so the emitter inserts them uniformly and pays nothing for scalars.

The rest falls out along the same grain. `Bind`/`Return` are A-normal form made literal: a `Bind` names a result as an SSA value, control runs straight down between calls, and `Return` yields the value word. A `Prim` on immediates unmasks the tag bit, applies the native `add`/`mul`/`icmp`, and re-tags, with an overflow check that falls back to the bignum runtime routine (see [integers](#integers)); the `I64`/`U64` lanes are raw `i64` machine ops with no tag. `If` is a `br`. A top-level function is a `define i64 @prism_<name>(i64, ...)`, a `Call` is a direct `call`, and an `App` of a closure goes through a generated `apply_<arity>` trampoline (closures are below); a `Thunk` is a nullary closure and `Force` runs it. A tail call becomes a `musttail` self-loop or a destination-passing loop, the classification the [shared emitter](#the-shared-emitter) owns. Every `define` carries `nounwind`, because there is nothing to unwind: only values, cells, and calls.

A dozen node-to-instruction rules cover almost everything a program is made of:

| Core node          | LLVM                                                                                          |
| ------------------ | --------------------------------------------------------------------------------------------- |
| `Int n`            | the tagged immediate `2n + 1`                                                                 |
| `Ctor tag [f..]`   | `prism_alloc(arity)`, `store` tag at +8 and fields from +24; the cell pointer is the value    |
| a field read       | `inttoptr`, `getelementptr` to the offset, `load`                                             |
| `Case`             | `load` the tag at +8, then `switch`; the default calls `prism_match_error` then `unreachable` |
| `If`               | `br i1`                                                                                       |
| `Prim +` `-` `*`   | untag, native `add`/`sub`/`mul`, re-tag, with a `prism_rt_int_*` call on overflow             |
| `Prim ==` `<`      | `icmp` (a `prism_rt_int_cmp` call where a bignum is possible)                                 |
| `Bind` / `Return`  | an SSA name / the returned `i64` word                                                         |
| `Call f`           | a direct `call i64 @prism_f(...)`                                                             |
| `App` (a closure)  | a `call` to a generated `apply_<arity>` trampoline (closures, below)                          |
| a self-tail `Call` | `musttail call`, which becomes a branch (below)                                               |
| `Force` a `Thunk`  | a `call` of a nullary closure                                                                 |
| `Dup` / `Drop`     | `call @prism_rc_inc` / `@prism_rc_dec`, a runtime no-op on an immediate                       |

**Function calls and tail recursion.** A `Call` is a direct call; the case worth watching is an accumulator loop. A self-tail call of equal arity is emitted `musttail`, which LLVM turns into a branch back to the function's own entry, so a loop written as recursion runs in constant stack with no call frame at all. The immediate arithmetic (untag, operate, re-tag, with the bignum runtime only on overflow) is elided here to keep the shape legible:

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/lower_sumto.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/lower_tail_core.txt}}
```

{{#endtab }}

{{#tab name="LLVM" }}

```llvm
{{#include ../examples/lower_tail_llvm.txt}}
```

{{#endtab }}

{{#tab name="ARM64" }}

```asm
{{#include ../examples/lower_tail_asm.txt}}
```

{{#endtab }}

{{#endtabs }}

The assembly is the payoff: there is no `bl _prism_sumto`. The recursive tail call is the `b Ltail` branch to the loop header, so a million-deep `sumto` never grows the C stack.

**Effects, handlers, and continuations.** By the time the backend runs no `Do` or `Handle` survives: [effect lowering](#effect-lowering) has discharged them. In the common case it fuses the handler into ordinary calls by _evidence passing_, threading each clause as an extra parameter, so a `perform` becomes a call on that evidence and a handler costs exactly a function call. The `State` handler lowers with `get`/`put` erased into calls on an evidence value, the state threaded as a plain argument, and no allocation:

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/eff_state.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/lower_eff_core.txt}}
```

{{#endtab }}

{{#tab name="Lowered" }}

```text
{{#include ../examples/lower_eff_lowered.txt}}
```

{{#endtab }}

{{#endtabs }}

When a handler cannot resolve to compile-time evidence, because a clause captures its continuation and may resume it more than once (search, a generator, a fiber scheduler), lowering falls back to the free-monad form: a `Do` builds a counted `EOp` cell whose `k` field _is_ the captured delimited continuation, and resuming splices a clone of that frame slice back onto the running chain with `prism_kont_splice` in O(1) regardless of depth ([the interpreter](#the-interpreter) realizes the same chain). A fiber is thus not a backend construct at all: it is exactly this captured continuation, suspended at a `yield` and re-entered by its scheduler, so multishot handlers and cooperative concurrency are one mechanism.

**Polymorphism and type classes.** Prism is fully type-erased: the checker verifies types and effect rows and then discards them, so Core and everything downstream is untyped and no value carries its type at run time (a cell's tag is a constructor tag, never a type tag; the only run-time discrimination is the immediate/pointer low bit and that constructor tag). Because every value is therefore one `i64`, a generic function has a single machine-code body that serves every instantiation: Prism does not monomorphize for layout the way a C++ template or a Rust generic does, so `map` is compiled once, not once per element type. Type classes ride the same evidence mechanism as effects: a constraint becomes a _dictionary_, a record of the instance's methods, passed as an ordinary value argument, and a method call is a field load plus an indirect call on it. The `Specialize` pass (see [specialize](#pass-specialize)) then clones and inlines that dictionary away wherever the instance is known at the call site, so dictionary passing is the always-correct fallback and specialization is speed layered on top, never a prerequisite for compiling. One `i64`, one body, and dictionaries for whatever polymorphism survives.

**Closures.** A lambda is lifted to a top-level function that takes its free variables ahead of its parameters, and a closure _value_ is a heap cell holding just those captured variables, tagged by which lambda it is; no code pointer is stored in the cell. Application is defunctionalized: a `Call` to a statically known function is direct, but an `App` of an unknown closure calls a generated `prism_apply_<arity>` trampoline that recovers the environment from the cell and dispatches on its tag to the lifted body. Higher-order code is therefore ordinary tagged data and a switch, in keeping with the uniform representation:

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/lower_adder.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/lower_clo_core.txt}}
```

{{#endtab }}

{{#tab name="LLVM" }}

```llvm
{{#include ../examples/lower_clo_llvm.txt}}
```

{{#endtab }}

{{#endtabs }}

**In-place reuse (FBIP).** The reuse pass (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)) turns match-then-rebuild, the shape of every functional update, into in-place mutation when the matched value is uniquely owned. It emits a `reuse_token` on the dead scrutinee and a `reuse_alloc` for the new constructor: `prism_reuse_token` hands back the cell's shell when its refcount is 1 and null otherwise, and `prism_reuse_alloc` overwrites that shell or falls back to a fresh allocation. So a `bump` mapping over a uniquely-owned list rewrites each node's fields with `store`s and allocates nothing, while the identical source over a shared list transparently copies:

{{#tabs }}

{{#tab name="Surface" }}

```prism
{{#include ../examples/lower_reuse.pr}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/lower_reuse_core.txt}}
```

{{#endtab }}

{{#tab name="LLVM" }}

```llvm
{{#include ../examples/lower_reuse_llvm.txt}}
```

{{#endtab }}

{{#endtabs }}

This is the whole of Prism's "functional code, mutable performance": the emitter never decides to mutate, it always emits reuse, and the refcount decides at run time.

**Tail calls, and where the C stack still is not enough.** The `musttail` loop above fires for a self-tail call of equal arity, and a constructor- or accumulator-shaped tail call becomes the destination-passing loop of [the shared emitter](#the-shared-emitter). But a tail call through a closure trampoline or to an unknown function cannot be `musttail` under the borrow calling convention (argument ownership is the caller's to settle), so it returns normally and could in principle grow the C stack. That is exactly why the delimited continuations of [the interpreter](#the-interpreter) are realized natively as a heap chain of frame cells rather than left on the hardware stack: a resumption, a deep generator, or a fiber that suspends and resumes thousands of times rides that heap chain, spliced in O(1) by `prism_kont_splice`, so the one place the C stack would overflow is the one place Prism declines to use it. Self-recursion is a loop, open control is heap-reified, and nothing counts on unbounded C stack.

## 13. The Runtime {#the-runtime}

The C runtime (the module family under `runtime/`: memory and reference counting, strings, bignums, floats and the vendored libm, effects, sorting, arrays, byte buffers, typed buffers, continuations, and IO) is linked with the code each backend emits. It assumes an LP64 target (64-bit pointers and `long`) and uses `mimalloc` when available. The data representation below is shared by the backends and the runtime.

### 13.1 Value Representation {#value-representation}

A Prism value is one 64-bit word, tagged by its low bit, so that a single representation serves both scalars and pointers under polymorphism:

```text
{{#include ../examples/value-repr.txt}}
```

A float does not fit the immediate scheme, so it is _boxed_: wrapped in a one-field cell holding the raw double bits, which are read back out (unboxed) at every float operation. Boxing makes a float field self-describing, so the collector frees it without interpreting its payload.

### 13.2 Cell Layout {#cell-layout}

A heap cell is a three-word header followed by its fields.[^cell-bytes-guard]

| Offset | Field      | Meaning                                                           |
| ------ | ---------- | ----------------------------------------------------------------- |
| 0      | `refcount` | number of live references to this cell                            |
| 8      | `tag`      | constructor tag; reserved values mark String and bignum cells     |
| 16     | `arity`    | number of fields (or byte length for a String)                    |
| 24     | `fields`   | `arity` words, each a value or pointer (UTF-8 bytes for a String) |

Constructor tags follow declaration order (for `Option(a) = None | Some(a)`, `None` is 0 and `Some` is 1). Two tag values are reserved, marking cells whose payload is raw bytes or limbs rather than child values:

| Tag          | Cell                                      |
| ------------ | ----------------------------------------- |
| `0x53545200` | String (UTF-8 bytes)                      |
| `0x42494700` | bignum (limbs; see [integers](#integers)) |

The collector and the reuse pass (see [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse)) read the tag to avoid recursing into them.

[^cell-bytes-guard]: Every cell allocation routes its size through one overflow-checked chokepoint, `prism_cell_bytes`, which rejects a negative field count and aborts (via `__builtin_add_overflow`/`__builtin_mul_overflow`) if the header-plus-payload word count, or its conversion to bytes, would overflow `size_t`, so a corrupt or oversized arity can never produce an undersized allocation.

### 13.3 Reference Counting {#reference-counting}

`prism_rc_inc` and `prism_rc_dec` take the raw value word and return immediately on an immediate or unit, so counting is a no-op on non-cell values. Decrement to a nonzero count just decrements. Decrement to zero frees the cell, but freeing is _iterative_, not recursive: the dead cell's now-zero refcount word is reused as a link field in an intrusive worklist of cells pending free, so a structure of any depth is reclaimed in constant auxiliary space without growing the C stack.[^rc-hour] A string or bignum tag short-circuits the child traversal.

[^rc-hour]: Unlike a collector, which comes for your values at an hour of its own choosing, reference counting frees each one at a moment fixed in advance and knowable from the source. Whether it is more restful to know exactly when everything you have allocated will die is not addressed here.

### 13.4 In-Place Reuse {#in-place-reuse}

The reuse pass of [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse) emits two runtime calls. `prism_reuse_token(v)` inspects a cell about to be dropped: if it is uniquely owned (refcount 1), it drops the cell's children and returns the shell as a token, leaving the live-cell count untouched; otherwise it decrements and returns null. `prism_reuse_alloc(token, n)` overwrites the token's header for the new constructor when the token is non-null, and falls back to a fresh allocation when it is null. A uniquely owned spine is therefore mutated in place, and a shared one transparently copies.

### 13.5 Integers {#integers}

A small integer is an immediate, `(n << 1) | 1`. An operation whose fixed-width result would overflow promotes to a _bignum_: a cell tagged `0x42494700` storing the value in sign-magnitude form (sign and magnitude kept separate).[^bignum-limbs] Each surface arithmetic operation takes a fast path on two immediates with a checked-overflow primitive and falls back to magnitude routines (add, subtract, multiply, and a shift-subtract long division) that renormalize the result, demoting back to an immediate when it again fits. The surface `Int` is this unbounded integer. The `I64` and `U64` lanes are raw machine words and wrap rather than promote.

[^bignum-limbs]: Its header word is a signed limb count whose sign is the value's sign; the magnitude follows as that many little-endian `u64` limbs (base-2^64 digits) with no leading zero limb. Zero is a count of zero with no limbs.

### 13.6 Strings {#strings}

A string is a cell tagged `0x53545200` whose field words hold its UTF-8 bytes inline, length-prefixed by the arity word and NUL-terminated for C interop. Each string the program builds, including a literal at each use, is a counted cell, so the leak counter (see [instrumentation](#instrumentation)) accounts for strings like any other allocation. Two indexing families coexist: `char_at`, `substring`, and `str_len` work in Unicode codepoints, walking the UTF-8 encoding (and so are O(n)), while `byte_at` and `byte_len` give O(1) raw-byte access for a scanner or hash.

### 13.7 Instrumentation {#instrumentation}

Three environment-gated counters report to stderr at exit, leaving stdout (the parity-checked channel) untouched. `PRISM_CHECK_LEAKS` reports the live-cell balance, which a clean run drives to zero. `PRISM_REUSE_STATS` reports how many cells the reuse pass rewrote in place. `PRISM_EFFOP_STATS` reports how many free-monad `EOp` cells were allocated, which the performance gate asserts is zero on the fusion corpus.

### 13.8 Growable Arrays {#growable-arrays}

The growable `Array(a)` (see [the standard prelude](./spec.md#the-standard-prelude)) is an ordinary cell, `{ rc, tag 0, arity cap+1, len, elem0 .. }`, with the length word stored odd-tagged (low bit set, so the collector skips it as an immediate per [value representation](#value-representation)) and unused slots held at zero. Because it is a normal cell, reference counting recurses into its live elements with no special case. Every array operation borrows its array argument. `array_get` returns a counted element; `array_set`, `array_push`, and `array_pop` write in place when the array is uniquely owned (refcount 1) and copy otherwise, so functional array code runs as mutation exactly when ownership permits. `array_push` doubles the capacity when full, making appends amortized O(1). The prelude's `HashMap` is a separate-chaining hash table layered on this array, with an FNV-1a hash written in Prism (so iteration order is a deterministic function of the inserts); it is library code, not a runtime primitive.

### 13.9 Primitive Sort {#primitive-sort}

`sort` is a runtime primitive (`prism_sort_prim`) that borrows a list and returns it sorted, dispatched on a key kind. Arbitrary-precision `Int` keys use a bignum-aware stable bottom-up merge sort, ping-ponging between two buffers; fixed-width keys use a radix sort over a derived key. When the input spine is uniquely owned, the sorted heads are written back into the existing cells with no allocation; a shared spine is copied with its elements shared. The `Cons` and `Nil` tags are read off the input spine, so no list layout is baked into the runtime.

### 13.10 Input, Output, and Randomness {#input-output-and-randomness}

The runtime provides the impure primitives. The nondeterministic _inputs_ are no longer untracked builtins: they are the raw `prim_*` calls (`prim_read_int`, `prim_read_line`, `prim_read_file`, `prim_file_exists`, `prim_rand`, `prim_getenv`, `prim_args_count`, `prim_arg`) that the prelude reaches only from the handler arms of the [capability effects and IO](./spec.md#capability-effects-and-io). The surface names `read_int`/`read_line` read stdin, `read_file`/`file_exists` read files, `getenv` reads the environment, `rand` draws a random word, and `args_count`/`arg` (wrapped by the prelude's `args`) read the command line; each is a prelude wrapper that performs the matching `Console`/`FileSystem`/`Random`/`Env` operation, which the default `run_io` world handler discharges by calling the corresponding `prim_*`. The output primitives stay direct builtins carrying `! {IO}`: `write_file`, `append_file`, and `remove_file` operate on files, `system` runs a shell command and returns its exit code, and `eprint`/`eprintln` write to stderr, leaving the parity-checked stdout untouched. Randomness is a SplitMix64 generator: `prim_rand` advances it and `srand` seeds it, so a seeded run is deterministic and reproducible. Because these touch the world, the parity harness (see [verification](#verification)) runs only the programs that avoid them.

### 13.11 Elementary Functions {#elementary-functions-runtime}

Floating-point transcendentals are owned rather than borrowed from the platform, because the [determinism contract](#content-addressed-core) does not survive a math library that rounds the last bit differently on two systems. `sin(large)`, `pow(edge, edge)`, or argument reduction near a multiple of `pi/2` can differ by one ULP between glibc, macOS, BSD libm, and compiler-emitted libcalls. That is enough to break the parity oracle: a content-addressed compiler cannot say "same source, same core, same backend contract" if the final bit is delegated to whichever C library happened to be installed. Prism therefore treats elementary functions like the runtime ABI, not like an ambient host service.

The implementation is a vendored double-precision subset of musl's `libm` (`runtime/libm/`, documented in `runtime/libm/README.md`). musl is a pragmatic fit here: the code is small, permissively licensed, already split into plain C translation units, and has no dependency on a platform `-lm` once the handful of internal support routines are carried with it. Prism keeps the fork intentionally shallow. The public musl symbols are renamed to `prism_v_*` by `runtime/prism_libm_rename.h` so they cannot collide with the host libm; `runtime/prism_libm.c` then exposes the stable `prism_m_*` wrapper surface that the compiler and interpreter call. Local patches are limited to portability glue such as replacing musl-only headers/macros and supplying the hardware IEEE `sqrt` helper for the vendored routines.

Every elementary function routes through that wrapper surface (`runtime/prism_libm.h`, `runtime/prism_libm.c`): the unary `sin`, `cos`, `tan`, their inverses and hyperbolics, `exp`/`exp2`/`expm1`, `log`/`log2`/`log10`/`log1p`, and `cbrt`, and the binary `pow`, `atan2`, `hypot`, and `fmod`. The boxed-float shims (`prism_float.c`, [value representation](#value-representation)) unbox their arguments, call the wrapper, and rebox. The native backend emits calls to the same `prism_m_*` symbols, `build.rs` compiles the vendored sources into one embedded archive, and the driver materializes and links that archive into generated programs. The host interpreter reaches the same wrappers by FFI because the compiler binary links the same runtime. The result is bit-identical native/interpreter behavior by construction rather than by a rounding coincidence, which is exactly what the parity oracle over float programs (`pendulum.pr`, `derivative.pr`) checks.

The whole library is compiled `-ffp-contract=off` (pinned in `build.rs` and the driver's link step), so no platform fuses `a*b+c` into an FMA and diverges the last bit of either ordinary arithmetic or a function's internals. The contract this buys is determinism, not correctly-rounded results: the vendored routines are as accurate as the upstream musl `libm` and no more, but they are the _same_ everywhere. The one current boundary is the browser-only wasm interpreter, which has no C link step and falls back to the Rust `libm` crate; that path is documented as a wasm resident compromise rather than a native-backend parity claim.

## 14. Verification {#verification}

A giant pile of advanced testing and formal-methods approaches keeps the compiler development honest through a rigorous CI gating system. The parity harness (`tests/parity.rs`) is differential testing with the interpreter as the reference: it runs every example on the interpreter and each native backend and asserts byte-identical output, and with `PRISM_CHECK_LEAKS` set, zero leaked cells.

The performance gate (`tests/perf_gate.rs`) asserts that the optimizations actually fire, so a regression that leaves output unchanged is still caught. With `PRISM_EFFOP_STATS` set, it requires zero free-monad cells allocated on the fusion corpus (the stream and multi-handler programs such as `streams.pr`), confirming that the evidence and state paths of [effect lowering](#effect-lowering) reify nothing. It also pins local monadification: a program that pairs an escaping effectful closure with an unrelated fused pipeline must allocate no more cells than the escape alone, so the pipeline stays fused despite the escape. That check is anti-vacuous: it first asserts the escaping component does allocate a nonzero number of cells, so the gate cannot pass by everything being zero. An asymptotic check runs the constant-space programs at n=1000 and n=10000 and fails if allocation grows with n, and a set of constant-stack checks run a pure tail recursion, a `var` loop, the internal control effects, and a parameter-passing `State` loop at a million iterations each under a 2 MB stack (`ulimit -s`), so a lost `musttail` or a regression into the free monad overflows the stack and fails the test. With `PRISM_REUSE_STATS` set, it requires in-place reuse to fire on the reuse corpus (`list.pr`), confirming the reuse pass of [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse) rewrites drops into in-place updates. A coverage gate (`optimization_coverage` in `tests/snapshots.rs`) recomputes the lowering strategy each corpus program takes, by the same decision the compiler makes, and fails if any named fast path (`evidence`, `state-fusion`, `local-partial`) is left with no live witness, so silently losing a whole optimization is caught even when output and counters are unchanged.

A layout test (`src/codegen/emit.rs`) pins the cell ABI: it reads the runtime source at compile time, parses the `#define`s for the tag offset, the header size, and the reserved string and bignum tags, and asserts each equals the constant the code generator emits against, so the runtime and the backends cannot drift apart without failing the build.

A static bar is enforced across the tree. It carries no `todo!`, `unimplemented!`, `FIXME`, or `allow(dead_code)` markers (a CI grep rejects them), and every `unsafe` block lives behind an audited local allow with a safety comment. `cargo clippy` runs clean with the `pedantic`, `nursery`, and `cargo` groups as warnings under `-D warnings`, and the C runtime compiles under `-Werror` with a broad warning set plus `clang-tidy`. Continuous integration (`.github/workflows/ci.yml`) runs on pull requests, pushes to `main`, and manual dispatch: formatting, the two lint passes, the full test suite (the parity and performance gates included), a re-run of the native parity corpus with the C runtime built under AddressSanitizer and UndefinedBehaviorSanitizer, the formatter checking its own corpus (`prism fmt --check`), a `PRISM_CORE_LINT` compile of every example, the WebAssembly playground (lint and type-check), the MLIR backend's parity test, and the Lean model (`lake build --wfail`).

### 14.1 The Lean Model {#the-lean-model}

Beyond the differential gates, the core calculus is mechanized in Lean 4 (the `models/` directory, built with `lake`). `Prism.lean` defines the syntax and a substitution-based small-step relation `Step` with its determinism theorem (`Step.deterministic`). `CEK.lean` then defines the abstract machine the compiler actually runs (see [the interpreter](#the-interpreter)): an environment machine with a continuation stack, `Rv` runtime values carrying closures and thunks, curried application, and the deep, mask-aware handler capture that makes `resume` multishot. The machine is a total, executable `step` function, so it is deterministic by construction and runnable.

The model's central theorem connects the two. A big-step natural semantics specifies what a program evaluates to, and `bigstep_runs` proves the machine implements it (a forward simulation under any continuation stack), so the abstract machine is a faithful realization of the specification rather than an independent artifact. `Meta.lean` adds the supporting metatheory: a unique-normal-form corollary, substitution lemmas, and a progress trichotomy (every computation is a value, takes a step, or is an explicit `Stuck` error, with `stuckNoStep` confirming the classification is a genuine partition). `Dynamics.lean` covers the effect machinery, proving the machine reaches a handler exactly when one is in scope (`effect_progress`) and is stuck on an unhandled operation otherwise (`effect_unhandled`). These compose into the effect-safety property behind [concurrency](#concurrency): a computation performing an operation the frames a handler crosses do not name (`Tunnels`, the `args`/`bind`/non-matching-`handle`/`mask` frames a scheduler contributes) still reaches an outer handler (`effect_tunnels`), so a covered `doOp` steps while an uncovered one is provably stuck (`effect_tunnels_progress`). That is the machine-level image of the ambient-row discipline: a forked fiber's capability tunnels through the non-handling scheduler to the handler the caller's row demanded and cannot escape it. The surface typing side, that ambient-row inference forces every operation a fiber performs into the caller's row so a covering handler must exist, is not itself mechanized; the two meet at the handler-in-scope predicate, inference guaranteeing the stack covers the row and these theorems guaranteeing a covered stack is effect-safe. Every theorem is `sorry`-free; the proofs declare no axioms of their own and reduce to Lean 4's three standard ones, the entire trusted base sitting above the kernel at the top of the verification chain.

| Axiom              | What it is                                                                                                                  | What the model uses it for                                                                                                                                                                                                                     |
| ------------------ | --------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `propext`          | Propositional extensionality: `(a ↔ b) → a = b`.                                                                            | Rewriting a proposition for a provably equivalent one, so `Prop`-level equalities behave like any other equation in the metatheory.                                                                                                            |
| `Quot.sound`       | Quotient soundness: `r a b → Quot.mk r a = Quot.mk r b`.                                                                    | The computational core of quotient types, and in Lean 4 of the kernel's `funext` and the `Acc`/well-founded recursion the executable `step` and its termination proofs rely on.                                                                |
| `Classical.choice` | The axiom of choice: extracts an element from a nonempty type, underwriting excluded middle and non-constructive existence. | Only where the model evaluates IEEE floats, whose arithmetic and the shortest-round-trip `fmt_g` port ([the differential oracle](#the-model-as-a-differential-oracle)) Lean defines non-constructively; the rest of the model is constructive. |

Determinism, progress, and effect-safety therefore rest on `propext` and `Quot.sound` alone, with `Classical.choice` confined to the float-formatting path.

The full stack of trust, top to bottom: the pseudocode traditionally known as mathematics, then the code that actually _is_ mathematics (the Lean 4 kernel), then a hand-written Core-JSON-Lean mangler, and finally the most non-trivial subset of my pile of shit code that I could be bothered to verify. Maybe more someday, but I'm tired, so probably not. So Prism depends on the axiom of choice and some JSON mangling, the correctness of the Lean 4 kernel and a prayer, but I guess that's better than nothing.

Maybe one day I'll do a full mechanization of the typechecker algorithm, but that is going to be highly non-trivial, so probably not.

### 14.2 The Model as a Differential Oracle {#the-model-as-a-differential-oracle}

The Lean model is the top of a verification chain rather than a co-equal third oracle beside the interpreter and native backends. The machine carries [its proven guarantees](#the-lean-model), determinism and soundness against the big-step semantics, and is checked to agree with the interpreter on the compiler's own core; the interpreter is in turn the differential oracle the native LLVM and MLIR backends are held byte-identical to (the [parity harness](#verification) above). A property proved once at the top, that the machine computes the specified value and no other, therefore propagates down the chain to every native binary the gate accepts. Concretely, `prism dump core-json <file>` serializes the elaborated core to a JSON tree (`src/core/json.rs`), which `models/Json.lean` decodes back into the Lean syntax, and the `oracle` executable (`models/Oracle.lean`) runs the verified machine on it and prints the result, rendering floats through a port of the runtime's `fmt_g` shortest-round-trip formatter so output is byte-identical. Because Lean cannot call the C and Rust `printf` machinery the other two backends use, that formatter is reimplemented from the raw IEEE-754 bits in exact arbitrary-precision integer arithmetic, choosing the fewest significant digits (one to seventeen) that round-trip back to the same double; the round-trip check is the one place the otherwise constructive model uses `Classical.choice`. `models/diff_against_rust.sh` pipes each fixture through `prism dump core-json | oracle` and compares against `prism run`, so the verified model is checked against the interpreter on the compiler's actual core, not a hand-transcription. `models/Certificates.lean` records the same agreements as kernel-checked `rfl` theorems for the curated set. The grammar in [the specification](spec.md) is itself single-sourced from `models/grammar.ebnf`.

This hash-equals-behavior guarantee is what makes [content-addressed core](#content-addressed-core) sound, and the compiler already computes those hashes (`prism dump core-hash`, folded into a stdlib Merkle root): a content hash names a piece of core whose meaning is pinned by the oracle, so identifying definitions by hash inherits the parity guarantee for free rather than asserting that two equal hashes mean equal behavior.

The gate turns this same discipline back on itself. Because a native binary's output and its cell-leak result are a pure function of the source and the toolchain that built it, a passing parity verdict is content-addressable: with `PRISM_GATE_CACHE` set (off by default locally, opt-in), the parity harness records each verified case under a key hashing the program source together with a fingerprint of the whole toolchain, the C compiler in use and its version, the backend-opt level, and the extra linker flags. The compiler half of that fingerprint is chosen by `PRISM_GATE_FINGERPRINT`: by default the test executable's own bytes (so any change to the front end, code generator, or the embedded C runtime rebuilds it and moves the key), or in `source` mode a reproducible hash of the compiler's source tree (`src/`, `runtime/`, `lib/`, the manifests), which two checkouts of the same commit compute identically. A re-run whose key already carries a green marker skips the build and run entirely, its verdict inherited from the earlier verification exactly as a definition inherits the oracle's guarantee through its hash. The key includes everything that can move the result and only passes are recorded, so a stale verdict can never be served after a toolchain change and a failing case is always re-run; the cache narrows re-verification to the programs whose behavior could actually have changed.

The reproducible fingerprint is what lets continuous integration cache safely across runners: the Test and MLIR jobs run in `source` mode and persist `target/gate-cache` between runs, so a pull request that touches only one example re-verifies that program while the rest of the corpus is skipped, and a pull request that touches the compiler moves the source hash and re-runs everything. The restored cache needs no trusted key of its own, a stale marker simply fails to match. The hardening re-runs are unaffected: the AddressSanitizer/UBSan and `-DPRISM_RT_DEBUG` passes set distinct linker flags, so their verdicts carry distinct keys and are never served from a plain-build marker. That the correctness gate can safely memoize itself this way is the behavior-equivalence contract and content addressing paying a concrete dividend back into the compiler's own development loop, not just the language it compiles.

## 15. Optimization {#optimization}

The mid-level Core-to-Core tier is a composable pass framework in the spirit of GHC's `[CoreToDo]` pipeline. One shared traversal (`Rewrite`/`Visit`) replaces the hand-rolled Core walkers, so newtype erasure, dictionary specialization, free-variable collection, call collection, and substitution all ride a single visitor (the canonical hasher from [architecture](#architecture) and the tail-recursion classifier from [reference counting and FBIP reuse](#reference-counting-and-fbip-reuse) stay bespoke by design). Each pass is a `CorePass` keyed by a `PassStage`, and the whole pipeline runs from one ordered, level-keyed list through a single `opt::run` entry.

The pipeline spans two stages around effect lowering, so passes are not freely reorderable across it. _Pre-lowering_ passes run in the front end on the elaborated core (see [the core calculus](#the-core-calculus)); _late_ passes run on the lowered core, after [effect lowering](#effect-lowering) has fixed the fusion strategy. The split is important for performance. The simplifier runs in the late stage on purpose: run before effect lowering it rewrote the Core shapes the var/State fusion analysis depends on and degraded that fusion (a regression bisected to copy-propagation), so it runs after lowering, where it cannot defeat the fusion.

The pipeline currently implements five passes, given below in the order the default `-O1` pipeline runs them; each subsection heading is the name `--passes` uses. Three controls switch a pass on and off ([controlling the pipeline](#explicit-pass-lists)): the `-O` level enables passes in groups ([optimization levels](#optimization-levels)), a `--no-<pass>` flag subtracts a single pass from that pipeline, and `--passes` replaces the level with an exact ordered list. Each example shows the same fragment before and after the pass, with the others held off so the rewrite is the only change.

### 15.1 EraseNewtypes {#pass-erase-newtypes}

- **Stage:** pre-lowering
- **Levels:** every level (including `-O0`)
- **Disable:** `--no-erase-newtypes` (honored, but both backends rely on it)

A `newtype` is a distinct type at compile time but identical to its single field at runtime, so this pass deletes the wrapper: each constructor application becomes its argument and each projection becomes the identity. Both backends assume it has happened, which is why it is the one pass `-O0` still runs and the one a `--passes` list should never omit.

{{#tabs }}

{{#tab name="Before" }}

```prism
newtype Age = Age(Int)

fn birthday(a) =
  match a of
    Age(n) => Age(n + 1)
```

{{#endtab }}

{{#tab name="After" }}

```prism
-- an `Age` is represented exactly as its `Int`, so the wrapper compiles away
fn birthday(n) = n + 1
```

{{#endtab }}

{{#endtabs }}

### 15.2 Specialize {#pass-specialize}

- **Stage:** pre-lowering
- **Levels:** `-O1`, `-O2`
- **Disable:** `--no-specialize` (or `PRISM_NO_SPECIALIZE`)

Type-class methods are compiled by passing a dictionary. When the instance is known at a call site, this pass replaces the dictionary-dispatched call with a direct call to that instance's method, so both the dictionary argument and the indirect call disappear.

{{#tabs }}

{{#tab name="Before" }}

```prism,ignore
-- `show` is dispatched through the `Show` dictionary `d`
fn render(d, x) = show(d, x)

render(show_int, 7)
```

{{#endtab }}

{{#tab name="After" }}

```prism,ignore
-- the instance is known, so the call resolves straight to `show_int`
fn render(x) = show_int(x)

render(7)
```

{{#endtab }}

{{#endtabs }}

### 15.3 Simplify (Gentle Simplifier) {#pass-simplify}

- **Stage:** late
- **Levels:** `-O1`, `-O2`
- **Disable:** `--no-simplify`

A gentle simplifier run to a fixed point: case-of-known-constructor (a `match` on a known constructor picks its arm), copy-propagation, dead-`let` elimination, integer constant folding, and used-once-thunk inlining. It is the workhorse, run three times in the `-O1` pipeline: once to expose call sites for `Inline`, once to clean up after it, and once more after `Cse`.

{{#tabs }}

{{#tab name="Before" }}

```prism,ignore
let p = Some(2 + 3)

match p of
  Some(n) => n * 10
  None => 0
```

{{#endtab }}

{{#tab name="After" }}

```prism,ignore
-- 2 + 3 folds, the `Some` arm is chosen, then n * 10 folds
50
```

{{#endtab }}

{{#endtabs }}

### 15.4 Inline {#pass-inline}

- **Stage:** late
- **Levels:** `-O1`, `-O2`
- **Disable:** `--no-inline`

A bounded inliner: a non-recursive function called from exactly one site is pasted into that site, with every binder alpha-renamed so no name collides. Single-call-site only, so inlining never duplicates code; the `Simplify` that follows then optimizes across the merged boundary.

{{#tabs }}

{{#tab name="Before" }}

```prism
fn scale(x) = x * 2

fn main() = println(scale(21))
```

{{#endtab }}

{{#tab name="After" }}

```prism
-- `scale` has one caller, so its body is pasted in (then Simplify folds 21 * 2)
fn main() = println(21 * 2)
```

{{#endtab }}

{{#endtabs }}

### 15.5 Cse {#pass-cse}

- **Stage:** late
- **Levels:** `-O1`, `-O2`
- **Disable:** `--no-cse`

Conservative common-subexpression elimination: a pure, non-trapping `Prim` computed twice is computed once and shared through a `let`. It is restricted to operations with no effect and no trap, so it never reorders a division or an effectful call, making it the most cautious pass in the pipeline.

{{#tabs }}

{{#tab name="Before" }}

```prism
fn f(x, y) = (x * y) + (x * y)
```

{{#endtab }}

{{#tab name="After" }}

```prism
-- `x * y` is pure, so it is computed once and reused
fn f(x, y) = let t = x * y in t + t
```

{{#endtab }}

{{#endtabs }}

### 15.6 Optimization Levels {#optimization-levels}

The `-O`/`--opt` flag selects a level; the default is `-O1` and a bare `-O` is the highest. A level is a named pipeline, from which `--no-<pass>` can then subtract individual passes ([controlling the pipeline](#explicit-pass-lists)).

`-O0` is representation only. It runs just [`EraseNewtypes`](#pass-erase-newtypes), the one pass both backends require, and nothing more, so the compiled core stays a direct image of the elaborated program. This is the level to reach for when reading `dump core` or bisecting whether an optimization caused a change.

`-O1`, the default, is the real optimization level. On top of `EraseNewtypes` it runs [`Specialize`](#pass-specialize) before effect lowering and, after it, the late pipeline [`Simplify`](#pass-simplify) -> [`Inline`](#pass-inline) -> [`Simplify`](#pass-simplify) -> [`Cse`](#pass-cse) -> [`Simplify`](#pass-simplify): dictionary specialization, then a gentle simplifier brought to a fixed point around a bounded inliner and scalar CSE. This is the GHC simplify/inline/simplify shape, and it is what the compiler runs unless told otherwise.

`-O2` currently runs exactly the `-O1` pipeline. It is the reserved slot for the heavier passes that have not landed yet (stronger inlining, a worker/wrapper split, loop-invariant code motion); until they do, `-O2` and `-O1` produce identical core.

### 15.7 Controlling the Pipeline {#explicit-pass-lists}

Below the `-O` level, two mechanisms drive the passes directly. The `-O`/`--opt`, `--passes`, and `--no-<pass>` flags are global, so they apply to building, running, and `dump core` alike.

A `--no-<pass>` flag subtracts a single pass from whatever pipeline is otherwise in effect, an `-O` level or a `--passes` list. There is one per pass, and they stack:

```console
prism app.pr -O1 --no-inline             # the -O1 pipeline, minus Inline
prism app.pr -O1 --no-inline --no-cse    # ...minus Inline and Cse
prism app.pr --no-specialize             # default -O1, minus Specialize
prism dump core app.pr -O0 --no-erase-newtypes   # the raw elaborated core, nothing run
```

`--no-specialize` is the flag form of the `PRISM_NO_SPECIALIZE` environment variable; the two are equivalent and combine. `--no-erase-newtypes` is honored but rarely wise, since both backends assume newtype erasure has run.

`--passes` instead replaces the level outright with an explicit, ordered list, the LLVM `opt -passes=` / GHC `[CoreToDo]` analogue; it is mutually exclusive with `-O`. The spec names the two stages around effect lowering:

```text
--passes '[pre:<names>][;late:<names>]'
```

`<names>` is a comma-separated list in run order; a bare list with no marker is the pre stage. The pre passes are `EraseNewtypes` and `Specialize`; the late passes are `Simplify`, `Inline`, and `Cse`. Each section is exactly the passes named, with no level defaults filled in, so explicit means explicit. The `-O1` pipeline written out in full, and a pre-only run that stops after specialization:

```console
prism app.pr --passes 'pre:EraseNewtypes,Specialize;late:Simplify,Inline,Simplify,Cse,Simplify'
prism dump core app.pr --passes 'pre:EraseNewtypes,Specialize'
```

A `--no-<pass>` flag still applies on top of an explicit list, filtering it:

```console
prism app.pr --passes 'late:Simplify,Inline,Simplify' --no-inline   # Inline dropped from the list
```

The parser rejects an unknown name (suggesting the closest known one), a pass placed in the wrong stage, a pre section that orders `Specialize` before `EraseNewtypes`, and an empty spec.

### 15.8 Controlling LLVM Codegen {#controlling-llvm-codegen}

The `-O` level and the controls above tune the Core-to-Core optimizer, which runs identically on both backends. A separate set of knobs tunes the native backend's own codegen, the last step where the emitted bitcode and the C runtime are compiled and linked. They are independent of the Core `-O`: a program can pair an aggressive Core pipeline with a light backend, or the reverse, for granular control of the generated code.

Prism runs no LLVM optimization passes in process. It verifies the module, writes bitcode, and hands the rest to `clang`, which compiles the bitcode and the C runtime in one `-flto=thin` invocation so ThinLTO inlines the runtime into the generated code. ThinLTO stays on at every level, since it is what folds the runtime in, and every emitted function carries `nounwind` (Prism has no exceptions and this backend emits no invokes or landingpads), which lets the pipeline drop unwind tables. Four controls override this step:

| Control                    | Default | Effect                                                                                                           |
| -------------------------- | ------- | ---------------------------------------------------------------------------------------------------------------- |
| `--backend-opt`            | `2`     | the `clang -O` level over the emitted bitcode: `0`, `1`, `2`, `3`, or `s`/`z` for size; also `PRISM_BACKEND_OPT` |
| `PRISM_CC`                 | `clang` | the compiler driver invoked for the compile-and-link step (e.g. a pinned `clang-18`)                             |
| `PRISM_CC_FLAGS`           | (none)  | arbitrary flags appended after the defaults, so a trailing token wins                                            |
| `PRISM_NATIVE_KONT_FRAMES` | off     | preserve frame pointers, unwind tables, and non-mandatory call frames for experimental native-kont frame capture |

Because `PRISM_CC_FLAGS` is appended last and `clang` honors the final `-O` it sees, a trailing `-O0` there overrides `--backend-opt`; the same hook adds `-march=native`, `-g`, or a sanitizer such as `-fsanitize=undefined`:

```console
prism app.pr --backend-opt 3                       # heaviest backend pipeline
PRISM_CC_FLAGS='-march=native -g' prism app.pr     # native tuning plus debug info
PRISM_CC=clang-18 prism app.pr --backend-opt z     # a pinned compiler, optimized for size
PRISM_NATIVE_KONT_FRAMES=1 prism app.pr            # make native frame capture less optimizer-dependent
```

These controls drive the `clang` step shared by the LLVM and MLIR backends; `prism run` invokes no compiler, so they do not affect the interpreter. The native-kont frame mode is deliberately not a native suspend/resume switch: it defines `PRISM_NATIVE_KONT_FRAMES` for the runtime, asks the toolchain to preserve enough call-frame structure for `prism_native_kont_capture_frames` to produce stable symbol and PC-offset anchors, and enables the generated entry-ABI shadow stack used to report function argument values. Arbitrary suspended locals, stack slots, and registers remain unserialized.

### 15.9 Lint, Telemetry, and Parity {#lint-telemetry-and-parity}

A Core Lint well-formedness check, pipeline idempotence, and per-pass tick telemetry gate every pass, alongside the triple-backend parity oracle (see [verification](#verification)). Parity is the invariant: compiled behavior at every level, and under any `--passes` spec, is byte-identical under the oracle, so optimization can only change cost, never meaning.

Several environment knobs aid debugging, all off by default.

| Variable              | Effect                                                                                 |
| --------------------- | -------------------------------------------------------------------------------------- |
| `PRISM_OPT_STATS`     | dumps per-pass rewrite counts                                                          |
| `PRISM_CORE_LINT`     | lints between passes                                                                   |
| `PRISM_DUMP_CORE`     | writes the Core after each pass to a stream or to run-namespaced files under `target/` |
| `PRISM_OPT_LEVEL`     | overrides the level when no `-O` flag is given                                         |
| `PRISM_NO_SPECIALIZE` | disables dictionary specialization                                                     |

## 16. The Interactive Shell {#the-interactive-shell}

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

## 17. The Formatter {#the-formatter}

`prism fmt` is a rustfmt-style canonical formatter: it parses a file to the surface AST and prints that tree back from scratch (layout is reconstructed, not reflowed), so an already-formatted file is a fixed point that `prism fmt --check` verifies byte-for-byte. What lifts it above a plain pretty-printer is that it preserves _trivia_ (comments and deliberate blank lines) and the original _surface syntax_, restoring sugar the parser had already desugared (UFCS, string interpolation, `?`-binding) instead of printing the lowered form, and it never destroys code: a node it cannot otherwise print falls back to its verbatim source bytes, and an unparseable file is an error rather than a mangled rewrite. The trivia and span bookkeeping ride on [`marginalia`](https://crates.io/crates/marginalia), a small crate written for this compiler but published independently. The implementation is `src/fmt/`.

## 18. Documentation Generation {#documentation-generation}

`prism docs` generates Markdown API documentation for a project, one page per module, from the two things the compiler already produces: the comment trivia the [formatter](#the-formatter) also relies on, and the types the [checker](#type-and-effect-inference) infers. It is a general tool (`src/docs/`); the [standard library](./stdlib/index.md) reference in this book is its first output, produced by `prism docs --stdlib` with the output redirected into the book source.

Documentation comments are the only convention it layers on top of the language. A `-- |` line comment (an ordinary `--` comment marked with a bar) directly above a declaration is that declaration's docstring, and one at the top of a file is the module description; every other comment is ignored. This adds nothing to the lexer or grammar: the comment never reaches the AST, and the generator recovers it from the [`marginalia`](https://crates.io/crates/marginalia) trivia table by span, exactly as the [formatter](#the-formatter) re-associates leading comments. So `-- |` is a documentation convention, not a syntactic form.

Signatures are not read from the source but taken from the checker, because most standard-library functions carry no written signature: the generator type-checks each module and renders the declaration's inferred type (`Type::show`). Types, classes, and effects are printed from the surface AST with the formatter's own declaration printers, so they read exactly as written.

A fenced `prism` code block inside a docstring is a doctest. `prism docs --test` extracts every such block and compiles it, running it when it produces a program to run, so an example that drifts out of sync with the code fails the build. An example need not spell out a `main`: a block without one is wrapped as the body of an implicit `main`, so a bare expression like `unwrap_or(0, Some(5))` or a short `let`-block runs like a REPL line and shows its value, which keeps examples to the point. The in-browser Run button (and the playground) apply the same wrapping. Per-fence attributes gate the treatment: `ignore` skips a block, `no_run` compiles without running, and `compile_fail` expects a type error, for the cases where a snippet is illustrative or is meant to be rejected. The standard-library pages are committed to the book, and `prism docs --stdlib --check` in continuous integration regenerates them in memory and fails if the checked-in Markdown has drifted, the same contract `prism fmt --check` enforces for source.

A doctest may also pin its output: an `output` fence immediately after a `prism` fence is the example's expected text, checked by `prism docs --test` against the actual print transcript (or the result's `show` when nothing prints). When an expectation goes stale, `prism docs --test --accept` (alias `--bless`, wrapped as `just bless`) rewrites the expected block in the source file in place, touching only the expectation lines and preserving every byte of surrounding code and comment trivia; blocks rewrite bottom-up so earlier spans never shift, a file that changed on disk since parsing is refused, and the run exits nonzero whenever anything was rewritten, so continuous integration can check expectations but can never silently bless them.

## 19. Editor Integration {#editor-integration}

Editor support is, to put it generously, nascent. What exists today is a dependency-free Neovim highlighter under `scripts/nvim/` (an `ftdetect/` map for `*.pr` plus a `syntax/` highlighter whose keyword set is mirrored from `src/lex/token.rs`, so it tracks the lexer). That is the whole story: no semantic highlighting, no go-to-definition, no inline diagnostics.

A proper [tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar and a language server (LSP) are planned, which would bring incremental parsing, structural selection, and the usual hover, jump-to-definition, and live-diagnostic surface to any editor that speaks the protocol. They are not built yet. The project is written for one person, by one person, so the editor it integrates with is, for now, the one that person happens to use.

## 20. Content-Addressed Core {#content-addressed-core}

Prism identifies every top-level definition by a hash of its elaborated core rather than by its name. `prism dump core-hash` (`src/core/hash.rs`) computes that hash over the core after three normalizations. Every free reference to another top-level symbol is replaced by that symbol's own hash, so a definition's hash transitively commits to everything it calls and the program becomes a Merkle DAG.

Bound variables are alpha-normalized to positions, and source spans, comments, and formatting are erased. The hash commits to the elaboration inputs an importer reads, not just the term: the generalized type, the principal effect row, the `fip`/`fbip` mode, and the borrow mask. A recursive group is hashed as one strongly-connected component (reusing the shared Tarjan machinery from [name resolution](#name-resolution-and-modules)) with members keyed by index. The result is a name-independent, position-independent identifier for behavior: a rename, a reformat, or a local-variable rename leaves it unchanged, while any change to type, effect row, or computed result changes it.

Declarations with no term body are committed the same way by structural digest (`src/core/shape.rs`): a datatype or effect by the shape of its constructors and operations, a type class by its interface, and an instance by its identity, meaning its class, head type, and the behavior hashes of its methods. Top-level constants, which the compiler inlines rather than compiling to a node, are elaborated as zero-parameter definitions for hashing, so nothing a reader sees on a page is left unaddressed except transparent aliases, which have no content of their own.

Precisely, every hash below is a BLAKE3 digest of a length-prefixed token stream, so no field boundary is ever ambiguous. Resolving one variable reference, inside the structural walk of a `Comp`/`Value` tree, is a four-way case split:

```text
tok(s)     = len(s) : s

refer(s)   = "b" ++ i         s bound at de Bruijn depth i (a param, let, or match binder)
           | "r" ++ idx(s)    s is a member of this definition's own recursive group (SCC)
           | "h" ++ H(s)      s is an external dependency, already hashed (Merkle substitution)
           | "g" ++ tok(s)    otherwise, a free leaf: a builtin, a constructor, an effect op

encode(f)  = "fn" ++ arity(f) ++ walk(body(f))
H(f)       = blake3(SCHEME ++ meta(f) ++ encode(f))
```

`walk` tags each node with its variant name and then its children, resolving every variable through `refer`; `H(f)` is the singleton case, where a non-recursive definition is a group of one. A strongly-connected component `{f1, ..., fn}` (mutual recursion) hashes as a unit instead, in two passes, since a member's final index does not exist until every member's shape is known:

```text
order      = sort by (encoding, name) of  [ (encode(fi, self = "r?"), fi)  for fi in scc ]
idx(fi)    = position of fi in order
blob       = SCHEME ++ concat  [ meta(fi) ++ encode(fi, self = "r" ++ idx(·))  for fi in order ]
component  = blake3(blob)
H(fi)      = blake3(component ++ ":" ++ idx(fi))
```

The first pass orders the group with every intra-group reference behind the neutral placeholder `"r?"`, so the order itself never depends on names; the second pass re-encodes each member with real indices and folds the result into `component`, and a member's own hash is `component` tagged with its position, so every member of the group gets a distinct hash from one shared digest. `meta(f)` folds in the elaboration inputs above (type, row, `fip`/`fbip` mode, borrow mask) as one more length-prefixed field.[^effect-op-canon]

[^effect-op-canon]: Effect-op names canonicalize too: a `var`-desugared `get@x@n`/`set@x@n` becomes `get@#k`/`set@#k`, a per-definition id assigned by first occurrence, so renaming the `var` or reordering top-level definitions never moves the hash; a genuine effect operation's name is committed verbatim, since renaming one of those is a behavior change.

`prism dump stdlib-hash` folds every standard-library definition's hash together with every datatype, effect, class, and instance digest into a single Merkle root, a Unison-style namespace hash stamped with the scheme tag and the compiler version, computed over the pre-optimization core so it is reproducible and independent of optimizer flags. The generated [Standard Library Reference](stdlib/index.md) anchors that root on its index page and gives every documented definition a subtle content-hash badge beside its signature; both are regenerated and byte-diffed in CI (`prism docs --stdlib --check`), so any behavioral change to the library moves the root and fails the gate until the documentation is regenerated. The hashing spans every declaration kind and is surfaced where a reader can see it; the source files remain the authority, and the store is a cache derived from them.

The same fold that builds one module's namespace builds the whole library's:

```text
defs       : Sym  -> Hash  = hash_program(core, meta)
shapes     : Name -> Hash  = shape_digests(types, effects)
classes    : Name -> Hash  = class_digests(classes)
instances  : Name -> Hash  = { inst.name -> instance_digest(inst)  for inst in instances }
```

An instance's digest folds its class, its head type, and its methods into one identity:

```text
instance_digest(inst)  = blake3(SCHEME ++ "|instance" ++ tok(inst.class) ++ encode_ty(inst.head) ++ methods_blob(inst))
methods_blob(inst)     = "{" ++ concat [ tok(name) ++ tok(hash)  for (name, hash) in sorted(inst.methods) ] ++ "}"
```

`inst.head`'s type variables are alpha-normalized positionally, so `Eq(List(a))` and `Eq(List(b))` share one identity, and methods fold in sorted by name so declaration order never matters. Every kind then merges into one namespace, keyed by kind so a value and an instance, both lowercase surface syntax, cannot collide:

```text
entries = { "def "      ++ sym  -> h     for (sym,  h) in defs      }
        | { "shape "    ++ name -> h     for (name, h) in shapes    }
        | { "class "    ++ name -> h     for (name, h) in classes   }
        | { "instance " ++ name -> h     for (name, h) in instances }

root(entries) = blake3(SCHEME ++ concat  [ "|" ++ len(name) ++ ":" ++ name ++ "=" ++ hash
                                            for (name, hash) in sorted(entries) ])
```

One fold, sorted by key, is both a module's root and the stdlib's: `root` moves under any rename or content change, entry by entry, but never under reordering. `stdlib_root = root(entries)` over the whole library's `entries` is exactly the value the docs anchor and CI byte-diffs. The same construction now reaches values and persisted formats: a derived [`Hash`](spec.md#type-classes) instance folds a runtime value through the identical BLAKE3 tokenization, so a value's digest is canonical across backends for the same reason a definition's is, and each frozen rung of a [`stable` block](spec.md#stable-blocks) commits its shape digest in source, checked at compile time and reseated only by the explicit `prism store wire --accept`, which extends the committed-golden discipline from the standard library's docs to every user-declared wire format.

Prism is an unusually good host for the Unison-style managed codebase this points at, because two of the hardest preconditions are already paid. Name resolution canonicalizes every definition to a globally unique symbol ([modules](spec.md#modules)), and the [differential oracle](#the-model-as-a-differential-oracle) makes "equal hash means equal behavior" a verified property rather than an assertion, since the hash is taken over the very core the parity gate runs byte-identically across three backends. The direction is the codebase as a content-addressed database: names become a mutable index over immutable `hash -> core` entries, so a rename is an O(1) metadata edit, two versions of a dependency coexist as two hashes with no version solver, an unchanged hash is already compiled and parity-verified so a rebuild touches only a definition's Merkle closure, and a computation named by a hash can be shipped across a wire and run with a proof it is the same computation.

The same content hash is exposed to programs directly. The `Incr` standard-library module ([incremental computation](spec.md#incremental-computation)) is self-adjusting computation whose early-cutoff test is exactly this digest: a memoized derivation that recomputes to a value with an unchanged blake3 hash stops propagating to its dependents, and the durable form persists the memo table to a snapshot that cold-starts on a digest mismatch, so a warm run's result is byte-identical to a cold one. Where the compiler recompiles only a change's Merkle closure, an `Incr` program recomputes only a change's demand cone, and it is the same hashing that decides the boundary in both.

### 20.1 The On-Disk Store {#the-on-disk-store}

`src/store/` persists the content-addressed graph to disk under a single store root, in the two layers the [`dump namespace`](#dump-phases) export mirrors. The _anonymous_ layer is an immutable, append-only object directory: each definition is serialized by the same [wire codec](spec.md#stable-blocks) the language exposes, hash-consed per node, and written to `objects/<first two hex>/<rest>`, the git-style sharding that keeps a single directory from growing unbounded (`src/store/disk/objects.rs`). Writing an object that already exists re-verifies byte-identity and treats a mismatch as a hard collision rather than an overwrite, so an object address always denotes exactly one byte string. The per-node codec (`src/store/codec.rs`) writes a variable as a de Bruijn index, its outward binder distance, which is what makes the stored form invariant under var-local renaming and under reordering the definitions of a recursive group. The _metadata_ layer (`meta/`) is mutable and keyed by the same hash: it holds the facts a reader needs but that are not part of a definition's identity (a name, a rendered type, a doc comment), so a rename or a doc edit touches this layer and never the object the hash commits to.

Those two layers sit under a store root beside a version stamp, an index directory, and the verified, certificate, and package artifacts the later sections build on:

```text
<store root>/
├─ VERSION                      hash-scheme tag, then store-format tag, one per line
├─ objects/ <2 hex>/<62 hex>    immutable anonymous layer: one encoded definition per hash
├─ meta/    <2 hex>/<62 hex>    mutable facts beside the object (name, type, doc)
├─ index/
│  ├─ names                     name          -> content hash
│  ├─ deps                      content hash  -> its direct dependents
│  ├─ canonical                 (class, head) -> canonical instance hash
│  └─ lock                      advisory lock serializing the index writers
├─ verified/ <2 hex>/<62 hex>   the checks each hash has already passed
├─ certs/    <2 hex>/<62 hex>   immutable parity certificates, one per attested subject
└─ pkg/
   ├─ index                     signed  origin/name/tag -> root-hash table
   ├─ index.sig                 detached signature over index (absent when unsigned)
   └─ log                       append-only transparency log of published pointers
```

Every file outside the two opaque blob layers (`objects/` and `certs/`) is line-oriented, tab-separated, and header-versioned: its first line is a `<kind><TAB>v<n>` stamp, so a format change is a header bump an old reader refuses rather than misreads.

| File                 | First line                     | Record (fields tab-separated)                                 |
| -------------------- | ------------------------------ | ------------------------------------------------------------- |
| `index/names`        | `prism-store-names<TAB>v1`     | `<name><TAB><hash>`                                           |
| `index/deps`         | `prism-store-deps<TAB>v1`      | `<hash><TAB><dependent-hash> <dependent-hash> ...`            |
| `index/canonical`    | `prism-store-canonical<TAB>v1` | `<class><TAB><type-head><TAB><instance-hash>`                 |
| `meta/<sharded>`     | `prism-store-meta<TAB>v1`      | one `name` / `type` / `doc` key per line, `<key><TAB><value>` |
| `verified/<sharded>` | `prism-store-verified<TAB>v1`  | `<check-kind><TAB><scheme><TAB><pass or fail>`                |
| `pkg/index`          | `prism-pkg-index<TAB>v1`       | `<name><TAB><tag><TAB><root-hash>`                            |
| `pkg/log`            | `prism-pkg-log<TAB>v1`         | `<seq><TAB><nanos><TAB><name><TAB><tag><TAB><root-hash>`      |

The root `VERSION` carries the [hash-scheme](#content-addressed-core) tag and the store-format tag on their own lines, and a store whose either tag this build does not speak is refused outright rather than read under the wrong assumptions. Both blob layers and both hash-keyed metadata layers shard git-style on the first byte of the hex digest (`<first two hex>/<rest>`) so no directory grows without bound.[^atomic-write] The three `index/` files, which read-modify-write a whole file, additionally serialize their writers through the advisory `index/lock`, best-effort because a lost index binding is recovered on the next commit.

[^atomic-write]: Every write lands atomically: bytes go to a uniquely named `.tmp.*` file in the destination directory, are flushed, and are renamed into place, which is the commit point, so a reader sees the whole old file or the whole new one and a process killed mid-write leaves only a temp file no reader ever opens (readers open exact hash paths only).

The store is off by default and enabled with `PRISM_STORE`, its location chosen by `PRISM_STORE_PATH` (resolved through `store::resolve_store_path`). When it is on, a build commits every definition's object and prints a one-line summary, `store: N unchanged, M recompiled`, counting the objects served from the store against those written fresh, so the Merkle-closure property, that a change recompiles only its own closure, is visible at the command line. A from-scratch build and an incremental build are held to the same result by an oracle pair (`tests/store_oracle.rs`): a cold build and a warm incremental build of the same program must produce byte-identical artifacts, a change must move only its Merkle closure, and a reformat or a rename must move nothing at all.

### 20.2 Verification Caching {#verification-caching}

A stored object carries its verification verdicts alongside it (`src/store/verify.rs`, `src/store/disk/verified.rs`). A check that a definition passed, its interpreter [parity](#lint-telemetry-and-parity), its doctests, or its expect tests, is recorded as an append-only verified record keyed by the definition's content hash and the hash scheme in force. A later build reads the verdict rather than re-running the check, so an unchanged definition does not re-run its tests, doctests, or parity comparison, and the total cost of verifying a change tracks the Merkle closure of that change rather than the size of the program. The scheme tag is part of the key on purpose: bumping the hash scheme invalidates every prior verdict at once, because a verdict recorded under an old scheme no longer matches, so a scheme change can never silently reuse a stale pass. Because the hash is invariant under formatting and renaming, reformatting a file keeps its verdicts intact.

Store-level instance coherence extends the compile-time [coherence check](spec.md#coherence-and-resolution) across programs. At commit time each canonical `(class, head)` binding records its instance's identity digest in the canonical index (`src/store/coherence.rs`), and a second program that commits a divergent canonical instance for the same key is rejected as a hard error before anything is written, the cross-program form of the ambiguity the single-program checker already forbids. This is the enforcement the instance identity digest of the previous section was the primitive for.

A verified record is local to the build that wrote it; a _parity certificate_ (`src/store/cert.rs`, `src/store/disk/certs.rs`) is the transferable form of the same idea, an immutable object in a `certs/` layer beside the verified records. `prism store attest` compiles a program through two of the three backends (LLVM and MLIR, or LLVM and the interpreter) and, once their output is byte-identical, emits a certificate whose body records the claim (`parity-passed`), the hash scheme, and which backend pair agreed, addressed by the hash of its own envelope so it is itself content-addressed. `prism pkg audit` reads the certificate back and reports it per root, and a certificate that fails to verify (a foreign scheme or a subject mismatch) blocks the audit, while a certificate whose claim a reader does not recognize is reported unverifiable rather than treated as corruption, so an older build reads a newer certificate without rejecting it. Exactly one claim is live, parity agreement across backends; a Lean-checked claim that would let the certificate carry the [differential oracle](#the-model-as-a-differential-oracle)'s verdict too is reserved.

### 20.3 The Kont Envelope {#the-kont-envelope}

Where the store's codec serializes the compiler's own anonymous core (a `def`), a second codec (`src/eval/kont.rs`) serializes the interpreter's _runtime_ representation: the live continuation of a suspended program, so it can be written to a file, moved to another process, and resumed. This is the wire under [suspend and resume](spec.md#suspend-and-resume). The two codecs are distinct wires over distinct domains, but an operator (a `CoreOp`, `Builtin`, `FloatOp`, or `NegLane`) means the same thing in both, so its wire number is drawn from the one canonical home in `store::codec` rather than re-typed here.

The envelope is the same self-describing frame every Prism wire uses, read left to right, each header part checked before the next byte is touched:

```text
+------------+------+------------------+--------------------------------+
| scheme tag | kind |  bundle digest   |              body              |
+------------+------+------------------+--------------------------------+

scheme tag     length-prefixed "prism-core-hash-v1"; a foreign scheme is rejected first
kind           uvarint, WireKind::Kont
bundle digest  length-prefixed: the code identity of the program this continuation runs in
body           the machine snapshot below
```

The body is the whole interpreter machine frozen as data: the scalar registers (the `rand`/`srand` generator state so a resumed run continues the same stream, the current function name, the observation count, an optional exit code, and the [replay trace](spec.md#record-and-replay) recorded up to the cut so the prefix's world reads stay pinned across the resume), then one hash-consed **node table**, then the roots that point into it, the frame stack (bottom to top) and the pending state (mid-evaluation of a computation under an environment, or about to return a value).

The node table is what makes freezing a call stack tractable. Every recursive object the machine holds, across six domains (a runtime value, a lowered computation node, an atom, a stack frame, an environment, a handler record), is interned once into one shared table and referenced by index, and a child's index is always strictly below its parent's. The graph is acyclic by construction, decode is a single forward pass with no fixups, and an environment shared by twenty frames is stored once.

One uvarint tag numbering (`TAGS`, the single source of truth so encode and decode cannot drift) spans all six domains. An index is untyped on the wire, and the builder validates each referent's tag against the domain it is used in, so a cross-domain reference in a hostile frame is rejected rather than misread.[^suspend-depth]

[^suspend-depth]: The frame stack itself is encoded iteratively, so the depth bound (`MAX_SUSPEND_DEPTH`, 256) limits nested runtime data (a cons-list, a tree) and the source-bounded computation depth, not the count of pending frames, which keeps both the recursive encoder and the recursive decoder inside the native stack.

Unlike the `def` wire, a binder here keeps its interned name, since the interpreter resolves variables by symbol through the environment rather than by de Bruijn distance; environment and handler-op orderings are canonicalized by name, because symbol ids are process-local. Code references resolve **reference-or-inline**: a call to a top-level definition rides as the callee's _name_ and is resolved at resume against the resumer's function table, whose identity the matching bundle digest guarantees, so same-bundle wire cost is the captured state alone; an inline lambda or thunk body travels inline.

Decoding is total on the same discipline as every other Prism wire: `decode_kont` never panics on hostile bytes.[^kont-decode-total] Encoding is fallible in the other direction: a value that cannot cross the suspend boundary (a graph nested past the suspendable depth, the fingerprint of a cycle or an unserializable capture) is refused by name at suspend time rather than written into a snapshot that would fail on the far side.

[^kont-decode-total]: Totality holds because every varint is byte-capped, every length is bounded, the scheme, kind, and bundle are checked before the body, child indices are range-checked against the already-parsed prefix, reconstruction runs against an expansion budget, and trailing bytes are rejected.

The field that matters is the bundle digest. It is not a checksum of the envelope bytes; it is the program's **namespace root**, the Merkle fold of the [content-addressed core](#content-addressed-core): `root` over `{"def " ++ sym -> H(sym)}` for every definition the program reaches, the standard library included. That digest is a name-independent, dependency-complete fingerprint of all the code the continuation could run.

A resumer recomputes the namespace root from its own copy of the program and refuses a snapshot whose digest differs. The kont envelope is therefore the content-addressed Merkle DAG applied to a live computation: because the code already has a canonical identity, a running computation over it can travel with a compact proof that the far side is the same program.

## 21. The Package Manager {#package-manager}

The package manager is deliberately a synthesis, not a clone. It takes the fast command surface of Bun-style package UX, the Nix idea that installed code lives in an immutable content-addressed store, and the git idea that distribution can be hash-addressed and cheaply mirrored.

The Prism-specific move is the unit of identity. A package is not a tarball, a registry row, a checkout, or a semver range; it is the compiler's content-addressed Core/source bundle and the complete dependency closure reachable from that bundle, folded to one Merkle root. Names, tags, manifests, and indexes are mutable ways to find the root. The root is the package.

Distribution is therefore the content-addressed store carried across a network. A project declares its dependencies in a `[dependencies]` table in its `prism.toml` (`src/project/`), in one of three forms: a `path` to a local directory, a `git` URL paired with an opaque tag, or a bare content-hash pin naming an exact definition graph. The three are the same `DepSource` the resolver consumes, differing only in how a name is turned into a root hash. Edits to the table go through a format-preserving manifest writer (`src/pkg/writer.rs`) that rewrites only the dependency lines and leaves every comment, blank line, and untouched byte exactly where the author put it, so `prism pkg add` does not reformat a hand-maintained manifest.

All dependency spellings are explicit about where the eventual root hash comes from:

```toml
[dependencies]
geometry = { path = "../geometry" }
legacy_geometry = "../legacy-geometry"
crypto = "prism-core-hash-v1:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
http = { git = "github.com/prism-lang/http", version = "2.0" }
```

`path` is a local Prism project, with the bare string accepted as its shorthand unless it carries the `prism-core-hash-v1:` prefix. Path dependencies are editable source roots, not accountable artifacts: they are for local development and enter the compiler as explicit module search roots. The hash string is the fully explicit pin: no name lookup, no network resolution, and no version label. The `git` form is the human release surface; `version` is an opaque tag, not a range, and the signed package index maps the full package identity `(git URL, display name, tag)` to the exact source-bundle identity that enters the lockfile: origin, package name, artifact kind, hash scheme, and root.

Resolution is a Merkle-closure walk, not a version solver. Given a set of root hashes, `resolve_closure` (`src/pkg/resolve.rs`) reads each definition's stored frame and follows its dependency edges until the closure is complete, fetching any object it does not already hold. Every fetch crosses a `Transport` seam (`src/pkg/transport.rs`) that re-hashes the received bytes and rejects a mismatch, so a definition is trusted because its content hashes to its address and for no other reason; a `DiskTransport` serves a local store and a `GitTransport` clones, pulls, and pushes a store held in a git repository by shelling to the system `git`.

The resolved closure is frozen into a v2 `prism.lock` (`src/pkg/lock.rs`) whose header pins the lock format and whose Std and dependency rows carry both hash scheme and root hash. Its entries are terminal: a locked hash on a warm cache is never re-resolved, re-fetched, or re-verified, because a content hash cannot mean two things.

`prism pkg export` (`src/pkg/export.rs`) writes a project's closure back out as source text and a v2 `.namespace` manifest naming the hash scheme, artifact kind, and namespace root; consumers verify all three before trusting the projection. Its guarantee is source stability, the exported text round-trips through the parser, and it deliberately stops short of promising that re-ingesting that text reproduces the same store hashes.

Trust over that graph is a signed package-identity-to-root index and a local transparency log (`src/pkg/trust.rs`). A publish signs the `(origin, name, tag, hash scheme, artifact kind, root)` row of the index, through one of three interchangeable seams selected by [`PRISM_SIGN_MODE`](#environment-variables): an `ssh-keygen -Y sign` signature verified against an allowed-signers file, a `minisign` signature, or an explicit unsigned mode for a private store. Verification classifies each artifact `Ok`, `Unsigned`, or `Bad`.

Alongside the index a project keeps an append-only transparency log that verifies each entry as it is appended and assigns it a dense, monotonic sequence number. A package identity silently repointed at a different root leaves a detectable gap in the log after the fact rather than passing unnoticed. The verbs are `prism pkg add`, `prism pkg why`, `prism pkg export`, `prism pkg publish`, `prism pkg audit`, and `prism pkg check-world`; they are tabulated with the rest of the surface under [commands](#commands).

## 22. Lineage {#build-lineage}

Every served artifact explains itself through one typed graph. `src/lineage/` defines a single format, `prism-lineage-graph-v1`, whose nodes are content-addressed inputs, capability observations, produced artifacts, and the verification edges between them; a node's identity is derived from its own digest, so the graph is content-addressed the same way Core is ([content-addressed core](#content-addressed-core)). Four variants ride that one format, `Variant::ProjectBuild`, `Variant::Run`, `Variant::Docs`, and the world resident's timeline, and they share one envelope, one renderer (`render.rs`), one verifier (`verify.rs`), and one differ (`diff.rs`). A new kind of served thing becomes a new node family and a variant tag, not a new file format, a second explainer, or a parallel verifier.

The identity every variant records is computed in one place. `BuildIdentity` (`src/driver/identity.rs`) folds the compiler version, hash scheme, target, backend, optimizer surface, scheduler, behavior-affecting flags, and, for a native backend, the linker toolchain inputs, into the identity rows the sidecar carries. Every consumer that previously assembled those rows piecewise now derives them from this one computation, so a build sidecar, a run sidecar, and a docs manifest cannot disagree about what "the compiler that produced this" means.

A **project build** writes a `.plineage` sidecar beside the emitted binary, naming the root request, the source namespace root, the Std root, every store-served package root, the `BuildIdentity` rows, emitted artifact digests, store cache hits when the store is enabled, and diagnostics. This is the minimal bridge from the current explicit driver to a future build-as-handler model: it records facts the build already knows, without introducing a new scheduler, cache protocol, or effect operation.

A **run** sidecar (`src/lineage/run.rs`) is the same graph over an executed program. `prism run p.pr --record run.replay --lineage run.plineage` writes it beside the `.replay` trace it explains, naming the source/Std/package roots, the `BuildIdentity`, `argv`, each environment read, each input file by content digest, each file the run wrote, the stdout digest, and the trace digest. The trace's own file relation is recorded as an edge, so verification reads the graph rather than a filesystem convention. `--lineage` is gated on `--record` in the CLI definition, because a run sidecar's whole point is to explain a trace.

Those observations are backed by the **provenance event protocol** (`src/provenance.rs`). Every capability the run performs, every `Console`/`FileSystem`/`Random`/`Env` operation, is recorded as an event carrying a canonical hash of its kind and its payload, and a variable-length value commits a content digest rather than raw bytes, so a hostile input cannot forge an event boundary by embedding a delimiter. The protocol's guarantee is asserted by test, not claimed: recording a run and replaying its trace produce identical event hashes, so the trace a sidecar explains is provably the trace the program performed. A mismatched replay names the failing event index and the operation it expected, rather than diverging silently.

Verification comes in the three strengths the variants need. `prism lineage verify SIDECAR` **rehashes**: it recomputes the digests the sidecar recorded and confirms they still match, cheap and offline. `--replay` **re-runs**: it replays the trace through the interpreter and re-checks the result, catching a divergence the recorded numbers alone could not. The world variant **verifies structurally**: a timeline's node ids are self-certifying, so `verify` confirms the graph is well-formed (its laws, states, and forks are consistent) and honestly reports that re-derivation of the cellular evolution is not implemented rather than claiming a re-execution it did not run. `prism lineage show` and `prism lineage why` render an explanation from any variant, and both work after the source files are gone, because every fact is in the graph. In a project, bare `prism diff` compares the `.pr` sources at Git `HEAD` with the working tree (including staged changes), reports the semantic delta, then prints only the changed definitions as a compact surface diff; `prism diff OLD NEW` still compares explicit source revisions. Over two `.plineage` sidecars it reports preserved, moved, added, and removed digests by logical key, exiting nonzero when anything moved; sidecars are dispatched by `is_lineage_sidecar` in `bin/prism.rs`.

A passed verification can be **persisted as a certificate** (`src/lineage/cert.rs`). `prism lineage verify SIDECAR --certify out.cert` mints a digest-named certificate over the sidecar it verified, claiming `replay-verified` under `--replay` or `lineage-verified` otherwise. The certificate rides the store's existing certificate discipline (`src/store/cert.rs`, [verification caching](#verification-caching)): it shares the one claim number space parity certificates use, is addressed by the hash of its own envelope, and is checked by scheme, subject digest, and claim recognition. `prism lineage check-cert out.cert SIDECAR` rejects a certificate whose subject digest does not match the named sidecar, and a certificate carrying a claim the reader does not recognize is recognized-but-untrusted, reported unverifiable rather than honored, so a newer certificate read by an older build is neither trusted nor treated as corruption.

`prism docs` is the one **docs-manifest** writer (`src/lineage/docs.rs`). Alongside the rendered pages it emits `docs.plineage`, the docs variant of the graph, naming the same roots and `BuildIdentity` a build carries, plus the generator format (`prism-docs-markdown-v1`), every page digest, and every doctest output hash. Regenerating under the same roots is byte-identical. `prism docs --verify-manifest` rehashes the committed pages and confirms the roots have not drifted, rejecting a stale page or a moved root by name; `prism pkg check-world` runs the same check as one of its per-package gates.

`prism pkg check-world [path]` applies the identity discipline to a whole package universe. It discovers package projects under `path` (default `packages/`), resolves each project's explicit Std and dependency roots, and reports the package set keyed by source-root digest, with a compatibility summary: all observed Std roots, compiler surfaces, packages grouped by declared name, store dependencies grouped by package identity, and problems such as duplicate package names with different source roots or one dependency identity resolving to multiple roots. `--strict` turns incompatibility into a nonzero CI gate. Each package now carries **per-package gates**, the build lineage, examples run through the compiler-owned runner, doctests, committed replay traces, and the docs manifest, each reporting `passed`, `failed`, or `not-run`. The `not-run` distinction is essential: a gate that does not apply says so rather than passing silently, so a green report never overstates what was checked. Each package also exposes a **public-API surface** of definition behavior hashes; given a prior report as `--baseline`, check-world names exactly which public definitions changed behavior, by digest and never by path, so an API break is reported as which definitions moved rather than which files were touched.

```console
$ prism pkg check-world packages
checked 1 package(s) in packages
validation: typecheck-only
  typecheck: passed
  doctests: not-run
  replay: not-run
  native: not-run
compatibility: compatible
  tzdb: prism-core-hash-v1:b9e853148727...
    gates: check=passed example=not-run doctests=passed replay=not-run docs=passed usage=passed root=passed dependency=passed
    stdlib: prism-core-hash-v1:ac8a7aa43202...
```

The useful invariant across all of this is that any served artifact, a binary, a run's output, a documentation set, a package universe, answers "which source root, Std root, package roots, compiler scheme, target, and flags produced you?" by digest, without reading ambient process state, and says whether it is internally coherent without implying gates it has not run.

## 23. Metaprogramming {#metaprogramming}

Prism has no macro system, and that is a considered omission rather than a gap waiting to be filled: I am, by temperament, allergic to metaprogramming, having been burned by Template Haskell and OCaml's metaprogramming fire and watched it trade a moment's convenience for code that no reader and no tool can follow. The honest status, in one sentence, is that doing it _well_ in a typed setting, weaving phase distinctions and Lisp-style hygienic macros into the type system so that generated code is as principled, type-safe, and legible as code written by hand, is still an open research problem rather than a solved one, and Prism is waiting for the right model instead of bolting on the wrong one. If anything, the [content-addressed core](#content-addressed-core) and the verified [differential oracle](#the-model-as-a-differential-oracle) are an unusually disciplined substrate to host such a thing once the design is clear. I am genuinely open to new ideas here: if you know a model that does this elegantly, [get in touch](https://www.stephendiehl.com/hire/). Until then it stays an open problem.

## 24. Bootstrapping Plan {#bootstrapping-and-self-hosting}

The compiler is written in Rust, but only until it can be written in Prism. The end state is the ordinary one for a serious language: a self-hosting compiler that compiles its own source, reached by a standard multi-stage bootstrap. The current Rust compiler is _stage 0_. Compiling the Prism-in-Prism source with stage 0 yields _stage 1_; compiling that same source again with stage 1 yields _stage 2_; and the bootstrap is sound exactly when stage 1 and stage 2 are byte-identical, the fixed point that proves the compiler reproduces itself. Prism is already unusually well-equipped to check that last step, because the [differential oracle](#the-model-as-a-differential-oracle) and the triple-backend [parity gate](#lint-telemetry-and-parity) make "two builds agree byte-for-byte" the property the whole test suite is already built around.

Two pieces of the present design are deliberately the seams a self-hosting move needs. The first is the [shared emitter](#the-shared-emitter): codegen is one Core walk behind an `Isa` trait, and the textual LLVM and MLIR backends are just two instances of it that hand their output to an external tool (`clang`, `mlir-translate`) rather than calling into a library. A Prism compiler therefore needs to emit text and shell out, not bind LLVM's C++ API, so the dependency on Rust's `inkwell` binding is an implementation detail of stage 0, not something the language inherits. Abstracting the link step the same way, a small interface over "assemble this IR and link it against the runtime", is the remaining backend work that lets a self-hosted compiler depend only on a C toolchain it can find on `$PATH`.

The second is size. The whole front end already compiles to a [WebAssembly](#webassembly) bundle that runs in a browser and, gzipped, still fits on a 3.5-inch floppy disk. A self-hosted Prism is then the pleasing closure of that fact: a modern functional language with algebraic effects, typeclasses, and a formally verified core, shipped as a floppy-disk-sized binary of itself that compiles itself and can run on a microcontroller.

At which point, modulo an FFI, a full package ecosystem, and roughly every other thing a real language actually needs to be used in anger, I think Prism is "done", in the sense that it will never be used by anyone. But [that's fine](https://www.stephendiehl.com/posts/prism/)!

There is, if you squint, a purity argument in that. Every functional language chases referential transparency and forfeits it the instant a program runs, because running is where the effects leak back into the world. Haskell, to its great misfortune, is actually used, so it prints, allocates, warms a CPU, and nudges the universe a hair closer to heat death. Prism does none of this. Never run, it adds not one joule to the universe, and so attains the nirvana every other language strives towards: complete purity through unuse. Haskell is pure and used in the real world; Prism is useless and unused, which is a stronger form of purity.

## 25. Command-Line Interface {#command-line-interface}

The `prism` binary is one executable with a handful of subcommands. With no subcommand, a bare path argument compiles that file or project and no argument at all opens the [interactive shell](#the-interactive-shell). This section tabulates the full surface; every entry is generated from the same `clap` definition in `bin/prism.rs`.

### 25.1 Commands {#commands}

The surface is eleven top-level commands plus four noun groups (`exec`, `lineage`, `pkg`, `store`), each group collecting the verbs that share a subject.

#### Top-level

The everyday commands: build, run, check, format, inspect, document, compare.

| Command                              | What it does                                                                                                                                                                                                                                                                                        |
| ------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `prism`                              | Start the interactive shell (REPL).                                                                                                                                                                                                                                                                 |
| `prism <file.pr>`                    | Compile a single file to a native binary named after the source (`-o` overrides).                                                                                                                                                                                                                   |
| `prism <dir>` / `prism <prism.toml>` | Compile the project rooted at that manifest to `target/<package>`.                                                                                                                                                                                                                                  |
| `prism build [path]`                 | Compile the enclosing project (the nearest `prism.toml`); fails outside a project.                                                                                                                                                                                                                  |
| `prism run <file.pr>`                | Type-check and run in the interpreter, with real stdin/stdout (`exit(n)` becomes a real process exit); `--record PATH` writes a `.replay` trace, `--lineage PATH` a run sidecar.                                                                                                                    |
| `prism check [file.pr]`              | Type-check only; with no file, check the enclosing project; with a file, check that one source. Success is quiet and reported by exit status.                                                                                                                                                       |
| `prism fmt [paths..]`                | Format `.pr` files in place. No path formats the current tree recursively; `-` filters stdin to stdout.                                                                                                                                                                                             |
| `prism dump <phase> <file.pr>`       | Print one pipeline artifact (see [dump phases](#dump-phases)).                                                                                                                                                                                                                                      |
| `prism docs [path]`                  | Generate API documentation and a `docs.plineage` manifest; `--test` runs doctests, `--accept`/`--bless` rewrites stale output blocks, `--verify-manifest` rechecks the manifest.                                                                                                                    |
| `prism diff [<old> <new>]`           | With no paths, diff the enclosing project's Git `HEAD` against its working tree over `.pr` sources, showing semantic changes, their dependents cone, and compact definition-level surface deltas; with paths, diff two source revisions by content hash or two `.plineage` sidecars by logical key. |
| `prism report <file.pr>`             | Print every pipeline phase for a program.                                                                                                                                                                                                                                                           |
| `prism clean [path]`                 | Remove the project's `target/` build-artifact directory; an absent one is a no-op success.                                                                                                                                                                                                          |
| `prism repl`                         | Start the interactive shell (same as bare `prism`); accepts `--no-banner`.                                                                                                                                                                                                                          |

The project-shaped diff keeps the source view intentionally smaller than a file patch. It names each definition whose own behavior changed and shows only its old and new surface forms; unchanged files, surrounding declarations, and the dependent definitions whose own source did not move are omitted. The `-` rows are red and `+` rows green on an interactive terminal, with no ANSI escapes when output is redirected.

```console
$ prism diff
diff: 2 changed, 0 added, 0 removed, 95 unchanged
  ~ europe_london  a7a093434a3fa41e -> 2f10d6906e3fcb96
  ~ utc  7c2ae112ad1a57be -> 88caf0b8780e1e01
cone: 1 affected (find_zone)
surface:
  europe_london
    - fn europe_london() : Zone = Zone { name = "Europe/London", offset_minutes = 0 }
    + fn europe_london() : Zone = Zone { name = "Europe/London", offset_minutes = 1 }
  utc
    - fn utc() : Zone = Zone { name = "UTC", offset_minutes = 0 }
    + fn utc() : Zone = Zone { name = "UTC", offset_minutes = 4 }
```

#### `prism exec`: recorded and suspended execution

Verbs over a run as a value: replay a trace, cut a running program into a snapshot, resume one, step through a recording.

| Command                                   | What it does                                                                                                                                      |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| `prism exec replay <file.pr> <trace>`     | Re-run a recorded `.replay` trace, producing output byte-identical to the original.                                                               |
| `prism exec steps <file.pr> [--json]`     | Run the program and print each observation with the machine step at which it fired, the ruler a suspend budget is picked from.                    |
| `prism exec suspend <file.pr> --at N`     | Run the program, pause after `N` machine steps, and write the live continuation to a [`kont` envelope](#the-kont-envelope) (`-o` names the file). |
| `prism exec resume <file.pr> <snap.kont>` | Decode a `kont` envelope, check its bundle digest against the program's code identity, and run the continuation to completion.                    |
| `prism exec debug <file.pr> <trace>`      | Terminal reverse-step debugger over a recorded trace (step forward and back by replay-to-N).                                                      |

#### `prism lineage`: explaining artifacts

Verbs over a `.plineage` sidecar ([lineage](#build-lineage)): render it, interrogate it, verify it, certify a verification.

| Command                                     | What it does                                                                                                                                             |
| ------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `prism lineage show <file> [--json]`        | Render a build or run `.plineage` sidecar and explain why an artifact exists.                                                                            |
| `prism lineage why <sidecar> <output>`      | Walk a sidecar backward to explain why an output exists (`--json` for data).                                                                             |
| `prism lineage verify <sidecar> [--replay]` | Rehash a sidecar's recorded artifacts; `--replay` re-runs and re-checks a run sidecar; `--certify PATH` persists a passed verification as a certificate. |
| `prism lineage check-cert <cert> <sidecar>` | Check a lineage certificate against the sidecar it names; a subject mismatch or unrecognized claim is rejected.                                          |

#### `prism pkg`: the package manager

Verbs over projects and the package universe ([the package manager](#package-manager)).

| Command                                            | What it does                                                                                                                                                                                                                                                                                            |
| -------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `prism pkg init`                                   | Prompt for a package name and directory, then create a minimal `prism.toml` and `src/main.pr`.                                                                                                                                                                                                          |
| `prism pkg add <dep>`                              | Add a dependency to `prism.toml` (path, `git` URL plus tag, or hash pin) and update `prism.lock`.                                                                                                                                                                                                       |
| `prism pkg why <name>`                             | Explain why a definition is in the resolved dependency closure.                                                                                                                                                                                                                                         |
| `prism pkg export [path]`                          | Write the project's content-addressed closure back out as source text.                                                                                                                                                                                                                                  |
| `prism pkg publish`                                | Sign and record a package-identity-to-root binding in the signed index; `--tag`, `--name`, and `--origin` set the row.                                                                                                                                                                                  |
| `prism pkg audit`                                  | Verify the signed index and the transparency log; `--allow-unsigned` tolerates the unsigned seam.                                                                                                                                                                                                       |
| `prism pkg check-world [path] [--json] [--strict]` | Check package projects in a package universe and report digest-addressed source, Std, dependency, compiler, and compatibility identities plus per-package gates; `--baseline REPORT` names public definitions that changed behavior; `--strict-usage` promotes usage-summary drift to a strict failure. |
| `prism pkg accept-usage [path]`                    | Regenerate a package's usage summary and write it to `usage-summary.md` at the package root, creating or reseating the usage gate's golden.                                                                                                                                                             |

#### `prism store`: the content-addressed store

Verbs over content-addressed code identity ([the store](#content-addressed-core)).

| Command                                 | What it does                                                                                              |
| --------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| `prism store wire <file.pr> [--accept]` | Check the `stable` rung goldens of a file; `--accept` recomputes and reseats them in place.               |
| `prism store attest <file.pr>`          | Compile through two independent backends, attest byte-identical output, and cross-check the signed index. |

### 25.2 Flags {#flags}

The four optimizer/backend flags are global (`-O`, `--passes`, `--backend-opt` apply to any subcommand, since they affect building, running, and `dump core`); the rest are positional to the command shown. `-h`/`--help` works on the binary and every subcommand, and `-V`/`--version` on the binary.

| Flag                          | Applies to           | Default                        | Meaning                                                                                                                                                                        |
| ----------------------------- | -------------------- | ------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `-o`, `--out <PATH>`          | bare build, `build`  | source stem, or `target/<pkg>` | Output path for the compiled binary.                                                                                                                                           |
| `--mlir`                      | bare build, `build`  | off (LLVM)                     | Lower through the MLIR backend instead of the textual LLVM emitter (requires the `mlir` build feature).                                                                        |
| `-O`, `--opt [LEVEL]`         | global               | `1` (bare `-O` is `2`)         | Core optimizer level (`0`/`1`/`2`); see [optimization levels](#optimization-levels).                                                                                           |
| `--passes <SPEC>`             | global               | unset                          | Run an explicit ordered pass list, overriding `-O` (mutually exclusive); see [controlling the pipeline](#explicit-pass-lists).                                                 |
| `--no-<pass>`                 | global               | off                            | Remove one pass from the pipeline: `--no-erase-newtypes`, `--no-specialize`, `--no-simplify`, `--no-inline`, `--no-cse`; see [controlling the pipeline](#explicit-pass-lists). |
| `--backend-opt <LEVEL>`       | global               | `2`                            | LLVM-backend opt level handed to the C compiler as `-O<LEVEL>`: `0`, `1`, `2`, `3`, or `s`/`z` for size. Distinct from `-O`, which tunes Prism's Core optimizer.               |
| `--no-banner`                 | `repl`               | off                            | Skip the REPL startup banner.                                                                                                                                                  |
| `--check`                     | `fmt`                | off                            | Check only: exit 1 if any file is not canonical, write nothing.                                                                                                                |
| `--time-compile`              | compiling commands   | off, or `PRISM_TIME_COMPILE=1` | Emit one tab-separated timing row per compiler phase on stderr: phase, wall time, abbreviated input artifact key, cache status, output key and counts where they exist.        |
| `--record <PATH>`             | `run`                | off                            | Write a `.replay` trace of the run to `PATH`, replayable with `prism exec replay`.                                                                                             |
| `--lineage <PATH>`            | `run`                | off                            | Write a run `.plineage` sidecar to `PATH` (requires `--record`, which it explains); see [lineage](#build-lineage).                                                             |
| `--certify <PATH>`            | `lineage verify`     | off                            | Persist a passed verification as a digest-named certificate (`replay-verified` with `--replay`, else `lineage-verified`).                                                      |
| `--verify-manifest`           | `docs`               | off                            | Verify the committed `docs.plineage` manifest against the output pages; rehash pages, confirm roots have not drifted, write nothing.                                           |
| `--baseline <PATH>`           | `pkg check-world`    | off                            | Diff each package's public-surface hashes against a prior `--json` report and name the changed definitions.                                                                    |
| `--strict-usage`              | `pkg check-world`    | off                            | With `--strict`, fail on usage-summary drift; a package with no committed summary still reports missing without failing.                                                       |
| `--accept`                    | `store wire`, `docs` | off                            | Reseat stale goldens in place (`wire` rung digests, `docs` expected-output blocks); alias `--bless` for `docs`.                                                                |
| `--tag`, `--name`, `--origin` | `pkg publish`        | source-derived                 | The tag, display name, and canonical package identity of the published index row.                                                                                              |
| `--allow-unsigned`            | `pkg audit`          | off                            | Accept an unsigned artifact instead of reporting it (the unsigned signing seam).                                                                                               |
| `-h`, `--help`                | binary, all commands |                                | Print help.                                                                                                                                                                    |
| `-V`, `--version`             | binary               |                                | Print the version.                                                                                                                                                             |

### 25.3 Dump Phases {#dump-phases}

`prism dump <phase> <file.pr>` prints one intermediate form. The optimizer flags above apply, so `dump core` reflects the selected `-O` level.

| `<phase>`               | Output                                                                                                         |
| ----------------------- | -------------------------------------------------------------------------------------------------------------- |
| `tokens`                | The token stream after lexing and layout.                                                                      |
| `ast`                   | The surface AST.                                                                                               |
| `types`                 | Each definition's inferred type and effect row.                                                                |
| `core`                  | The CBPV / ANF core after elaboration and the optimizer.                                                       |
| `core-json`             | The core as a JSON tree the Lean model reads (the [differential oracle](#the-model-as-a-differential-oracle)). |
| `core-hash`             | A [content-addressed hash](#content-addressed-core) of each definition's elaborated core.                      |
| `native-kont-table`     | The deterministic native-symbol-to-definition-hash table embedded into native LLVM builds.                     |
| `native-kont-state-map` | The versioned native state map for entry ABI-word slots embedded into native LLVM builds.                      |
| `fbip`                  | Core after reference-count insertion and in-place reuse.                                                       |
| `lowered`               | Core after [effect lowering](#effect-lowering) (handlers and operations removed).                              |
| `tier`                  | The [effect-lowering](#effect-lowering) strategy the program's handlers compile to.                            |
| `captures`              | Closure-capture facts, each classified portable, nonportable, or unknown for a move across a suspend boundary. |
| `usage-summary`         | A per-definition table of allocation, `fip`/`fbip`, borrow, and effect-row facts, committable as a golden.     |
| `usage-summary-md`      | The same usage facts as a markdown pipe table, the projection `prism pkg check-world`'s usage gate compares.   |
| `usage-summary-json`    | The same usage facts as a JSON object, for tooling that consumes the summary programmatically.                 |
| `shape`                 | The structural shape digest of each datatype, effect, and class.                                               |
| `stdlib-hash`           | The standard library's Merkle root ([content-addressed core](#content-addressed-core)).                        |
| `namespace`             | The versioned definition-layer export, wrapped in the wire envelope header.                                    |
| `llvm`                  | The emitted LLVM IR.                                                                                           |
| `mlir`                  | The emitted textual MLIR (requires the `mlir` build feature).                                                  |

`dump captures` is a read-only analysis over the program's own elaborated core. For every lambda and thunk it lists what the closure closes over (a source value or a call to a top-level definition) and what scoped operations it performs (a `var` cell's get/set, a named handler instance's private op), and classifies each fact as **portable**, **nonportable**, or **unknown** for a hypothetical move across a suspend boundary. A value type defers to the suspend codec's own encodability judgment; a top-level definition is portable because it travels as a content-addressed code reference; a `var` cell and a named handler instance are nonportable because their backing scope ends before a moved computation could resume. The classification is conservative in one direction: nothing is called portable unless it provably is, so a false "unknown" only costs a diagnostic while a false "portable" is impossible. The dump is diagnostic and changes no compilation output.

`dump usage-summary` prints one tab-separated line per definition, name-sorted, of the usage facts the compiler already holds: the `@ noalloc` allocation certificate, the `fip`/`fbip` discipline, the per-parameter borrow mask (`b` for a borrowed parameter, `-` for an owned one), and the checked effect row. A header names the format version and the whole-program [lowering tier](#effect-lowering); the tier is a whole-program cost decision, so it heads the table rather than repeating on every line. The table is scoped to the program's own definitions, the entry file plus the modules its own source directories serve, so an imported library's rows never appear and a committed summary drifts only when the program's own source changes. Every fact is read from its canonical source and none is recomputed.

The same facts project three ways: `usage-summary` is the tab-separated form above, `usage-summary-md` renders them as an aligned markdown pipe table (cells escape `|`, so a row-polymorphic tail like `{X | e}` cannot break the table, and the alignment matches the repository formatter so a committed file is stable under it), and `usage-summary-json` emits one JSON object for tooling. A package may commit the markdown projection as `usage-summary.md` at its root; `prism pkg check-world` regenerates it and reports drift as the `usage` gate, naming the first differing line. `prism pkg accept-usage <pkg>` writes that golden, creating it the first time and reseating a drifted one with the same byte-stable regeneration, the same accept discipline as the tier manifest and the wire rung goldens. The gate is report-only by default: drift is printed but excluded from `--strict` failure, so packages can adopt the golden incrementally, and a package that commits no summary reports the gate as missing rather than failing. `--strict-usage` opts a CI lane in, promoting usage drift to a strict failure while a missing summary stays non-fatal, since missing means not opted in rather than wrong. In the `--json` report the gate carries its evidence: `usage` (`missing`, `passed`, `failed`), `usage_drift` naming the first differing line with expected and actual, `usage_format` naming the artifact format the golden is compared under (`usage-summary-md`), and `usage_tier`, the whole-program lowering tier that heads the summary, present only when a summary was regenerated. The tier is deliberately a single whole-program scalar, the same fact the summary's header states; per-definition rows carry no tier, so the JSON claims none.

### 25.4 Environment Variables {#environment-variables}

These are read by the compiler at build time. `PRISM_CC`, `PRISM_CC_FLAGS`, and `LLVM_SYS_221_PREFIX` are the ones a normal build cares about; the rest are diagnostic or opt-out knobs.

| Variable                     | Effect                                                                                                                                                                |
| ---------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `PRISM_CC`                   | C compiler used to assemble and link the runtime (default `clang`).                                                                                                   |
| `PRISM_CC_FLAGS`             | Extra flags passed to the C compiler (e.g. `-march=native`, `-g`, `-DPRISM_RT_DEBUG`).                                                                                |
| `PRISM_BACKEND_OPT`          | LLVM-backend opt level (same values as `--backend-opt`); the flag wins when both are set.                                                                             |
| `PRISM_OPT_LEVEL`            | Core optimizer level used when `-O` is not passed (same values as `-O`).                                                                                              |
| `PRISM_NATIVE_EFFECTS`       | `0` opts out of the native delimited-continuation effect runtime, back to the mutually recursive free-monad driver; on otherwise.                                     |
| `PRISM_NATIVE_KONT_FRAMES`   | If set, add frame-preservation flags to native builds so experimental native-kont frame capture is less optimizer-dependent; off by default.                          |
| `PRISM_NO_SPECIALIZE`        | If set, skip the dictionary-specialization pass.                                                                                                                      |
| `PRISM_CORE_LINT`            | If set, run Core Lint (IR well-formedness) between every optimizer pass.                                                                                              |
| `PRISM_RT_CHECKS`            | If set, compile the C runtime with `-DPRISM_RT_DEBUG` (cell-validity backstop); off by default so release builds stay zero-overhead.                                  |
| `PRISM_OPT_STATS`            | If set, print per-pass optimizer telemetry to stderr.                                                                                                                 |
| `PRISM_DUMP_CORE`            | If set to a directory, dump the core before and after each pass for debugging the optimizer.                                                                          |
| `PRISM_QUIET`                | Silence the non-fatal fallback / matcher-drift warnings on stderr.                                                                                                    |
| `PRISM_STORE`                | Enable the on-disk [content-addressed store](#the-on-disk-store); off by default.                                                                                     |
| `PRISM_STORE_PATH`           | Where the store's object and metadata layers live (resolved through `store::resolve_store_path`).                                                                     |
| `PRISM_SIGN_MODE`            | Signing seam for the [package index](#package-manager): `ssh` (`ssh-keygen -Y sign`), `minisign`, or `unsigned`; an invalid value warns once and falls back to `ssh`. |
| `PRISM_SIGN_KEY`             | Signing key for `publish` (the `minisign` secret key or the `ssh` key path).                                                                                          |
| `PRISM_SIGN_IDENTITY`        | Signer identity recorded and checked in `ssh` mode.                                                                                                                   |
| `PRISM_SIGN_ALLOWED_SIGNERS` | Allowed-signers file that `audit` verifies an `ssh` signature against.                                                                                                |
| `LLVM_SYS_221_PREFIX`        | Where the LLVM 22 dev libraries live, for linking the compiler itself (a build-of-`prism` setting).                                                                   |
| `VISUAL`, `EDITOR`           | Editor launched by the REPL `:edit` command (`VISUAL` first, then `EDITOR`).                                                                                          |
| `HOME`                       | REPL history is persisted at `$HOME/.prism_history`.                                                                                                                  |

A second set is read at runtime by the generated program, for the instrumentation the test gates assert. They print to stderr and never change output.

| Variable            | Effect                                                                                                   |
| ------------------- | -------------------------------------------------------------------------------------------------------- |
| `PRISM_CHECK_LEAKS` | At exit, report any heap cell allocated but not freed (the deterministic leak gate `parity.rs` asserts). |
| `PRISM_REUSE_STATS` | Print how many constructor allocations were satisfied by in-place FBIP reuse.                            |
| `PRISM_EFFOP_STATS` | Print how many free-monad effect-operation cells were allocated (zero on the fully fused path).          |
| `PRISM_DRIVE_STATS` | Print native effect-driver statistics.                                                                   |

The runtime also has two compile-time switches. `-DPRISM_RT_DEBUG` inserts a structural validity check at every cell dereference (non-null, aligned, positive refcount, in-bounds field), aborting with a diagnostic instead of corrupting memory; the canonical way to turn it on is `PRISM_RT_CHECKS` (which adds the define to the `cc` invocation), and `PRISM_CC_FLAGS=-DPRISM_RT_DEBUG` also works. It is off by default so release builds and the parity oracle stay byte-identical and zero-overhead; it is the always-available structural backstop for builds where ASan/UBSan are unavailable. The `mimalloc` cargo feature routes the runtime's allocations through mimalloc.

### 25.5 REPL Commands {#repl-commands}

Inside the shell, input beginning with `:` is a command; anything else is an expression or declaration to evaluate. The full command set, the `:set` toggles, and the multi-line block syntax are documented under [the interactive shell](#the-interactive-shell).

## 26. Diagnostics {#diagnostics}

A diagnostic is a value, not a string. Every error the compiler can produce is a variant of a structured catalogue (`src/error/`), each variant owning one stable `E`-code; the rendered message is payload, never the discriminator a caller or renderer matches on. A code is permanent once assigned, so a diagnostic can be looked up years later, scripted against, and searched, and a message can be reworded freely without breaking anything that keyed on the code.

The philosophy is that an error message is the interface the language presents at the moment of failure, and it owes the user three things. First, **the site**: every diagnostic carries a span and renders a source ribbon pointing at the offending characters, and a type error raised while checking a definition names its enclosing frame (`in \`main\`: unbound variable 'MkCelsius'`), so an error deep in an application still says whose body it fired in. Second, **the cause in the program's own vocabulary**: the unknown constructor by name, the two rows that failed to unify, the arity that did not match, not the internal state of the checker. Third, **the remedy where one is mechanical**: an unknown name close to a name in scope gets a "did you mean" hint (Damerau-Levenshtein distance with a threshold that scales with the name's length, so a long name tolerates a proportionally larger typo without matching wild guesses), and a removed or re-spelled construct gets a migration error that states the new spelling outright rather than a generic parse failure, so an upgrade is a series of pointed instructions instead of an archaeology project.

Codes are banded by the phase and domain that owns them, walking the pipeline in order:

| band    | domain                                                 |
| ------- | ------------------------------------------------------ |
| `E1xxx` | types and unification                                  |
| `E2xxx` | scope and unbound names                                |
| `E3xxx` | classes, instances, and coherence                      |
| `E4xxx` | patterns and matching                                  |
| `E5xxx` | effects, handlers, and usage contracts                 |
| `E6xxx` | declarations and desugaring                            |
| `E70xx` | lexing                                                 |
| `E71xx` | parsing                                                |
| `E72xx` | module, project, and package resolution                |
| `E74xx` | codegen, documentation, formatting, dump, verification |
| `E75xx` | runtime evaluation, replay, and the debugger           |
| `E76xx` | file and process IO                                    |
| `E9xxx` | internal compiler errors                               |

The `E1xxx` through `E6xxx` bands are the type checker's structured catalogue, keyed by what the user wrote; the `E7xxx` bands are the phase errors that cross the compiler's API boundary, keyed by which subsystem failed. `E9999` is the internal-invariant band: a condition the compiler believed impossible, rendered with an apology and a request to report it, because an internal error is a compiler bug by definition. Warnings ride the same channel with the same discipline (a deprecation names the definition, the suggestion, and the use site) but never stop a build: by the determinism contract a warning is a diagnostic, not a semantic.

## 27. Prism as a Library {#prism-as-a-library}

The `prism` crate is usable as a compiler library when you want the language machinery without the CLI wrapper. The high-level entry points are re-exported from `src/lib.rs`: `prism::check(src)` type-checks a Rust `&str` and returns the inferred declarations, `prism::interpret(src)` runs it in the tree-walking interpreter with output captured in the returned `eval::Run`, and `prism::build_at(src, base, out)` / `prism::build_on(src, roots, out, cfg)` compile native binaries when the `native` feature is enabled. For live IO, use `prism::interpret_io_on(src, roots, out_sink, input, cfg)` or `prism::interpret_io_on_with_args` so stdin, stdout, argv, scheduler, optimizer level, and effect-lowering flags are all explicit values rather than ambient CLI state. For inspection, `prism::dump_on(phase, src, roots, cfg)`, `prism::core_of(src)`, `prism::core_ir(src)`, `prism::emit_ir(src)`, `prism::namespace_root(src, roots)`, and `prism::shape_digests_of(src)` are the same surfaces the command line uses.

The smallest embedding is just a string:

```rust,ignore
let src = prism::with_prelude("fn main() = print(1 + 2)");
let checked = prism::check(&src)?;
let run = prism::interpret(&src)?;
assert_eq!(run.term, "3");
```

For projects or custom module sources, pass explicit roots instead of relying on the current directory: `prism::default_roots(base)` gives the normal single-file search path, while `prism::project_roots`, `prism::project_roots_with_std`, and `prism::project_roots_with_packages_and_std` are the project/package forms. The important rule is the same identity rule the CLI follows: module roots, Std roots, package roots, stores, lockfiles, and behavior-affecting flags are inputs to the driver call, not hidden globals.

A different front end should target the same `syntax::ast::Program<Surface>` or go lower and produce `core::Core` directly. The ordinary route is `lex::lex` / `parse::parse`, module resolution through `resolve::resolve_modules_in`, desugaring through `syntax::desugar::desugar`, typechecking through the driver (`check_on`) or the internal checker, and elaboration through `core::elaborate` into Core. If you produce Core yourself, you have taken responsibility for the invariants the front end usually proves: names are resolved, types and effects are coherent, builtins are used with the right arity, and the Core is well-formed enough for optimization, effect lowering, reference counting, interpretation, and codegen.

The tool that checks those invariants is Core Lint, exported as `prism::core::lint_core`. It is stage-aware: a `PassStage` argument says where in the pipeline the Core sits, because the two families of node have opposite legality across the effect-lowering seam. Effect nodes (`Do`, `Handle`, `Mask`) are legal only before lowering, and the reference-counting and local-cell nodes (`Dup`, `Drop`, `WithReuse`, `Reuse`, `RefNew`/`RefGet`/`RefSet`) are legal only after it. Lint at `PassStage::PreLowering` on Core you assembled or transformed by hand and it rejects any runtime node that leaked in early; lint at `PassStage::Late` on lowered Core and it rejects any effect node lowering should have erased. It also checks scoping (every free variable resolves to a parameter or a top-level function) and reuse-token linearity (no token spent twice on one path). A violation comes back as `Err(Vec<String>)`, one message per problem, attributed to the offending function.

```rust,ignore
use prism::core::{lint_core, Comp, Core, CoreFn, PassStage, Value};
use prism::sym::Sym;

// fn main = return 42
let prog = Core {
    fns: vec![CoreFn {
        name: Sym::new("main"),
        params: vec![],
        body: Comp::Return(Value::Int(42)),
        dict_arity: 0,
    }],
};
assert!(lint_core(&prog, PassStage::PreLowering).is_ok());
```

This snippet mirrors the runnable doctest on `prism::core::lint_core` (in `src/core/opt/lint.rs`), which CI compiles and runs under `cargo test --doc`. That doctest, including the companion case where a pre-lowering lint rejects a stray runtime node, is the tested source of truth; the block here cannot drift from it silently.

To read Core back out, the pretty printers are exported from `prism::core`. `pp_core_pretty` renders a whole program in the indented, one-bind-per-line notation `dump core` prints; `pp_core` renders the same program in the compact single-line form the snapshot tests pin; `pp_comp` renders a single computation and `pp_value` a single value. They are the same functions the `dump` surfaces call, so Core you produced or rewrote prints in exactly the notation the rest of the toolchain reads.

A different backend should start from Core, not from the surface language. The easiest in-tree pattern is the shared emitter: `src/codegen/emit.rs` walks lowered Core once and delegates instruction spelling to the `Isa` trait, with LLVM and MLIR as the two current instances. For an out-of-tree target, implement the public `prism::codegen::Isa` interface and pass it with the lowered Core and constructor table to `prism::codegen::emit_with_isa`; the associated `Buf`, `IntOp`, `Cmp`, `FloatBinOp`, and `FloatIntrinsic` types are exported from the same module. If the target can share Prism's runtime representation, implement the small instruction vocabulary (`load`, `store`, `call`, `switch`, `ret`, merge blocks, tail calls, and the primitive arithmetic/float operations) and let the existing Core walk keep evaluation order, reference counting, handler lowering, and FBIP reuse centralized. If it cannot share that representation, treat `core::Core` as the semantic contract and write a backend that re-proves the same byte-parity obligations the LLVM path is held to.

In other words: the library API is quite usable and the compiler internals are fairly modular, so it should be easy to hack on if you feel so inclined to do something weird.

## 28. Warranty {#warranty}

Prism is released under the vanilla [MIT License](https://github.com/sdiehl/prism/blob/main/LICENSE). Which in lawyer speak is essentially, do whatever the fuck you like. Fork it, sell it, embed it in a toaster, put it in a spaceship. Whatever.

What MIT also means, in the traditional all-caps liturgy, is that the software is provided "as is", without warranty of any kind. Do take that clause seriously here. If you have downloaded software written by some random compiler nerd in London and you are expecting it to be production-ready, bug-free, or in any sense safe to put under real money, you must be truly, magnificently mad.

This is an experiment. The entire premise is to see how far one person can push modern language design as a hobby: principal effect inference, content-addressed everything, a Lean model checking the compiler against itself, running continuations you can freeze to bytes and move between same-origin browser contexts, incremental computation you can pause in the middle of and warm back up across a restart, five lowering tiers that are supposed to be observationally identical and deterministic. The fun stuffz. It is one dude with a family, some late evenings, and an unreasonable amount of love for functional programming. It compiles. It even runs. Whether it should be anywhere near your infrastructure is a question the license already answered, in capital letters, and I am inclined to agree with it.

If it breaks, you get to keep both pieces, and you are welcome to return it for a full refund of the purchase price. If it works, that is frankly as much a surprise to me as it is to you. Enjoy responsibly.
