# The Prism Language Specification {#the-prism-language-specification}

Prism is a strict, impure functional language in the ML family whose type system tracks side effects. This document defines the surface language: its lexical structure, grammar, type system, and evaluation. It describes the language as the `prism` compiler accepts it; limitations are stated precisely where they apply.

## 1. Introduction {#introduction}

A Prism program is a set of modules, each a file of declarations. The surface language elaborates to a strict, call-by-push-value core ([Levy, 2004](bibliography.md#levy-2004)) in A-normal form (the companion [Compiler](./compiler.md) document), compiles to native code through LLVM, and is managed by deterministic reference counting rather than a garbage collector.

Three things distinguish Prism from its ML and Haskell ancestors. It is **strict**, with laziness opt-in through thunks over a [call-by-push-value](./compiler.md#the-core-calculus) core, so evaluation and effect order are left to right and explicit. Side effects are inferred, extensible **effect rows** ([effects and handlers](#effects-and-handlers)) that combine structurally across calls instead of through monads and track both observability and capability ([capability effects and IO](#capability-effects-and-io)): an operation handled inside a function does not appear in its type, so internally effectful code is reused as pure, and a function that reads the outside world names the part it reads (`Console`, `FileSystem`, `Random`, `Env`) rather than a blanket `IO`. The same reference-count discipline both frees memory and performs **fully-in-place (FBIP) update** ([declarations and programs](#declarations-and-programs)), compiling record updates and derived setters to in-place writes on uniquely owned values (those that a reference count proves have no other live reference; see [reference counting and FBIP reuse](./compiler.md#reference-counting-and-fbip-reuse)). Beyond these, the language provides record and replay of a program's interaction with the world over the capability effects ([record and replay](#record-and-replay)), derived lenses and use-site optic paths for nested access and update ([optic paths](#optic-paths)), and fusing stream combinators ([streams](#streams)).

This specification proceeds in dependency order: notation, lexical structure, grammar, types, then the constructs the grammar describes.

## 2. Notation {#notation}

Grammar is given in the following EBNF. A _terminal_ is a literal token written in double quotes; a _nonterminal_ is a lower-case name. The character classes are the ASCII letters (`letter`), the two cases (`lower`, `upper`), the decimal digits (`digit`), any printable character (`graphic`), and any character other than `"`, `\`, or a newline (`strchar`). These are primitives, not grammar nonterminals.

```text
{{#include ../../models/grammar.ebnf:notation}}
```

Identifiers in productions name the tokens defined in the [lexical structure](#lexical-structure) (`varid`, `conid`, `qualid`, `integer`, `float`, `char`, `string`) and the character classes defined just above. The [layout](#layout) algorithm inserts block delimiters that the grammar then treats as ordinary terminals.

## 3. Lexical Structure {#lexical-structure}

Source text is UTF-8. Tokens are lexed by longest match, then the stream is rewritten by the [layout algorithm](#layout). Whitespace and comments separate tokens and are otherwise insignificant except as layout boundaries.

```text
{{#include ../../models/grammar.ebnf:lexical}}
```

### 3.1 Identifiers {#identifiers}

Prism distinguishes identifiers by initial case. A `varid` begins with a lower-case letter or underscore and names a variable, function, parameter, or record field. A `conid` begins with an upper-case letter and names a type, data constructor, type class, or effect. A `qualid` is a dotted path such as `Data.Map` or `Map.insert`; it is lexed as a single token so that a module path never collides with field access.

### 3.2 Keywords {#keywords}

The following are reserved and may not be used as identifiers.

|            |             |              |           |            |
| ---------- | ----------- | ------------ | --------- | ---------- |
| `fn`       | `fip`       | `fbip`       | `pub`     | `import`   |
| `as`       | `type`      | `newtype`    | `opaque`  | `alias`    |
| `effect`   | `error`     | `throw`      | `try`     | `catch`    |
| `transact` | `class`     | `instance`   | `pattern` | `deriving` |
| `where`    | `given`     | `handle`     | `with`    | `handler`  |
| `mask`     | `ctl`       | `final`      | `fun`     | `val`      |
| `return`   | `let`       | `var`        | `borrow`  | `in`       |
| `for`      | `do`        | `if`         | `then`    | `else`     |
| `elif`     | `match`     | `of`         | `forall`  | `true`     |
| `false`    | `while`     | `loop`       | `break`   | `continue` |
| `using`    | `canonical` | `replayable` |           |            |

The built-in type names `Int`, `I64`, `U64`, `Bool`, `Unit`, `Float`, `Char`, and `String` are also reserved. The prelude effect names `Console`, `FileSystem`, `Random`, and `Env`, the [capability effects](#capability-effects-and-io), are reserved as well.

### 3.3 Operators and Punctuation {#operators-and-punctuation}

The operator set is fixed; the language has no user-defined operators. Every comparison operator, and every arithmetic operator except `%` and `^`, also has a floating-point form suffixed with a dot. Exponentiation `^` is a single operator over both `Int` and `Float` ([exponentiation](#exponentiation)).

| Class      | Operators                                                               |
| ---------- | ----------------------------------------------------------------------- |
| Arithmetic | `+` `-` `*` `/` `%` `^` and float `+.` `-.` `*.` `/.`                   |
| Comparison | `==` `/=` `<` `<=` `>` `>=` and float `==.` `/=.` `<.` `<=.` `>.` `>=.` |
| Logical    | `&&` `\|\|`                                                             |
| Pipeline   | `\|>` `>>` `<<`                                                         |
| Failure    | `??` `?.` `?`                                                           |
| Arrows     | `->` `<-` `=>`                                                          |
| Binding    | `=` `:=` `:` and compound `+=` `-=` `*=` `%=`                           |
| Effect     | `!`                                                                     |
| Brackets   | `(` `)` `{` `}` `[` `]`                                                 |
| Other      | `,` `.` `..` `\|` `\`                                                   |

### 3.4 Literals {#literals}

An `integer` is a sequence of decimal digits. A value that fits in a machine word is an immediate; a larger literal is an arbitrary-precision integer (bignum). The suffix `i64` or `u64` selects a fixed-width 64-bit lane that wraps on overflow. A `float` is an IEEE-754 double. A `char` is a single Unicode scalar in single quotes. A `string` is double-quoted UTF-8.

The escape sequences `\n`, `\t`, `\r`, `\\`, `\"`, `\{`, and `\}` are recognized in both character and string literals; a character literal additionally accepts `\'`.

### 3.5 String Interpolation {#string-interpolation}

Within a string, an unescaped `{ expr }` is an interpolation hole. The hole text is re-lexed at its source position and elaborated as an expression whose `Show` value is spliced into the string. A hole runs to its matching `}`, balancing nested braces and string literals, so a hole may itself contain a string with braces. A literal brace outside a hole is written `\{` or `\}`. An empty hole, an unterminated hole, and an unterminated string are each lexical errors. The catch arms of the error example under [errors and failure](#errors-and-failure) use interpolation, as in `"no such key: {k}"`.

### 3.6 Layout {#layout}

Prism uses the offside rule: indentation, not explicit braces, delimits a block. A layout block opens after any of the keywords or symbols `=`, `then`, `else`, `=>`, `of`, `with`, `handler`, `do`, `where`, `try`, `catch`, `transact`, `loop`, and after `fn` (a `while` block opens at its `do`). The first token after such an opener sets the block's indentation column; a later line at that column starts a new item in the block, and a line indented less closes the block. Explicit `{` `}` override layout and may always be used in place of an implicit block, as in the brace-delimited handler arms of the [masking](#masking) example.

## 4. Surface Grammar {#surface-grammar}

A program is a layout-delimited sequence of top-level declarations.

```text
{{#include ../../models/grammar.ebnf:program}}
```

```text
{{#include ../../models/grammar.ebnf:decls}}
```

Type syntax. A function type carries an optional effect _row_ on its codomain ([effects and handlers](#effects-and-handlers)); the row binds to a function type only.

```text
{{#include ../../models/grammar.ebnf:types}}
```

Expressions, patterns, and the handler block of `handle`/`try` (used in [effects and handlers](#effects-and-handlers)).

```text
{{#include ../../models/grammar.ebnf:expr}}
```

```text
{{#include ../../models/grammar.ebnf:pattern}}
```

```text
{{#include ../../models/grammar.ebnf:handler}}
```

### 4.1 Operator Precedence {#operator-precedence}

The table gives the binding of each operator, loosest to tightest. Levels 1 to 9 are the `binop` operators of the grammar; level 10 is application, field access, and the postfix failure operators, which bind tighter than every `binop`.

| Level | Operators                                     | Associativity |
| ----- | --------------------------------------------- | ------------- |
| 1     | `??`                                          | right         |
| 2     | `\|>`                                         | left          |
| 3     | `>>` `<<`                                     | left          |
| 4     | `\|\|`                                        | left          |
| 5     | `&&`                                          | left          |
| 6     | `==` `/=` `<` `<=` `>` `>=` (and float forms) | none          |
| 7     | `+` `-` (and float forms)                     | left          |
| 8     | `*` `/` `%`, and float `*.` `/.`              | left          |
| 9     | `^`                                           | right         |
| 10    | `f(...)` `a[i]` `.field` `?.field` `?`        | left          |

## 5. Types and Kinds {#types-and-kinds}

Prism infers types by the bidirectional, higher-rank inference algorithm of [Dunfield & Krishnaswami (2013)](bibliography.md#dunfield-krishnaswami-2013). An unannotated declaration infers its principal type; an annotated one is checked against the annotation. Annotations are required for rank-N polymorphism, since a nested `forall` cannot be inferred.

Quantification is _predicative_: a type-constructor argument and an inferred type variable range over monomorphic types, so a `forall` may not be written directly as a type argument (`List(forall a. (a) -> a)` is rejected as impredicative). Higher-rank types are allowed wherever they are not a type argument, namely as a function parameter, a function result, and a declared data field; a polymorphic value can be carried through a generic container by wrapping it in a data type with a polymorphic field.

### 5.1 Types {#types}

The scalar types are `Int` (arbitrary precision), `I64`, `U64`, `Float`, `Bool`, `Char`, `String`, and `Unit`. A type constructor applied to arguments is written `Con(t, ...)`; the list type has the sugar `[t]` for `List(t)`. A tuple type is `(t, ...)`. A function type is `(t, ...) -> u`, optionally carrying an effect row on `u`. A universally quantified type is `forall a. t`. Type variables are `varid`s.

### 5.2 Kinds {#kinds}

A type has kind `*` (a type of values) or `* -> *` (a type constructor awaiting one argument), and so on; `List` has kind `* -> *`, since `List(Int)` is a type only once `Int` is supplied. A class parameter may range over a constructor of kind `* -> *`, applied as `f(a)` in method signatures; see [type classes](#type-classes). There is no explicit kind-checking phase: well-kindedness is enforced during unification, which requires a constructor and its arguments to agree in arity.

### 5.3 Inference, Generalization, and Defaulting {#inference-generalization-and-defaulting}

A row is built from _labels_, the effect names of [effects and handlers](#effects-and-handlers) (a parametric effect's label carries type arguments). It is _closed_ when it ends in a fixed set of labels and _open_ when it ends in a row variable (`! {L | r}`), which stands for further labels the caller may add. An unannotated binding is generalized over its free type and row variables not fixed by the surrounding scope. Two cases default rather than generalize, both resolved in one pass at generalization. A numeric operand of an arithmetic or comparison operator left otherwise unconstrained defaults to `Int`; because the default is deferred to that pass rather than applied at the operator, a later use that fixes the operand to a fixed-width lane (`I64`/`U64`) takes precedence, so `x + y` followed by an `i64` use of `x` is fixed-width, not `Int`. An open row left unconstrained at a monomorphic declaration (one with no remaining free row variable) defaults to empty (pure); an effect-polymorphic declaration keeps its row variable, as `traverse` does in the prelude ([the standard prelude](#the-standard-prelude)).

### 5.4 Subsumption and Row Equivalence {#subsumption-and-row-equivalence}

Checking a value against an expected type uses subsumption, not equality. A more polymorphic type is accepted where a less polymorphic one is expected: a `forall` on the expected side introduces a rigid variable the value must satisfy for all instances, and a `forall` on the value side is instantiated to meet the expectation. Function subtyping is contravariant in the arguments and covariant in the result, so a function accepting more and returning less may stand in for one accepting less and returning more.

Effect rows are compared up to reordering: `! {A, B}` and `! {B, A}` are the same row, because unification hoists a demanded label to the head of the other row before matching the tails. An open row `! {A | r}` unifies with any row that provides `A` by binding `r` to the remainder; for instance `! {A | r}` unifies with `! {A, B}` by binding `r` to `{B}`. This is how a caller's row absorbs a callee's. A unification that would make a row contain itself is rejected, so recursive effect rows do not arise.

### 5.5 Fixed-Width Integers {#fixed-width-integers}

`Int` is arbitrary precision. `I64` and `U64` are the signed two's-complement and unsigned 64-bit lanes; they wrap on overflow rather than promoting to a bignum. Their operations are named builtins, not operators, since the surface `+`, `-`, and so on target `Int` and `Float`. Each takes two operands of the lane type.

| Family     | Operations (and the `u64_*` counterparts)                   |
| ---------- | ----------------------------------------------------------- |
| Arithmetic | `i64_add` `i64_sub` `i64_mul` `i64_div` `i64_rem` `i64_cmp` |
| Bitwise    | `i64_and` `i64_or` `i64_xor`                                |
| Shift      | `i64_shl` `i64_shr`                                         |

`and`, `or`, and `xor` share a single bit pattern across both lanes; `i64_shr` is an arithmetic (sign-extending) shift while `u64_shr` is logical; a shift count is taken modulo 64. `to_i64`/`to_u64` and `int_of_i64`/`int_of_u64` convert between `Int` and the fixed-width lanes.

### 5.6 Algebraic Data Types {#algebraic-data-types}

A `type` declaration introduces an algebraic data type: a _sum_ of constructors, each a _product_ of fields. A constructor is named with an upper-case identifier and applied like a function to build a value; a `match` ([patterns](#patterns)) destructures a value by constructor. A type may take type parameters and may be recursive, including mutually so.

```prism
{{#include ../examples/adt.pr}}
```

A `newtype` is a data type with exactly one single-field constructor: a type distinct from its payload, with no runtime wrapper. An `alias` on a type expression is a transparent synonym, interchangeable with its definition. A `deriving (C, ...)` clause generates the named instances structurally ([type classes](#type-classes)); `Eq`, `Ord`, `Show`, and `Lens` are derivable.

### 5.7 Records {#record-types}

A constructor may instead take _named_ fields, `C { f : T, ... }`, making the type a record. A field is read with `e.f`; records are built and updated by the [record expressions](#record-expressions). `deriving (Lens)` synthesizes a getter `f_of` and a setter `with_f` per field.

```prism
{{#include ../examples/record.pr}}
```

## 6. Type Classes {#type-classes}

A class declares a single-parameter constraint and a set of method signatures. An instance is a _named_ value providing those methods for one head type. A constrained function receives its dictionaries as hidden arguments resolved at each call site. The following program declares a second `Ord(Int)` instance named `ordDesc` that reverses the ordering, designates the prelude's ascending `ordInt` as canonical, and selects each explicitly.

```prism
{{#include ../examples/classes.pr}}
```

### 6.1 Coherence and Resolution {#coherence-and-resolution}

An instance is selected by the head constructor of the constraint type (the outermost constructor, for example `List` in `List(Int)`). Resolution is _coherent_: a program's meaning never silently depends on which instance the resolver happened to pick. For each `(class, type-head)` there is exactly one _canonical_ instance, and implicit resolution always selects it, so resolution is deterministic.

With a single instance for a head, that instance is canonical automatically. When two or more instances share a head, one must be designated canonical with a top-level declaration:

```text
canonical Class(Head) = instanceName
```

Two instances for one head with no designation is a coherence error reported at definition, not a silent ambiguity deferred to the use site. The designated instance is what implicit resolution selects; the others remain reachable only through an explicit override.

An explicit override is visible at the use site and changes nothing else's resolution: pass the chosen instance as a trailing `using` argument, `f(args, using instanceName)`, as `sort_by_ord(xs, using ordDesc)` does above. (This is the same `using` form reserved for first-class dictionary passing.) There is no ambient, scoped instance mechanism: an override is always written where it is used.

The preferred way to obtain a _different_ instance for a type is a `newtype` with its own canonical instance (`newtype Down = Down(Int)` for reverse order, a folded-case wrapper for case-insensitive comparison) rather than a non-canonical instance of the base type. This changes the type, not the instance-for-a-type, so coherence is preserved exactly and the difference is visible in the signature; an explicit `using` override is the second-line tool when a newtype is too heavy.

Resolution recurses through instance contexts up to a fixed depth.

### 6.2 Superclasses {#superclasses}

A class may require another as a superclass with `given`. Each instance then stores a resolved superclass dictionary as the leading field of its dictionary cell, and a `given Ord(a)` constraint discharges an `Eq(a)` obligation by projecting that field. The superclass witness is found automatically from the instances in scope.

```prism
{{#include ../examples/superclass.pr}}
```

### 6.3 Higher-Kinded Classes {#higher-kinded-classes}

A class parameter may be a type constructor of kind `* -> *`, applied as `f(a)` in method signatures and resolved on the head constructor of each instance. The prelude's `Functor`/`Applicative`/`Monad`/`Foldable`/`Traversable` tower is built this way. Its methods are _effect-polymorphic_ (defined under [effect polymorphism](#effect-polymorphism)): a per-element effect row threads through in place of an `Applicative` wrapper, so effectful traversal needs no monad and no do-notation.

```prism
{{#include ../examples/hkt.pr}}
```

Classes remain single-parameter; multi-parameter classes are not supported.

## 7. Effects and Handlers {#effects-and-handlers}

An `effect` declares a set of operations; each `ctl` operation has an argument list and a result type. Performing an operation is an ordinary call to its name. A function's effect _row_ is the set of effects whose operations it may perform and has not handled, written `! {L, ...}` on its result type, with an optional row variable tail `! {L | r}`. A bare `!` is an explicit empty row. A row is inferred when omitted.

```prism
{{#include ../examples/eff_state.pr}}
```

A `handle e with` block discharges operations; its grammar is the `handler` nonterminal of the [surface grammar](#surface-grammar). Each operation clause names an operation and binds its arguments and the resumption `k` (the captured continuation, explained below); calling `k(v)` resumes the suspended computation with `v`, and `k` may be called zero times (abort), once (the common case), or many times (multishot). A `return r` clause transforms the final value. The handler in `eff_state.pr` interprets `get`/`put` by threading a state parameter, so `counter`, which only performs the operations, never mentions a state value.

Operations and handlers are delimited control: the `handle` block is the _delimiter_ (a prompt), and the resumption `k` is the _delimited continuation_ it captures, the slice of computation between the perform site and the handler. Being first-class, `k` reinstalls that slice under the same handler when invoked. This is the typed, named generalization of `shift`/`reset`: a single prompt with one anonymous continuation becomes a row of named operations, each with its own clause, and the effect row is the static record of which delimiters a computation still requires.

A clause may invoke `k` any number of times; more than once makes the continuation _multishot_: each call re-runs the captured slice from the perform site with a different result, so one handler can pursue several futures of the same computation. This is how nondeterminism or search handlers explore alternatives (an `amb` operation whose clause calls `k` once per choice and combines the outcomes) and how generators yield and continue. Never invoking `k` discards the captured slice, which is exactly how `raise` ([observability](#observability)) and a `final ctl` clause abort.

### 7.1 Observability {#observability}

The defining property of the row discipline: an operation handled inside a function is discharged, so it does not appear in that function's inferred row. In the example below, `checked` carries the row `! {Exn}`, but `attempt`, which handles `raise`, is pure.

```prism
{{#include ../examples/eff_exn.pr}}
```

### 7.2 Clause Sugar {#clause-sugar}

Two clause forms abbreviate common shapes. `fun op(x) => e` is tail-resumptive sugar for `op(x, k) => k(e)`, resuming exactly once. `val v = e` is an install-time constant: `e` runs once when the handler installs, and every use of `v` returns it.

```prism
{{#include ../examples/handlers_funval.pr}}
```

A `final ctl op(x) => e` clause is non-resumable: it discards the continuation. This is the shape that `error`, `throw`, `try`, and `catch` desugar to ([errors and failure](#errors-and-failure)).

### 7.3 Masking {#masking}

`mask<E>(e)` makes every operation of effect `E` performed in `e` bypass the innermost enclosing handler of `E` and reach the next one out. Masks nest, so a double mask skips two handlers. The masked expression still demands an enclosing handler, so `E` remains in its row.

```prism
{{#include ../examples/mask.pr}}
```

### 7.4 Local Mutation {#local-mutation}

A `var` mutates, yet the function holding it stays pure. `fib_iter` below updates two locals in a loop but has type `(Int) -> Int` with an empty row, so it is accepted where only a pure function is allowed. Prism has no mutation primitive; `var` is sugar over the effect system.

A `var x := e` desugars to a private two-operation effect (a get and a set); each read of `x` becomes a perform of get, each `x := v` a perform of set. In the same pass, a handler that threads the value as a hidden parameter is wrapped around the block. That handler discharges the get and set labels ([observability](#observability)), so they never reach the function's type: the state is implemented but not observable. Because an escape analysis (below) has proved the state never leaves its block, effect lowering then erases the whole handler to a mutable cell, turning each get into a cell read and each set into a cell write, and the loop into a constant-stack loop, so the lowered code allocates nothing per iteration.

{{#tabs }}

{{#tab name="Source" }}

```prism
{{#include ../examples/var_fib.pr}}
```

{{#endtab }}

{{#tab name="Desugared" }}

```text
{{#include ../examples/var_desugared.txt}}
```

{{#endtab }}

{{#tab name="Core" }}

```text
{{#include ../examples/var_core.txt}}
```

{{#endtab }}

{{#endtabs }}

An escape analysis keeps the purity honest: the compiler rejects any closure or returned value that would carry the var out of its block, so the state cannot outlive its handler.

### 7.5 Errors and Failure {#errors-and-failure}

Prism has no built-in exception type. Errors and failure are two related mechanisms, both resting on the non-resumable `final ctl` clause of the [clause sugar](#clause-sugar). With the imperative `break`, `continue`, and `return` of [imperative control flow](#imperative-control-flow), they are one mechanism wearing several faces: each is a single-operation effect whose handler never resumes the captured continuation, installed only where the corresponding keyword actually occurs, so non-local control costs nothing where it is not used and (being handled at its boundary) surfaces in no effect row where it is.

**Extensible errors.** An `error N(t)` declaration introduces a one-operation effect whose operation never resumes; `throw N(x)` performs it. A function's error row is exactly the set of errors it may raise and has not caught, and distinct `error` declarations union structurally as functions compose, with no umbrella sum type and no conversion glue: `find_port` carrying `{NotFound}` and `parse_port` carrying `{Malformed}` compose to `{NotFound, Malformed}`. `try e catch { ... }` is subtractive handler sugar (one nested `final ctl` per arm): a partial catch discharges the labels it names and lets the rest flow to an enclosing handler, and an uncaught error is an unhandled-effect error naming exactly the labels that remain. Each catch arm names an error and binds its fields to variables.

```prism
{{#include ../examples/errors.pr}}
```

These idioms span the recovery spectrum: the built-in `Exn` effect, raised by `error(code)` and uncatchable (it aborts); `Result` with the postfix `e?` propagation of the [expression forms](#expressions); a plain `match` on `Ok`/`Err`; and a custom non-resumable effect.

```prism
{{#include ../examples/exceptions.pr}}
```

**The failure axis.** Beyond named errors, Prism has an anonymous, recoverable `fail()`, the deterministic-functional-logic failure of the Verse calculus ([Augustsson et al., 2023](bibliography.md#augustsson-verse-2023)). `guard(b)` fails when `b` is false; `a ?? b` runs `a` under a failure handler and falls back to `b`; `e?.field` chains through options, failing on `None`; `optional`/`succeeds`/`default` reify a failing computation as an `Option`, a `Bool`, or a default; and a comprehension guard may itself fail, pruning the element ([expressions](#expressions)). `transact body else fallback` snapshots every live `var`, runs the body under a failure handler, and restores the snapshots on failure, so an aborted attempt leaves observable state unchanged. The whole axis is `final ctl` handlers over a `Fail` effect, so an unhandled `fail()` is the ordinary unhandled-effect error, and "failable only in a failure context" falls out of the row discipline for free.

```prism
{{#include ../examples/transact.pr}}
```

### 7.6 Effect Polymorphism {#effect-polymorphism}

A function can be generic over the effects of a thunk it is given by quantifying over a row variable in the argument's type. Below, `twice` accepts any `(Unit) -> Int` thunk and adds an open row `{| e}` for whatever that thunk performs; each call unifies `e` with the actual row (empty, `{Tick}`, or `{Say}`), and a handler discharges only the label it names, leaving the rest in `e`. This is the mechanism the prelude's `fmap` and `traverse` use to thread a per-element effect ([higher-kinded classes](#higher-kinded-classes)), so an effectful traversal needs no `Applicative` wrapper.

```prism
{{#include ../examples/eff_poly.pr}}
```

### 7.7 Capability Effects and IO {#capability-effects-and-io}

Reading the outside world is itself effectful, and the row records which part of the world a function reads. The nondeterministic input operations are the four _capability_ effects `Console` (`read_int`, `read_line`), `FileSystem` (`read_file`, `file_exists`), `Random` (`rand`), and `Env` (`getenv`, `args_count`, `arg`). A function that reads input names exactly that capability in its row: a function calling `read_int` carries `! {Console}`, not a blanket `! {IO}`, so the row says which part of the world is read rather than merely that some IO happens. (`Console`, `FileSystem`, `Random`, and `Env` are therefore reserved effect names, among the [keywords](#keywords). A `Clock` capability is reserved in spirit but not yet introduced, pending a time primitive.)

The surface is unchanged: `read_int()`, `read_file(p)`, `getenv(s)`, and friends stay ordinary calls, defined in the prelude as thin wrappers that perform the corresponding capability operation. A default `run_io` world handler is wrapped around `main` on demand, only when `main` reaches a capability, and discharges each operation by performing the real input and resuming with the result, so the capabilities collapse to `! {IO}` at the program boundary. The handler is tail-resumptive, so it fuses to a direct call at no cost ([effect lowering](./compiler.md#effect-lowering)). Output stays an opaque `IO` effect: `print`, `write_file`, `append_file`, and `remove_file` carry `! {IO}` and are not capability operations, because [record and replay](#record-and-replay) needs only inputs pinned.

Because input is now an interceptable operation rather than an untracked builtin, a handler other than `run_io` can supply the values, which is what record/replay rests on.

### 7.8 Record and Replay {#record-and-replay}

A program that reads stdin, files, randomness, or the environment takes a different path each time the world answers differently, which is what makes such a run hard to reproduce. Record and replay captures one run as a trace and re-runs it deterministically: an interactive session becomes a fixed regression test, a failing run becomes a reproducible bug report that needs none of the original environment, and a program can be re-executed offline against the captured trace rather than the live world. Persisting that trace to a log as it is produced turns replay into durable execution: the module's `durable` handler reloads the logged prefix on restart and continues live once it is exhausted, so a crashed run resumes where it stopped rather than starting over. The direction this points at is a suspended computation that is itself a value, one that can be persisted and resumed later or after a crash, the durable-execution semantics other systems provide as a separate service.

The `Replay` stdlib module (`import Replay`) turns a program's interaction with the world into a recordable, replayable trace over the [capability effects](#capability-effects-and-io). `record(action)` runs `action` against the real world, logging every `Console`/`FileSystem`/`Random`/`Env` observation into an opaque `Trace` and returning `(result, trace)`. `replay(trace, action)` re-runs the same action performing no real input, discharging each operation from the recorded trace instead; a wrong-variant or exhausted trace is a `fail()` ([errors and failure](#errors-and-failure)). Replaying a recorded trace reproduces the original result, because the effect-erased core is deterministic and the trace pins every input.

A `replayable` function annotation, in the family of `fip`/`fbip` but orthogonal to them (`replayable fn` and `replayable fip fn` are both valid), certifies that a function is reproducible from a recorded trace. It is accepted only when the inferred effect row stays within `{Console, FileSystem, Random, Env, Exn, Fail}`, the recordable capabilities plus the deterministic builtin effects. A row containing `IO` (un-logged nondeterminism: output, the system clock, `srand`) or any user-defined effect is rejected with a caret diagnostic naming the offending effects. The check is a row-subset test on the already-inferred row, so it costs nothing beyond inference.

The two pieces fit together in a few lines: `roll` is `replayable` because it reads only `Random`, and recording one run then replaying its trace reproduces the result without drawing real randomness the second time.

```prism
{{#include ../examples/replay_intro.pr}}
```

`durable(path, action)` persists the trace as each observation is made, so a run that stops partway resumes on re-run: the logged prefix replays performing no real input, then the run continues live once the log is exhausted. Re-running this workflow reaches the same result rather than redrawing its inputs.

```prism
{{#include ../examples/durable_intro.pr}}
```

### 7.9 Streams {#streams}

Streams are the prelude's data-processing combinators, built on a single `Emit(a)` effect rather than on intermediate collections. A _producer_ performs `Emit` once per element (`srange`, `sof`); a _transformer_ handles a producer's emissions and re-emits the survivors (`smap`, `skeep`, `stake`); and a _consumer_ handles `Emit` by folding every emission into a result (`sfold`, `ssum`, `scollect`). A pipeline is the consumer wrapped around the transformers wrapped around the producer, one handler stack over one producer loop.

Because emission is an effect the consumer discharges, a pipeline _fuses_: `srange(1, 1000).smap(square).skeep(even).stake(5).ssum()` runs as one loop that allocates neither an intermediate list nor a cell per element, the state-threading path of [effect lowering](./compiler.md#effect-lowering). A transformer that stops early, like `stake`, drops the producer's continuation, so the source halts at once. Comprehensions and the statement `for` desugar to these combinators ([comprehensions](#comprehensions)) and fuse the same way.

```prism
{{#include ../examples/streams.pr}}
```

## 8. Expressions {#expressions}

The expression grammar is in the [surface grammar](#surface-grammar) and the effect and failure forms are in [effects and handlers](#effects-and-handlers); the forms below are those the grammar alone does not settle.

A method call `e.m(args)` is uniform-function-call sugar for `m(e, args)`. A trailing block argument, `e.m(args) fn (x) { body }`, appends a lambda as the last argument; this is how the stream consumers in [streams.pr](./compiler.md#effect-lowering) chain. Field access is `e.field`.

### 8.1 Comprehensions {#comprehensions}

A comprehension `[ e for x in s, q, ... ]` collects `e` for each element; a qualifier `q` is a guard `if g` or a binder `let y = e`. A guard is evaluated in a failure context, so an element is pruned both when `g` is false and when computing `g` fails: a failable accessor such as `at_list` (a prelude lookup from [the standard prelude](#the-standard-prelude)) past the end of a list prunes that element rather than aborting. The statement form `for x in s, q, ... do body` runs `body` per survivor. Both desugar to the prelude's stream combinators (the `Emit` effect of [the standard prelude](#the-standard-prelude)), so they fuse without building an intermediate list.

```prism
{{#include ../examples/comprehension.pr}}
```

### 8.2 Records {#record-expressions}

Record construction `C { f = e, ... }`, functional update `C { ..base, f = e }`, and nested path update `{ base | a.b = e, ... }` build and modify the [record types](#record-types); each is an in-place write on a uniquely owned value. The `deriving (Lens)` getters and setters compose with them for deeper access. A path generalizes past nested fields to traversals, indices, prisms, filters, and a read form ([optic paths](#optic-paths)).

```prism
{{#include ../examples/lens_derive.pr}}
```

### 8.3 Imperative control flow {#imperative-control-flow}

Loops and early exit are surface sugar over tail recursion and effects, so they cost nothing beyond what an explicit recursion would. `while cond do body` and `loop body` (an unconditional loop) lower to a tail-recursive driver applied to the condition and body as thunks; because a `var` is a State effect ([the standard prelude](#the-standard-prelude)) the body mutates freely and the loop runs in constant stack with no per-iteration allocation. `break` and `continue` (valid inside `while`, `loop`, and `for`) and statement-form `return e` (which exits the enclosing function) compile to non-resumable performs of internal, fully-handled control effects, installed only for the keyword a body actually uses; a nested loop captures its own `break`/`continue`. Because each control effect is discharged at its loop or function boundary, none appears in the surfaced effect row: a loop is as pure as its body, and a function using `return` infers the same row as the equivalent recursion. Compound assignment `x += e` (and `-=`, `*=`, `%=`) on a `var` is shorthand for `x := x <op> e`.

Each form desugars to an existing construct:

| Surface                         | Desugaring                                                                           |
| ------------------------------- | ------------------------------------------------------------------------------------ |
| `x += e` (and `-=`, `*=`, `%=`) | `x := x <op> e`                                                                      |
| `while cond do body`            | `repeat_while(\() -> cond, \() -> body)`                                             |
| `loop body` (reachable `break`) | `repeat_while(\() -> true, \() -> body)`                                             |
| `loop body` (no `break`)        | `forever(\() -> body)`, whose result is a bottom type                                |
| `break` / `continue`            | a `final ctl` perform of an internal `Break`/`Continue` effect handled at the loop   |
| `return e`                      | a `final ctl` perform of an internal `Return(a)` effect handled at the function body |

```prism
{{#include ../examples/imperative.pr}}
```

### 8.4 Exponentiation {#exponentiation}

`a ^ b` raises `a` to the power `b`. It binds tighter than `*` and is right-associative, so `2 ^ 3 ^ 2` is `2 ^ (3 ^ 2)`. It is the method of the `Pow` class ([the standard prelude](#the-standard-prelude)) with `Int` and `Float` instances, so it desugars to `pow(a, b)`: over `Int` it is bignum-correct (the instance multiplies), over `Float` it is a `pow_float` call. A mixed `Int ^ Float` is a type error, resolved by an explicit `to_float`, exactly as `2 + 3.0` is (Prism never coerces between `Int` and `Float` implicitly).

### 8.5 Indexing {#indexing}

`a[i]` reads, `a[i] := v` writes, and `a[i] += e` updates an indexed container. The form is dispatched on the receiver's type (not a class, so no inference change): `Array` is indexed by `Int`, `HashMap` by `String`, `String` by `Int` (yielding the byte), and `List` by `Int`. `Array`, `HashMap`, and `List` are writable; `String` is read-only. `Array` and `HashMap` rewrite the cell in place (FBIP); a `List` write is the functional `list_set`, rebuilding the spine.

A read is _failable_: a missing index or key performs the `Fail` effect ([errors and failure](#errors-and-failure)), so `a[i]` has type `Elem ! {Fail}` and the partiality surfaces in the row rather than in an `Option` wrapper. It therefore composes with `??`, `?.`, `default`, and the rest of the failure axis: `a[i] ?? d` supplies a default, and the counter idiom is `m[k] := (m[k] ?? 0) + 1`, honest that an absent key starts at zero. A plain write `a[i] := v` is total; `a[i] += e` reads first, so it is `! {Fail}`. Writes rebind the underlying `var` and rewrite the cell in place when it is uniquely owned (FBIP, [declarations and programs](#declarations-and-programs)); nested `grid[i][j] := v` composes the same way. `a[i] := v` requires `a` to be an assignable `var`.

### 8.6 Optic Paths {#optic-paths}

Prism has no optic library: no `Lens` type, no `over`/`set`/`toListOf` to compose, no profunctor encodings. It has one rule instead. Between the `|` and the operator of a record update ([record expressions](#record-expressions)), or inside `s.[ ... ]`, a **path** is a sequence of steps read left to right. The path _is_ the optic, spelled at the use site rather than reified as a value. Every form is sugar over `map`/`with`/`match`, so in-place reuse and fusion come for free and nothing new reaches the core: this is the language's "effects instead of monads" stance applied to optics, paths instead of optic combinators.

A step is one of:

| Step              | Meaning                                                |
| ----------------- | ------------------------------------------------------ |
| `.field`          | descend into a record field                            |
| `each`            | traverse every element of a functor (lowers to `fmap`) |
| `[i]`             | focus one element of a list or array, by index         |
| `?Ctor`           | focus through a sum constructor; others pass through   |
| `(steps where p)` | keep only the foci satisfying the predicate `p`        |

End a path with `= v` to **set** the focus or `~ f` to **modify** it (apply `f`); wrap a path in `s.[ path ]` to **read** every focus it selects into a list. `each` is a reserved keyword; the other steps reuse existing tokens.

Each form lowers to ordinary code, shown here over `type Player = Player { name: String, pos: Vec2, hp: Int, bag: List(Int) }` and `type Shape = Circle { radius: Int } | Square { side: Int }`. A field sets through the derived setter, `{ p | hp = 100 }` to `with_hp(p, 100)`, and nests, `{ pl | pos.x = 30 }` to `with_pos(pl, with_x(pl.pos, 30))`. Modify reads the focus, `{ p | hp ~ heal }` to `with_hp(p, heal(p.hp))`. `each` fans out over any functor, `{ players | each.hp ~ heal }` to `fmap(\p -> with_hp(p, heal(p.hp)), players)`, and composes with descent, `{ world | party.each.pos.x = 0 }`. An index focuses one element, `{ world | party[0].hp = 100 }`, lowering through `list_set` (or in-place `array_set`); an out-of-range index leaves the container unchanged. A prism rebuilds a matched constructor and passes the others through, the prism law for update:

```text
{ shape | ?Circle.radius ~ double }
  =>  match shape of
        Circle { radius = r } => Circle { radius = double(r) }
        other                 => other
```

A filter guards a traversal, `{ world | party.(each where alive).hp ~ heal }` applying the rest only to the foci `alive` keeps and passing the rest through. The whole vocabulary composes in one path:

```text
{ world | party.(each where alive).bag.each.count ~ \(n) -> n + 5 }
  =>  with_party(world,
        fmap(\p -> if alive(p)
                   then with_bag(p, fmap(\it -> with_count(it, it.count + 5), p.bag))
                   else p,
             world.party))
```

The read form `s.[ path ]` collects every focus a path selects into a list, the read twin of the update: `players.[each.hp]` is the list of each `hp`, `each` flat-maps so `world.[party.each.bag.each.count]` flattens, `?Ctor` previews zero or one focus, and a single-focus path yields a one-element list.

Paths are deliberately use-site syntax, not first-class values: there is no `Optic` type, no passing an optic to a function, no library of named composable optics, and optic _kinds_ are not tracked in the type system (that a read-only path is read-only is a structural fact of the desugaring, not a typed law). This is the explicit trade: paths cover the great majority of real optic _use_ and give up abstracting over _which_ optic. The mental model is one breath: steps read left to right, `= v`/`~ f` to write, `s.[ ... ]` to read, nothing escaping into a new core construct.

```prism
{{#include ../examples/optics_tour.pr}}
```

## 9. Patterns {#patterns}

Patterns appear in `match` arms, `let` bindings, lambda and function parameters, and `catch` arms; their grammar is the `pattern` nonterminal of the [surface grammar](#surface-grammar). A constructor pattern destructures a value of the algebraic data type that built it ([algebraic data types](#algebraic-data-types)), binding its fields; literal, tuple, wildcard, and record patterns match the remaining forms.

A `match` arm may carry a guard, `pat if cond => body`; when the guard is false, control falls through to the next arm. Matches are checked for exhaustiveness and redundancy by the usefulness algorithm of [Maranget (2007)](bibliography.md#maranget-2007): an unreachable arm is an error, and a non-exhaustive match is an error naming a missing pattern. A guarded arm does not count toward exhaustiveness, since its guard may fail at run time.

```prism
{{#include ../examples/guards.pr}}
```

A `pattern N(x) for T = view ... make ...` declaration defines a bidirectional pattern synonym: in match position it runs `view` and succeeds when that returns `Some` (the present case of `Option`, from [the standard prelude](#the-standard-prelude)); in expression position it runs `make`. Here `view` and `make` are contextual keywords, significant only inside a `pattern` declaration. A synonym with both halves is a _prism_ (a composable view-and-build pair); one with only `view` is a view pattern.

```prism
{{#include ../examples/pattern_syn_sugar.pr}}
```

## 10. Declarations and Programs {#declarations-and-programs}

A function is declared with `fn`; a parameter may carry a type annotation, a default value `:= e`, or the `borrow` modifier, which lets a pure function read a parameter without taking ownership of it. A return annotation is written `: !{R} T` for result type `T` and effect row `R`, `: ! T` for an explicit empty row, or `: T` to leave the row inferred. A parameter with a default may be omitted, and any argument may be passed by name as `f(p = e)`; the call is rewritten to positional form, filling omitted defaults. Defaults and named arguments are honored on top-level functions. A top-level `let` is a constant: its references are inlined. A `where` block attaches non-recursive, lexically scoped definitions to a function body.

A function may be annotated `fip` or `fbip` to assert the fully-in-place discipline of [Lorenzen et al. (2023)](bibliography.md#lorenzen-fp2-2023). `fbip` proves the body allocates no fresh cell and calls only annotated, allocation-free functions. `fip` additionally proves linearity (each owned, non-immediate binding is consumed at most once) and bounded stack (each recursive call in the group is a tail call or a single tail-modulo-cons or tail-modulo-add). These are static checks that reject a non-conforming body; the mechanism is described under [reference counting and FBIP reuse](./compiler.md#reference-counting-and-fbip-reuse). A function may additionally, or independently, be annotated `replayable` ([record and replay](#record-and-replay)), which certifies it performs only the recordable capability effects and so is reproducible from a recorded trace; `replayable` is orthogonal to `fip`/`fbip` and may combine with either.

```prism
{{#include ../examples/fip_list.pr}}
```

## 11. Modules {#modules}

A file is a module and a directory is a namespace prefix: `import Data.Map` loads `Data/Map.pr`. A project is a `prism.toml` manifest plus a source tree, resolved from the project root. A single-file program is one module.

`import M` brings `M`'s exports into scope under qualified names; `import M (a, b)` also brings `a` and `b` into bare scope; `import M as N` adds the alias `N`. The `pub` modifier on a declaration makes it visible to importers; `pub import M (x)` re-exports `x` through the importing module. An `opaque type` exports its name but not its constructors.

Name resolution rewrites every top-level definition to a canonical, module-qualified symbol (an export as `Data.Map.insert`, a private as the unforgeable, source-unwritable `Data.Map@helper`) and merges all modules into one program keyed by those symbols. Because identity is the canonical symbol, two modules may export the same short name and coexist. This is namespacing, not separate compilation: there are no per-module artifacts, and changing one module recompiles the whole program.

Instances are global, but each records its defining module. An _orphan_ instance (defined apart from both its class and its head type) and instances that overlap across modules are reported as warnings; an ambiguity names each candidate's module.

## 12. The Standard Prelude {#the-standard-prelude}

The prelude in `lib/prelude.pr` is in scope in every module. It is ordinary Prism, not built-in. Its contents, by category:

- **Data types.** `Option(a)`, `Result(a, e)`, `List(a)`, the balanced-tree `Map(k, v)`, and the hash table `HashMap(v)`. A set is a `Map(k, Unit)`, with a `set_*` API rather than a distinct type.
- **List combinators.** `map`, `filter`, `foldl`, `foldr`, `length`, `append`, `reverse`, `zip`/`unzip`, `take`/`drop`, `sort`, `range`, and the rest of the usual vocabulary.
- **Option and Result combinators.** `map_option`, `and_then`, `unwrap_or`, `map_result`, `and_then_result`, `result_or`, and conversions between the two.
- **The class tower.** `Eq`, `Ord` (with `Eq` as superclass), `Show`, `Pow` (exponentiation `^`, with `Int` and `Float` instances), and the higher-kinded `Functor`, `Applicative`, `Monad`, `Foldable`, `Traversable`, with instances for `List` and `Option`.
- **Strings and characters.** Classifiers (`is_digit`, `is_alpha`, ...), case mapping, `starts_with`/`ends_with`/`contains`/`index_of`, `split`, `trim`, `chars`, and single-allocation joining.
- **Arrays and maps.** The growable `Array(a)` API (`array_new`, `array_get`, `array_set`, `array_push`, with in-place update on unique ownership), the AVL `Map` and `set_*` API, and the `HashMap` API over string keys.
- **Streams.** The `Emit(a)` effect and the producer/transformer/consumer combinators `srange`, `sof`, `smap`, `skeep`, `stake`, `sfold`, `ssum`, `scollect`, which fuse without intermediate collections.
- **Numerics and failure.** Fixed-width `i64_*`/`u64_*` operations, common math, and the failure helpers `guard`, `optional`, `succeeds`, `default`.
- **World and IO.** The capability effects `Console`, `FileSystem`, `Random`, and `Env` ([capability effects and IO](#capability-effects-and-io)), their input wrappers (`read_int`, `read_line`, `read_file`, `file_exists`, `rand`, `getenv`, `args_count`, `arg`), the default `run_io` world handler, and the output builtins (`print`, `write_file`, `append_file`, `remove_file`). The separate `Replay` module (`import Replay`, [record and replay](#record-and-replay)) adds `record`, `replay`, and the durable-execution handler `durable` over those capabilities.
