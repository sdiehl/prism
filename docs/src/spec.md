# The Prism Language Specification

Prism is a strict, impure functional language in the ML family whose type system tracks side effects. This document defines the surface language: its lexical structure, grammar, type system, and evaluation. It describes the language as the `prism` compiler accepts it. Where the implementation is incomplete or carries known debt, the limitation is stated as such, not hidden.

## 1. Introduction

A Prism program is a set of modules, each a file of declarations. The surface language elaborates to a strict, call-by-push-value core ([Levy, 2004](bibliography.md#levy-2004)) in A-normal form (the companion [Compiler](./compiler.md) document), compiles to native code through LLVM, and is managed by deterministic reference counting rather than a garbage collector.

Two things distinguish Prism from its ML and Haskell ancestors. Side effects are inferred, extensible _effect rows_ (Section [7](#7-effects-and-handlers)) that combine structurally across calls instead of through monads, and they track observability: an operation handled inside a function does not appear in its type, so internally effectful code is reused as pure. The same reference-count discipline both frees memory and performs fully-in-place (FBIP) update (Section [10](#10-declarations-and-programs)), compiling record updates and derived setters to in-place writes on uniquely owned values (those that a reference count proves have no other live reference; see [Compiler](./compiler.md#10-reference-counting-and-fbip-reuse)).

This specification proceeds in dependency order: notation, lexical structure, grammar, types, then the constructs the grammar describes.

## 2. Notation

Grammar is given in the following EBNF. A _terminal_ is a literal token written in double quotes; a _nonterminal_ is a lower-case name. The character classes are the ASCII letters (`letter`), the two cases (`lower`, `upper`), the decimal digits (`digit`), any printable character (`graphic`), and any character other than `"`, `\`, or a newline (`strchar`). These are primitives, not grammar nonterminals.

```text
{{#include ../examples/notation.ebnf}}
```

Identifiers in productions name the tokens defined in [3](#3-lexical-structure) (`varid`, `conid`, `qualid`, `integer`, `float`, `char`, `string`) and the character classes defined just above. Layout (Section [3.6](#36-layout)) inserts block delimiters that the grammar then treats as ordinary terminals.

## 3. Lexical Structure

Source text is UTF-8. Tokens are lexed by longest match, then the stream is rewritten by the layout algorithm of Section [3.6](#36-layout). Whitespace and comments separate tokens and are otherwise insignificant except as layout boundaries.

```text
{{#include ../examples/lexical.ebnf}}
```

### 3.1 Identifiers

Prism distinguishes identifiers by initial case. A `varid` begins with a lower-case letter or underscore and names a variable, function, parameter, or record field. A `conid` begins with an upper-case letter and names a type, data constructor, type class, or effect. A `qualid` is a dotted path such as `Data.Map` or `Map.insert`; it is lexed as a single token so that a module path never collides with field access.

### 3.2 Keywords

The following are reserved and may not be used as identifiers.

|            |         |            |           |            |
| ---------- | ------- | ---------- | --------- | ---------- |
| `fn`       | `fip`   | `fbip`     | `pub`     | `import`   |
| `as`       | `type`  | `newtype`  | `opaque`  | `alias`    |
| `effect`   | `error` | `throw`    | `try`     | `catch`    |
| `transact` | `class` | `instance` | `pattern` | `deriving` |
| `where`    | `given` | `handle`   | `with`    | `handler`  |
| `mask`     | `ctl`   | `final`    | `fun`     | `val`      |
| `return`   | `let`   | `var`      | `borrow`  | `in`       |
| `for`      | `do`    | `if`       | `then`    | `else`     |
| `elif`     | `match` | `of`       | `forall`  | `true`     |
| `false`    |         |            |           |            |

The built-in type names `Int`, `I64`, `U64`, `Bool`, `Unit`, `Float`, `Char`, and `String` are also reserved.

### 3.3 Operators and Punctuation

The operator set is fixed; the language has no user-defined operators. Every comparison operator, and every arithmetic operator except `%`, also has a floating-point form suffixed with a dot.

| Class      | Operators                                                               |
| ---------- | ----------------------------------------------------------------------- |
| Arithmetic | `+` `-` `*` `/` `%` and float `+.` `-.` `*.` `/.`                       |
| Comparison | `==` `/=` `<` `<=` `>` `>=` and float `==.` `/=.` `<.` `<=.` `>.` `>=.` |
| Logical    | `&&` `\|\|`                                                             |
| Pipeline   | `\|>` `>>` `<<`                                                         |
| Failure    | `??` `?.` `?`                                                           |
| Arrows     | `->` `<-` `=>`                                                          |
| Binding    | `=` `:=` `:`                                                            |
| Effect     | `!`                                                                     |
| Brackets   | `(` `)` `{` `}` `[` `]`                                                 |
| Other      | `,` `.` `..` `\|` `\`                                                   |

### 3.4 Literals

An `integer` is a sequence of decimal digits. A value that fits in a machine word is an immediate; a larger literal is an arbitrary-precision integer (bignum). The suffix `i64` or `u64` selects a fixed-width 64-bit lane that wraps on overflow. A `float` is an IEEE-754 double. A `char` is a single Unicode scalar in single quotes. A `string` is double-quoted UTF-8.

The escape sequences `\n`, `\t`, `\r`, `\\`, `\"`, `\{`, and `\}` are recognized in both character and string literals; a character literal additionally accepts `\'`.

### 3.5 String Interpolation

Within a string, an unescaped `{ expr }` is an interpolation hole. The hole text is re-lexed at its source position and elaborated as an expression whose `Show` value is spliced into the string. A hole runs to its matching `}`, balancing nested braces and string literals, so a hole may itself contain a string with braces. A literal brace outside a hole is written `\{` or `\}`. An empty hole, an unterminated hole, and an unterminated string are each lexical errors. The catch arms of the error example in Section [7.5](#75-errors-and-failure) use interpolation, as in `"no such key: {k}"`.

### 3.6 Layout

Prism uses the offside rule: indentation, not explicit braces, delimits a block. A layout block opens after any of the keywords or symbols `=`, `then`, `else`, `=>`, `of`, `with`, `handler`, `do`, `where`, `try`, `catch`, `transact`, and after `fn`. The first token after such an opener sets the block's indentation column; a later line at that column starts a new item in the block, and a line indented less closes the block. Explicit `{` `}` override layout and may always be used in place of an implicit block, as in the brace-delimited handler arms of the masking example (Section [7.3](#73-masking)).

## 4. Surface Grammar

A program is a layout-delimited sequence of top-level declarations.

```text
{{#include ../examples/grammar-program.ebnf}}
```

```text
{{#include ../examples/grammar-decls.ebnf}}
```

Type syntax. A function type carries an optional effect _row_ on its codomain (Section [7](#7-effects-and-handlers)); the row binds to a function type only.

```text
{{#include ../examples/grammar-types.ebnf}}
```

Expressions, patterns, and the handler block of `handle`/`try` (used in Section [7](#7-effects-and-handlers)).

```text
{{#include ../examples/grammar-expr.ebnf}}
```

```text
{{#include ../examples/grammar-pattern.ebnf}}
```

```text
{{#include ../examples/grammar-handler.ebnf}}
```

### 4.1 Operator Precedence

The table gives the binding of each operator, loosest to tightest. Levels 1 to 8 are the `binop` operators of the grammar; level 9 is application, field access, and the postfix failure operators, which bind tighter than every `binop`.

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
| 9     | `f(...)` `f[...]` `.field` `?.field` `?`      | left          |

## 5. Types and Kinds

Prism infers types by the bidirectional, higher-rank inference algorithm of [Dunfield & Krishnaswami (2013)](bibliography.md#dunfield-krishnaswami-2013). An unannotated declaration infers its principal type; an annotated one is checked against the annotation. Annotations are required for rank-N polymorphism, since a nested `forall` cannot be inferred.

### 5.1 Types

The scalar types are `Int` (arbitrary precision), `I64`, `U64`, `Float`, `Bool`, `Char`, `String`, and `Unit`. A type constructor applied to arguments is written `Con(t, ...)`; the list type has the sugar `[t]` for `List(t)`. A tuple type is `(t, ...)`. A function type is `(t, ...) -> u`, optionally carrying an effect row on `u`. A universally quantified type is `forall a. t`. Type variables are `varid`s.

### 5.2 Kinds

A type has kind `*` (a type of values) or `* -> *` (a type constructor awaiting one argument), and so on; `List` has kind `* -> *`, since `List(Int)` is a type only once `Int` is supplied. A class parameter may range over a constructor of kind `* -> *`, applied as `f(a)` in method signatures; see Section [6](#6-type-classes). There is no explicit kind-checking phase: well-kindedness is enforced during unification, which requires a constructor and its arguments to agree in arity.

### 5.3 Inference, Generalization, and Defaulting

A row is built from _labels_, the effect names of Section [7](#7-effects-and-handlers) (a parametric effect's label carries type arguments). It is _closed_ when it ends in a fixed set of labels and _open_ when it ends in a row variable (`! {L | r}`), which stands for further labels the caller may add. An unannotated binding is generalized over its free type and row variables not fixed by the surrounding scope. Two cases default rather than generalize. An otherwise-unconstrained numeric operand defaults to `Int`. An open row left unconstrained at a monomorphic declaration (one with no remaining free row variable) defaults to empty (pure); an effect-polymorphic declaration keeps its row variable, as `traverse` does in the prelude (Section [12](#12-the-standard-prelude)).

### 5.4 Subsumption and Row Equivalence

Checking a value against an expected type uses subsumption, not equality. A more polymorphic type is accepted where a less polymorphic one is expected: a `forall` on the expected side introduces a rigid variable the value must satisfy for all instances, and a `forall` on the value side is instantiated to meet the expectation. Function subtyping is contravariant in the arguments and covariant in the result, so a function accepting more and returning less may stand in for one accepting less and returning more.

Effect rows are compared up to reordering: `! {A, B}` and `! {B, A}` are the same row, because unification hoists a demanded label to the head of the other row before matching the tails. An open row `! {A | r}` unifies with any row that provides `A` by binding `r` to the remainder; for instance `! {A | r}` unifies with `! {A, B}` by binding `r` to `{B}`. This is how a caller's row absorbs a callee's. A unification that would make a row contain itself is rejected, so recursive effect rows do not arise.

### 5.5 Fixed-Width Integers

`Int` is arbitrary precision. `I64` and `U64` are the signed two's-complement and unsigned 64-bit lanes; they wrap on overflow rather than promoting to a bignum. Their operations are named builtins, not operators, since the surface `+`, `-`, and so on target `Int` and `Float`. Each takes two operands of the lane type.

| Family     | Operations (and the `u64_*` counterparts)                   |
| ---------- | ----------------------------------------------------------- |
| Arithmetic | `i64_add` `i64_sub` `i64_mul` `i64_div` `i64_rem` `i64_cmp` |
| Bitwise    | `i64_and` `i64_or` `i64_xor`                                |
| Shift      | `i64_shl` `i64_shr`                                         |

`and`, `or`, and `xor` share a single bit pattern across both lanes; `i64_shr` is an arithmetic (sign-extending) shift while `u64_shr` is logical; a shift count is taken modulo 64. `to_i64`/`to_u64` and `int_of_i64`/`int_of_u64` convert between `Int` and the fixed-width lanes.

### 5.6 Algebraic Data Types

A `type` declaration introduces an algebraic data type: a _sum_ of constructors, each a _product_ of fields. A constructor is named with an upper-case identifier and applied like a function to build a value; a `match` (Section [9](#9-patterns)) destructures a value by constructor. A type may take type parameters and may be recursive, including mutually so.

```prism
{{#include ../examples/adt.pr}}
```

A `newtype` is a data type with exactly one single-field constructor: a type distinct from its payload, with no runtime wrapper. An `alias` on a type expression is a transparent synonym, interchangeable with its definition. A `deriving (C, ...)` clause generates the named instances structurally (Section [6](#6-type-classes)); `Eq`, `Ord`, `Show`, and `Lens` are derivable.

### 5.7 Records

A constructor may instead take _named_ fields, `C { f : T, ... }`, making the type a record. A field is read with `e.f`; records are built and updated by the expressions of Section [8.2](#82-records). `deriving (Lens)` synthesizes a getter `f_of` and a setter `with_f` per field.

```prism
{{#include ../examples/record.pr}}
```

## 6. Type Classes

A class declares a single-parameter constraint and a set of method signatures. An instance is a _named_ value providing those methods for one head type. A constrained function receives its dictionaries as hidden arguments resolved at each call site. The following program declares an `Ord(Int)` instance named `ordDesc` that reverses the ordering and uses it explicitly.

```prism
{{#include ../examples/classes.pr}}
```

### 6.1 Resolution and Ambiguity

An instance is selected by the head constructor of the constraint type (the outermost constructor, for example `List` in `List(Int)`). When two instances match one head, resolution is ambiguous and the program must pick one explicitly with the postfix form `f[instanceName]`, as `sort_by_ord[ordDesc]` does above. Resolution recurses through instance contexts up to a fixed depth.

### 6.2 Superclasses

A class may require another as a superclass with `given`. Each instance then stores a resolved superclass dictionary as the leading field of its dictionary cell, and a `given Ord(a)` constraint discharges an `Eq(a)` obligation by projecting that field. The superclass witness is found automatically from the instances in scope.

```prism
{{#include ../examples/superclass.pr}}
```

### 6.3 Higher-Kinded Classes

A class parameter may be a type constructor of kind `* -> *`, applied as `f(a)` in method signatures and resolved on the head constructor of each instance. The prelude's `Functor`/`Applicative`/`Monad`/`Foldable`/`Traversable` tower is built this way. Its methods are _effect-polymorphic_ (defined in Section [7.6](#76-effect-polymorphism)): a per-element effect row threads through in place of an `Applicative` wrapper, so effectful traversal needs no monad and no do-notation.

```prism
{{#include ../examples/hkt.pr}}
```

Classes remain single-parameter; multi-parameter classes are not supported.

## 7. Effects and Handlers

An `effect` declares a set of operations; each `ctl` operation has an argument list and a result type. Performing an operation is an ordinary call to its name. A function's effect _row_ is the set of effects whose operations it may perform and has not handled, written `! {L, ...}` on its result type, with an optional row variable tail `! {L | r}`. A bare `!` is an explicit empty row. A row is inferred when omitted.

```prism
{{#include ../examples/eff_state.pr}}
```

A `handle e with` block discharges operations; its grammar is the `handler` nonterminal of Section [4](#4-surface-grammar). Each operation clause names an operation and binds its arguments and the resumption `k` (the captured continuation, explained below); calling `k(v)` resumes the suspended computation with `v`, and `k` may be called zero times (abort), once (the common case), or many times (multishot). A `return r` clause transforms the final value. The handler in `eff_state.pr` interprets `get`/`put` by threading a state parameter, so `counter`, which only performs the operations, never mentions a state value.

Operations and handlers are delimited control: the `handle` block is the _delimiter_ (a prompt), and the resumption `k` is the _delimited continuation_ it captures, the slice of computation between the perform site and the handler. Being first-class, `k` reinstalls that slice under the same handler when invoked. This is the typed, named generalization of `shift`/`reset`: a single prompt with one anonymous continuation becomes a row of named operations, each with its own clause, and the effect row is the static record of which delimiters a computation still requires.

A clause may invoke `k` any number of times; more than once makes the continuation _multishot_: each call re-runs the captured slice from the perform site with a different result, so one handler can pursue several futures of the same computation. This is how nondeterminism or search handlers explore alternatives (an `amb` operation whose clause calls `k` once per choice and combines the outcomes) and how generators yield and continue. Never invoking `k` discards the captured slice, which is exactly how `raise` (Section [7.1](#71-observability)) and a `final ctl` clause abort.

### 7.1 Observability

The defining property of the row discipline: an operation handled inside a function is discharged, so it does not appear in that function's inferred row. In the example below, `checked` carries the row `! {Exn}`, but `attempt`, which handles `raise`, is pure.

```prism
{{#include ../examples/eff_exn.pr}}
```

### 7.2 Clause Sugar

Two clause forms abbreviate common shapes. `fun op(x) => e` is tail-resumptive sugar for `op(x, k) => k(e)`, resuming exactly once. `val v = e` is an install-time constant: `e` runs once when the handler installs, and every use of `v` returns it.

```prism
{{#include ../examples/handlers_funval.pr}}
```

A `final ctl op(x) => e` clause is non-resumable: it discards the continuation. This is the shape that `error`, `throw`, `try`, and `catch` desugar to (Section [7.5](#75-errors-and-failure)).

### 7.3 Masking

`mask<E>(e)` makes every operation of effect `E` performed in `e` bypass the innermost enclosing handler of `E` and reach the next one out. Masks nest, so a double mask skips two handlers. The masked expression still demands an enclosing handler, so `E` remains in its row.

```prism
{{#include ../examples/mask.pr}}
```

### 7.4 Local Mutation

A `var` mutates, yet the function holding it stays pure. `fib_iter` below updates two locals in a loop but has type `(Int) -> Int` with an empty row, so it is accepted where only a pure function is allowed. Prism has no mutation primitive; `var` is sugar over the effect system.

A `var x := e` desugars to a private two-operation effect (a get and a set); each read of `x` becomes a perform of get, each `x := v` a perform of set. In the same pass, a handler that threads the value as a hidden parameter is wrapped around the block. That handler discharges the get and set labels (Section [7.1](#71-observability)), so they never reach the function's type: the state is implemented but not observable. Effect lowering then turns the tail-resumptive handler into threaded arguments and the loop into a constant-stack loop, so the lowered code allocates nothing.

{{#tabs }} {{#tab name="Source" }}

```prism
{{#include ../examples/var_fib.pr}}
```

{{#endtab }} {{#tab name="Desugared" }}

```text
{{#include ../examples/var_desugared.txt}}
```

{{#endtab }} {{#tab name="Core" }}

```text
{{#include ../examples/var_core.txt}}
```

{{#endtab }} {{#endtabs }}

An escape analysis keeps the purity honest: the compiler rejects any closure or returned value that would carry the var out of its block, so the state cannot outlive its handler.

### 7.5 Errors and Failure

Prism has no built-in exception type. Errors and failure are two related mechanisms, both resting on the non-resumable `final ctl` clause of Section [7.2](#72-clause-sugar).

**Extensible errors.** An `error N(t)` declaration introduces a one-operation effect whose operation never resumes; `throw N(x)` performs it. A function's error row is exactly the set of errors it may raise and has not caught, and distinct `error` declarations union structurally as functions compose, with no umbrella sum type and no conversion glue: `find_port` carrying `{NotFound}` and `parse_port` carrying `{Malformed}` compose to `{NotFound, Malformed}`. `try e catch { ... }` is subtractive handler sugar (one nested `final ctl` per arm): a partial catch discharges the labels it names and lets the rest flow to an enclosing handler, and an uncaught error is an unhandled-effect error naming exactly the labels that remain. Each catch arm names an error and binds its fields to variables.

```prism
{{#include ../examples/errors.pr}}
```

These idioms span the recovery spectrum: the built-in `Exn` effect, raised by `error(code)` and uncatchable (it aborts); `Result` with the postfix `e?` propagation of Section [8](#8-expressions); a plain `match` on `Ok`/`Err`; and a custom non-resumable effect.

```prism
{{#include ../examples/exceptions.pr}}
```

**The failure axis.** Beyond named errors, Prism has an anonymous, recoverable `fail()`, the deterministic-functional-logic failure of the Verse calculus ([Augustsson et al., 2023](bibliography.md#augustsson-verse-2023)). `guard(b)` fails when `b` is false; `a ?? b` runs `a` under a failure handler and falls back to `b`; `e?.field` chains through options, failing on `None`; `optional`/`succeeds`/`default` reify a failing computation as an `Option`, a `Bool`, or a default; and a comprehension guard may itself fail, pruning the element (Section [8](#8-expressions)). `transact body else fallback` snapshots every live `var`, runs the body under a failure handler, and restores the snapshots on failure, so an aborted attempt leaves observable state unchanged. The whole axis is `final ctl` handlers over a `Fail` effect, so an unhandled `fail()` is the ordinary unhandled-effect error, and "failable only in a failure context" falls out of the row discipline for free.

```prism
{{#include ../examples/transact.pr}}
```

### 7.6 Effect Polymorphism

A function can be generic over the effects of a thunk it is given by quantifying over a row variable in the argument's type. Below, `twice` accepts any `(Unit) -> Int` thunk and adds an open row `{| e}` for whatever that thunk performs; each call unifies `e` with the actual row (empty, `{Tick}`, or `{Say}`), and a handler discharges only the label it names, leaving the rest in `e`. This is the mechanism the prelude's `fmap` and `traverse` use to thread a per-element effect (Section [6.3](#63-higher-kinded-classes)), so an effectful traversal needs no `Applicative` wrapper.

```prism
{{#include ../examples/eff_poly.pr}}
```

## 8. Expressions

The expression grammar is in Section [4](#4-surface-grammar) and the effect and failure forms are in Section [7](#7-effects-and-handlers); the forms below are those the grammar alone does not settle.

A method call `e.m(args)` is uniform-function-call sugar for `m(e, args)`. A trailing block argument, `e.m(args) fn (x) { body }`, appends a lambda as the last argument; this is how the stream consumers in [streams.pr](./compiler.md#9-effect-lowering) chain. Field access is `e.field`.

### 8.1 Comprehensions

A comprehension `[ e for x in s, q, ... ]` collects `e` for each element; a qualifier `q` is a guard `if g` or a binder `let y = e`. A guard is evaluated in a failure context, so an element is pruned both when `g` is false and when computing `g` fails: a failable accessor such as `at_list` (a prelude lookup, Section [12](#12-the-standard-prelude)) past the end of a list prunes that element rather than aborting. The statement form `for x in s, q, ... do body` runs `body` per survivor. Both desugar to the prelude's stream combinators (the `Emit` effect of Section [12](#12-the-standard-prelude)), so they fuse without building an intermediate list.

```prism
{{#include ../examples/comprehension.pr}}
```

### 8.2 Records

Record construction `C { f = e, ... }`, functional update `C { ..base, f = e }`, and nested path update `{ base | a.b = e, ... }` build and modify the records of Section [5.7](#57-records); each is an in-place write on a uniquely owned value. The `deriving (Lens)` getters and setters compose with them for deeper access.

```prism
{{#include ../examples/lens_derive.pr}}
```

## 9. Patterns

Patterns appear in `match` arms, `let` bindings, lambda and function parameters, and `catch` arms; their grammar is the `pattern` nonterminal of Section [4](#4-surface-grammar). A constructor pattern destructures a value of the algebraic data type that built it (Section [5.6](#56-algebraic-data-types)), binding its fields; literal, tuple, wildcard, and record patterns match the remaining forms.

A `match` arm may carry a guard, `pat if cond => body`; when the guard is false, control falls through to the next arm. Matches are checked for exhaustiveness and redundancy by the usefulness algorithm of [Maranget (2007)](bibliography.md#maranget-2007): an unreachable arm is an error, and a non-exhaustive match is an error naming a missing pattern. A guarded arm does not count toward exhaustiveness, since its guard may fail at run time.

```prism
{{#include ../examples/guards.pr}}
```

A `pattern N(x) for T = view ... make ...` declaration defines a bidirectional pattern synonym: in match position it runs `view` and succeeds when that returns `Some` (the present case of `Option`, Section [12](#12-the-standard-prelude)); in expression position it runs `make`. Here `view` and `make` are contextual keywords, significant only inside a `pattern` declaration. A synonym with both halves is a _prism_ (a composable view-and-build pair); one with only `view` is a view pattern.

```prism
{{#include ../examples/pattern_syn_sugar.pr}}
```

## 10. Declarations and Programs

A function is declared with `fn`; a parameter may carry a type annotation, a default value `:= e`, or the `borrow` modifier, which lets a pure function read a parameter without taking ownership of it. A return annotation is written `: !{R} T` for result type `T` and effect row `R`, `: ! T` for an explicit empty row, or `: T` to leave the row inferred. A parameter with a default may be omitted, and any argument may be passed by name as `f(p = e)`; the call is rewritten to positional form, filling omitted defaults. Defaults and named arguments are honored on top-level functions. A top-level `let` is a constant: its references are inlined. A `where` block attaches non-recursive, lexically scoped definitions to a function body.

A function may be annotated `fip` or `fbip` to assert the fully-in-place discipline of [Lorenzen et al. (2023)](bibliography.md#lorenzen-fp2-2023). `fbip` proves the body allocates no fresh cell and calls only annotated, allocation-free functions. `fip` additionally proves linearity (each owned, non-immediate binding is consumed at most once) and bounded stack (each recursive call in the group is a tail call or a single tail-modulo-cons or tail-modulo-add). These are static checks that reject a non-conforming body; the mechanism is described in [Compiler](./compiler.md#10-reference-counting-and-fbip-reuse).

```prism
{{#include ../examples/fip_list.pr}}
```

## 11. Modules

A file is a module and a directory is a namespace prefix: `import Data.Map` loads `Data/Map.pr`. A project is a `prism.toml` manifest plus a source tree, resolved from the project root. A single-file program is one module.

`import M` brings `M`'s exports into scope under qualified names; `import M (a, b)` also brings `a` and `b` into bare scope; `import M as N` adds the alias `N`. The `pub` modifier on a declaration makes it visible to importers; `pub import M (x)` re-exports `x` through the importing module. An `opaque type` exports its name but not its constructors.

Name resolution rewrites every top-level definition to a canonical, module-qualified symbol (an export as `Data.Map.insert`, a private as the unforgeable, source-unwritable `Data.Map@helper`) and merges all modules into one program keyed by those symbols. Because identity is the canonical symbol, two modules may export the same short name and coexist. This is namespacing, not separate compilation: there are no per-module artifacts, and changing one module recompiles the whole program.

Instances are global, but each records its defining module. An _orphan_ instance (defined apart from both its class and its head type) and instances that overlap across modules are reported as warnings; an ambiguity names each candidate's module.

## 12. The Standard Prelude

The prelude in `lib/prelude.pr` is in scope in every module. It is ordinary Prism, not built-in. Its contents, by category:

- **Data types.** `Option(a)`, `Result(a, e)`, `List(a)`, the balanced-tree `Map(k, v)`, and the hash table `HashMap(v)`. A set is a `Map(k, Unit)`, with a `set_*` API rather than a distinct type.
- **List combinators.** `map`, `filter`, `foldl`, `foldr`, `length`, `append`, `reverse`, `zip`/`unzip`, `take`/`drop`, `sort`, `range`, and the rest of the usual vocabulary.
- **Option and Result combinators.** `map_option`, `and_then`, `unwrap_or`, `map_result`, `and_then_result`, `result_or`, and conversions between the two.
- **The class tower.** `Eq`, `Ord` (with `Eq` as superclass), `Show`, and the higher-kinded `Functor`, `Applicative`, `Monad`, `Foldable`, `Traversable`, with instances for `List` and `Option`.
- **Strings and characters.** Classifiers (`is_digit`, `is_alpha`, ...), case mapping, `starts_with`/`ends_with`/`contains`/`index_of`, `split`, `trim`, `chars`, and single-allocation joining.
- **Arrays and maps.** The growable `Array(a)` API (`array_new`, `array_get`, `array_set`, `array_push`, with in-place update on unique ownership), the AVL `Map` and `set_*` API, and the `HashMap` API over string keys.
- **Streams.** The `Emit(a)` effect and the producer/transformer/consumer combinators `srange`, `sof`, `smap`, `skeep`, `stake`, `sfold`, `ssum`, `scollect`, which fuse without intermediate collections.
- **Numerics and failure.** Fixed-width `i64_*`/`u64_*` operations, common math, and the failure helpers `guard`, `optional`, `succeeds`, `default`.
