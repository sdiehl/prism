# The Prism Language Specification {#the-prism-language-specification}

Prism is a strict, impure functional language in the ML family whose type system tracks side effects. This document defines the surface language: its lexical structure, grammar, type system, and evaluation. It describes the language as the `prism` compiler accepts it.

## 1. Introduction {#introduction}

A Prism program is a set of modules, each a file of declarations. The surface language elaborates to a strict, call-by-push-value core ([Levy, 2004](bibliography.md#levy-2004)) in A-normal form (the companion [Compiler](./compiler.md) document), compiles to native code through LLVM, and is managed by deterministic reference counting rather than a garbage collector.

Three things distinguish Prism from its ML and Haskell ancestors. It is **strict**, with laziness opt-in through thunks over a [call-by-push-value](./compiler.md#the-core-calculus) core, so evaluation and effect order are left to right and explicit. Side effects are inferred, extensible **effect rows** ([effects and handlers](#effects-and-handlers)) that combine structurally across calls instead of through monads and track both observability and capability ([capability effects and IO](#capability-effects-and-io)): an operation handled inside a function does not appear in its type, so internally effectful code is reused as pure, and a function that reads the outside world names the part it reads (`Console`, `FileSystem`, `Random`, `Env`) rather than a blanket `IO`. The same reference-count discipline both frees memory and performs **fully-in-place (FBIP) update** ([declarations and programs](#declarations-and-programs)), compiling record updates and derived setters to in-place writes on uniquely owned values (those that a reference count proves have no other live reference; see [reference counting and FBIP reuse](./compiler.md#reference-counting-and-fbip-reuse)). Beyond these, the language provides isolated fibers through handlers, failure as ordinary typed control flow, record and replay of a program's interaction with the world over the capability effects ([record and replay](#record-and-replay)), derived lenses and use-site optic paths for deeply nested structure traversal and update ([optic paths](#optic-paths)), and fusing stream combinators ([streams](#streams)).

The deterministic core opens the door to globally content-addressed, replayable programs, where a definition is identified by the hash of its canonical Core form: names and binder spelling are erased by alpha-renaming, so alpha-equivalent definitions have the same identity, while any behavior-visible Core change moves the hash ([content-addressed core](./compiler.md#content-addressed-core)). The same identity discipline extends from code to execution: a suspended continuation is serialized as a `kont` envelope whose bundle digest names the code it may resume against ([the kont envelope](./compiler.md#the-kont-envelope)), so teleporting a running computation is not a side channel around the type system or package store ([suspend and resume](#suspend-and-resume)). It is content addressing applied to the live program state itself: `suspend` captures the continuation, `resume` re-derives the code hash before accepting it, and replayability supplies the byte-identical guarantee that moving the computation did not change it.

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
| `using`    | `canonical` | `replayable` | `without` | `alloc`    |

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

An `integer` is a run of decimal digits, optionally grouped by underscore separators (`1_000_000`) that are cosmetic and carry no value. A value that fits in a machine word is an immediate; a larger literal is an arbitrary-precision integer (bignum). The suffix `i64` or `u64` selects a fixed-width 64-bit lane that wraps on overflow. A `float` is an IEEE-754 double, written with a fractional part (`1.5`), an exponent (`1e25`, `1.5e3`), or both; the exponent may be signed (`1e-25`, `1E25`) and separators are admitted in its mantissa and exponent on the same rule. Exponent notation always denotes a `Float`. A separator is valid only between two digits, so a leading, trailing, doubled, or `.`/`e`-adjacent underscore is a lexical error. A `char` is a single Unicode scalar in single quotes. A `string` is double-quoted UTF-8.

There are no negative literals at the lexical level: a leading minus is the unary-minus operator ([operator precedence](#operator-precedence)), so `-5`, `-5i64`, and `-1.5` are `-` applied to the literal. `-5u64` is rejected because negation is undefined on the unsigned lane, and the exponent sign lives inside the `float` token, so it never collides with that operator. The lexical minimum of the signed fixed-width lane is written by folding the sign into the literal: `-9223372036854775808i64` is `I64` min, one past the magnitude the bare positive literal admits. The formatter preserves a writer's separator grouping verbatim.

The escape sequences `\n`, `\t`, `\r`, `\\`, `\"`, `\{`, and `\}` are recognized in both character and string literals; a character literal additionally accepts `\'`.

### 3.5 String Interpolation {#string-interpolation}

Within a string, an unescaped `{ expr }` is an interpolation hole. The hole text is re-lexed at its source position and elaborated as an expression whose type-directed display is spliced into the string; a top-level string is spliced in raw, not quoted the way the `Show` method renders it. A hole runs to its matching `}`, balancing nested braces and string literals, so a hole may itself contain a string with braces. A literal brace outside a hole is written `\{` or `\}`. An empty hole, an unterminated hole, and an unterminated string are each lexical errors. The catch arms of the error example under [errors and failure](#errors-and-failure) use interpolation, as in `"no such key: {k}"`.

### 3.6 Layout {#layout}

Prism uses the offside rule: indentation, not explicit braces, delimits a block. A layout block opens after any of the keywords or symbols `=`, `then`, `else`, `=>`, `of`, `with`, `handler`, `do`, `where`, `try`, `catch`, `transact`, `loop`, and after `fn` (a `while` block opens at its `do`). A `class`, `instance`, or `effect` body opens the same way, but after the head rather than a keyword: the head ends the line and the members follow as its indented block. The first token after such an opener sets the block's indentation column; a later line at that column starts a new item in the block, and a line indented less closes the block. Explicit `{` `}` override layout for expression blocks and may be used in place of an implicit one, as in the brace-delimited handler arms of the [masking](#masking) example. The three declaration bodies are the exception: they are layout-only, and a brace opening one is a parse error that names the layout rewrite.

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

The table gives the binding of each operator, loosest to tightest. Levels 1 to 9 are the `binop` operators of the grammar; level 10 is the prefix unary minus; level 11 is application, field access, and the postfix failure operators, which bind tighter than every `binop`. Unary minus is a _tight prefix_: it binds looser than application and projection but tighter than every binary operator, so `-f(x)` is `-(f(x))`, `-x * y` is `(-x) * y`, `-x ^ y` is `(-x) ^ y`, and a leading `f -x` is the binary `f - x` (there is no juxtaposition application; write `f(-x)`).

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
| 10    | prefix `-` (unary minus)                      | prefix        |
| 11    | `f(...)` `a[i]` `.field` `?.field` `?`        | left          |

## 5. Types and Kinds {#types-and-kinds}

Prism infers types by the bidirectional, higher-rank inference algorithm of [Dunfield & Krishnaswami (2013)](bibliography.md#dunfield-krishnaswami-2013). An unannotated declaration infers its principal type; an annotated one is checked against the annotation. Annotations are required for rank-N polymorphism, since a nested `forall` cannot be inferred.

Quantification is _predicative_: a type-constructor argument and an inferred type variable range over monomorphic types, so a `forall` may not be written directly as a type argument (`List(forall a. (a) -> a)` is rejected as impredicative). Higher-rank types are allowed wherever they are not a type argument, namely as a function parameter, a function result, and a declared data field; a polymorphic value can be carried through a generic container by wrapping it in a data type with a polymorphic field.

### 5.1 Types {#types}

The scalar types are `Int` (arbitrary precision), `I64`, `U64`, `Float`, `Bool`, `Char`, `String`, and `Unit`. A type constructor applied to arguments is written `Con(t, ...)`; the list type has the sugar `[t]` for `List(t)`. A tuple type is `(t, ...)`. A function type is `(t, ...) -> u`, optionally carrying an effect row on `u`. A universally quantified type is `forall a. t`. Type variables are `varid`s.

### 5.2 Kinds {#kinds}

A type has kind `*` (a type of values) or `* -> *` (a type constructor awaiting one argument), and so on; `List` has kind `* -> *`, since `List(Int)` is a type only once `Int` is supplied. A class parameter may range over a constructor of kind `* -> *`, applied as `f(a)` in method signatures; see [type classes](#type-classes). Each constructor's parameter kinds form an arrow `k1 -> ... -> *`, and an applied head is checked argument by argument against that arrow: too many arguments, or an argument whose kind does not match the parameter's, is a kind mismatch reported at the annotation. There is no separate global kind-checking phase; the remaining well-kindedness obligations are discharged during unification, which requires a constructor and its arguments to agree in arity.

Besides `*` and its arrows there is one further kind, `Row`, inhabited by effect rows rather than types. A type parameter annotated `: Row` ranges over rows, so a data type can carry an effect row as a parameter and thereby store an effectful computation in a field: in `type Cmd(a, e : Row)` a field may name `e` as `! {e}` (or in a tail, `! {IO | e}`), the constructor quantifies `e` with a row-level `forall`, and the applied head `Cmd(a, e)` carries the row in that position. A `Row`-kinded argument is an effect row, written either as a row variable (`Cmd(a, e)`) or a `{ .. }` row literal (`Cmd(Int, {IO})`); supplying a type where a row is expected, or a row where a type is expected, is a kind mismatch reported at the annotation. An unannotated parameter still defaults to `*`, so `Row` is opt-in and existing types are unchanged. This is the type-system support for storing an effect-polymorphic reified handler, such as the concurrency scheduler of [effects and handlers](#effects-and-handlers).

The third non-`*` kind is `Nat`, inhabited by type-level natural numbers, the dimensions of a shape-indexed type. A type parameter annotated `: Nat` ranges over dimensions, so in `type Vec(a, n : Nat)` the length `n` is a compile-time index rather than a stored field; an argument in that position is either a bare natural literal (`Vec(Int, 3)`) or a `Nat`-kinded variable (`Vec(a, n)`). As with `Row`, supplying a type where a dimension is expected, or a dimension literal where a type is expected, is a kind mismatch reported at the annotation. Dimensions unify **by equality only**: two literals unify when they are equal (`3` with `3`), a variable unifies with whatever dimension it meets, and a clash is a compile error naming both lengths (zipping a `Vec(Int, 3)` with a `Vec(Int, 4)` reports `expected length 3, but got length 4`). There is deliberately no successor structure and no arithmetic on dimensions: `n + m` and `n + 1` in a dimension position are declined at the parser with a pointed message, and this is a decision, not a gap. The consequence is stated honestly rather than worked around: an operation whose correctness needs an arithmetic relation between dimensions cannot be given a length-precise type. A length-changing `cons` of type `(a, Vec(a, n)) -> Vec(a, n + 1)` is therefore not expressible, and a `head` over `Vec(a, n)` cannot statically exclude the empty vector (which would require `n` to be a successor `m + 1`); such a `head` accepts any length and faults, or ranges over `Fail`, on the empty case. Equality-only dimension unification is exactly the reach that shape indexing needs (fixed-length containers, matching-length zips) without importing a dependent-arithmetic decision procedure into the frozen core. Dimensions are erased before the Core IR and never reach code generation, so a `Nat` index is a purely static fact: it constrains what type-checks but is invisible to every backend and to the determinism contract, exactly like a phantom parameter. An unannotated parameter still defaults to `*`, so `Nat` is opt-in.

### 5.3 Inference, Generalization, and Defaulting {#inference-generalization-and-defaulting}

A row is built from _labels_, the effect names of [effects and handlers](#effects-and-handlers) (a parametric effect's label carries type arguments). It is _closed_ when it ends in a fixed set of labels and _open_ when it ends in a row variable (`! {L | r}`), which stands for further labels the caller may add. An unannotated binding is generalized over its free type and row variables not fixed by the surrounding scope. A bare type variable written in a top-level function's signature is an implicit `forall`: it is universally quantified and rigid, so the body is checked to hold for every instantiation and may neither narrow it to a concrete type nor equate two distinct signature variables (a body that does is a type error), and the declaration exports exactly the polymorphic scheme it wrote. Two cases default rather than generalize, both resolved in one pass at generalization. A numeric operand of an arithmetic or comparison operator left otherwise unconstrained defaults to `Int`; because the default is deferred to that pass rather than applied at the operator, a later use that fixes the operand to a fixed-width lane (`I64`/`U64`) takes precedence, so `x + y` followed by an `i64` use of `x` is fixed-width, not `Int`. An open row left unconstrained at a monomorphic declaration (one with no remaining free row variable) defaults to empty (pure); an effect-polymorphic declaration keeps its row variable, as `traverse` does in the prelude ([the standard prelude](#the-standard-prelude)).

### 5.4 Subsumption and Row Equivalence {#subsumption-and-row-equivalence}

Checking a value against an expected type uses subsumption, not equality. A more polymorphic type is accepted where a less polymorphic one is expected: a `forall` on the expected side introduces a rigid variable the value must satisfy for all instances, and a `forall` on the value side is instantiated to meet the expectation. Function subtyping is contravariant in the arguments and covariant in the result, so a function accepting more and returning less may stand in for one accepting less and returning more.

Effect rows are checked by unification over scoped labels, not by covariant widening. Two rows are compared up to reordering: `! {A, B}` and `! {B, A}` are the same row, because unification hoists a demanded label to the head of the other row before matching the tails. An open row `! {A | r}` unifies with any row that provides `A` by binding `r` to the remainder; for instance `! {A | r}` unifies with `! {A, B}` by binding `r` to `{B}`. This is how a caller's row absorbs a callee's. A unification that would make a row contain itself is rejected, so recursive effect rows do not arise.

At a function arrow the value's effect row is made _equal_ to the expected one by this same unification, so a narrower row fits a wider context only by _solving_ a row variable, never by silent widening. A pure function still fits an effectful context, because its own latent row is a quantified variable ([effect polymorphism](#effect-polymorphism)) that unification solves to the demanded effects. Where a function carries an explicit return row, that annotation is the row its body is unified against: a body that performs an effect the annotation omits does not unify and is rejected with a diagnostic naming the effect the annotation must declare, and the annotation's row variables are rigid, so an annotation may not silently narrow to fewer effects than the body performs.

### 5.5 Fixed-Width Integers {#fixed-width-integers}

`Int` is arbitrary precision. `I64` and `U64` are the signed two's-complement and unsigned 64-bit lanes; they wrap on overflow rather than promoting to a bignum. Their operations are named builtins, not operators, since the surface `+`, `-`, and so on target `Int` and `Float`. Each takes two operands of the lane type.

| Family     | Operations (and the `u64_*` counterparts)                   |
| ---------- | ----------------------------------------------------------- |
| Arithmetic | `i64_add` `i64_sub` `i64_mul` `i64_div` `i64_rem` `i64_cmp` |
| Bitwise    | `i64_and` `i64_or` `i64_xor`                                |
| Shift      | `i64_shl` `i64_shr`                                         |

`and`, `or`, and `xor` share a single bit pattern across both lanes; `i64_shr` is an arithmetic (sign-extending) shift while `u64_shr` is logical; a shift count is taken modulo 64. `to_i64`/`to_u64` and `int_of_i64`/`int_of_u64` convert between `Int` and the fixed-width lanes.

### 5.6 Integer Arithmetic and Division {#integer-arithmetic}

The arithmetic operators `+`, `-`, `*`, `/`, and `%` spell integer arithmetic here through the [numerical tower](#numerical-tower)'s `Int`, `I64`, and `U64` instances; `^` is [exponentiation](#exponentiation). On `Int` they are arbitrary precision: a sum, product, or difference is exact and never overflows, promoting a machine-word result to a bignum on demand. This section states the two facts that arithmetic on `Int` cannot state by its type alone: how division rounds, and what division by zero does. Both are identical on the interpreter and native backends, a corollary of the determinism contract and pinned by the parity corpus.

Division truncates toward zero and remainder takes the sign of the dividend. That is, `/` discards the fractional part by rounding toward zero rather than toward negative infinity, and `a % b` has the sign of `a` (or is zero), so the identity `a == (a / b) * b + (a % b)` holds for every non-zero `b`. The four sign combinations make the rule concrete: `7 / 2` and `(0 - 7) / (0 - 2)` are `3`, while `(0 - 7) / 2` and `7 / (0 - 2)` are `-3`; `7 % 3` and `7 % (0 - 3)` are `1`, while `(0 - 7) % 3` and `(0 - 7) % (0 - 3)` are `-1`. This is truncated division, the semantics of C99, Rust, and the hardware division instruction both backends emit.

```prism
{{#include ../../tests/cases/run/num_int_div.pr}}
```

Floored division, where `/` rounds toward negative infinity and `%` (the Euclidean-adjacent modulus) takes the sign of the divisor, was considered and declined. Two reasons decide it. The fixed-width lanes are the constraint: `i64_div`/`u64_div` and their remainders are the machine's truncating division, and an `Int` operator whose meaning diverged from the lane it shares a spelling with would split the integer family into two rounding rules a reader must track by type. And the determinism contract wants one rule across every lane and both backends rather than a surface convenience that the hardware does not compute; a caller who wants a floored or Euclidean modulus writes it once over these primitives (`((a % b) + b) % b` for a non-negative residue) rather than having the language pick a second, silently different `%`.

Division or remainder by zero is the one partial case of integer arithmetic. It is a runtime fault: the program halts immediately with exit status 1 and exactly `fatal: division by zero` on standard error, byte-identical on the interpreter and the native backend, on both `Int` and the fixed-width lanes. It is not a value, and unlike the recoverable `fail()` of [errors and failure](#errors-and-failure) it is not routed through an effect and cannot be caught; it aborts the run the way an unrecoverable `error(code)` does. Every other integer operation is total.

The fixed-width lanes wrap rather than fault or promote ([fixed-width integers](#fixed-width-integers)): `i64_add`, `i64_sub`, and `i64_mul` (and their `u64_` and `U64` counterparts) are two's-complement modular arithmetic, so `i64_add(I64_MAX, 1)` is `I64_MIN` and `u64_add(U64_MAX, 1)` is `0`. Division wraps on the one signed input that would overflow it, so `i64_div(I64_MIN, -1)` is `I64_MIN` and `i64_rem(I64_MIN, -1)` is `0`, consistent with the wrapping add/sub/mul rather than trapping; only a zero divisor faults. Unary minus follows the same wrap on the fixed-width lane, so `-x` on `I64` is the two's-complement negation and `-I64_MIN` is `I64_MIN`. `Int`, being a bignum, has no such edge: negation and division there are always exact.

```prism
{{#include ../../tests/cases/run/num_fixed_wrap.pr}}
```

#### 5.6.1 Safe Arithmetic Families {#safe-arithmetic}

The wrapping and faulting defaults above are the primitives; a program that wants overflow to be visible rather than silent reaches for the safe families in the `Data.Checked` library, which layer four disciplines over those primitives through one class, `Checked(a)`. The `checked_*` methods (`checked_add`, `checked_sub`, `checked_mul`, `checked_neg`, `checked_div`, `checked_mod`) return `Option(a)`, `None` exactly when the operation overflows the lane or divides by zero. The `saturating_*` methods (`add`, `sub`, `mul`) clamp to the bound the overflow crossed instead. The `wrapping_*` methods (`add`, `sub`, `mul`, `neg`) are explicit names for the two's-complement wrap the raw operators already perform ([fixed-width integers](#fixed-width-integers)), so a caller can spell the intent rather than rely on the default. And the `overflowing_*` methods (`add`, `sub`, `mul`) return the wrapped result paired with a `Bool` that is true precisely when the operation overflowed. Instances cover `I64`, `U64`, and `Int`; the checked narrowings `int_to_i64` and `int_to_u64` sit beside the class as free functions returning `Option`, the partial inverses of the total widenings `int_of_i64`/`int_of_u64`.

`Checked` sits beside the arithmetic classes rather than inheriting from them: it carries no superclass and no raw operators, so it stays meaningful for any integer lane independently of what algebraic structure that lane also has. The connection runs the other way, as a law. The `wrapping_*` methods agree exactly, value for value, with the lane's raw arithmetic, `wrapping_add`/`wrapping_sub`/`wrapping_mul` with the two's-complement `+`/`-`/`*` and `wrapping_neg` with unary negation. `wrapping_neg` on `U64` is that same two's-complement wrap the lane's other operations use, so `wrapping_neg(0)` is `0` and `wrapping_neg(x)` is `U64_MAX - x + 1` for a nonzero `x`, rather than a fault or a rejection; the unsigned lane simply has no non-wrapping negation to prefer. Because the agreement is with the raw operators, it is stable under any later refactor that gives those operators a class of their own: the `wrapping_*` methods and the lane's ring operations remain the same function by construction.

The families are not independent definitions that happen to line up; each fixed-width operation is computed once in the exact `Int` lane and then narrowed three ways, so the laws hold by construction and are pinned on both backends. For a lane bounded by `[lo, hi]`, `checked_op(x, y)` is `Some(wrapping_op(x, y))` when the exact result lies in range and `None` otherwise; `overflowing_op(x, y)` is `(wrapping_op(x, y), flag)` with `flag` true iff `checked_op(x, y)` is `None`; and `saturating_op(x, y)` is that same wrapped value when it is in range, and otherwise the crossed bound, `hi` on overflow above (`I64` max or `U64` max) and `lo` below (`I64` min or `0`). The overflow cases follow the primitives exactly: `checked_add(I64_MAX, 1)` is `None` while `saturating_add(I64_MAX, 1)` is `I64_MAX`; `checked_neg(I64_MIN)` and `checked_div(I64_MIN, -1)` are `None`, the two signed edges where the exact result escapes the lane; and `checked_sub` on `U64` is `None` on any unsigned underflow, with `checked_neg` there `Some(0)` only for `0`. Division and remainder inside a `checked_*` follow the truncating rule of [integer arithmetic](#integer-arithmetic). The `Int` instance is the degenerate case that keeps the class total rather than vacuous: unbounded, so `wrapping_*` and `saturating_*` are the identity, `overflowing_*` always flags `false`, and only a zero divisor turns a `checked_*` into `None`.

```prism
{{#include ../../tests/cases/run/law_checked.pr}}
```

### 5.7 Floating-Point Arithmetic {#floating-point}

`Float` is an IEEE-754 double. Its arithmetic operators are the plain `+`, `-`, `*`, `/`, and `%` through the [numerical tower](#numerical-tower) (the dot-suffixed forms `+.`, `-.`, `*.`, `/.` remain as deprecated aliases), and its comparisons are the dot-suffixed `==.`, `/=.`, `<.`, `<=.`, `>.`, `>=.` ([operators](#operators-and-punctuation)); there is no implicit coercion between `Int` and `Float`, so a mixed expression is a type error resolved by an explicit `to_float` ([exponentiation](#exponentiation)). Floating-point arithmetic is where a language most often becomes tier-dependent, because a fused multiply-add, an extended-precision register, or a differently rounded library call changes a low bit. Prism forbids that: every float operation follows one rounding rule and one set of special-value rules, and the interpreter and both native backends agree bit for bit, pinned by the parity corpus and, for the printer, by a dedicated formatter oracle.

The rounding contract is round to nearest, ties to even, the IEEE-754 default, applied to every arithmetic operation with no fused or wider-than-double intermediate. This is the single rule the language commits to, and it is why `0.1 + 0.2` is `0.30000000000000004` and `1.0 / 3.0` is `0.3333333333333333` identically everywhere: the result is the correctly rounded double, not an artifact of an evaluation order or a backend.

Float division never faults. Where integer `/` by zero aborts, `/.` by zero is an ordinary IEEE result: `x / 0.0` is `inf` or `-inf` according to the sign of the numerator and of the zero, and `0.0 / 0.0` is `nan`. A `nan` then propagates through every arithmetic operation it touches, so `nan + 1.0` and `nan * 0.0` are both `nan`; there is no arithmetic that turns a `nan` back into a finite number. Because no float operation faults, a floating-point pipeline never introduces a failure edge into a function's effect row the way integer division by zero conceptually could.

Signed zero is observable. `0.0` and `-0.0` are distinct values that compare equal (`0.0 ==. -0.0` is `true`) yet are distinguished by any operation that reads the sign bit: `1.0 / 0.0` is `inf` while dividing by negative zero is `-inf`. Unary minus on a `Float` is a genuine sign flip, not a subtraction from zero, so `-(0.0)` is `-0.0` (a subtraction `0.0 - 0.0` would give `+0.0`) and `-(-0.0)` is `0.0`; the sign flip is bit-identical on the interpreter and both native backends. Comparisons follow IEEE unordered semantics for `nan`: `nan` is equal to nothing including itself, so `nan ==. nan` is `false` and `nan /=. nan` is `true`, and every ordering against `nan` (`nan <. x`, `nan >. x`) is `false`. The program below exercises each of these on both backends.

```prism
{{#include ../../tests/cases/run/num_float_ieee.pr}}
```

Printing is owned by the canonical `Float` formatter and not respecified here; this section fixes only the tokens the special values render as, since a claim about `nan` or `-0.0` is a claim about output. `show` (and therefore `print` and string interpolation, [type classes](#type-classes)) renders a `nan` as `nan`, positive and negative infinity as `inf` and `-inf`, and negative zero as `-0`, distinct from `0` for positive zero; the shortest round-tripping form the formatter chooses for finite values is the formatter's contract, not this chapter's.

#### 5.7.1 Elementary Functions and Conversions {#elementary-functions}

The elementary functions are owned the same way the arithmetic is. Rather than call whatever `libm` the platform links, Prism vendors one implementation of the double-precision math library and routes every function through it on every backend: the native code calls it, and the interpreter calls the identical compiled symbols, so a transcendental is a consequence of in-repo code, not of a system library's rounding. The determinism flag that makes this hold at the lowest bit is floating-point contraction disabled everywhere (`-ffp-contract=off`), so no fused multiply-add fuses `a*b+c` on one platform and not another, in ordinary arithmetic or inside these functions.

The accuracy statement is deliberately modest and honest: the contract is **determinism, not correct rounding**. Each function is a deterministic faithful approximation, bit-for-bit identical on the interpreter and both native backends and across platforms, but it is not guaranteed to be the correctly rounded double of the true real result. Correctly-rounded transcendentals (the table-maker's-dilemma problem) are an explicit non-goal; what the language guarantees is that whatever value a function produces, it produces the same value everywhere, pinned by the conformance corpus over the hard cases (subnormals, the extremes, argument reduction near multiples of pi/2, signed zero, `nan`, and the infinities) and a deterministic bulk sweep.

The functions divide into two classes. The **exact** operations are correctly rounded or integer-valued by IEEE-754 and therefore identical on every conforming platform regardless of implementation: `sqrt` (correctly rounded), `abs_float`, and the roundings `floor`, `ceil`, `trunc` (toward zero), and `round` (ties away from zero, so `round(2.5)` is `3.0` and `round(-2.5)` is `-3.0`, distinct from the ties-to-even of arithmetic). The **approximate** transcendentals are the owned-library functions: `sin`, `cos`, `tan`; the inverses `asin`, `acos`, `atan`, and the two-argument `atan2(y, x)`; the hyperbolics `sinh`, `cosh`, `tanh`; the exponentials `exp`, `exp2`, `expm1`; the logarithms `ln` (natural), `log2`, `log10`, `log1p`; `pow`, `cbrt`, and `hypot`. `fmod(x, y)` is the exact IEEE remainder. Domains and special values follow the usual conventions and propagate IEEE special values: a `nan` argument yields `nan`; `asin` and `acos` are `nan` outside `[-1, 1]`; `sqrt` of a negative is `nan`; `ln`, `log2`, `log10` are `-inf` at `0` and `nan` below it; `atan2` and `hypot` are defined on the whole plane; and every function is total (none faults), so like the operators they add no failure edge to an effect row.

The `Int`/`Float` conversions pin their rounding once, identically on both backends. `to_float` rounds an `Int` to the nearest `Float`, ties to even. The three float-to-`Int` conversions differ only in how they round to an integer before converting: `truncate` toward zero, `floor_to_int` down, `ceil_to_int` up. All three then apply one saturating cast: a value beyond the signed 64-bit range clamps to that range's endpoint, and `nan` converts to `0`, matching the interpreter's semantics exactly (the native backend uses the saturating conversion, never the undefined-on-overflow one). A result that exceeds the tagged-immediate range becomes a bignum `Int`, so `truncate(1e300)` is the saturated `9223372036854775807` on both backends rather than a wrapped low word.

#### 5.7.2 The Numerical Tower {#numerical-tower}

The arithmetic operators are one spelling per operation across every lane, with the lane chosen by the operand's type and resolved entirely at compile time. Two classes carry them. `Num(a)` provides `+`, `-`, `*`, and unary minus; `Div(a)` provides `/` and `%`. Both have instances for `Int`, `I64`, `U64`, and `Float`, so `+` reads on any of them and the earlier per-lane semantics of this chapter (the exact `Int`, the wrapping fixed-width lanes, the IEEE `Float`) are the instances' behavior, unchanged. `Div` is split from `Num` so a type with addition but no sensible division stays representable without a vacuous method. The dot-suffixed float operators `+.`, `-.`, `*.`, `/.` remain as aliases for the plain operators on `Float` and are scheduled for removal; a plain `+` on `Float` and a `+.` elaborate to the identical primitive.

Resolution has no runtime cost. A monomorphic operand keeps the lane's direct primitive, exactly the code the operator emitted before the tower, so the class dictionary never survives specialization and the generated core is byte-identical, pinned by the allocation gate. Only genuinely polymorphic code, a function written `given Num(a)` or `given Div(a)`, dispatches through a dictionary, and that dictionary too is erased wherever the function is specialized to a concrete lane. Unary minus follows the same rule: `-x` on a concrete lane is the sign flip or two's-complement negation of [floating-point](#floating-point) and [integer arithmetic](#integer-arithmetic), and `-x` on a `Num(a)` operand dispatches through the class with the same value. Unsigned `U64` has no surface negation (`-x` on a `U64` is a type error naming the signed lanes), but the `Num(U64)` instance's negation is the two's-complement wrap, reachable through generic `Num` code and agreeing with `wrapping_neg` ([safe arithmetic](#safe-arithmetic)).

Integer literals are polymorphic. A literal with no width suffix adopts whatever numeric lane its context expects: `1` is a `Float` where a `Float` is wanted (so a `Float`-typed binding or argument needs no `.0`), an `I64` in an `I64` position, and so on, with the lane's constant placed directly in the elaborated core and no runtime conversion. A decimal or exponent literal denotes a fractional lane, of which `Float` is currently the only one. The **defaulting rule** fixes the ambiguous case: an integer literal with no constraining context defaults to `Int`, and a fractional literal to `Float`. The default always fires, so a program that never mentions the numeric classes never sees a class-constraint error; `let n = 5` is an `Int` exactly as before the tower. A width-suffixed literal (`5i64`, `5u64`) is monomorphic, its suffix a type ascription rather than a hint, and a literal out of range for the lane it resolves to is a compile error at resolution time.

There is no implicit coercion, ever. The lane a value carries is fixed by its type, and only literals adapt; a variable never does. `x + 2.5` where `x : Int` is a type error naming both lanes, not a promotion of `x` to `Float`, and the same holds across any two distinct lanes (`I64` and `U64`, `Int` and `Float`). Cross-lane movement is always an explicit, named conversion (`to_float`, the checked narrowings and exact widenings of [fixed-width integers](#fixed-width-integers) and [safe arithmetic](#safe-arithmetic)). This is the line between a numeric surface that stays predictable and one whose every operator hides a possible conversion.

### 5.8 Algebraic Data Types {#algebraic-data-types}

A `type` declaration introduces an algebraic data type: a _sum_ of constructors, each a _product_ of fields. A constructor is named with an upper-case identifier and applied like a function to build a value; a `match` ([patterns](#patterns)) destructures a value by constructor. A type may take type parameters and may be recursive, including mutually so. A type parameter may be annotated `: Row` to range over an effect row rather than a type ([kinds](#kinds)), so a field can store an effectful computation, as in `type Cmd(a, e : Row)` whose field is a `() -> a ! {e}`, or `: Nat` to range over a compile-time dimension, as in `type Vec(a, n : Nat)` whose length index is erased rather than stored.

```prism
{{#include ../examples/adt.pr}}
```

A `newtype` is a data type with exactly one single-field constructor: a type distinct from its payload, with no runtime wrapper. An `alias` on a type expression is a transparent synonym, interchangeable with its definition. An `alias` whose body is a row literal is a _row alias_, the same transparency for a set of effect labels: usable wherever a row is written, expanded before checking, and composable with other aliases ([composing rows](#composing-rows)); a row alias takes no parameters. A `deriving (C, ...)` clause generates the named instances structurally ([type classes](#type-classes)). `Eq`, `Ord`, `Show`, `Hash`, and `Lens` are derivable everywhere: derived `Ord` compares fields lexicographically in declaration order and orders constructors by declaration, and derived `Hash` folds the value through the same blake3 Merkle construction that content-addresses code ([content-addressed core](compiler.md#content-addressed-core)), so structurally equal values carry one canonical digest on every backend. Three more classes derive against opt-in modules: `Serialize` and `Stable` (`import Wire`) for the wire codec, where `Stable` derives only when every component is itself `Stable` and a non-stable field is a compile error at the derive site, and `Arbitrary` (`import Test`) for property-test generators built from the type's structure ([stable blocks](#stable-blocks)). `deriving (Identifiable)` is shorthand for the identity starter pack, expanding to exactly `Eq`, `Ord`, `Hash`, and `Show` so an ID newtype is comparable, hashable, and printable from one keyword with no imports; a class listed alongside it is derived once, not twice, and `Arbitrary` is deliberately excluded (it lives behind `import Test` and is a testing concern), so a value that also wants a generator writes `deriving (Identifiable, Arbitrary)`.

### 5.9 Records {#record-types}

A constructor may instead take _named_ fields, `C { f : T, ... }`, making the type a record. A field is read with `e.f`; records are built and updated by the [record expressions](#record-expressions). `deriving (Lens)` synthesizes a getter `f_of` and a setter `with_f` per field.

```prism
{{#include ../examples/record.pr}}
```

## 6. Type Classes {#type-classes}

A class declares a single-parameter constraint and a set of method signatures. An instance is a _named_ value providing those methods for one head type. A function states its constraints with a `given` clause after the return annotation, as `maximum_by_ord` and `join_shown` below do, and receives its dictionaries as hidden arguments resolved at each call site, one per constraint. The following program declares a second `Ord(Int)` instance named `ordDesc` that reverses the ordering, designates the prelude's ascending `ordInt` as canonical, and selects each explicitly.

A class, instance, or effect body is a layout block: the head ends its line and the members follow on indented lines, one per line, with no braces and no `where`. Each instance method is written in expression form, `fn m(x) = e`, and because the body is layout rather than brace-delimited it is a full layout context, so a method needing several bindings uses the same layout-sequenced statements a top-level `fn` body admits, not only `let .. in` chaining. A brace opening one of these bodies is a parse error that names the layout rewrite. A marker class with no methods, and its instance, are written as the bare head with no body.

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

A consequence worth naming: equality, ordering, and hashing are ordinary methods of coherent classes (`Eq`, `Ord`, `Hash`), never built-ins that work on any value by inspecting its representation. Prism has no polymorphic structural `==`, `compare`, or `hash`. A structural default is a known hazard: it typechecks on functions, abstract types, and cyclic values where it has no principled meaning, and it silently overrides whatever notion of equality an abstraction intended. OCaml's Base goes so far as to shadow the polymorphic versions to keep them out of reach; in Prism the hazard never arises, because the only equality in scope is the one an `Eq` instance supplies and coherence makes that instance unique.

Printing follows the same discipline. `print` and `println` display a concrete argument by its structure (a top-level string prints raw, exactly as interpolation splices it), but a polymorphic argument requires `Show`: a generic function that prints declares `given Show(a)`, the display dispatches through the instance (a generic `Bool` prints `true`, never a representation tag), and printing a rigid type variable without the constraint is a type error naming the missing `given Show(a)`. What is never consulted is the runtime representation; the tag check that guards the raw printer is defense in depth against compiler bugs, not a semantics.

### 6.2 Superclasses {#superclasses}

A class may require another as a superclass with `given`. Each instance then stores a resolved superclass dictionary as the leading field of its dictionary cell, and a `given Ord(a)` constraint discharges an `Eq(a)` obligation by projecting that field. The superclass witness is found automatically from the instances in scope.

```prism
{{#include ../examples/superclass.pr}}
```

### 6.3 Higher-Kinded Classes {#higher-kinded-classes}

A class parameter may be a type constructor of kind `* -> *`, applied as `f(a)` in method signatures and resolved on the head constructor of each instance. The prelude's `Functor`/`Applicative`/`Monad`/`Foldable`/`Traversable` tower is built this way. The example below builds that tower explicitly over a custom container, each level naming its predecessor as a superclass with `given`, so an instance high in the tower can exist only where the ones below it do.

```prism
{{#include ../examples/hkt_tower.pr}}
```

The prelude provides the same tower for `List` and `Option`. Its methods are _effect-polymorphic_ (defined under [effect polymorphism](#effect-polymorphism)): a per-element effect row threads through in place of an `Applicative` wrapper, so effectful traversal needs no monad and no do-notation. Using it, one `fmap`/`ap`/`bind`/`traverse` works across either container.

```prism
{{#include ../examples/hkt.pr}}
```

So `Monad` here is just another class, structure for `List`-style nondeterminism and `Option`-style failure, with none of the language integration it carries elsewhere: no do-notation, no privileged status, no `return`. Sequencing side effects is the effect system's job, not the monad's.

The two systems meet in `Traversable`. The example below defines a recursive `Tree`, gives it the `Functor`/`Foldable`/`Traversable` instances, then runs a single generic `traverse` over it four ways. Nothing about the traversal changes between them; the behaviour is chosen entirely by the effect the per-element function performs, since `traverse`'s signature carries that row straight through. `State` numbers the leaves, `Fail` short-circuits, `Choice` (resumed multishot) enumerates every assignment, and `{State, Fail}` does the first two at once under two stacked handlers. Each is a job a monadic language hands to a different `Applicative` instance (`State`, `Maybe`, the list monad) or, for the last, a `StateT s Maybe` transformer stack; here it is one traversal and the effect rows supply the rest. This is the whole type system in one program: higher-kinded classes with a superclass chain, principal effect rows that compose, and handlers (including multishot resumption) discharging them.

```prism
{{#include ../examples/effectful_traverse.pr}}
```

Because a row is an unordered set, `{State, Fail}` fixes no layering the way a transformer stack must: whether a failure discards the numbering or keeps it is decided by which handler sits outside the other at the use site, not baked into the type. The monad-transformer ordering question, `StateT s Maybe` versus `MaybeT (State s)`, moves from the type to the handler site, free to differ from one call to the next without changing a single signature.

Classes remain single-parameter; multi-parameter classes are not supported.

## 7. Effects and Handlers {#effects-and-handlers}

An `effect` declares a set of operations; each operation has an argument list and a result type. Performing an operation is an ordinary call to its name. A function's effect _row_ is the set of effects whose operations it may perform and has not handled, written `! {L, ...}` on its result type, with an optional row variable tail `! {L | r}`. A bare `!` is an explicit empty row. A row is inferred when omitted.

An operation's declaration carries a _grade_, the resumption multiplicity every handler clause for it must respect, written as the keyword prefix `ctl`, `fun`, or `final ctl`. The grades form a three-point lattice ordered `final ctl < fun < ctl`: `final ctl` never resumes (the continuation is dropped), `fun` resumes exactly once in tail position (no capture), and bare `ctl` may capture the continuation and resume any number of times. `ctl` is the default and the most general grade, so an operation declared without a narrower prefix admits every handler. The checking rule is one line: a handler clause's own multiplicity must be at most its operation's declared grade. A clause that resumes a `final ctl` operation, or that captures or re-enters the continuation of a `fun` operation, is rejected at that clause, its caret naming the operation and its declared grade; a clause more restrictive than the grade (handling a `ctl` operation tail-resumptively, say) is always allowed. The grade is a static, checked fact only: it constrains which handlers typecheck and lets the compiler keep an unrelated in-place `var` loop on its fast lowering when some other component resumes multishot, but it never changes the observable behavior of an accepted program.

| Prefix      | Grade      | Resumption                                                               |
| ----------- | ---------- | ------------------------------------------------------------------------ |
| `final ctl` | `0` (zero) | never resumes; the continuation is dropped                               |
| `fun`       | `1` (one)  | resumes exactly once, in tail position, without capturing `k`            |
| `ctl`       | `ω` (many) | may capture `k` and resume any number of times, including zero (default) |

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

The old joke about purity is that a function of type `Int -> Int` cannot launch the missiles. A single `IO` type can put it no more precisely than that: somewhere, something happens to the world. Here the international side effect is declared in the language itself, an `effect Missiles` whose row label follows `first_strike` through every signature that might perform it, and observability is what disarms it: `war_games` handles `launch` and never resumes, so its inferred type is `() -> Int`, pure. The missiles are not merely unlaunched but gone from the type. `joshua` adds multishot resumption ([effects and handlers](#effects-and-handlers)): its `choose` clause resumes the continuation once per side, so every future of the exchange is played out under the treaty handler and their scores summed. Every future is explored, none of them wins, and `joshua` is still pure. So thermonuclear war doesn't typecheck, world peace achieved.

```prism
{{#include ../examples/missiles.pr}}
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

### 7.4 Named Handlers {#named-handlers}

The statement form `with handler { ... }` scopes a handler over the remainder of the enclosing block, so a stack of handlers reads as a flat sequence of layers rather than a rightward drift of nested `handle` expressions ([composing rows](#composing-rows) puts this form to work). Adding a binder makes the handler first-class: `with f <- handler { ... }` installs the handler and binds it as an _instance_, and an operation addressed through it, `f.read()`, dispatches to that instance even when another handler of the same effect sits closer. A bare `read()` still reaches the innermost ordinary handler, so two instances of one effect can serve one scope, distinguished by name where the innermost-handler rule alone could not tell them apart. [Masking](#masking) skips handlers by position; a named handler addresses one directly.

```prism
{{#include ../examples/named_handlers.pr}}
```

Each instance desugars to a fresh private effect whose operations are unforgeable from source, so the rest of the pipeline sees ordinary effects and ordinary rows; resumption is unrestricted through an instance (the multishot clause above resumes the continuation of `h.ask()` twice). The escape analysis of [local mutation](#local-mutation) applies here too: a closure or returned value that would carry an instance out of its `with` block is rejected, so an instance never outlives its handler.

The resource form `with x <- f(args)` generalizes the same shape to any function that takes its continuation last: the remainder of the block becomes a function `\(x) -> rest` appended to the call's arguments, so `f` decides when, whether, and how often to run the rest. This is the bracket idiom (acquire, use, release) written without nesting.

The same scope-local skolem underwrites ordered containers. A `Map(k, v)` is ordered by the ambient canonical `Ord(k)`, but a program that needs two orderings of the same keys at once cannot let a map built under one be walked under the other: the tree structure encodes the ordering, so a lookup under the wrong comparator silently returns the wrong answer. The map type carries a third, phantom parameter for exactly this, `Map(k, v, ord)`, a brand naming the ordering a map was built under; it appears in no field, so an unbranded `Map(k, v)` is the same type with the brand left to inference, and pre-brand source keeps checking unchanged. The `Data.Ordered` module (`import Data.Ordered`) hands out brands the way a named handler hands out an instance. `with_ordering(cmp, body)` runs `body` with a witness carrying `cmp`, and the witness's brand is a fresh rigid skolem unique to that call, so a map built through one witness carries a brand that a second witness's brand cannot unify with. Two witnesses coexist in one scope, and handing a map built under one to the other's operation is a compile-time type error naming both brands. The brand never escapes: the body's result may not mention it, so only a summary of a branded map (a size, a looked-up value, an encoded form) leaves the block, never the branded map itself.

This is the explicit half of the coherence story, and it closes statically. The implicit half is calling the ambient `map_insert` under a non-canonical `Ord` chosen with `using`, then reading the result under the canonical one. No v0.7 brand catches that at compile time: the two maps have the same unbranded type, and reflecting the chosen dictionary into the brand is the capability machinery of a later phase. Instead it is caught dynamically where it does the most harm, when an ordered container crosses a package boundary: a serialized map records its keys in the writer's order, and `Wire`'s map reader checks that they arrive strictly ascending under its own `Ord(k)`, faulting through [failure](#errors-and-failure) rather than rebuilding a mis-ordered tree when a map ordered by one comparator is read where a different one is canonical. Both faults, the compile-time brand mismatch and the runtime order check, are pure functions of the source and the pinned inputs, so a program's behavior never reveals which backend ran it. The division is deliberate and stated as such: the explicit witness path is static this release, the implicit path is dynamic, and only a later phase's dictionary reflection makes the implicit path static too. Nothing here claims the implicit path is closed statically today.

### 7.5 Local Mutation {#local-mutation}

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

### 7.6 Errors and Failure {#errors-and-failure}

Prism has no built-in exception type. Errors and failure are two related mechanisms, both resting on the non-resumable `final ctl` clause of the [clause sugar](#clause-sugar). With the imperative `break`, `continue`, and `return` of [imperative control flow](#imperative-control-flow), they are one mechanism wearing several faces: each is a single-operation effect whose handler never resumes the captured continuation, installed only where the corresponding keyword actually occurs, so non-local control costs nothing where it is not used and (being handled at its boundary) surfaces in no effect row where it is.

**Extensible errors.** An `error N(t)` declaration introduces a one-operation effect whose operation never resumes; `throw N(x)` performs it. A function's error row is exactly the set of errors it may raise and has not caught, and distinct `error` declarations union structurally as functions compose, with no umbrella sum type and no conversion glue: `find_port` carrying `{NotFound}` and `parse_port` carrying `{Malformed}` compose to `{NotFound, Malformed}`. `try e catch { ... }` is subtractive handler sugar (one nested `final ctl` per arm): a partial catch discharges the labels it names and lets the rest flow to an enclosing handler, and an uncaught error is an unhandled-effect error naming exactly the labels that remain. Each catch arm names an error and binds its fields to variables.

```prism
{{#include ../examples/errors.pr}}
```

**Stacks of failure modes.** Because each `error` is an ordinary row label, a row alias ([composing rows](#composing-rows)) names a set of failure modes: `alias ConfigErr = {NotFound, Malformed}` states a subsystem's failure vocabulary once, and a layer above extends it structurally, `alias AppErr = {ConfigErr, NetErr}`, with no umbrella type and no wrapping. A signature `: !{AppErr} Int` reads as "may fail in exactly these ways", and because expansion flattens before checking, `catch` subtracts labels from the expanded set like any other handler: a partial catch over an alias discharges the modes it names and leaves the rest in the row.

```prism
{{#include ../examples/failure_stack.pr}}
```

These idioms span the recovery spectrum: the built-in `Exn` effect, raised by `error(code)` and uncatchable (it aborts); `Result` with the postfix `e?` propagation of the [expression forms](#expressions); a plain `match` on `Ok`/`Err`; and a custom non-resumable effect.

```prism
{{#include ../examples/exceptions.pr}}
```

**The failure axis.** Beyond named errors, Prism has an anonymous, recoverable `fail()`, the deterministic-functional-logic failure of the Verse calculus ([Augustsson et al., 2023](bibliography.md#augustsson-verse-2023)). `guard(b)` fails when `b` is false; `a ?? b` runs `a` under a failure handler and falls back to `b`; `e?.field` chains through options, failing on `None`; `optional`/`succeeds`/`default` reify a failing computation as an `Option`, a `Bool`, or a default; and a comprehension guard may itself fail, pruning the element ([expressions](#expressions)). `transact body else fallback` snapshots every live `var`, runs the body under a failure handler, and restores the snapshots on failure, so an aborted attempt leaves observable state unchanged. The whole axis is `final ctl` handlers over a `Fail` effect, so an unhandled `fail()` is the ordinary unhandled-effect error, and "failable only in a failure context" falls out of the row discipline for free.

```prism
{{#include ../examples/transact.pr}}
```

**Partiality is in the row, not the name.** ML libraries such as OCaml's Base and Core suffix a partial function with `_exn` (`List.hd_exn`) so a reader knows it may raise, a naming convention standing in for what the type itself cannot say. Prism needs no such convention: a function that may fail carries that in its effect row, whether as the anonymous `Fail` above or a named `error`, so the possibility of failure is written into the signature and the row discipline forces it to be handled before the result is used. The `_exn` suffix is the workaround for a type system that cannot express failure; the row is the version the compiler checks.

### 7.7 Composing Rows {#composing-rows}

A row alias composes rows the way `+` composes sums. With `AB = {A, B}` and `CD = {C, D}`, the row `{AB, CD, E}` assembles five effects from two named pairs and a fifth label: `(A + B) + (C + D) + E`. Because a row is an unordered set ([subsumption and row equivalence](#subsumption-and-row-equivalence)) and an alias expands transparently before checking, the sum flattens: any grouping and any order of the same five labels is the _same row_, so `omega` and `flat` below are interchangeable, and a grouping is chosen for the reader, not for the checker. An alias may reference other aliases (a cycle is an error at the declarations involved), and takes no parameters.

```prism
{{#include ../examples/row_compose.pr}}
```

This is the row discipline's answer to the monad-transformer stack. A transformer application fixes one composite type, `ReaderT Config (WriterT Log (Except E))`, and pays for it twice: every layer's operations are lifted through the layers above (or a class such as `MonadWriter` is threaded through, at a quadratic cost in instances), and the order of wrapping is welded into every signature even where no code depends on it. An alias instead makes the application row a name for a set, `Ctx = {Ask, Tell}` and `App = {Ctx, Invalid}` below. An operation reaches its handler by label, never by position, so there is no `lift`; a function that uses only `Tell` states `!{Tell}` and slots unchanged into `App` or any other row containing it; and two subsystems' aliases union structurally, with no adapter between their stack and ours.

What a transformer stack fixes in the type, the handler site decides per call (the layering point already made for `{State, Fail}` under [higher-kinded classes](#higher-kinded-classes)). Discharged one label at a time with the scoped `with handler` layers of [named handlers](#named-handlers), the run function reads like the transformer stack it replaces, except that the order is chosen where the handlers install, free to differ between call sites without a signature changing. The application monad becomes the application row: a name for what may happen, not a recipe for how it is wrapped.

```prism
{{#include ../examples/app_stack.pr}}
```

### 7.8 Effect Polymorphism {#effect-polymorphism}

A function can be generic over the effects of a thunk it is given by quantifying over a row variable in the argument's type. Below, `twice` accepts any `(Unit) -> Int` thunk and adds an open row `{| e}` for whatever that thunk performs; each call unifies `e` with the actual row (empty, `{Tick}`, or `{Say}`), and a handler discharges only the label it names, leaving the rest in `e`. This is the mechanism the prelude's `fmap` and `traverse` use to thread a per-element effect ([higher-kinded classes](#higher-kinded-classes)), so an effectful traversal needs no `Applicative` wrapper.

The same row variable also governs an effect operation whose argument is a computation. An operation such as concurrency's `fork(() -> a ! {Async(a) | e})` shares the _ambient_ row for `e`: performing it ties the argument's row to the caller's own, so a forked or deferred computation may perform only effects the caller already admits, and those effects flow out to whoever handles the operation rather than escaping it (the discipline of Koka, Frank, and Links; [Leijen, 2017](bibliography.md#leijen-2017)). Combined with a `Row`-kinded parameter ([kinds](#kinds)) that stores the reified continuations, this is what makes a handler like `run_async` both effect-polymorphic and sound: it is written once for any row `e` the fibers perform, and a fiber cannot smuggle past it an effect that no outer handler was required to discharge.

```prism
{{#include ../examples/eff_poly.pr}}
```

### 7.9 Structured Concurrency and Cancellation {#structured-concurrency}

The [`Concurrent`](./stdlib/concurrent.md) library builds structured concurrency and cancellation on the `Async` operations above, and their contract is stated here as observable behavior rather than as a property of the scheduler. A `scope(tasks)` forks a list of fibers and joins them all before it returns, so no fiber outlives the call that spawned it, and a fiber's descendants are tracked so that an action taken on a fiber reaches everything it forked.

Cancellation is a cooperative unwind, not an abrupt drop. `cancel(f)` marks the fiber `f` and all of its descendants; each stops at its next suspension point (a `yield`, an `await`, a channel operation) rather than mid-step, and then unwinds through its finalizers so every resource it holds is released. A finalizer is installed with `on_cancel(cleanup, body)`, which guarantees `cleanup` runs exactly once whether `body` finishes normally or is cancelled, and nested `on_cancel` cleanups run innermost first, the same order a stack of `final ctl` handlers unwinds ([clause sugar](#clause-sugar)). Waiting on a fiber that may be cancelled never hangs: `try_await(f)` returns an `Outcome(a) = Completed(a) | Was_Cancelled`, `Completed(v)` when `f` produced `v` and `Was_Cancelled` when it was cancelled before it could, where a bare `await` would have no value to yield.

A `scope` is fail-fast. If one task fails with an unhandled `fail()` ([errors and failure](#errors-and-failure)), its sibling tasks are cancelled, their `on_cancel` finalizers run, and the failure is re-raised at the scope boundary rather than being swallowed. The failure therefore leaves `run_async` in the caller's residual row: `run_async : (() -> a ! {Async(a) | e}) -> a ! {e}` discharges `Async` but a failing scope forces `Fail` into `e`, so a program that spawns fallible work carries `{Fail}` out to a handler exactly as if it had performed `fail()` directly. Cancellation and failure are thus one mechanism seen from two sides: a deliberate `cancel` and a fail-fast sibling cancellation unwind through the identical finalizer path, so a resource is released once and only once on either.

### 7.10 Capability Effects and IO {#capability-effects-and-io}

Reading the outside world is itself effectful, and the row records which part of the world a function reads. The nondeterministic input operations are the four _capability_ effects `Console` (`read_int`, `read_line`), `FileSystem` (`read_file`, `file_exists`), `Random` (`rand`), and `Env` (`getenv`, `args_count`, `arg`). A function that reads input names exactly that capability in its row: a function calling `read_int` carries `! {Console}`, not a blanket `! {IO}`, so the row says which part of the world is read rather than merely that some IO happens. (`Console`, `FileSystem`, `Random`, and `Env` are therefore reserved effect names, among the [keywords](#keywords). The `Concurrent` library adds a fifth capability, `Clock`, described below. One further name, `Preempt`, the row label a preemptive scheduler will discharge, is reserved not shipped: it is rejected as a user effect declaration and, being outside the `replayable`-permitted set, makes a preemptive program non-replayable by the existing row check with no new rule.)

The surface is unchanged: `read_int()`, `read_file(p)`, `getenv(s)`, and friends stay ordinary calls, defined in the prelude as thin wrappers that perform the corresponding capability operation. A default `run_io` world handler is wrapped around `main` on demand, only when `main` reaches a capability, and discharges each operation by performing the real input and resuming with the result, so the capabilities collapse to `! {IO}` at the program boundary. The handler is tail-resumptive, so it fuses to a direct call at no cost ([effect lowering](./compiler.md#effect-lowering)). Output stays an opaque `IO` effect: `print`, `write_file`, `append_file`, and `remove_file` carry `! {IO}` and are not capability operations, because [record and replay](#record-and-replay) needs only inputs pinned. Binary file IO sits on the same split: `read_bytes(p)` is a `FileSystem` capability that reads a file as raw `Bytes` and is recorded like any other input, its own operation rather than a detour through `read_file` (routing bytes through a `String` would corrupt them at the first non-UTF-8 byte), while `write_bytes(p, bs)` is an `IO` output returning a `Result`.

Below, `roll` performs `Random` alone, `user` performs `Env` alone, and `summary` carries the structural union `! {Env, Random}` of what it calls; the capabilities collapse to `! {IO}` only at `main`, where `run_io` discharges them.

```prism
{{#include ../examples/capabilities.pr}}
```

Because input is now an interceptable operation rather than an untracked builtin, a handler other than `run_io` can supply the values, which is what record/replay rests on.

Time is a capability too. The `Concurrent` library's `Clock` effect (`now`, `sleep`) is discharged by `run_clock`, which threads a pure logical counter: `now()` reads the current tick and `sleep(d)` advances it, so time is virtual and a run is deterministic and replayable with no real clock and no time primitive. A fiber may perform `Clock`; because the scheduler does not handle it, `Clock` flows out of `run_async` to an enclosing `run_clock` like any other capability. The idea is a routing of `now`/`sleep`/timeouts through an ambient time capability rather than the wall clock: a test advances a virtual clock and scheduling becomes a pure function of it, so the cooperative-deterministic story is _testable_ rather than merely asserted, and retrofitting a clock later is avoided. Treating time as one capability among `Console`/`FileSystem`/`Random`/`Env`, discharged by a handler you can swap for a real-time one, is the same move applied to the clock (see the [`Concurrent`](./stdlib/concurrent.md) reference).

The example below is the whole discipline on one page. Two fibers `sleep` and read `now` under `run_clock`, which is installed outside `run_async`; because the scheduler is generic in its residual row, `Clock` tunnels through it to the clock handler, and logical time is the running sum of the sleeps, identical on every run with no real time elapsing.

```prism
{{#include ../examples/clock.pr}}
```

### 7.11 Capability-Based Sandboxing {#capability-based-sandboxing}

Because a function's row records exactly which capabilities it exercises and a handler is what discharges a capability, a `handle` block that installs a restricted set of handlers is a sandbox: a sub-computation it runs can perform only the operations those handlers answer. A function given no `Async` handler in scope cannot spawn a fiber; a function whose row lacks `FileSystem` cannot read a file; a computation run under a world handler that stubs `read_file` to a fixed value cannot reach the real filesystem no matter what it calls, because the only interpreter for that operation in scope is the stub. Anything the sandbox does not discharge is not ambient background authority it might reach anyway, it is a label left in the row that some enclosing handler must still answer, and if none does the program does not type. This is object-capability security recovered from the effect row at no additional cost: authority is precisely the set of handlers in scope, it is delegated by passing a thunk into a handler rather than by granting an ambient permission, and it is attenuated by nesting a sub-computation inside a narrower handler that intercepts or denies operations before any outer one sees them. Concurrency is one capability among the rest rather than a privileged subsystem, so the same `handle` that sandboxes IO sandboxes spawning: a scheduler is just the handler that answers `Async`, and code with no such handler in scope is sequential by construction. The mechanism is exactly the effect handlers already described ([capability effects](#capability-effects-and-io), [effect polymorphism](#effect-polymorphism)); this section only names the security reading that the rows already justify.

Below, `untrusted` reads files, but `sandbox` discharges its `FileSystem` capability with stub handlers, so it cannot reach the real filesystem however it branches; `sandbox` stays polymorphic in the other effects `e`, constraining only the one capability it names.

```prism
{{#include ../examples/sandbox.pr}}
```

### 7.12 Record and Replay {#record-and-replay}

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

### 7.13 Streams {#streams}

Streams are the prelude's data-processing combinators, built on a single `Emit(a)` effect rather than on intermediate collections. A _producer_ performs `Emit` once per element (`srange`, `sof`); a _transformer_ handles a producer's emissions and re-emits the survivors (`smap`, `skeep`, `stake`); and a _consumer_ handles `Emit` by folding every emission into a result (`sfold`, `ssum`, `scollect`). A pipeline is the consumer wrapped around the transformers wrapped around the producer, one handler stack over one producer loop.

Because emission is an effect the consumer discharges, a pipeline _fuses_: `srange(1, 1000).smap(square).skeep(even).stake(5).ssum()` runs as one loop that allocates neither an intermediate list nor a cell per element, the state-threading path of [effect lowering](./compiler.md#effect-lowering). A transformer that stops early, like `stake`, drops the producer's continuation, so the source halts at once. Comprehensions and the statement `for` desugar to these combinators ([comprehensions](#comprehensions)) and fuse the same way.

The push model above fuses but is single-source: a consumer drives one producer. For the combinators that need to advance two sources in step, `zip`, `interleave`, `window`, the [`Sequence`](./stdlib/sequence.md) module (`import Sequence as Seq`) offers the dual, a _pull_ sequence built on an explicit step co-structure `Step(a) = SDone | SMore(a, () -> Step(a))` where a sequence is a thunk the consumer pulls one element at a time. It carries the full combinator vocabulary (`map`, `filter`, `take`, `flat_map`, `zip_with`, `scan`, `chunk`, and the rest) over a value the caller holds and passes around, which the effect-emission producer, being a running loop rather than a value, cannot be. The two are complementary: reach for the fusing prelude streams when one pipeline consumes one source, and for `Sequence` when a sequence must be named, stored, or advanced alongside another.

```prism
{{#include ../examples/streams.pr}}
```

### 7.14 Incremental Computation {#incremental-computation}

The `Incr` stdlib module (`import Incr`) is self-adjusting computation as a handler: a program builds a demand graph of source nodes and derivations, and re-reading the graph after a change recomputes only the part a change can reach. `input(v)` creates a mutable source, `get(n)` reads a node (recording the read as a dependency of whatever derivation is running), `set(n, v)` updates a source, and `memo(thunk)` wraps a derivation whose value is cached and re-demanded rather than recomputed blindly. `run_incr(action)` discharges the effect, running `action` as the root observer of a fresh graph; the ambient row of effects the derivations perform flows out unchanged, exactly as `run_async` passes a fiber's row through.

The contract that makes it incremental is _early cutoff_: after a `set`, re-reading a node re-demands exactly the affected cone, and a derivation whose recomputed value is unchanged does not disturb its dependents. "Unchanged" is an exact content-hash comparison over the serialized value, the same blake3 digest that content-addresses code ([content-addressed core](./compiler.md#content-addressed-core)), not a user-written equality, so a derivation that recomputes to the same answer halts propagation with no dirty-bit bookkeeping, and a `set` to a value a source already holds is a no-op.

`run_incr_durable(path, tag, action)` persists the memo table to a snapshot so a later run warms from it rather than recomputing from scratch. A warm run's output is byte-identical to a cold one, and a missing, corrupt, or foreign-tagged snapshot silently cold-starts rather than yielding a wrong answer, so the snapshot changes only cost, never result. Because warming a derivation skips its thunk, a durable derivation must be pure up to `Fail` (a thunk that printed or drew randomness would change the output if skipped), and only the derivations built before the first input-dependent read are warmed. The worked example is [`examples/leaderboard.pr`](https://github.com/sdiehl/prism/blob/main/examples/leaderboard.pr).

`run_incr_durable_replay(path, tag, action)` lifts the purity restriction for the one effect a skipped thunk can still honor: output. It records each memo's emitted output beside its cached result and _replays_ that output on a warm hit, so a derivation that prints when it fires is warmed from the snapshot without running its thunk yet reproduces the recorded lines byte-for-byte. A second run therefore fires no memo, does no work, and still prints exactly what the first run printed, effects and all, extending the "snapshot changes cost, never result" guarantee to effectful memos rather than only pure ones (the action's row is `! {Incr, Output, Fail | e}`). The worked example is [`examples/incr_trace.pr`](https://github.com/sdiehl/prism/blob/main/examples/incr_trace.pr), which prints identically whether run cold or warm.

### 7.15 Suspend and Resume {#suspend-and-resume}

Record and replay reproduces a run from its start; suspend and resume is the stronger checkpoint the previous section points at, a paused computation that is itself a value. `prism suspend FILE --at N -o snapshot.kont` runs a program, pauses it after `N` machine steps, and writes the whole live continuation, its pending work, its call stack, and every value bound along the way, to a file as a _kont envelope_. `prism resume FILE snapshot.kont` reads that file and runs the continuation to completion. The suspending run's output followed by the resuming run's output is byte-identical to one uninterrupted run: suspend is a cut, not a change, another corollary of the determinism contract. Because a machine step is a pure state transition, a given step count pauses at a deterministic point, so a snapshot is reproducible.

```prism
fn count(i, last) =
  if i > last then ()
  else
    println("step {i}: {i} squared is {i * i}")
    count(i + 1, last)

fn main() = count(1, 6)
```

The recursion is an ordinary tail call carrying `i` forward; nothing in the program knows it can be interrupted. Suspend it partway and the live call (the pending `count`, the bound `i`, the frame that will print next) is written to a file; resume it elsewhere and the count continues from where it stopped:

```text
$ prism suspend count.pr --at 120 -o half.kont
step 1: 1 squared is 1
step 2: 2 squared is 4
step 3: 3 squared is 9
$ prism resume count.pr half.kont
step 4: 4 squared is 16
step 5: 5 squared is 25
step 6: 6 squared is 36
```

Concatenate the two outputs and you have exactly `prism run count.pr`. The resuming process never re-ran the first three steps; it decoded the frozen call stack, checked that `count.pr` still hashes to the bundle the snapshot was captured in, and stepped the machine forward from the cut.

The envelope is a self-describing wire frame in the discipline the store's definitions use ([content-addressed core](./compiler.md#content-addressed-core)): a scheme tag, the `kont` kind, then a _bundle digest_, the program's namespace root, checked before the body. `resume` re-derives that digest from its own copy of the program and refuses a snapshot whose digest does not match, so a continuation only resumes against the code it was captured in; this is code identity checked by hash, not by name or trust. Decoding is total: a truncated, reordered, or otherwise hostile envelope is rejected with a diagnostic rather than trusted, on the same discipline (byte-capped lengths, digest before body, range-checked references, a bounded reconstruction, trailing-byte rejection) as every other Prism wire. Code inside the envelope resolves reference-or-inline: a call to a top-level definition rides as its name and resolves against the resumer's function table, which the matching bundle digest guarantees is identical, so same-bundle wire cost is the captured state alone; an inline closure body travels inline.

The suspendable subset is explicit. A value that cannot cross the boundary, a graph nested past the suspendable depth (the fingerprint of a cycle or a native resource a future release might hold), is refused at suspend time naming what could not be written, never encoded into a snapshot that would fail on the far side. This release's envelope is the dynamic one: a runtime-value encoding over the interpreter's representation, serialized and resumed by the tree-walking interpreter, including that interpreter compiled to WebAssembly, so a running program can move between two independent hosts over a channel and each re-verifies the bundle by hash before resuming. Two fences are deliberate and stated: native code cannot yet be suspended (it needs a compiled reverse map from function pointers to definition hashes), and the typed, compile-time-checked mobile-value surface is future work; the dynamic envelope is the wire underneath it.

Mobility is therefore a consequence of the same two invariants the rest of the runtime already uses: continuations are reified values, and code identity is content-addressed. Teleporting a computation means sending the `kont` envelope, not inventing a separate remote-call mechanism: the receiver decodes the suspended continuation, recomputes the namespace root for its local program, and resumes only if that digest matches the envelope. What crosses the wire is the pending computation and captured state; what authorizes it is the hash of the code it was captured in.

That keeps the mobility story aligned with replay rather than distribution magic. A suspended program resumed on another host must produce the same suffix as the original uninterrupted run, because the step it resumes from and the code it resumes into are both checked facts. Content addressing names the definitions, the `kont` envelope names the live continuation over those definitions, and deterministic replay is the observable contract tying them together.

## 8. Expressions {#expressions}

The expression grammar is in the [surface grammar](#surface-grammar) and the effect and failure forms are in [effects and handlers](#effects-and-handlers); the forms below are those the grammar alone does not settle.

### 8.1 Method Calls {#method-calls}

A method call `e.m(args)` is uniform-function-call syntax (UFCS): pure sugar for `m(e, args)`, with the receiver `e` supplied as the first argument. Prism has no methods, only top-level functions; the dot is notation, not dispatch, so any function reads as a method and calls chain left to right (`e.f().g()` is `g(f(e))`). Extra arguments follow the receiver: `a.add(b)` is `add(a, b)`. A trailing block argument, `e.m(args) fn (x) { body }`, appends the lambda as the last argument; this is how the stream consumers in [streams.pr](./compiler.md#effect-lowering) chain. Field access is `e.field`, and the two compose, `e.field.m(args)` being `m(e.field, args)`.

```prism
{{#include ../examples/ufcs.pr}}
```

### 8.2 Comprehensions {#comprehensions}

A comprehension `[ e for x in s, q, ... ]` collects `e` for each element; a qualifier `q` is a guard `if g` or a binder `let y = e`. A guard is evaluated in a failure context, so an element is pruned both when `g` is false and when computing `g` fails: a failable accessor such as `at_list` (a prelude lookup from [the standard prelude](#the-standard-prelude)) past the end of a list prunes that element rather than aborting. The statement form `for x in s, q, ... do body` runs `body` per survivor. Both desugar to the prelude's stream combinators (the `Emit` effect of [the standard prelude](#the-standard-prelude)), so they fuse without building an intermediate list.

```prism
{{#include ../examples/comprehension.pr}}
```

### 8.3 Records {#record-expressions}

Record construction `C { f = e, ... }`, functional update `C { ..base, f = e }`, and nested path update `{ base | a.b = e, ... }` build and modify the [record types](#record-types); each is an in-place write on a uniquely owned value. The `deriving (Lens)` getters and setters compose with them for deeper access. A path generalizes past nested fields to traversals, indices, prisms, filters, and a read form ([optic paths](#optic-paths)).

```prism
{{#include ../examples/lens_derive.pr}}
```

### 8.4 Imperative control flow {#imperative-control-flow}

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

### 8.5 Exponentiation {#exponentiation}

`a ^ b` raises `a` to the power `b`. It binds tighter than `*` and than unary minus (`-2 ^ 2` is `-(2 ^ 2)`, the mathematical reading; a negative base needs parentheses, `(-2) ^ 2`), and is right-associative, so `2 ^ 3 ^ 2` is `2 ^ (3 ^ 2)`. It is the method of the `Pow` class ([the standard prelude](#the-standard-prelude)) with `Int` and `Float` instances, so it desugars to `pow(a, b)`: over `Int` it is bignum-correct (the instance multiplies), over `Float` it is a `pow_float` call. A mixed `Int ^ Float` is a type error, resolved by an explicit `to_float`, exactly as `2 + 3.0` is (Prism never coerces between `Int` and `Float` implicitly).

An `Int` exponent may be negative: `a ^ b` with `b < 0` is defined as `1 / a ^ (-b)` under the language's one truncating division rule ([integer arithmetic](#integer-arithmetic)). So `2 ^ -1` is `0`, `1 ^ -5` is `1`, `(-1) ^ -5` is `-1`, and `0 ^ -1` faults as the division by zero it literally is. `Float` exponents follow IEEE `pow`, so `2.0 ^ -1.0` is `0.5`.

### 8.6 Indexing {#indexing}

`a[i]` reads, `a[i] := v` writes, and `a[i] += e` updates an indexed container. The form is dispatched on the receiver's type (not a class, so no inference change): `Array` is indexed by `Int`, `HashMap` by `String`, `String` by `Int` (yielding the byte), and `List` by `Int`. `Array`, `HashMap`, and `List` are writable; `String` is read-only. `Array` and `HashMap` rewrite the cell in place (FBIP); a `List` write is the functional `list_set`, rebuilding the spine.

A read is _failable_: a missing index or key performs the `Fail` effect ([errors and failure](#errors-and-failure)), so `a[i]` has type `Elem ! {Fail}` and the partiality surfaces in the row rather than in an `Option` wrapper. It therefore composes with `??`, `?.`, `default`, and the rest of the failure axis: `a[i] ?? d` supplies a default, and the counter idiom is `m[k] := (m[k] ?? 0) + 1`, honest that an absent key starts at zero. A plain write `a[i] := v` is total; `a[i] += e` reads first, so it is `! {Fail}`. Writes rebind the underlying `var` and rewrite the cell in place when it is uniquely owned (FBIP, [declarations and programs](#declarations-and-programs)); nested `grid[i][j] := v` composes the same way. `a[i] := v` requires `a` to be an assignable `var`.

### 8.7 Optic Paths {#optic-paths}

Prism has no optic library: no `Lens` type, no `over`/`set`/`toListOf` to compose, no profunctor encodings. It has one rule instead. Between the `|` and the operator of a record update ([record expressions](#record-expressions)), or inside `s.[ ... ]`, a **path** is a sequence of steps read left to right. The path _is_ the optic, spelled at the use site rather than reified as a value. Every form is sugar over `map`/`with`/`match`, so in-place reuse and fusion come for free and nothing new reaches the core: this is the language's "effects instead of monads" stance applied to optics, paths instead of optic combinators.

A step is one of:

| Step              | Meaning                                                |
| ----------------- | ------------------------------------------------------ |
| `.field`          | descend into a record field                            |
| `each`            | traverse every element of a functor (lowers to `fmap`) |
| `[i]`             | focus one element of a list or array, by index         |
| `?Ctor`           | focus through a sum constructor; others pass through   |
| `(steps where p)` | keep only the foci satisfying the predicate `p`        |

A path is closed by one of three operations:

| Form         | Operation                                         |
| ------------ | ------------------------------------------------- |
| `path = v`   | **set** the focus to `v`                          |
| `path ~ f`   | **modify** the focus, applying `f`                |
| `s.[ path ]` | **read** every focus the path selects into a list |

`each` is a reserved keyword; every other step reuses existing tokens.

Each form lowers to ordinary code. The examples below are written over two types:

```text
type Player = Player { name: String, pos: Vec2, hp: Int, bag: List(Int) }
type Shape  = Circle { radius: Int } | Square { side: Int }
```

A field sets through the derived setter, and nests through the setter of each enclosing field:

```text
{ p  | hp = 100 }     =>  with_hp(p, 100)
{ pl | pos.x = 30 }   =>  with_pos(pl, with_x(pl.pos, 30))
```

Modify reads the focus, applies the function, and writes the result back:

```text
{ p | hp ~ heal }     =>  with_hp(p, heal(p.hp))
```

`each` fans out over any functor (lowering to `fmap`) and composes with further descent:

```text
{ players | each.hp ~ heal }      =>  fmap(\p -> with_hp(p, heal(p.hp)), players)
{ world | party.each.pos.x = 0 }
```

An index focuses one element, lowering through `list_set` (or in-place `array_set`); an out-of-range index leaves the container unchanged:

```text
{ world | party[0].hp = 100 }     =>  element 0 of party, via list_set / array_set
```

A prism rebuilds a matched constructor and passes the others through, the prism law for update:

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

The read form `s.[ path ]` collects every focus a path selects into a list, the read twin of the update:

```text
players.[each.hp]                  =>  the list of every player's hp
world.[party.each.bag.each.count]  =>  each flat-maps, so nested traversals flatten
```

A `?Ctor` step previews zero or one focus, and a single-focus path yields a one-element list.

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

A `pattern N(x) for T = view ... make ...` declaration defines a bidirectional pattern synonym: in match position it runs `view` and succeeds when that returns `Some` (the present case of `Option`, from [the standard prelude](#the-standard-prelude)); in expression position it runs `make`. Here `view` and `make` are contextual keywords, significant only inside a `pattern` declaration. A synonym with both halves is a _prism_ (a composable view-and-build pair); one with only `view` is a view pattern. The `for` target may also name a class rather than a type, with the view a method of that class: `pattern First(n) for Peek = view peek` matches a value of any type with a `Peek` instance, dispatching `peek` through the dictionary at each match site, so one synonym destructures every instance.

```prism
{{#include ../examples/pattern_syn_sugar.pr}}
```

## 10. Declarations and Programs {#declarations-and-programs}

A function is declared with `fn`; a parameter may carry a type annotation, a default value `:= e`, or the `borrow` modifier, which lets a pure function read a parameter without taking ownership of it. A return annotation is written `: !{R} T` for result type `T` and effect row `R`, `: ! T` for an explicit empty row, or `: T` to leave the row inferred. A parameter with a default may be omitted, and any argument may be passed by name as `f(p := e)`, in any order and mixed with positional arguments; the call is rewritten to positional form, filling omitted defaults. Defaults and named arguments are honored on top-level functions. A top-level `let` is a constant: its references are inlined. A `where` block attaches non-recursive, lexically scoped definitions to a function body.

```prism
{{#include ../examples/named_args.pr}}
```

```prism
{{#include ../examples/borrow.pr}}
```

A function may be annotated `fip` or `fbip` to assert the fully-in-place discipline of [Lorenzen et al. (2023)](bibliography.md#lorenzen-fp2-2023). `fbip` proves the body allocates no fresh cell and calls only annotated, allocation-free functions. `fip` additionally proves linearity (each owned, non-immediate binding is consumed at most once) and bounded stack (each recursive call in the group is a tail call or a single tail-modulo-cons or tail-modulo-add). These are static checks that reject a non-conforming body; the mechanism is described under [reference counting and FBIP reuse](./compiler.md#reference-counting-and-fbip-reuse). A function may additionally, or independently, be annotated `replayable` ([record and replay](#record-and-replay)), which certifies it performs only the recordable capability effects and so is reproducible from a recorded trace; `replayable` is orthogonal to `fip`/`fbip` and may combine with either.

```prism
{{#include ../examples/fip_list.pr}}
```

### 10.1 Zero-Allocation Blocks {#zero-allocation-blocks}

The zero-allocation guarantee has a postfix spelling, `without alloc`, written after the return annotation. It reads allocation as a capability the function revokes, and carries the same check as `fbip` (the body and its whole call tree allocate no fresh cell, calling only allocation-free functions), without the linearity and bounded-stack requirements `fip` adds. It composes with an effect row and with `given` constraints (`: !{IO} T without alloc`), and interoperates with the keyword forms: a `without alloc` function may call `fip`, `fbip`, or `without alloc` functions.

The same guarantee applies to a region rather than a whole function through the block form `without alloc <block>`, which asserts that the block allocates no fresh cell. Desugar lifts the block to a synthetic top-level `without alloc` function capturing the block's free locals and replaces it with a call ([desugaring](compiler.md#desugaring)), so the identical check covers exactly the region; a `return`, `break`, or `var` inside the block behaves as if written inline, since its control or state effect tunnels out to the enclosing handler. `gcd` below certifies a whole function; `horner` certifies only the expression after its `let`.

```prism
{{#include ../examples/no_alloc.pr}}
```

The same certificate has a terser second spelling, `\ alloc`, read as the result type with the `alloc` usage subtracted. It is a pure synonym, checked identically; the formatter canonicalizes it to `without alloc`.

```prism
fn scale(x : Int, k : Int) : Int \ alloc = k * x

fn area(w : Int, h : Int) : Int \ alloc = scale(w, h)
```

`borrow`, `fip`/`fbip`, and `without alloc`/`\ alloc` form one family, distinct from the effect row. The effect row records what a function _does_ to the world (which operations it performs); these annotations record how a function _uses_ its values (whether it retains a borrowed argument, allocates a fresh cell, or consumes each owned value once). The two axes are orthogonal and compose freely: a function can be `without alloc` while performing `IO`, and `replayable` while being `fip`. Allocation appears on both axes for different purposes: as a usage property here, checked and forbidden by `without alloc`, and, in a future arena facility, as an ordinary effect a handler interprets to service allocation out of a region.

### 10.2 Stable Blocks {#stable-blocks}

A serialized value is a contract across time: bytes written by yesterday's binary are read by today's, so a persisted format must never drift silently with the in-memory type. A `stable` block declares a type's frozen wire history inline, on the type itself. Each entry is a _rung_: a record layout named `V1`, `V2`, and so on, where a later rung may extend its predecessor with `..Vn` and new fields. The block's last rung is the current one, and the bare type name (`Save` below) refers to it; an earlier rung is a real type of its own, named `Save.V1`.

```prism
{{#include ../examples/stable.pr}}
```

The inline default (`fog: Int = 30`) is the entire cost of an additive change: from it the compiler generates the total `upgrade_Save_V1_V2` (fill the new field with its default) and the honest `downgrade_Save_V2_V1`, which drops the field and returns the lowered value together with a `Loss` naming what could not be carried down. A change the compiler cannot guess, such as a field changing type, is written by hand inside the block as an `upgrade Vn -> Vm = ...` or `downgrade Vm -> Vn = ... drop_loss(f)` converter. Only adjacent converters ever exist; spanning several versions composes along the ladder, so N versions cost N-1 converters, never a pairwise matrix. Upgrade after downgrade is the identity on the safe subset, a law emitted as a property test over the derived generators rather than left to review.

A rung marked `frozen "<digest>"` is sealed: the digest is the rung's structural shape digest, the same construction that content-addresses every datatype ([content-addressed core](compiler.md#content-addressed-core)). Editing a sealed rung in place moves the digest and the program stops compiling, with the error naming the rung and the remedy: add a new rung instead of editing a shipped one. A rung that never shipped is reseated with `prism wire --accept <file>`, which recomputes and rewrites its digest in place, loudly. The block also derives the type's `Serialize` against the current rung, and the generated ladder functions lift a value between rungs explicitly, so an old value is carried up through its converters rather than re-parsed by hand; a frame's version rides its envelope, and dispatching an old frame through the ladder automatically is the wire library's job as that layer grows. The codec itself, the byte-level frame with its total decoder, is the `Wire` library, an opt-in import ([the standard prelude](#the-standard-prelude)): a program that never persists a value pays for none of this.

### 10.3 Deprecation {#deprecation}

A declaration is marked superseded with a `deprecated` annotation line directly above it, carrying the suggested replacement as a string:

```prism,ignore
deprecated "use `insert`, which also returns the displaced value"
pub fn add(m, k, v) = insert(m, k, v)
```

The annotation attaches to the declaration that follows it (a `fn`, `type`, `class`, `effect`, or any other named declaration) and records the suggestion; it is not itself a declaration. A `deprecated` line with no declaration after it, or two in a row, is a syntax error. `deprecated` is a contextual word, not a reserved one, so a program may still bind the name.

A _use_ of a deprecated definition compiles, with a warning that names the definition, the suggestion, and the use site. It is only a warning: behavior is unchanged, so a deprecation never breaks a build or alters what a program computes (a determinism corollary: the warning is a diagnostic, not a semantic). A definition's own body may use it without warning; only references from other definitions are reported, and only in the user's own source, so a deprecation inside an imported library does not warn at the library's internal call sites.

The compiler applies the same mechanism to two families it supersedes but has no declaration to annotate: the float dot-operators `+.` `-.` `*.` `/.`, now that the plain operators are lane-polymorphic ([numeric arithmetic](#floating-point)), each warn with the plain spelling; and the fixed-width arithmetic builtins that duplicate an operator (`i64_add`, `u64_mul`, and the rest of the `+ - * / %` set) warn with that operator. The bitwise, shift, comparison, and conversion builtins have no operator replacement and are not deprecated.

The policy is one release wide: a name deprecated in a release keeps working, with the warning, for that release, and is removed in the next. This is what lets the standard library (Section 12) evolve without a flag day, and what "1.0" freezes: Base's surface may only ever grow, or shrink through one full deprecation window, never break in place.

## 11. Modules {#modules}

A file is a module and a directory is a namespace prefix: `import Data.Map` loads `Data/Map.pr`. A project is a `prism.toml` manifest plus a source tree, resolved from the project root. A single-file program is one module.

`import M` brings `M`'s exports into scope under qualified names; `import M (a, b)` also brings `a` and `b` into bare scope; `import M as N` adds the alias `N`. The `pub` modifier on a declaration makes it visible to importers; `pub import M (x)` re-exports `x` through the importing module. An `opaque type` exports its name but not its constructors.

{{#tabs }}

{{#tab name="src/Geometry.pr" }}

```prism
pub fn area(w, h) = w * h   -- exported

fn clamp(x) = if x < 0 then 0 else x   -- private to the module
```

{{#endtab }}

{{#tab name="src/main.pr" }}

```prism,ignore
import Geometry (area)

fn main() = println(area(4, 5))
```

{{#endtab }}

{{#endtabs }}

Name resolution rewrites every top-level definition to a canonical, module-qualified symbol (an export as `Data.Map.insert`, a private as the unforgeable, source-unwritable `Data.Map@helper`) and merges all modules into one program keyed by those symbols. Because identity is the canonical symbol, two modules may export the same short name and coexist. This is namespacing, not separate compilation: there are no per-module artifacts, and changing one module recompiles the whole program. Identifying each definition by a content hash of its core rather than by its name is a direction the compiler is prototyping ([content-addressed core](./compiler.md#content-addressed-core)); it would make a definition's identity independent of its name and recompilation incremental over only what actually changed.

Instances are global, but each records its defining module. An _orphan_ instance (defined apart from both its class and its head type) and instances that overlap across modules are reported as warnings; an ambiguity names each candidate's module.

### 11.1 Projects {#projects}

A single `.pr` file compiles on its own (`prism file.pr`), resolving imports relative to its own directory. A multi-file program is a _project_: a `prism.toml` manifest at the root plus a `src/` tree, where dotted module paths resolve from the source root rather than from the entry file's location. The smallest manifest names the package and its entry point:

```toml
[package]
name = "myapp"

[bin]
entry = "src/main.pr"
```

`prism build` compiles the nearest enclosing project to a native binary under a `target/` directory at the project root (rustc-style), named after the package; `prism run <path>` interprets it instead, and `prism clean` removes `target/`. A single file is still built with a bare `prism file.pr`. The manifest keys are:

| Key              | Section     | Required           | Meaning                                                                             |
| ---------------- | ----------- | ------------------ | ----------------------------------------------------------------------------------- |
| `name`           | `[package]` | yes                | package name; also the default binary name                                          |
| `entry`          | `[bin]`     | yes                | the entry `.pr` file, relative to the project root                                  |
| `src`            | `[package]` | no (default `src`) | the module root that dotted `import` paths resolve from                             |
| `prelude`        | `[package]` | no                 | a `.pr` file whose contents replace the built-in prelude for this project           |
| `[dependencies]` | table       | no                 | path dependencies, each `name = { path = "..." }` (or the shorthand `name = "..."`) |

A path dependency's modules import under their own dotted paths, so a `geometry = { path = "../geometry" }` entry makes that project's `Geometry` module reachable as `import Geometry`:

```toml
[package]
name = "myapp"

[bin]
entry = "src/main.pr"

[dependencies]
geometry = { path = "../geometry" }
```

## 12. The Standard Prelude {#the-standard-prelude}

The library ships in two rings.

**Base** is the always-on prelude, in scope in every module without an import: the core types (`Option`, `Result`, `List`, tuples), the class tower (`Eq`, `Ord`, `Show`, `Num`, `Div`, `Hash`, and the `Functor`/`Foldable`/`Applicative`/`Monad`/`Traversable` structures), the string and character basics, the effect vocabulary (`Exn`, `Fail`, and the capability effects), and the core combinators. It is ordinary Prism, not built-in, assembled from modules under `lib/std`: the prelude opens a fixed set of `Data.*` modules with `import M (..)` so their names are unqualified everywhere. Base is small and its surface is frozen: at 1.0 it may only grow, or shrink through one full [deprecation](#deprecation) window, never break in place. The exact surface is pinned by a committed golden, so an accidental addition fails a test in review rather than silently widening the frozen ring.

**Std** is everything else the compiler ships (`Replay`, `Concurrent`, `Incr`, `Wire`, `Time`, `Json`, `Sequence`, and the rest), reached only through an explicit `import`. Std is distributed as a pinned content-addressed root through the store: "the standard library" is a single hash, the fold `prism dump stdlib-hash` reports, over every Std definition's behavior hash and every type, class, and instance digest ([content-addressed core](compiler.md#content-addressed-core)). A lockfile records that root in a `std` line, and a build recomputes the embedded stdlib's root and compares: a pin that matches is on the same standard library the lock was resolved against; a pin that differs is named exactly, both roots reported, so two programs pinning different Std roots are told apart the way two dependency hashes are rather than silently coexisting. Because the root is content-addressed, everything reachable from it is the zero-cost baseline both ends of a transfer assume, and never travels.

Beyond Std are first-party packages resolved through the store (`prism.toml` dependencies): blessed and versioned, but not frozen with the language.

The rings and the store bound how far a Std pin carries today. The standard library is still embedded in the compiler binary, so a lockfile's `std` pin detects that a build's Std differs from the one it was resolved against, but it cannot yet select a different Std against that pin: a full flag-day-free evolution, where two builds resolve two different Std roots from the store rather than from the compiler, waits on serving the prelude itself from the store. The pin is the seam; closing it is future work.

This document does not restate the API. The [Standard Library](./stdlib/index.md) part of this book is the per-declaration reference for every prelude and stdlib module, generated from the source by `prism docs` and regenerated against the typechecker so it never drifts.
