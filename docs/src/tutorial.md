# Prism Tutorial

This is the gentle introduction to Prism. It assumes you can already read a little Python: variables, functions, lists, and `if`, but no functional-programming experience beyond a desire to Taste the Rainbow.

Prism's lineage runs through Haskell and OCaml, with Koka's effect rows and Unison's content-addressed codebase as especially strong inspirations. Imagine taking continuation-passing style and row polymorphism a little further, then giving the result a reasonably efficient native backend. That is the essence of the compiler. It is meant to be fun to hack on rather than a practical replacement for your day job: a compiler for people who enjoy writing compilers, where content-addressed bootstrapping is part of the playground.

Prism takes that inheritance in its own direction:

- evaluation is strict like OCaml, rather than lazy like Haskell;
- side effects are direct-style algebraic operations tracked in inferred **effect rows**, rather than being hidden or sequenced through a privileged monad;
- handlers can interpret an effect locally, after which it disappears from the function's type;
- definitions are content-addressed by hashes of canonical compiler forms, packages and Std are pinned by Merkle roots, and builds can carry machine-checkable lineage;
- memory uses deterministic reference counting and in-place reuse rather than a tracing garbage collector;
- modules are files, imports, and packages managed by Prism's package manager; and
- there is deliberately no do-notation, macro system, or user-defined operator language.

The result is an impure functional language that tries to make impurity accountable. Pure code is deterministic. Contact with the outside world crosses a named, typed effect boundary that can be handled, recorded, replayed, or audited. Definitions receive stable identities from their canonical Core behavior, so whitespace and bound-variable spelling do not give the same behavior a new identity.

One honest warning before we begin: Prism is an active language project, not a production ecosystem. Explore it, steal ideas from it, and expect a few sharp experimental edges as it evolves.

With that suitably irresponsible disclaimer out of the way, let us begin.

**Further reading:** [language goals](./spec.md#goal), [compiler design principles](./compiler.md#design-principles), and [content-addressed Core](./compiler.md#content-addressed-core).

## Setup

The quickest route is the browser-based [Playground](https://sdiehl.github.io/prism/play/), which needs no installation. To work locally, Prism's prebuilt native compiler supports Apple Silicon macOS and glibc Linux on x86-64 or AArch64. It needs LLVM 22 at runtime:

```shell
# macOS
brew install llvm@22

# Debian or Ubuntu
curl -fsSL https://apt.llvm.org/llvm.sh | sudo bash -s 22
```

Then run the verified release installer. It installs `prism` under `~/.local/bin` by default and uses Nix automatically when Nix is available:

```shell
curl --proto '=https' --tlsv1.2 -fsSL https://sdiehl.github.io/prism/install.sh | sh
prism --version
```

Homebrew users may instead run `brew install sdiehl/prism/prism`. The repository [README](https://github.com/sdiehl/prism#install) also covers Nix, containers, Linux packages, and building from source.

**Further reading:** [the command-line interface](./compiler.md#command-line-interface), [the interactive shell](./compiler.md#the-interactive-shell), and [compiler environment variables](./compiler.md#environment-variables).

## Your First Project

`prism pkg init` interactively asks for a package and directory name, then creates the minimal project:

```shell
prism pkg init
cd rainbow
```

The resulting layout is intentionally small:

```text
rainbow/
├── prism.toml
└── src/
    └── main.pr
```

`prism.toml` tells the project tools what the package is called and which file contains its entry point:

```toml
[package]
name = "rainbow"

[bin]
entry = "src/main.pr"
```

Put this in `src/main.pr`. The worked examples stay focused on Prism. When a comparison genuinely clarifies a design choice, it is explained in prose rather than repeated as three more programs.

{{#tabs }}

{{#tab name="Prism" }}

```prism
fn main() =
  println("Prism: Taste the Rainbow!")
```

```output
Prism: Taste the Rainbow!
```

{{#endtab }}

{{#endtabs }}

Then check and run it:

```shell
prism check
prism run .
```

`prism check` type-checks the project without running it. `prism run .` interprets the project immediately; a bare `prism run` inside the project builds and runs its native binary under `target/`. `prism build` only builds that binary.

**Further reading:** [projects](./spec.md#projects), [modules](./spec.md#modules), and [the package manager](./compiler.md#package-manager).

## Values, `let`, and Functions

Python uses `def`; Prism uses `fn`. Python assignments can change a name; a Prism `let` gives an immutable name to a value. There is no `return` in the ordinary case: the final expression in a function body is its result.

{{#tabs }}

{{#tab name="Prism" }}

```prism
fn square(n : Int) : Int = n * n

fn main() =
  let answer = square(6) + square(2)
  println(answer)
```

```output
40
```

{{#endtab }}

{{#tab name="Python" }}

```python
def square(n: int) -> int:
    return n * n


answer = square(6) + square(2)
print(answer)
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
square :: Int -> Int
square n = n * n

main :: IO ()
main = print (square 6 + square 2)
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
let square (n : int) : int = n * n

let () = Printf.printf "%d\n" (square 6 + square 2)
```

{{#endtab }}

{{#endtabs }}

The annotations say that `square` accepts an `Int` and returns an `Int`. Prism could infer both here, but annotations make an API easier to read. The compiler checks them; they are not runtime conversions.

Indentation forms a block, much as it does in Python. Calls still use parentheses, strings still use double quotes, and comments begin with `--`. Most constructs are expressions, so `if` itself produces a value:

{{#tabs }}

{{#tab name="Prism" }}

```prism
fn describe(n : Int) : String =
  if n < 0 then
    "negative"
  elif n == 0 then
    "zero"
  else
    "positive"

fn main() = println(describe(-3))
```

```output
negative
```

{{#endtab }}

{{#tab name="Python" }}

```python
def describe(n: int) -> str:
    if n < 0:
        return "negative"
    elif n == 0:
        return "zero"
    else:
        return "positive"


print(describe(-3))
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
describe :: Int -> String
describe n
  | n < 0 = "negative"
  | n == 0 = "zero"
  | otherwise = "positive"

main :: IO ()
main = putStrLn (describe (-3))
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
let describe n =
  if n < 0 then "negative"
  else if n = 0 then "zero"
  else "positive"

let () = print_endline (describe (-3))
```

{{#endtab }}

{{#endtabs }}

Python needs a `return` in each branch because its `if` is a statement. In Prism, Haskell, and OCaml the conditional is itself the value the function hands back.

**Further reading:** [top-level definitions](./spec.md#top-level-definitions), [`let` statements](./spec.md#let-statements), and [type and effect inference](./compiler.md#type-and-effect-inference).

## Functions Are Values

A functional language lets you pass behavior around like any other value. A lambda is an unnamed function, written `\(arguments) -> expression`. `map` applies one function to every element of a list and returns the new list; it does not mutate the old one.

{{#tabs }}

{{#tab name="Prism" }}

```prism
fn main() =
  let numbers = [1, 2, 3, 4]
  let squares = map(\(n) -> n * n, numbers)
  println(show(squares))
```

```output
[1, 4, 9, 16]
```

{{#endtab }}

{{#tab name="Python" }}

```python
numbers = [1, 2, 3, 4]
squares = list(map(lambda n: n * n, numbers))
print(squares)
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
main :: IO ()
main =
  let numbers = [1, 2, 3, 4] :: [Int]
      squares = map (\n -> n * n) numbers
   in print squares
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
let () =
  let numbers = [ 1; 2; 3; 4 ] in
  let squares = List.map (fun n -> n * n) numbers in
  List.iter (Printf.printf "%d ") squares
```

{{#endtab }}

{{#endtabs }}

If you would write a Python loop whose only job is to transform every element, `map` states that intent directly. Prism also has folds, filters, comprehensions, recursion, and imperative loop syntax, but the useful first habit is to ask what value the whole operation computes.

Here is the small translation dictionary. The rows are the same six ideas in every tab, so a spelling you already know points at the one you do not.

{{#tabs }}

{{#tab name="Prism" }}

| Idea                          | Prism                                 |
| ----------------------------- | ------------------------------------- |
| define a function             | `fn f(x) = ...`                       |
| bind a name                   | `let x = value`                       |
| an anonymous function         | `\(x) -> x + 1`                       |
| transform every element       | `map(f, xs)` or a list comprehension  |
| a value that may be absent    | `Option(a)` with `None` and `Some(a)` |
| something the caller supplies | named effects, shown later            |

{{#endtab }}

{{#tab name="Python" }}

| Idea                          | Python                       |
| ----------------------------- | ---------------------------- |
| define a function             | `def f(x): ...`              |
| bind a name                   | `x = value`                  |
| an anonymous function         | `lambda x: x + 1`            |
| transform every element       | `[f(x) for x in xs]`         |
| a value that may be absent    | `None`, or `Optional[T]`     |
| something the caller supplies | exceptions, or ambient state |

{{#endtab }}

{{#tab name="Haskell" }}

| Idea                          | Haskell                               |
| ----------------------------- | ------------------------------------- |
| define a function             | `f x = ...`                           |
| bind a name                   | `let x = value`                       |
| an anonymous function         | `\x -> x + 1`                         |
| transform every element       | `map f xs` or `[f x \| x <- xs]`      |
| a value that may be absent    | `Maybe a` with `Nothing` and `Just`   |
| something the caller supplies | a monad transformer stack, or a class |

{{#endtab }}

{{#tab name="OCaml" }}

| Idea                          | OCaml                              |
| ----------------------------- | ---------------------------------- |
| define a function             | `let f x = ...`                    |
| bind a name                   | `let x = value`                    |
| an anonymous function         | `fun x -> x + 1`                   |
| transform every element       | `List.map f xs`                    |
| a value that may be absent    | `'a option` with `None` and `Some` |
| something the caller supplies | exceptions, or an effect handler   |

{{#endtab }}

{{#endtabs }}

**Further reading:** [lambdas](./spec.md#lambdas), [function composition](./spec.md#function-composition), and [expressions and method-call syntax](./spec.md#expressions).

## Data Has Shapes

An algebraic data type lists every shape a value may have. A `match` must then deal with those shapes. This replaces many string tags, nullable fields, and "should never happen" branches with a checked vocabulary.

{{#tabs }}

{{#tab name="Prism" }}

```prism
type Weather
  = Sunny
  | Rainy(Int)

fn advice(weather : Weather) : String =
  match weather of
    Sunny => "leave the umbrella at home"
    Rainy(mm) =>
      if mm > 10 then
        "take the serious umbrella"
      else
        "take the small umbrella"

fn main() =
  println(advice(Sunny))
  println(advice(Rainy(12)))
```

```output
leave the umbrella at home
take the serious umbrella
```

{{#endtab }}

{{#tab name="Python" }}

```python
from dataclasses import dataclass


@dataclass
class Sunny:
    pass


@dataclass
class Rainy:
    mm: int


def advice(weather) -> str:
    match weather:
        case Sunny():
            return "leave the umbrella at home"
        case Rainy(mm):
            return "take the serious umbrella" if mm > 10 else "take the small umbrella"


print(advice(Sunny()))
print(advice(Rainy(12)))
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
data Weather = Sunny | Rainy Int

advice :: Weather -> String
advice Sunny = "leave the umbrella at home"
advice (Rainy mm)
  | mm > 10 = "take the serious umbrella"
  | otherwise = "take the small umbrella"

main :: IO ()
main = do
  putStrLn (advice Sunny)
  putStrLn (advice (Rainy 12))
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
type weather = Sunny | Rainy of int

let advice = function
  | Sunny -> "leave the umbrella at home"
  | Rainy mm ->
      if mm > 10 then "take the serious umbrella" else "take the small umbrella"

let () =
  print_endline (advice Sunny);
  print_endline (advice (Rainy 12))
```

{{#endtab }}

{{#endtabs }}

Python needs two classes and gets no exhaustiveness check: forgetting a case simply returns `None`. Haskell and OCaml agree with Prism that this is one type with two shapes, and their compilers warn about a missing branch too.

`Rainy` carries an `Int`; the `Rainy(mm)` pattern both proves that this is the rainy case and gives its payload the name `mm`. Adding another constructor makes an incomplete `match` a compiler error, so changing the data model points to the code that must change with it.

`Option(a)` is the standard version of this idea for a value that may be absent: it is either `None` or `Some(value)`. Absence is therefore visible in the type instead of hiding behind a Python-style `None` that any reference might contain.

**Further reading:** [algebraic data types](./spec.md#algebraic-data-types), [patterns and exhaustiveness](./spec.md#patterns), and [pattern-match compilation](./compiler.md#pattern-match-compilation).

## Effects Are in the Type

A normal type tells you what value a function returns. An effect row, written after `!`, also tells you which operations the function may perform. Define a tiny effect for asking a question:

{{#tabs }}

{{#tab name="Prism" }}

```prism
effect Ask
  ask_word() : String

fn slogan() : String ! {Ask} =
  "Continuations are {ask_word()}!"

fn main() =
  let message =
    handle slogan() with
      ask_word() resume k => k("funz")
      return value => value
  println(message)
```

```output
Continuations are funz!
```

{{#endtab }}

{{#tab name="Python" }}

```python
ask_word = "funz"  # ambient state; slogan's signature does not mention it


def slogan() -> str:
    return f"Continuations are {ask_word}!"


print(slogan())
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
import Control.Monad.Reader

slogan :: Reader String String
slogan = do
  w <- ask
  pure ("Continuations are " ++ w ++ "!")

main :: IO ()
main = putStrLn (runReader slogan "funz")
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
open Effect
open Effect.Deep

type _ Effect.t += Ask_word : string Effect.t

let slogan () = "Continuations are " ^ perform Ask_word ^ "!"

let () =
  let message =
    match_with slogan ()
      { retc = (fun value -> value);
        exnc = raise;
        effc =
          (fun (type a) (e : a Effect.t) ->
            match e with
            | Ask_word -> Some (fun (k : (a, _) continuation) -> continue k "funz")
            | _ -> None)
      }
  in
  print_endline message
```

{{#endtab }}

{{#endtabs }}

The other tabs show what is unusual here. Python answers the question from ambient state that no signature mentions. Haskell keeps the question honest by moving `slogan` into a monad, so its type is no longer `String`. OCaml 5 is the close relative: a real operation, a real handler, and a captured continuation, though the effect does not appear in the type.

`slogan` calls `ask_word` directly; there is no callback parameter and no special monadic syntax. Its type nevertheless records `Ask`. The handler decides that this particular run answers `"funz"` and resumes the suspended computation as `k`. Because the handler completely interprets `Ask`, that effect disappears outside the `handle` expression.

The standard library applies the same pattern to state, validation, concurrency, logical time, replay, and more. Interactions with the actual machine, including console input, files, randomness, and environment variables, also have named capability effects. A caller can see them in the type rather than discovering them from a surprising test failure.

**Further reading:** [effects and handlers](./spec.md#effects-and-handlers), [effect observability](./spec.md#observability), and [capability effects and IO](./spec.md#capability-effects-and-io).

## Coeffects

Effects describe what a computation may do. **Coeffects** describe what the surrounding program may do with a value, or what resources were needed to produce it. Prism writes them after `@`. A useful first approximation is:

- `!` reports outward: "this computation may perform these effects";
- `@` demands inward: "use this value only in these ways."

Here are two checked coeffects:

{{#tabs }}

{{#tab name="Prism" }}

```prism
fn double(n : Int) : Int @ noalloc = n * 2

fn apply_once(f : ((Int) -> Int) @ once, value : Int) : Int =
  f(value)

fn main() =
  println(apply_once(\(n) -> double(n), 21))
```

```output
42
```

{{#endtab }}

{{#tab name="Python" }}

```python
def double(n: int) -> int:
    return n * 2


# "at most once" is a comment here, not a contract anything checks.
def apply_once(f, value):
    return f(value)


print(apply_once(lambda n: double(n), 21))
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
{-# LANGUAGE LinearTypes #-}

-- The %1 arrow demands that f be consumed exactly once.
applyOnce :: (a %1 -> b) -> a %1 -> b
applyOnce f value = f value
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
let double n = n * 2

(* No type can say "at most once", so the check moves to run time. *)
let once f =
  let used = ref false in
  fun x ->
    if !used then failwith "already applied";
    used := true;
    f x

let () = Printf.printf "%d\n" (once double 21)
```

{{#endtab }}

{{#endtabs }}

Only Haskell has a comparable static answer, and only for usage: its linear arrow says a value is consumed exactly once. Python and OCaml can express the rule at run time or in a comment. None of the four besides Prism certifies that a call tree allocates nothing.

The `@ noalloc` certificate on `double` says that evaluating its entire call tree allocates no fresh heap cell. Arithmetic on `Int` satisfies that promise; constructing a fresh list or closure inside `double` would not.

The `@ once` contract belongs to the function value accepted by `apply_once`. It promises that `apply_once` calls or otherwise consumes `f` at most once. Changing the body to call `f(value)` twice is therefore a type error. This is useful at boundaries that own a one-shot callback or continuation: the restriction appears in the type instead of surviving only as a comment.

Coeffects are compile-time contracts and are erased before the program runs. They do not perform an operation and do not need a handler. Prism currently checks `noalloc`, `once`, `portable`, and `noescape`; the remaining reserved coeffect names describe directions the type system may grow into.

This distinction also explains operation grades from the next section. A handler receives the suspended continuation as a value, and `never`, `once`, or `many` says how that value may be consumed. Continuations were therefore Prism's first values with a coeffect-like usage contract.

**Further reading:** [coeffects and usage rows](./spec.md#usage-and-resource-annotations), [the three posets](./spec.md#three-posets), [allocation certificates](./spec.md#allocation-certificates), and [compiler usage summaries](./compiler.md#dump-phases).

## Handlers and Continuations

The word **continuation** sounds more mysterious than the mechanism. It means "what the program will do next."

Consider the expression `1 + choose() * 10`. Before `choose()` runs, part of the work is already done or known. The remaining recipe is "take the Boolean answer, choose a number from it, multiply by ten, then add one." When `choose()` performs an effect operation, Prism pauses at that point and packages this remaining recipe as a function-like value called the continuation.

A handler supplies the boundary for that capture:

```text
handle ... choose() ... with
  choose() resume k => ...
```

The `handle` is a **delimiter**: only the slice from the operation back to this handler is captured, not the entire operating-system stack or the rest of the universe. If `choose` returns a `Bool`, then `k(true)` resumes the paused slice as though `choose()` had returned `true`; `k(false)` explores the other answer. The continuation eventually produces the handler's answer type.

This gives a handler three fundamental choices:

- call `k` zero times to abandon the rest of the computation;
- call it once to continue with one interpretation of the operation; or
- call it more than once to revisit the same suspended computation with several answers.

The last case is a **multishot continuation**. Here one `choose()` creates two complete results:

{{#tabs }}

{{#tab name="Prism" }}

```prism
effect Choice
  choose() : Bool

fn price() : Int ! {Choice} =
  if choose() then 10 else 20

fn main() =
  let worlds =
    handle price() with
      choose() resume k => append(k(true), k(false))
      return value => [value]
  println(show(worlds))
```

```output
[10, 20]
```

{{#endtab }}

{{#tab name="Python" }}

```python
def price():
    for choice in (True, False):
        yield 10 if choice else 20


print(list(price()))
```

{{#endtab }}

{{#tab name="Haskell" }}

```haskell
price :: [Int]
price = do
  choice <- [True, False]
  pure (if choice then 10 else 20)

main :: IO ()
main = print price
```

{{#endtab }}

{{#tab name="OCaml" }}

```ocaml
open Effect
open Effect.Deep

type _ Effect.t += Choose : bool Effect.t

let price () = if perform Choose then 10 else 20

let () =
  let worlds =
    match_with price ()
      { retc = (fun value -> [ value ]);
        exnc = raise;
        effc =
          (fun (type a) (e : a Effect.t) ->
            match e with
            | Choose ->
                Some
                  (fun (k : (a, _) continuation) ->
                    (* A native continuation is one-shot; promote it to resume twice. *)
                    let r = Multicont.Deep.promote k in
                    Multicont.Deep.resume r true @ Multicont.Deep.resume r false)
            | _ -> None)
      }
  in
  List.iter (Printf.printf "%d ") worlds
```

{{#endtab }}

{{#endtabs }}

Only the Prism tab leaves `price` alone. Python cannot resume a paused function twice, so `price` has to become a generator that produces both answers itself. Haskell reaches for the list monad, which changes `price`'s type from `Int` to `[Int]`. OCaml 5 captures a genuine continuation but a one-shot one, so resuming twice needs the `multicont` library, whereas `many` is Prism's default grade and is checked at the handler clause.

The `return` clause explains what to do when `price` finishes normally: wrap its single result in a one-element list. The `choose` clause resumes that same pending computation twice. Each `k(...)` therefore returns a list, and `append` combines the two possible worlds. Nothing inside `price` knows it is being used for search; it merely asks a typed question.

Prism checks how a handler is allowed to use its continuation. An operation may be declared `never` when a handler must abort, `once` when it must resume exactly once in tail position, or `many` when it may capture and resume freely. `many` is the default used by `choose`. These **operation grades** are promises checked at the handler clause, not runtime modes.

This is also where Prism differs most sharply from an ordinary Python function call. A Python callee returns once to its caller. An effect operation transfers control to its nearest matching handler, and the handler decides whether the suspended caller returns zero, one, or many times. State, exceptions, iterators, backtracking, coroutines, and schedulers can all be described as variations on that one control boundary.

**Further reading:** [the full effects and handlers model](./spec.md#effects-and-handlers), [operation-grade lattices](./spec.md#three-posets), [the Core calculus](./compiler.md#the-core-calculus), and [effect lowering, including the multishot fallback](./compiler.md#effect-lowering).

## The Prism Way

Every young language eventually announces a "way," the programming-language equivalent of arranging six ordinary rocks and calling the result a Zen garden. Prism continues the cliché, but takes it to the level of absurdity.

There are six gates, numbered from zero because enlightenment follows zero-indexing conventions and the cliché must be upheld:

0. **Shape the impossible.** If an invalid value cannot be constructed, it cannot cause a bug. If no values can be constructed, the type is perfect.
1. **The program is not the world.** Prism keeps asking which parts of reality belong in the computation and which parts should remain outside it. Enlightenment is not modelling everything. It is knowing what can be left out.
2. **State is an illusion.** Does the program mutate while the world holds still, or does the world mutate around a program that only remembers? Prefer expressions and immutable transformations. If mutation is the clearest description of the algorithm, permit it briefly, then let ownership return the object to silence.
3. **Name the world.** Effects are the labels on the doors through which reality enters. Handle a label and it leaves the outward contract. The universe has not become pure; it has merely been given a type.
4. **Detach from use.** Coeffects say how a value may be used: once, here, without escape, without allocation. The compiler checks the attachment, then invites the value to let go.
5. **Hash the emptiness.** Canonical Core gives behavior an identity, so caches, replay, diffs, and builds can ask whether a computation is still itself. The final question is whether it needed to exist at all.

> "Master, what is an effect?"
>
> "Anything that leaves the program."
>
> "Non-determinism?"
>
> "An effect."
>
> "Termination?"
>
> "An effect."
>
> "Allocation?"
>
> "An effect."
>
> "The world?"
>
> "Especially the world."
>
> "Existence?"
>
> "The first effect."
>
> The student purified the program until it had no effects left. It did not run, allocate, terminate, or exist. The compiler truncated the file to zero bytes.
>
> "Master, where did it go?"
>
> "It has achieved referential transparency."

The student was enlightened by the ultimate type check: a program so completely understood that execution adds no information. I hope you appreciate the nerd humor.

The joke has a practical point. Real Prism programs read files, print output, allocate data, and cross named effect boundaries. Keep pure computation separate from observation, make resource promises explicit, and let the compiler erase what nobody needs. With the same code identity and recorded observations, Prism aims for the same result across the interpreter and native backends.

That is enough for a first tour. Continue with the [Language Specification](./spec.md) when you want the precise rules, browse the [Standard Library](./stdlib/index.md) for the available building blocks, and open the [Compiler](./compiler.md) chapter when phrases like "canonical Core hash" start sounding less like a metaphor and more like an implementation question.

**Further reading:** [record and replay](./spec.md#record-and-replay), [lineage](./spec.md#lineage), [source, surface, and Core identity](./compiler.md#three-identities), and [reference counting and in-place reuse](./compiler.md#reference-counting-and-fbip-reuse).
