# Handlers and Continuations

The word **continuation** sounds abstract, but it names a concrete thing: what the program will do next.

In Python, a suspended generator remembers where to continue. Prism generalizes that idea. When an effect operation reaches a handler, Prism packages the slice of computation between the operation and that handler as a function-like value called the continuation.

## Find the rest of the computation

Imagine evaluating this expression:

```text
1 + choose() * 10
```

When `choose()` runs, the remaining recipe is:

```text
take the answer, select a number, multiply it by 10, then add 1
```

A handler names that recipe `k`:

```text
handle ... choose() ... with
  choose() resume k => ...
```

If `choose` returns a `Bool`, then `k(true)` resumes the recipe as though the operation returned `true`. The `handle` is a **delimiter**: it captures only the work back to this handler, not the entire operating-system stack.

## Resume once

The `Ask` handler from the previous chapter resumes once:

```prism
effect Ask
  ask_number() : Int

fn calculate() : Int ! {Ask} = 1 + ask_number() * 10

fn main() =
  let answer =
    handle calculate() with
      ask_number() resume k => k(4)
      return value => value
  println(answer)
```

```output
41
```

At the operation, `calculate` is paused. `k(4)` inserts `4` as the operation's result and finishes the pending arithmetic. The `return` clause describes what to do when the handled computation finishes normally.

## Resume zero times

A handler may discard the continuation. That abandons everything after the operation inside the delimiter, which is the control behavior behind an exception or early rejection:

```prism
effect Abort
  never abort(String) : String

fn checked_name(name : String) : String ! {Abort} =
  if name == "" then
    abort("empty name")
  else
    "hello {name}"

fn safe_name(name : String) : String =
  handle checked_name(name) with
    never abort(message) => "invalid: {message}"
    return value => value

fn main() =
  println(safe_name("Ada"))
  println(safe_name(""))
```

```output
hello Ada
invalid: empty name
```

`never` records that an `abort` handler must not resume. In the invalid branch, the handler's string becomes the result of the whole `handle` expression.

## Resume more than once

Calling the same continuation with several answers explores several futures of one otherwise ordinary computation:

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

`price` returns one `Int` and does not know that a search is happening. The handler decides to run the remainder once with `true` and again with `false`. The return clause wraps each completed result in a list, so each `k(...)` returns a list and `append` combines the possible worlds.

This is a **multishot continuation**. A Python generator can yield several values, but the producer must be written as a generator. Here the computation only asks a typed question. The handler decides whether that question means a fixed answer, interactive input, replay, search, or something else.

## Grades make resumption promises explicit

Every effect operation has a resumption grade:

| Grade   | What a handler may do with the continuation    |
| ------- | ---------------------------------------------- |
| `never` | discard it and do not resume                   |
| `once`  | resume exactly once in tail position           |
| `many`  | capture it and resume zero, one, or many times |

`many` is the default, which is why `Choice.choose` may resume twice. A stronger grade lets the compiler reject a handler that violates the operation's control contract:

```prism,compile_fail
effect Read
  once read() : Int

fn query() : Int ! {Read} = read() + 1

fn invalid_handler() : Int =
  handle query() with
    read() resume k => k(10) + k(20)
    return value => value
```

The declaration promises one tail-position resumption, but the handler tries to use `k` twice. This is checked statically rather than left as a comment about a callback.

## One mechanism, several familiar features

Handlers change policy without rewriting the computation:

- resuming zero times gives abort, failure, and pruning.
- resuming once can supply configuration, state, logging, or simulation time.
- resuming later gives coroutines and schedulers.
- resuming several times gives search and nondeterminism.

The important boundary is always the same: the computation names what it needs, and the nearest matching handler decides what that request means.

> **Try it:** Change the `Choice` handler to resume only with `true`. Then change it to `append(k(false), k(true))`. Notice that `price` never changes. Only the interpretation and result order do.

## Checkpoint

You are ready to continue when you can point to an operation and describe `k` as “the rest of the computation up to this handler,” then predict what happens when the handler calls it zero, one, or several times.

Next, [Coeffects](./coeffects.md) moves from what a computation may do to how a value may be used.

**Further reading:** [effects and handlers](../spec.md#effects-and-handlers), [operation grades](../spec.md#three-posets), and [effect lowering](../compiler.md#effect-lowering).
