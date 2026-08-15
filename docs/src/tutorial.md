# Taste the Rainbow

This is Prism for Python programmers. It assumes you know variables, functions, lists, and `if`, but it assumes no functional-programming experience. By the end you will be able to read and write a small multi-file Prism program, model data, transform collections, follow inferred types and effects, write a test, and understand the ideas that make Prism unusual.

The tutorial is a bridge, not a compressed language specification. Every new idea starts from a Python habit, replaces it with a Prism mental model, and ends with something you can run or deliberately break.

## What changes when you leave Python?

The punctuation is the easy part. These are the larger shifts:

| Python instinct                                      | Prism model                                               |
| ---------------------------------------------------- | --------------------------------------------------------- |
| execute statements and `return`                      | evaluate expressions to values                            |
| reassign names freely                                | bind immutable values with `let`                          |
| represent alternatives with classes or tags          | define the exact alternatives with an algebraic data type |
| use `match` as convenient control flow               | let exhaustive patterns prove every case is covered       |
| discover IO, mutation, and exceptions from the body  | read observable effects from the function type            |
| document “call once” or “does not allocate” in prose | express usage and resource promises as coeffects          |
| build nested copies by hand                          | focus and update immutable data with optic paths          |
| use iterators to avoid intermediate lists            | fuse stream producers, transformations, and consumers     |
| identify code by filenames and source hashes         | identify canonical Core definitions by content            |

Prism is **strict**: arguments are evaluated before a function runs, as in Python. It is also deliberately **impure**: useful programs print, read files, fail, and communicate. The difference is accountability. Prism infers those observations as named effects and lets handlers interpret them at explicit boundaries.

## How to use this tutorial

The quickest route is the browser-based [Playground](https://sdiehl.github.io/prism/play/). It needs no installation and is ideal for the single-file examples in the first five chapters.

For the project, module, test, and content-identity sections, use a local compiler. Prebuilt Prism supports Apple Silicon macOS and glibc Linux on x86-64 or AArch64. Native code generation needs LLVM 22:

```shell
# macOS
brew install llvm@22

# Debian or Ubuntu
curl -fsSL https://apt.llvm.org/llvm.sh | sudo bash -s 22
```

Install the compiler and confirm it is available:

```shell
curl --proto '=https' --tlsv1.2 -fsSL https://sdiehl.github.io/prism/install.sh | sh
prism --version
```

Homebrew users may instead run `brew install sdiehl/prism/prism`. The repository [README](https://github.com/sdiehl/prism#install) covers Nix, containers, Linux packages, and building from source.

Code marked **output** is what the preceding program prints. A **Try it** prompt is small enough to do immediately. Making the change matters more than merely reading the answer. All ordinary Prism blocks in this book are checked by the compiler, and intentionally broken blocks are checked to ensure they really do fail.

## Run your first program

Put this in the Playground or save it as `rainbow.pr`:

```prism
fn main() =
  let name = "Python programmer"
  println("Welcome, {name}. Taste the Rainbow!")
```

```output
Welcome, Python programmer. Taste the Rainbow!
```

Run a local file through the interpreter:

```shell
prism check rainbow.pr
prism run rainbow.pr
prism fmt rainbow.pr
```

That three-command loop is the ordinary workflow:

- `check` finds problems without executing the program.
- `run` interprets it immediately.
- `fmt` gives the source its canonical layout.

A program begins at `main`. A `let` binds a value without making a mutable variable. There is no ordinary `return`: the last expression is the value of the body. Indentation forms the body, comments start with `--`, and `{name}` inside a string interpolates an expression.

Most type annotations are optional. The compiler inferred that `name` is a `String`, `println` produces `Unit`, and `main` performs console IO. Hover those expressions in the rendered book to see the inferred facts.

## Let the compiler teach you

Python type annotations are usually advice to a separate checker. A Prism annotation is part of the program and the compiler must prove the body agrees with it:

```prism,compile_fail
fn square(n : Int) : Int = n * n

fn main() = println(square("six"))
```

This program is supposed to fail: `square` requires an `Int`, but the call supplies a `String`. Prism diagnostics carry stable codes. When an unfamiliar one appears, ask for its explanation:

```shell
prism explain E1002
```

Use the code printed by your own diagnostic. `E1002` is simply an example. The explanation includes the cause, a minimal reproducer, and a fix.

> **Try it:** Change the greeting to accept an `Int` named `count`, interpolate it into the message, then deliberately pass a string. Read the error before repairing the call.

## The route ahead

The chapters build on one another:

1. [Functions and Values](./tutorial/functions.md) replaces statements and reassignment with expressions, immutable data flow, and higher-order functions.
2. [Data and Patterns](./tutorial/data.md) introduces records, algebraic data types, `Option`, and exhaustive matching.
3. [Purity and Effect Types](./tutorial/effects.md) makes observation visible in types and explains effect rows and row polymorphism.
4. [Handlers and Continuations](./tutorial/continuations.md) shows how a handler controls the rest of a computation.
5. [Coeffects](./tutorial/coeffects.md) turns usage and resource promises into compile-time contracts.
6. [Lenses and Streams](./tutorial/lenses-streams.md) scales immutable updates and collection pipelines.
7. [Projects and Content Identity](./tutorial/projects-identity.md) assembles a package, modules, tests, and Prism's content-addressed view of code.
8. [The Prism Way](./tutorial/prism-way.md) collects the themes into practical working habits.

One honest warning: Prism is an active language project, not a production ecosystem. Explore it, steal ideas from it, and expect a few sharp experimental edges as it evolves.

**Further reading:** [language goals](./spec.md#goal), [command-line interface](./compiler.md#command-line-interface), and [diagnostics](./compiler.md#diagnostics).
