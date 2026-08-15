# Lenses and Streams

Immutability removes the need to track surprise mutation, but two practical questions follow:

1. How do you update something deeply nested without rebuilding every layer by hand?
2. How do you transform a large sequence without allocating a fresh list after every step?

Lenses and streams answer those questions.

## From nested copies to a focus

Python's frozen dataclasses can be updated with `dataclasses.replace`, but a deep update repeats every layer:

```python
moved = replace(player, position=replace(player.position, x=9))
```

Prism records have ordinary functional update syntax, and an **optic path** composes the nested focus:

```prism
type Vec2 = Vec2 { x: Int, y: Int }

type Player = Player { name: String, position: Vec2, score: Int }

fn main() =
  let player =
    Player {
      name = "Ada",
      position = Vec2 { x = 1, y = 2 },
      score = 10
    }
  let moved = { player | position.x = 9, score += 5 }
  println(moved.position.x)
  println(moved.score)
  println(player.position.x)
```

```output
9
15
1
```

The path `position.x` focuses an `Int` inside a `Vec2` inside a `Player`. The update returns a `Player`. The original still contains `x = 1`. When ownership is unique, the compiler may reuse the old storage in place without changing that functional meaning.

## A lens is a reusable single focus

Conceptually, a lens packages two operations:

- view one part of a larger value.
- return the larger value with that part replaced.

`deriving (Lens)` generates checked getters and functional setters for a record:

```prism
type Vec2 = Vec2 { x: Int, y: Int } deriving (Lens)

fn main() =
  let point = Vec2 { x = 3, y = 4 }
  let moved = with_x(point, 12)
  println(x_of(point))
  println(x_of(moved))
```

```output
3
12
```

The generated `x_of` and `with_x` are ordinary functions. Optic paths provide the concise surface syntax for composing such focuses through real data.

The idea generalizes:

- a **lens** focuses exactly one field.
- a **prism** focuses one constructor of an algebraic data type.
- a **traversal** focuses zero or more elements.

For example, `each` traverses a list, and `~` modifies every focus with a function:

```prism
type Player = Player { name: String, score: Int }

fn bonus(score : Int) : Int = score + 10

fn main() =
  let players = [
      Player { name = "Ada", score = 30 },
      Player { name = "Grace", score = 40 },
    ]
  let rewarded = { players | each.score ~ bonus }
  println(rewarded.[each.score])
```

```output
[40, 50]
```

The path says what to focus. `=`, `~`, and compound updates say what to do there. That separates navigation from policy.

## Lists are values and streams are processes

Each call in this list pipeline produces another complete list:

```text
numbers -> mapped list -> filtered list -> first five -> sum
```

Python often replaces those intermediates with generator expressions or `itertools`. Prism uses streams. Although evaluation is strict, stream transformers are fused between a producer and a consumer:

```prism
fn square(n : Int) : Int = n * n

fn main() =
  let total =
    srange(1, 1000)
      .smap(square)
      .skeep(even)
      .stake(5)
      .ssum()
  println(total)
```

```output
220
```

Read the chain from left to right:

1. produce integers beginning at `1`.
2. square each integer.
3. keep the even squares.
4. stop after five values.
5. sum them.

No list of 999 integers or intermediate squares is required. `stake(5)` also stops the source early, so later values are never requested.

`sof(xs)` turns a list into a stream. `scollect()` consumes a stream into a list when a materialized result is actually wanted:

```prism
fn main() =
  let values = sof([1, 2, 3, 4]).smap(\(n) -> n * 3).scollect()
  println(show(values))
```

```output
[3, 6, 9, 12]
```

## Streams are another use of handlers

A Prism stream is a producer that emits values through an effect. Transformers handle each emission and emit a transformed stream. Consumers handle emissions and fold them into a final value. The compiler can lower the composed handlers to a fused state-threading loop.

This connects the feature to the previous chapters:

- `smap` resumes once for each transformed value.
- `skeep` may drop a value while continuing the source.
- `stake` stops early by discarding the remaining continuation.

The user-facing pipeline stays direct and declarative. Effects and continuations explain why its control flow can be composed and optimized.

> **Try it:** Change the stream to cube the numbers, keep odd results, and take three. Predict which source value is the last one requested. Then replace `ssum()` with `scollect()` and inspect the values.

## Checkpoint

You are ready to continue when you can explain an optic as a composable focus and a stream as a producer/consumer process rather than an already-built collection.

Next, [Projects and Content Identity](./projects-identity.md) puts the language ideas into a package and shows how Prism decides whether code is still the same code.

**Further reading:** [optic paths](../spec.md#optic-paths), [derived lenses](../spec.md#deriving-lens), [streams](../spec.md#streams), and [effect lowering](../compiler.md#effect-lowering).
