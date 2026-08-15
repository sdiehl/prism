# Coeffects

An effect describes what may happen while a computation runs. A **coeffect** describes how the surrounding program may use a value, or which resource property was required to produce it.

A useful reading rule is:

- `!` reports outward: “this computation may perform these effects.”
- `@` demands inward: “use this value only under these conditions.”

Python has no direct equivalent. A decorator can perform a runtime check and a type-checker plugin can enforce a convention, but neither makes these promises part of the ordinary function type.

## Certify an allocation property

`@ noalloc` promises that evaluation of the function's whole call tree allocates no fresh heap cell:

```prism
fn gcd(a : Int, b : Int) : Int @ noalloc =
  if b == 0 then
    a
  else
    gcd(b, a % b)

fn main() = println(gcd(48, 18))
```

```output
6
```

Integer arithmetic and this recursion satisfy the promise. Constructing a fresh list inside `gcd` would not. The annotation is not an optimization hint. It is a claim the compiler checks.

This sharpens the meaning of purity from the previous chapter. A pure function has no outward observable effect, but it may still allocate. `@ noalloc` certifies the stronger and separate resource property.

## Constrain how a function value is consumed

`@ once` on a function value says that its receiver consumes it at most once:

```prism
fn apply_once(f : ((Int) -> Int) @ once, value : Int) : Int =
  f(value)

fn main() =
  println(apply_once(\(n) -> n * 2, 21))
```

```output
42
```

The contract belongs to `apply_once`, not to the lambda. It promises callers that the callback will not be duplicated or retained for a second use. Breaking that promise is a type error:

```prism,compile_fail
fn apply_once(f : ((Int) -> Int) @ once, value : Int) : Int =
  f(value) + f(value)
```

Python can write “called at most once” in a docstring or wrap the callback in a runtime guard. Prism makes the restriction visible before the program runs.

## The checked vocabulary

Prism currently checks four coeffects:

| Coeffect   | Promise                                                               |
| ---------- | --------------------------------------------------------------------- |
| `noalloc`  | evaluation allocates no fresh heap cell                               |
| `once`     | a value is consumed at most once                                      |
| `portable` | a value carries only state safe to move across the supported boundary |
| `noescape` | a borrowed value does not escape its permitted scope                  |

Coeffects are compile-time contracts and are erased before execution. They do not perform operations and they do not need handlers.

## Effects, grades, and coeffects are different views

These features are related but not interchangeable:

| Question                                 | Prism feature                               |
| ---------------------------------------- | ------------------------------------------- |
| What may this computation do?            | effect row, such as `! {IO, Ask}`           |
| How may this handler resume?             | operation grade: `never`, `once`, or `many` |
| How may this value be consumed?          | usage coeffect, such as `@ once`            |
| What resource fact holds for evaluation? | resource coeffect, such as `@ noalloc`      |

The connection becomes concrete at a handler clause. The continuation `k` is a value, and an operation grade constrains how the handler may consume it. A `once` operation therefore gives its continuation a checked one-use discipline. A `many` operation permits capture and duplication.

> **Try it:** Add `let xs = [a, b]` inside `gcd` and return `a` as before. The list is unused, but its allocation still violates `@ noalloc`. Remove the annotation and compare the inferred function type.

## Checkpoint

You are ready to continue when “pure” and “does not allocate” no longer sound like synonyms, and when you can distinguish a computation's effect row from a value's usage contract.

Next, [Lenses and Streams](./lenses-streams.md) uses these functional foundations to update nested immutable data and process large sequences.

**Further reading:** [coeffects and usage rows](../spec.md#usage-and-resource-annotations), [allocation certificates](../spec.md#allocation-certificates), and [the three posets](../spec.md#three-posets).
