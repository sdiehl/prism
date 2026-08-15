# Functions and Values

Python functions usually contain a sequence of statements and an explicit `return`. Prism functions are expressions: evaluate the body and its final value is the result.

## Bind values instead of assigning variables

Here is the same small calculation in both languages:

{{#tabs }}

{{#tab name="Prism" }}

```prism
fn square(n : Int) : Int = n * n

fn main() =
  let side = 6
  let area = square(side)
  println("area = {area}")
```

```output
area = 36
```

{{#endtab }}

{{#tab name="Python" }}

```python
def square(n: int) -> int:
    return n * n


side = 6
area = square(side)
print(f"area = {area}")
```

{{#endtab }}

{{#endtabs }}

`let` does not create a cell waiting to be reassigned. It gives a value a name. That makes data flow local: after reading `let area = square(side)`, you never have to search the rest of the function for a later `area = ...`.

Prism does support scoped mutation with `var` when it is the clearest way to write an algorithm. It is not the default vocabulary for ordinary data flow. Begin with `let` and introduce a `var` only when changing one place over time is the idea you mean.

## Types describe, inference fills the gaps

The annotation in

```prism
fn square(n : Int) : Int = n * n
```

says that `square` accepts one `Int` and returns an `Int`. Prism can infer this particular signature, so this is valid too:

```prism
fn square(n) = n * n

fn main() = println(square(7))
```

```output
49
```

Annotations are most useful at an API boundary or when they explain intent. They are checked descriptions, not runtime conversions: annotating a `String` as `Int` does not coerce it.

## Control flow produces values

Python's `if` chooses which statements to execute. Prism's `if` also chooses a value:

```prism
fn temperature_word(c : Int) : String =
  if c < 10 then
    "cold"
  elif c < 20 then
    "mild"
  else
    "warm"

fn main() =
  let word = temperature_word(18)
  println(word)
```

```output
mild
```

There is no `return` in the branches. Every branch must produce a compatible type because the entire `if` occupies one position in the program.

```prism,compile_fail
fn inconsistent(flag : Bool) =
  if flag then 1 else "one"
```

The failing example cannot choose between returning `Int` and returning `String`. Catching that disagreement at the branch is much better than letting it travel through later code.

## Functions are ordinary values

Python programmers already pass functions to `sorted`, `map`, decorators, and callbacks. Functional programming makes that habit central.

A Prism lambda is an unnamed function written `\(arguments) -> expression`:

```prism
fn apply_twice(f : (Int) -> Int, n : Int) : Int = f(f(n))

fn main() =
  let add_three = \(n) -> n + 3
  println(apply_twice(add_three, 10))
```

```output
16
```

The type `(Int) -> Int` describes a function value. `apply_twice` knows nothing about the implementation of `f`. Its type supplies everything needed to call it.

`map` applies a function to every element without changing the original list:

```prism
fn square(n : Int) : Int = n * n

fn main() =
  let numbers = [1, 2, 3, 4]
  let squares = map(square, numbers)
  println(show(numbers))
  println(show(squares))
```

```output
[1, 2, 3, 4]
[1, 4, 9, 16]
```

If a Python loop exists only to append one transformed value per input, `map` or a comprehension states the same intent without managing an accumulator.

## Composition and left-to-right reading

Small functions become useful when they compose. `f >> g` builds a function that runs `f` and then `g`. `x |> f` sends an existing value through a function:

```prism
fn double(n : Int) : Int = n * 2

fn add_one(n : Int) : Int = n + 1

fn main() =
  let double_then_add_one = double >> add_one
  println(double_then_add_one(20))
  println(20 |> double_then_add_one)
```

```output
41
41
```

Prism also permits `value.function(args)` as left-to-right call syntax, but it is only syntax: Prism has top-level functions rather than Python-style methods. `value.f(x)` means `f(value, x)`.

> **Try it:** Write `classify : (Int) -> String` using `if`. Then map it over `[-2, 0, 5]`. Before running the program, predict the inferred type of the resulting list.

## Checkpoint

You are ready to move on when these statements feel natural:

- a function body is an expression whose final value is its result.
- `let` names immutable data.
- annotations state facts that inference must satisfy.
- a function can be passed, returned, or stored like any other value.

Next, [Data and Patterns](./data.md) replaces open-ended object conventions with types that enumerate their valid shapes.

**Further reading:** [functions](../spec.md#functions), [`let` statements](../spec.md#let-statements), and [function composition](../spec.md#function-composition).
