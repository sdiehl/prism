# Data and Patterns

Python offers lists, tuples, dictionaries, dataclasses, enums, inheritance, and `None`. That flexibility is convenient, but it can leave basic questions to runtime: which fields exist, which alternatives are possible, and whether every case was handled.

Prism builds those answers into data types.

## Lists, tuples, and comprehensions

A list contains values of one type. A tuple has a fixed number of positions whose types may differ:

```prism
fn main() =
  let colours = ["red", "green", "blue"]
  let reading = ("violet", 42)
  let (name, value) = reading
  println("{name}: {value}")
  println(show(colours))
```

```output
violet: 42
[red, green, blue]
```

The pattern `(name, value)` destructures the tuple. It does not index into an unknown object. The type establishes that the pair has exactly two positions.

List comprehensions look familiar, but their source is a stream. This one collects five squares into a list:

```prism
fn main() =
  let squares = [n * n for n in srange(1, 6)]
  println(show(squares))
```

```output
[1, 4, 9, 16, 25]
```

Later we will keep a pipeline as a stream instead of collecting it. For now, use `map` or a comprehension when the result you want is another list.

## Records are named products

A Python dataclass says that one value contains several named fields. A Prism record says the same thing without attaching methods or an inheritance tree:

```prism
type Colour = Colour { name: String, wavelength: Int }

fn describe(c : Colour) : String = "{c.name}: {c.wavelength}nm"

fn main() =
  let violet = Colour { name = "violet", wavelength = 400 }
  let shifted = Colour { ..violet, wavelength = 405 }
  println(describe(violet))
  println(describe(shifted))
```

```output
violet: 400nm
violet: 405nm
```

`Colour { ..violet, wavelength = 405 }` creates an updated value. It does not mutate `violet`, which remains available with wavelength `400`.

A record is a **product** because one `Colour` contains a name _and_ a wavelength. A tuple is also a product. Records simply name the positions.

## Algebraic data types enumerate alternatives

Suppose a reading is either visible, infrared, or invalid. In Python you might use an enum plus optional payload fields, several dataclasses behind a union, or a string tag and conventions. Prism declares the complete vocabulary directly:

```prism
type Reading
  = Visible(String, Int)
  | Infrared(Int)
  | Invalid

fn describe(reading : Reading) : String =
  match reading of
    Visible(name, wavelength) => "{name} at {wavelength}nm"
    Infrared(wavelength) => "infrared at {wavelength}nm"
    Invalid => "invalid reading"

fn main() =
  println(describe(Visible("red", 700)))
  println(describe(Infrared(900)))
  println(describe(Invalid))
```

```output
red at 700nm
infrared at 900nm
invalid reading
```

`Reading` is a **sum** because a value has one shape _or_ another. Each constructor determines its payload. `Visible` always carries a `String` and an `Int`, while `Invalid` carries nothing. An invalid mixture of fields cannot be constructed.

This is the first major functional-programming habit: design the valid shapes first, then let functions consume those shapes.

## Patterns destructure and prove

A pattern performs two jobs at once. In `Visible(name, wavelength)`, it proves that the value is the `Visible` alternative and gives names to its two fields. The names exist only in that arm.

More importantly, a `match` must cover every constructor:

```prism,compile_fail
type Reading
  = Visible(String, Int)
  | Infrared(Int)
  | Invalid

fn describe(reading : Reading) : String =
  match reading of
    Visible(name, wavelength) => "{name} at {wavelength}nm"
    Invalid => "invalid reading"
```

The missing `Infrared` arm is a compiler error. If you later add an `Ultraviolet` constructor, every incomplete match points to code whose policy must be reconsidered.

Patterns also work for literals, tuples, lists, and records. `_` means “this shape is possible, but I do not need its value”:

```prism
fn first_or(xs : List(Int), fallback : Int) : Int =
  match xs of
    Nil => fallback
    Cons(first, _rest) => first

fn main() =
  println(first_or([], 9))
  println(first_or([3, 4, 5], 9))
```

```output
9
3
```

## `Option` makes absence explicit

Python's `None` can appear wherever an object was expected, whether or not the annotation admitted it. Prism uses the ordinary algebraic data type `Option(a)`, whose alternatives are `None` and `Some(a)`:

```prism
fn visible_name(reading : Reading) : Option(String) =
  match reading of
    Visible(name, _wavelength) => Some(name)
    Infrared(_wavelength) => None
    Invalid => None

fn name_or_unknown(name : Option(String)) : String =
  match name of
    Some(value) => value
    None => "unknown"

fn main() =
  println(name_or_unknown(visible_name(Visible("green", 550))))
  println(name_or_unknown(visible_name(Infrared(900))))

# type Reading = Visible(String, Int) | Infrared(Int) | Invalid
```

```output
green
unknown
```

`Option(String)` announces absence to every caller. Accessing the string requires handling `Some` and `None`. There is no stray null reference to fail somewhere unrelated.

> **Try it:** Add `Ultraviolet(Int)` to `Reading`. Let the compiler show every match that became incomplete, then decide separately what `describe` and `visible_name` should do with it.

## Checkpoint

You are ready to continue when you can explain:

- a record is one shape containing several fields.
- an algebraic data type is a closed set of possible shapes.
- a constructor builds one shape and a pattern takes it apart.
- exhaustiveness turns a data-model change into a useful list of affected code.

Next, [Purity and Effect Types](./effects.md) moves from the shapes of values to the observable actions computations may perform.

**Further reading:** [algebraic data types](../spec.md#algebraic-data-types), [records](../spec.md#record-types), [patterns](../spec.md#patterns), and [comprehensions](../spec.md#comprehensions).
