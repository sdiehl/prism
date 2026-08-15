# Purity and Effect Types

Python's `-> str` says what a function returns. It does not say whether the function also prints, reads a file, mutates global state, draws randomness, or raises an exception.

Prism gives a computation two descriptions:

- its value type says what it returns.
- its **effect row** says what it may observe or perform along the way.

## Pure computation versus observation

Consider a tiny report with a pure core and an effectful boundary:

```prism
fn band(wavelength : Int) : String =
  if wavelength < 450 then
    "violet"
  elif wavelength < 495 then
    "blue"
  elif wavelength < 570 then
    "green"
  else
    "warm"

fn report(wavelength : Int) : Unit ! {IO} =
  println("{wavelength}nm is {band(wavelength)}")

fn main() = report(530)
```

```output
530nm is green
```

`band` has no effect row because it only computes a `String` from an `Int`. Calling it again with the same argument supplies no new information. `report` returns only `Unit`, but its `! {IO}` says it may interact with the outside world.

In this tutorial, **pure** means “no outward observable effects.” It does not mean “does no work” or “allocates nothing.” Allocation promises belong to coeffects, and termination is a separate question.

Purity is useful rather than ceremonial. Pure code is easy to call from tests, simulations, optimizers, or several effectful front ends because it has no hidden world to reconstruct.

## Rows compose through ordinary calls

An effect row is a set of named capabilities. If a function calls something with an effect, that effect becomes part of the caller's row unless it is handled locally.

Errors demonstrate the rule with familiar control flow:

```prism
error InvalidWavelength(Int)

fn validate(wavelength : Int) : Int ! {InvalidWavelength} =
  if wavelength >= 380 && wavelength <= 750 then
    wavelength
  else
    throw InvalidWavelength(wavelength)

fn label(wavelength : Int) : String ! {InvalidWavelength} =
  "visible: {validate(wavelength)}nm"

fn safe_label(wavelength : Int) : String =
  try
    label(wavelength)
  catch
    InvalidWavelength(bad) => "outside the visible range: {bad}"

fn main() =
  println(safe_label(550))
  println(safe_label(900))
```

```output
visible: 550nm
outside the visible range: 900
```

`validate` may throw `InvalidWavelength`, so `label` inherits that label by calling it. `safe_label` catches every `InvalidWavelength`, so the label is absent outside the `try`/`catch`. Handling is **subtractive**: a fully interpreted effect disappears from the outward contract.

Compare that with Python. A Python caller must read documentation or inspect the body to learn which exceptions may escape. In Prism, unhandled errors are part of the same composition rule as every other effect.

## Define a capability as a typed question

An effect declares operations a computation may request. The computation calls an operation directly. A surrounding handler chooses its meaning:

```prism
effect Ask
  ask_word() : String

fn slogan() : String ! {Ask} =
  "Continuations are {ask_word()}!"

fn main() =
  let message =
    handle slogan() with
      ask_word() resume k => k("programmable")
      return value => value
  println(message)
```

```output
Continuations are programmable!
```

`slogan` neither receives a callback nor looks up ambient state. It asks the named `Ask` capability for a `String`, and its type records that dependency. The handler answers this run with `"programmable"` and resumes the suspended computation as `k`.

This separation is deeper than dependency injection. The handler can provide an answer, record the request, reject it, replay an earlier answer, or resume the request more than once. The next chapter explains that control explicitly.

## Closed and open rows

`! {Ask, IO}` is a **closed row**: it names the complete set of effects admitted there. Higher-order code often should not care which effects its function argument performs. It should preserve them.

```prism
effect Tick
  tick() : Int

fn twice(f : (Int) -> Int ! {| e}, x : Int) : Int ! {| e} =
  f(x) + f(x)

fn plus_one(n : Int) : Int = n + 1

fn plus_tick(n : Int) : Int ! {Tick} = n + tick()

fn main() =
  println(twice(plus_one, 20))
  let answer =
    handle twice(plus_tick, 20) with
      tick() resume k => k(1)
      return value => value
  println(answer)
```

```output
42
42
```

The row variable `e` means “whatever effects `f` has.” For `plus_one`, `e` is empty. For `plus_tick`, it contains `Tick`. `twice` does not erase, reinterpret, or add to that row. It passes the caller's effect information through.

This is **row polymorphism**. Ordinary polymorphism abstracts over a value type, such as “a list of any element type.” Row polymorphism abstracts over an open set of labels. It is what lets reusable wrappers remain honest without fixing one global stack of effects.

> **Try it:** Add an effect `Trace` with `trace(String) : Unit`. Write a function that traces and returns its argument, pass it to `twice`, and handle `Trace` in `main`. Watch the inferred row grow and then disappear at the handler.

## Checkpoint

You are ready to continue when you can read `(Int) -> String ! {Ask, InvalidWavelength}` as:

> accepts an `Int`, returns a `String`, and may ask a question or reject a wavelength before it returns.

You should also be able to explain why a handler can remove a label and why an open row lets higher-order code preserve effects it does not understand.

Next, [Handlers and Continuations](./continuations.md) examines the `k` that the handler receives.

**Further reading:** [effects and handlers](../spec.md#effects-and-handlers), [errors and failure](../spec.md#errors-and-failure), [effect observability](../spec.md#observability), and [effect polymorphism](../spec.md#effect-polymorphism).
