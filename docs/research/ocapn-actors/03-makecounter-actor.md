# makeCounter in a Prism Actor Library

Based on Endo/Hardened JS and Goblins.

## The JS Original (Endo/Hardened JS)

```js
const makeCounter = () => {
  let count = 0;
  return harden({
    incr: () => (count += 1),
    decr: () => (count -= 1),
  });
};

const counter = makeCounter();
counter.incr();
```

Two facets (incr, decr) demonstrate separation of duties: give entryGuard only incr, exitGuard only decr.

## Key Design Questions for Prism

1. **Encapsulated state**: JS closures capture `let count`. In Prism, `var` provides scoped mutable state that desugars to a private effect discharged by a handler -- but the state must survive across multiple method calls.

2. **Multiple capability facets**: The record `{ incr, decr }` returns two separate closures. In Prism, a record of functions works identically -- each closes over the same `var`.

3. **Single-vat vs cross-vat**: In a vat-local context, direct closures + `var` suffice. Cross-vat (distributed) requires far references managed by CapTP.

## Approach 1: Direct (Single-Vat, Closures + var)

This is the closest translation of the JS pattern. The `var` lives in `makeCounter`'s frame and persists across calls because both `incr` and `decr` close over it.

```prism,compile_fail
-- | Two facets of a counter, returned separately for POLA.
type Counter = Counter {
  incr : () -> Int,
  decr : () -> Int
}

-- | Create a new counter actor. Each call produces an independent instance
-- with its own encapsulated `count` variable.
fn makeCounter() : Counter =
  var count := 0
  Counter {
    incr = \() ->
      count := count + 1
      count
    decr = \() ->
      count := count - 1
      count
  }
```

The `var` block desugars to a private `State(Int)` effect handled by an enclosing frame, so `makeCounter` and its returned functions are **pure** (empty effect row): the mutation is discharged by the handler that wraps the block.

But there's a subtlety: `makeCounter()` returns a record **before** the `var` block's handler closes. The `var`-lifting analysis needs to prove the mutable cell escapes in the closures; currently Prism's `var` escape analysis rejects this because the closures capture the `var` and escape the function. This is a known limitation -- the analysis could be relaxed to allow this pattern with heap-lifted mutable cells.

Usage (not yet compiling):
```prism,ignore
fn main() =
  let c = makeCounter()
  println(c.incr())  -- 1
  println(c.incr())  -- 2
  println(c.decr())  -- 1
```

Separation of duties (POLA):
```prism,ignore
fn main() =
  let c = makeCounter()
  let entryGuard = c.incr    -- only incr
  let exitGuard  = c.decr    -- only decr
  entryGuard()               -- 1
  entryGuard()               -- 2
  exitGuard()                -- 1
```

## Approach 2: Explicit State Effect (for extensibility)

If we want the actor's state to be introspectable or interceptable by handlers, make the effect explicit. Instead of `var`, we use a **parameter-passing handler** that threads the state through continuations:

```prism
-- | Effect for counter operations.
effect Counter {
  ctl incr(Unit) : Int,
  ctl decr(Unit) : Int
}

-- | Run a counter action with an initial count. Each incr/decr in the action
-- threads the state via handler-local parameter passing.
fn run_counter(start : Int, action : () -> a ! {Counter | e}) =
  let f =
    handle action() with
      incr(u, k) => \(s) -> k(s + 1)(s + 1)
      decr(u, k) => \(s) -> k(s - 1)(s - 1)
      return r => \(_s) -> r
  f(start)

fn main() =
  let (x, y, z) = run_counter(0, \() ->
    let a = incr(()) in let b = incr(()) in let c = decr(()) in (a, b, c)
  )
  println(x)
  println(y)
  println(z)
```

This is more verbose but allows interleaving counter operations with other effects, and the handler can be composed (logging, revocation, etc.).

### POLA separation with effects

```prism
effect Counter {
  ctl incr(Unit) : Int,
  ctl decr(Unit) : Int
}

fn run_counter(start : Int, action : () -> a ! {Counter}) = 
  let f =
    handle action() with
      incr(u, k) => \(s) -> k(s + 1)(s + 1)
      decr(u, k) => \(s) -> k(s - 1)(s - 1)
      return r => \(_s) -> r
  f(start)

fn use_entry(f : () -> Int ! {Counter}, n) : !{Counter} Int =
  if n == 0 then 0
  else let _ = f() in use_entry(f, n - 1)

fn use_exit(f : () -> Int ! {Counter}, n) : !{Counter} Int =
  if n == 0 then 0
  else let _ = f() in use_exit(f, n - 1)

fn main() =
  let (x, y) = run_counter(0, \() ->
    let entry = \() -> incr(()) in
    let exit = \() -> decr(()) in
    let _ = use_entry(entry, 2) in
    let _ = use_exit(exit, 1) in
    (incr(()), incr(()))
  )
  println(x)
  println(y)
```

Each guard receives only its own capability (`incr` or `decr`), never both.

## Pure Functional Alternative (no effects)

The simplest counter needs no effects at all -- just thread the state explicitly:

```prism
type Counter = Counter { count : Int }

fn makeCounter() : Counter = Counter { count = 0 }
fn incr(c : Counter) : Counter = Counter { count = c.count + 1 }
fn decr(c : Counter) : Counter = Counter { count = c.count - 1 }

fn main() =
  let c1 = incr(makeCounter())
  let c2 = incr(c1)
  let c3 = decr(c2)
  println(c1.count)
  println(c2.count)
  println(c3.count)
```

In this style the counter value is a pure data structure; `incr` and `decr` are pure functions that return new counters. No mutation, no effects, no handlers. The tradeoff is that the caller must thread the state through explicitly.

## Approach 3: Goblins-style Actor with bcom (research sketch)

In Goblins, actors receive a `bcom` ("become") capability allowing them to change their behavior for the next message. This is the canonical actor pattern. In Prism:

```prism,ignore
-- | An actor is a function from message to (response, next-behavior).
type Actor(msg, resp) = (msg) -> (resp, Actor(msg, resp))

-- | The "become" capability: change the actor's behavior for the next message.
effect Become(msg, resp) {
  ctl become(Actor(msg, resp)) : Unit
}
```

But this is more complex than Prism needs initially. The parameter-passing effect handler (Approach 2) or the pure functional approach are the simplest translations of the Endo pattern and map naturally to Prism's existing semantics.

## Cross-Vat (Distributed) Design Sketch

Once we have CapTP/OCapN, a vat-local `makeCounter` would produce far references:

```prism,ignore
-- | A far reference to a counter on another vat.
type FarCounter = FarCounter {
  incr : () -> Promise(Int),
  decr : () -> Promise(Int)
}

-- | Register a counter so remote vats can obtain a FarCounter.
fn exposeCounter(c : Counter) : Sturdyref =
  sturdyref(c, ["counter"])
```

The `Promise(Int)` return type wraps eventual sends. Under CapTP, `incr()` sends `op:deliver` to the remote vat and returns a promise pipelining slot.

## Key Insight

Prism's effect system with parameter-passing handlers provides encapsulated mutable state like JS's `let`. The actor pattern is just:

```
effect with parameter passing → record of capabilities → separate facets for POLA
```

For distributed, we wrap the record in far references managed by CapTP, with `Promise` return types instead of direct `Int`.
