# Local Unforgeable Identity with Prism

This document outlines how to achieve local unforgeable identity and Erlang-style message passing in Prism using modules and algebraic effects. 

## Core Concepts

In an actor model or capability system, an identity (like an `ActorRef`) must be unforgeable: a component cannot simply guess an integer ID and send a message to it; it must have been legitimately given the capability/reference.

Prism provides the tools to enforce this directly through its module system and effect handlers.

### Modules and Opaque Types

Prism's module system supports information hiding via the `opaque type` declaration.

```prism
pub opaque type ActorRef = ActorRef(Int)
```

When a module declares an `opaque type`, it exports the type name but *not* its constructor. This means:
1. Inside the defining module, `ActorRef(42)` is valid.
2. Outside the defining module, `ActorRef(42)` is a compile-time error.

By hiding the integer index of the allocated identity, `ActorRef` becomes an unforgeable capability outside its module. Users can pass it around or store it, but they can only obtain one by calling an exported function (like `spawn`) that legitimately returns one.

### The Vat Effect (Message Handling)

As discussed in [the Vat Effect design](04-vat-effect.md), Erlang-style actors can be implemented by an algebraic effect (the "Vat Effect").

```prism
pub effect VatEff {
  ctl spawn(Behavior) : ActorRef,
  ctl send(ActorRef, Msg) : Unit,
  ctl bcom(Behavior) : Unit
}
```

- **`spawn`**: Allocates a new identity, registers it in the vat's state (the "heap"), and returns the unforgeable `ActorRef`.
- **`send`**: Places a message in a queue destined for a specific `ActorRef`.
- **`bcom`** (become): Allows an actor to replace its behavior for the next message, which is the functional equivalent of state mutation in Erlang actors.

Because state and side effects in Prism are handled through `! {VatEff}`, the system evaluates the actor purely up to the point it yields an effect, rolling back cleanly if a failure occurs (transactional turns via `transact`).

## Implementation Structure

We can combine the `opaque type` and `VatEff` into a single, cohesive Vat module. See the `examples/actor_identity/Vat.pr` and `main.pr` files for a complete, compilable sketch of this pattern.

### The Heap/Actormap
The "heap" or "object effect" is managed by the `VatEff` handler. The handler threads a `VatState` containing a list or map of actors (`actormap : List((Int, Behavior))`) and a queue of pending messages.

```prism
type VatState = VatState {
  actormap : List((Int, Behavior)),
  queue : List((Int, Msg)),
  next_id : Int,
  next_behavior : Option(Behavior)
}
```

Since `ActorRef` is opaque, external code cannot arbitrarily modify this actormap. All interaction goes through the handled effects, enforcing the capability boundary.

### Working Code

A working example has been placed in `examples/actor_identity/`. 
- `Vat.pr` defines the unforgeable `ActorRef`, the messages, and the central `run_system` handler that acts as the "heap".
- `main.pr` imports `Vat` and defines `ping` and `pong` behaviors, showing how to instantiate actors and pass messages safely.

## A Functional Synthesis: Closures, Channels, and Effects

While managing an integer-based `actormap` (as shown in the Goblins-style model above) works, functional programming offers a more elegant, native synthesis of unforgeable identity that avoids central lookup tables:

### 1. Lexical Scope (Closures) as Local Capabilities
In a functional language, a closure is the most basic object-capability. Closed-over variables are private and unguessable:
```prism
fn makeCounter() =
  var count := 0
  Counter {
    incr = \() -> count := count + 1; count,
    decr = \() -> count := count - 1; count
  }
```
The returned closures hold exclusive, unforgeable authority to mutate `count`. No global heap or pointer-comparison machinery is required.

### 2. Channels (`Chan`) as Actor Identities
For concurrent, message-passing actors, we can synthesize the Actor Model with Pi-Calculus: an actor's identity is a **first-class concurrent Channel**.
- `ActorRef` is an opaque wrapper around a typed `Chan(Msg)`.
- Since channel handles are allocated on the runtime heap and managed by the GC, they are **unforgeable by construction** (you cannot "guess" a channel reference; you must be given it).
- This eliminates the central `actormap` bottleneck entirely. The runtime scheduler manages message routing and garbage-collecting dead actors automatically.

### 3. Pure Threaded State vs. Imperative Mutation
Instead of mutating state imperatively, a channel-based actor runs as a concurrent fiber executing a recursive tail-call loop. It threads its state purely through loop arguments:
```prism
fn actor_loop(chan : Chan(Msg), state : State) : !{Async} Unit =
  let msg = recv(chan)
  let next_state = handle_msg(msg, state)
  actor_loop(chan, next_state)
```
This achieves a beautiful synthesis:
- **Purity**: The actor's behavior is a pure, tail-recursive function.
- **Identity**: The actor's public handle (the `Chan` reference) remains completely constant and unforgeable.
- **Transactions**: If `handle_msg` raises an error, the recursive call is never made, and the state rollback is cleanly handled by the scheduler's fiber containment.
