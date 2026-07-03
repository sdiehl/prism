# Vat Effect: Actors with bcom, Pattern Matching, and Transactions

Based on Goblins' vat model, Erlang's receive/pattern-matching, and Prism's
existing effect system, `transact`, and `Replay` serialization.

## Table of Contents

1. [Why Not Async?](#1-why-not-async)
2. [The Vat Effect](#2-the-vat-effect)
3. [Actor Definition: bcom and Pattern Matching](#3-actor-definition-bcom-and-pattern-matching)
4. [The Vat Handler: Turns as Transactions](#4-the-vat-handler-turns-as-transactions)
5. [makeCounter in the Vat Model](#5-makecounter-in-the-vat-model)
6. [Persistence via Replay](#6-persistence-via-replay)
7. [Running the Tests](#7-running-the-tests)

## 1. Why Not Async?

Prism's `Async` effect (`Concurrent.pr`) provides cooperative fibers with a
**deterministic scheduler**. The schedule is a pure function of program
structure -- fibers run in a fixed order, identical on every execution.

This is the wrong model for actors. Here's why:

### 1.1 Deterministic Scheduling Hides Real Distributed Behavior

In a distributed system, messages from *different* remote vats arrive at a recipient vat in
**arbitrary order**. 

It is important to distinguish this from the ordering guarantees provided by CapTP. Historically, the E language provided **E-order**, a whole-system ordering guarantee that spanned 3-party handoffs. Under E-order, if Alice sends message `m1` to Carol, and then Alice introduces Bob to Carol, any message `m2` that Bob subsequently sends to Carol is guaranteed to arrive *after* `m1`. 

However, modern implementations (like Agoric's and the [OCapN pre-standardization effort](https://github.com/ocapn/ocapn/issues/40)) have explicitly backed away from full E-order due to the complexity it introduces with 3-party handoffs and edge cases like the "lost resolution bug". Instead, OCapN provides **point-to-point FIFO ordering** per session:

> "A CapTP session consists of two entities exchanging CapTP messages over a reliable, in-order OCapN Netlayer channel..."

So while `m1` and `m2` sent directly from Vat A to Vat B will arrive in order, messages from independent actors in independent vats have no such global ordering. 

A deterministic scheduler, like the one in `Async`, forces a specific interleaving
even for messages arriving from *different* vats, which completely hides real distributed non-determinism:

```prism
-- Two DIFFERENT remote vats (A and B) send messages concurrently.
-- With Async's deterministic scheduler, fiber A always runs before fiber B.
-- In a real network, either message could arrive first.
--
-- This test PASSES under Async (deterministic ordering hides the bug)
-- but FAILS under a non-deterministic vat scheduler:

fn test_ordering() =
  var log := Nil
  let ch = channel()
  -- Vat A: send "a" then receive
  let _a = fork(\() ->
    send(ch, "a")
    let r = recv(ch)
    log := Cons(r, log)
    r
  )
  -- Vat B: send "b" then receive
  let _b = fork(\() ->
    send(ch, "b")
    let r = recv(ch)
    log := Cons(r, log)
    r
  )
  -- Under deterministic scheduling, fiber A always runs first,
  -- so log is always ["b", "a"]. In a real distributed system,
  -- log could be ["a", "b"] if B's message arrives first.
  await(_a)
  await(_b)
  -- This assertion only passes because the scheduler is deterministic.
  -- It would fail under realistic message ordering.
  guard(log == ["b", "a"])
```

### 1.2 No Message Dispatch

`Async` has `channel`/`send`/`recv` for FIFO channels, but no concept of
"receive a message and pattern-match on it." You'd have to build a
message-dispatch loop on top of channels, which is exactly what a vat provides.

### 1.3 No bcom (Become)

`Async` fibers run to completion. There's no way for a fiber to replace its
behavior for the next message. In the actor model, `bcom` is the fundamental
state-update mechanism: after handling a message, the actor becomes a new
behavior for the next message.

### 1.4 No Transaction Boundary Per Message

In Goblins, each turn (message delivery) is a **transaction**. If an error
occurs, all state changes within that turn roll back. `Async` has no such
boundary -- a fiber that errors partway through leaves partial state changes.

### 1.5 No Far References

`Async` has no concept of remote objects. Everything is local. A vat needs
to distinguish near references (same vat, synchronous `$`) from far references
(different vat, asynchronous `<-`).

## 2. The Vat Effect

The `Vat` effect provides three operations available to actors during a turn:

```prism
-- | The Vat effect: actor lifecycle within a vat.
-- Parameterized by the message type `msg`.
pub effect Vat(msg) {
  -- | Replace this actor's behavior for the next message.
  -- The current turn still completes and returns its response.
  ctl bcom(Actor(msg)) : Unit,

  -- | Spawn a new actor in this vat, returning a near reference.
  ctl spawn(Actor(msg)) : ActorRef,

  -- | Send an asynchronous message to an actor (near or far).
  -- The message is queued and delivered in a future turn.
  ctl send(ActorRef, msg) : Unit
}
```

### Design Notes

- **`bcom` does not interrupt the current turn.** The actor's behavior function
  still returns its response for the current message. `bcom` only affects the
  *next* message delivery.

- **`spawn` returns an `ActorRef`**, an opaque handle. Within a vat, this is a
  near reference (synchronous calls are direct function calls). Across vats,
  this becomes a far reference managed by CapTP.

- **`send` is asynchronous.** The message goes into the target's queue and is
  delivered in a future turn. For synchronous calls within a vat, just call the
  behavior function directly -- no effect needed.

### Supporting Types

```prism
-- | An opaque reference to an actor in this vat.
pub newtype ActorRef = ActorRef(Int)

-- | An actor is a function from message to response.
-- It may perform Vat operations (bcom, spawn, send) plus
-- any ambient effects `e` (capabilities the actor holds).
pub type Actor(msg) = (msg) -> msg ! {Vat(msg) | e}
```

## 3. Actor Definition: bcom and Pattern Matching

### 3.1 The Simplest Actor: A Cell

This is the Goblins `^cell` translated to Prism. A cell holds a value and
responds to `Get` and `Set` messages:

```prism
-- | Messages a cell understands.
pub type CellMsg
  = Get
  | Set(Int)

-- | A cell actor: holds an integer value.
-- Pattern-matches on the message, uses bcom to update state.
pub fn cell(val : Int) : Actor(CellMsg) =
  \msg ->
    match msg of
      Get => val
      Set(n) =>
        bcom(cell(n))
        n
```

Key points:
- **Pattern matching** via `match` on the ADT `CellMsg`
- **`bcom(cell(n))`** replaces the behavior for the next message with a new
  cell holding `n`
- **The response** is the current value (for `Get`) or the new value (for `Set`)
- **No mutable variables.** State change is purely functional: `bcom` installs a
  new closure capturing the new value.

### 3.2 Record Types for Message-Like Syntax

Prism's record types give a more natural message syntax:

```prism
-- | Messages as a record type: each field is a message variant.
-- The actor matches on the record to dispatch.
pub type GreeterMsg = GreeterMsg {
  greet : String,       -- greet someone by name
  set_name : String     -- change the greeter's own name
}

-- | A greeter actor using record-style messages.
pub fn greeter(name : String) : Actor(GreeterMsg) =
  \msg ->
    match msg of
      GreeterMsg { greet = who } =>
        "Hello {who}, my name is {name}!"
      GreeterMsg { set_name = new_name } =>
        bcom(greeter(new_name))
        "Name changed to {new_name}"
```

### 3.3 Composing Actors: A Counting Greeter

An actor that contains another actor (like Goblins' `^cgreeter`):

```prism
-- | A greeter that counts how many times it has greeted.
pub fn cgreeter(name : String) : Actor(GreeterMsg) =
  let counter = spawn(cell(0))
  \msg ->
    match msg of
      GreeterMsg { greet = who } =>
        -- Synchronous call to the counter (same vat, direct function call)
        let n = cell(0)(Get)  -- would need the ref; see handler below
        "Hello {who}, my name is {name}!"
      GreeterMsg { set_name = new_name } =>
        bcom(cgreeter(new_name))
        "Name changed to {new_name}"
```

> **Note:** Synchronous calls between near actors require the vat handler to
> provide a `call` operation or direct access to the actormap. The sketch above
> is simplified; the full design adds a `call` effect operation for near-actor
> synchronous invocation.

## 4. The Vat Handler: Turns as Transactions

The vat handler manages the actormap and message queue. Each turn is a
**transaction**: if an error occurs, all state changes roll back.

### 4.1 Actormap and Queue

```prism
-- | Internal state of the vat handler.
type VatState(msg) = VatState {
  -- Mapping from ActorRef to current behavior.
  actormap : List((Int, Actor(msg))),
  -- Queue of (target, message) pairs to deliver.
  queue : List((Int, msg)),
  -- Next available ActorRef ID.
  next_id : Int,
  -- Messages to send after the turn commits (outgoing queue).
  outgoing : List((Int, msg))
}
```

### 4.2 The Handler

```prism
-- | Run a vat: bootstrap an initial actor and process turns.
-- Each turn is a Prism `transact` block: on failure, the turn rolls back.
-- The handler provides the Vat effect to actors.
pub fn run_vat(boot : Actor(msg), initial_msg : msg) : msg ! {e} =
  -- Bootstrap: spawn the initial actor as ref 0.
  var state := VatState {
    actormap = [(0, boot)],
    queue = [(0, initial_msg)],
    next_id = 1,
    outgoing = Nil
  }

  -- Process turns until the queue is empty.
  -- (In a real system, we'd also wait for network messages.)
  fn drive() : msg =
    match state.queue of
      Nil => error("deadlock: empty queue")
      Cons((ref_id, msg), rest) =>
        -- Find the actor's current behavior.
        match lookup(ref_id, state.actormap) of
          None => error("actor not found")
          Some(behavior) =>
            -- Run the turn as a transaction.
            -- On failure, state rolls back to pre-turn values.
            let response =
              transact
                -- Remove this message from the queue.
                state := VatState { ..state, queue = rest }
                -- Run the actor's behavior with the Vat effect.
                let r = handle behavior(msg) with
                  bcom(new_behavior, k) =>
                    -- Update the actormap entry for this actor.
                    state := VatState {
                      ..state,
                      actormap = update(ref_id, new_behavior, state.actormap)
                    }
                    k(())
                  spawn(new_actor, k) =>
                    let new_id = state.next_id
                    state := VatState {
                      ..state,
                      next_id = new_id + 1,
                      actormap = Cons((new_id, new_actor), state.actormap)
                    }
                    k(ActorRef(new_id))
                  send(target, m, k) =>
                    match target of
                      ActorRef(tid) =>
                        state := VatState {
                          ..state,
                          outgoing = Cons((tid, m), state.outgoing)
                        }
                        k(())
                  return r => r
                r
              else
                -- Turn failed: state is rolled back, message stays in queue.
                -- Re-queue the message for retry or propagate the error.
                error("turn failed")
            -- Commit outgoing messages to the queue.
            state := VatState {
              ..state,
              queue = append(rest, state.outgoing),
              outgoing = Nil
            }
            response
```

### 4.3 Transaction Semantics

Prism's `transact body else fallback` snapshots every live `var`, runs the body
under a `Fail` handler, and restores the snapshots on failure. This maps
directly to Goblins' turn-based transactions:

| Goblins | Prism |
|---|---|
| Turn = transaction | `transact` block per message |
| Error rolls back actormap changes | `var` snapshots restored on failure |
| Outgoing messages only sent on commit | `outgoing` queue flushed after `transact` |
| Time-travel debugging | `Replay` module records turns for replay |

## 5. makeCounter in the Vat Model

The "hello world" of capabilities, now as a vat actor:

```prism
-- | Messages for the counter actor.
pub type CounterMsg
  = Incr
  | Decr

-- | A counter actor: encapsulates a count, exposes incr/decr.
-- This is the actor equivalent of the Endo makeCounter pattern.
pub fn counter(count : Int) : Actor(CounterMsg) =
  \msg ->
    match msg of
      Incr =>
        let n = count + 1
        bcom(counter(n))
        n
      Decr =>
        let n = count - 1
        bcom(counter(n))
        n

-- | Create a new counter actor and return its reference.
pub fn makeCounter() : ActorRef =
  spawn(counter(0))
```

### 5.1 Separation of Duties (POLA)

To give one principal only `incr` and another only `decr`, we create **facet
actors** that forward specific messages:

```prism
-- | A facet that only forwards Incr messages to the real counter.
pub fn incrFacet(target : ActorRef) : Actor(CounterMsg) =
  \msg ->
    match msg of
      Incr =>
        -- Forward to the real counter (synchronous, same vat).
        -- The response flows back to the caller.
        send(target, Incr)
        -- For synchronous: call(target, Incr)
        Incr  -- placeholder; real impl uses call effect
      Decr =>
        error("not authorized")
```

> **Note:** The facet pattern requires a `call` operation for synchronous
> near-actor invocation. This is a natural addition to the Vat effect:
> `ctl call(ActorRef, msg) : msg`.

### 5.2 Usage

```prism
fn main() =
  let counter_ref = makeCounter()
  -- In a real vat, you'd spawn these and send messages:
  -- send(counter_ref, Incr)  -- returns 1 (via promise)
  -- send(counter_ref, Incr)  -- returns 2
  -- send(counter_ref, Decr)  -- returns 1
  ()
```

## 6. Persistence via Replay

Prism's `Replay` module provides record/replay of capability effects. For a
vat, we can extend this to record the **sequence of turns** (messages delivered
and their responses), enabling:

1. **Durable execution**: persist the turn log; on restart, replay turns to
   restore vat state.
2. **Time-travel debugging**: replay turns up to a specific point, inspect
   actormap state.
3. **Upgrade**: replay turns against a new version of actor behaviors.

### 6.1 Turn Logging

```prism
-- | A recorded turn: the message delivered and the response produced.
type TurnEntry(msg) = TurnEntry {
  target : Int,       -- ActorRef ID
  message : msg,      -- The message delivered
  response : msg      -- The response produced
}

-- | Run a vat with turn logging. Each turn is recorded.
-- On restart, replay the log to restore state.
pub fn durable_vat(
  log_path : String,
  boot : Actor(msg),
  initial_msg : msg
) : msg =
  -- Load existing log if any.
  let log = load_log(log_path)
  -- Replay recorded turns to restore actormap state.
  -- Then continue live, appending new turns to the log.
  ...
```

### 6.2 Relationship to Goblins' Safe Serialization

| Goblins | Prism |
|---|---|
| Objects self-describe via sealed serializer | `Replay` records capability observations |
| Restore by walking self-portrait graph | Replay turns from log |
| Upgrade on restore | Replay against new behavior versions |
| Turn deltas for efficiency | `Replay` only records inputs (deterministic replay) |
| Sealer/unsealer for authority safety | Effect rows enforce capability boundaries |

Prism's approach is **input-log-based** rather than **state-snapshot-based**.
Because Prism's core is deterministic (Lean-proven), replaying the same
sequence of inputs reproduces the same state. This is more storage-efficient
than full state snapshots and naturally supports upgrade (replay old inputs
against new code).

## 7. Running the Tests

This document contains Prism code sketches. To run them as tests:

```bash
# Create a test file
cat > /tmp/vat_test.pr << 'EOF'
-- Copy the Vat effect and handler code here
-- Add test cases

fn main() =
  let ref = makeCounter()
  -- send(ref, Incr)
  -- send(ref, Incr)
  -- send(ref, Decr)
  println("vat tests pass")
EOF

# Run with the prism interpreter
prism run /tmp/vat_test.pr
```

### Doctest-Style Verification

For automated verification, add assertions:

```prism
-- | Test: counter increments correctly.
-- Expected: incr from 0 -> 1, incr -> 2, decr -> 1.
fn test_counter() =
  let ref = makeCounter()
  -- These would use the vat handler's call/send operations
  -- let r1 = call(ref, Incr)
  -- guard(r1 == 1)
  -- let r2 = call(ref, Incr)
  -- guard(r2 == 2)
  -- let r3 = call(ref, Decr)
  -- guard(r3 == 1)
  ()

-- | Test: bcom changes behavior correctly.
fn test_bcom() =
  let ref = spawn(cell(0))
  -- call(ref, Set(42))
  -- let r = call(ref, Get)
  -- guard(r == 42)
  ()

-- | Test: transaction rollback on error.
fn test_transaction_rollback() =
  let ref = spawn(cell(0))
  -- call(ref, Set(99))
  -- This turn should fail and roll back:
  -- transact
  --   call(ref, Set(999))
  --   error("boom")
  -- else
  --   ()
  -- Value should still be 99:
  -- let r = call(ref, Get)
  -- guard(r == 99)
  ()
```

### What's Missing for Full Doctests

The code in this document is a **design sketch**, not a working implementation.
To make it runnable:

1. **Implement the Vat handler** (`run_vat`) in the standard library
2. **Add a `call` operation** to the Vat effect for synchronous near-actor
   invocation
3. **Integrate with `Replay`** for turn logging and durable execution
4. **Add CapTP support** for cross-vat messaging (far references)

The design follows Prism's existing patterns:
- Effects with handlers (like `Async`/`run_async`)
- `transact` for transactional turns (like the existing `transact` examples)
- `Replay` for persistence (like `durable` in the Replay module)
- ADTs + `match` for message dispatch (like all Prism pattern matching)
- Record types for message-like syntax (like existing record examples)
