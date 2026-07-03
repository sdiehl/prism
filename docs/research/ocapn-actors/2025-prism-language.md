# Prism Language: Capability Effects, Deterministic Replay, Content-Addressed Core

**Author**: Stephen Diehl
- [sdiehl/prism on GitHub](https://github.com/sdiehl/prism)
- [Introducing Prism](https://www.stephendiehl.com/posts/prism/) — stephendiehl.com, 2025
- [Prism compiler documentation](https://sdiehl.github.io/prism/compiler.html)
- [Prism language specification](https://sdiehl.github.io/prism/spec.html)
- [Prism playground](https://sdiehl.github.io/prism/play/)

## Overview

Prism is an impure functional language with typed algebraic effects, compiled via LLVM/MLIR to native code and WebAssembly. The core thesis: effects should be visible, typed, and composable, tracked in the type system, and optimizable to zero cost.

## Capability Effects (Static)

Prism uses algebraic effect handlers with row-polymorphic effect types, not monads. Effects are declared as sets of operations; handlers give them meaning. The language provides four reserved capability effects representing different parts of the outside world: `Console`, `FileSystem`, `Random`, `Env`, `Output`, `Clock`.

A function's effect row names exactly which capabilities it exercises:
```prism
fn roll() : !{Random} Int = rand()
```

Capability-based sandboxing falls out naturally: a `handle` block with restricted handlers is a sandbox. A sub-computation can only perform operations those handlers answer. Anything not handled is a label left in the row that some enclosing handler must answer.

> "Authority is precisely the set of handlers in scope, it is delegated by passing a thunk into a handler rather than by granting an ambient permission, and it is attenuated by nesting a sub-computation inside a narrower handler that intercepts or denies operations before any outer one sees them."

## Content-Addressed Core

`prism dump core-hash` computes a cryptographic hash of each top-level definition's elaborated core after:
1. Free references replaced by those symbols' own hashes (Merkle DAG)
2. Bound variables alpha-normalized to positions
3. Source spans, comments, formatting erased

> "A computation named by a hash can be shipped across a wire and run with a proof it is the same computation"

The hash commits to the generalized type, principal effect row, mode/borrow mask. A rename reformat leaves the hash unchanged; any behavioral change changes it.

## Deterministic Replay

The `Replay` stdlib module provides `record(action)` (logs capability observations into a `Trace`) and `replay(trace, action)` (re-runs with no real IO, serving from recorded trace). `durable(path, action)` persists logs for crash recovery.

Replay is sound because of: (1) Lean-proven determinism theorem, (2) capability effects partition the world into traceable inputs and suppressible outputs, (3) parity oracle verifies byte-identical behavior across backends, (4) concurrency scheduler is deterministic (pure function of program structure).

## Runtime and Actor-Like Semantics

No built-in concurrency; the `Concurrent` standard library provides an `Async` effect and `run_async` handler with:
- `fork` for fiber spawning
- `channel`/`send`/`recv` for buffered FIFO communication
- Capability tunneling through scheduler to outer handlers
- Structured concurrency via `scope`
- Deterministic scheduling (fixed by program structure)

## Relevance to OCapN

Prism already has capability-based security for the single-machine case via effect rows. The content-addressed core provides a foundation for distributed computation identified by hash. For OCapN integration, the key questions are:
- How to model vats as effect handlers
- How to represent far references (cross-vat) in the type system
- How to integrate CapTP promise pipelining with Prism's deterministic scheduling
- Whether content hashes can serve as sturdyrefs
