# OCapN for Prism: Actors, Unforgeable Identity, and Distributed Capabilities

Research conducted July 2026 for [awesome-ocap#71](https://github.com/dckc/awesome-ocap/issues/71).

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Prism's Current Design](#2-prisms-current-design)
3. [OCapN Protocol Suite](#3-ocapn-protocol-suite)
4. [Body of Related Work](#4-body-of-related-work)
5. [Key Architectural Questions](#5-key-architectural-questions)
6. [Recommended Next Steps](#6-recommended-next-steps)

---

## 1. Problem Statement

**How to add distributed object-capability networking (OCapN) to Prism?**

[Prism language design](2025-prism-language.md) — Stephen Diehl, is an impure functional language with typed algebraic effects, a content-addressed core (Merkle DAG of definition hashes), deterministic replay, and capability-based sandboxing through effect handlers. It already has single-machine capability security via effect rows.

The OCapN issue asks: can we extend this to a distributed setting? The key questions are:
- **Unforgeable identity**: How do we name objects across a network so references cannot be forged?
- **Actor / remotable semantics**: How do vats, far references, and promise pipelining map onto Prism?
- **Networking**: CapTP-style protocol? Flower-style label matching? Or just raw channels?

## 2. Prism's Current Design

The core of our approach relies on the [Prism language design](2025-prism-language.md), which tracks capabilities statically via effect rows (e.g., `!{Console, FileSystem}`). Object-capability security falls out naturally: a `handle` block that installs a restricted set of handlers is a secure sandbox. Concurrency is handled via a `Concurrent` standard library effect with a completely deterministic scheduler.

## 3. OCapN Protocol Suite

The [OCapN Protocol Suite](2023-ocapn-protocol.md) provides a protocol stack for secure, distributed, peer-to-peer object communication, primarily via **CapTP** (Capability Transport Protocol). Distributed identity relies on connection-scoped integer indices (unforgeable due to the lack of a global namespace) and cryptographic **sturdyrefs** for persistence.

## 4. Body of Related Work

The following systems and models were researched to inform Prism's OCapN architecture:

- 2019 — **[Goblins actor framework](2019-goblins.md)**. Spritely Institute. The reference implementation of OCapN. Demonstrates the vat model, automatic local transactions, time-travel debugging, and safe serialization via self-portraits.
- 2016 — **[Flower label-based networking](2016-flower.md)**. A local, single-machine networking daemon demonstrating label-based attenuation and file descriptor passing, though operating at the OS-level rather than object-level.
- 2015 — **[Pony language capabilities](2015-pony.md)**. An actor-based language providing the most complete treatment of distributed cyclic GC (ORCA protocol). Its deny capabilities type system statically enforces the `DeepFrozen` property.
- 2013 — **[Monte in Haskell and OCaml](2013-monte-masque-spotter.md)**. Implementations of the capability-secure Monte language. Spotter shows how structural typing maps to dynamic object models and introduces the `DeepFrozen` auditor for cross-vat safety.
- 2011 — **[Haskell actor libraries](2011-haskell-actors.md)**. Cloud Haskell (`distributed-process`) relies on forgeable `ProcessId`s. True capability safety in Haskell has been explored in projects like Actors Guild (implementing OCapN on Troupe) and `haskell-capnp`.
- 2009 — **[Scala actors in Akka and Pekko](2009-scala-akka.md)**. Demonstrates that path-based actor identity (`akka://...`) is inherently forgeable and relies on perimeter security, confirming the necessity of OCapN's connection-scoped indices.
- 1998 — **[Erlang BEAM actor model](1998-erlang-beam.md)**. Features lightweight processes but fundamentally lacks a capability model. PIDs are enumerable and constructable, and distribution implies all-or-nothing node trust.

## 5. Key Architectural Questions

### 5.1 How should Prism model distributed identity?
Connection-scoped integer indices (per CapTP) are essential for unforgeability across the network, avoiding the pitfalls of global namespaces seen in Akka and Erlang. However, Prism's content-addressed Merkle DAGs offer a novel opportunity: could computation hashes replace or augment swiss numbers for self-verifying sturdyrefs?

### 5.2 How do actors and vats fit into Prism's effect system?
Prism's deterministic `Async` scheduler is inadequate for distributed actors because it forces a rigid interleaving that hides real network non-determinism (and the E-order / point-to-point FIFO guarantees of CapTP). Instead, we can model vats under [the Vat effect design](04-vat-effect.md) as a `Vat(msg)` effect providing `bcom`, `spawn`, and asynchronous `send`. Synchronous calls within a vat remain standard function calls. 

### 5.3 How do we guarantee transitive immutability?
A `DeepFrozen` typeclass can be used to statically guarantee that values contain no capabilities (promises or remotables) and are thus safe to pass by copy across vat boundaries. 

### 5.4 How do we format data for the wire?
Endo's `Passable` concept maps perfectly to a [Passable ADT wire format](02-passable-datatype.md) in Prism (`Passable = Atom | Container | Remotable | Promise | PassError`), natively matching the Syrup encoding and enforcing acyclicity by construction.

### 5.5 How do we handle actor state and separation of duties?
By leveraging the [makeCounter actor pattern](03-makecounter-actor.md), we can use Prism's `var` construct to provide encapsulated mutable state (desugaring to private effects). Actors are represented simply as closures capturing a `var` and returning a record of capability facets.

## 6. Recommended Next Steps

Based on the completed research, the path forward for bringing OCapN to Prism is highly tractable and leans heavily on Prism's existing strengths (effects, ADTs, and determinism):

1. **Implement the `Vat` Handler**: Build a non-deterministic vat scheduler in Prism (as designed in [the vat effect](04-vat-effect.md)) that manages a message queue and an actormap. Leverage Prism's existing `transact` blocks to give each turn automatic rollback semantics.
2. **Define `Passable` and `DeepFrozen`**: Add the `Passable` ADT ([Passable wire format](01-passable-datatype.md)) to the standard library and implement a `DeepFrozen` typeclass to statically enforce cross-vat copy safety.
3. **Implement Syrup and CapTP over TCP**: Use Prism's native capabilities to implement the Syrup serialization format, followed by the CapTP wire protocol. OCapN's point-to-point FIFO ordering maps well to standard TCP sockets.
4. **Extend `Replay` for Durable Vats**: Instead of complex state snapshotting, persist vats by logging the sequence of incoming messages (turns) via an extension to the `Replay` module. Thanks to Prism's determinism, replaying the message log perfectly restores vat state.
5. **Explore Content-Addressed Sturdyrefs**: Investigate using Prism's core definition hashes as part of the OCapN Locator / Sturdyref system.
