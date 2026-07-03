# Scala Actor Libraries: Akka and Pekko

- [Akka Core documentation](https://doc.akka.io/libraries/akka-core/current/)
- [Pekko documentation](https://pekko.apache.org/docs/pekko/current/)

## ActorRef Identity Model

`ActorRef[T]` is an immutable, serializable handle to a typed actor:
- **Path + UID**: `akka://<system>@<host>:<port>/<path/to/actor>#<UID>`
- **Location transparent**: Same API for local and remote sends
- **Serialization**: Protobuf with full path string; deserialization resolves to local or remote ref

## Distributed Features

- **Cluster sharding**: Entities by logical ID; `EntityRef` (not `ActorRef`) for explicit lifecycle difference
- **Receptionist**: Distributed registry via CRDTs for eventual consistency
- **Untrusted mode**: Blocks system messages and `ActorSelection` but NOT arbitrary sends
- **Artery transport**: Aeron/UDP-based, TLS with mutual authentication

## The Capability Gap

**`ActorRef` is NOT unforgeable** in the ocap sense:

| Property | Akka | OCapN |
|---|---|---|
| Reference | Path-based URI | Connection-local integer index |
| Unforgeability | Not truly (path can be constructed) | Yes (connection-scoped) |
| Security model | Perimeter-based (firewalls, TLS) | Capability-based |
| Namespace | Global (`akka://host:port/path`) | None (references are pairwise) |
| GC | JVM-local | Distributed acyclic |
| Promise pipelining | No | First-class |

### Why ActorRef is Not a Capability
1. **Path-based addressing**: `ActorSelection` can construct refs from strings
2. **Wildcard resolution**: `ActorSelection` supports `*` and `?` patterns (actor hierarchy scanning)
3. **Receptionist exposure**: Any actor knowing `ServiceKey` can discover registered actors
4. **Event bus snooping**: Dead letters and event bus can leak message contents

## Research on Capabilities for Scala Actors

- 2025 — Gordon et al. ["Actor Capabilities for Message Ordering"](https://arxiv.org/abs/2502.07958). Extends typed actor refs with ordering-restricted capabilities. arXiv: 2502.07958
- 2016 — Haller & Loiko. ["LaCasa"](https://doi.org/10.1145/2983990.2984042). _OOPSLA 2016._ Compiler plugin for affine types + ocap; `Box[T]` for ownership transfer. DOI: 10.1145/2983990.2984042
- **play-ocaps-demo**: Capabilities on top of Akka via `Brand`/`Unsealer` pairs. [play-ocaps-demo on GitHub](https://github.com/wsargent/play-ocaps-demo)

## Relevance to Prism

Akka demonstrates that path-based actor identity is incompatible with capability security. Prism should NOT use path-based or global-namespace identity. The connection-scoped integer index model of OCapN/CapTP is the correct approach for unforgeability. LaCasa's approach to affine types for ownership transfer could inform Prism's `DeepFrozen` design.

## Links
- [Akka addressing docs](https://doc.akka.io/libraries/akka-core/current/general/addressing.html)
- [Akka remote security docs](https://doc.akka.io/libraries/akka-core/current/remote-security.html)
- [Object-capability model (Wikipedia)](https://en.wikipedia.org/wiki/Object-capability_model)
- [Miller thesis: Robust Composition](http://erights.org/talks/thesis/) — 2006
