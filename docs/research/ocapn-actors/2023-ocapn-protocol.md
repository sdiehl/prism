# OCapN Protocol Suite

- [OCapN](https://www.ocapn.org/)
- [ocapn/ocapn](https://github.com/ocapn/ocapn)
- [OCapN Implementation Guide](https://github.com/ocapn/ocapn/blob/main/implementation-guide/Implementation%20Guide.md)
- [OCapN test suite](https://github.com/ocapn/ocapn-test-suite)
- [Spritely Institute announcement](https://spritely.institute/news/introducing-ocapn-interoperable-capabilities-over-the-network.html) — 2023

## Protocol Stack

| Layer | Spec | Purpose |
|---|---|---|
| **CapTP** | [draft](https://github.com/ocapn/ocapn/blob/main/draft-specifications/CapTP%20Specification.md) | Object-to-object messaging, promises, pipelining, distributed GC, 3rd-party handoffs |
| **Netlayers** | [draft](https://github.com/ocapn/ocapn/blob/main/draft-specifications/Netlayers.md) | Pluggable transport abstraction (Tor, TCP, libp2p, IBC) |
| **Locators** | [draft](https://github.com/ocapn/ocapn/blob/main/draft-specifications/Locators.md) | URI-based peer + object addressing |
| **Syrup** | [repo](https://github.com/ocapn/syrup) | Canonical binary serialization (based on Preserves) |

## Distributed Identity Model

- **Per-session EdDSA (Ed25519) keypairs**: Fresh keys per session, never reused
- **Self-authenticating designators**: Peer identity = cryptographic public key; no PKI
- **Connection-scoped integer indices**: Live references are small integers in session-specific import/export tables, not path-based URIs
- **Sturdyrefs**: Persistent reference = Peer Locator + Swiss Number (unguessable string)
- **No ambient authority**: No global namespace, no enumeration, no root object

## CapTP Operations

- `op:deliver` -- send message to object
- `op:listen` -- listen for promise resolution
- `op:get` / `op:index` / `op:untag` -- promise-pipelining operations
- `op:gc-exports` / `op:gc-answers` -- distributed acyclic GC
- `op:start-session` -- session initialization with key exchange
- `op:abort` -- terminate session

Third-party handoffs use signed certificates (gifter creates `desc:handoff-give`, receiver presents `desc:handoff-receive` to exporter).

## Existing Implementations

| Implementation | Language | Status |
|---|---|---|
| Goblins | Guile Scheme | Canonical |
| Goblins | Racket | Maintained, interops |
| Endo | JavaScript | Production (Agoric) |
| DObjects | Dart | Community |
| Actors Guild | Haskell | NLnet-funded, passes test suite |

## Relationship to Actor Models

OCapN is built on the actor model with key differences from classical actor systems (Erlang, Akka):

| Aspect | Classical Actors | OCapN/CapTP |
|---|---|---|
| Security | Identity-based (cookie, TLS cert) | Capability-based (reference = authority) |
| Reference passing | Free sharing; security orthogonal | 3rd-party handoffs with certs |
| GC | Typically not distributed | Distributed acyclic GC |
| Promises | Futures exist but not wire-level | Promise pipelining in wire protocol |
| Transport | Usually TCP/TLS | Abstract netlayers (Tor, IBC, etc.) |

## Relevance to Prism

Prism should implement CapTP wire protocol rather than inventing a new one. The OCapN test suite provides an interop benchmark. The netlayer abstraction means CapTP can run over Tor for production, TCP for dev, or WebAssembly channels for browser embedding.
