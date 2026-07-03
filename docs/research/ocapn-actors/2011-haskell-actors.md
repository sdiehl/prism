# Haskell Actor Libraries and Distributed Identity

## Cloud Haskell / distributed-process

- 2011 — Epstein, Black, Peyton Jones. ["Towards Haskell in the Cloud"](https://doi.org/10.1145/2034675.2034690). _Haskell 2011._
- [distributed-process on GitHub](https://github.com/haskell-distributed/distributed-process)
- [haskell-distributed documentation](https://haskell-distributed.github.io/)

### Identity Model

`ProcessId` = `NodeId` (address) + `LocalProcessId` (seed, counter). Serializable via `Binary` instance. Show instance: `pid://<addr>:<counter>`.

**Not unforgeable**: `ProcessId` is plain serializable data. Documentation states: "the references are not easily forged (i.e., sent by mistake - this is not a security feature of any sort)."

### Architecture
- Pluggable network transports (network-transport package)
- `Process` monad for actor behavior
- Typed channels with `SendPort`/`ReceivePort`
- Name registration via `register`/`nsend`
- Remote spawning via `spawn` + `Closure`

### Status
Low activity. 2024 discussion about revival as "Cloud Haskell 3.0." The proposal would introduce URI-based addressing similar to Akka.

## Troupe

- [Troupe on GitHub](https://github.com/NicolasT/troupe)

Single-process actor framework. No IPC. `ProcessM` monad on `IO`. Erlang-style linking/monitoring. Messages fully evaluated (`NFData`) before mailbox delivery.

NLnet-funded project to add OCapN support via "Actors Guild" (see below).

## Haskell OCapN Implementations

### Actors Guild
- **Site**: [Actors Guild](https://dpwiz.gitlab.io/actors-guild/)
- **NLnet**: [NLnet Haskell-OCAP project](https://nlnet.nl/project/Haskell-OCAP/)
- Implements OCapN + Syndicate protocols for Troupe. Passes OCapN test suite.

### haskell-capnp (zenhack)
- **Repo**: [haskell-capnp on GitHub](https://github.com/zenhack/haskell-capnp)
- Cap'n Proto RPC for Haskell with CapTP support (Level 1)
- Promise pipelining via `pipe`/`waitPipeline`
- Bootstrap interfaces

### haskell-ocap (zenhack)
- **Repo**: [haskell-ocap on GitHub](https://github.com/zenhack/haskell-ocap)
- `OCapIO` monad for local-process capability safety
- First-class capability values (`TcpPort`, `Host`)
- Not distributed, but demonstrates capability discipline in Haskell

## Comparison

| System | Identity | Unforgeable? | Distributed? | OCapN? |
|---|---|---|---|---|
| distributed-process | `ProcessId` (NodeId + counter) | No | Yes | No |
| Troupe | Internal (no IPC) | N/A | No | Via Actors Guild |
| haskell-capnp | Cap'n Proto RPC refs | Yes (protocol-level) | Yes | Partial (CapTP) |
| Actors Guild | OCapN sturdyrefs | Yes (cryptographic) | Via Troupe | Yes |

## Key Links
- 2011 — Epstein, Black, Peyton Jones. ["Towards Haskell in the Cloud"](https://doi.org/10.1145/2034675.2034690). _Haskell 2011._ DOI: 10.1145/2034675.2034690
- [Cloud Haskell revival](https://discourse.haskell.org/t/facilitating-cloud-haskell-use-and-development/10252) — Haskell Discourse, 2024
- [Troupe design ideas](https://github.com/NicolasT/troupe/wiki/Design-Ideas/)
- [Actors Guild](https://dpwiz.gitlab.io/actors-guild/)
- [haskell-capnp on GitHub](https://github.com/zenhack/haskell-capnp)
