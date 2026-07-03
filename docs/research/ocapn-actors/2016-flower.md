# Flower (NuxiNL): Label-Based Networking

- [NuxiNL/flower on GitHub](https://github.com/NuxiNL/flower)
**Status**: Unmaintained since v0.11 (Jan 2019). Author recommends WASI as successor.

## Overview

Flower is a local, single-machine label-based networking daemon for CloudABI -- a capability-based POSIX-like runtime. CloudABI processes have no ambient network authority (no `bind()`, `connect()`, `open()`), so Flower mediates all network communication.

## Architecture

### Switchboard Daemon
- Central daemon on Unix domain socket (`/var/run/flower`)
- Clients connect via UDS, communicate via ARPC (gRPC-like RPC over Argdata serialization)
- Never touches the real network -- only creates socket pairs and hands one end to matched parties via `SCM_RIGHTS` fd-passing

### Labels
- String key-value pairs on every handle (`{"program": "demo", "server_name": "My server v0.1"}`)
- Connection established if no labels have matching keys but contradictory values
- Labels are **monotonic**: adding constraints never grants new authority
- `Constrain` RPC creates derived connection with narrower labels and fewer rights (capability attenuation)

### Ingress/Egress
- **Ingress**: Accepts real TCP connections, pushes accepted sockets into switchboard with labels (remote addr/port)
- **Egress**: Registers as outbound proxy; bridges switchboard connections to real remote hosts

## Capability Model

- Connection handle = **capability** (confers authority for RPCs + label matching)
- `Constrain` = **capability attenuation** (fewer rights, narrower labels)
- `Right` enum: `CLIENT_CONNECT`, `EGRESS_START`, `INGRESS_CONNECT`, `RESOLVER_START`, `SERVER_START`, `LIST`
- **File-descriptor capabilities** (OS-level), NOT object capabilities (language-level)

## Relevance to Netlayers

Flower operates at the **netlayer** level, not the CapTP level. It provides capability-based network access control for sandboxed processes — mediating which processes can talk to which peers, with what labels, over what transports. This is exactly the problem a netlayer abstraction must solve: how does a vat obtain a bidirectional channel to a peer, and what authority does that channel confer?

| Dimension | Flower | Prism Netlayer |
|---|---|---|
| Scope | Single-machine daemon | Single-machine or distributed |
| Identity | String key-value labels | Cryptographic locators (via CapTP) |
| Transport | Unix domain sockets + fd-passing | Pluggable (channel-pair, TCP, Tor) |
| Attenuation | `Constrain` RPC (narrower labels) | Effect row narrowing |
| Authority model | OS-level file descriptors | Language-level effect capabilities |

Flower is not a CapTP implementation — it solves the netlayer problem: **how to securely connect two parties and hand them a bidirectional channel**.

## Lessons for Prism

1. **Label-based attenuation as effect row narrowing**: Flower's `Constrain` is analogous to how Prism's effect handlers narrow the ambient authority of a sub-computation. A netlayer handle with fewer labels = a netlayer with fewer possible peers.
2. **File descriptor passing as capability transfer**: `SCM_RIGHTS` for cross-process delegation — if Prism ever crosses process boundaries, this is how netlayer channels could be handed off.
3. **Ingress/egress as boundary proxies**: Decoupling the internal capability-secure world from the untrusted external network. A Prism netlayer implementation needs the same pattern: an ingress proxy that accepts real connections and pushes them into the capability-secure world, and an egress proxy that bridges outbound.
4. **Monotonic labels as authority reduction**: Adding constraints never grants new authority — same invariant as Prism's effect rows. A netlayer handle that has been constrained to only connect to `{"program": "demo"}` cannot be used to connect to anything else.

## Related Projects (NuxiNL Ecosystem)
- [CloudABI on GitHub](https://github.com/NuxiNL/cloudabi)
- [Cloudlibc on GitHub](https://github.com/NuxiNL/cloudlibc)
- [Argdata on GitHub](https://github.com/NuxiNL/argdata)
- [ARPC on GitHub](https://github.com/NuxiNL/arpc)
- [32C3 talk (YouTube)](https://www.youtube.com/watch?v=3N29vrPoDv8)
