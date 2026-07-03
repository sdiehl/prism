# Erlang BEAM: Actor Model and Distributed Identity

- [Erlang process reference manual](https://www.erlang.org/doc/system/ref_man_processes.html)
- [Erlang distribution protocol](https://www.erlang.org/doc/apps/erts/erl_dist_protocol.html)
- [Erlang external term format](https://www.erlang.org/doc/apps/erts/erl_ext_dist.html)
- [The BEAM Book](https://blog.stenmans.org/theBeamBook/)

## Actor Model

Erlang processes: lightweight, private heap, mailbox, no shared memory. Communication via `!` operator (async, FIFO) + signals (link, unlink, exit). Location transparent -- same API for local and remote.

## Distributed Identity (PIDs)

### Internal PID Structure
Stored as immediate (unboxed) value in one machine word. 28-bit process number = index + serial/wrap counter. Printed as `<A.B.C>`.

### External PID Structure
When crossing node boundaries: `<<131, 103, NodeAtom, ID, Serial, Creation>>`. The `Creation` value distinguishes node incarnations (prevent stale PIDs from previous instance).

### PIDs Are NOT Capabilities
1. **Constructable**: `list_to_pid/1`, `pid/3` BIFs
2. **Enumerable**: `erlang:processes/0` lists all PIDs
3. **Interrogable**: `erlang:process_info/1` on any PID without authorization
4. **Full access by default**: Holding a PID grants right to send any message

## Distribution Protocol

- **EPMD** (Erlang Port Mapper Daemon) on port 4369
- **Cookie-based authentication**: MD5 challenge-response, shared secret atom
- **Cleartext data by default** (TLS optional)
- **Transitive connectivity**: A connects to B, B to C => A auto-connects to C
- **All-or-nothing trust**: Once a node authenticates, full access to all processes

## The Capability Gap

| Property | Erlang | OCapN/E/CapTP |
|---|---|---|
| Identity | PIDs: relative, enumerable, constructable | Opaque, connection-scoped, unforgeable |
| Access control | All-or-nothing per node | Reference-based; no ambient authority |
| Distribution security | Cookie (MD5); cleartext data | Mutual suspicion; pairwise encrypted |
| Node model | Trust domain; full access | Vat-based; limited references |
| Delegation | Pass PID (no attenuation) | RevocableForwarder, membrane |
| GC | Local only | Distributed acyclic |
| Promise pipelining | No | First-class |

## Prior Capability Work on BEAM

- **Stefan et al.** "Analysing Object-Capability Security" (2011): Section 5 applies ocap vulnerability analysis to Erlang as actor model instance. [PDF](https://cseweb.ucsd.edu/~dstefan/pubs/stefan:2011:ocap.pdf)
- **OTP security docs**: "All loaded code is assumed to be trusted. There is no built-in sand-boxing mechanism." [OTP secure coding guide](https://github.com/erlang/otp/blob/OTP-28.5/system/doc/design_principles/secure_coding.md)
- **Elixir Forum (2022)**: "BEAM explicitly rejects even isolating nodes from each other, never mind processes on a single node." [Discussion](https://elixirforum.com/t/elixir-and-object-capabilities/52311)

## Lessons for Prism

1. PIDs are NOT capabilities -- Prism should NOT use Erlang-style relative, enumerable, constructable identifiers
2. Erlang's cookie-based all-or-nothing trust model is fundamentally incompatible with fine-grained capability delegation
3. Prism's effect-row system is already more principled than Erlang for capabilities
4. Distributed GC is hard but necessary (Erlang lacks it)
5. CapTP promise pipelining is absent from Erlang distribution and worth adopting
