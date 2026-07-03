# Goblins: Distributed, Transactional Actor Framework

- [Spritely Institute - Goblins](https://spritely.institute/goblins/)
- [guile-goblins (Codeberg)](https://codeberg.org/spritely/goblins)
- [racket-goblins (Codeberg)](https://codeberg.org/spritely/racket-goblins)
- [Goblins Racket documentation](https://docs.racket-lang.org/goblins/index.html)
- [Goblins Guile documentation](https://files.spritely.institute/docs/guile-goblins/latest/index.html)
- [Spritely Core whitepaper](https://files.spritely.institute/papers/spritely-core.html)

Created by Christine Lemmer-Webber, stewarded by the Spritely Institute. The reference implementation and origin of OCapN.

## Architecture

### Vat Model
- Event loop per vat; synchronous `$` calls within a vat, asynchronous `<-` sends across vats
- Single turn = transaction: unhandled exceptions roll back all state changes
- Enables time-travel debugging (snapshot and interact with past states)

### Actors as Closures
No special actor class. Constructor receives `bcom` ("become") capability as first argument, returns a behavior procedure. State mutation modeled by returning new behavior via `(bcom <new-behavior>)`.

### Two Communication Primitives
| Primitive | Name | Scope | Returns |
|---|---|---|---|
| `$` | Synchronous call | Same vat only | Immediate value |
| `<-` | Asynchronous send | Any vat | Promise |

## Capability Model

- **Object-capability security**: "If you don't have it, you can't use it"
- **bcom capability**: Only the actor itself possesses this, allowing self-modification
- **Facets**: Multiple independent interfaces to the same object
- **Revocable caretakers, sealers/unsealers, mints**: Standard ocap patterns
- **Paired post/editor pattern**: Two capabilities from one factory (read vs. write)

## Distributed Identity

- **Live references**: Opaque, per-session integer indices in CapTP export/import tables
- **Sturdy references**: Persistent, serialized to disk, survive peer restarts
- **Near vs far**: Same-vat (synchronous, transactional) vs cross-vat (asynchronous)
- **Actormaps**: Low-level tables mapping actor identities to behaviors; `transactormap` adds transactional semantics

### Tor as Default Netlayer
Built-in support for Tor Onion Services, providing strong anonymity, NAT traversal, and end-to-end encryption.

## OCapN Leadership

Goblins is the primary origin of OCapN. OCapN was extracted from Goblins into an independent standardization effort in 2022-2023. Goblins implements the full OCapN stack: CapTP, netlayers, locators, Syrup.

## Key Innovations

1. **Automatic transactions via vat model**: No manual rollback or compensating actions
2. **Time-travel debugging**: Interact with snapshots of past states
3. **CapTP standardization**: Extracted into OCapN for cross-language interop
4. **Certificate-based third-party handoffs**: Secure reference sharing across sessions
5. **Netlayer abstraction**: Decouples protocol from transport

## Lessons for Prism

1. Capabilities = references (no special machinery needed beyond lexical scoping)
2. Vat/turn model enables automatic transactions
3. Promise pipelining from day one -- single most powerful distributed optimization
4. Separate read vs. write capabilities (post/editor pattern)
5. Netlayer abstraction decouples CapTP from transport
6. Distributed GC must be acyclic for practical cross-language implementation
7. Sturdyrefs for persistence, live refs for active connections
8. OCapN interop as a goal (test suite exists)
