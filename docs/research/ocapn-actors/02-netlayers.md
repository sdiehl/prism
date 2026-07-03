# Netlayers: Transport Abstraction for CapTP

## Motivation

CapTP messages need a bidirectional, ordered, unreliable (or reliable) byte stream
between two vats. The **netlayer** XXX link abstraction decouples CapTP from any specific
transport — TCP, TLS, Tor, libp2p, IBC, or (for testing and embedding) a pair of
file descriptors or in-process channels.

## The Semantic Boundary: `Eventual` vs `Async`

Cross-vat message arrival is inherently non-deterministic. A vat author decides the order among a set of non-deterministically ordered incoming messages. We separate a vat's internal structured concurrency (`Async`) from eventual message delivery from the network (`Eventual`):

- **`Async`**: Deterministic, structured concurrency *inside* a vat (fork/join/channels).
- **`Eventual`**: Non-deterministic message arrival *between* vats (deliver/turn).

The `Eventual` effect captures this: it is a capability the vat's event loop holds.

```prism
-- | Eventual delivery from the network.
-- |
-- | Messages arrive at a vat in non-deterministic order. The vat's event loop
-- | discharges this effect by deciding which incoming message to deliver next.
-- | Unlike `Async` (structured concurrency within a vat), `Eventual` models the
-- | vat boundary: the peer's sends become our deliveries, and we cannot predict
-- | their arrival order.
pub effect Eventual(a) {
  ctl deliver(a) : Unit
}
```

## Interface

A netlayer provides outbound and inbound streams. In (a patch to XXX) Prism's standard library, the `Netlayer` structure abstracts this. For instance, testing over channels:

```prism
import Concurrent (..)

-- | A bidirectional transport: one channel to send, one to receive.
pub type Netlayer = Netlayer {
  outbound : Chan,
  inbound : Chan
}

-- | Send a message on the netlayer's outbound channel.
pub fn netlayer_send(nl : Netlayer, msg : a) : !{Async(a)} Unit =
  send(nl.outbound, msg)

-- | Receive the next message from the netlayer's inbound channel.
pub fn netlayer_recv(nl : Netlayer) : !{Async(a)} a =
  recv(nl.inbound)
```

## Testing with Real File Descriptors (FDS)

To accurately simulate two vats across a network without assuming a shared internal channel scheduler, we can use a Unix Domain Socket pair and connect them to two separate interpreter instances using `prism::interpret_io_at`.

### Prism Node Programs

We write isolated Prism programs that use standard I/O (mapped to the FDS).

**`tests/netlayer_fd/node_a.pr`**:
```prism
import Concurrent (..)

pub type Netlayer = Netlayer { fd: Int }
pub fn create_fd_netlayer() : Netlayer = Netlayer { fd = 0 }

pub fn netlayer_send(nl : Netlayer, msg : String) : !{IO} Unit =
  println(msg)

pub fn netlayer_recv(nl : Netlayer) : !{Console, IO} String =
  read_line()

fn scene() : !{Console, IO} String =
  let nl = create_fd_netlayer()
  eprintln("[Node A] Sending ping...")
  netlayer_send(nl, "ping")
  let reply = netlayer_recv(nl)
  eprintln("[Node A] Received: {reply}")
  "done"

fn main() =
  let res = scene()
  eprintln("[Node A] Exiting with: {res}")
```

**`tests/netlayer_fd/node_b.pr`** is symmetric, waiting to receive before sending.

### Rust Test Harness

We bind a `UnixStream::pair()` to the interpreter's I/O environment (`out_sink` and `input`), spawning Node B in a separate thread.

```rust
#[test]
fn test_fd_netlayer() {
    let (mut a_write, mut b_write) = UnixStream::pair().unwrap();
    let mut a_read = BufReader::new(a_write.try_clone().unwrap());
    let mut b_read = BufReader::new(b_write.try_clone().unwrap());

    let node_a_src = prism::with_prelude(include_str!("netlayer_fd/node_a.pr"));
    let node_b_src = prism::with_prelude(include_str!("netlayer_fd/node_b.pr"));

    let handle = thread::spawn(move || {
        prism::interpret_io_at(&node_b_src, Path::new("."), &mut b_write, &mut b_read);
    });

    prism::interpret_io_at(&node_a_src, Path::new("."), &mut a_write, &mut a_read);

    handle.join().unwrap();
}
```

### Running the Test

Since the native Prism binary relies on LLVM (provided by the Nix flake), run the test using the Nix development shell:

```bash
nix develop -c just test-netlayer-fd
```

This outputs:

```text
running 1 test
Node A started.
Node B thread started.
[Node B] Waiting for message...
[Node A] Sending ping...
[Node B] Received: ping
[Node B] Sending pong...
[Node B] Exiting with: done
[Node A] Received: pong
[Node A] Exiting with: done
test test_fd_netlayer ... ok
```

## Layered Architecture

```
┌─────────────────────────────┐
│        CapTP Session        │
│  (op:deliver, op:listen, …) │
├─────────────────────────────┤
│  netlayer_send / netlayer_recv
├─────────────────────────────┤
│        Netlayer             │
│  (channel-pair | TCP | UDS) │
└─────────────────────────────┘
```

CapTP never touches the transport directly. `op:deliver` and `op:listen` are CapTP semantics; the netlayer only transports the serialized bytes. This lets us swap real networking in later without changing a line of CapTP logic.

## Future Netlayer Implementations

| Netlayer | Use Case | Status |
|---|---|---|
| UDS (File Descriptors) | Cross-process isolated testing | Done |
| Channel pair | In-process shared-scheduler testing | Done |
| TCP sockets | Dev, LAN | Future |
| Tor onion service | Production anonymity | Future |
| WebSocket | Browser embedding (WASM) | Future |
