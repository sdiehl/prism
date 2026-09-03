//! The interpreter's half of the stream-socket boundary (`runtime/prism_net.c`
//! is the native half). Sockets live in a table keyed by a logical handle drawn
//! from a counter starting at 1, so the nth socket a program opens is handle n
//! in both tiers whatever descriptor the OS hands out, and a recorded
//! observation names the same socket either way.
//!
//! The table belongs to one run on one thread: it is thread-local so concurrent
//! tests get independent handle spaces, and [`reset`] hands it to a new machine
//! so a run that ended holding sockets neither leaks them into the next program
//! on that thread nor shifts its handle numbering.

// On wasm32-unknown-unknown, std::net's socket types are unsupported zero-sized
// stubs (every constructor fails at runtime), which makes the handle table's
// value type zero-sized there. The table logic is target-independent, so the
// zero-sized-value lint is browser-target noise rather than a design signal.
#![cfg_attr(target_arch = "wasm32", allow(clippy::zero_sized_map_values))]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io::{ErrorKind, Read as _, Write as _};
use std::net::{TcpListener, TcpStream};

use super::Rv;

// The classification codes, in step with the `#define`s at the top of
// `runtime/prism_net.c` and with the `NetError` constructors in `lib/std/Net.pr`.
const OTHER: i64 = 0;
const REFUSED: i64 = 1;
const UNREACHABLE: i64 = 2;
const TIMED_OUT: i64 = 3;
const RESET: i64 = 4;
const IN_USE: i64 = 5;
const INVALID: i64 = 6;
const CLOSED: i64 = 7;
const DENIED: i64 = 8;
const LIMIT: i64 = 9;

// The same bound the native table declares, so a program that exhausts the
// socket table fails at the same point in both tiers.
const SLOTS: usize = 256;

enum Socket {
    Listener(TcpListener),
    Stream(TcpStream),
}

struct Table {
    next: i64,
    open: BTreeMap<i64, Socket>,
}

impl Table {
    // The only way to build one. Numbering starts at 1 because 0 is the handle no
    // socket ever has, so the derived `Default` would hand out a value the rest of
    // this module treats as impossible; there is one constructor rather than a
    // literal at each site so that invariant has one place to live.
    const fn new() -> Self {
        Self {
            next: 1,
            open: BTreeMap::new(),
        }
    }
}

thread_local! {
    static TABLE: RefCell<Table> = const { RefCell::new(Table::new()) };
}

/// Give the socket table to a new run: close whatever the last one left open and
/// start handle numbering again at 1.
///
/// A landed continuation gets a fresh table too, which is the answer a program
/// that carried a handle across the boundary deserves: it observes `Closed`
/// rather than reaching whatever socket this process opened. The type system
/// gets there first (`Listener` and `Stream` are opaque, so `@ portable` refuses
/// to seal one), and this is what backs that refusal up if a raw number ever
/// finds another way across.
pub(super) fn reset() {
    TABLE.with_borrow_mut(|t| *t = Table::new());
}

/// Classify a host error the way the native runtime classifies the `errno`
/// behind it: the standard library reads the same `errno` values the C switch
/// does, so the two agree wherever a kind exists. Descriptor exhaustion has no
/// stable `ErrorKind`, so the interpreter answers `Other` where native answers
/// `Limit`; branching on that difference is branching on how many descriptors
/// the host had left.
fn code_of(e: &std::io::Error) -> i64 {
    match e.kind() {
        ErrorKind::ConnectionRefused => REFUSED,
        ErrorKind::HostUnreachable | ErrorKind::NetworkUnreachable | ErrorKind::NetworkDown => {
            UNREACHABLE
        }
        ErrorKind::TimedOut => TIMED_OUT,
        ErrorKind::ConnectionReset | ErrorKind::ConnectionAborted | ErrorKind::BrokenPipe => RESET,
        ErrorKind::AddrInUse | ErrorKind::AddrNotAvailable => IN_USE,
        ErrorKind::InvalidInput | ErrorKind::Unsupported => INVALID,
        ErrorKind::NotConnected => CLOSED,
        ErrorKind::PermissionDenied => DENIED,
        ErrorKind::OutOfMemory => LIMIT,
        _ => OTHER,
    }
}

fn ok(v: Rv) -> Rv {
    Rv::Data("Ok".into(), vec![v].into())
}

fn err(code: i64) -> Rv {
    Rv::Data("Err".into(), vec![Rv::Int(code)].into())
}

fn failed(e: &std::io::Error) -> Rv {
    err(code_of(e))
}

// Take a slot and return its handle, or `None` (dropping the socket, which
// closes it) when the table is full: a socket that cannot be named must not
// be left open.
fn intern(t: &mut Table, s: Socket) -> Option<i64> {
    if t.open.len() >= SLOTS {
        return None;
    }
    let h = t.next;
    t.next += 1;
    t.open.insert(h, s);
    Some(h)
}

fn interned(t: &mut Table, s: Socket) -> Rv {
    intern(t, s).map_or_else(|| err(LIMIT), |h| ok(Rv::Int(h)))
}

/// The host must be given explicitly, even for a listener: see the matching note
/// in `prism_net_resolve`. A port outside the 16-bit range is invalid rather
/// than truncated.
fn endpoint(host: &str, port: i64) -> Option<(String, u16)> {
    if host.is_empty() {
        return None;
    }
    u16::try_from(port).ok().map(|p| (host.to_string(), p))
}

/// `listen`. The requested accept-queue depth is advisory in both tiers: native
/// clamps it into what the host accepts and the kernel may still pick another,
/// and the standard library picks its own here. What a program can observe is
/// which connections it accepts and in what order, never how deep the queue
/// behind them was.
pub(super) fn listen(host: &str, port: i64, _backlog: i64) -> Rv {
    let Some(addr) = endpoint(host, port) else {
        return err(INVALID);
    };
    match TcpListener::bind(addr) {
        Ok(l) => TABLE.with_borrow_mut(|t| interned(t, Socket::Listener(l))),
        Err(e) => failed(&e),
    }
}

pub(super) fn accept(handle: i64) -> Rv {
    let accepted = TABLE.with_borrow(|t| match t.open.get(&handle) {
        Some(Socket::Listener(l)) => Some(l.accept().map(|(s, _)| s)),
        // A stream is a live handle that cannot accept. Native answers `Closed`
        // here too: its table carries the same listener/stream distinction, so
        // the syscall is never reached with a connected descriptor.
        Some(Socket::Stream(_)) | None => None,
    });
    match accepted {
        Some(Ok(s)) => TABLE.with_borrow_mut(|t| interned(t, Socket::Stream(s))),
        Some(Err(e)) => failed(&e),
        None => err(CLOSED),
    }
}

pub(super) fn connect(host: &str, port: i64) -> Rv {
    let Some(addr) = endpoint(host, port) else {
        return err(INVALID);
    };
    match TcpStream::connect(addr) {
        Ok(s) => TABLE.with_borrow_mut(|t| interned(t, Socket::Stream(s))),
        Err(e) => failed(&e),
    }
}

/// At most `max` bytes, however many have arrived. An empty buffer is the peer's
/// orderly close, which `Net.pr` reads as `End`, so a read that could not have
/// returned bytes must not answer with one: a non-positive `max` is `Invalid`
/// rather than a false end of stream.
///
/// The handle is judged before the size, as it is in every operation here and in
/// the native runtime: whether this call applies to this socket at all is the
/// first question, so a call that is wrong in both ways is `Closed` in both
/// tiers rather than whichever check that tier happened to run first.
pub(super) fn recv(handle: i64, max: i64) -> Rv {
    TABLE.with_borrow_mut(|t| {
        let Some(Socket::Stream(s)) = t.open.get_mut(&handle) else {
            return err(CLOSED);
        };
        let Ok(cap) = usize::try_from(max) else {
            return err(INVALID);
        };
        if cap == 0 {
            return err(INVALID);
        }
        // The size is the program's to choose, so the allocation is fallible:
        // an unmeetable request is `Limit`, which is what the native tier's
        // failed `malloc` answers, and never an abort.
        let mut buf = Vec::new();
        if buf.try_reserve_exact(cap).is_err() {
            return err(LIMIT);
        }
        buf.resize(cap, 0u8);
        loop {
            match s.read(&mut buf) {
                Ok(n) => {
                    buf.truncate(n);
                    return ok(Rv::Buf(buf.into()));
                }
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return failed(&e),
            }
        }
    })
}

/// Write what the kernel accepts from `off` onward and report how much that was;
/// a short write is an ordinary outcome, not an error, and the caller advances.
pub(super) fn send(handle: i64, bytes: &[u8], off: i64) -> Rv {
    TABLE.with_borrow_mut(|t| {
        let Some(Socket::Stream(s)) = t.open.get_mut(&handle) else {
            return err(CLOSED);
        };
        let Ok(from) = usize::try_from(off) else {
            return err(INVALID);
        };
        if from > bytes.len() {
            return err(INVALID);
        }
        let rest = &bytes[from..];
        if rest.is_empty() {
            return ok(Rv::Int(0));
        }
        loop {
            match s.write(rest) {
                Ok(n) => return ok(Rv::Int(i64::try_from(n).unwrap_or(i64::MAX))),
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return failed(&e),
            }
        }
    })
}

/// Drop the socket, which closes it. The handle is retired either way, so a
/// second close reports a closed handle rather than acting on a reissued one.
pub(super) fn close(handle: i64) -> Rv {
    TABLE.with_borrow_mut(|t| {
        t.open
            .remove(&handle)
            .map_or_else(|| err(CLOSED), |_| ok(Rv::Unit))
    })
}

/// `SocketAddr`'s rendering is "host:port" with an IPv6 host in brackets, which
/// is the spelling `prism_net_addr_text` builds by hand for the native tier.
fn addr(handle: i64, local: bool) -> Rv {
    TABLE.with_borrow(|t| {
        let found = match t.open.get(&handle) {
            Some(Socket::Listener(l)) if local => Some(l.local_addr()),
            Some(Socket::Stream(s)) => Some(if local { s.local_addr() } else { s.peer_addr() }),
            // A listener has no peer.
            Some(Socket::Listener(_)) | None => None,
        };
        match found {
            Some(Ok(a)) => ok(Rv::Str(a.to_string())),
            Some(Err(e)) => failed(&e),
            None => err(CLOSED),
        }
    })
}

pub(super) fn local_addr(handle: i64) -> Rv {
    addr(handle, true)
}

pub(super) fn peer_addr(handle: i64) -> Rv {
    addr(handle, false)
}
