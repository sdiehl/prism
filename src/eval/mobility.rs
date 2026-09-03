//! The interpreter's half of the mobility envelope: freezing a portable,
//! single-use computation into bytes, and landing those bytes back into a
//! running machine somewhere else.
//!
//! Sealing takes the closure a placement handler was handed and builds the
//! `kont` a resumer would have built had the program suspended at exactly that
//! call: a stack holding one zero-argument application, about to return the
//! closure into it. Landing decodes such an envelope, checks it belongs to this
//! program, and re-enters the machine loop on it, which is why both live here
//! against `&mut Machine` rather than beside the value-returning builtins.
//!
//! Both halves answer a classification code rather than a message, for the same
//! reason the socket boundary does: the same failure has to be the same Prism
//! value on every host and on both tiers. `lib/std/Teleport.pr` is the one
//! reader of the table, and `runtime/prism_mobility.c` answers `UNSUPPORTED`
//! from it because a native binary has no interpreter to land a continuation in.
//!
//! The one thing neither half classifies is a host that promised an execution
//! identity and then could not produce one. That is not an outcome of moving a
//! computation, it is the host failing at something it said it could do, so it
//! travels as a fault carrying its cause rather than as a code the program is
//! asked to handle.

use std::rc::Rc;

use super::kont::{decode_kont, encode_kont, Kont, KontState, Portability};
use super::{Frame, Machine, Outcome, Rv, State};

// The classification codes, in step with the `#define`s in
// `runtime/prism_mobility.c` and with the `MoveError` constructors in
// `lib/std/Teleport.pr`.
const UNPORTABLE: i64 = 1;
const MALFORMED: i64 = 2;
const FOREIGN: i64 = 3;
const UNSUPPORTED: i64 = 4;
const UNCERTIFIED: i64 = 5;

fn ok(v: Rv) -> Rv {
    Rv::Data("Ok".into(), vec![v].into())
}

fn err(code: i64) -> Rv {
    Rv::Data("Err".into(), vec![Rv::Int(code)].into())
}

/// Freeze `work` into an envelope stamped with this program's execution
/// identity.
///
/// The envelope is the machine state a suspend at this point would have
/// captured: `work` about to be applied to no arguments, over the registers the
/// run has reached (the random stream and the observation count), so a landing
/// continues the same run rather than starting a fresh one. A capture that
/// cannot cross the boundary is refused here, by the `kont` codec, rather than
/// producing bytes that fail on the far side.
///
/// # Errors
/// Faults when this host armed mobility and then could not derive the digest.
/// A host that never offered mobility is a classified refusal instead, because
/// that is a fact about where the program runs rather than a broken promise.
pub(super) fn seal(m: &mut Machine<'_>, work: &Rv) -> Result<Rv, String> {
    let Some(bundle) = m.execution_identity()? else {
        return Ok(err(UNSUPPORTED));
    };
    // Exactly what `work()` would have done here: force the value, then apply
    // what comes back to no arguments. A `() -> a` is a thunk of a lambda, so
    // forcing it is evaluating that lambda; a value that is already a function
    // returns into the same pending application.
    let state = match work {
        Rv::Thunk(body, env) => KontState::Eval(body.clone(), env.clone()),
        _ => KontState::Ret(work.clone()),
    };
    let kont = Kont {
        bundle,
        // `prim_kont_encode` declares its parameter `@ {once, portable}`, so
        // reaching here at all means the compiler checked the closure's captures
        // at the call that produced `work`. That is the whole of the claim this
        // stamp makes, and it is why the stamp belongs here rather than in the
        // encoder, which cannot tell one caller from another.
        portable: Portability::Checked,
        stack: vec![Frame::Args(Rc::from([]), super::Env::default())],
        state,
        rng: m.rng,
        fn_name: m.fn_name,
        observed: m.observed,
        // The three fields a suspended run carries and a placed computation does
        // not. `exit` is empty because there is no pending exit at a `teleport`
        // call, which is mid-expression rather than at the end of a run. The tape
        // and the provenance list are empty because a recording belongs to the
        // host that is keeping it: `land` re-enters *this* machine's loop rather
        // than building a machine out of the envelope, which is exactly how
        // `resume_kont` differs, so a landing in this process keeps recording on
        // the tape it was already recording on, and a landing in another process
        // records on that host's, under that host's driver. Carrying the sealing
        // side's tape across would make the receiver replay observations it never
        // made. A recording transport, when there is one, records the frame at
        // the transport rather than inside it.
        exit: None,
        trace: Vec::new(),
        observations: Vec::new(),
    };
    // The codec names what it could not serialize, and that name is dropped here.
    // It is not lost: the capture contract is checked at compile time, where the
    // diagnostic names the binding and points at it in the source, so reaching
    // this arm at all means something got past a static check rather than that a
    // programmer needs to be told which capture was at fault. What a program can
    // act on is the classification, and `MoveError` carries no payload on purpose,
    // because a reason string would have to mean the same thing on a host that
    // never built this envelope.
    Ok(encode_kont(&kont).map_or_else(|_| err(UNPORTABLE), |bytes| ok(Rv::Buf(Rc::new(bytes)))))
}

/// Decode `envelope`, check it belongs to this program, and run it to
/// completion here.
///
/// Three questions are answered before a single step. Is this code's identity
/// mine: a continuation captured against other code would resolve its by-name
/// references against definitions that are not the ones it was compiled with.
/// Is the capture graph the one that was checked: the codec recomputes the
/// certificate's digest over the bytes it parsed, so an envelope edited in
/// flight is refused rather than reconstructed. And was anything checked at all:
/// a suspended run is not a placeable computation, whatever its bundle says, and
/// `teleport` is the only boundary that proves a closure may travel.
///
/// Output goes to this machine's sink from the landing point on, so the sealing
/// run's prefix followed by this suffix reproduces an uninterrupted run byte for
/// byte.
///
/// None of the three questions is "who sent this". A landed envelope is a
/// machine graph the sender chose, executed here with this program's full
/// capabilities; the frame's digests are unkeyed, so they establish that the
/// bytes are intact and that they belong to this program, never that a peer is
/// entitled to place work in it. A host that lands envelopes off a socket owns
/// that choice, which is why `lib/std/Teleport.pr` and the codec header say to
/// bind such a receiver to loopback or a trusted network.
///
/// # Errors
/// Propagates an evaluation fault raised after the landing point. A malformed
/// envelope, a foreign one, an uncertified one, and a host with no mobility are
/// classified answers rather than faults.
pub(super) fn land(m: &mut Machine<'_>, envelope: &Rv) -> Result<Rv, String> {
    let Rv::Buf(bytes) = envelope else {
        return Ok(err(MALFORMED));
    };
    let Some(bundle) = m.execution_identity()? else {
        return Ok(err(UNSUPPORTED));
    };
    let Ok(kont) = decode_kont(bytes) else {
        return Ok(err(MALFORMED));
    };
    if kont.bundle != bundle {
        return Ok(err(FOREIGN));
    }
    if kont.portable != Portability::Checked {
        return Ok(err(UNCERTIFIED));
    }
    // The registers the cut threads: the landed suffix continues the sealing
    // run's random stream and observation count, not this host's.
    let caller = m.fn_name;
    m.rng = kont.rng;
    m.fn_name = kont.fn_name;
    m.observed = kont.observed;
    let state = match kont.state {
        KontState::Eval(c, env) => State::Eval(c, env),
        KontState::Ret(v) => State::Ret(v),
    };
    let outcome = m.run_loop(kont.stack, state);
    // The landing host's own continuation resumes under its own name; the random
    // stream and observation count stay where the landed suffix left them,
    // because those did advance.
    m.fn_name = caller;
    match outcome? {
        Outcome::Done(_) => Ok(ok(Rv::Unit)),
        // No step budget is set on this machine's landing, so the loop cannot
        // pause inside one.
        Outcome::Suspended { .. } => Err("landed continuation paused unexpectedly".into()),
    }
}
