//! Record and replay observation machinery.
//!
//! The observation kinds, the tape modes that govern one run's capability I/O,
//! and the frame/event codecs the machine's observe sites share.

use std::rc::Rc;

use crate::core::builtins::Builtin;
use crate::debug::durable::DurableLog;
use crate::lineage::provenance::{
    CapOp, EventValue, OP_CLOCK_MONO_NOW, OP_CLOCK_WALL_NOW, OP_ENV_ARG, OP_ENV_ARGS_COUNT,
    OP_ENV_GETENV, OP_FS_APPEND_FILE, OP_FS_FILE_EXISTS, OP_FS_READ_FILE, OP_FS_READ_FILE_BYTES,
    OP_FS_REMOVE_FILE, OP_FS_WRITE_BYTES, OP_FS_WRITE_FILE, OP_PROCESS_SYSTEM,
};

use super::Rv;

/// One recorded observation on a program's execution: the result of a
/// capability read (an integer, a string, or a boolean) or an output boundary.
///
/// This is the in-memory form of a `.replay` frame; the string codec that makes
/// it durable lives in `crate::debug::trace`, mirroring `Replay.pr`'s tags
/// (I/S/B/O). A whole run's trace is the ordered list of these observations, and
/// determinism makes the list a complete, replayable record of the run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obs {
    Int(i64),
    Str(String),
    Bool(bool),
    Out,
}

/// How the interpreter's capability I/O is governed for one run.
///
/// `Live` performs real I/O (the ordinary path). `Record` performs real I/O and
/// logs every observation. `Replay` serves each capability read from a recorded
/// trace and re-performs outputs live, so a deterministic program reproduces its
/// original transcript byte for byte; an optional `budget` halts the run after
/// that many observations, which is the mechanism behind replay-to-N stepping.
///
/// `Durable` is the crash-safe form: the same observation stream, but persisted
/// to an on-disk [`DurableLog`] as it is produced, so a process killed mid-run
/// resumes byte-identically. It is the production form of `Replay.pr`'s `durable`
/// handler, moved onto the interpreter's observe sites and the atomic, index-
/// committed log substrate. It is reached only through the explicit durable-run
/// driver, never by an ordinary interpret/record/replay, so those paths and every
/// program's observation trace are untouched.
#[derive(Debug)]
pub enum Tape {
    Live,
    Record(Vec<Obs>),
    Replay {
        frames: Vec<Obs>,
        cursor: usize,
        budget: Option<usize>,
    },
    /// Replay the committed prefix (`frames`, up to `cursor`) with no real I/O,
    /// then perform each further observation live and append it to `log`,
    /// committing it durably before the run advances. `budget` halts the run
    /// after that many observations: the deterministic mid-run crash used to
    /// prove a resume continues byte-identically. A durable output is committed
    /// before it is emitted, and a committed output is dropped (not re-emitted)
    /// on resume, so an already-persisted output is never printed twice.
    Durable {
        log: DurableLog,
        frames: Vec<Obs>,
        cursor: usize,
        budget: Option<usize>,
    },
}

// The observation kind a capability read must yield, so a replayed trace that
// does not match the program (wrong variant at the cursor) is a detectable
// error rather than a silent divergence.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ObsKind {
    Int,
    Str,
    Bool,
    // A raw byte read (`read_bytes`). It has no valid-UTF-8 `Str` form, so it
    // rides the trace as a `Str` frame carrying lowercase hex, which keeps the
    // frame format (and the `Replay.pr` agreement) unchanged while still
    // round-tripping arbitrary bytes.
    Bytes,
}

// Lowercase hex, one frame's worth of bytes. Must stay byte-identical to
// `Data.Bytes.hex_encode`/`hex_decode`, since a byte read recorded by the
// interpreter and one recorded by `Replay.pr` are the same trace.
fn hex_encode_bytes(v: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(v.len() * 2);
    for &b in v {
        s.push(DIGITS[(b >> 4) as usize] as char);
        s.push(DIGITS[(b & 0xf) as usize] as char);
    }
    s
}

fn hex_decode_bytes(s: &str) -> Result<Vec<u8>, String> {
    let b = s.as_bytes();
    if !b.len().is_multiple_of(2) {
        return Err(format!("replay: odd-length hex byte frame {s:?}"));
    }
    let nib = |c: u8| -> Result<u8, String> {
        match c {
            b'0'..=b'9' => Ok(c - b'0'),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            _ => Err(format!("replay: non-hex byte frame {s:?}")),
        }
    };
    (0..b.len() / 2)
        .map(|i| Ok((nib(b[2 * i])? << 4) | nib(b[2 * i + 1])?))
        .collect()
}

// Log a real read's result as the matching observation frame.
pub(super) fn obs_of_rv(kind: ObsKind, v: &Rv) -> Result<Obs, String> {
    match (kind, v) {
        (ObsKind::Int, Rv::Int(n)) => Ok(Obs::Int(*n)),
        (ObsKind::Str, Rv::Str(s)) => Ok(Obs::Str(s.clone())),
        (ObsKind::Bool, Rv::Bool(b)) => Ok(Obs::Bool(*b)),
        (ObsKind::Bytes, Rv::Buf(v)) => Ok(Obs::Str(hex_encode_bytes(v))),
        _ => Err(format!(
            "record: capability read produced {v:?}, not a {kind:?}"
        )),
    }
}

// Why a recorded frame could not serve the read the program performed: either the
// frame is the wrong kind (a genuine program/trace divergence) or the frame itself
// is corrupt (a malformed byte payload). The two are distinct so replay can name a
// mismatch by event index while passing a corrupt-trace error through verbatim.
pub(super) enum FrameError {
    Kind,
    Malformed(String),
}

impl FrameError {
    // The user-facing message. A mismatch names the zero-based event index, the
    // operation the program expected at that point, and what the trace holds
    // instead; a malformed frame keeps its own decode error.
    pub(super) fn explain(self, index: usize, expected: &str, frame: &Obs) -> String {
        match self {
            Self::Malformed(m) => m,
            Self::Kind => format!(
                "replay: trace does not match program at event {index}: \
                 expected {expected}, but the recorded frame is {}",
                obs_label(frame)
            ),
        }
    }
}

// A human label for a recorded frame, for the "got" side of a mismatch message.
pub(super) const fn obs_label(frame: &Obs) -> &'static str {
    match frame {
        Obs::Int(_) => "an integer read",
        Obs::Str(_) => "a string read",
        Obs::Bool(_) => "a boolean read",
        Obs::Out => "an output",
    }
}

// Serve a recorded frame as a value, checking it is the kind the program asked
// for at this point in the trace.
pub(super) fn rv_of_obs(kind: ObsKind, frame: &Obs) -> Result<Rv, FrameError> {
    match (kind, frame) {
        (ObsKind::Int, Obs::Int(n)) => Ok(Rv::Int(*n)),
        (ObsKind::Str, Obs::Str(s)) => Ok(Rv::Str(s.clone())),
        (ObsKind::Bool, Obs::Bool(b)) => Ok(Rv::Bool(*b)),
        (ObsKind::Bytes, Obs::Str(s)) => hex_decode_bytes(s)
            .map(|b| Rv::Buf(Rc::new(b)))
            .map_err(FrameError::Malformed),
        _ => Err(FrameError::Kind),
    }
}

// The observation kind and canonical provenance operation label a capability
// `StrBuiltin` yields, or `None` for a builtin that is not a world read (so it
// stays on the ordinary pure path). The two facts travel together so the observe
// site records the frame and the provenance event from one lookup.
pub(super) const fn capability_obs(b: Builtin) -> Option<(ObsKind, CapOp)> {
    match b {
        Builtin::ReadFile => Some((ObsKind::Str, OP_FS_READ_FILE)),
        Builtin::Getenv => Some((ObsKind::Str, OP_ENV_GETENV)),
        Builtin::Arg => Some((ObsKind::Str, OP_ENV_ARG)),
        Builtin::ReadBytesFile => Some((ObsKind::Bytes, OP_FS_READ_FILE_BYTES)),
        Builtin::FileExists => Some((ObsKind::Bool, OP_FS_FILE_EXISTS)),
        Builtin::ArgsCount => Some((ObsKind::Int, OP_ENV_ARGS_COUNT)),
        Builtin::WallNow => Some((ObsKind::Int, OP_CLOCK_WALL_NOW)),
        Builtin::MonoNow => Some((ObsKind::Int, OP_CLOCK_MONO_NOW)),
        Builtin::System => Some((ObsKind::Int, OP_PROCESS_SYSTEM)),
        _ => None,
    }
}

// The provenance operation label a file-mutating `StrBuiltin` emits, or `None` for
// a builtin that mutates nothing. A write is an output observation, not a world
// read: it performs its effect and, when event capture is armed, records the path
// and content it committed. It is never a `.replay` tape frame, so the trace format
// and replay semantics are untouched.
pub(super) const fn write_obs(b: Builtin) -> Option<CapOp> {
    match b {
        Builtin::WriteFile => Some(OP_FS_WRITE_FILE),
        Builtin::WriteBytesFile => Some(OP_FS_WRITE_BYTES),
        Builtin::AppendFile => Some(OP_FS_APPEND_FILE),
        Builtin::RemoveFile => Some(OP_FS_REMOVE_FILE),
        _ => None,
    }
}

// The protocol value for a runtime value, at an observation boundary. A byte
// buffer records its raw bytes (the hex form is a trace-frame detail, not the
// value's identity); values with no scalar form record as `Unit`.
pub(super) fn event_value_of_rv(v: &Rv) -> EventValue {
    match v {
        Rv::Int(n) => EventValue::Int(*n),
        Rv::Str(s) => EventValue::Str(s.clone()),
        Rv::Bool(b) => EventValue::Bool(*b),
        Rv::Buf(bytes) => EventValue::Bytes(bytes.to_vec()),
        _ => EventValue::Unit,
    }
}

// The protocol values for a capability's argument list.
pub(super) fn event_args(vals: &[Rv]) -> Vec<EventValue> {
    vals.iter().map(event_value_of_rv).collect()
}
