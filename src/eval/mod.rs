use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;
use std::rc::Rc;
use std::sync::OnceLock;
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use std::{env, fs, io, mem};

use num_bigint::{BigInt, Sign};

use crate::core::builtins::{Builtin, FloatOp};
// Short aliases for the two builtin-op enums, used to keep their `match` arms
// readable in `float_builtin`/`str_builtin`.
use crate::core::{Comp, Core, CoreFn, CoreOp, CorePat, IoOp, NegLane, Value};
use crate::names::ENTRY_POINT;
use crate::store::bridge;
use crate::sym::Sym;
use crate::types::{CONS, NIL};
use Builtin as B;
use FloatOp as F;

/// The `kont`-kind wire codec.
///
/// Serializes a live interpreter continuation (the frame stack, the lowered node
/// graph, and the runtime values it holds) as a portable envelope, and reads one
/// back.
pub mod kont;

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
#[derive(Debug)]
pub enum Tape {
    Live,
    Record(Vec<Obs>),
    Replay {
        frames: Vec<Obs>,
        cursor: usize,
        budget: Option<usize>,
    },
}

// The observation kind a capability read must yield, so a replayed trace that
// does not match the program (wrong variant at the cursor) is a detectable
// error rather than a silent divergence.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ObsKind {
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
fn obs_of_rv(kind: ObsKind, v: &Rv) -> Result<Obs, String> {
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

// Serve a recorded frame as a value, checking it is the kind the program asked
// for at this point in the trace.
fn rv_of_obs(kind: ObsKind, frame: &Obs) -> Result<Rv, String> {
    match (kind, frame) {
        (ObsKind::Int, Obs::Int(n)) => Ok(Rv::Int(*n)),
        (ObsKind::Str, Obs::Str(s)) => Ok(Rv::Str(s.clone())),
        (ObsKind::Bool, Obs::Bool(b)) => Ok(Rv::Bool(*b)),
        (ObsKind::Bytes, Obs::Str(s)) => Ok(Rv::Buf(Rc::new(hex_decode_bytes(s)?))),
        _ => Err(format!(
            "replay: trace does not match program (expected a {kind:?})"
        )),
    }
}

// The observation kind a capability `StrBuiltin` yields, or `None` for a builtin
// that is not a world read (so it stays on the ordinary pure path).
const fn capability_kind(b: Builtin) -> Option<ObsKind> {
    match b {
        Builtin::ReadFile | Builtin::Getenv | Builtin::Arg => Some(ObsKind::Str),
        Builtin::ReadBytesFile => Some(ObsKind::Bytes),
        Builtin::FileExists => Some(ObsKind::Bool),
        Builtin::ArgsCount | Builtin::WallNow | Builtin::MonoNow => Some(ObsKind::Int),
        _ => None,
    }
}

// How values that have no surface syntax render in `show`/`repr`. `print` goes
// through `show`, so these must stay byte-identical to the native runtime's own
// output; keeping them as named constants makes that contract changeable in one
// place rather than as ad-hoc literals.
const UNIT_REPR: &str = "()";
const FUNCTION_REPR: &str = "<function>";
const CONTINUATION_REPR: &str = "<continuation>";

#[derive(Clone, Debug)]
pub enum Rv {
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Big(BigInt),
    Closure(Rc<[Sym]>, Cmp, Env),
    Thunk(Cmp, Env),
    Data(Sym, Fields),
    Tuple(Fields),
    Array(Fields),
    // An unboxed byte buffer, the storage under `Bytes`. Held as raw bytes (not
    // boxed `Rv`s) so it threads byte-for-byte identically to the native buffer
    // cell; shared via `Rc` for O(1) clone, copied on write for value semantics,
    // mirroring the runtime's rc==1 in-place / shared-copy discipline.
    Buf(Rc<Vec<u8>>),
    Resume(Rc<[Frame]>),
}

// Constructor payloads share structure via Rc, so cloning a value out of an env
// is O(1), not a deep copy. Drop drains children through a worklist rather than
// recursive drop glue, so freeing a deep structure cannot overflow the Rust
// stack (mirroring the C runtime's iterative prism_rc_dec).
#[derive(Clone, Debug)]
pub struct Fields(Rc<Vec<Rv>>);

impl std::ops::Deref for Fields {
    type Target = [Rv];
    fn deref(&self) -> &[Rv] {
        &self.0
    }
}

impl From<Vec<Rv>> for Fields {
    fn from(vs: Vec<Rv>) -> Self {
        Self(Rc::new(vs))
    }
}

impl Drop for Fields {
    fn drop(&mut self) {
        let Some(vs) = Rc::get_mut(&mut self.0) else {
            return;
        };
        let mut work = mem::take(vs);
        let mut i = 0;
        while i < work.len() {
            if let Rv::Data(_, fs) | Rv::Tuple(fs) = &mut work[i] {
                if let Some(inner) = Rc::get_mut(&mut fs.0) {
                    let mut inner = mem::take(inner);
                    work.append(&mut inner);
                }
            }
            i += 1;
        }
    }
}

type Env = Rc<BTreeMap<Sym, Rv>>;
pub type Cmp = Rc<Node>;

// Core lowered once into Rc-linked nodes so the machine can hold subterms in
// heap frames without deep-cloning them on every step.
#[derive(Debug)]
pub enum Node {
    Return(Atom),
    Bind(Cmp, Sym, Cmp),
    Force(Atom),
    Lam(Rc<[Sym]>, Cmp),
    App(Cmp, Rc<[Atom]>),
    If(Atom, Cmp, Cmp),
    Prim(CoreOp, Atom, Atom),
    Call(Sym, Vec<Atom>),
    Print(Atom),
    PrintNl,
    ReadInt,
    ReadLine,
    Rand,
    Srand(Atom),
    Error(Atom),
    Case(Atom, Vec<(CorePat, Cmp)>),
    FloatBuiltin(FloatOp, Atom),
    Neg(NegLane, Atom),
    Do(Sym, Vec<Atom>),
    Handle(Rc<HandleInfo>),
    Mask(Rc<[Sym]>, Cmp),
    StrBuiltin(Builtin, Vec<Atom>),
}

#[derive(Debug)]
pub enum Atom {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Thunk(Cmp),
    Ctor(Sym, Vec<Self>),
    Tuple(Vec<Self>),
}

#[derive(Debug)]
pub struct HandleInfo {
    body: Cmp,
    ops: BTreeMap<Sym, (Vec<Sym>, Sym, Cmp)>,
    return_var: Option<Sym>,
    return_body: Option<Cmp>,
}

// Pending work lives on a heap stack of frames, so object-program recursion
// never grows the Rust call stack. A captured continuation is the slice of
// frames between a `do` and its handler (handler included: deep semantics);
// resuming pushes a clone of that slice back, which keeps resume multishot.
#[derive(Clone, Debug)]
pub enum Frame {
    Bind(Sym, Cmp, Env),
    Args(Rc<[Atom]>, Env),
    Restore(Sym),
    Handle(Rc<HandleInfo>, Env),
    Mask(Rc<[Sym]>),
}

enum State {
    Eval(Cmp, Env),
    Ret(Rv),
}

// How a run of the machine loop ended: with a final value, or paused at a step
// budget with its whole pending state (the frame stack and the next transition)
// still live, ready to be snapshotted into a `kont` envelope or resumed in place.
enum Outcome {
    Done(Rv),
    Suspended { stack: Vec<Frame>, state: State },
}

fn lower(c: &Comp) -> Cmp {
    let mut binds = Vec::new();
    let mut cur = c;
    while let Comp::Bind(m, x, n) = cur {
        binds.push((lower(m), *x));
        cur = n;
    }
    let mut acc = Rc::new(node(cur));
    for (m, x) in binds.into_iter().rev() {
        acc = Rc::new(Node::Bind(m, x, acc));
    }
    acc
}

fn node(c: &Comp) -> Node {
    match c {
        Comp::Return(v) => Node::Return(atom_of(v)),
        Comp::Bind(m, x, n) => Node::Bind(lower(m), *x, lower(n)),
        Comp::Force(v) => Node::Force(atom_of(v)),
        Comp::Lam(ps, b) => Node::Lam(Rc::from(ps.as_slice()), lower(b)),
        Comp::App(m, args) => Node::App(lower(m), args.iter().map(atom_of).collect()),
        Comp::If(v, t, e) => Node::If(atom_of(v), lower(t), lower(e)),
        Comp::Prim(op, a, b) => Node::Prim(*op, atom_of(a), atom_of(b)),
        Comp::Call(n, args) => Node::Call(*n, args.iter().map(atom_of).collect()),
        Comp::Io(op, args) => match op {
            IoOp::Print | IoOp::PrintF | IoOp::PrintS => Node::Print(atom_of(&args[0])),
            IoOp::PrintNl => Node::PrintNl,
            IoOp::ReadInt => Node::ReadInt,
            IoOp::ReadLine => Node::ReadLine,
            IoOp::Rand => Node::Rand,
            IoOp::Srand => Node::Srand(atom_of(&args[0])),
        },
        Comp::Error(v) => Node::Error(atom_of(v)),
        Comp::Case(v, arms) => Node::Case(
            atom_of(v),
            arms.iter().map(|(p, b)| (p.clone(), lower(b))).collect(),
        ),
        Comp::FloatBuiltin(n, v) => Node::FloatBuiltin(*n, atom_of(v)),
        Comp::Neg(l, v) => Node::Neg(*l, atom_of(v)),
        Comp::Do(op, args) => Node::Do(*op, args.iter().map(atom_of).collect()),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Node::Handle(Rc::new(HandleInfo {
            body: lower(body),
            ops: ops
                .iter()
                .map(|op| (op.name, (op.params.clone(), op.resume, lower(&op.body))))
                .collect(),
            return_var: *return_var,
            return_body: return_body.as_deref().map(lower),
        })),
        Comp::Mask(ops, b) => Node::Mask(Rc::from(ops.as_slice()), lower(b)),
        Comp::StrBuiltin(n, args) => Node::StrBuiltin(*n, args.iter().map(atom_of).collect()),
        // The interpreter runs un-lowered core; Dup/Drop/WithReuse/Reuse and the
        // mutable-cell Ref ops are injected only by codegen-side lowering (RC
        // reuse, var erasure) and must never reach here. Masking them to a silent
        // sink would hide the invariant breaking.
        Comp::Dup(_)
        | Comp::Drop(_)
        | Comp::WithReuse { .. }
        | Comp::Reuse(..)
        | Comp::RefNew(_)
        | Comp::RefGet(_)
        | Comp::RefSet(..) => {
            unreachable!("lowering-only node reached the interpreter; it runs un-lowered core")
        }
    }
}

fn atom_of(v: &Value) -> Atom {
    match v {
        Value::Var(x) => Atom::Var(*x),
        Value::Int(n) => Atom::Int(*n),
        Value::I64(n) => Atom::I64(*n),
        Value::U64(n) => Atom::U64(*n),
        Value::Float(f) => Atom::Float(*f),
        Value::Bool(b) => Atom::Bool(*b),
        Value::Unit => Atom::Unit,
        Value::Str(s) => Atom::Str(s.clone()),
        Value::Thunk(c) => Atom::Thunk(lower(c)),
        Value::Ctor(n, _, vs) => Atom::Ctor(*n, vs.iter().map(atom_of).collect()),
        Value::Tuple(vs) => Atom::Tuple(vs.iter().map(atom_of).collect()),
    }
}

impl Rv {
    /// Runtime shape tag. `print`/`show` dispatch on this, so the test corpus
    /// must exercise a direct `print` of each printable kind (see the
    /// `print_kind_coverage` oracle) or a backend mishandling of one shape can
    /// hide behind cases that only ever print strings.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Int(_) => "Int",
            Self::I64(_) => "I64",
            Self::U64(_) => "U64",
            Self::Float(_) => "Float",
            Self::Bool(_) => "Bool",
            Self::Unit => "Unit",
            Self::Str(_) => "Str",
            Self::Big(_) => "Big",
            Self::Closure(..) => "Closure",
            Self::Thunk(..) => "Thunk",
            Self::Data(..) => "Data",
            Self::Tuple(_) => "Tuple",
            Self::Array(_) => "Array",
            Self::Buf(_) => "Buf",
            Self::Resume(_) => "Resume",
        }
    }

    #[must_use]
    pub fn show(&self) -> String {
        self.render(false)
    }

    // Like `show`, but renders a value as it would be written as a literal:
    // strings quoted and escaped, including strings nested in lists, tuples, and
    // constructors. Used for result display (the REPL), where a bare `foo` is
    // ambiguous with an identifier; `print` keeps using `show` for raw output so
    // the backends stay byte-identical.
    #[must_use]
    pub fn repr(&self) -> String {
        self.render(true)
    }

    // The shared body of `show`/`repr`: `quote` only affects how strings render
    // (quoted and escaped vs raw), and it threads through list/tuple/constructor
    // fields. Arrays always render their elements unquoted (`repr` of an array
    // historically deferred to `show`), so the `Array` arm recurses via `show`.
    fn render(&self, quote: bool) -> String {
        match self {
            Self::Int(n) | Self::I64(n) => n.to_string(),
            Self::U64(n) => n.to_string(),
            Self::Float(f) => fmt_g(*f),
            Self::Bool(b) => b.to_string(),
            Self::Unit => UNIT_REPR.into(),
            Self::Str(s) if quote => format!("{s:?}"),
            Self::Str(s) => s.clone(),
            Self::Big(n) => n.to_string(),
            Self::Closure(..) | Self::Thunk(..) => FUNCTION_REPR.into(),
            Self::Resume(..) => CONTINUATION_REPR.into(),
            Self::Data(name, fs) => match self.list_elems() {
                Some(es) => {
                    let es: Vec<_> = es.iter().map(|e| e.render(quote)).collect();
                    format!("[{}]", es.join(", "))
                }
                None if fs.is_empty() => name.to_string(),
                None => {
                    let fs: Vec<_> = fs.iter().map(|f| f.render(quote)).collect();
                    format!("{name}({})", fs.join(", "))
                }
            },
            Self::Tuple(fs) => {
                let fs: Vec<_> = fs.iter().map(|f| f.render(quote)).collect();
                format!("({})", fs.join(", "))
            }
            Self::Array(es) => {
                let es: Vec<_> = es.iter().map(Self::show).collect();
                format!("[|{}|]", es.join(", "))
            }
            // A raw buffer has no surface literal; render its bytes as lowercase
            // hex for debugging. Normal programs print a `Bytes` through its
            // stdlib `Show`, never a bare buffer through this path.
            Self::Buf(bytes) => {
                let mut s = String::from("buf\"");
                for b in bytes.iter() {
                    let _ = write!(s, "{b:02x}");
                }
                s.push('"');
                s
            }
        }
    }

    fn list_elems(&self) -> Option<Vec<&Self>> {
        let mut es = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Self::Data(n, fs) if n == NIL && fs.is_empty() => return Some(es),
                Self::Data(n, fs) if n == CONS && fs.len() == 2 => {
                    es.push(&fs[0]);
                    cur = &fs[1];
                }
                _ => return None,
            }
        }
    }
}

// Output and input are host-supplied so the interpreter never touches real stdio
// itself: as the differential oracle and the wasm engine it must capture the
// transcript, while the native CLI streams to a real terminal. `out_sink`
// receives `print`/`println` bytes; `input` feeds `read_int`/`read_line`.
pub struct Machine<'a> {
    fns: BTreeMap<Sym, (Rc<[Sym]>, Cmp)>,
    pub out: Vec<Rv>,
    pub term: String,
    rng: u64,
    fn_name: Sym,
    out_sink: &'a mut dyn io::Write,
    input: &'a mut dyn io::BufRead,
    // Set by `exit(n)`: evaluation unwinds and the host maps it to a process
    // exit (CLI) or a returned status (REPL/wasm), never a `process::exit` here.
    exit: Option<i32>,
    // Governs capability I/O for record/replay/debug. `Live` is the ordinary
    // path (no behavior change). See [`Tape`].
    tape: Tape,
    // Observations performed so far, and whether the run stopped at a replay
    // budget. `halted` unwinds like `exit`, so replay-to-N stops in constant
    // stack without special-casing every frame.
    observed: usize,
    halted: bool,
    // Suspension: `step_budget` pauses the loop after that many machine steps (a
    // whole-program checkpoint), `steps` counts them. `None` is the ordinary
    // unbounded run. Steps are pure state transitions, so a given budget stops the
    // machine at a deterministic point, the basis of the `kont` snapshot.
    step_budget: Option<usize>,
    steps: usize,
}

// The borrowed `dyn Write`/`dyn BufRead` handles are not `Debug`; show only the
// captured transcript state, which is what a dump wants anyway.
impl std::fmt::Debug for Machine<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Machine")
            .field("out", &self.out)
            .field("term", &self.term)
            .field("exit", &self.exit)
            .finish_non_exhaustive()
    }
}

#[derive(Debug)]
pub struct Run {
    pub value: Rv,
    pub out: Vec<Rv>,
    pub term: String,
    // `Some(code)` when the program called `exit(code)`; the host decides what
    // a process exit means in its context.
    pub exit: Option<i32>,
}

// SplitMix64 default seed, shared with the C runtime so the interpreter and
// native backends produce identical streams from an unseeded `rand`.
const DEFAULT_SEED: u64 = 0x9E37_79B9_7F4A_7C15;

// SplitMix64's Weyl-sequence increment (the "gamma", 2^64 / golden ratio). This
// happens to equal the default seed but plays a distinct role: it advances the
// internal state on every draw.
const SPLITMIX_GAMMA: u64 = 0x9E37_79B9_7F4A_7C15;

// The C runtime's `prism_show_float_prec` formats `%.*f` into a 64-byte buffer,
// so it can emit at most 63 characters. The interpreter mirrors that cap to stay
// byte-identical with the native backend.
const RT_FLOAT_PREC_MAX_CHARS: usize = 63;

const fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(SPLITMIX_GAMMA);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

impl<'a> Machine<'a> {
    #[must_use]
    pub fn new(
        globals: &BTreeMap<Sym, CoreFn>,
        out_sink: &'a mut dyn io::Write,
        input: &'a mut dyn io::BufRead,
    ) -> Self {
        Self {
            fns: globals
                .iter()
                .map(|(k, f)| (*k, (Rc::from(f.params.as_slice()), lower(&f.body))))
                .collect(),
            out: Vec::new(),
            term: String::new(),
            rng: DEFAULT_SEED,
            fn_name: ENTRY_POINT.into(),
            out_sink,
            input,
            exit: None,
            tape: Tape::Live,
            observed: 0,
            halted: false,
            step_budget: None,
            steps: 0,
        }
    }

    /// Governs this machine's capability I/O for record/replay/debug.
    pub fn set_tape(&mut self, tape: Tape) {
        self.tape = tape;
    }

    // True when a replay budget is set and already reached, so the next
    // observation must halt the run instead of being performed.
    const fn budget_hit(&self) -> bool {
        matches!(&self.tape, Tape::Replay { budget: Some(b), .. } if self.observed >= *b)
    }

    // Consume the next recorded frame under `Replay`, advancing the cursor. A
    // spent trace is a mismatch: the program asked for more than was recorded.
    fn next_frame(&mut self) -> Result<Obs, String> {
        match &mut self.tape {
            Tape::Replay { frames, cursor, .. } => {
                let f = frames
                    .get(*cursor)
                    .cloned()
                    .ok_or("replay: trace exhausted before the program finished")?;
                *cursor += 1;
                Ok(f)
            }
            _ => Err("next_frame off a non-replay tape".into()),
        }
    }

    // Perform one capability read of the given kind. Under `Live` the real read
    // runs; under `Record` it runs and its result is logged; under `Replay` the
    // recorded value is served and the real read is skipped. Reaching a replay
    // budget sets `halted` and returns a placeholder the unwinding discards.
    fn observe(
        &mut self,
        kind: ObsKind,
        real: impl FnOnce(&mut Self) -> Result<Rv, String>,
    ) -> Result<Rv, String> {
        if matches!(self.tape, Tape::Live) {
            return real(self);
        }
        if self.budget_hit() {
            self.halted = true;
            return Ok(Rv::Unit);
        }
        if matches!(self.tape, Tape::Replay { .. }) {
            let frame = self.next_frame()?;
            let v = rv_of_obs(kind, &frame)?;
            self.observed += 1;
            return Ok(v);
        }
        // Record: perform for real, then log the observation.
        let v = real(self)?;
        let obs = obs_of_rv(kind, &v)?;
        if let Tape::Record(frames) = &mut self.tape {
            frames.push(obs);
        }
        self.observed += 1;
        Ok(v)
    }

    // Perform one output observation. Under `Replay` the recorded `Out` boundary
    // is consumed and the output re-performed live (reproducing the transcript);
    // under `Record` the output fires and an `Out` boundary is logged.
    fn observe_out(
        &mut self,
        emit: impl FnOnce(&mut Self) -> Result<(), String>,
    ) -> Result<(), String> {
        if matches!(self.tape, Tape::Live) {
            return emit(self);
        }
        if self.budget_hit() {
            self.halted = true;
            return Ok(());
        }
        if matches!(self.tape, Tape::Replay { .. }) {
            let frame = self.next_frame()?;
            if frame != Obs::Out {
                return Err("replay: trace does not match program (expected an output)".into());
            }
            emit(self)?;
            self.observed += 1;
            return Ok(());
        }
        emit(self)?;
        if let Tape::Record(frames) = &mut self.tape {
            frames.push(Obs::Out);
        }
        self.observed += 1;
        Ok(())
    }

    /// # Errors
    /// Fails with a runtime error message.
    pub fn eval(&mut self, c: &Comp) -> Result<Rv, String> {
        self.comp(&Env::default(), c)
    }

    /// # Errors
    /// Fails with a runtime error message.
    pub fn comp(&mut self, env: &Env, c: &Comp) -> Result<Rv, String> {
        self.exec(lower(c), env.clone())
    }

    fn exec(&mut self, root: Cmp, env: Env) -> Result<Rv, String> {
        match self.run_loop(Vec::new(), State::Eval(root, env))? {
            Outcome::Done(v) => Ok(v),
            // A bare `exec` never sets a step budget, so it cannot suspend; the
            // suspend/resume drivers use `run_loop` directly.
            Outcome::Suspended { .. } => Err("evaluation suspended without a resume driver".into()),
        }
    }

    // The machine loop, started from an arbitrary pending state so a resumed
    // continuation picks up exactly where a suspend left off. It ends either with a
    // final value or, if a step budget is set and reached, paused with its whole
    // live state handed back for snapshotting.
    fn run_loop(&mut self, mut stack: Vec<Frame>, mut state: State) -> Result<Outcome, String> {
        loop {
            // `exit` short-circuits the whole program: stop unwinding and hand
            // the last value back so the host can act on `self.exit`. A replay
            // budget halt unwinds the same way (replay-to-N stops here).
            if self.exit.is_some() || self.halted {
                if let State::Ret(v) = state {
                    return Ok(Outcome::Done(v));
                }
            }
            // A step budget pauses the machine with its state intact. Checked before
            // the transition so the resumed run re-performs exactly the step the
            // suspend stopped short of, never skipping or repeating one.
            if let Some(budget) = self.step_budget {
                if self.steps >= budget {
                    return Ok(Outcome::Suspended { stack, state });
                }
            }
            self.steps += 1;
            state = match state {
                State::Eval(c, env) => self.step(&mut stack, &c, env)?,
                State::Ret(v) => match stack.pop() {
                    None => return Ok(Outcome::Done(v)),
                    Some(frame) => self.cont(&mut stack, frame, v)?,
                },
            };
        }
    }

    fn step(&mut self, stack: &mut Vec<Frame>, c: &Node, env: Env) -> Result<State, String> {
        Ok(match c {
            Node::Return(a) => State::Ret(atom(&env, a)?),
            Node::Bind(m, x, n) => {
                stack.push(Frame::Bind(*x, Rc::clone(n), env.clone()));
                State::Eval(Rc::clone(m), env)
            }
            Node::Force(a) => match atom(&env, a)? {
                Rv::Thunk(c, e) => State::Eval(c, e),
                other => State::Ret(other),
            },
            Node::Lam(ps, body) => State::Ret(Rv::Closure(Rc::clone(ps), Rc::clone(body), env)),
            Node::App(m, args) => {
                stack.push(Frame::Args(Rc::clone(args), env.clone()));
                State::Eval(Rc::clone(m), env)
            }
            Node::If(a, t, e) => match atom(&env, a)? {
                Rv::Bool(true) => State::Eval(Rc::clone(t), env),
                Rv::Bool(false) => State::Eval(Rc::clone(e), env),
                _ => return Err("if on non-boolean".into()),
            },
            Node::Prim(op, a, b) => State::Ret(prim(*op, &atom(&env, a)?, &atom(&env, b)?)?),
            Node::Call(name, args) => {
                let (params, body) = self
                    .fns
                    .get(name)
                    .ok_or_else(|| format!("unknown function {name}"))?;
                let avs = atoms(&env, args)?;
                if avs.len() < params.len() {
                    let mut cenv = BTreeMap::new();
                    for (p, a) in params.iter().zip(&avs) {
                        cenv.insert(*p, a.clone());
                    }
                    State::Ret(Rv::Closure(
                        Rc::from(&params[avs.len()..]),
                        Rc::clone(body),
                        Rc::new(cenv),
                    ))
                } else {
                    // ANF saturates every call, so over-application is a lowering
                    // bug. Trap rather than let `zip` silently drop the extra args:
                    // as the differential oracle we must diverge from a broken
                    // backend here, not agree with it.
                    if avs.len() > params.len() {
                        return Err(format!(
                            "over-application of `{name}`: {} args for {} params",
                            avs.len(),
                            params.len()
                        ));
                    }
                    let mut e2 = BTreeMap::new();
                    for (p, a) in params.iter().zip(avs) {
                        e2.insert(*p, a);
                    }
                    let body = Rc::clone(body);
                    let prev = mem::replace(&mut self.fn_name, *name);
                    // A Restore already on top means we are in tail position:
                    // collapsing keeps tail calls O(1) space.
                    if !matches!(stack.last(), Some(Frame::Restore(_))) {
                        stack.push(Frame::Restore(prev));
                    }
                    State::Eval(body, Rc::new(e2))
                }
            }
            Node::Print(a) => {
                let rv = atom(&env, a)?;
                let s = rv.show();
                self.out.push(rv);
                self.observe_out(|m| {
                    write!(m.out_sink, "{s}").map_err(|e| format!("print: {e}"))?;
                    m.out_sink.flush().ok();
                    m.term.push_str(&s);
                    Ok(())
                })?;
                State::Ret(Rv::Unit)
            }
            Node::PrintNl => {
                self.observe_out(|m| {
                    writeln!(m.out_sink).map_err(|e| format!("println: {e}"))?;
                    m.out_sink.flush().ok();
                    m.term.push('\n');
                    Ok(())
                })?;
                State::Ret(Rv::Unit)
            }
            Node::Rand => State::Ret(self.observe(ObsKind::Int, |m| {
                Ok(Rv::Int((splitmix64(&mut m.rng) >> 2).cast_signed()))
            })?),
            Node::Srand(a) => {
                self.rng = match atom(&env, a)? {
                    Rv::Int(n) => n.cast_unsigned(),
                    _ => return Err("srand: expected Int".into()),
                };
                State::Ret(Rv::Unit)
            }
            Node::ReadInt => State::Ret(self.observe(ObsKind::Int, |m| {
                let mut line = String::new();
                m.input
                    .read_line(&mut line)
                    .map_err(|e| format!("read_int: {e}"))?;
                line.trim()
                    .parse::<i64>()
                    .map(Rv::Int)
                    .map_err(|e| format!("read_int: {e}"))
            })?),
            Node::ReadLine => State::Ret(self.observe(ObsKind::Str, |m| {
                let mut line = String::new();
                m.input
                    .read_line(&mut line)
                    .map_err(|e| format!("read_line: {e}"))?;
                let s = line.strip_suffix('\n').unwrap_or(&line);
                Ok(Rv::Str(s.strip_suffix('\r').unwrap_or(s).into()))
            })?),
            Node::Error(a) => {
                return Err(match atom(&env, a)? {
                    Rv::Str(s) => s,
                    Rv::Int(n) => format!("error({n})"),
                    _ => "error(1)".into(),
                })
            }
            Node::Case(a, arms) => {
                let scrut = atom(&env, a)?;
                for (pat, body) in arms {
                    if let Some(binds) = match_pat(pat, &scrut) {
                        if binds.is_empty() {
                            return Ok(State::Eval(Rc::clone(body), env));
                        }
                        let mut env2 = env;
                        Rc::make_mut(&mut env2).extend(binds);
                        return Ok(State::Eval(Rc::clone(body), env2));
                    }
                }
                return Err(format!("no matching pattern in `{}`", self.fn_name));
            }
            Node::FloatBuiltin(name, a) => State::Ret(float_builtin(*name, atom(&env, a)?)?),
            Node::Neg(lane, a) => State::Ret(neg_rv(*lane, &atom(&env, a)?)?),
            Node::StrBuiltin(name, args) => {
                let vals = atoms(&env, args)?;
                // `exit(n)` is a host action, not a value: record the code and
                // let the exec loop unwind rather than killing the process here.
                #[allow(clippy::cast_possible_truncation)]
                if let (Builtin::Exit, [Rv::Int(n)]) = (*name, vals.as_slice()) {
                    self.exit = Some(*n as i32);
                    State::Ret(Rv::Unit)
                } else if let Some(kind) = capability_kind(*name) {
                    // A world read (file/env): route through the tape so it is
                    // recorded or served from a trace like the other capabilities.
                    let nm = *name;
                    let v = self.observe(kind, move |_m| str_builtin(nm, &vals))?;
                    State::Ret(v)
                } else {
                    State::Ret(str_builtin(*name, &vals)?)
                }
            }
            Node::Do(op, args) => {
                let avs = atoms(&env, args)?;
                self.perform(stack, *op, avs)?
            }
            Node::Handle(hi) => {
                stack.push(Frame::Handle(Rc::clone(hi), env.clone()));
                State::Eval(Rc::clone(&hi.body), env)
            }
            Node::Mask(ops, body) => {
                stack.push(Frame::Mask(Rc::clone(ops)));
                State::Eval(Rc::clone(body), env)
            }
        })
    }

    fn cont(&mut self, stack: &mut Vec<Frame>, frame: Frame, v: Rv) -> Result<State, String> {
        Ok(match frame {
            Frame::Bind(x, n, mut env) => {
                Rc::make_mut(&mut env).insert(x, v);
                State::Eval(n, env)
            }
            Frame::Restore(name) => {
                self.fn_name = name;
                State::Ret(v)
            }
            Frame::Args(args, env) => {
                let avs = atoms(&env, &args)?;
                match v {
                    Rv::Closure(ps, body, mut cenv) => {
                        let e = Rc::make_mut(&mut cenv);
                        if avs.len() < ps.len() {
                            for (p, a) in ps.iter().zip(&avs) {
                                e.insert(*p, a.clone());
                            }
                            State::Ret(Rv::Closure(Rc::from(&ps[avs.len()..]), body, cenv))
                        } else {
                            // The sibling of the `Node::Call` over-application trap:
                            // saturated application evaluates the body, but ANF never
                            // over-applies, so surplus args are a lowering bug. Trap
                            // rather than let `zip` silently drop them.
                            if avs.len() > ps.len() {
                                return Err(format!(
                                    "over-application of closure: {} args for {} params",
                                    avs.len(),
                                    ps.len()
                                ));
                            }
                            for (p, a) in ps.iter().zip(avs) {
                                e.insert(*p, a);
                            }
                            State::Eval(body, cenv)
                        }
                    }
                    Rv::Resume(frames) => {
                        // resume takes exactly one argument; more is a lowering bug.
                        if avs.len() > 1 {
                            return Err(format!(
                                "resume applied to {} arguments, expected 1",
                                avs.len()
                            ));
                        }
                        let arg = avs
                            .into_iter()
                            .next()
                            .ok_or_else(|| "resume requires an argument".to_string())?;
                        stack.extend(frames.iter().cloned());
                        State::Ret(arg)
                    }
                    _ => return Err(format!("applied a non-function in `{}`", self.fn_name)),
                }
            }
            Frame::Mask(_) => State::Ret(v),
            Frame::Handle(hi, env) => match (&hi.return_var, &hi.return_body) {
                (Some(rv), Some(rb)) => {
                    let mut env2 = env;
                    Rc::make_mut(&mut env2).insert(*rv, v);
                    State::Eval(Rc::clone(rb), env2)
                }
                _ => State::Ret(v),
            },
        })
    }

    fn perform(&mut self, stack: &mut Vec<Frame>, op: Sym, args: Vec<Rv>) -> Result<State, String> {
        let mut captured = Vec::new();
        // Each mask frame for this op's effect crossed on the way out makes
        // the walk skip one more matching handler.
        let mut skip = 0usize;
        while let Some(frame) = stack.pop() {
            match frame {
                // A call boundary crossed while unwinding to the handler belongs
                // to the captured continuation: keep it so a later `resume`
                // restores the caller's `fn_name` (else post-resume diagnostics
                // name the wrong function). `Sym` is `Copy`, so this both updates
                // the live name and records the frame.
                Frame::Restore(name) => {
                    self.fn_name = name;
                    captured.push(Frame::Restore(name));
                }
                // An effect performed with a pending application on the stack:
                // capture the application frame into the continuation so `resume`
                // re-applies the args to the resumed value. ANF keeps application
                // heads value-only so this rarely fires, but dropping the frame
                // would silently resume with the un-applied function.
                Frame::Args(a, e) => captured.push(Frame::Args(a, e)),
                Frame::Mask(ops) => {
                    if ops.contains(&op) {
                        skip += 1;
                    }
                    captured.push(Frame::Mask(ops));
                }
                Frame::Handle(hi, henv) if hi.ops.contains_key(&op) => {
                    // A masked op skips one matching handler; otherwise this
                    // handler catches it, binding the op args and the captured
                    // continuation as `resume`.
                    if skip > 0 {
                        skip -= 1;
                        captured.push(Frame::Handle(hi, henv));
                    } else {
                        let (params, resume_var, body) = &hi.ops[&op];
                        // The op is performed with exactly its declared arity; a
                        // mismatch is a lowering bug that `zip` would otherwise hide
                        // by dropping surplus args or leaving params unbound.
                        if params.len() != args.len() {
                            return Err(format!(
                                "effect `{op}` performed with {} argument(s), handler binds {}",
                                args.len(),
                                params.len()
                            ));
                        }
                        let body = Rc::clone(body);
                        let mut env2 = henv.clone();
                        captured.push(Frame::Handle(Rc::clone(&hi), henv));
                        captured.reverse();
                        let e = Rc::make_mut(&mut env2);
                        for (p, a) in params.iter().zip(args) {
                            e.insert(*p, a);
                        }
                        e.insert(*resume_var, Rv::Resume(Rc::from(captured)));
                        return Ok(State::Eval(body, env2));
                    }
                }
                other => captured.push(other),
            }
        }
        Err(format!("unhandled effect `{op}`"))
    }
}

/// Mirrors `prism_big_of_str` in the C runtime: ASCII-trim, optional sign, then
/// a strict all-digit decimal parse. Anything else is None.
fn big_of_str(s: &str) -> Option<BigInt> {
    let t = s.trim_matches(|c: char| c.is_ascii_whitespace());
    let digits = t.strip_prefix(['+', '-']).unwrap_or(t);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    t.parse().ok()
}

/// Builds the `Result(Unit, String)` ADT value the file builtins return,
/// matching the `Ok`/`Err` cells the native runtime constructs.
fn file_result(r: std::io::Result<()>) -> Rv {
    match r {
        Ok(()) => Rv::Data("Ok".into(), vec![Rv::Unit].into()),
        Err(e) => Rv::Data("Err".into(), vec![Rv::Str(e.to_string())].into()),
    }
}

fn atom(env: &Env, a: &Atom) -> Result<Rv, String> {
    match a {
        Atom::Var(x) => env
            .get(x)
            .cloned()
            .ok_or_else(|| format!("unbound {x} at runtime")),
        Atom::Int(n) => Ok(Rv::Int(*n)),
        Atom::I64(n) => Ok(Rv::I64(*n)),
        Atom::U64(n) => Ok(Rv::U64(*n)),
        Atom::Float(f) => Ok(Rv::Float(*f)),
        Atom::Bool(b) => Ok(Rv::Bool(*b)),
        Atom::Unit => Ok(Rv::Unit),
        Atom::Str(s) => Ok(Rv::Str(s.clone())),
        Atom::Thunk(c) => Ok(Rv::Thunk(Rc::clone(c), env.clone())),
        Atom::Ctor(name, vs) => Ok(Rv::Data(*name, atoms(env, vs)?.into())),
        Atom::Tuple(vs) => Ok(Rv::Tuple(atoms(env, vs)?.into())),
    }
}

fn atoms(env: &Env, args: &[Atom]) -> Result<Vec<Rv>, String> {
    args.iter().map(|a| atom(env, a)).collect()
}

// Truncating/widening conversions are the language semantics of these builtins.
#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
// Genuine unary negation per lane. Int reuses the exact `0 - x` subtract path
// (immediate/bignum promotion included) so the result is identical to the old
// lowering; I64 is the wrapping fixed-width subtract from zero; Float is a real
// sign-bit flip (`-f`, not `-0.0 - f`) so it preserves signed zero and matches
// the native `fneg` bit for bit.
fn neg_rv(lane: NegLane, v: &Rv) -> Result<Rv, String> {
    match lane {
        NegLane::Int => prim(CoreOp::Sub, &Rv::Int(0), v),
        NegLane::I64 => fixed2(&Rv::I64(0), v, u64::wrapping_sub),
        NegLane::Float => match v {
            Rv::Float(f) => Ok(Rv::Float(-f)),
            _ => Err("negation on non-float value".into()),
        },
    }
}

// The owned math surface for the interpreter. On native it FFIs the vendored
// `prism_m_*` C symbols (linked into this binary), the identical implementation
// native codegen calls, so interpreter and native agree bit for bit. On wasm,
// where there is no C to link, it falls back to the pure-Rust `libm` crate, a
// documented ~1 ULP browser-only divergence from native (there is no native
// backend in the browser to diverge from).
// `pub` (doc-hidden) so the conformance gate (`tests/float_math_conformance.rs`)
// can diff this interpreter path against the native runtime bit for bit.
#[doc(hidden)]
#[cfg(not(target_arch = "wasm32"))]
pub mod owned_math {
    // SAFETY (whole module): every `prism_m_*` is a pure `extern "C"` function
    // taking and returning plain `f64`, defined in runtime/prism_libm.c and linked
    // into this binary. The calls touch no memory and cannot fault, so each is
    // sound. This is the crate's one audited FFI (see Cargo.toml `unsafe_code`).
    #![allow(unsafe_code)]
    extern "C" {
        fn prism_m_sin(x: f64) -> f64;
        fn prism_m_cos(x: f64) -> f64;
        fn prism_m_tan(x: f64) -> f64;
        fn prism_m_asin(x: f64) -> f64;
        fn prism_m_acos(x: f64) -> f64;
        fn prism_m_atan(x: f64) -> f64;
        fn prism_m_sinh(x: f64) -> f64;
        fn prism_m_cosh(x: f64) -> f64;
        fn prism_m_tanh(x: f64) -> f64;
        fn prism_m_exp(x: f64) -> f64;
        fn prism_m_exp2(x: f64) -> f64;
        fn prism_m_expm1(x: f64) -> f64;
        fn prism_m_log(x: f64) -> f64;
        fn prism_m_log2(x: f64) -> f64;
        fn prism_m_log10(x: f64) -> f64;
        fn prism_m_log1p(x: f64) -> f64;
        fn prism_m_cbrt(x: f64) -> f64;
        fn prism_m_pow(x: f64, y: f64) -> f64;
        fn prism_m_atan2(y: f64, x: f64) -> f64;
        fn prism_m_hypot(x: f64, y: f64) -> f64;
        fn prism_m_fmod(x: f64, y: f64) -> f64;
    }
    macro_rules! unary {
        ($($name:ident => $ffi:ident),* $(,)?) => {
            $(#[must_use] pub fn $name(x: f64) -> f64 { unsafe { $ffi(x) } })*
        };
    }
    macro_rules! binary {
        ($($name:ident => $ffi:ident),* $(,)?) => {
            $(#[must_use] pub fn $name(x: f64, y: f64) -> f64 { unsafe { $ffi(x, y) } })*
        };
    }
    unary! {
        sin => prism_m_sin, cos => prism_m_cos, tan => prism_m_tan,
        asin => prism_m_asin, acos => prism_m_acos, atan => prism_m_atan,
        sinh => prism_m_sinh, cosh => prism_m_cosh, tanh => prism_m_tanh,
        exp => prism_m_exp, exp2 => prism_m_exp2, expm1 => prism_m_expm1,
        log => prism_m_log, log2 => prism_m_log2, log10 => prism_m_log10,
        log1p => prism_m_log1p, cbrt => prism_m_cbrt,
    }
    binary! {
        pow => prism_m_pow, atan2 => prism_m_atan2,
        hypot => prism_m_hypot, fmod => prism_m_fmod,
    }
}

#[cfg(target_arch = "wasm32")]
mod owned_math {
    pub(super) use libm::{
        acos, asin, atan, atan2, cbrt, cos, cosh, exp, exp2, expm1, fmod, hypot, log, log10, log1p,
        log2, pow, sin, sinh, tan, tanh,
    };
}

// The int/float conversion casts are the conversion semantics, not accidents:
// `Int -> Float` rounds to nearest (the IEEE double nearest to the integer),
// and the float-to-int forms truncate/floor/ceil saturate into the i64 lane,
// mirroring the native `llvm.fptosi.sat` lowering and pinned by the parity
// corpus and the conformance gate.
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
fn float_builtin(op: FloatOp, rv: Rv) -> Result<Rv, String> {
    let Rv::Float(f) = rv else {
        // The one non-float input is the int->float conversion.
        return match (op, rv) {
            (F::ToFloat, Rv::Int(n)) => Ok(Rv::Float(n as f64)),
            (o, _) => Err(format!("float builtin {}: wrong argument type", o.name())),
        };
    };
    Ok(match op {
        // int<->float conversions. `f as i64` truncates toward zero and saturates
        // (NaN -> 0), the pinned rounding; native codegen matches it with
        // `llvm.fptosi.sat`, so the two backends agree on out-of-range inputs.
        F::Truncate => Rv::Int(f as i64),
        F::FloorToInt => Rv::Int(owned_floor(f) as i64),
        F::CeilToInt => Rv::Int(owned_ceil(f) as i64),
        // Exact float->float: correctly rounded / exact on every IEEE-754
        // platform, so Rust std matches the hardware intrinsic codegen emits.
        F::AbsFloat => Rv::Float(f.abs()),
        F::Sqrt => Rv::Float(f.sqrt()),
        F::Floor => Rv::Float(owned_floor(f)),
        F::Ceil => Rv::Float(owned_ceil(f)),
        F::Round => Rv::Float(f.round()),
        F::Trunc => Rv::Float(f.trunc()),
        // Transcendentals: the owned vendored libm, identical to native.
        F::Sin => Rv::Float(owned_math::sin(f)),
        F::Cos => Rv::Float(owned_math::cos(f)),
        F::Tan => Rv::Float(owned_math::tan(f)),
        F::Asin => Rv::Float(owned_math::asin(f)),
        F::Acos => Rv::Float(owned_math::acos(f)),
        F::Atan => Rv::Float(owned_math::atan(f)),
        F::Sinh => Rv::Float(owned_math::sinh(f)),
        F::Cosh => Rv::Float(owned_math::cosh(f)),
        F::Tanh => Rv::Float(owned_math::tanh(f)),
        F::Exp => Rv::Float(owned_math::exp(f)),
        F::Exp2 => Rv::Float(owned_math::exp2(f)),
        F::Expm1 => Rv::Float(owned_math::expm1(f)),
        F::Ln => Rv::Float(owned_math::log(f)),
        F::Log2 => Rv::Float(owned_math::log2(f)),
        F::Log10 => Rv::Float(owned_math::log10(f)),
        F::Log1p => Rv::Float(owned_math::log1p(f)),
        F::Cbrt => Rv::Float(owned_math::cbrt(f)),
        F::ToFloat => return Err(format!("float builtin {}: wrong argument type", op.name())),
    })
}

// `floor`/`ceil` are exact and share their result with the codegen intrinsic;
// factored out so the float->float and float->int forms cannot drift.
const fn owned_floor(f: f64) -> f64 {
    f.floor()
}
const fn owned_ceil(f: f64) -> f64 {
    f.ceil()
}

fn str_builtin(b: Builtin, vals: &[Rv]) -> Result<Rv, String> {
    match (b, vals) {
        (B::Concat, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Str(format!("{a}{b}"))),
        (B::StrLen, [Rv::Str(s)]) => Ok(Rv::Int(i64::try_from(s.chars().count()).unwrap_or(0))),
        (B::StrEq, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Bool(a == b)),
        (B::StrCmp, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Int(match a.cmp(b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        })),
        (B::ShowInt, [Rv::Int(n)]) | (B::ShowI64, [Rv::I64(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ShowInt, [Rv::Big(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ShowBool, [Rv::Bool(b)]) => Ok(Rv::Str(b.to_string())),
        (B::ShowFloat, [Rv::Float(f)]) => Ok(Rv::Str(fmt_g(*f))),
        (B::ShowFloatPrec, [Rv::Float(f), Rv::Int(d)]) => {
            // Cap at the runtime's buffer width to stay byte identical (see
            // `RT_FLOAT_PREC_MAX_CHARS`).
            let mut s = format!("{f:.*}", usize::try_from(*d).unwrap_or(0));
            s.truncate(RT_FLOAT_PREC_MAX_CHARS);
            Ok(Rv::Str(s))
        }
        (B::PowFloat, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::pow(*a, *b))),
        (B::Atan2, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::atan2(*a, *b))),
        (B::Hypot, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::hypot(*a, *b))),
        (B::Fmod, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::fmod(*a, *b))),
        // Strict full-consume parse: trailing garbage and hex yield 0.0, matching
        // `prism_parse_float` in the runtime (see its note on the strtod divergence).
        (B::ParseFloat, [Rv::Str(s)]) => Ok(Rv::Float(s.trim().parse::<f64>().unwrap_or(0.0))),
        (B::Substring, [Rv::Str(s), Rv::Int(start), Rv::Int(len)]) => {
            let st = usize::try_from(*start).unwrap_or(0);
            let take = usize::try_from(*len).unwrap_or(0);
            Ok(Rv::Str(s.chars().skip(st).take(take).collect()))
        }
        (B::CharAt, [Rv::Str(s), Rv::Int(i)]) => {
            Ok(Rv::Int(usize::try_from(*i).map_or(-1, |idx| {
                s.chars().nth(idx).map_or(-1, |c| i64::from(c as u32))
            })))
        }
        // Hash a string's raw bytes with blake3, returned as lowercase hex. The
        // native runtime's `prism_blake3` must produce the identical string.
        (B::Blake3, [Rv::Str(s)]) => Ok(Rv::Str(blake3::hash(s.as_bytes()).to_hex().to_string())),
        (B::ShowChar, [Rv::Int(cp)]) => Ok(Rv::Str(
            u32::try_from(*cp)
                .ok()
                .and_then(char::from_u32)
                .map(|c| c.to_string())
                .unwrap_or_default(),
        )),
        (B::ParseInt, [Rv::Str(s)]) => Ok(big_of_str(s).map_or_else(
            || Rv::Data("None".into(), Vec::new().into()),
            |n| Rv::Data("Some".into(), vec![norm(n)].into()),
        )),
        // Elaborator-only: decimal text of a valid big literal to its `Integer`.
        (B::BigLit, [Rv::Str(s)]) => Ok(norm(s.parse().unwrap_or(BigInt::ZERO))),
        (B::Getenv, [Rv::Str(s)]) => Ok(Rv::Str(env::var(s).unwrap_or_default())),
        (B::ReadFile, [Rv::Str(p)]) => match fs::read_to_string(p) {
            Ok(s) => Ok(Rv::Str(s)),
            Err(e) => Err(format!("read_file: {e}: {p}")),
        },
        // Raw bytes, no UTF-8 constraint: a byte buffer holds an arbitrary file
        // faithfully where `Rv::Str` (a Rust `String`) could not.
        (B::ReadBytesFile, [Rv::Str(p)]) => match fs::read(p) {
            Ok(v) => Ok(Rv::Buf(Rc::new(v))),
            Err(e) => Err(format!("read_bytes: {e}: {p}")),
        },
        (B::WriteBytesFile, [Rv::Str(p), Rv::Buf(v)]) => Ok(file_result(fs::write(p, &v[..]))),
        (B::WriteFile, [Rv::Str(p), Rv::Str(c)]) => Ok(file_result(fs::write(p, c))),
        (B::FileExists, [Rv::Str(p)]) => Ok(Rv::Bool(std::path::Path::new(p).exists())),
        (B::AppendFile, [Rv::Str(p), Rv::Str(c)]) => {
            let r = fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(p)
                .and_then(|mut f| f.write_all(c.as_bytes()));
            Ok(file_result(r))
        }
        (B::RemoveFile, [Rv::Str(p)]) => {
            let _ = fs::remove_file(p);
            Ok(Rv::Unit)
        }
        // The content-addressed store bridge. Reads are best-effort cache reads:
        // a missing, dangling, or corrupt blob returns empty/false so the caller
        // cold-starts, exactly as a missing snapshot file does. A write failure is
        // swallowed too, since the store is only a cache.
        (B::StoreGet, [Rv::Str(root), Rv::Str(key)]) => Ok(Rv::Str(
            bridge::get(Path::new(root), key)
                .ok()
                .flatten()
                .unwrap_or_default(),
        )),
        (B::StorePut, [Rv::Str(root), Rv::Str(key), Rv::Str(content)]) => {
            let _ = bridge::put(Path::new(root), key, content);
            Ok(Rv::Unit)
        }
        (B::StoreHas, [Rv::Str(root), Rv::Str(key)]) => {
            Ok(Rv::Bool(bridge::has(Path::new(root), key)))
        }
        // `exit` is intercepted in `step` (it sets the machine's exit status
        // and unwinds), so it never reaches the value-returning builtin path.
        (B::Exit, _) => Err("exit: unexpected argument".into()),
        // Run a shell command, returning its exit code (-1 on spawn failure or
        // signal death), matching the C runtime's `WEXITSTATUS(system(..))`.
        (B::System, [Rv::Str(cmd)]) => Ok(Rv::Int(i64::from(
            std::process::Command::new("sh")
                .arg("-c")
                .arg(cmd)
                .status()
                .ok()
                .and_then(|s| s.code())
                .unwrap_or(-1),
        ))),
        (B::Eprint, [Rv::Str(s)]) => {
            eprint!("{s}");
            let _ = std::io::stderr().flush();
            Ok(Rv::Unit)
        }
        (B::ArgsCount, []) => Ok(Rv::Int(i64::try_from(env::args().count()).unwrap_or(0))),
        // Clock reads, in nanoseconds, matching the C runtime. Both are recorded
        // capability observations (see `capability_kind`), so the live value here
        // is only read on the first (recording) run; replay serves the trace. The
        // monotonic origin is this process's first read, so only differences are
        // meaningful, exactly as the native `CLOCK_MONOTONIC` origin is arbitrary.
        (B::WallNow, []) => {
            let ns = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos());
            Ok(Rv::Int(i64::try_from(ns).unwrap_or(i64::MAX)))
        }
        (B::MonoNow, []) => {
            static MONO_BASE: OnceLock<Instant> = OnceLock::new();
            let ns = MONO_BASE.get_or_init(Instant::now).elapsed().as_nanos();
            Ok(Rv::Int(i64::try_from(ns).unwrap_or(i64::MAX)))
        }
        (B::Arg, [Rv::Int(i)]) => Ok(Rv::Str(
            usize::try_from(*i)
                .ok()
                .and_then(|k| env::args().nth(k))
                .unwrap_or_default(),
        )),
        (B::I64Add | B::U64Add, [a, b]) => fixed2(a, b, u64::wrapping_add),
        (B::I64Sub | B::U64Sub, [a, b]) => fixed2(a, b, u64::wrapping_sub),
        (B::I64Mul | B::U64Mul, [a, b]) => fixed2(a, b, u64::wrapping_mul),
        (B::I64Div | B::I64Rem, [_, Rv::I64(0)]) | (B::U64Div | B::U64Rem, [_, Rv::U64(0)]) => {
            Err("division by zero".into())
        }
        (B::I64Div, [Rv::I64(x), Rv::I64(y)]) => Ok(Rv::I64(x.wrapping_div(*y))),
        (B::I64Rem, [Rv::I64(x), Rv::I64(y)]) => Ok(Rv::I64(x.wrapping_rem(*y))),
        (B::U64Div, [Rv::U64(x), Rv::U64(y)]) => Ok(Rv::U64(x / y)),
        (B::U64Rem, [Rv::U64(x), Rv::U64(y)]) => Ok(Rv::U64(x % y)),
        (B::I64Cmp, [Rv::I64(x), Rv::I64(y)]) => Ok(ord(x.cmp(y))),
        (B::U64Cmp, [Rv::U64(x), Rv::U64(y)]) => Ok(ord(x.cmp(y))),
        (B::ArrayNew, [Rv::Int(n), init]) => {
            let k = usize::try_from(*n).map_err(|_| "array_new: negative length".to_string())?;
            Ok(Rv::Array(vec![init.clone(); k].into()))
        }
        (B::ArrayEmpty, []) => Ok(Rv::Array(Vec::new().into())),
        (B::ArrayPush, [Rv::Array(v), x]) => {
            let mut next = v.to_vec();
            next.push(x.clone());
            Ok(Rv::Array(next.into()))
        }
        (B::ArrayPop, [Rv::Array(v)]) => {
            if v.is_empty() {
                return Err("array_pop: empty array".to_string());
            }
            let mut next = v.to_vec();
            next.pop();
            Ok(Rv::Array(next.into()))
        }
        (B::ByteLen, [Rv::Str(s)]) => Ok(Rv::Int(i64::try_from(s.len()).unwrap_or(0))),
        (B::ByteAt, [Rv::Str(s), Rv::Int(i)]) => Ok(Rv::Int(
            usize::try_from(*i)
                .ok()
                .and_then(|k| s.as_bytes().get(k))
                .map_or(-1, |b| i64::from(*b)),
        )),
        (B::StringOfBytes, [Rv::Array(v)]) => {
            let bytes: Vec<u8> = v
                .iter()
                .map(|e| {
                    if let Rv::Int(n) = e {
                        u8::try_from(*n & 0xFF).unwrap_or(0)
                    } else {
                        0
                    }
                })
                .collect();
            Ok(Rv::Str(String::from_utf8_lossy(&bytes).into_owned()))
        }
        (B::ArrayLen, [Rv::Array(v)]) => Ok(Rv::Int(i64::try_from(v.len()).unwrap_or(0))),
        (B::StringOfArray, [Rv::Array(v)]) => {
            let mut s = String::new();
            for e in v.iter() {
                let Rv::Str(t) = e else {
                    return Err("string_of_array: non-string element".to_string());
                };
                s.push_str(t);
            }
            Ok(Rv::Str(s))
        }
        (B::ArrayGet, [Rv::Array(v), Rv::Int(i)]) => usize::try_from(*i)
            .ok()
            .and_then(|k| v.get(k).cloned())
            .ok_or_else(|| "array index out of bounds".to_string()),
        (B::ArraySet, [Rv::Array(v), Rv::Int(i), x]) => {
            let k = usize::try_from(*i).map_err(|_| "array index out of bounds".to_string())?;
            if k >= v.len() {
                return Err("array index out of bounds".to_string());
            }
            let mut next = v.to_vec();
            next[k] = x.clone();
            Ok(Rv::Array(next.into()))
        }
        // The unboxed byte buffer under `Bytes`. Bytes are masked into 0..255 on
        // the way in and every op is value-semantic (copy on write), mirroring the
        // C runtime's rc==1 in-place / shared-copy discipline bit-for-bit.
        (B::BufEmpty, []) => Ok(Rv::Buf(Rc::new(Vec::new()))),
        (B::BufNew, [Rv::Int(n), Rv::Int(init)]) => {
            let k = usize::try_from(*n).map_err(|_| "buf_new: negative length".to_string())?;
            #[expect(clippy::cast_sign_loss)]
            let byte = (*init & 0xFF) as u8;
            Ok(Rv::Buf(Rc::new(vec![byte; k])))
        }
        (B::BufLen, [Rv::Buf(v)]) => Ok(Rv::Int(i64::try_from(v.len()).unwrap_or(0))),
        (B::BufGet, [Rv::Buf(v), Rv::Int(i)]) => usize::try_from(*i)
            .ok()
            .and_then(|k| v.get(k))
            .map(|b| Rv::Int(i64::from(*b)))
            .ok_or_else(|| "buffer index out of bounds".to_string()),
        (B::BufSet, [Rv::Buf(v), Rv::Int(i), Rv::Int(x)]) => {
            let k = usize::try_from(*i).map_err(|_| "buffer index out of bounds".to_string())?;
            if k >= v.len() {
                return Err("buffer index out of bounds".to_string());
            }
            let mut next = v.to_vec();
            #[expect(clippy::cast_sign_loss)]
            {
                next[k] = (*x & 0xFF) as u8;
            }
            Ok(Rv::Buf(Rc::new(next)))
        }
        (B::BufPush, [Rv::Buf(v), Rv::Int(x)]) => {
            let mut next = v.to_vec();
            #[expect(clippy::cast_sign_loss)]
            next.push((*x & 0xFF) as u8);
            Ok(Rv::Buf(Rc::new(next)))
        }
        (B::BufSlice, [Rv::Buf(v), Rv::Int(start), Rv::Int(len)]) => {
            let n = v.len();
            let s = usize::try_from(*start).unwrap_or(0).min(n);
            let take = usize::try_from(*len).unwrap_or(0);
            let e = s.saturating_add(take).min(n);
            Ok(Rv::Buf(Rc::new(v[s..e].to_vec())))
        }
        (B::BufCat, [Rv::Buf(a), Rv::Buf(b)]) => {
            let mut next = a.to_vec();
            next.extend_from_slice(b);
            Ok(Rv::Buf(Rc::new(next)))
        }
        (B::BufEq, [Rv::Buf(a), Rv::Buf(b)]) => Ok(Rv::Bool(a == b)),
        (B::BufCmp, [Rv::Buf(a), Rv::Buf(b)]) => Ok(ord(a.as_slice().cmp(b.as_slice()))),
        // blake3 of the raw bytes, byte-identical to a string's `blake3` over the
        // same bytes and to the native `prism_buf_hash`.
        (B::BufHash, [Rv::Buf(v)]) => Ok(Rv::Str(blake3::hash(v).to_hex().to_string())),
        (B::BufOfString, [Rv::Str(s)]) => Ok(Rv::Buf(Rc::new(s.as_bytes().to_vec()))),
        // The total lossy decode (the boundary wrapper validates first, so on
        // valid input this is lossless); matches `prism_string_of_buf`.
        (B::StringOfBuf, [Rv::Buf(v)]) => Ok(Rv::Str(String::from_utf8_lossy(v).into_owned())),
        (B::BufUtf8Valid, [Rv::Buf(v)]) => Ok(Rv::Bool(std::str::from_utf8(v).is_ok())),
        (B::I64And | B::U64And, [a, b]) => fixed2(a, b, |x, y| x & y),
        (B::I64Or | B::U64Or, [a, b]) => fixed2(a, b, |x, y| x | y),
        (B::I64Xor | B::U64Xor, [a, b]) => fixed2(a, b, |x, y| x ^ y),
        // Shift counts are masked to 0..64; `i64_shr` is arithmetic (signed),
        // `u64_shr` logical, matching the C runtime's signed/unsigned `>>`.
        (B::I64Shl, [Rv::I64(x), Rv::I64(y)]) => {
            Ok(Rv::I64(x.wrapping_shl(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::I64Shr, [Rv::I64(x), Rv::I64(y)]) => {
            Ok(Rv::I64(x.wrapping_shr(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::U64Shl, [Rv::U64(x), Rv::U64(y)]) => {
            Ok(Rv::U64(x.wrapping_shl(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::U64Shr, [Rv::U64(x), Rv::U64(y)]) => {
            Ok(Rv::U64(x.wrapping_shr(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::ShowU64, [Rv::U64(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ToI64, [v]) => Ok(Rv::I64(low64(v)?.cast_signed())),
        (B::ToU64, [v]) => Ok(Rv::U64(low64(v)?)),
        (B::IntOfI64, [Rv::I64(n)]) => Ok(Rv::Int(*n)),
        (B::IntOfU64, [Rv::U64(n)]) => {
            Ok(i64::try_from(*n).map_or_else(|_| Rv::Big(BigInt::from(*n)), Rv::Int))
        }
        // The native kernel keys off `kind`. The interpreter compares the runtime
        // values directly, which gives the same stable order for every element
        // type the elaborator specializes.
        (B::SortPrim, [_kind, list]) => {
            let Some(elems) = list.list_elems() else {
                return Err("sort_prim: not a list".into());
            };
            let mut v: Vec<Rv> = elems.into_iter().cloned().collect();
            v.sort_by(rv_key_cmp);
            let mut acc = Rv::Data(NIL.into(), Vec::new().into());
            for e in v.into_iter().rev() {
                acc = Rv::Data(CONS.into(), vec![e, acc].into());
            }
            Ok(acc)
        }
        (op, _) => Err(format!("str builtin {}: wrong args", op.name())),
    }
}

// Total order on the primitive element types the sort kernel specializes,
// matching each canonical `Ord` instance: floats by IEEE total order (the same
// bit order the native radix uses), fixed-width ints by their signedness, and
// Integer (and Char-as-codepoint) by numeric value.
fn rv_key_cmp(a: &Rv, b: &Rv) -> Ordering {
    match (a, b) {
        (Rv::Float(x), Rv::Float(y)) => x.total_cmp(y),
        (Rv::I64(x), Rv::I64(y)) => x.cmp(y),
        (Rv::U64(x), Rv::U64(y)) => x.cmp(y),
        (Rv::Bool(x), Rv::Bool(y)) => x.cmp(y),
        _ => to_big(a)
            .zip(to_big(b))
            .map_or(Ordering::Equal, |(x, y)| x.cmp(&y)),
    }
}

// Render a float as the shortest decimal that round-trips back to `d`, laid out
// like a Python `repr`: full precision with no truncation, scientific notation
// only outside the `[-4, 16)` decimal-exponent window. Both the interpreter and
// the C runtime (`prism_show_float`) and the Lean oracle (`fmtG`) must implement
// the identical algorithm, since they are differentially tested against each
// other; `Float::to_string`'s exact-integer expansion would not be portable.
//
// `0.1` stays "0.1", `0.1 +. 0.2` shows "0.30000000000000004", `100.0` is
// "100", `1e100` is "1e+100". Rust's `{:e}` is correctly rounded (round half to
// even) like the printf family, so the digits and exponent agree with C.
// `pub` so the native float-formatter parity test (`tests/float_fmt.rs`) can
// diff the C runtime's shortest-round-trip output against this, the canonical
// interpreter form. Exposing it changes no output; the C side conforms to this.
// The `unwrap`s rest on `{:e}` invariants (always an `e`, always parseable), so
// the function does not panic for any finite or non-finite `f64`.
#[must_use]
#[allow(clippy::missing_panics_doc)]
pub fn fmt_g(d: f64) -> String {
    if d.is_nan() {
        return "nan".to_string();
    }
    if d.is_infinite() {
        return if d < 0.0 { "-inf" } else { "inf" }.to_string();
    }
    if d == 0.0 {
        return if d.is_sign_negative() { "-0" } else { "0" }.to_string();
    }
    // Shortest scientific form (fewest significant digits, 1..=17) that round-
    // trips; 17 digits always suffice for an IEEE double, so the fallback always
    // parses. `find` formats only up to the winning precision, so the chosen
    // string is reused rather than reformatted.
    let sci = (1..17usize)
        .map(|cand| format!("{:.*e}", cand - 1, d))
        .find(|s| s.parse::<f64>() == Ok(d))
        .unwrap_or_else(|| format!("{:.*e}", 16, d)); // "[-]D[.DDD]e±XX"
    let neg = sci.starts_with('-');
    let (mant, exp) = sci.trim_start_matches('-').split_once('e').unwrap();
    let e10: i32 = exp.parse().unwrap();
    let digits: String = mant.chars().filter(|c| *c != '.').collect();
    let body = if (-4..16).contains(&e10) {
        layout_fixed(&digits, e10)
    } else {
        // Scientific: one digit before the point, the rest after (`layout_fixed`
        // at exponent 0 does exactly this), then the `e±XX` suffix.
        let m = layout_fixed(&digits, 0);
        let sign = if e10 < 0 { '-' } else { '+' };
        format!("{m}e{sign}{:02}", e10.abs())
    };
    if neg {
        format!("-{body}")
    } else {
        body
    }
}

// Place the decimal point in `digits` (the significant figures, no point) so the
// leading digit has place value 10^`e10`. Trailing zeros are stripped.
fn layout_fixed(digits: &str, e10: i32) -> String {
    if e10 >= 0 {
        let k = e10.unsigned_abs() as usize + 1;
        if digits.len() <= k {
            format!("{digits}{}", "0".repeat(k - digits.len()))
        } else {
            strip_zeros(format!("{}.{}", &digits[..k], &digits[k..]))
        }
    } else {
        let zeros = "0".repeat((-e10 - 1).unsigned_abs() as usize);
        strip_zeros(format!("0.{zeros}{digits}"))
    }
}

fn strip_zeros(s: String) -> String {
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        s
    }
}

// IEEE 754 value equality is the intended semantics of Eqf/Nef (NaN never
// equal, +0.0 == -0.0), matching the backend's `fcmp oeq`/`une`. This is not
// bit equality.
#[allow(clippy::float_cmp)]
fn dispatch_float_op(op: CoreOp, x: f64, y: f64) -> Result<Rv, String> {
    Ok(match op {
        CoreOp::Addf => Rv::Float(x + y),
        CoreOp::Subf => Rv::Float(x - y),
        CoreOp::Mulf => Rv::Float(x * y),
        CoreOp::Divf => Rv::Float(x / y),
        CoreOp::Eqf => Rv::Bool(x == y),
        CoreOp::Nef => Rv::Bool(x != y),
        CoreOp::Ltf => Rv::Bool(x < y),
        CoreOp::Lef => Rv::Bool(x <= y),
        CoreOp::Gtf => Rv::Bool(x > y),
        CoreOp::Gef => Rv::Bool(x >= y),
        _ => return Err(format!("op {op:?} not defined for Float")),
    })
}

// i64 fast path: arithmetic that overflows i64 promotes to a normalized Big.
// The six ordering/equality ops are identical across every numeric type; only
// the arithmetic arms differ, so each `dispatch_*_op` consults this first.
fn cmp_op<T: Ord>(op: CoreOp, x: &T, y: &T) -> Option<Rv> {
    Some(Rv::Bool(match op {
        CoreOp::Eq => x == y,
        CoreOp::Ne => x != y,
        CoreOp::Lt => x < y,
        CoreOp::Le => x <= y,
        CoreOp::Gt => x > y,
        CoreOp::Ge => x >= y,
        _ => return None,
    }))
}

fn dispatch_int_op(op: CoreOp, x: i64, y: i64) -> Result<Rv, String> {
    if matches!(op, CoreOp::Div | CoreOp::Rem) && y == 0 {
        return Err("division by zero".into());
    }
    if let Some(r) = cmp_op(op, &x, &y) {
        return Ok(r);
    }
    let wide = |r: Option<i64>, f: fn(BigInt, BigInt) -> BigInt| {
        r.map_or_else(|| norm(f(BigInt::from(x), BigInt::from(y))), Rv::Int)
    };
    Ok(match op {
        CoreOp::Add => wide(x.checked_add(y), |a, b| a + b),
        CoreOp::Sub => wide(x.checked_sub(y), |a, b| a - b),
        CoreOp::Mul => wide(x.checked_mul(y), |a, b| a * b),
        CoreOp::Div => wide(x.checked_div(y), |a, b| a / b),
        CoreOp::Rem => Rv::Int(x.wrapping_rem(y)),
        _ => return Err(format!("op {op:?} not defined for Int")),
    })
}

fn dispatch_bigint_op(op: CoreOp, x: BigInt, y: BigInt) -> Result<Rv, String> {
    if matches!(op, CoreOp::Div | CoreOp::Rem) && y.sign() == Sign::NoSign {
        return Err("division by zero".into());
    }
    if let Some(r) = cmp_op(op, &x, &y) {
        return Ok(r);
    }
    Ok(match op {
        CoreOp::Add => norm(x + y),
        CoreOp::Sub => norm(x - y),
        CoreOp::Mul => norm(x * y),
        CoreOp::Div => norm(x / y),
        CoreOp::Rem => norm(x % y),
        _ => return Err(format!("op {op:?} not defined for Int")),
    })
}

fn prim(op: CoreOp, a: &Rv, b: &Rv) -> Result<Rv, String> {
    if let (Rv::Float(x), Rv::Float(y)) = (a, b) {
        return dispatch_float_op(op, *x, *y);
    }
    if let (Rv::Int(x), Rv::Int(y)) = (a, b) {
        return dispatch_int_op(op, *x, *y);
    }
    let (Some(x), Some(y)) = (to_big(a), to_big(b)) else {
        return Err("arithmetic on non-numeric value".into());
    };
    dispatch_bigint_op(op, x, y)
}

fn norm(n: BigInt) -> Rv {
    i64::try_from(&n).map_or_else(|_| Rv::Big(n), Rv::Int)
}

fn to_big(v: &Rv) -> Option<BigInt> {
    match v {
        Rv::Int(n) => Some(BigInt::from(*n)),
        Rv::Big(n) => Some(n.clone()),
        _ => None,
    }
}

fn low64(v: &Rv) -> Result<u64, String> {
    match v {
        Rv::Int(n) => Ok(n.cast_unsigned()),
        Rv::Big(n) => {
            let lo = n.iter_u64_digits().next().unwrap_or(0);
            Ok(if n.sign() == Sign::Minus {
                lo.wrapping_neg()
            } else {
                lo
            })
        }
        _ => Err("to_i64/to_u64: wrong args".into()),
    }
}

fn fixed2(a: &Rv, b: &Rv, f: fn(u64, u64) -> u64) -> Result<Rv, String> {
    match (a, b) {
        (Rv::I64(x), Rv::I64(y)) => Ok(Rv::I64(
            f(x.cast_unsigned(), y.cast_unsigned()).cast_signed(),
        )),
        (Rv::U64(x), Rv::U64(y)) => Ok(Rv::U64(f(*x, *y))),
        _ => Err("fixed-width op: wrong args".into()),
    }
}

const fn ord(o: Ordering) -> Rv {
    Rv::Int(match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    })
}

// Core patterns are shallow after match compilation: a ctor or tuple test whose
// fields are plain binders, or a catch-all that binds the whole scrutinee.
fn match_pat(p: &CorePat, v: &Rv) -> Option<Vec<(Sym, Rv)>> {
    match (p, v) {
        (CorePat::Wild, _) => Some(vec![]),
        (CorePat::Var(x), _) => Some(vec![(*x, v.clone())]),
        (CorePat::Ctor(name, fields), Rv::Data(dname, vals))
            if name == dname && fields.len() == vals.len() =>
        {
            Some(bind_fields(fields, vals))
        }
        (CorePat::Tuple(fields), Rv::Tuple(vals)) if fields.len() == vals.len() => {
            Some(bind_fields(fields, vals))
        }
        _ => None,
    }
}

// Bind each named field position to its value, ignoring wildcard positions.
fn bind_fields(fields: &[Option<Sym>], vals: &[Rv]) -> Vec<(Sym, Rv)> {
    fields
        .iter()
        .zip(vals.iter())
        .filter_map(|(b, val)| b.map(|s| (s, val.clone())))
        .collect()
}

#[must_use]
pub fn globals(core: &Core) -> BTreeMap<Sym, CoreFn> {
    core.fns.iter().map(|f| (f.name, f.clone())).collect()
}

/// Run `core` capturing all `print` output into the returned [`Run`]'s `term`
/// (the differential oracle and wasm path), reading input from an empty source.
/// Nothing reaches real stdio.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults.
pub fn run(core: &Core) -> Result<Run, String> {
    let mut sink: Vec<u8> = Vec::new();
    let mut input = io::Cursor::new(Vec::new());
    run_io(core, &mut sink, &mut input)
}

/// Run `core` with a host-supplied output sink and input source.
///
/// The native CLI passes real stdout/stdin here for live streaming; the oracle
/// passes in-memory buffers. `term` always carries the exact transcript
/// regardless of the sink.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults.
pub fn run_io(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<Run, String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let mut m = Machine::new(&g, out_sink, input);
    let value = m.comp(&Env::default(), &main.body)?;
    Ok(Run {
        value,
        out: m.out,
        term: m.term,
        exit: m.exit,
    })
}

/// The result of a traced run: the transcript plus the observation trace and how
/// far the run got.
#[derive(Debug)]
pub struct TracedRun {
    /// The full `print` transcript, exactly as it reached the sink.
    pub term: String,
    /// `Some(code)` when the program called `exit(code)`.
    pub exit: Option<i32>,
    /// Under `Record`, the observations captured; under `Replay`, the trace
    /// that was served (unchanged), so a debugger can inspect it.
    pub frames: Vec<Obs>,
    /// Observations performed before the run ended (finished or hit a budget).
    pub observed: usize,
    /// Whether the run stopped at a replay budget rather than running to
    /// completion, which is how replay-to-N halts.
    pub halted: bool,
}

/// Run `core` under a [`Tape`], returning the transcript and the observation
/// trace.
///
/// This is the one entry the record/replay/debug drivers share: `Record`
/// captures a trace against the real world, `Replay` reproduces a recorded run
/// (byte-identically, by determinism), and a `Replay` with a budget halts after
/// N observations for reverse-step debugging.
///
/// # Errors
/// Fails when `main` is missing, evaluation faults, or a replayed trace does not
/// match the program.
pub fn run_traced(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    tape: Tape,
) -> Result<TracedRun, String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let mut m = Machine::new(&g, out_sink, input);
    m.set_tape(tape);
    m.comp(&Env::default(), &main.body)?;
    let frames = match m.tape {
        Tape::Record(frames) | Tape::Replay { frames, .. } => frames,
        Tape::Live => Vec::new(),
    };
    Ok(TracedRun {
        term: m.term,
        exit: m.exit,
        frames,
        observed: m.observed,
        halted: m.halted,
    })
}

/// The result of a suspendable run: either the program ran to completion, or it
/// paused at the step budget with its whole state captured as a [`kont::Kont`].
#[derive(Debug)]
pub enum Checkpoint {
    /// The program finished before the budget; there was nothing to suspend.
    Done(Run),
    /// The program paused; the continuation is the whole suspended machine. The
    /// prefix output has already streamed to the caller's sink.
    Suspended(kont::Kont),
}

// Snapshot the machine's scalar registers and the loop's live state into a
// `Kont`. The prefix trace rides along when the run was recording, so the snapshot
// is a complete replayable record (a whole suspended program), not only a
// continuation; a live run carries no trace.
fn snapshot(m: Machine<'_>, bundle: String, stack: Vec<Frame>, state: State) -> kont::Kont {
    let state = match state {
        State::Eval(c, env) => kont::KontState::Eval(c, env),
        State::Ret(v) => kont::KontState::Ret(v),
    };
    let trace = match m.tape {
        Tape::Record(frames) | Tape::Replay { frames, .. } => frames,
        Tape::Live => Vec::new(),
    };
    kont::Kont {
        bundle,
        stack,
        state,
        rng: m.rng,
        fn_name: m.fn_name,
        observed: m.observed,
        exit: m.exit,
        trace,
    }
}

/// Run `core`, pausing after `budget` machine steps.
///
/// The whole live continuation is captured as a [`kont::Kont`] tagged with
/// `bundle` (the program's code-identity digest, checked when it is later resumed).
/// Output streams to `out_sink` up to the pause exactly as an ordinary run would;
/// a `budget` past the program's length simply runs to completion ([`Checkpoint::Done`]).
///
/// # Errors
/// Fails when `main` is missing or evaluation faults before the budget.
pub fn run_suspending(
    core: &Core,
    bundle: String,
    budget: usize,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<Checkpoint, String> {
    run_suspending_in(&globals(core), bundle, budget, out_sink, input)
}

/// Like [`run_suspending`] but over an already-built global table.
///
/// Building the table deep-clones every function body, so a caller that runs the
/// same program under many budgets (mapping line boundaries) builds it once and
/// reuses it here rather than paying that clone per budget.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults before the budget.
pub fn run_suspending_in(
    g: &BTreeMap<Sym, CoreFn>,
    bundle: String,
    budget: usize,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<Checkpoint, String> {
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let root = lower(&main.body);
    let mut m = Machine::new(g, out_sink, input);
    m.step_budget = Some(budget);
    match m.run_loop(Vec::new(), State::Eval(root, Env::default()))? {
        Outcome::Done(value) => Ok(Checkpoint::Done(Run {
            value,
            out: m.out,
            term: m.term,
            exit: m.exit,
        })),
        Outcome::Suspended { stack, state } => {
            Ok(Checkpoint::Suspended(snapshot(m, bundle, stack, state)))
        }
    }
}

/// Resume a decoded [`kont::Kont`] against `core` and run it to completion.
///
/// The caller must have verified `kont.bundle` matches `core`'s code identity
/// before calling: resume trusts that the continuation's by-name code references
/// resolve in this program's function table. Output streams to `out_sink` from the
/// resume point on, so a suspend-run's prefix output followed by this suffix output
/// reproduces an uninterrupted run byte for byte.
///
/// # Errors
/// Fails if evaluation faults after the resume point.
pub fn resume_kont(
    core: &Core,
    kont: kont::Kont,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<Run, String> {
    let g = globals(core);
    let mut m = Machine::new(&g, out_sink, input);
    // Restore the registers the loop threads across the cut so the resumed run
    // continues the same random stream and observation count.
    m.rng = kont.rng;
    m.fn_name = kont.fn_name;
    m.observed = kont.observed;
    m.exit = kont.exit;
    let state = match kont.state {
        kont::KontState::Eval(c, env) => State::Eval(c, env),
        kont::KontState::Ret(v) => State::Ret(v),
    };
    match m.run_loop(kont.stack, state)? {
        Outcome::Done(value) => Ok(Run {
            value,
            out: m.out,
            term: m.term,
            exit: m.exit,
        }),
        // No step budget is set on a resume, so the loop cannot pause again.
        Outcome::Suspended { .. } => Err("resumed continuation paused unexpectedly".into()),
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use num_bigint::BigInt;

    use super::{big_of_str, fmt_g, splitmix64, DEFAULT_SEED, SPLITMIX_GAMMA};

    // `fmt_g` renders the shortest decimal that round-trips back to the same
    // double: full precision, no truncation, scientific only outside [-4, 16).
    // Reference values match Python `repr`. The C runtime and Lean oracle must
    // agree byte for byte (proven against C by `prism_show_float_matches_fmt_g`).
    #[test]
    fn fmt_g_is_shortest_round_trip() {
        let cases: &[(f64, &str)] = &[
            (0.0, "0"),
            (-0.0, "-0"),
            (1.0, "1"),
            (-1.0, "-1"),
            (0.1, "0.1"),
            (0.5, "0.5"),
            (1.5, "1.5"),
            (0.1 + 0.2, "0.30000000000000004"),
            (1.0 / 3.0, "0.3333333333333333"),
            (10.0 / 3.0, "3.3333333333333335"),
            (std::f64::consts::PI, "3.141592653589793"),
            (12.34, "12.34"),
            (100.0, "100"),
            (1_000_000.0, "1000000"),
            (0.0001, "0.0001"),
            (0.00001, "1e-05"),
            (1e15, "1000000000000000"),
            (1e16, "1e+16"),
            (1e100, "1e+100"),
            (1e-100, "1e-100"),
            (1.234_567_89e-5, "1.23456789e-05"),
        ];
        for &(d, want) in cases {
            assert_eq!(fmt_g(d), want, "fmt_g({d})");
            assert_eq!(fmt_g(d).parse::<f64>(), Ok(d), "round-trip fmt_g({d})");
        }
        assert_eq!(fmt_g(f64::NAN), "nan");
        assert_eq!(fmt_g(f64::INFINITY), "inf");
        assert_eq!(fmt_g(f64::NEG_INFINITY), "-inf");
    }

    // Compile the C runtime with a small `prism_main` body and run it, returning
    // the lines it prints. The C runtime is the native backend's source of truth,
    // so executing it pins behavior here directly: a divergence fails because the
    // streams differ, not because a magic substring went missing. That survives a
    // behavior-preserving refactor (rename `z`, hoist a helper, regroup a
    // constant) where a `contains(...)` grep of the source would not, and it
    // actually proves equivalence rather than textual presence. Returns None when
    // no C compiler is available, so the test skips like the parity corpus (CI
    // sets PRISM_CC).
    fn rt_oracle(body: &str) -> Option<Vec<String>> {
        use std::process::Command;
        use std::sync::atomic::{AtomicU64, Ordering};

        // Unique per call: tests run concurrently in one process, so a pid-only
        // path would let two oracles clobber each other's source and binary.
        static SEQ: AtomicU64 = AtomicU64::new(0);

        // Same compiler the runtime was built with (see `cc_link`): keeps this
        // oracle's C on the identical toolchain as the interpreter it checks.
        let cc = std::env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").into());
        if !Command::new(&cc)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
        {
            eprintln!("skipping runtime oracle: C compiler `{cc}` not found (set PRISM_CC)");
            return None;
        }

        let stem = format!(
            "prism_oracle_{}_{}",
            std::process::id(),
            SEQ.fetch_add(1, Ordering::Relaxed)
        );
        let dir = std::env::temp_dir().join(&stem);
        std::fs::create_dir_all(&dir).unwrap();
        let src = dir.join(format!("{stem}.c"));
        let bin = dir.join(&stem);
        // Materialize the split runtime modules from the one canonical list and
        // compile all of them, so this oracle links the same sources the native
        // backend does. The vendored libm is linked as the one pre-built archive
        // (the same bytes the interpreter and native backend use), not recompiled.
        let rt_sources = crate::codegen::rt::write_runtime(&dir).unwrap();
        let libm_archive = crate::codegen::rt::write_libm_archive(&dir).unwrap();
        // The runtime owns `main` and calls `prism_main`; the harness supplies it
        // and returns a tagged immediate 0 (exit code 0).
        std::fs::write(
            &src,
            format!(
                "#include <stdio.h>\n#include <string.h>\n\
                 long prism_prim_rand(void);\n\
                 long prism_str_lit(const char *, long);\n\
                 long prism_big_of_str(long, int *);\n\
                 long prism_big_show(long);\n\
                 void print_str(long);\n\
                 long prism_main(void) {{\n{body}\nreturn 1;\n}}\n"
            ),
        )
        .unwrap();
        let comp = Command::new(&cc)
            .args(["-O0", "-w"])
            .arg(&src)
            .args(&rt_sources)
            .arg(&libm_archive)
            .arg("-o")
            .arg(&bin)
            .output()
            .unwrap();
        assert!(
            comp.status.success(),
            "runtime oracle failed to compile:\n{}",
            String::from_utf8_lossy(&comp.stderr)
        );
        let run = Command::new(&bin).output().unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        assert!(
            run.status.success(),
            "runtime oracle crashed: {:?}",
            run.status
        );
        Some(
            String::from_utf8(run.stdout)
                .unwrap()
                .lines()
                .map(str::to_owned)
                .collect(),
        )
    }

    // The C runtime's float printer is the native backend's source of truth and
    // must match the interpreter's `fmt_g` byte for byte (they are differentially
    // tested). Pass exact bit patterns so no C literal parsing intervenes, then
    // run `prism_show_float` as the oracle.
    #[test]
    fn prism_show_float_matches_fmt_g() {
        let vals: &[f64] = &[
            0.0,
            -0.0,
            1.0,
            -1.0,
            0.1,
            0.5,
            1.5,
            0.1 + 0.2,
            1.0 / 3.0,
            10.0 / 3.0,
            std::f64::consts::PI,
            12.34,
            100.0,
            1_000_000.0,
            0.0001,
            0.00001,
            1e15,
            1e16,
            1e100,
            1e-100,
            1.234_567_89e-5,
            123.456,
            9.999_999e5,
            f64::MAX,
            f64::MIN_POSITIVE,
        ];
        let want: Vec<String> = vals.iter().map(|&d| fmt_g(d)).collect();
        let mut body = String::from("long prism_show_float(long);\n");
        for &d in vals {
            let bits = d.to_bits().cast_signed();
            let _ = writeln!(
                body,
                "{{ long b = {bits}L; print_str(prism_show_float(b)); }}"
            );
        }
        let Some(lines) = rt_oracle(&body) else {
            return;
        };
        assert_eq!(
            lines, want,
            "C prism_show_float diverged from interpreter fmt_g"
        );
    }

    // An unseeded `rand` must stream identical values on every backend, so the
    // interpreter's SplitMix64 and the C runtime's must be the same generator.
    // Pin the interpreter to a hand-verified golden vector, then run the C
    // runtime as the oracle: its `prism_prim_rand()` (which drops the low 2 bits) must
    // equal `splitmix64() >> 2`. Drift in either implementation fails here, not
    // only in the end-to-end corpus.
    #[test]
    fn splitmix64_matches_runtime() {
        assert_eq!(DEFAULT_SEED, SPLITMIX_GAMMA);
        let mut state = DEFAULT_SEED;
        let golden: Vec<u64> = (0..4).map(|_| splitmix64(&mut state)).collect();
        assert_eq!(
            golden,
            [
                0x6E78_9E6A_A1B9_65F4,
                0x06C4_5D18_8009_454F,
                0xF88B_B8A8_724C_81EC,
                0x1B39_896A_51A8_749B,
            ]
        );

        let Some(lines) =
            rt_oracle("for (int i = 0; i < 4; i++) printf(\"%ld\\n\", prism_prim_rand());")
        else {
            return;
        };
        let want: Vec<String> = golden.iter().map(|z| (z >> 2).to_string()).collect();
        assert_eq!(
            lines, want,
            "C runtime rand() stream diverged from interpreter"
        );
    }

    // Bignum decimal parsing must agree with the C runtime's `prism_big_of_str`
    // so a literal that overflows the immediate parses to the same value on every
    // backend. Pin the interpreter against golden values, then run the C runtime
    // as the oracle: it must parse each literal to the same value and reject the
    // same inputs (ok=0, surfaced as "ERR") the interpreter rejects with None.
    #[test]
    fn big_of_str_matches_runtime() {
        use std::str::FromStr;

        let cases = [
            ("0", "0"),
            ("  42 ", "42"),
            (
                "-170141183460469231731687303715884105728",
                "-170141183460469231731687303715884105728",
            ),
            (
                "99999999999999999999999999999999",
                "99999999999999999999999999999999",
            ),
            ("+1000000000000000000000", "1000000000000000000000"),
        ];
        for &(input, want) in &cases {
            assert_eq!(
                big_of_str(input),
                Some(BigInt::from_str(want).unwrap()),
                "big_of_str({input:?})"
            );
        }
        assert_eq!(big_of_str("12x3"), None);
        assert_eq!(big_of_str(""), None);

        // Both the accepted literals and the rejected ones go through the C
        // parser; "ERR" mirrors the interpreter's None.
        let inputs: Vec<&str> = cases.iter().map(|&(i, _)| i).chain(["12x3", ""]).collect();
        let want: Vec<String> = inputs
            .iter()
            .map(|s| big_of_str(s).map_or_else(|| "ERR".to_owned(), |b| b.to_string()))
            .collect();
        let mut body = String::new();
        for s in &inputs {
            let _ = writeln!(
                body,
                "{{ const char *t = \"{esc}\"; long c = prism_str_lit(t, (long)strlen(t)); \
                 int ok = 0; long b = prism_big_of_str(c, &ok); \
                 if (!ok) printf(\"ERR\\n\"); else print_str(prism_big_show(b)); }}",
                esc = s.escape_default()
            );
        }
        let Some(lines) = rt_oracle(&body) else {
            return;
        };
        assert_eq!(
            lines, want,
            "C runtime big_of_str diverged from interpreter"
        );
    }
}
