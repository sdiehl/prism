use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io::Write as _;
use std::rc::Rc;
use std::{io, mem};

use num_bigint::BigInt;

use crate::core::builtins::Builtin;
use crate::core::{Comp, Core, CoreFn, CorePat};
use crate::lineage::provenance::{
    CapEvent, CapOp, EventValue, Observation, OP_CONSOLE_EPRINT, OP_CONSOLE_NEWLINE,
    OP_CONSOLE_PRINT, OP_CONSOLE_READ_INT, OP_CONSOLE_READ_LINE, OP_RANDOM_RAND,
};
use crate::names::ENTRY_POINT;
use crate::sym::Sym;
use crate::types::{CONS, FLOAT_BUF, NIL};

/// The `kont`-kind wire codec.
///
/// Serializes a live interpreter continuation (the frame stack, the lowered node
/// graph, and the runtime values it holds) as a portable envelope, and reads one
/// back.
pub mod kont;
#[cfg(test)]
mod runtime_oracle;

mod builtin;
mod node;
mod tape;

pub use builtin::fmt_g;
pub use node::{Atom, Cmp, HandleInfo, Node};
pub use tape::{Obs, Tape};

use builtin::{float_builtin, neg_rv, prim, str_builtin};
use node::{lower, lower_runtime};
use tape::{
    capability_obs, event_args, event_value_of_rv, obs_label, obs_of_rv, rv_of_obs, write_obs,
    ObsKind,
};

// How values that have no surface syntax render in `show`/`repr`. `print` goes
// through `show`, so these must stay byte-identical to the native runtime's own
// output; keeping them as named constants makes that contract changeable in one
// place rather than as ad-hoc literals.
const UNIT_REPR: &str = "()";
const FUNCTION_REPR: &str = "<function>";
const CONTINUATION_REPR: &str = "<continuation>";
const LOCAL_REF_REPR: &str = "<local-ref>";

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
    // An unboxed typed buffer of raw 8-byte words (`runtime/prism_tbuf.c`), the
    // flat storage under the tensor library. Held as raw bits (not boxed `Rv`s) so
    // it threads bit-for-bit identically to the native buffer cell, including NaN
    // payloads and subnormals; shared via `Rc`, copied on write, mirroring the
    // runtime's rc==1 in-place / shared-copy discipline.
    TBuf(Rc<Vec<u64>>),
    // A baseline 128-bit SIMD vector: two raw 64-bit words (float lanes as their
    // double bit patterns, integer lanes as two's-complement). Opaque: produced
    // and consumed only by the `simd_*` builtins, never shown, compared,
    // serialized, or hashed. Boxed so the two-word payload does not widen the
    // `Rv` enum (which every evaluator frame carries), keeping the recursive
    // render/drop stack depth of ordinary programs unchanged.
    Vec128(Rc<[u64; 2]>),
    Resume(Rc<[Frame]>),
    // Verification-only runtime form for an effect-lowered local `var`. Ordinary
    // source interpretation never constructs it; only the explicit lowered-Core
    // evaluator does.
    Ref(Rc<RefCell<Self>>),
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
            Self::TBuf(_) => FLOAT_BUF,
            Self::Vec128(_) => "Vec128",
            Self::Resume(_) => "Resume",
            Self::Ref(_) => "Ref",
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
            Self::Ref(_) => LOCAL_REF_REPR.into(),
            // Opaque: a SIMD vector has no surface representation. It only ever
            // reaches here through a diagnostic path, never ordinary output.
            Self::Vec128(_) => "<simd>".into(),
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
            // A debug fallback: the tensor library owns user-facing rendering.
            Self::TBuf(words) => {
                let elems: Vec<String> = words.iter().map(|w| fmt_g(f64::from_bits(*w))).collect();
                format!("fbuf[{}]", elems.join(", "))
            }
        }
    }

    fn list_elems(&self) -> Option<Vec<&Self>> {
        let mut es = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Self::Data(n, fs) if n.as_str() == NIL && fs.is_empty() => return Some(es),
                Self::Data(n, fs) if n.as_str() == CONS && fs.len() == 2 => {
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
    args: Rc<[String]>,
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
    // The provenance event stream, captured at the same observe sites as the tape
    // frames whenever the tape is not `Live` (record or replay). `Some` mirrors
    // "this run is being observed"; a live run leaves it `None` and pays nothing.
    // Record and replay of one trace produce an identical stream by determinism.
    events: Option<Vec<CapEvent>>,
    observations: Option<Vec<Observation>>,
    // Suspension: `step_budget` pauses the loop after that many machine steps (a
    // whole-program checkpoint), `steps` counts them. `None` is the ordinary
    // unbounded run. Steps are pure state transitions, so a given budget stops the
    // machine at a deterministic point, the basis of the `kont` snapshot.
    step_budget: Option<usize>,
    steps: usize,
    // The step ruler: when armed, every observation (capability read or output
    // boundary) is marked with the machine step at which it fired. Diagnostic
    // only: marks are collected in every tape mode, never enter the tape or the
    // provenance stream, and an unarmed run pays nothing (the preview is built
    // lazily). See `prism exec steps` and the suspend cut report.
    ruler: Option<Vec<StepMark>>,
    // A named cut predicate (`--at-call` / `--at-op`): when armed, the machine
    // watches the deterministic step stream for the named program point and, on
    // reaching it, records the equivalent step budget plus the def stack and
    // pauses there. Interpreter-only and armed only by the suspend/debug drivers,
    // so tier/backend parity is untouched and the program cannot observe it.
    cut: Option<CutState>,
}

/// One observation on the machine-step clock: the step at which it fired, its
/// canonical operation label, and a short rendering of what it read or wrote.
#[derive(Debug, Clone)]
pub struct StepMark {
    pub step: usize,
    pub op: &'static str,
    pub preview: String,
}

/// A named cut predicate for a suspend: pause at a program point named by a
/// definition or a capability op, instead of by an opaque step count.
///
/// Both are pure functions of the deterministic step stream, so the pause they
/// pick reduces to a single equivalent `--at N` and reproduces the identical
/// snapshot. Diagnostic-only and interpreter-only: the program cannot observe
/// which predicate armed the machine, only whether it ran.
#[derive(Debug, Clone)]
pub enum CutPredicate {
    /// Pause on entering the `nth` (1-based) call to the global definition `def`.
    Call { def: Sym, nth: usize },
    /// Pause just before the `nth` (1-based) performance of the capability op
    /// whose canonical label is `op` (`Console.print`, `FileSystem.read_file`, ...).
    Op { op: &'static str, nth: usize },
}

/// What a fired [`CutPredicate`] recorded: the equivalent `--at N` budget that
/// reproduces the pause, and the call-provenance stack at that point.
#[derive(Debug, Clone)]
pub struct CutOutcome {
    /// The `--at N` budget that pauses at the identical machine state. The named
    /// cut is exactly as reproducible as this step count.
    pub equiv_at: usize,
    /// The def stack at the cut, outermost caller first, the paused definition
    /// last: `[main, ..., f]`.
    pub def_stack: Vec<Sym>,
}

// The armed cut and its progress. `seen` counts matching events; the predicate
// fires when it reaches its `nth`, recording an outcome once and never again.
// Held only when a suspend/debug driver arms it, so an ordinary run pays nothing
// and cannot observe it.
struct CutState {
    pred: CutPredicate,
    seen: usize,
    outcome: Option<CutOutcome>,
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
        Self::new_with_args(globals, out_sink, input, Vec::new())
    }

    #[must_use]
    pub fn new_with_args(
        globals: &BTreeMap<Sym, CoreFn>,
        out_sink: &'a mut dyn io::Write,
        input: &'a mut dyn io::BufRead,
        args: Vec<String>,
    ) -> Self {
        Self::new_with_lowerer(globals, out_sink, input, args, lower)
    }

    fn new_lowered_with_args(
        globals: &BTreeMap<Sym, CoreFn>,
        out_sink: &'a mut dyn io::Write,
        input: &'a mut dyn io::BufRead,
        args: Vec<String>,
    ) -> Self {
        Self::new_with_lowerer(globals, out_sink, input, args, lower_runtime)
    }

    fn new_with_lowerer(
        globals: &BTreeMap<Sym, CoreFn>,
        out_sink: &'a mut dyn io::Write,
        input: &'a mut dyn io::BufRead,
        args: Vec<String>,
        lowerer: fn(&Comp) -> Cmp,
    ) -> Self {
        Self {
            fns: globals
                .iter()
                .map(|(k, f)| (*k, (Rc::from(f.params.as_slice()), lowerer(&f.body))))
                .collect(),
            out: Vec::new(),
            term: String::new(),
            rng: DEFAULT_SEED,
            fn_name: ENTRY_POINT.into(),
            out_sink,
            input,
            args: Rc::from(args),
            exit: None,
            tape: Tape::Live,
            observed: 0,
            halted: false,
            events: None,
            observations: None,
            step_budget: None,
            steps: 0,
            ruler: None,
            cut: None,
        }
    }

    /// Arm the step ruler: from here on, every observation is marked with the
    /// machine step at which it fired.
    pub fn arm_ruler(&mut self) {
        self.ruler = Some(Vec::new());
    }

    /// The marks collected since [`arm_ruler`](Self::arm_ruler), in step order.
    pub fn take_ruler(&mut self) -> Vec<StepMark> {
        self.ruler.take().unwrap_or_default()
    }

    /// Machine steps taken so far.
    #[must_use]
    pub const fn steps_taken(&self) -> usize {
        self.steps
    }

    // Mark one observation on the step ruler, when armed. The preview closure
    // only runs on an armed machine, so ordinary runs pay nothing for it.
    fn mark(&mut self, op: &'static str, preview: impl FnOnce() -> String) {
        if let Some(marks) = &mut self.ruler {
            marks.push(StepMark {
                step: self.steps,
                op,
                preview: preview(),
            });
        }
    }

    /// Arm a named cut predicate: the machine watches the step stream for the
    /// named program point and records where it lands. Interpreter-only.
    pub fn arm_cut(&mut self, pred: CutPredicate) {
        self.cut = Some(CutState {
            pred,
            seen: 0,
            outcome: None,
        });
    }

    /// The outcome of an armed cut, if its predicate fired. `None` when nothing
    /// was armed or the program ended before the k-th event.
    pub fn take_cut_outcome(&mut self) -> Option<CutOutcome> {
        self.cut.take().and_then(|cut| cut.outcome)
    }

    // The call-provenance stack at this instant: the caller chain the live
    // `Restore` frames record, outermost first, then the definition currently
    // executing. Read off the frame stack the machine already keeps, so it costs
    // nothing per call and materializes only at a cut; tail calls (whose frames
    // collapse) and resumed continuations (whose frames are back on the stack)
    // are handled for free, because the frames are the ground truth.
    fn def_stack(&self, stack: &[Frame]) -> Vec<Sym> {
        let mut defs: Vec<Sym> = stack
            .iter()
            .filter_map(|frame| match frame {
                Frame::Restore(name) => Some(*name),
                _ => None,
            })
            .collect();
        defs.push(self.fn_name);
        defs
    }

    // Record entry to global definition `name`'s body for an armed `--at-call`
    // cut. On the k-th matching entry it captures the def stack and the
    // equivalent `--at N` budget (the current step count: pausing after this
    // call transition lands on the same state `--at N` would), then arms that
    // budget so the ordinary suspend path performs the pause identically.
    fn note_call_entry(&mut self, name: Sym, stack: &[Frame]) {
        // Only an unfired call cut for this definition acts; anything else returns
        // on the match alone.
        let Some(CutState {
            pred: CutPredicate::Call { def, nth },
            outcome: None,
            ..
        }) = &self.cut
        else {
            return;
        };
        if *def != name {
            return;
        }
        let nth = *nth;
        let cut = self.cut.as_mut().expect("cut is armed");
        cut.seen += 1;
        if cut.seen < nth {
            return;
        }
        let equiv_at = self.steps;
        let def_stack = self.def_stack(stack);
        self.cut.as_mut().expect("cut is armed").outcome = Some(CutOutcome {
            equiv_at,
            def_stack,
        });
        self.step_budget = Some(equiv_at);
    }

    // Test an armed `--at-op` cut against the transition the machine is about to
    // take. On the k-th performance of the named op it captures the def stack and
    // the equivalent `--at N` budget (the current step count, before the op runs),
    // and returns `true` so the loop pauses here, before the op's effect. Pausing
    // at this same point via `--at N` yields the identical snapshot.
    fn note_op_before(&mut self, state: &State, stack: &[Frame]) -> bool {
        // Only an unfired op cut inspects transitions; a call cut or a spent cut
        // pays only this match, never the label lookup.
        let Some(CutState {
            pred: CutPredicate::Op { op, nth },
            outcome: None,
            ..
        }) = &self.cut
        else {
            return false;
        };
        let (target, nth) = (*op, *nth);
        let State::Eval(node, _) = state else {
            return false;
        };
        if op_label_of(node) != Some(target) {
            return false;
        }
        let cut = self.cut.as_mut().expect("cut is armed");
        cut.seen += 1;
        if cut.seen < nth {
            return false;
        }
        let equiv_at = self.steps;
        let def_stack = self.def_stack(stack);
        self.cut.as_mut().expect("cut is armed").outcome = Some(CutOutcome {
            equiv_at,
            def_stack,
        });
        true
    }

    /// Governs this machine's capability I/O for record/replay/debug.
    ///
    /// Record and replay also arm the provenance event stream, so a recorded run
    /// and a replay of its trace carry the identical observation events.
    pub fn set_tape(&mut self, tape: Tape) {
        self.events = match tape {
            Tape::Live => None,
            Tape::Record(_) | Tape::Replay { .. } | Tape::Durable { .. } => Some(Vec::new()),
        };
        self.observations = match tape {
            Tape::Live => None,
            Tape::Record(_) | Tape::Replay { .. } | Tape::Durable { .. } => Some(Vec::new()),
        };
        self.tape = tape;
    }

    // Append one capability observation to the provenance stream, when armed. The
    // op label and arguments are known at the call site; the result is the value
    // the observation produced (a real read under record, a served frame under
    // replay), so the same event is recorded either way.
    fn record_event(&mut self, op: CapOp, args: Vec<EventValue>, result: &Rv) {
        if let Some(events) = &mut self.events {
            let event = CapEvent {
                op,
                args,
                result: event_value_of_rv(result),
            };
            events.push(event.clone());
            if let Some(observations) = &mut self.observations {
                observations.push(Observation::Capability(event));
            }
        }
    }

    // Append one file-write output event to the provenance stream, when armed. The
    // path is the first argument; the committed content (a string or byte buffer, or
    // nothing for a removal) is the result. Recorded in both record and replay, so a
    // run that writes files reproduces the identical events on replay.
    fn record_write_event(&mut self, op: CapOp, vals: &[Rv]) -> Result<(), String> {
        let args = vals.first().map(event_value_of_rv).into_iter().collect();
        let result = vals.get(1).map_or(EventValue::Unit, event_value_of_rv);
        let event = CapEvent { op, args, result };
        if let Some(events) = &mut self.events {
            events.push(event.clone());
        } else {
            return Ok(());
        }
        let path = vals.first().and_then(|value| match value {
            Rv::Str(path) => Some(path.as_str()),
            _ => None,
        });
        if let (Some(path), Some(observations)) = (path, self.observations.as_mut()) {
            if op == crate::lineage::provenance::OP_FS_REMOVE_FILE {
                observations.push(Observation::Capability(event));
            } else {
                let committed = std::fs::read(path)
                    .map_err(|error| format!("observe committed file {path:?}: {error}"))?;
                observations.push(Observation::FileCommit {
                    path: path.to_string(),
                    digest: crate::lineage::provenance::sha256_hex(&committed),
                });
            }
        }
        Ok(())
    }

    fn record_output(&mut self, op: CapOp, text: String) {
        if let Some(observations) = &mut self.observations {
            observations.push(match op {
                OP_CONSOLE_EPRINT => Observation::Stderr(text.into_bytes()),
                OP_CONSOLE_PRINT | OP_CONSOLE_NEWLINE => Observation::Stdout(text.into_bytes()),
                _ => unreachable!("only console output operations record output"),
            });
        }
    }

    // True when a replay/durable budget is set and already reached, so the next
    // observation must halt the run instead of being performed. Under `Durable`
    // this is the deterministic mid-run crash: the run stops with exactly the
    // observations committed so far durably on disk.
    const fn budget_hit(&self) -> bool {
        match &self.tape {
            Tape::Replay {
                budget: Some(b), ..
            }
            | Tape::Durable {
                budget: Some(b), ..
            } => self.observed >= *b,
            _ => false,
        }
    }

    // Serve the next already-committed frame of a durable run, advancing the
    // cursor, or `None` once the committed prefix is exhausted (the point the run
    // goes live and starts appending). Returns the frame's zero-based index so a
    // mismatch can name the failing event, exactly like `next_frame`.
    fn durable_next_committed(&mut self) -> Option<(usize, Obs)> {
        if let Tape::Durable { frames, cursor, .. } = &mut self.tape {
            if *cursor < frames.len() {
                let index = *cursor;
                let frame = frames[index].clone();
                *cursor += 1;
                return Some((index, frame));
            }
        }
        None
    }

    // Commit one observation to the durable log, the sole persistence point of a
    // live durable step. The append flushes the frame and advances the log's
    // committed extent atomically, so a crash after it recovers the frame and one
    // before it does not.
    fn durable_commit(&mut self, obs: &Obs) -> Result<(), String> {
        if let Tape::Durable { log, .. } = &mut self.tape {
            log.append(obs)
                .map_err(|e| format!("durable log append failed: {e}"))?;
        }
        Ok(())
    }

    // Consume the next recorded frame under `Replay`, advancing the cursor. The
    // returned index is that frame's zero-based position in the trace, so a
    // mismatch downstream can name the failing event. A spent trace is a mismatch:
    // the program asked for more than was recorded.
    fn next_frame(&mut self) -> Result<(usize, Obs), String> {
        match &mut self.tape {
            Tape::Replay { frames, cursor, .. } => {
                let index = *cursor;
                let f = frames.get(index).cloned().ok_or_else(|| {
                    format!(
                        "replay: trace exhausted before the program finished \
                         (needed event {index}, trace has {})",
                        frames.len()
                    )
                })?;
                *cursor += 1;
                Ok((index, f))
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
        op: CapOp,
        args: Vec<EventValue>,
        kind: ObsKind,
        real: impl FnOnce(&mut Self) -> Result<Rv, String>,
    ) -> Result<Rv, String> {
        if matches!(self.tape, Tape::Live) {
            let v = real(self)?;
            self.mark(op.label(), || v.show());
            return Ok(v);
        }
        if self.budget_hit() {
            self.halted = true;
            return Ok(Rv::Unit);
        }
        if matches!(self.tape, Tape::Replay { .. }) {
            let (index, frame) = self.next_frame()?;
            let v = rv_of_obs(kind, &frame).map_err(|e| e.explain(index, op.label(), &frame))?;
            self.record_event(op, args, &v);
            self.observed += 1;
            self.mark(op.label(), || v.show());
            return Ok(v);
        }
        if matches!(self.tape, Tape::Durable { .. }) {
            // Replay the committed prefix with no real read; once it is exhausted,
            // perform the real read and commit it durably before serving it.
            if let Some((index, frame)) = self.durable_next_committed() {
                let v =
                    rv_of_obs(kind, &frame).map_err(|e| e.explain(index, op.label(), &frame))?;
                self.record_event(op, args, &v);
                self.observed += 1;
                self.mark(op.label(), || v.show());
                return Ok(v);
            }
            let v = real(self)?;
            let obs = obs_of_rv(kind, &v)?;
            self.durable_commit(&obs)?;
            self.record_event(op, args, &v);
            self.observed += 1;
            self.mark(op.label(), || v.show());
            return Ok(v);
        }
        // Record: perform for real, then log the observation.
        let v = real(self)?;
        let obs = obs_of_rv(kind, &v)?;
        if let Tape::Record(frames) = &mut self.tape {
            frames.push(obs);
        }
        self.record_event(op, args, &v);
        self.observed += 1;
        self.mark(op.label(), || v.show());
        Ok(v)
    }

    // Perform one output observation. Under `Replay` the recorded `Out` boundary
    // is consumed and the output re-performed live (reproducing the transcript);
    // under `Record` the output fires and an `Out` boundary is logged. `op` and
    // `preview` label the boundary on the step ruler when it is armed.
    fn observe_out(
        &mut self,
        op: CapOp,
        preview: impl FnOnce() -> String,
        emit: impl FnOnce(&mut Self) -> Result<(), String>,
    ) -> Result<(), String> {
        if matches!(self.tape, Tape::Live) {
            emit(self)?;
            self.mark(op.label(), preview);
            return Ok(());
        }
        if self.budget_hit() {
            self.halted = true;
            return Ok(());
        }
        if matches!(self.tape, Tape::Replay { .. }) {
            let (index, frame) = self.next_frame()?;
            if frame != Obs::Out {
                return Err(format!(
                    "replay: trace does not match program at event {index}: \
                     expected an output, but the recorded frame is {}",
                    obs_label(&frame)
                ));
            }
            emit(self)?;
            let output = preview();
            self.record_output(op, output.clone());
            self.observed += 1;
            self.mark(op.label(), || output);
            return Ok(());
        }
        if matches!(self.tape, Tape::Durable { .. }) {
            // A committed output already ran in the crashed process: replay it by
            // dropping the boundary (no re-emit), so a resume never double-prints.
            if let Some((index, frame)) = self.durable_next_committed() {
                if frame != Obs::Out {
                    return Err(format!(
                        "replay: trace does not match program at event {index}: \
                         expected an output, but the recorded frame is {}",
                        obs_label(&frame)
                    ));
                }
                let output = preview();
                self.record_output(op, output.clone());
                self.observed += 1;
                self.mark(op.label(), || output);
                return Ok(());
            }
            // Live: commit the boundary durably before emitting, so a crash after
            // the commit drops the output on resume (at most once) rather than
            // re-performing it (never twice).
            self.durable_commit(&Obs::Out)?;
            emit(self)?;
            let output = preview();
            self.record_output(op, output.clone());
            self.observed += 1;
            self.mark(op.label(), || output);
            return Ok(());
        }
        emit(self)?;
        if let Tape::Record(frames) = &mut self.tape {
            frames.push(Obs::Out);
        }
        let output = preview();
        self.record_output(op, output.clone());
        self.observed += 1;
        self.mark(op.label(), || output);
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

    fn comp_lowered(&mut self, env: &Env, c: &Comp) -> Result<Rv, String> {
        self.exec(lower_runtime(c), env.clone())
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
            // An `--at-op` cut pauses before the transition that would perform the
            // named op, so the effect has not yet run and the snapshot matches the
            // equivalent `--at N`. Checked before the budget so the two paths pause
            // at the identical loop position.
            if self.cut.is_some() && self.note_op_before(&state, &stack) {
                return Ok(Outcome::Suspended { stack, state });
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
                    // An armed `--at-call` cut records this body entry (after the
                    // Restore push, so the def stack reads correctly) and arms the
                    // equivalent step budget when it is the k-th entry.
                    if self.cut.is_some() {
                        self.note_call_entry(*name, stack);
                    }
                    State::Eval(body, Rc::new(e2))
                }
            }
            Node::Print(a) => {
                let rv = atom(&env, a)?;
                let s = rv.show();
                self.out.push(rv);
                self.observe_out(
                    OP_CONSOLE_PRINT,
                    || s.clone(),
                    |m| {
                        write!(m.out_sink, "{s}").map_err(|e| format!("print: {e}"))?;
                        m.out_sink.flush().ok();
                        m.term.push_str(&s);
                        Ok(())
                    },
                )?;
                State::Ret(Rv::Unit)
            }
            Node::PrintNl => {
                self.observe_out(
                    OP_CONSOLE_NEWLINE,
                    || "\n".to_string(),
                    |m| {
                        writeln!(m.out_sink).map_err(|e| format!("println: {e}"))?;
                        m.out_sink.flush().ok();
                        m.term.push('\n');
                        Ok(())
                    },
                )?;
                State::Ret(Rv::Unit)
            }
            Node::Rand => {
                State::Ret(self.observe(OP_RANDOM_RAND, Vec::new(), ObsKind::Int, |m| {
                    Ok(Rv::Int((splitmix64(&mut m.rng) >> 2).cast_signed()))
                })?)
            }
            Node::Srand(a) => {
                self.rng = match atom(&env, a)? {
                    Rv::Int(n) => n.cast_unsigned(),
                    _ => return Err("srand: expected Int".into()),
                };
                State::Ret(Rv::Unit)
            }
            Node::ReadInt => {
                State::Ret(
                    self.observe(OP_CONSOLE_READ_INT, Vec::new(), ObsKind::Int, |m| {
                        let mut line = String::new();
                        m.input
                            .read_line(&mut line)
                            .map_err(|e| format!("read_int: {e}"))?;
                        line.trim()
                            .parse::<i64>()
                            .map(Rv::Int)
                            .map_err(|e| format!("read_int: {e}"))
                    })?,
                )
            }
            Node::ReadLine => {
                State::Ret(
                    self.observe(OP_CONSOLE_READ_LINE, Vec::new(), ObsKind::Str, |m| {
                        let mut line = String::new();
                        m.input
                            .read_line(&mut line)
                            .map_err(|e| format!("read_line: {e}"))?;
                        let s = line.strip_suffix('\n').unwrap_or(&line);
                        Ok(Rv::Str(s.strip_suffix('\r').unwrap_or(s).into()))
                    })?,
                )
            }
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
                } else if let Some((kind, op)) = capability_obs(*name) {
                    // A world read (file/env): route through the tape so it is
                    // recorded or served from a trace like the other capabilities.
                    let nm = *name;
                    let ev_args = event_args(&vals);
                    let v =
                        self.observe(op, ev_args, kind, move |m| str_builtin(nm, &vals, &m.args))?;
                    State::Ret(v)
                } else if let Some(op) = write_obs(*name) {
                    // A world write: perform the mutation, then log the provenance
                    // output event. Unlike a read it takes no tape frame and does not
                    // advance the observation count; the write re-runs on replay, so
                    // the event recurs and the trace digest is unchanged.
                    let v = str_builtin(*name, &vals, &self.args)?;
                    self.record_write_event(op, &vals)?;
                    State::Ret(v)
                } else if let (Builtin::Eprint, [Rv::Str(s)]) = (*name, vals.as_slice()) {
                    let s = s.clone();
                    let preview = s.clone();
                    self.observe_out(
                        OP_CONSOLE_EPRINT,
                        move || preview,
                        move |_| {
                            eprint!("{s}");
                            let _ = std::io::stderr().flush();
                            Ok(())
                        },
                    )?;
                    State::Ret(Rv::Unit)
                } else {
                    State::Ret(str_builtin(*name, &vals, &self.args)?)
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
            // Verification-only semantics for the runtime Core forms. RC and
            // allocation choices are deliberately erased; operand evaluation,
            // local mutation, constructor identity, and deterministic faults
            // remain observable.
            Node::RcNoop(value) => {
                let _ = atom(&env, value)?;
                State::Ret(Rv::Unit)
            }
            Node::WithReuse { token, freed, body } => {
                let _ = atom(&env, freed)?;
                let mut next = env;
                Rc::make_mut(&mut next).insert(*token, Rv::Unit);
                State::Eval(Rc::clone(body), next)
            }
            Node::Reuse(token, value) => {
                env.get(token)
                    .ok_or_else(|| format!("unbound reuse token {token} at runtime"))?;
                match atom(&env, value)? {
                    value @ (Rv::Data(..) | Rv::Tuple(_)) => State::Ret(value),
                    _ => return Err("reuse: non-constructor value".into()),
                }
            }
            Node::InitAt(cell, value) => {
                let _ = atom(&env, cell)?;
                match atom(&env, value)? {
                    value @ (Rv::Data(..) | Rv::Tuple(_)) => State::Ret(value),
                    _ => return Err("init_at: non-constructor value".into()),
                }
            }
            Node::RefNew(value) => State::Ret(Rv::Ref(Rc::new(RefCell::new(atom(&env, value)?)))),
            Node::RefGet(cell) => match atom(&env, cell)? {
                Rv::Ref(cell) => {
                    let value = cell
                        .try_borrow()
                        .map_err(|_| "ref_get: cell is already mutably borrowed")?
                        .clone();
                    State::Ret(value)
                }
                _ => return Err("ref_get: non-reference cell".into()),
            },
            Node::RefSet(cell, value) => match atom(&env, cell)? {
                Rv::Ref(cell) => {
                    let value = atom(&env, value)?;
                    *cell
                        .try_borrow_mut()
                        .map_err(|_| "ref_set: cell is already borrowed")? = value;
                    State::Ret(Rv::Unit)
                }
                _ => return Err("ref_set: non-reference cell".into()),
            },
            Node::Bump(args) => match atoms(&env, args)?.as_slice() {
                [Rv::Int(_)] => State::Ret(Rv::Unit),
                _ => return Err("bump: wrong args in lowered verifier".into()),
            },
            // Region brackets: no regions in the verifier, so enter yields a
            // placeholder token and exit is the identity on the activation's
            // result, both unobservable (the native contract).
            Node::ArenaEnter => State::Ret(Rv::Int(0)),
            Node::ArenaExit(args) => match atoms(&env, args)?.as_slice() {
                [Rv::Int(_), v] => State::Ret(v.clone()),
                _ => return Err("arena_exit: wrong args in lowered verifier".into()),
            },
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
    // sound. This is one of the crate's audited `unsafe` sites (see Cargo.toml
    // `unsafe_code`).
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
    run_io_with_args(core, out_sink, input, Vec::new())
}

/// Like [`run_io`], with explicit host-provided program arguments for
/// `args_count`/`arg`.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults.
pub fn run_io_with_args(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    args: Vec<String>,
) -> Result<Run, String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let mut m = Machine::new_with_args(&g, out_sink, input, args);
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
    /// The provenance events captured under record or replay: one per capability
    /// observation, in order. A recording and a replay of its trace produce the
    /// identical sequence.
    pub events: Vec<CapEvent>,
    /// Complete ordered observable behavior captured at the evaluator boundary.
    pub observations: Vec<Observation>,
    /// Runtime fault captured by the observation-only entry point.
    pub fault: Option<String>,
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
    run_traced_with_args(core, out_sink, input, tape, Vec::new())
}

/// Like [`run_traced`], with explicit host-provided program arguments.
///
/// # Errors
/// Fails when `main` is missing, evaluation faults, or a replayed trace does not
/// match the program.
pub fn run_traced_with_args(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    tape: Tape,
    args: Vec<String>,
) -> Result<TracedRun, String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let mut m = Machine::new_with_args(&g, out_sink, input, args);
    m.set_tape(tape);
    let value = m.comp(&Env::default(), &main.body)?;
    if let Some(observations) = &mut m.observations {
        if let Some(exit) = m.exit {
            observations.push(Observation::Exit(exit));
        } else {
            observations.push(Observation::Return(value.show()));
        }
    }
    let events = m.events.take().unwrap_or_default();
    let observations = m.observations.take().unwrap_or_default();
    // A durable run's authoritative trace is the on-disk log; the in-memory
    // `frames` here is only the committed prefix it replayed, which the driver
    // ignores in favor of reading the committed log back from disk.
    let frames = match m.tape {
        Tape::Record(frames) | Tape::Replay { frames, .. } | Tape::Durable { frames, .. } => frames,
        Tape::Live => Vec::new(),
    };
    Ok(TracedRun {
        term: m.term,
        exit: m.exit,
        frames,
        observed: m.observed,
        halted: m.halted,
        events,
        observations,
        fault: None,
    })
}

/// Run while preserving runtime faults as terminal observations.
///
/// Unlike [`run_traced_with_args`], a language-level runtime fault is returned
/// in the artifact rather than discarded through `Err`; frontend failures remain
/// outside this Core-level entry point.
pub fn run_observed_with_args(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    args: Vec<String>,
) -> TracedRun {
    run_observed_mode(core, out_sink, input, args, false)
}

/// Verification-only observation entry for effect-lowered / RC / reuse Core.
///
/// Ordinary source interpretation intentionally rejects runtime-only Core nodes;
/// this explicit seam gives optimizer gates their semantics without changing the
/// source interpreter's accepted IR.
pub(crate) fn run_observed_lowered_with_args(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    args: Vec<String>,
) -> TracedRun {
    run_observed_mode(core, out_sink, input, args, true)
}

fn run_observed_mode(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    args: Vec<String>,
    lowered: bool,
) -> TracedRun {
    let g = globals(core);
    let Some(main) = g.get(&Sym::new(ENTRY_POINT)) else {
        let fault = "no main function".to_string();
        return TracedRun {
            term: String::new(),
            exit: None,
            frames: Vec::new(),
            observed: 0,
            halted: false,
            events: Vec::new(),
            observations: vec![Observation::Fault(fault.clone())],
            fault: Some(fault),
        };
    };
    let mut m = if lowered {
        Machine::new_lowered_with_args(&g, out_sink, input, args)
    } else {
        Machine::new_with_args(&g, out_sink, input, args)
    };
    m.set_tape(Tape::Record(Vec::new()));
    let result = if lowered {
        m.comp_lowered(&Env::default(), &main.body)
    } else {
        m.comp(&Env::default(), &main.body)
    };
    let fault = match result {
        Ok(value) => {
            if let Some(observations) = &mut m.observations {
                if let Some(exit) = m.exit {
                    observations.push(Observation::Exit(exit));
                } else {
                    observations.push(Observation::Return(value.show()));
                }
            }
            None
        }
        Err(fault) => {
            if let Some(observations) = &mut m.observations {
                observations.push(Observation::Fault(fault.clone()));
            }
            Some(fault)
        }
    };
    let frames = match m.tape {
        Tape::Record(frames) => frames,
        Tape::Live | Tape::Replay { .. } | Tape::Durable { .. } => {
            unreachable!("observed run records")
        }
    };
    TracedRun {
        term: m.term,
        exit: m.exit,
        frames,
        observed: m.observed,
        halted: m.halted,
        events: m.events.take().unwrap_or_default(),
        observations: m.observations.take().unwrap_or_default(),
        fault,
    }
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
        Tape::Record(frames) | Tape::Replay { frames, .. } | Tape::Durable { frames, .. } => frames,
        Tape::Live => Vec::new(),
    };
    let observations = m.observations.unwrap_or_default();
    kont::Kont {
        bundle,
        stack,
        state,
        rng: m.rng,
        fn_name: m.fn_name,
        observed: m.observed,
        exit: m.exit,
        trace,
        observations,
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
    Ok(run_suspending_inner(g, bundle, budget, out_sink, input, false)?.0)
}

/// Like [`run_suspending_in`] with the step ruler armed.
///
/// Alongside the checkpoint, returns the observations performed before the
/// cut, each marked with the machine step at which it fired, so a suspend can
/// report where on the observation timeline it paused.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults before the budget.
pub fn run_suspending_ruled(
    core: &Core,
    bundle: String,
    budget: usize,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<(Checkpoint, Vec<StepMark>), String> {
    run_suspending_inner(&globals(core), bundle, budget, out_sink, input, true)
}

fn run_suspending_inner(
    g: &BTreeMap<Sym, CoreFn>,
    bundle: String,
    budget: usize,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
    ruler: bool,
) -> Result<(Checkpoint, Vec<StepMark>), String> {
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let root = lower(&main.body);
    let mut m = Machine::new(g, out_sink, input);
    m.set_tape(Tape::Record(Vec::new()));
    if ruler {
        m.arm_ruler();
    }
    m.step_budget = Some(budget);
    match m.run_loop(Vec::new(), State::Eval(root, Env::default()))? {
        Outcome::Done(value) => {
            let marks = m.take_ruler();
            Ok((
                Checkpoint::Done(Run {
                    value,
                    out: m.out,
                    term: m.term,
                    exit: m.exit,
                }),
                marks,
            ))
        }
        Outcome::Suspended { stack, state } => {
            let marks = m.take_ruler();
            Ok((
                Checkpoint::Suspended(snapshot(m, bundle, stack, state)),
                marks,
            ))
        }
    }
}

// The canonical capability-op label the machine will perform when it steps this
// node, or `None` for a node that performs no observable capability op. The single
// source of truth for what `--at-op` counts, aligned with the labels the step
// ruler records at the observe sites. Pure: it only inspects the node, never runs
// it, so a cut can recognize an op before its effect fires.
fn op_label_of(node: &Node) -> Option<&'static str> {
    let op = match node {
        Node::Print(_) => OP_CONSOLE_PRINT,
        Node::PrintNl => OP_CONSOLE_NEWLINE,
        Node::ReadInt => OP_CONSOLE_READ_INT,
        Node::ReadLine => OP_CONSOLE_READ_LINE,
        Node::Rand => OP_RANDOM_RAND,
        Node::StrBuiltin(Builtin::Eprint, _) => OP_CONSOLE_EPRINT,
        Node::StrBuiltin(name, _) => match capability_obs(*name) {
            Some((_, op)) => op,
            None => write_obs(*name)?,
        },
        _ => return None,
    };
    Some(op.label())
}

/// Run `core` under a suspend armed with a named cut predicate.
///
/// Runs forward with the step ruler and the cut armed. On the predicate's k-th
/// event the machine pauses at the point named, capturing the whole live
/// continuation as a [`kont::Kont`] and reporting the equivalent `--at N` budget
/// and the def stack. A program that ends before the k-th event runs to
/// completion ([`Checkpoint::Done`]) with no outcome. The cut is a pure function
/// of the deterministic step stream, so the snapshot equals `--at equiv_at`.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults before the cut.
pub fn run_suspending_at_cut(
    core: &Core,
    bundle: String,
    pred: CutPredicate,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<(Checkpoint, Vec<StepMark>, Option<CutOutcome>), String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let root = lower(&main.body);
    let mut m = Machine::new(&g, out_sink, input);
    m.set_tape(Tape::Record(Vec::new()));
    m.arm_ruler();
    m.arm_cut(pred);
    match m.run_loop(Vec::new(), State::Eval(root, Env::default()))? {
        Outcome::Done(value) => {
            let marks = m.take_ruler();
            let outcome = m.take_cut_outcome();
            Ok((
                Checkpoint::Done(Run {
                    value,
                    out: m.out,
                    term: m.term,
                    exit: m.exit,
                }),
                marks,
                outcome,
            ))
        }
        Outcome::Suspended { stack, state } => {
            let marks = m.take_ruler();
            let outcome = m.take_cut_outcome();
            Ok((
                Checkpoint::Suspended(snapshot(m, bundle, stack, state)),
                marks,
                outcome,
            ))
        }
    }
}

/// Run the whole program with the step ruler armed.
///
/// A full live run whose every observation is marked with the machine step at
/// which it fired. Returns the run, the marks in step order, and the total
/// steps taken.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults.
pub fn run_ruler(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<(Run, Vec<StepMark>, usize), String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let mut m = Machine::new(&g, out_sink, input);
    m.arm_ruler();
    let value = m.comp(&Env::default(), &main.body)?;
    let marks = m.take_ruler();
    let steps = m.steps_taken();
    Ok((
        Run {
            value,
            out: m.out,
            term: m.term,
            exit: m.exit,
        },
        marks,
        steps,
    ))
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
    m.set_tape(Tape::Record(kont.trace.clone()));
    m.observations = Some(kont.observations.clone());
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

/// Resume while retaining the snapshot's observation prefix and capturing a
/// terminal return, exit, or fault in one complete trace.
pub fn resume_kont_observed(
    core: &Core,
    kont: kont::Kont,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> TracedRun {
    let g = globals(core);
    let mut m = Machine::new(&g, out_sink, input);
    m.set_tape(Tape::Record(kont.trace.clone()));
    m.observations = Some(kont.observations.clone());
    m.rng = kont.rng;
    m.fn_name = kont.fn_name;
    m.observed = kont.observed;
    m.exit = kont.exit;
    let state = match kont.state {
        kont::KontState::Eval(c, env) => State::Eval(c, env),
        kont::KontState::Ret(v) => State::Ret(v),
    };
    let result = m.run_loop(kont.stack, state);
    let fault = match result {
        Ok(Outcome::Done(value)) => {
            if let Some(observations) = &mut m.observations {
                if let Some(exit) = m.exit {
                    observations.push(Observation::Exit(exit));
                } else {
                    observations.push(Observation::Return(value.show()));
                }
            }
            None
        }
        Ok(Outcome::Suspended { .. }) => {
            let fault = "resumed continuation paused unexpectedly".to_string();
            if let Some(observations) = &mut m.observations {
                observations.push(Observation::Fault(fault.clone()));
            }
            Some(fault)
        }
        Err(fault) => {
            if let Some(observations) = &mut m.observations {
                observations.push(Observation::Fault(fault.clone()));
            }
            Some(fault)
        }
    };
    let frames = match m.tape {
        Tape::Record(frames) => frames,
        Tape::Live | Tape::Replay { .. } | Tape::Durable { .. } => {
            unreachable!("observed resume records")
        }
    };
    let observations = m.observations.take().unwrap_or_default();
    let term = observations
        .iter()
        .filter_map(|observation| match observation {
            Observation::Stdout(bytes) => Some(String::from_utf8_lossy(bytes)),
            _ => None,
        })
        .collect::<String>();
    TracedRun {
        term,
        exit: m.exit,
        frames,
        observed: m.observed,
        halted: m.halted,
        events: m.events.take().unwrap_or_default(),
        observations,
        fault,
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;
    use std::str::FromStr;

    use num_bigint::BigInt;

    use crate::core::{Comp, Core, CoreFn, Value};
    use crate::lineage::provenance::{EventValue, Observation, OP_PROCESS_SYSTEM};

    use super::builtin::big_of_str;
    use super::{
        fmt_g, run_observed_lowered_with_args, run_observed_with_args, run_traced,
        runtime_oracle::rt_oracle, splitmix64, Builtin, Obs, Sym, Tape, TracedRun, DEFAULT_SEED,
        SPLITMIX_GAMMA,
    };

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

    fn main_core(body: Comp) -> Core {
        Core {
            fns: vec![CoreFn {
                name: Sym::new(crate::names::ENTRY_POINT),
                params: Vec::new(),
                body,
                dict_arity: 0,
            }],
        }
    }

    fn observe_lowered(body: Comp) -> TracedRun {
        let mut output = Vec::new();
        let mut input = std::io::Cursor::new(Vec::new());
        run_observed_lowered_with_args(&main_core(body), &mut output, &mut input, Vec::new())
    }

    #[test]
    fn lowered_runtime_mutable_refs_sequence() {
        let cell = Sym::new("cell");
        let before = Sym::new("before");
        let ignored = Sym::new("ignored");
        let after = Sym::new("after");
        let body = Comp::Bind(
            Box::new(Comp::RefNew(Value::Int(1))),
            cell,
            Box::new(Comp::Bind(
                Box::new(Comp::RefGet(Value::Var(cell))),
                before,
                Box::new(Comp::Bind(
                    Box::new(Comp::RefSet(Value::Var(cell), Value::Int(9))),
                    ignored,
                    Box::new(Comp::Bind(
                        Box::new(Comp::RefGet(Value::Var(cell))),
                        after,
                        Box::new(Comp::Return(Value::Tuple(vec![
                            Value::Var(before),
                            Value::Var(after),
                        ]))),
                    )),
                )),
            )),
        );
        assert_eq!(
            observe_lowered(body).observations,
            vec![Observation::Return("(1, 9)".into())]
        );
    }

    #[test]
    fn lowered_runtime_reuse_and_init_at_preserve_values() {
        let token = Sym::new("reuse_token");
        let reused = Sym::new("reused");
        let raw_cell = Sym::new("raw_cell");
        let initialized = Sym::new("initialized");
        let body = Comp::WithReuse {
            token,
            freed: Value::Ctor(Sym::new("Old"), 0, vec![Value::Int(0)]),
            body: Box::new(Comp::Bind(
                Box::new(Comp::Reuse(
                    token,
                    Value::Ctor(Sym::new("New"), 1, vec![Value::Int(7)]),
                )),
                reused,
                Box::new(Comp::Bind(
                    Box::new(Comp::StrBuiltin(Builtin::Bump, vec![Value::Int(2)])),
                    raw_cell,
                    Box::new(Comp::Bind(
                        Box::new(Comp::InitAt(
                            Value::Var(raw_cell),
                            Value::Tuple(vec![Value::Int(8), Value::Int(9)]),
                        )),
                        initialized,
                        Box::new(Comp::Return(Value::Tuple(vec![
                            Value::Var(reused),
                            Value::Var(initialized),
                        ]))),
                    )),
                )),
            )),
        };
        assert_eq!(
            observe_lowered(body).observations,
            vec![Observation::Return("(New(7), (8, 9))".into())]
        );
    }

    #[test]
    fn lowered_runtime_rc_nodes_evaluate_operand_then_return_unit() {
        let dup = Sym::new("dup");
        let drop = Sym::new("drop");
        let body = Comp::Bind(
            Box::new(Comp::Dup(Value::Int(1))),
            dup,
            Box::new(Comp::Bind(
                Box::new(Comp::Drop(Value::Int(2))),
                drop,
                Box::new(Comp::Return(Value::Tuple(vec![
                    Value::Var(dup),
                    Value::Var(drop),
                ]))),
            )),
        );
        assert_eq!(
            observe_lowered(body).observations,
            vec![Observation::Return("((), ())".into())]
        );
    }

    #[test]
    fn lowered_runtime_ref_type_fault_is_deterministic() {
        assert_eq!(
            observe_lowered(Comp::RefGet(Value::Int(0))).observations,
            vec![Observation::Fault("ref_get: non-reference cell".into())]
        );
    }

    #[test]
    #[should_panic(expected = "use the explicit lowered verifier")]
    fn ordinary_observer_still_rejects_runtime_core() {
        let mut output = Vec::new();
        let mut input = std::io::Cursor::new(Vec::new());
        let _ = run_observed_with_args(
            &main_core(Comp::Dup(Value::Int(1))),
            &mut output,
            &mut input,
            Vec::new(),
        );
    }

    #[test]
    fn replay_serves_system_from_trace() {
        let x = Sym::new("system_result");
        let core = main_core(Comp::Bind(
            Box::new(Comp::StrBuiltin(
                Builtin::System,
                vec![Value::Str("exit 99".to_string())],
            )),
            x,
            Box::new(Comp::Return(Value::Var(x))),
        ));
        let mut out = Vec::new();
        let mut input = std::io::Cursor::new(Vec::new());

        let run = run_traced(
            &core,
            &mut out,
            &mut input,
            Tape::Replay {
                frames: vec![Obs::Int(7)],
                cursor: 0,
                budget: None,
            },
        )
        .expect("system should replay from the trace");

        assert_eq!(run.observed, 1);
        assert_eq!(run.events.len(), 1);
        assert_eq!(run.events[0].op, OP_PROCESS_SYSTEM);
        assert_eq!(run.events[0].result, EventValue::Int(7));
    }

    #[test]
    fn replay_eprint_consumes_output_frame() {
        let core = main_core(Comp::StrBuiltin(
            Builtin::Eprint,
            vec![Value::Str("replayed stderr\n".to_string())],
        ));
        let mut out = Vec::new();
        let mut input = std::io::Cursor::new(Vec::new());

        let run = run_traced(
            &core,
            &mut out,
            &mut input,
            Tape::Replay {
                frames: vec![Obs::Out],
                cursor: 0,
                budget: None,
            },
        )
        .expect("eprint should consume an output frame under replay");

        assert_eq!(run.observed, 1);
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
    // Check the interpreter to a hand-verified golden vector, then run the C
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
    // backend. Check the interpreter against golden values, then run the C runtime
    // as the oracle: it must parse each literal to the same value and reject the
    // same inputs (ok=0, surfaced as "ERR") the interpreter rejects with None.
    #[test]
    fn big_of_str_matches_runtime() {
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
