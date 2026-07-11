//! Running programs: the driver's evaluation front doors.
//!
//! Every way the driver runs a source lives here: plain interpretation and the
//! differential oracle, IO-streaming runs, capability recording and trace
//! replay, the reverse-step debugger, and the suspend/resume checkpoint pair
//! that snapshots a paused program as a `kont` envelope. All of them share the
//! `prepared_core` front end and pin their code identity to the program's
//! namespace root.

use std::path::Path;

use crate::debug::trace;
use crate::error::Error;
use crate::eval::{run, run_ruler, run_traced, run_traced_with_args, Run, StepMark, Tape};
use crate::provenance::CapEvent;
use crate::resolve::{default_roots, Root};
use serde::Serialize;

use super::{namespace_identity, prepared_core, stdlib_hash, timing, Config};

// The version of the runtime semantics a snapshot is bound to. Bumped only when a
// change to evaluation that a persisted continuation could observe (scheduler
// mechanics, effect-runtime behavior) ships without moving code identity. Held
// separate from the compiler version so a routine release does not needlessly
// invalidate every snapshot.
const RUNTIME_SEMANTICS_VERSION: &str = "1";

// The semantic execution identity a continuation snapshot is bound to: code
// identity (the namespace root), the standard-library root it links against, the
// scheduler policy, and the runtime-semantics version. Optimization tier and
// backend are deliberately excluded (tier parity proves them unobservable);
// scheduler policy is included because it reorders concurrent execution, so a
// suffix resumed under a different policy need not equal the uninterrupted run.
// Folding all four into one digest means a resume under any changed input is
// refused before a step runs: a snapshot taken under cooperative FIFO cannot be
// resumed under LIFO.
fn execution_bundle(src: &str, roots: &[Root], cfg: &Config) -> Result<String, Error> {
    let code = namespace_identity(src, roots)?.root;
    let stdlib = stdlib_hash()?.root;
    let entries = std::collections::BTreeMap::from([
        ("code".to_string(), code),
        ("stdlib".to_string(), stdlib),
        (
            "scheduler".to_string(),
            crate::core::hash_str(cfg.scheduler.label()),
        ),
        (
            "runtime".to_string(),
            crate::core::hash_str(RUNTIME_SEMANTICS_VERSION),
        ),
    ]);
    Ok(crate::core::hash_root(&entries).into_string())
}

/// # Examples
/// ```
/// let src = prism::with_prelude("fn main() = print(1 + 2)");
/// let run = prism::interpret(&src).unwrap();
/// assert_eq!(run.out[0].show(), "3");
/// ```
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret(src: &str) -> Result<Run, Error> {
    interpret_at(src, Path::new("."))
}

/// Like [`interpret`], resolving any module imports relative to `base`.
///
/// Captures all `print` output into the returned [`Run`]'s `term` (the
/// differential oracle and wasm path); nothing reaches real stdio.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_at(src: &str, base: &Path) -> Result<Run, Error> {
    let core = prepared_core(src, &default_roots(base), &Config::from_env())?;
    run(&core).map_err(Error::RuntimeEvaluation)
}

/// Like [`interpret_at`], but streams `print` to `out_sink` and reads `input`.
///
/// The native CLI passes real stdout/stdin so program output is live and
/// `read_*` reaches the terminal; `term` still carries the exact transcript and
/// `Run::exit` carries any `exit(code)`.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_io_at(
    src: &str,
    base: &Path,
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
) -> Result<Run, Error> {
    interpret_io_on(
        src,
        &default_roots(base),
        out_sink,
        input,
        &Config::from_env(),
    )
}

/// Like [`interpret_io_at`], but against an explicit module search path (a
/// project's source root, its path dependencies, and the stdlib).
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_io_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<Run, Error> {
    interpret_io_on_with_args(src, roots, out_sink, input, cfg, Vec::new())
}

/// Like [`interpret_io_on`], with explicit host-provided program arguments for
/// `args_count`/`arg`.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_io_on_with_args(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
    args: Vec<String>,
) -> Result<Run, Error> {
    let core = prepared_core(src, roots, cfg)?;
    timing::timed_res(
        cfg.timing.as_ref(),
        timing::Phase::Eval,
        "",
        || {
            crate::eval::run_io_with_args(&core, out_sink, input, args)
                .map_err(Error::RuntimeEvaluation)
        },
        |_| timing::RowExtras::default(),
    )
}

/// Run `src` against the real world, recording every capability observation.
///
/// Streams output live (like `interpret_io_on`) and returns the process exit
/// code, if any, plus the encoded `.replay` trace to persist and its length.
///
/// # Errors
/// Fails on any front-end error or an evaluation fault.
pub fn record_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<(Option<i32>, String, usize), Error> {
    record_on_with_args(src, roots, out_sink, input, cfg, Vec::new())
}

/// Like [`record_on`], with explicit host-provided program arguments.
///
/// # Errors
/// Fails on any front-end error or an evaluation fault.
pub fn record_on_with_args(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
    args: Vec<String>,
) -> Result<(Option<i32>, String, usize), Error> {
    let core = prepared_core(src, roots, cfg)?;
    let run =
        crate::eval::run_traced_with_args(&core, out_sink, input, Tape::Record(Vec::new()), args)
            .map_err(Error::RuntimeEvaluation)?;
    Ok((run.exit, trace::encode(&run.frames), run.frames.len()))
}

/// A recorded (or replayed) run reduced to the facts a run-lineage sidecar
/// explains: its exit status, the durable `.replay` trace, its provenance events,
/// and the captured stdout transcript.
///
/// The transcript is byte-identical to what streamed to the sink, so hashing it
/// names the run's output without a second capture path.
#[derive(Debug)]
pub struct RecordedRun {
    /// `Some(code)` when the program called `exit(code)`.
    pub exit: Option<i32>,
    /// The encoded `.replay` trace to persist.
    pub trace: String,
    /// The number of observation frames in the trace.
    pub observations: usize,
    /// The provenance events, one per capability observation, in order.
    pub events: Vec<CapEvent>,
    /// The full `print` transcript, exactly as it reached the sink.
    pub term: String,
}

/// Record a run against the real world, returning everything a run-lineage sidecar
/// needs: the trace to persist, the provenance events, and the captured stdout.
///
/// Output still streams live to `out_sink`, like [`record_on`].
///
/// # Errors
/// Fails on any front-end error or an evaluation fault.
pub fn record_run_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
    args: Vec<String>,
) -> Result<RecordedRun, Error> {
    let core = prepared_core(src, roots, cfg)?;
    let run = run_traced_with_args(&core, out_sink, input, Tape::Record(Vec::new()), args)
        .map_err(Error::RuntimeEvaluation)?;
    Ok(RecordedRun {
        exit: run.exit,
        trace: trace::encode(&run.frames),
        observations: run.frames.len(),
        events: run.events,
        term: run.term,
    })
}

/// Replay `src` against a recorded trace, returning the same [`RecordedRun`] facts.
///
/// Reproduces the run's provenance events exactly (a corollary of determinism), so
/// the run-lineage trace digest a replay computes equals the one the recording did.
///
/// # Errors
/// Fails on a front-end error, a malformed trace, an evaluation fault, or a trace
/// that does not match the program.
pub fn replay_run_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    trace: &str,
    cfg: &Config,
) -> Result<RecordedRun, Error> {
    let core = prepared_core(src, roots, cfg)?;
    let frames = trace::decode(trace).map_err(Error::RuntimeReplay)?;
    let mut empty = std::io::Cursor::new(Vec::new());
    let run = run_traced(
        &core,
        out_sink,
        &mut empty,
        Tape::Replay {
            frames,
            cursor: 0,
            budget: None,
        },
    )
    .map_err(Error::RuntimeReplay)?;
    Ok(RecordedRun {
        exit: run.exit,
        trace: trace::encode(&run.frames),
        observations: run.frames.len(),
        events: run.events,
        term: run.term,
    })
}

/// Replay `src` against a recorded `.replay` trace, performing no real reads.
///
/// Reproduces the original run's output byte for byte (a corollary of the
/// determinism contract) and returns the process exit code, if any.
///
/// # Errors
/// Fails on a front-end error, a malformed trace, an evaluation fault, or a
/// trace that does not match the program.
pub fn replay_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    trace: &str,
    cfg: &Config,
) -> Result<Option<i32>, Error> {
    let core = prepared_core(src, roots, cfg)?;
    let frames = trace::decode(trace).map_err(Error::RuntimeReplay)?;
    let mut empty = std::io::Cursor::new(Vec::new());
    let run = run_traced(
        &core,
        out_sink,
        &mut empty,
        Tape::Replay {
            frames,
            cursor: 0,
            budget: None,
        },
    )
    .map_err(Error::RuntimeReplay)?;
    Ok(run.exit)
}

/// Drive the terminal reverse-step debugger over `src` and a recorded trace:
/// read stepping commands from `cmds`, write the debugger UI to `ui`.
///
/// # Errors
/// Fails on a front-end error, a malformed trace, an I/O error, or a trace that
/// does not match the program.
pub fn debug_on(
    src: &str,
    roots: &[Root],
    trace: &str,
    cmds: &mut dyn std::io::BufRead,
    ui: &mut dyn std::io::Write,
    cfg: &Config,
) -> Result<(), Error> {
    let core = prepared_core(src, roots, cfg)?;
    let frames = trace::decode(trace).map_err(Error::RuntimeReplay)?;
    crate::debug::run_repl(&core, &frames, cmds, ui).map_err(Error::RuntimeDebugger)
}

/// The versioned format tag heading a step-ruler rendering.
pub const STEP_RULER_FORMAT: &str = "prism-step-ruler-v1";

/// One observation on the machine-step clock.
///
/// This is the row shape `prism exec steps` reports.
#[derive(Debug, Clone, Serialize)]
pub struct StepRulerRow {
    /// The machine step at which the observation fired.
    pub step: usize,
    /// The canonical operation label (`Console.print`, `FileSystem.read_file`, ...).
    pub op: String,
    /// A short rendering of what was read or written.
    pub preview: String,
}

/// The step ruler of one full run.
///
/// Every observation with the machine step at which it fired, plus the run's
/// totals. Because a step is a pure state transition, these indices are stable
/// program points: the same source and the same inputs mark the same steps on
/// every machine, which is what makes them usable as suspend budgets.
#[derive(Debug, Serialize)]
pub struct StepRuler {
    /// The versioned format tag ([`STEP_RULER_FORMAT`]).
    pub format: &'static str,
    /// Machine steps the whole run took.
    pub total_steps: usize,
    /// `Some(code)` when the program called `exit(code)`.
    pub exit: Option<i32>,
    /// The observations, in step order.
    pub rows: Vec<StepRulerRow>,
}

fn ruler_row(m: StepMark) -> StepRulerRow {
    StepRulerRow {
        step: m.step,
        op: m.op.to_string(),
        preview: m.preview,
    }
}

/// Run `src` to completion with the step ruler armed.
///
/// Streams output to `out_sink` as an ordinary run and reports every
/// observation with the machine step at which it fired. This is how a suspend
/// budget is picked by eye: pausing "between observation 3 and 4" is any
/// `--at` between their steps.
///
/// # Errors
/// Fails on any front-end error or an evaluation fault.
pub fn step_ruler_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<StepRuler, Error> {
    let core = prepared_core(src, roots, cfg)?;
    let (run, marks, total_steps) =
        run_ruler(&core, out_sink, input).map_err(Error::RuntimeEvaluation)?;
    Ok(StepRuler {
        format: STEP_RULER_FORMAT,
        total_steps,
        exit: run.exit,
        rows: marks.into_iter().map(ruler_row).collect(),
    })
}

/// Where on the observation timeline a suspend paused: how many observations
/// the prefix performed, and the last one before the cut.
#[derive(Debug, Serialize)]
pub struct SuspendCut {
    /// Observations performed before the cut.
    pub observations: usize,
    /// The last observation before the cut, when any.
    pub last: Option<StepRulerRow>,
}

/// The outcome of a suspendable run: the program either finished (nothing to
/// snapshot) or paused, yielding the encoded `kont` envelope to persist.
#[derive(Debug)]
pub enum SuspendResult {
    /// Ran to completion before the step budget; carries any `exit(code)`.
    Done(Option<i32>),
    /// Paused at the budget; carries the serialized `kont` envelope and the
    /// cut's position on the observation timeline.
    Suspended {
        /// The serialized `kont` envelope.
        bytes: Vec<u8>,
        /// Where the cut fell on the observation timeline.
        cut: SuspendCut,
    },
}

/// Run `src` under a step budget, streaming its prefix output to `out_sink` and
/// snapshotting the whole suspended program as a `kont` envelope when it pauses.
///
/// The snapshot is tagged with the program's code-identity digest (its namespace
/// root), which [`resume_on`] re-derives and checks. If a captured value cannot
/// cross the suspend boundary (too deeply nested, the fingerprint of an
/// unserializable capture), the refusal is raised here, at suspend time, naming
/// the value.
///
/// # Errors
/// Fails on any front-end error, an evaluation fault before the budget, or a value
/// that cannot be serialized.
pub fn suspend_on(
    src: &str,
    roots: &[Root],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    budget: usize,
    cfg: &Config,
) -> Result<SuspendResult, Error> {
    let bundle = execution_bundle(src, roots, cfg)?;
    let core = prepared_core(src, roots, cfg)?;
    let (checkpoint, marks) =
        crate::eval::run_suspending_ruled(&core, bundle, budget, out_sink, input)
            .map_err(Error::RuntimeEvaluation)?;
    match checkpoint {
        crate::eval::Checkpoint::Done(run) => Ok(SuspendResult::Done(run.exit)),
        crate::eval::Checkpoint::Suspended(kont) => {
            let bytes = crate::eval::kont::encode_kont(&kont)
                .map_err(|e| Error::RuntimeEvaluation(e.to_string()))?;
            let cut = SuspendCut {
                observations: marks.len(),
                last: marks.into_iter().next_back().map(ruler_row),
            };
            Ok(SuspendResult::Suspended { bytes, cut })
        }
    }
}

// A hard cap on the line-cut scan so a nonterminating program cannot spin the
// mapping forever. Any real demo program prints its lines in far fewer steps.
const MAX_LINE_CUT_STEPS: usize = 8192;

/// The machine-step budget at which each successive output line first appears.
///
/// Compiles `src` once, then re-runs it under growing step budgets and records,
/// for each printed line, the smallest budget after which that line has been
/// emitted. The `i`th entry is the budget to pass [`suspend_on`] to pause exactly
/// after line `i + 1` has printed, so a caller can cut on a legible line boundary
/// instead of an opaque step count. The final line's boundary is omitted: pausing
/// there is completion, with nothing left to suspend.
///
/// # Errors
/// Fails on any front-end error or an evaluation fault before the program ends.
pub fn suspend_line_cuts(src: &str, roots: &[Root], cfg: &Config) -> Result<Vec<usize>, Error> {
    let identity = namespace_identity(src, roots)?;
    let bundle = identity.root.into_string();
    let core = prepared_core(src, roots, cfg)?;
    // Build the global table once: it deep-clones every function body, so rebuilding
    // it per budget would make the scan quadratic in that clone.
    let g = crate::eval::globals(&core);
    let mut cuts: Vec<usize> = Vec::new();
    for budget in 1..=MAX_LINE_CUT_STEPS {
        let mut out: Vec<u8> = Vec::new();
        let mut input = std::io::Cursor::new(Vec::new());
        let checkpoint =
            crate::eval::run_suspending_in(&g, bundle.clone(), budget, &mut out, &mut input)
                .map_err(Error::RuntimeEvaluation)?;
        let lines = out.iter().fold(0usize, |n, &b| n + usize::from(b == b'\n'));
        while cuts.len() < lines {
            cuts.push(budget);
        }
        if matches!(checkpoint, crate::eval::Checkpoint::Done(_)) {
            break;
        }
    }
    // Drop the last line's boundary: a cut there is a completed run.
    cuts.pop();
    Ok(cuts)
}

/// Resume a `kont` envelope against `src`, running the continuation to completion
/// and streaming its suffix output to `out_sink`.
///
/// The envelope is decoded totally (any malformed or hostile bytes are rejected),
/// then its bundle digest is checked against `src`'s freshly derived code identity:
/// a snapshot captured against a different program is refused before a single step
/// runs. The suffix output, following the suspend run's prefix, reproduces an
/// uninterrupted run byte for byte.
///
/// # Errors
/// Fails on a front-end error, a malformed envelope, a code-identity mismatch, or
/// an evaluation fault after the resume point.
pub fn resume_on(
    src: &str,
    roots: &[Root],
    snapshot: &[u8],
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
    cfg: &Config,
) -> Result<Option<i32>, Error> {
    let kont = crate::eval::kont::decode_kont(snapshot)
        .map_err(|e| Error::RuntimeReplay(format!("resume: malformed snapshot: {e}")))?;
    let bundle = execution_bundle(src, roots, cfg)?;
    if kont.bundle != bundle {
        return Err(Error::RuntimeReplay(format!(
            "resume: execution-identity mismatch: this snapshot was captured against a \
             different program or under different behavior-bearing settings (code, standard \
             library, scheduler policy, or runtime semantics); snapshot bundle {}, this run {}",
            kont.bundle, bundle
        )));
    }
    let core = prepared_core(src, roots, cfg)?;
    let run =
        crate::eval::resume_kont(&core, kont, out_sink, input).map_err(Error::RuntimeReplay)?;
    Ok(run.exit)
}

// The interpreter transcript for `src` on empty stdin: the reference oracle a
// native backend's output must match, and the second oracle when MLIR is absent.
#[cfg(feature = "native")]
pub(super) fn interp_transcript(src: &str, roots: &[Root], cfg: &Config) -> Result<Vec<u8>, Error> {
    let mut out: Vec<u8> = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    interpret_io_on(src, roots, &mut out, &mut input, cfg)?;
    Ok(out)
}
