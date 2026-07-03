//! The terminal reverse-step debugger and its `.replay` trace codec.
//!
//! A `.replay` file is a whole execution: the ordered trace of a program's
//! observations (see [`trace`]). Because the language's contract is that every
//! observable behavior is a pure function of the source and the pinned input
//! trace, "step" is honest time travel: stepping to observation N is
//! deterministic re-execution from the start through the first N observations
//! (replay-to-N), and stepping *back* is the same re-execution to N-1. There is
//! no OS-level record/replay, no hardware counters; the semantics themselves are
//! the debugger.
//!
//! This module is the driver-side machinery: the codec, a single `replay_to`
//! primitive over [`crate::eval::run_traced`], and the stepping REPL. The three
//! CLI verbs (`record`, `replay`, `debug`) are thin wrappers in the driver.

pub mod trace;

use std::io::{self, BufRead, Write};

use crate::core::Core;
use crate::eval::{run_traced, Obs, Tape, TracedRun};

// The debugger REPL commands, one per input line.
const HELP: &str =
    "commands: n(ext), b(ack), g(oto) N, p(rint state), l(ist trace), h(elp), q(uit)";

/// Replay the recorded trace through the program, stopping after the first `n`
/// observations (or at the end, whichever comes first). The returned run carries
/// the transcript produced up to that point.
///
/// # Errors
/// Fails when evaluation faults or the trace does not match the program.
pub fn replay_to(core: &Core, frames: &[Obs], n: usize) -> Result<TracedRun, String> {
    // Output is captured in `TracedRun.term` regardless of the sink, and replay
    // serves every read from the trace, so the program's stdin is unused.
    let mut sink = io::sink();
    let mut input = io::Cursor::new(Vec::new());
    let tape = Tape::Replay {
        frames: frames.to_vec(),
        cursor: 0,
        budget: Some(n),
    };
    run_traced(core, &mut sink, &mut input, tape)
}

// A short, one-line description of one observation, tag and payload both.
fn op_desc(o: &Obs) -> String {
    match o {
        Obs::Int(n) => format!("read int {n}"),
        Obs::Str(s) => format!("read {s:?}"),
        Obs::Bool(b) => format!("read bool {b}"),
        Obs::Out => "output".into(),
    }
}

// Program output rendered on one line (newlines shown as `\n`), so each step is
// a single, greppable transcript line.
fn one_line(term: &str) -> String {
    term.replace('\n', "\\n")
}

// The status line for observation index `n`: how far we are, the operation just
// performed (the frame at `n-1`), and the program output produced so far.
fn status(core: &Core, frames: &[Obs], n: usize) -> Result<String, String> {
    let run = replay_to(core, frames, n)?;
    let op = if n == 0 {
        "start".to_string()
    } else {
        op_desc(&frames[n - 1])
    };
    Ok(format!(
        "[{n}/{}] {op} | out: {}",
        frames.len(),
        one_line(&run.term)
    ))
}

/// Run the stepping REPL over a decoded trace, reading commands from `cmds` and
/// writing the debugger UI to `ui`.
///
/// Stepping is replay-to-N: `n`/`b`/`g` move the observation index and re-run
/// the program deterministically to that point, printing the observation index,
/// the operation performed, and the program output so far. Backwards stepping is
/// re-execution to N-1, the honest reverse step the determinism contract buys.
///
/// # Errors
/// Fails on an I/O error or when the trace does not match the program.
pub fn run_repl(
    core: &Core,
    frames: &[Obs],
    cmds: &mut dyn BufRead,
    ui: &mut dyn Write,
) -> Result<(), String> {
    let total = frames.len();
    let mut n = 0usize;
    writeln!(ui, "loaded {total} observations. {HELP}").map_err(|e| e.to_string())?;
    writeln!(ui, "{}", status(core, frames, n)?).map_err(|e| e.to_string())?;
    loop {
        write!(ui, "(debug) ").map_err(|e| e.to_string())?;
        ui.flush().ok();
        let mut line = String::new();
        if cmds.read_line(&mut line).map_err(|e| e.to_string())? == 0 {
            break; // EOF: end the session
        }
        let mut it = line.split_whitespace();
        let Some(cmd) = it.next() else {
            continue;
        };
        match cmd {
            "n" | "next" => n = (n + 1).min(total),
            "b" | "back" => n = n.saturating_sub(1),
            "g" | "goto" => {
                if let Some(k) = it.next().and_then(|a| a.parse::<usize>().ok()) {
                    n = k.min(total);
                } else {
                    writeln!(ui, "goto needs a number 0..={total}").map_err(|e| e.to_string())?;
                    continue;
                }
            }
            "p" | "print" => {
                let run = replay_to(core, frames, n)?;
                writeln!(ui, "observation {n} of {total}").map_err(|e| e.to_string())?;
                if n > 0 {
                    writeln!(ui, "last op: {}", op_desc(&frames[n - 1]))
                        .map_err(|e| e.to_string())?;
                }
                writeln!(ui, "output so far:\n{}", run.term).map_err(|e| e.to_string())?;
                continue;
            }
            "l" | "list" => {
                for (i, f) in frames.iter().enumerate() {
                    let mark = if i + 1 == n { ">" } else { " " };
                    writeln!(ui, "{mark} {}: {}", i + 1, op_desc(f)).map_err(|e| e.to_string())?;
                }
                continue;
            }
            "h" | "help" => {
                writeln!(ui, "{HELP}").map_err(|e| e.to_string())?;
                continue;
            }
            "q" | "quit" => break,
            other => {
                writeln!(ui, "unknown command {other:?}. {HELP}").map_err(|e| e.to_string())?;
                continue;
            }
        }
        writeln!(ui, "{}", status(core, frames, n)?).map_err(|e| e.to_string())?;
    }
    Ok(())
}
