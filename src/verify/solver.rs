//! Out-of-process solver adapters: pin an external solver,
//! discharge a canonical SMT-LIB script through it under a resource policy, and
//! normalize its answer into the six-member [`ResultStatus`] vocabulary.
//!
//! A solver is an untrusted external search engine over bytes Prism has already
//! fixed. Prism launches it out of process, treats its stdout/stderr as hostile
//! input, and bounds every read and the wall-clock time. An `unsat` is an honest
//! solver-oracle result, never an independently checked proof; a crash, timeout,
//! or unparseable output is an infrastructure status, never a logical verdict. No
//! solver is required to compile or run Prism, only to discharge contracts.
//!
//! Two families are supported out of the box, z3 and cvc5, plus a generic adapter
//! for any solver that reads SMT-LIB 2 on standard input. The family fixes only the
//! invocation flags; the emitted script bytes are identical across families, which
//! is what makes cross-solver agreement meaningful.

use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use crate::verify::response::{parse, ResponseError, SolverStatus};
use crate::verify::result::{ModelBinding, ResultStatus, SolverId};

/// The default wall-clock budget for one discharge when no policy overrides it.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(10);
/// How often the wait loop polls the child while it runs.
const POLL_INTERVAL: Duration = Duration::from_millis(5);
/// The cap on solver output Prism will read: hostile output cannot exhaust memory.
const MAX_OUTPUT_BYTES: u64 = 1 << 20;
/// The cap on the number of model bindings recovered from a diagnostic run.
const MAX_MODEL_BINDINGS: usize = 4096;

/// z3 reads an SMT-LIB 2 script from standard input under `-in`.
const Z3_STDIN_ARGS: &[&str] = &["-in"];
/// cvc5 reads from standard input when no input file is given; `--lang smt2` fixes
/// the input language explicitly.
const CVC5_STDIN_ARGS: &[&str] = &["--lang", "smt2"];
/// A generic solver is fed the script on standard input with no extra flags.
const GENERIC_STDIN_ARGS: &[&str] = &[];
/// The version-probe flag every supported family accepts.
const VERSION_ARG: &str = "--version";

/// A recognized solver family, fixing only the invocation flags.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum SolverFamily {
    Z3,
    Cvc5,
    /// Any solver that reads SMT-LIB 2 on standard input.
    Generic,
}

impl SolverFamily {
    /// Infer the family from the executable's basename. Unknown names default to
    /// the generic adapter.
    fn infer(exe: &str) -> Self {
        let base = Path::new(exe)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(exe)
            .to_ascii_lowercase();
        if base.contains("cvc5") {
            Self::Cvc5
        } else if base.contains("z3") {
            Self::Z3
        } else {
            Self::Generic
        }
    }

    /// The exact invocation flags that make this family read the script on stdin.
    /// These are the receipt's *semantic* flags; physical limits are not here.
    const fn stdin_args(self) -> &'static [&'static str] {
        match self {
            Self::Z3 => Z3_STDIN_ARGS,
            Self::Cvc5 => CVC5_STDIN_ARGS,
            Self::Generic => GENERIC_STDIN_ARGS,
        }
    }
}

/// A pinned solver: its family, executable, probed version, and resource policy.
/// Built by [`pin`], which confirms the executable launches; a receipt derives its
/// [`SolverId`] from the family name, version, and semantic flags recorded here.
pub(crate) struct PinnedSolver {
    family: SolverFamily,
    exe: String,
    version: String,
    timeout: Duration,
}

/// The normalized outcome of one discharge: a status plus a best-effort model.
pub(crate) struct Discharge {
    pub(crate) status: ResultStatus,
    pub(crate) model: Vec<ModelBinding>,
}

/// Pin the solver at `exe` by probing `--version`, adopting `timeout` (or the
/// default) as the resource policy. Returns `None` when the executable cannot be
/// launched, which is unavailability, never a logical verdict.
pub(crate) fn pin(exe: &str, timeout: Option<Duration>) -> Option<PinnedSolver> {
    let family = SolverFamily::infer(exe);
    let version = probe_version(exe)?;
    Some(PinnedSolver {
        family,
        exe: exe.to_string(),
        version,
        timeout: timeout.unwrap_or(DEFAULT_TIMEOUT),
    })
}

impl PinnedSolver {
    /// The content identity of this solver: family name, version, and semantic
    /// flags. A flag or version change moves it; the query digest never does.
    pub(crate) fn id(&self) -> SolverId {
        SolverId {
            family: self.family_name(),
            version: self.version.clone(),
            flags: self
                .family
                .stdin_args()
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
        }
    }

    fn family_name(&self) -> String {
        match self.family {
            SolverFamily::Z3 => "z3".to_string(),
            SolverFamily::Cvc5 => "cvc5".to_string(),
            SolverFamily::Generic => {
                let base = Path::new(&self.exe)
                    .file_name()
                    .and_then(|s| s.to_str())
                    .unwrap_or(&self.exe);
                format!("generic:{base}")
            }
        }
    }

    /// Discharge one canonical SMT-LIB script. The status is authoritative; a model
    /// is recovered by a separate diagnostic run only on `sat`, so the semantic
    /// script that fixes query identity is never perturbed.
    pub(crate) fn discharge(&self, script: &str) -> Discharge {
        let run = run_process(&self.exe, self.family.stdin_args(), script, self.timeout);
        let status = classify(&run);
        let model = if status == ResultStatus::Sat {
            self.collect_model(script)
        } else {
            Vec::new()
        };
        Discharge { status, model }
    }

    /// A best-effort diagnostic run to recover a `sat` model. It appends model
    /// requests to a copy of the script (a separately derived diagnostic script, so
    /// it does not change the obligation identity) and parses whatever comes back.
    /// Any failure yields an empty model; the model is diagnostic, not evidence.
    fn collect_model(&self, script: &str) -> Vec<ModelBinding> {
        let diagnostic = format!("(set-option :produce-models true)\n{script}(get-model)\n");
        match run_process(
            &self.exe,
            self.family.stdin_args(),
            &diagnostic,
            self.timeout,
        ) {
            Run::Exited { stdout, .. } => parse_model(&stdout),
            Run::TimedOut | Run::LaunchFailed => Vec::new(),
        }
    }
}

/// Probe `exe --version`, returning its first output line trimmed. `None` when the
/// executable cannot be launched.
fn probe_version(exe: &str) -> Option<String> {
    let output = Command::new(exe).arg(VERSION_ARG).output().ok()?;
    let text = String::from_utf8_lossy(&output.stdout);
    let line = text.lines().next().unwrap_or("").trim();
    Some(if line.is_empty() {
        "unknown".to_string()
    } else {
        line.to_string()
    })
}

/// The raw outcome of running a child process under the resource policy.
enum Run {
    /// The process exited on its own.
    Exited { signaled: bool, stdout: String },
    /// The process exceeded the wall-clock budget and was killed.
    TimedOut,
    /// The process could not be launched.
    LaunchFailed,
}

/// Run `exe args`, feeding `input` on stdin, killing it if it outlives `timeout`.
/// stdin, stdout, and stderr are serviced on threads so a full pipe can never
/// deadlock the child, and every read is byte-capped against hostile output.
fn run_process(exe: &str, args: &[&str], input: &str, timeout: Duration) -> Run {
    let Ok(mut child) = Command::new(exe)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    else {
        return Run::LaunchFailed;
    };

    if let Some(mut stdin) = child.stdin.take() {
        let input = input.to_string();
        thread::spawn(move || {
            let _ = stdin.write_all(input.as_bytes());
        });
    }
    let stdout = child.stdout.take();
    let out_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(s) = stdout {
            let _ = s.take(MAX_OUTPUT_BYTES).read_to_end(&mut buf);
        }
        buf
    });
    let stderr = child.stderr.take();
    let err_handle = thread::spawn(move || {
        if let Some(s) = stderr {
            let mut sink = Vec::new();
            let _ = s.take(MAX_OUTPUT_BYTES).read_to_end(&mut sink);
        }
    });

    let start = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    break None;
                }
                thread::sleep(POLL_INTERVAL);
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
        }
    };
    let stdout = String::from_utf8_lossy(&out_handle.join().unwrap_or_default()).into_owned();
    let _ = err_handle.join();
    status.map_or(Run::TimedOut, |st| Run::Exited {
        signaled: is_signaled(st),
        stdout,
    })
}

/// Whether a process was terminated by a signal (a crash), on platforms that
/// distinguish it. On others, never.
#[cfg(unix)]
fn is_signaled(status: ExitStatus) -> bool {
    // `ExitStatusExt::signal` is a Unix-only trait method, so its import is kept
    // local to this cfg-gated function; hoisting it would break the non-unix build.
    use std::os::unix::process::ExitStatusExt;
    status.signal().is_some()
}

#[cfg(not(unix))]
fn is_signaled(_status: ExitStatus) -> bool {
    false
}

/// Map a raw run to the normalized status. A timeout, a launch failure, and a
/// signal are infrastructure; a clean exit is classified by the response parser,
/// with empty output read as a crash and any other unparseable output as malformed.
fn classify(run: &Run) -> ResultStatus {
    match run {
        Run::TimedOut => ResultStatus::Timeout,
        Run::LaunchFailed | Run::Exited { signaled: true, .. } => ResultStatus::Crash,
        Run::Exited { stdout, .. } => match parse(stdout) {
            Ok(SolverStatus::Unsat) => ResultStatus::Unsat,
            Ok(SolverStatus::Sat) => ResultStatus::Sat,
            Ok(SolverStatus::Unknown) => ResultStatus::Unknown,
            // Empty output from a clean exit is a crash-like non-answer; named but
            // unrecognized, contradictory, or `(error ...)` output is malformed.
            Err(ResponseError::Empty) => ResultStatus::Crash,
            Err(_) => ResultStatus::Malformed,
        },
    }
}

/// Parse a solver model into normalized bindings. Recognizes the common
/// `(define-fun NAME () SORT VALUE)` form both z3 and cvc5 emit under `(get-model)`.
/// Tolerant and bounded: it extracts what it recognizes and ignores the rest, since
/// a model is a diagnostic aid, never proof evidence.
pub(crate) fn parse_model(output: &str) -> Vec<ModelBinding> {
    let toks = tokenize(output);
    let mut out = Vec::new();
    let mut i = 0;
    while i < toks.len() && out.len() < MAX_MODEL_BINDINGS {
        // A binding opens `( define-fun NAME ( ) SORT`; the value is the balanced
        // remainder up to the matching close of the `define-fun` list.
        if toks[i] == Tok::Open
            && matches!(toks.get(i + 1), Some(Tok::Atom(a)) if a == "define-fun")
        {
            if let Some((binding, next)) = read_define_fun(&toks, i) {
                out.push(binding);
                i = next;
                continue;
            }
        }
        i += 1;
    }
    out
}

/// Read one `(define-fun NAME () SORT VALUE)` starting at the `(` at `start`.
/// Returns the binding and the index just past the closing `)`.
fn read_define_fun(toks: &[Tok], start: usize) -> Option<(ModelBinding, usize)> {
    // toks[start] == Open, toks[start + 1] == "define-fun".
    let name = match toks.get(start + 2)? {
        Tok::Atom(a) => a.clone(),
        Tok::Open | Tok::Close => return None,
    };
    // Skip the parameter list `( )` and the sort.
    let mut i = start + 3;
    if toks.get(i) == Some(&Tok::Open) {
        i = skip_balanced(toks, i)?;
    } else {
        return None;
    }
    match toks.get(i)? {
        Tok::Atom(_) => i += 1,
        Tok::Open => i = skip_balanced(toks, i)?,
        Tok::Close => return None,
    }
    // The value is the balanced remainder up to the define-fun's closing paren.
    let value = render_until_close(toks, &mut i)?;
    Some((ModelBinding { name, value }, i))
}

/// Advance past a balanced `( ... )` beginning at `open` (a `(`), returning the
/// index just after the matching `)`.
fn skip_balanced(toks: &[Tok], open: usize) -> Option<usize> {
    let mut depth = 0;
    let mut i = open;
    while i < toks.len() {
        match toks[i] {
            Tok::Open => depth += 1,
            Tok::Close => {
                depth -= 1;
                if depth == 0 {
                    return Some(i + 1);
                }
            }
            Tok::Atom(_) => {}
        }
        i += 1;
    }
    None
}

/// Render the tokens up to (but not consuming beyond) the `)` that closes the
/// enclosing list, advancing `i` past that `)`. The value spelling is canonical
/// with single spaces and no space just inside parentheses.
fn render_until_close(toks: &[Tok], i: &mut usize) -> Option<String> {
    let mut parts: Vec<String> = Vec::new();
    let mut depth = 0i32;
    while *i < toks.len() {
        match &toks[*i] {
            Tok::Close if depth == 0 => {
                *i += 1;
                return Some(parts.join(" ").replace("( ", "(").replace(" )", ")"));
            }
            Tok::Open => {
                depth += 1;
                parts.push("(".to_string());
            }
            Tok::Close => {
                depth -= 1;
                parts.push(")".to_string());
            }
            Tok::Atom(a) => parts.push(a.clone()),
        }
        *i += 1;
    }
    None
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Tok {
    Open,
    Close,
    Atom(String),
}

/// A minimal SMT-LIB tokenizer: parentheses and whitespace-delimited atoms. Comment
/// tails (`;`) are dropped. Bounded by the already byte-capped input.
fn tokenize(s: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let mut atom = String::new();
    for line in s.lines() {
        let line = line.split(';').next().unwrap_or("");
        for c in line.chars() {
            match c {
                '(' | ')' => {
                    flush_atom(&mut atom, &mut out);
                    out.push(if c == '(' { Tok::Open } else { Tok::Close });
                }
                c if c.is_whitespace() => flush_atom(&mut atom, &mut out),
                c => atom.push(c),
            }
        }
        flush_atom(&mut atom, &mut out);
    }
    out
}

fn flush_atom(atom: &mut String, out: &mut Vec<Tok>) {
    if !atom.is_empty() {
        out.push(Tok::Atom(std::mem::take(atom)));
    }
}

#[cfg(test)]
mod tests {
    use super::{classify, parse_model, Run, SolverFamily};
    use crate::verify::result::{ModelBinding, ResultStatus};

    fn exited(stdout: &str) -> Run {
        Run::Exited {
            signaled: false,
            stdout: stdout.to_string(),
        }
    }

    #[test]
    fn classify_covers_the_normalized_vocabulary() {
        assert_eq!(classify(&Run::TimedOut), ResultStatus::Timeout);
        assert_eq!(classify(&Run::LaunchFailed), ResultStatus::Crash);
        // A signal is a crash regardless of any partial output.
        assert_eq!(
            classify(&Run::Exited {
                signaled: true,
                stdout: "unsat\n".to_string(),
            }),
            ResultStatus::Crash
        );
        assert_eq!(classify(&exited("unsat\n")), ResultStatus::Unsat);
        assert_eq!(classify(&exited("sat\n")), ResultStatus::Sat);
        assert_eq!(classify(&exited("unknown\n")), ResultStatus::Unknown);
        // Empty output from a clean exit is a crash-like non-answer.
        assert_eq!(classify(&exited("")), ResultStatus::Crash);
        // Named-but-unrecognized, contradictory, and error output are all malformed.
        assert_eq!(classify(&exited("banana\n")), ResultStatus::Malformed);
        assert_eq!(classify(&exited("sat\nunsat\n")), ResultStatus::Malformed);
        assert_eq!(
            classify(&exited("(error \"line 1: boom\")\n")),
            ResultStatus::Malformed
        );
    }

    #[test]
    fn parse_model_recovers_define_fun_bindings() {
        let out = "sat\n(\n  (define-fun x0 () Int 5)\n  (define-fun p () Bool true)\n  \
                   (define-fun y () Int (- 3))\n)\n";
        let m = parse_model(out);
        assert_eq!(
            m,
            vec![
                ModelBinding {
                    name: "x0".to_string(),
                    value: "5".to_string(),
                },
                ModelBinding {
                    name: "p".to_string(),
                    value: "true".to_string(),
                },
                ModelBinding {
                    name: "y".to_string(),
                    value: "(- 3)".to_string(),
                },
            ]
        );
        // No model text yields no bindings, never a panic on hostile input.
        assert!(parse_model("unsat\n").is_empty());
        assert!(parse_model("(((").is_empty());
    }

    #[test]
    fn family_inference_from_basename() {
        assert_eq!(SolverFamily::infer("z3"), SolverFamily::Z3);
        assert_eq!(
            SolverFamily::infer("/opt/homebrew/bin/z3"),
            SolverFamily::Z3
        );
        assert_eq!(SolverFamily::infer("cvc5"), SolverFamily::Cvc5);
        assert_eq!(SolverFamily::infer("/usr/bin/cvc5"), SolverFamily::Cvc5);
        assert_eq!(SolverFamily::infer("my-prover"), SolverFamily::Generic);
    }
}
