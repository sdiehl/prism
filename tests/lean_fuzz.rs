//! Generated differential gate between the Rust interpreter and the Lean CEK
//! oracle.
//!
//! The ordinary Rust suite leaves this test ignored because it requires a built
//! Lean executable. `just lean-fuzz` and the Lean CI job build that executable
//! and invoke this test explicitly; once invoked, a missing oracle or an empty,
//! stuck, undecodable, or zero-case run is a hard failure.

mod support;

use std::fs;
use std::io::{Read, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use num_bigint::BigInt;
use prism::eval::Rv;

use crate::support::fuzzgen::{generate, shrink, Program, ProgramFamily};
use crate::support::TempDir;

const GENERATED_CASES: usize = 12;
const SEED: u64 = 0x6c65_616e_5f66_757a;
const SUBPROCESS_TIMEOUT: Duration = Duration::from_secs(30);
const _: () = assert!(GENERATED_CASES > 0);

enum Comparison {
    Match,
    Mismatch(String),
    HarnessFailure(String),
}

fn oracle_path() -> PathBuf {
    std::env::var_os("PRISM_LEAN_ORACLE").map_or_else(
        || {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("models")
                .join(".lake")
                .join("build")
                .join("bin")
                .join(format!("oracle{}", std::env::consts::EXE_SUFFIX))
        },
        PathBuf::from,
    )
}

fn captured_pipe(pipe: impl Read + Send + 'static) -> thread::JoinHandle<std::io::Result<Vec<u8>>> {
    thread::spawn(move || {
        let mut bytes = Vec::new();
        let mut pipe = pipe;
        pipe.read_to_end(&mut bytes)?;
        Ok(bytes)
    })
}

fn finish_capture(
    label: &str,
    stream: &str,
    capture: thread::JoinHandle<std::io::Result<Vec<u8>>>,
) -> Result<Vec<u8>, String> {
    capture
        .join()
        .map_err(|_| format!("{label} {stream} capture thread panicked"))?
        .map_err(|error| format!("failed reading {label} {stream}: {error}"))
}

fn finish_input(
    label: &str,
    writer: Option<thread::JoinHandle<std::io::Result<()>>>,
) -> Result<(), String> {
    let Some(writer) = writer else {
        return Ok(());
    };
    writer
        .join()
        .map_err(|_| format!("{label} stdin writer thread panicked"))?
        .map_err(|error| format!("failed writing {label} stdin: {error}"))
}

fn run_bounded(label: &str, mut command: Command, input: Option<&[u8]>) -> Result<Output, String> {
    command
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command
        .spawn()
        .map_err(|error| format!("failed to start {label}: {error}"))?;
    let input = input
        .map(|bytes| {
            let mut stdin = child
                .stdin
                .take()
                .ok_or_else(|| format!("{label} stdin pipe was not created"))?;
            let bytes = bytes.to_vec();
            Ok::<_, String>(thread::spawn(move || stdin.write_all(&bytes)))
        })
        .transpose()?;
    let stdout = captured_pipe(
        child
            .stdout
            .take()
            .ok_or_else(|| format!("{label} stdout pipe was not created"))?,
    );
    let stderr = captured_pipe(
        child
            .stderr
            .take()
            .ok_or_else(|| format!("{label} stderr pipe was not created"))?,
    );
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| format!("failed waiting for {label}: {error}"))?
        {
            break status;
        }
        if started.elapsed() >= SUBPROCESS_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            let _ = finish_input(label, input);
            let stdout = finish_capture(label, "stdout", stdout)?;
            let stderr = finish_capture(label, "stderr", stderr)?;
            return Err(format!(
                "{label} exceeded {SUBPROCESS_TIMEOUT:?} and was killed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&stdout),
                String::from_utf8_lossy(&stderr)
            ));
        }
        thread::sleep(Duration::from_millis(10));
    };
    finish_input(label, input)?;
    Ok(Output {
        status,
        stdout: finish_capture(label, "stdout", stdout)?,
        stderr: finish_capture(label, "stderr", stderr)?,
    })
}

fn command_failure(label: &str, output: &std::process::Output) -> String {
    format!(
        "{label} exited {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn dump_core_json(source_path: &Path) -> Result<String, String> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_prism"));
    command
        .args(["dump", "core-json"])
        .arg(source_path)
        .env("PRISM_COMPILER_CACHE", "0");
    let output = run_bounded("prism dump core-json", command, None)?;
    if !output.status.success() {
        return Err(command_failure("prism dump core-json", &output));
    }
    let core = String::from_utf8(output.stdout)
        .map_err(|error| format!("prism dump core-json returned non-UTF-8 output: {error}"))?;
    if core.trim().is_empty() {
        return Err("prism dump core-json returned empty output".into());
    }
    Ok(core)
}

fn canonical_int(text: &str) -> Option<BigInt> {
    let bytes = text.as_bytes();
    let digits = bytes.strip_prefix(b"-").unwrap_or(bytes);
    if digits.is_empty()
        || !digits.iter().all(u8::is_ascii_digit)
        || (digits.len() > 1 && digits[0] == b'0')
        || (bytes.starts_with(b"-") && digits == b"0")
    {
        return None;
    }
    BigInt::parse_bytes(bytes, 10)
}

fn parse_lean_stdout(stdout: Vec<u8>) -> Result<(String, BigInt), String> {
    let stdout = String::from_utf8(stdout)
        .map_err(|error| format!("Lean oracle returned non-UTF-8 output: {error}"))?;
    let value = stdout
        .strip_suffix('\n')
        .ok_or_else(|| "Lean oracle result is missing its terminal LF".to_string())?;
    if value.contains(['\n', '\r']) {
        return Err(format!(
            "Lean oracle returned extra lines or CR bytes: {stdout:?}"
        ));
    }
    if value == "<stuck>" {
        return Err("Lean oracle exhausted its fuel or reached a stuck state".into());
    }
    let parsed = canonical_int(value).ok_or_else(|| {
        format!("Lean oracle did not return one canonical decimal Int line: {stdout:?}")
    })?;
    if format!("{parsed}") != value {
        return Err(format!(
            "Lean oracle returned a non-canonical decimal Int: {stdout:?}"
        ));
    }
    Ok((value.to_string(), parsed))
}

fn lean_value(core: &str) -> Result<(String, BigInt), String> {
    let oracle = oracle_path();
    if !oracle.is_file() {
        return Err(format!(
            "Lean oracle is missing at {}; run `cd models && lake build`",
            oracle.display()
        ));
    }
    let mut command = Command::new(&oracle);
    command.args(["eval", "-"]);
    let output = run_bounded("Lean oracle", command, Some(core.as_bytes()))?;
    if !output.status.success() {
        return Err(command_failure("Lean oracle", &output));
    }
    parse_lean_stdout(output.stdout)
}

#[test]
fn lean_result_requires_one_canonical_int_line() {
    for accepted in ["0\n", "1\n", "-1\n", "123456789012345678901234567890\n"] {
        assert!(
            parse_lean_stdout(accepted.as_bytes().to_vec()).is_ok(),
            "canonical result rejected: {accepted:?}"
        );
    }
    for rejected in [
        "",
        "\n",
        "0",
        "0\n\n",
        " 0\n",
        "0 \n",
        "+1\n",
        "-0\n",
        "00\n",
        "01\n",
        "-01\n",
        "true\n",
        "()\n",
        "<function>\n",
        "<stuck>\n",
        "1\r\n",
        "1\n2\n",
    ] {
        assert!(
            parse_lean_stdout(rejected.as_bytes().to_vec()).is_err(),
            "non-canonical result accepted: {rejected:?}"
        );
    }
}

fn compare(program: &Program, source_path: &Path) -> Comparison {
    let source = program.render_oracle();
    if let Err(error) = fs::write(source_path, &source) {
        return Comparison::HarnessFailure(format!(
            "failed to write generated source {}: {error}",
            source_path.display()
        ));
    }
    let full = prism::with_prelude(&source);
    let (rust, rust_int) = match prism::interpret_at(
        &full,
        source_path.parent().unwrap_or_else(|| Path::new(".")),
    ) {
        Ok(run) if run.term.is_empty() && run.out.is_empty() && run.exit.is_none() => {
            let value = match run.value {
                Rv::Int(value) => value,
                other => {
                    return Comparison::HarnessFailure(format!(
                        "oracle-mode main returned a non-Int: kind={} value={}",
                        other.kind(),
                        other.show()
                    ));
                }
            };
            (value.to_string(), BigInt::from(value))
        }
        Ok(run) => {
            return Comparison::HarnessFailure(format!(
                "oracle-mode main was not silent: kind={} value={} \
                 term={:?} out={:?} exit={:?}",
                run.value.kind(),
                run.value.show(),
                run.term,
                run.out,
                run.exit
            ));
        }
        Err(error) => {
            return Comparison::HarnessFailure(format!(
                "Rust interpreter rejected generated source: {error}"
            ));
        }
    };
    let core = match dump_core_json(source_path) {
        Ok(core) => core,
        Err(error) => return Comparison::HarnessFailure(error),
    };
    let (lean, lean_int) = match lean_value(&core) {
        Ok(value) => value,
        Err(error) => return Comparison::HarnessFailure(error),
    };
    if rust_int == lean_int {
        Comparison::Match
    } else {
        Comparison::Mismatch(format!("final-value mismatch: Rust=[{rust}] Lean=[{lean}]"))
    }
}

#[test]
#[ignore = "requires a built Lean oracle; run `just lean-fuzz`"]
fn generated_programs_match_lean_final_values() {
    let programs = generate(SEED, GENERATED_CASES);
    let pure = programs
        .iter()
        .filter(|program| program.family() == ProgramFamily::Pure)
        .count();
    let full = programs
        .iter()
        .filter(|program| program.family() == ProgramFamily::FullHandler)
        .count();
    let partial = programs
        .iter()
        .filter(|program| program.family() == ProgramFamily::PartialHandler)
        .count();
    eprintln!(
        "Lean fuzz seed={SEED:#018x} cases={} pure={pure} full-handler={full} \
         partial-handler={partial}",
        programs.len()
    );
    assert!(
        pure > 0 && full > 0 && partial > 0,
        "Lean fuzz seed {SEED:#018x} lost semantic-family coverage: \
         pure={pure}, full-handler={full}, partial-handler={partial}"
    );
    let scratch = TempDir::new("lean-fuzz", "cases");
    let path = scratch.join("candidate.pr");
    let mut ran = 0;
    for (index, program) in programs.into_iter().enumerate() {
        ran += 1;
        match compare(&program, &path) {
            Comparison::Match => {}
            Comparison::HarnessFailure(failure) => panic!(
                "Lean fuzz harness failed at seed {SEED:#018x}, case {index}:\n\
                 {failure}\n\ngenerated source:\n{}",
                program.render_oracle()
            ),
            Comparison::Mismatch(failure) => {
                let (minimal, failure) = shrink(program, failure, |candidate| {
                    match compare(candidate, &path) {
                        Comparison::Match => None,
                        Comparison::Mismatch(reason) => Some(reason),
                        Comparison::HarnessFailure(reason) => panic!(
                            "Lean fuzz harness failed while shrinking seed {SEED:#018x}, \
                             case {index}:\n{reason}\n\ncandidate source:\n{}",
                            candidate.render_oracle()
                        ),
                    }
                });
                panic!(
                    "Lean differential mismatch at seed {SEED:#018x}, case {index}, \
                     after shrinking:\n{failure}\n\nminimal reproducer:\n{}",
                    minimal.render_oracle()
                );
            }
        }
    }
    assert_eq!(
        ran, GENERATED_CASES,
        "Lean fuzz did not execute its complete deterministic corpus"
    );
}
