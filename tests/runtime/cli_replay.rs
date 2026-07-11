// The core property behind lib/std/Cli.pr: command-line arguments reach a
// program through the `Env` capability (`args`/`args_count`/`arg`), so they are
// recorded observations like a clock read or a file read. A run recorded with
// `--record` therefore replays argv-and-all from its `.replay` trace, and CLI
// parsing sits inside the determinism contract. Mirrors the clock proof in
// tests/time_json.rs, and adds a subprocess proof that replay serves the recorded
// argv even when the live command line differs.

use prism::resolve::default_roots;
use prism::{record_on_with_args, replay_on, with_prelude, Config};
use std::io::Cursor;
use std::path::Path;
use std::process::Command;

fn cfg() -> Config {
    Config::from_env()
}

fn roots() -> Vec<prism::resolve::Root> {
    default_roots(Path::new("."))
}

// Reads every argument through the `Env` capability and prints it with its index.
const ARGS_PROGRAM: &str = r#"
fn dump(i, n) =
  if i >= n then
    ()
  else
    println(concat(concat(show_int(i), ": "), arg(i)))
    dump(i + 1, n)

fn main() = dump(0, args_count())
"#;

#[test]
fn argv_reads_replay_byte_for_byte() {
    // Recording reads the live process argv and captures each `arg`/`args_count`
    // as an observation; replaying serves them from the trace, performing no live
    // argv read, and reproduces the transcript byte for byte.
    let full = with_prelude(ARGS_PROGRAM);

    let mut rec_out: Vec<u8> = Vec::new();
    let mut rec_in = Cursor::new(Vec::new());
    let (_exit, trace_str, n_obs) = record_on_with_args(
        &full,
        &roots(),
        &mut rec_out,
        &mut rec_in,
        &cfg(),
        vec!["alpha".into(), "--flag".into()],
    )
    .expect("record");
    assert!(
        n_obs >= 1,
        "the run observed at least the argument count, got {n_obs}"
    );
    assert!(
        !rec_out.is_empty(),
        "the program printed at least one argument"
    );

    let mut replay_out: Vec<u8> = Vec::new();
    replay_on(&full, &roots(), &mut replay_out, &trace_str, &cfg()).expect("replay");

    assert_eq!(
        replay_out, rec_out,
        "replaying the trace reproduces the recorded argv byte-for-byte"
    );
}

// The stronger proof: record and replay the built binary under two *different*
// command lines. The program prints its arguments; if replay reproduces the
// arguments seen at record time (rather than its own live argv), then argv truly
// came from the trace, not the command line.
#[test]
fn recorded_argv_replays_when_command_line_differs() {
    let dir = std::env::temp_dir().join(format!("prism_cli_replay_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let prog = dir.join("argv.pr");
    let trace = dir.join("argv.replay");
    std::fs::write(&prog, ARGS_PROGRAM).expect("write program");

    let bin = env!("CARGO_BIN_EXE_prism");

    // Record: only arguments after `--` reach the Prism program; compiler words
    // like `run` and `--record` are not visible through `args()`.
    let rec = Command::new(bin)
        .arg("run")
        .arg(&prog)
        .arg("--record")
        .arg(&trace)
        .arg("--")
        .arg("alpha")
        .arg("--flag")
        .output()
        .expect("run --record");
    assert!(rec.status.success(), "record exited non-zero: {rec:?}");
    let recorded_out = String::from_utf8(rec.stdout).expect("utf8");

    // Replay: the live argv is `<bin> exec replay <prog> <trace>`, but replay
    // serves the recorded Env observations instead of reading that command line.
    let rep = Command::new(bin)
        .arg("exec")
        .arg("replay")
        .arg(&prog)
        .arg(&trace)
        .output()
        .expect("replay");
    assert!(rep.status.success(), "replay exited non-zero: {rep:?}");
    let replayed_out = String::from_utf8(rep.stdout).expect("utf8");

    // The transcripts match despite the differing command lines, and both show
    // the record-time program arguments: replay served argv from the trace, not
    // from its own command line.
    assert_eq!(
        replayed_out, recorded_out,
        "replay reproduces the recorded transcript under a different command line"
    );
    assert!(
        recorded_out.contains("0: alpha") && recorded_out.contains("1: --flag"),
        "record read only program argv after `--`; got:\n{recorded_out}"
    );
    assert!(
        replayed_out.contains("0: alpha")
            && replayed_out.contains("1: --flag")
            && !replayed_out.contains("replay"),
        "replay printed recorded program argv, not its live argv; got:\n{replayed_out}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
