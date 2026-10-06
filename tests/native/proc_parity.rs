// The process boundary has two implementations, `src/eval/proc.rs` and
// `runtime/prism_proc.c`, and a program must not be able to tell which one ran
// its children. The fixture is the oracle for that: it is run through the
// interpreter and through a native binary, and the two must print the same bytes.
//
// It lives under `examples/fixtures/` rather than in the corpus for the reason
// the socket fixtures do: a program that spawns processes does not belong in a
// sweep diffed on every backend and tier combination. Its expected output is
// written out here because what is pinned is a contract (which outcome each
// command earns), not a rendering.

use std::io::Cursor;
use std::path::{Path, PathBuf};

use prism::error::Error;
use prism::{build_on, default_roots, record_on, replay_on, with_prelude, Config};

use crate::support::{check_native_parity, interpreted, require_cc, source};

const OUTCOMES: &str = r#"exit Proc.Exited(3) out="hi\n" err=""
stderr Proc.Exited(0) out="" err="oops\n"
feed Proc.Exited(0) out="fed" err=""
feed-ignored Proc.Exited(0) out="" err=""
both-pipes Proc.Exited(0) out=4194304 err=4194304
signal Proc.Signaled(9) out="" err=""
discard Proc.Exited(0) out="" err=""
out-limit Proc.OutputLimit(Proc.Stdout) out="" err=""
err-limit Proc.OutputLimit(Proc.Stderr) out="" err=""
deadline Proc.DeadlineExceeded out="" err=""
clean-env Proc.Exited(0) out="[]\n" err=""
set-env Proc.Exited(0) out="set\n" err=""
unset-env Proc.Exited(0) out="[]\n" err=""
cwd Proc.Exited(0) out="/\n" err=""
not-found Proc.SpawnFailed(Proc.NotFound) out="" err=""
relative-name Proc.SpawnFailed(Proc.NotFound) out="" err=""
empty-program Proc.SpawnFailed(Proc.BadCommand) out="" err=""
bad-limit Proc.SpawnFailed(Proc.BadCommand) out="" err=""
over-max Proc.SpawnFailed(Proc.BadCommand) out="" err=""
bad-deadline Proc.SpawnFailed(Proc.BadCommand) out="" err=""
missing-dir Proc.SpawnFailed(Proc.NotFound) out="" err=""
"#;

const PIPELINES: &str = r#"two [Proc.Exited(0), Proc.Exited(0)] out="HI\n" errs="",""
fed [Proc.Exited(0), Proc.Exited(0)] out="a\nb\n" errs="",""
first-fails [Proc.Exited(3), Proc.Exited(0)] out="" errs="",""
middle-fails [Proc.Exited(0), Proc.Exited(4), Proc.Exited(0)] out="" errs="","",""
last-fails [Proc.Exited(0), Proc.Exited(5)] out="x\n" errs="",""
early-exit [Proc.Signaled(13), Proc.Exited(0)] out="y\n" errs="",""
errs [Proc.Exited(0), Proc.Exited(0)] out="" errs="a\n","b\n"
first-missing [Proc.SpawnFailed(Proc.NotFound), Proc.Exited(0)] out="" errs="",""
middle-missing [Proc.Exited(0), Proc.SpawnFailed(Proc.NotFound), Proc.Exited(0)] out="after\n" errs="","",""
large [Proc.Exited(0), Proc.Exited(0), Proc.Exited(0)] out=1048576 err=1048576
out-limit [Proc.Aborted(Proc.ResourceLimit), Proc.OutputLimit(Proc.Stdout)] out="" errs="",""
err-limit [Proc.OutputLimit(Proc.Stderr), Proc.Aborted(Proc.ResourceLimit)] out="" errs="",""
deadline [Proc.DeadlineExceeded, Proc.DeadlineExceeded] out="" errs="",""
no-stages [Proc.SpawnFailed(Proc.BadCommand)] out="" errs=""
fed-later [Proc.SpawnFailed(Proc.BadCommand), Proc.SpawnFailed(Proc.BadCommand)] out="" errs="",""
stage-deadline [Proc.SpawnFailed(Proc.BadCommand)] out="" errs=""
checks last=[ok:""] all=[stage 0 Proc.Exited(1)] pipefail=[stage 1 Proc.Exited(2)]
checks-ok last=[ok:"ok\n"] all=[ok:"ok\n"] pipefail=[ok:"ok\n"]
"#;

const SHELL: &str = r#"text ok "a\nb\n"
lines ok ["a", "b"]
failed err /bin/sh: exited with code 2: nope
missing err prism-no-such-program: could not start: not found
bytes err /bin/sh: output is not UTF-8 text
quiet err /bin/sh: exited with code 1
exits-ok true false
env ok "set\n"
dir ok "/\n"
feed ok "fed"
within err sleep: ran past its deadline
pipe ok Some("b\na\n")
pipefail err /bin/sh: exited with code 3: e
argv ok "$HOME; `x`\n"
which /bin/sh
which-none none
search ["/usr/bin", "/bin"]
lines [] [""] ["a\r", "b"]
unlines "a\nb\n"
numbered [(1, "x"), (2, "y")]
"#;

fn fixture(name: &str) -> PathBuf {
    Path::new("examples/fixtures/proc").join(name)
}

fn quiet() -> Config {
    let mut cfg = Config::from_env();
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.compiler_cache = false);
    cfg
}

fn build(src: &str, out: &Path) -> Result<(), Error> {
    build_on(src, &default_roots(Path::new(".")), out, &quiet())
}

#[test]
fn every_outcome_matches_interpreter() {
    require_cc();
    let case = fixture("outcomes.pr");
    let got = interpreted(&source(&case));
    assert_eq!(got, OUTCOMES, "interpreted output changed");
    if let Err(e) = check_native_parity(&case, "proc", build) {
        panic!("{e}");
    }
}

#[test]
fn shell_vocabulary_matches_interpreter() {
    require_cc();
    let case = fixture("shell.pr");
    let got = interpreted(&source(&case));
    assert_eq!(got, SHELL, "interpreted output changed");
    if let Err(e) = check_native_parity(&case, "shell", build) {
        panic!("{e}");
    }
}

#[test]
fn every_pipeline_matches_interpreter() {
    require_cc();
    let case = fixture("pipelines.pr");
    let got = interpreted(&source(&case));
    assert_eq!(got, PIPELINES, "interpreted output changed");
    if let Err(e) = check_native_parity(&case, "pipeline", build) {
        panic!("{e}");
    }
}

// A child that appends a line to `log` and reports how many lines it holds.
fn counting(log: &Path, tag: &str) -> String {
    with_prelude(&format!(
        r#"import Proc (..)

fn main() : Unit ! {{IO}} =
  let o = run_proc(\() -> exec("/bin/sh", ["-c", "echo {tag} >> {log}; wc -l < {log}"]))
  println(show(text(o.out)))
"#,
        log = log.display(),
    ))
}

// A two-stage pipeline whose first stage appends a line to `log` and whose
// second counts the lines it holds.
fn counting_pipeline(log: &Path) -> String {
    with_prelude(&format!(
        r#"import Proc (..)

fn main() : Unit ! {{IO}} =
  let r = run_proc(\() -> collect_pipeline(pipeline([
      command("/bin/sh", ["-c", "echo a >> {log}; cat {log}"]),
      command("wc", ["-l"]),
    ])))
  println(show(text(r.out)))
"#,
        log = log.display(),
    ))
}

fn scratch_log(name: &str) -> PathBuf {
    let log = std::env::temp_dir().join(format!("prism-proc-{}-{name}", std::process::id()));
    let _ = std::fs::remove_file(&log);
    log
}

/// A replay serves the recorded outcome and spawns nothing: the child's append
/// to the log happens once, in the recording, and the replay prints the count
/// the recording saw.
#[test]
fn a_replay_serves_the_outcome_without_running_the_child() {
    let log = scratch_log("replay");
    let src = counting(&log, "a");
    let roots = default_roots(Path::new("."));
    let cfg = quiet();
    let mut recorded = Vec::new();
    let (_, trace, _) = record_on(
        &src,
        &roots,
        &mut recorded,
        &mut Cursor::new(Vec::new()),
        &cfg,
    )
    .expect("record");
    let mut replayed = Vec::new();
    replay_on(&src, &roots, &mut replayed, &trace, &cfg).expect("replay");
    let lines = std::fs::read_to_string(&log).expect("log").lines().count();
    let _ = std::fs::remove_file(&log);
    assert_eq!(replayed, recorded);
    assert_eq!(lines, 1, "the replay ran the child again");
}

/// A pipeline is one exchange, so a replay serves its whole result and starts
/// none of its stages.
#[test]
fn a_replay_serves_a_pipeline_without_running_it() {
    let log = scratch_log("pipeline");
    let src = counting_pipeline(&log);
    let roots = default_roots(Path::new("."));
    let cfg = quiet();
    let mut recorded = Vec::new();
    let (_, trace, _) = record_on(
        &src,
        &roots,
        &mut recorded,
        &mut Cursor::new(Vec::new()),
        &cfg,
    )
    .expect("record");
    let mut replayed = Vec::new();
    replay_on(&src, &roots, &mut replayed, &trace, &cfg).expect("replay");
    let lines = std::fs::read_to_string(&log).expect("log").lines().count();
    let _ = std::fs::remove_file(&log);
    assert_eq!(replayed, recorded);
    assert_eq!(lines, 1, "the replay ran the pipeline again");
}

/// The frame commits to a digest of the request, so a trace recorded for one
/// command cannot answer another, even one that would print the same thing.
#[test]
fn a_replay_refuses_a_different_command() {
    let log = scratch_log("mismatch");
    let roots = default_roots(Path::new("."));
    let cfg = quiet();
    let (_, trace, _) = record_on(
        &counting(&log, "a"),
        &roots,
        &mut Vec::new(),
        &mut Cursor::new(Vec::new()),
        &cfg,
    )
    .expect("record");
    let e = replay_on(&counting(&log, "b"), &roots, &mut Vec::new(), &trace, &cfg)
        .expect_err("a different command must not replay");
    let _ = std::fs::remove_file(&log);
    assert!(
        e.to_string().contains("different command"),
        "wrong diagnostic: {e}"
    );
}

/// `Proc` is recorded but not replayable: a recorded outcome does not redo what
/// the child did to the world. As with `Net`, the replayable-effect rule enforces
/// it, so a durable function that spawns is rejected before it can run.
#[test]
fn a_replayable_function_may_not_spawn() {
    let src = r#"import Proc (Proc, exec)

replayable fn build() : Unit ! {Proc} =
  let _o = exec("true", [])
  ()

fn main() : Unit ! {IO} = println("unreached")
"#;
    let e = prism::interpret(&with_prelude(src)).expect_err("replayable Proc must be rejected");
    let text = e.to_string();
    assert!(text.contains("replayable"), "wrong diagnostic: {text}");
    assert!(text.contains("Proc.Proc"), "wrong effect named: {text}");
}
