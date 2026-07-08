//! Run-lineage sidecar and provenance-event regressions.
//!
//! The subprocess cases drive `prism run --record --lineage` over a small program
//! that reads a file, an environment variable, and its argument count, then assert
//! the emitted graph. The library-level case pins the H3 contract directly: a
//! recording and a replay of its trace produce the identical provenance events.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

use prism::provenance::{trace_digest, OP_FS_WRITE_FILE};

// A program that observes one file, one environment variable, and its argument
// count, then prints all three. Every observed input becomes a graph node.
const PROGRAM: &str = "fn main() : !{IO} Unit =\n  \
    let cfg = read_file(\"input.json\")\n  \
    let who = getenv(\"PRISM_RUN_USER\")\n  \
    println(\"cfg={cfg} who={who} argc={args_count()}\")\n";

const ENV_VAR: &str = "PRISM_RUN_USER";

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let mut path = std::env::temp_dir();
        path.push(format!(
            "prism-run-lineage-{tag}-{}-{nanos}-{n}",
            process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

const fn prism_bin() -> &'static str {
    env!("CARGO_BIN_EXE_prism")
}

// Record a run of PROGRAM in `dir` with the given file contents, env value, and
// program arguments, returning the parsed `.plineage` sidecar.
fn record(dir: &Path, contents: &str, user: &str, args: &[&str]) -> Value {
    fs::write(dir.join("pipe.pr"), PROGRAM).unwrap();
    fs::write(dir.join("input.json"), contents).unwrap();
    let mut cmd = Command::new(prism_bin());
    cmd.current_dir(dir)
        .env(ENV_VAR, user)
        .arg("run")
        .arg("pipe.pr")
        .arg("--record")
        .arg("run.replay")
        .arg("--lineage")
        .arg("run.plineage")
        .arg("--");
    for arg in args {
        cmd.arg(arg);
    }
    let output = cmd.output().expect("runs prism run --record --lineage");
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = fs::read_to_string(dir.join("run.plineage")).unwrap();
    serde_json::from_str(&text).unwrap()
}

// The id of the single node of `kind` in a serialized graph.
fn node_id(graph: &Value, kind: &str) -> String {
    graph["nodes"]
        .as_array()
        .expect("nodes array")
        .iter()
        .find(|node| node["kind"].as_str() == Some(kind))
        .and_then(|node| node["id"].as_str())
        .unwrap_or_else(|| panic!("no {kind} node"))
        .to_string()
}

fn has_node(graph: &Value, kind: &str) -> bool {
    graph["nodes"]
        .as_array()
        .is_some_and(|nodes| nodes.iter().any(|node| node["kind"].as_str() == Some(kind)))
}

#[test]
fn recorded_run_writes_replay_and_lineage_with_all_observation_nodes() {
    let tmp = TempDir::new("emit");
    let graph = record(&tmp.path, "{\"t\": 5}", "alice", &["a", "b"]);

    assert!(
        tmp.path.join("run.replay").exists(),
        "wrote the replay trace"
    );
    assert!(tmp.path.join("run.plineage").exists(), "wrote the sidecar");
    assert_eq!(graph["format"].as_str(), Some("prism-lineage-graph-v1"));
    assert_eq!(graph["variant"].as_str(), Some("run"));

    // Every observed input and produced output is a node.
    for kind in [
        "request",
        "source-root",
        "stdlib-root",
        "compiler-identity",
        "argv",
        "env-read",
        "input-file",
        "trace",
        "stdout",
    ] {
        assert!(
            has_node(&graph, kind),
            "run graph should have a {kind} node"
        );
    }
}

#[test]
fn record_and_lineage_are_byte_identical_for_identical_runs() {
    let a = TempDir::new("det-a");
    let b = TempDir::new("det-b");
    record(&a.path, "{\"t\": 5}", "alice", &["a"]);
    record(&b.path, "{\"t\": 5}", "alice", &["a"]);
    // The sidecar names files by path, so identical relative runs match byte for
    // byte across two directories.
    assert_eq!(
        fs::read_to_string(a.path.join("run.plineage")).unwrap(),
        fs::read_to_string(b.path.join("run.plineage")).unwrap(),
        "identical runs must produce byte-identical sidecars"
    );
}

#[test]
fn changing_a_file_input_moves_only_the_matching_input_node() {
    let tmp = TempDir::new("file");
    let first = record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);
    let changed = record(&tmp.path, "{\"t\": 6}", "alice", &["a"]);

    assert_ne!(
        node_id(&first, "input-file"),
        node_id(&changed, "input-file"),
        "a changed file input must move the input-file node id"
    );
    assert_eq!(
        node_id(&first, "stdlib-root"),
        node_id(&changed, "stdlib-root"),
        "an unrelated node (stdlib root) must not move"
    );
    assert_eq!(
        node_id(&first, "source-root"),
        node_id(&changed, "source-root"),
        "the source did not change, so its root must not move"
    );
    assert_eq!(
        node_id(&first, "argv"),
        node_id(&changed, "argv"),
        "argv did not change, so its node must not move"
    );
}

#[test]
fn changing_only_argv_moves_only_the_argv_node() {
    let tmp = TempDir::new("argv");
    let first = record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);
    let changed = record(&tmp.path, "{\"t\": 5}", "alice", &["b"]);

    assert_ne!(
        node_id(&first, "argv"),
        node_id(&changed, "argv"),
        "a changed argument must move the argv node id"
    );
    assert_eq!(
        node_id(&first, "input-file"),
        node_id(&changed, "input-file"),
        "the file input did not change, so its node must not move"
    );
    assert_eq!(
        node_id(&first, "env-read"),
        node_id(&changed, "env-read"),
        "the environment read did not change, so its node must not move"
    );
    assert_eq!(
        node_id(&first, "stdout"),
        node_id(&changed, "stdout"),
        "the program reads no argument value, so stdout must not move"
    );
}

#[test]
fn verify_accepts_a_fresh_run_and_names_a_tampered_input() {
    let tmp = TempDir::new("verify");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);

    let fresh = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("verify")
        .arg("run.plineage")
        .output()
        .expect("runs prism lineage verify");
    assert!(
        fresh.status.success(),
        "a fresh run must verify: {}",
        String::from_utf8_lossy(&fresh.stderr)
    );

    fs::write(tmp.path.join("input.json"), "{\"t\": 9}").unwrap();
    let tampered = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("verify")
        .arg("run.plineage")
        .output()
        .unwrap();
    assert!(!tampered.status.success(), "a tampered input must fail");
    let err = String::from_utf8_lossy(&tampered.stderr);
    assert!(err.contains("input file"), "error names the input: {err}");
    assert!(err.contains("changed"), "error reports a mismatch: {err}");

    // A plain render still explains the old run even though verification failed.
    let render = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("show")
        .arg("run.plineage")
        .output()
        .unwrap();
    assert!(render.status.success(), "render must still succeed");
}

#[test]
fn a_missing_input_is_a_distinct_verification_error_but_render_still_works() {
    let tmp = TempDir::new("missing");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);
    fs::remove_file(tmp.path.join("input.json")).unwrap();

    let verify = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("verify")
        .arg("run.plineage")
        .output()
        .unwrap();
    assert!(!verify.status.success(), "a missing input must fail verify");
    let err = String::from_utf8_lossy(&verify.stderr);
    assert!(err.contains("missing"), "missing file is distinct: {err}");

    let render = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("show")
        .arg("run.plineage")
        .output()
        .unwrap();
    assert!(
        render.status.success(),
        "a missing input must not prevent explaining the old run"
    );
}

// `prism lineage why SIDECAR stdout` walks the graph backward and names the run's
// inputs and identity, and it does so from the sidecar alone.
#[test]
fn why_output_explains_stdout_from_the_sidecar() {
    let tmp = TempDir::new("why");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a", "b"]);

    let out = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("why")
        .arg("run.plineage")
        .arg("stdout")
        .output()
        .expect("runs prism lineage why");
    assert!(
        out.status.success(),
        "lineage why stdout must succeed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("why stdout"), "names the output: {text}");
    assert!(
        text.contains("input-file: input.json"),
        "names the input: {text}"
    );
    assert!(text.contains("argv: [\"a\", \"b\"]"), "names argv: {text}");
    assert!(text.contains("trace:"), "names the trace: {text}");
}

// The acceptance for `lineage why`: it works from the sidecar even after the source
// files have moved (been deleted), because the walk never touches disk.
#[test]
fn why_output_works_after_source_files_move() {
    let tmp = TempDir::new("why-moved");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);
    fs::remove_file(tmp.path.join("pipe.pr")).unwrap();
    fs::remove_file(tmp.path.join("input.json")).unwrap();

    let out = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("why")
        .arg("run.plineage")
        .arg("input.json")
        .output()
        .expect("runs prism lineage why");
    assert!(
        out.status.success(),
        "lineage why must explain a moved run: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(String::from_utf8_lossy(&out.stdout).contains("input.json"));
}

#[test]
fn why_output_unknown_selector_lists_the_available_outputs() {
    let tmp = TempDir::new("why-unknown");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);

    let out = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("why")
        .arg("run.plineage")
        .arg("no-such-output")
        .output()
        .expect("runs prism lineage why");
    assert!(!out.status.success(), "an unknown selector must fail");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("stdout"), "lists stdout: {err}");
    assert!(err.contains("input.json"), "lists the input file: {err}");
}

// The `.plineage` arm of `prism diff` acceptance: changing one input file names exactly that input as
// moved along with every downstream digest (trace, stdout), everything else
// preserved, and it exits nonzero so it can gate CI.
#[test]
fn diff_names_the_changed_input_and_downstream_outputs() {
    let a = TempDir::new("diff-a");
    let b = TempDir::new("diff-b");
    record(&a.path, "{\"t\": 5}", "alice", &["a"]);
    record(&b.path, "{\"t\": 6}", "alice", &["a"]);

    let out = Command::new(prism_bin())
        .arg("diff")
        .arg(a.path.join("run.plineage"))
        .arg(b.path.join("run.plineage"))
        .output()
        .expect("runs prism diff");
    assert!(
        !out.status.success(),
        "a diff with moved nodes must exit nonzero to gate CI"
    );
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        text.contains("moved    input-file input.json"),
        "the changed input is moved: {text}"
    );
    assert!(text.contains("moved    trace"), "the trace moved: {text}");
    assert!(text.contains("moved    stdout"), "stdout moved: {text}");
    assert!(
        text.contains("same     argv") && text.contains("same     source-root"),
        "unchanged inputs are preserved: {text}"
    );
    assert!(
        text.contains("0 added, 0 removed"),
        "nothing was added or removed: {text}"
    );
}

#[test]
fn diff_of_identical_runs_is_clean_and_exits_zero() {
    let a = TempDir::new("diff-same-a");
    let b = TempDir::new("diff-same-b");
    record(&a.path, "{\"t\": 5}", "alice", &["a"]);
    record(&b.path, "{\"t\": 5}", "alice", &["a"]);

    let out = Command::new(prism_bin())
        .arg("diff")
        .arg(a.path.join("run.plineage"))
        .arg(b.path.join("run.plineage"))
        .output()
        .expect("runs prism diff");
    assert!(out.status.success(), "identical runs diff clean, exit zero");
    assert!(String::from_utf8_lossy(&out.stdout).contains("unchanged"));
}

// `lineage verify --replay` acceptance: a fresh run verifies by replay (trace,
// stdout, and input-file digests all match), and tampering an input file is named.
#[test]
fn verify_lineage_replays_and_rehashes_then_names_a_tampered_input() {
    let tmp = TempDir::new("verify-lineage");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);

    let fresh = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("verify")
        .arg("run.plineage")
        .arg("--replay")
        .output()
        .expect("runs prism lineage verify --replay");
    assert!(
        fresh.status.success(),
        "a fresh run verifies by replay: {}",
        String::from_utf8_lossy(&fresh.stderr)
    );
    assert!(
        String::from_utf8_lossy(&fresh.stdout).contains("replay matches the sidecar"),
        "reports what was verified"
    );

    fs::write(tmp.path.join("input.json"), "{\"t\": 9}").unwrap();
    let tampered = Command::new(prism_bin())
        .current_dir(&tmp.path)
        .arg("lineage")
        .arg("verify")
        .arg("run.plineage")
        .arg("--replay")
        .output()
        .unwrap();
    assert!(
        !tampered.status.success(),
        "a tampered input must fail verify"
    );
    let err = String::from_utf8_lossy(&tampered.stderr);
    assert!(err.contains("input file"), "names the input node: {err}");
    assert!(err.contains("changed"), "reports a digest mismatch: {err}");
}

// A program that reads a file and writes a derived one, so its run graph gains a
// file-write output node keyed by the written path.
const WRITE_PROGRAM: &str = "fn main() : !{IO} Unit =\n  \
    let cfg = read_file(\"input.json\")\n  \
    write_file(\"out.txt\", \"seen:{cfg}\")\n  \
    println(\"wrote out.txt\")\n";

// Record a run of an arbitrary program in `dir`, writing the named input files
// first, and return the parsed `.plineage` sidecar.
fn record_program(dir: &Path, program: &str, inputs: &[(&str, &str)], args: &[&str]) -> Value {
    fs::write(dir.join("prog.pr"), program).unwrap();
    for (name, contents) in inputs {
        fs::write(dir.join(name), contents).unwrap();
    }
    let mut cmd = Command::new(prism_bin());
    cmd.current_dir(dir)
        .arg("run")
        .arg("prog.pr")
        .arg("--record")
        .arg("run.replay")
        .arg("--lineage")
        .arg("run.plineage")
        .arg("--");
    for arg in args {
        cmd.arg(arg);
    }
    let output = cmd.output().expect("runs prism run --record --lineage");
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_str(&fs::read_to_string(dir.join("run.plineage")).unwrap()).unwrap()
}

// The graph explains a file the run wrote: it gains a file-write node, `lineage why`
// names that file, and changing the input that feeds it moves the written output.
#[test]
fn graph_explains_a_written_file_and_diff_moves_it() {
    let a = TempDir::new("write-a");
    let b = TempDir::new("write-b");
    let graph = record_program(&a.path, WRITE_PROGRAM, &[("input.json", "5")], &[]);
    record_program(&b.path, WRITE_PROGRAM, &[("input.json", "6")], &[]);
    assert!(a.path.join("out.txt").exists(), "the run wrote the file");
    assert!(
        has_node(&graph, "file-write"),
        "the run graph names the written file"
    );

    let why = Command::new(prism_bin())
        .current_dir(&a.path)
        .arg("lineage")
        .arg("why")
        .arg("run.plineage")
        .arg("out.txt")
        .output()
        .expect("runs prism lineage why");
    assert!(
        why.status.success(),
        "lineage why out.txt must succeed: {}",
        String::from_utf8_lossy(&why.stderr)
    );
    let text = String::from_utf8_lossy(&why.stdout);
    assert!(
        text.contains("why written file out.txt"),
        "names the write: {text}"
    );
    assert!(
        text.contains("input-file: input.json"),
        "names the input it read: {text}"
    );

    let diff = Command::new(prism_bin())
        .arg("diff")
        .arg(a.path.join("run.plineage"))
        .arg(b.path.join("run.plineage"))
        .output()
        .expect("runs prism diff");
    assert!(
        !diff.status.success(),
        "a changed written output must gate CI"
    );
    assert!(
        String::from_utf8_lossy(&diff.stdout).contains("moved    file-write out.txt"),
        "the written output moved: {}",
        String::from_utf8_lossy(&diff.stdout)
    );
}

// `lineage why --json` and `diff --json` emit the answer object as JSON,
// deterministically (identical runs across two dirs produce byte-identical JSON).
#[test]
fn why_output_and_diff_json_are_deterministic() {
    let a = TempDir::new("json-a");
    let b = TempDir::new("json-b");
    record(&a.path, "{\"t\": 5}", "alice", &["a", "b"]);
    record(&b.path, "{\"t\": 5}", "alice", &["a", "b"]);

    let why = |dir: &Path| {
        Command::new(prism_bin())
            .current_dir(dir)
            .arg("lineage")
            .arg("why")
            .arg("run.plineage")
            .arg("stdout")
            .arg("--json")
            .output()
            .expect("runs prism lineage why --json")
    };
    let ja = why(&a.path);
    let jb = why(&b.path);
    assert!(ja.status.success() && jb.status.success());
    // Valid JSON, and byte-identical for identical relative runs.
    let _: Value = serde_json::from_slice(&ja.stdout).expect("lineage why --json is JSON");
    assert_eq!(ja.stdout, jb.stdout, "lineage why --json is deterministic");

    // `diff` takes its two positional sidecars first; `--json` follows.
    let diff = Command::new(prism_bin())
        .arg("diff")
        .arg(a.path.join("run.plineage"))
        .arg(b.path.join("run.plineage"))
        .arg("--json")
        .output()
        .expect("runs prism diff --json");
    assert!(diff.status.success(), "identical runs diff clean");
    let _: Value = serde_json::from_slice(&diff.stdout).expect("diff --json is JSON");
}

// `lineage verify --replay` resolves the replay trace from the graph's self-description and
// checks its digest: a tampered replay file and a missing one are distinct errors.
#[test]
fn verify_lineage_checks_the_replay_digest_from_the_graph() {
    let tmp = TempDir::new("replay-digest");
    record(&tmp.path, "{\"t\": 5}", "alice", &["a"]);
    let run = |dir: &Path| {
        Command::new(prism_bin())
            .current_dir(dir)
            .arg("lineage")
            .arg("verify")
            .arg("run.plineage")
            .arg("--replay")
            .output()
            .expect("runs prism lineage verify --replay")
    };
    assert!(run(&tmp.path).status.success(), "a fresh run verifies");

    // Tamper the durable trace: the graph records its digest, so the mismatch is
    // caught before replay.
    fs::write(tmp.path.join("run.replay"), "garbage").unwrap();
    let tampered = run(&tmp.path);
    assert!(
        !tampered.status.success(),
        "a tampered replay file must fail"
    );
    let err = String::from_utf8_lossy(&tampered.stderr);
    assert!(err.contains("replay file"), "names the replay file: {err}");
    assert!(err.contains("changed"), "reports a digest mismatch: {err}");

    // Remove it entirely: a distinct missing-file error.
    fs::remove_file(tmp.path.join("run.replay")).unwrap();
    let missing = run(&tmp.path);
    assert!(!missing.status.success(), "a missing replay file must fail");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("missing"),
        "missing is distinct from tampered: {}",
        String::from_utf8_lossy(&missing.stderr)
    );
}

// H3: recording a run and replaying its trace produce the identical provenance
// event sequence, hence the identical trace digest (the run's trace node id). This
// program observes only its argument count and a random draw, so it depends on
// neither the filesystem nor the environment and runs deterministically anywhere.
const PURE_PROGRAM: &str =
    "fn main() : !{IO} Unit = println(\"{args_count()} {rand_below(100)}\")\n";

#[test]
fn record_and_replay_produce_identical_provenance_events() {
    let full = prism::with_prelude(PURE_PROGRAM);
    let roots = prism::default_roots(Path::new("."));
    let cfg = prism::Config::default();

    let mut out = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    let recorded = prism::record_run_on(
        &full,
        &roots,
        &mut out,
        &mut input,
        &cfg,
        vec!["x".to_string(), "y".to_string()],
    )
    .unwrap();

    let mut replayed_out = Vec::new();
    let replayed =
        prism::replay_run_on(&full, &roots, &mut replayed_out, &recorded.trace, &cfg).unwrap();

    assert_eq!(
        recorded.events, replayed.events,
        "a replay must reproduce the recorded provenance events exactly"
    );
    assert_eq!(
        trace_digest(&recorded.events).hash,
        trace_digest(&replayed.events).hash,
        "record and replay must share the trace digest (the trace node id)"
    );
    assert!(
        !recorded.events.is_empty(),
        "the program performs recordable observations"
    );
}

// H3 diagnostic: a mismatched replay names the zero-based event index and the
// operation the program expected there. PURE_PROGRAM's first recorded frame is the
// integer argument count; replaying a program whose first read is a string against
// that trace diverges at event 0.
#[test]
fn mismatched_replay_names_the_event_index_and_expected_operation() {
    const STRING_FIRST: &str = "fn main() : !{IO} Unit = println(getenv(\"X\"))\n";

    let roots = prism::default_roots(Path::new("."));
    let cfg = prism::Config::default();

    let mut out = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    let recorded = prism::record_run_on(
        &prism::with_prelude(PURE_PROGRAM),
        &roots,
        &mut out,
        &mut input,
        &cfg,
        vec!["x".to_string()],
    )
    .unwrap();

    let mut replay_out = Vec::new();
    let err = prism::replay_run_on(
        &prism::with_prelude(STRING_FIRST),
        &roots,
        &mut replay_out,
        &recorded.trace,
        &cfg,
    )
    .expect_err("a program that reads a string cannot replay an integer-first trace");
    let msg = err.to_string();
    assert!(msg.contains("event 0"), "names the event index: {msg}");
    assert!(
        msg.contains("Env.getenv"),
        "names the expected operation: {msg}"
    );
    assert!(
        msg.contains("integer read"),
        "names what the trace held instead: {msg}"
    );
}

// H3 extends to writes: a program that writes a file re-executes the write on
// replay, so its output event recurs identically and the trace digest is unchanged.
#[test]
fn record_and_replay_reproduce_identical_write_events() {
    let dir = TempDir::new("h3-write");
    let target = dir.path.join("out.txt");
    let program = format!(
        "fn main() : !{{IO}} Unit =\n  write_file(\"{}\", \"payload\")\n  println(\"{{args_count()}}\")\n",
        target.display()
    );
    let full = prism::with_prelude(&program);
    let roots = prism::default_roots(Path::new("."));
    let cfg = prism::Config::default();

    let mut out = Vec::new();
    let mut input = std::io::Cursor::new(Vec::new());
    let recorded = prism::record_run_on(
        &full,
        &roots,
        &mut out,
        &mut input,
        &cfg,
        vec!["x".to_string()],
    )
    .unwrap();

    let mut replayed_out = Vec::new();
    let replayed =
        prism::replay_run_on(&full, &roots, &mut replayed_out, &recorded.trace, &cfg).unwrap();

    assert_eq!(
        recorded.events, replayed.events,
        "the write event must recur identically on replay"
    );
    assert_eq!(
        trace_digest(&recorded.events).hash,
        trace_digest(&replayed.events).hash,
        "a run that writes files keeps the record==replay trace digest"
    );
    assert!(
        recorded.events.iter().any(|e| e.op == OP_FS_WRITE_FILE),
        "the file write is a recorded provenance event"
    );
}
