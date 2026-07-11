// `--time-compile` / `PRISM_TIME_COMPILE`: one structured timing row per compiler
// phase, on stderr only. The contract these tests check: the rows are line-oriented
// and schema-stable (fixed leading fields, phases in pipeline order, `cold`
// status), program stdout is byte-identical with and without the knob, and the
// knob off emits no rows. Wall times themselves are never asserted; only that a
// `<n>.<n>ms` field is present and well-formed.

use std::path::{Path, PathBuf};
use std::process::{self, Command, Stdio};

// A program that compiles through every phase and reads no input, so its stdout is
// deterministic and the interpreter `eval` row always fires.
const PROGRAM: &str = "fn main() = println(1 + 2)\n";

// The pipeline order the rows must appear in for an interpreted `run`. Not every
// row must be present, but the ones that are must be in this order.
const PIPELINE_ORDER: &[&str] = &[
    "parse",
    "resolve",
    "desugar",
    "typecheck",
    "elaborate",
    "opt.pre",
    "lower.effects",
    "opt.late",
    "eval",
];

struct Output {
    stdout: Vec<u8>,
    stderr: String,
}

fn temp_program(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("prism_time_compile_{name}_{}", process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("prog.pr");
    std::fs::write(&file, PROGRAM).unwrap();
    file
}

fn run(file: &Path, time_compile: bool) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_prism"));
    cmd.arg("run").arg(file).stdin(Stdio::null());
    if time_compile {
        cmd.env("PRISM_TIME_COMPILE", "1");
    } else {
        cmd.env_remove("PRISM_TIME_COMPILE");
    }
    let out = cmd.output().expect("spawn prism");
    assert!(out.status.success(), "prism run failed: {out:?}");
    Output {
        stdout: out.stdout,
        stderr: String::from_utf8(out.stderr).expect("stderr utf8"),
    }
}

// The timing rows on stderr, split into their tab-separated fields.
fn phase_rows(stderr: &str) -> Vec<Vec<&str>> {
    stderr
        .lines()
        .filter(|l| l.starts_with("phase\t"))
        .map(|l| l.split('\t').collect())
        .collect()
}

fn is_millis(field: &str) -> bool {
    field.strip_suffix("ms").is_some_and(|n| {
        n.split_once('.').is_some_and(|(a, b)| {
            !a.is_empty() && b.len() == 1 && a.chars().chain(b.chars()).all(|c| c.is_ascii_digit())
        })
    })
}

fn is_abbrev_digest(field: &str, prefix: &str) -> bool {
    field
        .strip_prefix(prefix)
        .is_some_and(|h| !h.is_empty() && h.len() <= 8 && h.chars().all(|c| c.is_ascii_hexdigit()))
}

#[test]
fn rows_are_schema_stable_and_in_pipeline_order() {
    let file = temp_program("schema");
    let out = run(&file, true);
    let rows = phase_rows(&out.stderr);
    assert!(
        rows.len() >= PIPELINE_ORDER.len(),
        "expected at least one row per pipeline phase, got:\n{}",
        out.stderr
    );

    let mut seen_names = Vec::new();
    for row in &rows {
        // Fixed leading fields: `phase`, name, `<n>.<n>ms`, `in=src:<hex>`, `cold`.
        assert!(row.len() >= 5, "row has too few fields: {row:?}");
        assert_eq!(
            row[0], "phase",
            "field 1 must be the literal `phase`: {row:?}"
        );
        assert!(is_millis(row[2]), "field 3 must be `<n>.<n>ms`: {row:?}");
        assert!(
            is_abbrev_digest(row[3], "in=src:"),
            "field 4 must be `in=src:<hex>`: {row:?}"
        );
        assert_eq!(row[4], "cold", "field 5 must be the `cold` status: {row:?}");
        seen_names.push(row[1]);
    }

    // Every emitted phase name is a known pipeline phase, and the phases appear in
    // pipeline order (indices into PIPELINE_ORDER strictly increasing).
    let mut last = None;
    for name in &seen_names {
        let idx = PIPELINE_ORDER
            .iter()
            .position(|p| p == name)
            .unwrap_or_else(|| panic!("unknown phase `{name}` in:\n{}", out.stderr));
        if let Some(prev) = last {
            assert!(
                idx > prev,
                "phases out of pipeline order at `{name}`:\n{}",
                out.stderr
            );
        }
        last = Some(idx);
    }

    // The core phases a `run` always exercises are present.
    for required in ["parse", "typecheck", "elaborate", "eval"] {
        assert!(
            seen_names.contains(&required),
            "missing required phase `{required}`:\n{}",
            out.stderr
        );
    }

    // The elaborate row carries its output artifact key; the typecheck row carries
    // the definition count.
    let elaborate = rows.iter().find(|r| r[1] == "elaborate").unwrap();
    assert!(
        elaborate.iter().any(|f| is_abbrev_digest(f, "out=core:")),
        "elaborate row must carry `out=core:<hex>`: {elaborate:?}"
    );
    let typecheck = rows.iter().find(|r| r[1] == "typecheck").unwrap();
    assert!(
        typecheck.iter().any(|f| f.starts_with("defs=")),
        "typecheck row must carry a `defs=` count: {typecheck:?}"
    );

    let _ = std::fs::remove_dir_all(file.parent().unwrap());
}

#[test]
fn stdout_is_byte_identical_with_and_without_the_flag() {
    let file = temp_program("stdout");
    let on = run(&file, true);
    let off = run(&file, false);
    assert_eq!(
        on.stdout, off.stdout,
        "program stdout must not change under --time-compile"
    );
    let _ = std::fs::remove_dir_all(file.parent().unwrap());
}

#[test]
fn no_rows_when_the_flag_is_off() {
    let file = temp_program("off");
    let off = run(&file, false);
    assert!(
        !off.stderr.contains("phase\t"),
        "no timing rows must be emitted with the flag off, got stderr:\n{}",
        off.stderr
    );
    let _ = std::fs::remove_dir_all(file.parent().unwrap());
}
