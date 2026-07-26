// The differential gate for the Prism-side lexer's refusal behavior. The
// compiler's `lex` pipeline stays authoritative; each committed
// `prism-syntax-diagnostics-v1` artifact embeds a source with exactly one
// lexical fault, the exact source text, and the compiler's own diagnostic (the
// stable append-only code, the caret byte offset, and the rendered message). The
// harness `tests/fixtures/syntax/consumers/diag_check.pr` decodes an artifact,
// re-lexes the embedded text with `Syntax.Lex.lex_raw`, and reports whether the
// Prism lexer refuses at the same code, offset, and message, and classifies
// incompleteness the same way (`lex_incomplete` is true exactly for the
// unterminated-string and unterminated-hole faults). A divergence is a failure,
// not a silent fallback.
//
// The negative corpus covers the whole `LexError` vocabulary, one fixture per
// variant; the covers test below fails if a new malformed lex fixture is added
// without a gate entry.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, interpret_io_on_with_args, with_prelude, Config};
use serde_json::Value;

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "consumers/diag_check.pr";
const ACCEPT: &str = "PRISM_ACCEPT_SYNTAX_FIXTURES";
const PHASE: &str = "syntax-diagnostics";
const SCHEMA: &str = "prism-syntax-diagnostics-v1";

// One negative fixture per lexical error variant (E7000 through E7004), so the
// gate covers the whole `LexError` vocabulary. The stem names both the committed
// source and its diagnostics golden; the code is the variant the compiler must
// raise. `malformed_lex` (the pre-existing unterminated-string fixture) is the
// E7003 case.
const NEG: [(&str, &str); 5] = [
    ("malformed_invalid", "E7000"),
    ("malformed_empty_hole", "E7001"),
    ("malformed_unterm_hole", "E7002"),
    ("malformed_lex", "E7003"),
    ("malformed_number_sep", "E7004"),
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

// The committed golden: the dump's bytes plus exactly one terminating newline, so
// the file satisfies the end-of-file hook while the comparison stays exact bytes.
fn golden_document(dump: &str) -> String {
    format!("{dump}\n")
}

// Write a golden atomically (temp then rename) so an interrupted acceptance never
// leaves a truncated golden behind.
fn write_golden(path: &Path, bytes: &str) {
    let tmp = path.with_extension("tmp");
    fs::write(&tmp, bytes).unwrap_or_else(|e| panic!("write {}: {e}", tmp.display()));
    fs::rename(&tmp, path).unwrap_or_else(|e| panic!("rename to {}: {e}", path.display()));
}

// The golden gate: each negative source dumps a single lex diagnostic
// deterministically, matches its committed golden, and carries the schema tag and
// the expected code and phase. Under the acceptance switch it rewrites goldens.
#[test]
fn diag_goldens_hold() {
    let accepting = env::var_os(ACCEPT).is_some();
    let dir = fixture_dir();
    for (stem, code) in NEG {
        let src = read(&dir.join(format!("{stem}.pr")));
        let out = prism::dump(PHASE, &src).unwrap_or_else(|e| panic!("{stem}: dump: {e}"));
        let again = prism::dump(PHASE, &src).unwrap_or_else(|e| panic!("{stem}: dump: {e}"));
        assert_eq!(
            out, again,
            "{stem}: diagnostics dump must be byte-identical across runs"
        );

        let golden_path = dir.join(format!("{stem}.{PHASE}.json"));
        let document = golden_document(&out);
        if accepting {
            write_golden(&golden_path, &document);
            eprintln!("accepted {}", golden_path.display());
        } else {
            let golden = read(&golden_path);
            assert!(
                document == golden,
                "{stem}: diagnostics bytes diverge from the committed golden \
                 (review as a syntax boundary change; regenerate with {ACCEPT}=1)"
            );
        }

        let doc: Value = serde_json::from_str(&out).unwrap_or_else(|e| panic!("{stem}: JSON: {e}"));
        assert_eq!(doc["schema"], SCHEMA, "{stem}: schema tag");
        let diags = doc["diagnostics"]
            .as_array()
            .unwrap_or_else(|| panic!("{stem}: diagnostics must be an array"));
        assert_eq!(diags.len(), 1, "{stem}: expected exactly one diagnostic");
        assert_eq!(diags[0]["code"], code, "{stem}: expected code {code}");
        assert_eq!(
            diags[0]["phase"], "lex",
            "{stem}: expected a lex diagnostic"
        );
    }
}

// Run the differential harness over one artifact and capture its single verdict
// line.
fn diag_verdict(stem: &str) -> String {
    let dir = fixture_dir();
    let src = fs::read_to_string(dir.join(HARNESS)).expect("harness source");
    let full = with_prelude(&src);
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let artifact = dir.join(format!("{stem}.{PHASE}.json"));
    let mut sink = Vec::new();
    let cfg = Config::from_env();
    let args = vec![artifact.display().to_string()];
    interpret_io_on_with_args(
        &full,
        &default_roots(root),
        &mut sink,
        &mut &b""[..],
        &cfg,
        args,
    )
    .unwrap_or_else(|e| panic!("{stem}: harness run: {e}"));
    String::from_utf8(sink)
        .expect("utf8 harness output")
        .trim()
        .to_string()
}

fn assert_agrees(stem: &str, code: &str) {
    let out = diag_verdict(stem);
    assert!(
        out.starts_with("ok "),
        "{stem}: Prism lexer diverged from the compiler's {code} diagnostic: {out}"
    );
}

macro_rules! diag_gate {
    ($($name:ident => ($stem:literal, $code:literal)),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_agrees($stem, $code);
        })+
    };
}

diag_gate! {
    diag_invalid => ("malformed_invalid", "E7000"),
    diag_empty_hole => ("malformed_empty_hole", "E7001"),
    diag_unterm_hole => ("malformed_unterm_hole", "E7002"),
    diag_unterm_str => ("malformed_lex", "E7003"),
    diag_number_sep => ("malformed_number_sep", "E7004"),
}

// Every malformed lex fixture is exercised by the gate: a new `malformed_*.pr`
// source (other than the parse-fault fixture, which raises no lex diagnostic)
// cannot slip past the negative corpus.
#[test]
fn diag_covers_every_malformed_lex_fixture() {
    let mut found: Vec<String> = fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .filter_map(Result::ok)
        .filter_map(|e| {
            let name = e.file_name().into_string().ok()?;
            let stem = name.strip_suffix(".pr")?;
            let keep = stem.starts_with("malformed") && stem != "malformed_parse";
            keep.then(|| stem.to_string())
        })
        .collect();
    found.sort_unstable();

    let mut expected: Vec<String> = NEG.iter().map(|(s, _)| s.to_string()).collect();
    expected.sort_unstable();

    assert_eq!(
        found, expected,
        "malformed lex fixtures and the negative-corpus stem list have drifted apart"
    );
}
