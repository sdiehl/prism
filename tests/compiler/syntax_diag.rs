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

// The parse-fault corpus: stem, code, and whether the diagnostic carries a
// non-empty canonical expectation set. Deliberate migration diagnostics do not;
// generic refusals must.
const NEG_PARSE: [(&str, &str, bool); 3] = [
    ("malformed_parse", "E7100", true),
    ("malformed_parse_eof", "E7100", true),
    ("malformed_parse_flip", "E7100", false),
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

// The committed golden: the dump's bytes with the build stamp punched out, plus
// one terminating newline for the end-of-file hook. The stamp is still checked
// live below, against the dump rather than the golden.
fn golden_document(dump: &str) -> String {
    format!("{}\n", super::seam::json(dump))
}

// Write a golden atomically (temp then rename) so an interrupted acceptance never
// leaves a truncated golden behind.
fn write_golden(path: &Path, bytes: &str) {
    let tmp = path.with_extension("tmp");
    fs::write(&tmp, bytes).unwrap_or_else(|e| panic!("write {}: {e}", tmp.display()));
    fs::rename(&tmp, path).unwrap_or_else(|e| panic!("rename to {}: {e}", path.display()));
}

// Dump one negative source, assert determinism, hold (or accept) its golden,
// and return the single diagnostic it carries.
fn golden_diagnostic(stem: &str, accepting: bool) -> Value {
    let dir = fixture_dir();
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
    assert_eq!(
        doc["compiler"],
        env!("CARGO_PKG_VERSION"),
        "{stem}: compiler version"
    );
    let diags = doc["diagnostics"]
        .as_array()
        .unwrap_or_else(|| panic!("{stem}: diagnostics must be an array"));
    assert_eq!(diags.len(), 1, "{stem}: expected exactly one diagnostic");
    diags[0].clone()
}

// The golden gate: each negative source dumps a single lex diagnostic
// deterministically, matches its committed golden, and carries the schema tag and
// the expected code and phase. Under the acceptance switch it rewrites goldens.
#[test]
fn diag_goldens_hold() {
    let accepting = env::var_os(ACCEPT).is_some();
    for (stem, code) in NEG {
        let diag = golden_diagnostic(stem, accepting);
        assert_eq!(diag["code"], code, "{stem}: expected code {code}");
        assert_eq!(diag["phase"], "lex", "{stem}: expected a lex diagnostic");
    }
}

// The parse-side golden gate over the three refusal shapes the program seam can
// produce: an unexpected token (canonical expectation set present), an early end
// of source (the layout pass closes the block, so the fault is the general code
// at a zero-width caret on the virtual closer), and a deliberate migration
// rewrite (the message names the rewrite, so the generic expectation set stays
// empty). The exhausted-stream code is absent on purpose: only the expression
// entry can reach it, and this seam parses programs.
#[test]
fn parse_diag_goldens_hold() {
    let accepting = env::var_os(ACCEPT).is_some();
    for (stem, code, has_expected) in NEG_PARSE {
        let diag = golden_diagnostic(stem, accepting);
        assert_eq!(diag["code"], code, "{stem}: expected code {code}");
        assert_eq!(
            diag["phase"], "parse",
            "{stem}: expected a parse diagnostic"
        );
        let expected = diag["expected"]
            .as_array()
            .unwrap_or_else(|| panic!("{stem}: expected must be an array"));
        assert_eq!(
            !expected.is_empty(),
            has_expected,
            "{stem}: expectation-set presence diverged from the corpus contract"
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

// Every malformed fixture is exercised by a gate: a new `malformed_*.pr`
// source cannot slip past the negative corpus. The `malformed_parse` prefix
// routes a stem to the parse-fault table; everything else must be in the lex
// table.
#[test]
fn diag_covers_every_malformed_fixture() {
    let mut lex_found: Vec<String> = Vec::new();
    let mut parse_found: Vec<String> = Vec::new();
    for entry in fs::read_dir(fixture_dir()).expect("fixture dir") {
        let Ok(entry) = entry else { continue };
        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };
        let Some(stem) = name.strip_suffix(".pr") else {
            continue;
        };
        if stem.starts_with("malformed_parse") {
            parse_found.push(stem.to_string());
        } else if stem.starts_with("malformed") {
            lex_found.push(stem.to_string());
        }
    }
    lex_found.sort_unstable();
    parse_found.sort_unstable();

    let mut lex_expected: Vec<String> = NEG.iter().map(|(s, _)| s.to_string()).collect();
    lex_expected.sort_unstable();
    let mut parse_expected: Vec<String> = NEG_PARSE.iter().map(|(s, _, _)| s.to_string()).collect();
    parse_expected.sort_unstable();

    assert_eq!(
        lex_found, lex_expected,
        "malformed lex fixtures and the negative-corpus stem list have drifted apart"
    );
    assert_eq!(
        parse_found, parse_expected,
        "malformed parse fixtures and the parse-fault stem list have drifted apart"
    );
}
