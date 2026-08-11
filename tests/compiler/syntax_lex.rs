// The differential gate for the Prism-side raw lexer. The compiler's `lex_raw`
// pipeline stays authoritative; each committed `prism-syntax-tokens-v1` artifact
// embeds both the exact source text and that authoritative raw token stream and
// trivia. The harness `tests/fixtures/syntax/consumers/lex_check.pr` decodes an artifact,
// re-lexes the embedded text with `Syntax.Lex.lex_raw`, and reports whether the
// Prism lexer reproduces every raw token (wire kind, byte span, and decoded
// value) and every trivium. This test asserts that verdict: a divergence is a
// failure, not a silent fallback.
//
// The whole corpus is now lexed clean, interpolation included: an interpolated
// literal is split into its `istart`/`imid`/`iend` segments with the hole
// expressions re-lexed at their absolute source offsets, and each segment and
// hole token must match the compiler's raw stream.

use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, interpret_io_on_with_args, with_prelude, Config};

use super::fixture_stems;

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "consumers/lex_check.pr";

// Stems whose raw stream is interpolation-free.
const CLEAN_STEMS: [&str; 7] = [
    "classes",
    "contracts",
    "decls",
    "effects",
    "patterns",
    "stable",
    "types",
];

// Stems whose raw stream carries interpolation pieces; the Prism lexer now
// reproduces the split, so these lex clean as well.
const INTERP_STEMS: [&str; 3] = ["exprs", "interp", "roundtrip"];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

// Run the differential harness over one artifact and capture its single verdict
// line.
fn lex_verdict(stem: &str) -> String {
    let dir = fixture_dir();
    let src = fs::read_to_string(dir.join(HARNESS)).expect("harness source");
    let full = with_prelude(&src);
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let artifact = dir.join(format!("{stem}.syntax-tokens.json"));
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

fn assert_clean(stem: &str) {
    let out = lex_verdict(stem);
    assert!(
        out.starts_with("ok "),
        "{stem}: Prism lexer diverged from the compiler's raw stream: {out}"
    );
}

macro_rules! lex_gate {
    ($($name:ident => $stem:literal),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_clean($stem);
        })+
    };
}

lex_gate! {
    lex_classes => "classes",
    lex_contracts => "contracts",
    lex_decls => "decls",
    lex_effects => "effects",
    lex_patterns => "patterns",
    lex_stable => "stable",
    lex_types => "types",
    lex_exprs => "exprs",
    lex_interp => "interp",
    lex_roundtrip => "roundtrip",
}

// Every syntax-tokens artifact (bar the wrong-schema fixture) is accounted for
// in a stem list, so a new corpus file cannot slip past the differential gate.
#[test]
fn lex_covers_every_stem() {
    let found = fixture_stems(&fixture_dir(), ".syntax-tokens.json", "mismatch");

    let mut expected: Vec<String> = CLEAN_STEMS
        .iter()
        .chain(INTERP_STEMS.iter())
        .map(ToString::to_string)
        .collect();
    expected.sort_unstable();

    assert_eq!(
        found, expected,
        "syntax-tokens fixtures and the differential-gate stem lists have drifted apart"
    );
}
