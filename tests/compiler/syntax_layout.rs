// The differential gate for the Prism-side layout pass. The compiler's `lex`
// pipeline (raw tokens plus the offside layout) stays authoritative; each
// committed `prism-syntax-tokens-v1` artifact embeds both the exact source text
// and that authoritative post-layout token stream (`parse`). The harness
// `tests/fixtures/syntax/consumers/layout_check.pr` decodes an artifact, re-lays
// the embedded text with `Syntax.Layout.layout`, and reports whether the Prism
// pass reproduces every post-layout token (wire kind, byte span, and decoded
// value), including the virtual block delimiters. This test asserts that
// verdict: a divergence is a failure, not a silent fallback.

use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, interpret_io_on_with_args, with_prelude, Config};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "consumers/layout_check.pr";

// Every committed syntax-tokens stem: the layout pass must reproduce the
// post-layout stream of all of them, interpolation and declaration bodies
// included.
const STEMS: [&str; 10] = [
    "classes",
    "contracts",
    "decls",
    "effects",
    "exprs",
    "interp",
    "patterns",
    "roundtrip",
    "stable",
    "types",
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

// Run the differential harness over one artifact and capture its single verdict
// line.
fn layout_verdict(stem: &str) -> String {
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
    let out = layout_verdict(stem);
    assert!(
        out.starts_with("ok "),
        "{stem}: Prism layout diverged from the compiler's parse stream: {out}"
    );
}

macro_rules! layout_gate {
    ($($name:ident => $stem:literal),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_clean($stem);
        })+
    };
}

layout_gate! {
    layout_classes => "classes",
    layout_contracts => "contracts",
    layout_decls => "decls",
    layout_effects => "effects",
    layout_exprs => "exprs",
    layout_interp => "interp",
    layout_patterns => "patterns",
    layout_roundtrip => "roundtrip",
    layout_stable => "stable",
    layout_types => "types",
}

// Every syntax-tokens artifact (bar the wrong-schema fixture) is covered by the
// layout gate, so a new corpus file cannot slip past it.
#[test]
fn layout_covers_every_stem() {
    let mut found: Vec<String> = fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .filter_map(Result::ok)
        .filter_map(|e| {
            let name = e.file_name().into_string().ok()?;
            let stem = name.strip_suffix(".syntax-tokens.json")?;
            (!stem.starts_with("mismatch")).then(|| stem.to_string())
        })
        .collect();
    found.sort_unstable();

    let mut expected: Vec<String> = STEMS.iter().map(ToString::to_string).collect();
    expected.sort_unstable();

    assert_eq!(
        found, expected,
        "syntax-tokens fixtures and the layout-gate stem list have drifted apart"
    );
}
