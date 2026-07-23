// The syntax-artifact round trip: every committed golden decodes into the
// typed Prism `Syntax.*` vocabulary and re-encodes byte-identically, run
// through the interpreter via the committed harness program
// `tests/fixtures/syntax/roundtrip.pr`. This is the acceptance gate for the
// Prism-side codecs: the compiler's export and the standard library's
// re-encoding agree on every byte, and a wrong schema tag is refused with a
// structured error rather than a partial document.
//
// One test per corpus stem (each interpreter run re-checks the harness and its
// stdlib imports, so a stem costs seconds); the stem list is static so the
// tests exist at collection time, and `roundtrip_covers_every_stem` pins the
// list against the fixture directory so a new corpus file cannot silently
// skip the gate.

use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, interpret_io_on_with_args, with_prelude, Config};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";

// Every corpus stem with committed artifact goldens, kept sorted.
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

// Run the harness program over one artifact file and capture its stdout.
fn roundtrip(artifact: &Path, mode: &str) -> String {
    let dir = fixture_dir();
    let src = fs::read_to_string(dir.join("roundtrip.pr")).expect("harness source");
    let full = with_prelude(&src);
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut sink = Vec::new();
    let cfg = Config::from_env();
    let args = vec![artifact.display().to_string(), mode.to_string()];
    interpret_io_on_with_args(
        &full,
        &default_roots(root),
        &mut sink,
        &mut &b""[..],
        &cfg,
        args,
    )
    .unwrap_or_else(|e| panic!("{}: harness run: {e}", artifact.display()));
    String::from_utf8(sink).expect("utf8 harness output")
}

// Decode then re-encode reproduces the exact golden bytes for one stem's two
// artifact families.
fn assert_stem_roundtrips(stem: &str) {
    let dir = fixture_dir();
    for (family, mode) in [("syntax-tokens", "tokens"), ("surface-syntax", "surface")] {
        let path = dir.join(format!("{stem}.{family}.json"));
        let golden = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{stem}.{family}: missing golden: {e}"));
        let out = roundtrip(&path, mode);
        assert_eq!(
            out, golden,
            "{stem}.{family}: decode + re-encode must reproduce the artifact bytes"
        );
    }
}

macro_rules! stem_roundtrip {
    ($($name:ident => $stem:literal),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_stem_roundtrips($stem);
        })+
    };
}

stem_roundtrip! {
    roundtrip_classes => "classes",
    roundtrip_contracts => "contracts",
    roundtrip_decls => "decls",
    roundtrip_effects => "effects",
    roundtrip_exprs => "exprs",
    roundtrip_interp => "interp",
    roundtrip_patterns => "patterns",
    roundtrip_roundtrip => "roundtrip",
    roundtrip_stable => "stable",
    roundtrip_types => "types",
}

// The static stem list matches the fixture directory exactly, so adding a
// corpus file without extending the gate is a test failure, not a silent skip.
#[test]
fn roundtrip_covers_every_stem() {
    let mut found: Vec<String> = fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .filter_map(Result::ok)
        .filter_map(|e| {
            let name = e.file_name().into_string().ok()?;
            let stem = name.strip_suffix(".surface-syntax.json")?;
            (!stem.starts_with("mismatch")).then(|| stem.to_string())
        })
        .collect();
    found.sort_unstable();
    assert_eq!(
        found, STEMS,
        "fixture stems and the static round-trip list have drifted apart"
    );
}

// The committed wrong-tag fixtures are refused by the versioned Prism reader
// with the structured schema error.
#[test]
fn syntax_roundtrip_rejects_wrong_schema() {
    let dir = fixture_dir();
    for (fixture, mode) in [
        ("mismatch.syntax-tokens.json", "tokens"),
        ("mismatch.surface-syntax.json", "surface"),
    ] {
        let out = roundtrip(&dir.join(fixture), mode);
        assert!(
            out.starts_with("decode error: $.schema"),
            "{fixture}: expected the schema refusal, got: {out}"
        );
    }
}
