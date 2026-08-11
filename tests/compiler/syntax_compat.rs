// Released-format compatibility for the syntax schemas.
//
// A published artifact outlives the compiler that wrote it, so the promise a
// reader makes about an older document has to be written down and gated, not
// assumed. `tests/fixtures/syntax/released/<version>/` holds artifacts exactly
// as an earlier release cut them, byte for byte, and is never regenerated: the
// current reader must decode them, re-encode them to the same bytes, and agree
// with the current exporter on everything except the compiler stamp they carry.
//
// The refusal side matters as much. A document naming a different schema
// version is refused whether that version is older or newer than the current
// one; an old artifact is never quietly read under the current tag, and a
// newer one is never guessed at. The compiler version inside the envelope is
// data, not a gate: it records who wrote the document, and a reader that
// demanded its own version would make every artifact expire on release day.

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

use prism::{default_roots, dump, interpret_io_on_with_args, with_prelude, Config};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const RELEASED_DIR: &str = "released";
const HARNESS: &str = "roundtrip.pr";

// The release whose artifacts are retained, and the name of its directory.
const RETAINED: &str = "0.14.0";

// The retained corpus: representative sources across declaration forms, string
// interpolation, stable families with migrations, and type syntax.
const STEMS: [&str; 4] = ["decls", "interp", "stable", "types"];

// The artifact families retained from that release, as (file suffix, harness
// mode). Schema tags live in the matrix below.
const RETAINED_FAMILIES: [(&str, &str); 2] =
    [("syntax-tokens", "tokens"), ("surface-syntax", "surface")];

// What the current reader promises about one syntax schema.
//
// `Read` means the tag shipped in the named earlier release and its documents
// are still read unchanged; the retained corpus is the evidence. `New` means
// this release introduces the tag, so there is no earlier document to read and
// nothing is retained for it.
//
// The policy allows two states no schema is in yet. A shape change that leaves
// old documents interpretable bumps the tag and gains an explicit upgrade from
// the old one; a change that cannot be upgraded rejects the old tag outright.
// Neither has been needed, because no shipped syntax schema has changed shape.
#[derive(Clone, Copy)]
enum Compat {
    Read(&'static str),
    New,
}

struct SchemaRow {
    // The `dump` phase that emits the artifact.
    phase: &'static str,
    // The schema tag, re-typed here independently of the compiler so an
    // emitter drift cannot re-pin the value it is checked against.
    tag: &'static str,
    compat: Compat,
}

const MATRIX: [SchemaRow; 4] = [
    SchemaRow {
        phase: "syntax-tokens",
        tag: "prism-syntax-tokens-v1",
        compat: Compat::Read(RETAINED),
    },
    SchemaRow {
        phase: "surface-syntax",
        tag: "prism-surface-syntax-v1",
        compat: Compat::Read(RETAINED),
    },
    SchemaRow {
        phase: "syntax-diagnostics",
        tag: "prism-syntax-diagnostics-v1",
        compat: Compat::New,
    },
    SchemaRow {
        phase: "resolved-syntax",
        tag: "prism-resolved-syntax-v1",
        compat: Compat::New,
    },
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn retained_dir() -> PathBuf {
    fixture_dir().join(RELEASED_DIR).join(RETAINED)
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn json(path: &Path) -> Value {
    serde_json::from_str(&read(path)).unwrap_or_else(|e| panic!("{}: JSON: {e}", path.display()))
}

// The schema tag a phase actually emits. The single-file seams are read from a
// live export; the resolved seam needs a resolved program rather than a snippet,
// so its committed golden carries the tag instead.
fn emitted_tag(phase: &str, src: &str) -> String {
    let doc = dump(phase, src).map_or_else(
        |_| json(&fixture_dir().join(format!("stable.{phase}.json"))),
        |out| serde_json::from_str::<Value>(&out).expect("emitted JSON"),
    );
    doc["schema"]
        .as_str()
        .unwrap_or_else(|| panic!("{phase}: no schema tag"))
        .to_string()
}

// Run the committed round-trip harness over one artifact and capture its
// output: the re-encoded bytes, or a structured refusal.
fn roundtrip(artifact: &Path, mode: &str) -> String {
    let src = read(&fixture_dir().join(HARNESS));
    let full = with_prelude(&src);
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let args = vec![artifact.display().to_string(), mode.to_string()];
    let mut sink = Vec::new();
    interpret_io_on_with_args(
        &full,
        &default_roots(root),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        args,
    )
    .unwrap_or_else(|e| panic!("{}: harness run: {e}", artifact.display()));
    String::from_utf8(sink).expect("utf8 harness output")
}

// A retained artifact decodes into the current typed vocabulary and re-encodes
// to the exact bytes the older release wrote: the reader neither rejects the
// older stamp nor silently rewrites the document into a newer shape.
fn assert_stem_reads(stem: &str) {
    for (family, mode) in RETAINED_FAMILIES {
        let path = retained_dir().join(format!("{stem}.{family}.json"));
        let released = read(&path);
        let out = roundtrip(&path, mode);
        assert_eq!(
            out, released,
            "{RETAINED}/{stem}.{family}: a retained release artifact must re-encode byte-identically"
        );
    }
}

macro_rules! retained_reads {
    ($($name:ident => $stem:literal),+ $(,)?) => {
        $(#[test]
        fn $name() {
            assert_stem_reads($stem);
        })+
    };
}

retained_reads! {
    retained_decls_still_reads => "decls",
    retained_interp_still_reads => "interp",
    retained_stable_still_reads => "stable",
    retained_types_still_reads => "types",
}

// Every retained artifact carries the stamp of the release it was cut from, so
// the corpus cannot be quietly refreshed into current output and keep claiming
// to test an older format.
#[test]
fn retained_artifacts_carry_the_released_stamp() {
    for stem in STEMS {
        for (family, _) in RETAINED_FAMILIES {
            let path = retained_dir().join(format!("{stem}.{family}.json"));
            let doc = json(&path);
            assert_eq!(
                doc["compiler"], RETAINED,
                "{stem}.{family}: retained artifact is not stamped {RETAINED}"
            );
        }
    }
}

// The shape statement: the current exporter reproduces a retained artifact exactly,
// apart from the compiler stamp inside the envelope. Comparing the whole
// document rather than a schema tag is what makes the tag's claim honest, since
// an unbumped tag over a drifted shape is precisely the failure this catches.
#[test]
fn retained_artifacts_match_todays_export_modulo_stamp() {
    for stem in STEMS {
        for (family, _) in RETAINED_FAMILIES {
            let path = retained_dir().join(format!("{stem}.{family}.json"));
            let released = read(&path);
            let doc = json(&path);
            let source = doc["source"]["text"]
                .as_str()
                .unwrap_or_else(|| panic!("{stem}.{family}: no embedded source"));

            let today =
                dump(family, source).unwrap_or_else(|e| panic!("{stem}.{family}: dump: {e}"));
            let today = format!("{today}\n");

            let stamp = |doc: &str, version: &str| {
                doc.replace(
                    &format!("\"compiler\": \"{version}\""),
                    "\"compiler\": \"<version>\"",
                )
            };
            assert_eq!(
                stamp(&today, env!("CARGO_PKG_VERSION")),
                stamp(&released, RETAINED),
                "{stem}.{family}: the exported shape drifted from {RETAINED} without a schema bump"
            );
        }
    }
}

// A schema tag is matched exactly, never ordered. An older tag is not read
// under the current one and a newer tag is not guessed at; both are refused
// with the structured schema error, and the untouched document still decodes so
// the refusal is attributable to the tag alone.
#[test]
fn other_schema_versions_are_refused() {
    let stem = STEMS[0];
    for (family, mode) in RETAINED_FAMILIES {
        let path = retained_dir().join(format!("{stem}.{family}.json"));
        let released = read(&path);
        let tag = MATRIX
            .iter()
            .find(|r| r.phase == family)
            .unwrap_or_else(|| panic!("{family}: not in the compatibility matrix"))
            .tag;
        assert!(
            released.contains(tag),
            "{stem}.{family}: retained artifact does not carry {tag}"
        );

        for other in ["v0", "v2"] {
            let stripped = tag
                .strip_suffix("v1")
                .unwrap_or_else(|| panic!("{tag}: schema tag is not version-suffixed"));
            let retagged = released.replace(tag, &format!("{stripped}{other}"));
            let tmp = std::env::temp_dir().join(format!("prism_compat_{family}_{other}.json"));
            fs::write(&tmp, &retagged).expect("write retagged artifact");
            let out = roundtrip(&tmp, mode);
            assert!(
                out.starts_with("decode error: $.schema"),
                "{family}: a {other} document was not refused on its tag, got: {out}"
            );
        }
    }
}

// The matrix is the record, so it must describe the schemas that exist. Every
// row's tag is the one the compiler actually emits, every `Read` row has a
// retained corpus stamped with the release it names, and every `New` row has
// nothing retained: a schema introduced here has no older document to read.
#[test]
fn compatibility_matrix_matches_the_corpus() {
    let src = read(&fixture_dir().join(format!("{}.pr", STEMS[0])));
    for row in &MATRIX {
        assert_eq!(
            emitted_tag(row.phase, &src),
            row.tag,
            "{}: matrix tag and emitted tag disagree",
            row.phase
        );

        let retained: Vec<PathBuf> = STEMS
            .iter()
            .map(|s| retained_dir().join(format!("{s}.{}.json", row.phase)))
            .filter(|p| p.exists())
            .collect();
        match row.compat {
            Compat::Read(release) => {
                assert_eq!(release, RETAINED, "{}: unknown retained release", row.phase);
                assert_eq!(
                    retained.len(),
                    STEMS.len(),
                    "{}: read-compatible schema is missing retained artifacts",
                    row.phase
                );
            }
            Compat::New => assert!(
                retained.is_empty(),
                "{}: a schema introduced in this release has retained artifacts",
                row.phase
            ),
        }
    }

    // Nothing sits in the retained corpus that the matrix does not describe.
    let expected: Vec<String> = STEMS
        .iter()
        .flat_map(|s| {
            RETAINED_FAMILIES
                .iter()
                .map(move |(family, _)| format!("{s}.{family}.json"))
        })
        .collect();
    let mut found: Vec<String> = fs::read_dir(retained_dir())
        .expect("retained dir")
        .filter_map(Result::ok)
        .filter_map(|e| e.file_name().into_string().ok())
        .collect();
    found.sort_unstable();
    let mut expected = expected;
    expected.sort_unstable();
    assert_eq!(
        found, expected,
        "the retained corpus and the compatibility matrix have drifted apart"
    );
}
