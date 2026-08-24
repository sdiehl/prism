// Released-format compatibility for the syntax schemas.
//
// A published artifact outlives the compiler that wrote it, so the promise a
// reader makes about an older document has to be written down and gated, not
// assumed. `tests/fixtures/syntax/released/<version>/` holds artifacts exactly
// as an earlier release cut them, byte for byte, and is never regenerated: the
// current reader must decode them, re-encode them to the same bytes, and agree
// with the current exporter on everything except the compiler stamp they carry.
//
// That last agreement is not the same statement for every schema. The three
// source-local seams are a function of the source their document carries, so the
// current exporter reproduces them byte for byte. The resolved seam is not: it
// numbers nodes with a counter that spans the prelude and every imported module,
// so an unrelated library edit renumbers a document whose source did not change.
// What it promises instead is the same document with that numbering erased,
// which is still the statement worth gating, since a shape change without a
// schema bump shows up there either way.
//
// The refusal side matters as much. A document naming a different schema
// version is refused whether that version is older or newer than the current
// one. An old artifact is never read under the current tag, and a
// newer one is never guessed at. The compiler version inside the envelope is
// data, not a gate: it records who wrote the document, and a reader that
// demanded its own version would make every artifact expire on release day.

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

use prism::{default_roots, dump_on, interpret_io_on_with_args, with_prelude, Config, Error};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const RELEASED_DIR: &str = "released";
const HARNESS: &str = "roundtrip.pr";

// The releases whose artifacts are retained, oldest first. A schema is retained
// from the release its matrix row names onward, so this order is what decides
// which directory carries which families.
const RETAINED: &[&str] = &["0.14.0", "0.15.0"];

// The retained corpus: representative sources across declaration forms, string
// interpolation, stable families with migrations, and type syntax.
const STEMS: &[&str] = &["decls", "interp", "stable", "types"];

// The resolved seam needs a program the resolver accepts, and `types.pr` is a
// type-syntax snippet naming types no module defines. It has a token, surface
// and diagnostic form, but no resolved one.
const RESOLVED_STEMS: &[&str] = &["decls", "interp", "stable"];

// The holes a cross-release comparison leaves in a document, and the key whose
// value the second of them replaces.
const VERSION_HOLE: &str = "<version>";
const NODE_ID_KEY: &str = "\"id\": ";
const NODE_ID_HOLE: &str = "<node>";

// How much of a retained document the current exporter reproduces from the
// source that document carries.
#[derive(Clone, Copy)]
enum Export {
    // The whole envelope, apart from the compiler stamp.
    Bytes,
    // The envelope with the node numbering erased as well, because that
    // numbering is a property of the compilation and not of the source.
    Shape,
}

struct SchemaRow {
    // The `dump` phase that emits the artifact.
    phase: &'static str,
    // The schema tag, re-typed here independently of the compiler so an
    // emitter drift cannot re-pin the value it is checked against.
    tag: &'static str,
    // The harness mode that decodes and re-encodes this family.
    mode: &'static str,
    // The stems retained for this family.
    stems: &'static [&'static str],
    // The oldest retained release carrying the tag: its documents are still
    // read unchanged, and every retained release from that one onward holds the
    // evidence. A schema first written by the release under development has no
    // earlier document to read and no row here until its release is cut.
    //
    // The policy allows two states no schema is in yet. A shape change that
    // leaves old documents interpretable bumps the tag and gains an explicit
    // upgrade from the old one; a change that cannot be upgraded rejects the old
    // tag outright. Neither has been needed, because no shipped syntax schema
    // has changed shape.
    since: &'static str,
    export: Export,
}

// A `static` rather than a `const`: the corpus walk below hands out borrows of
// these rows, which a const's per-use temporary could not outlive.
static MATRIX: [SchemaRow; 4] = [
    SchemaRow {
        phase: "syntax-tokens",
        tag: "prism-syntax-tokens-v1",
        mode: "tokens",
        stems: STEMS,
        since: "0.14.0",
        export: Export::Bytes,
    },
    SchemaRow {
        phase: "surface-syntax",
        tag: "prism-surface-syntax-v1",
        mode: "surface",
        stems: STEMS,
        since: "0.14.0",
        export: Export::Bytes,
    },
    SchemaRow {
        phase: "syntax-diagnostics",
        tag: "prism-syntax-diagnostics-v1",
        mode: "diagnostics",
        stems: STEMS,
        since: "0.15.0",
        export: Export::Bytes,
    },
    SchemaRow {
        phase: "resolved-syntax",
        tag: "prism-resolved-syntax-v1",
        mode: "resolved",
        stems: RESOLVED_STEMS,
        since: "0.15.0",
        export: Export::Shape,
    },
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn released_dir(release: &str) -> PathBuf {
    fixture_dir().join(RELEASED_DIR).join(release)
}

fn artifact(release: &str, stem: &str, row: &SchemaRow) -> PathBuf {
    released_dir(release).join(format!("{stem}.{}.json", row.phase))
}

// The retained releases carrying a family: every release from the one its row
// names onward, since a release cuts every schema it can already write.
fn releases_for(row: &SchemaRow) -> &'static [&'static str] {
    let first = RETAINED
        .iter()
        .position(|r| *r == row.since)
        .unwrap_or_else(|| panic!("{}: {} is not a retained release", row.phase, row.since));
    &RETAINED[first..]
}

// Every artifact the matrix claims, as (release, stem, row).
fn retained_artifacts() -> impl Iterator<Item = (&'static str, &'static str, &'static SchemaRow)> {
    MATRIX.iter().flat_map(|row| {
        releases_for(row)
            .iter()
            .flat_map(move |release| row.stems.iter().map(move |stem| (*release, *stem, row)))
    })
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn json(path: &Path) -> Value {
    serde_json::from_str(&read(path)).unwrap_or_else(|e| panic!("{}: JSON: {e}", path.display()))
}

// Replace every node number with a hole. Only `id` carries one, and nothing
// refers to a node by number, so erasing the values leaves every structural
// field of the document still under comparison.
fn erase_node_ids(doc: &str) -> String {
    let mut out = String::with_capacity(doc.len());
    let mut rest = doc;
    while let Some(at) = rest.find(NODE_ID_KEY) {
        let (head, tail) = rest.split_at(at + NODE_ID_KEY.len());
        out.push_str(head);
        let digits = tail.len() - tail.trim_start_matches(|c: char| c.is_ascii_digit()).len();
        if digits > 0 {
            out.push_str(NODE_ID_HOLE);
        }
        rest = &tail[digits..];
    }
    out.push_str(rest);
    out
}

// Erase what a comparison across releases must not depend on: the compiler
// stamp always, and the node numbering for a schema that does not promise it.
fn comparable(doc: &str, version: &str, export: Export) -> String {
    let doc = doc.replace(
        &format!("\"compiler\": \"{version}\""),
        &format!("\"compiler\": \"{VERSION_HOLE}\""),
    );
    match export {
        Export::Bytes => doc,
        Export::Shape => erase_node_ids(&doc),
    }
}

// What the current exporter writes for one source, taken the way the command
// line takes it. The prelude is prepended, because a program that derives an
// instance or names a class does not resolve without it; the exporters rebase
// spans and drop prelude declarations, so the artifact still commits to the
// user's own file and the embedded source can be fed straight back in here.
//
// # Errors
// Propagates a front-end failure so the caller can name the artifact it came
// from.
fn today(phase: &str, source: &str) -> Result<String, Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let full = with_prelude(source);
    dump_on(phase, &full, &default_roots(root), &Config::from_env())
}

// The schema tag a phase actually emits.
fn emitted_tag(phase: &str, src: &str) -> String {
    let out = today(phase, src).unwrap_or_else(|e| panic!("{phase}: dump: {e}"));
    let doc: Value = serde_json::from_str(&out).expect("emitted JSON");
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
    let mut checked = 0;
    for (release, _, row) in retained_artifacts().filter(|(_, s, _)| *s == stem) {
        let path = artifact(release, stem, row);
        let released = read(&path);
        assert_eq!(
            roundtrip(&path, row.mode),
            released,
            "{release}/{stem}.{}: a retained release artifact must re-encode byte-identically",
            row.phase
        );
        checked += 1;
    }
    assert!(checked > 0, "{stem}: nothing retained to read");
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

// Every retained artifact carries the stamp of the release whose directory it
// sits in, so refreshing the corpus with current output cannot masquerade as an
// older-format test.
#[test]
fn retained_artifacts_carry_the_released_stamp() {
    for (release, stem, row) in retained_artifacts() {
        let doc = json(&artifact(release, stem, row));
        assert_eq!(
            doc["compiler"], release,
            "{release}/{stem}.{}: retained artifact is not stamped {release}",
            row.phase
        );
    }
}

// The shape statement: the current exporter reproduces a retained artifact from
// the source it carries, to whatever precision that schema promises. Comparing
// the document rather than a schema tag is what makes the tag's claim honest,
// since an unbumped tag over a drifted shape is precisely the failure this
// catches.
#[test]
fn retained_artifacts_match_todays_export_modulo_stamp() {
    for (release, stem, row) in retained_artifacts() {
        let path = artifact(release, stem, row);
        let released = read(&path);
        let doc = json(&path);
        let source = doc["source"]["text"]
            .as_str()
            .unwrap_or_else(|| panic!("{release}/{stem}.{}: no embedded source", row.phase));

        let exported = today(row.phase, source)
            .unwrap_or_else(|e| panic!("{release}/{stem}.{}: dump: {e}", row.phase));
        let exported = format!("{exported}\n");

        assert_eq!(
            comparable(&exported, env!("CARGO_PKG_VERSION"), row.export),
            comparable(&released, release, row.export),
            "{release}/{stem}.{}: the exported shape drifted without a schema bump",
            row.phase
        );
    }
}

// A schema tag is matched exactly, never ordered. An older tag is not read
// under the current one and a newer tag is not guessed at; both are refused
// with the structured schema error, and the untouched document still decodes so
// the refusal is attributable to the tag alone.
#[test]
fn other_schema_versions_are_refused() {
    let stem = STEMS[0];
    for row in &MATRIX {
        let release = releases_for(row)
            .last()
            .expect("a retained family carries at least one release");
        let path = artifact(release, stem, row);
        let released = read(&path);
        assert!(
            released.contains(row.tag),
            "{release}/{stem}.{}: retained artifact does not carry {}",
            row.phase,
            row.tag
        );

        for other in ["v0", "v2"] {
            let stripped = row
                .tag
                .strip_suffix("v1")
                .unwrap_or_else(|| panic!("{}: schema tag is not version-suffixed", row.tag));
            let retagged = released.replace(row.tag, &format!("{stripped}{other}"));
            let tmp = std::env::temp_dir().join(format!("prism_compat_{}_{other}.json", row.phase));
            fs::write(&tmp, &retagged).expect("write retagged artifact");
            let out = roundtrip(&tmp, row.mode);
            assert!(
                out.starts_with("decode error: $.schema"),
                "{}: a {other} document was not refused on its tag, got: {out}",
                row.phase
            );
        }
    }
}

// The matrix is the record, so it must describe the schemas that exist: every
// row's tag is the one the compiler actually emits, and every row has a retained
// corpus in each release from the one it names onward.
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

        for (release, stem, _) in retained_artifacts().filter(|(.., r)| r.phase == row.phase) {
            let path = artifact(release, stem, row);
            assert!(
                path.exists(),
                "{}: read-compatible schema is missing {}",
                row.phase,
                path.display()
            );
        }
    }

    // Nothing sits in a retained release that the matrix does not describe, and
    // nothing the matrix describes is missing from disk.
    for release in RETAINED {
        let mut expected: Vec<String> = retained_artifacts()
            .filter(|(r, ..)| r == release)
            .map(|(_, stem, row)| format!("{stem}.{}.json", row.phase))
            .collect();
        let mut found: Vec<String> = fs::read_dir(released_dir(release))
            .unwrap_or_else(|e| panic!("{release}: retained dir: {e}"))
            .filter_map(Result::ok)
            .filter_map(|e| e.file_name().into_string().ok())
            .collect();
        expected.sort_unstable();
        found.sort_unstable();
        assert_eq!(
            found, expected,
            "{release}: the retained corpus and the compatibility matrix have drifted apart"
        );
    }
}
