// The rejection seam: `dump tc-rejection`. Every other front-end fixture
// requires the checker to accept, so a Prism-written checker could be diffed
// only on what this compiler admits and never on what it refuses. This seam
// exports the negative half: the resolved tree desugar built before
// typechecking, plus the refusal's stable code, owning phase, and user-relative
// span. Coverage:
//
// 1. Determinism, on both verdicts.
// 2. An accepted program reports `accepted`, carries no error row, and its tree
//    and source are exactly what `resolved-syntax` exports, so the two seams
//    cannot render the same program differently.
// 3. A rejected program reports `rejected` with a type-phase code and a span
//    inside the embedded user source, and still carries the resolved tree.
// 4. A program that fails before a resolved tree exists (a parse error) is
//    refused outright rather than reported as a rejection with no tree.

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

const FIXTURE_DIR: &str = "tests/fixtures/frontend";
const PHASE: &str = "tc-rejection";
// Re-typed independently of the emitter so a schema drift cannot re-pin the
// value it is checked against.
const SCHEMA: &str = "prism-tc-rejection-v1";
const RESOLVED_PHASE: &str = "resolved-syntax";
const ACCEPTED_STEM: &str = "program";
const REJECTED_STEM: &str = "malformed_type";
const UNRESOLVABLE_STEM: &str = "malformed_parse";

fn fixture(stem: &str) -> String {
    let path: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(format!("{stem}.pr"));
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn dump(stem: &str) -> Value {
    let src = fixture(stem);
    let out = prism::dump(PHASE, &src).unwrap_or_else(|e| panic!("{stem}: dump: {e}"));
    let again = prism::dump(PHASE, &src).unwrap_or_else(|e| panic!("{stem}: dump: {e}"));
    assert_eq!(out, again, "{stem}: must be byte-identical across runs");
    let doc: Value = serde_json::from_str(&out).unwrap_or_else(|e| panic!("{stem}: JSON: {e}"));
    assert_eq!(doc["schema"], SCHEMA, "{stem}: schema tag");
    assert_eq!(
        doc["compiler"],
        env!("CARGO_PKG_VERSION"),
        "{stem}: version"
    );
    doc
}

// An accepted program: the verdict is the only thing this seam adds, and the
// tree it reports is the one `resolved-syntax` already publishes.
#[test]
fn accepted_program_matches_the_resolved_seam() {
    let doc = dump(ACCEPTED_STEM);
    assert_eq!(doc["status"], "accepted");
    assert!(doc.get("error").is_none(), "accepted: no error row");

    let src = fixture(ACCEPTED_STEM);
    let resolved: Value = serde_json::from_str(
        &prism::dump(RESOLVED_PHASE, &src).expect("resolved-syntax dump of an accepted program"),
    )
    .expect("resolved-syntax is JSON");
    assert_eq!(doc["source"], resolved["source"], "embedded source");
    assert_eq!(doc["functions"], resolved["functions"], "resolved tree");
}

// A rejected program: the refusal is reported as data, and the resolved tree
// desugar built before the checker ran survives alongside it.
#[test]
fn rejected_program_reports_the_refusal_and_keeps_its_tree() {
    let doc = dump(REJECTED_STEM);
    assert_eq!(doc["status"], "rejected");

    let error = &doc["error"];
    assert_eq!(error["phase"], "type", "the checker owns this refusal");
    let code = error["code"].as_str().expect("a stable code");
    assert!(
        code.starts_with('E') && code[1..].chars().all(|c| c.is_ascii_digit()),
        "malformed code {code}"
    );

    // The span addresses the embedded source, not the prelude-prefixed one.
    let text = doc["source"]["text"].as_str().expect("embedded source");
    let span = error["span"].as_array().expect("a primary span");
    let (start, end) = (
        span[0].as_u64().expect("span start"),
        span[1].as_u64().expect("span end"),
    );
    let len = u64::try_from(text.len()).expect("source length");
    assert!(start < end && end <= len, "span [{start}, {end}]");

    assert!(
        !doc["functions"].as_array().expect("functions").is_empty(),
        "the resolved tree of a rejected program"
    );
}

// A refusal that lands before resolution has no tree to report against, so the
// seam fails rather than claiming a rejection with an empty program.
#[test]
fn unresolvable_program_is_refused_outright() {
    assert!(prism::dump(PHASE, &fixture(UNRESOLVABLE_STEM)).is_err());
}
