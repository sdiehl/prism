// The `dump hir` phase: a versioned, deterministic checker-fact fixture, the
// stable boundary a future Prism-written typechecker/elaborator is diffed
// against.
//
// Two layers of coverage:
//
// 1. Committed goldens. Each `tests/fixtures/hir/<name>.pr` pairs with a
//    `<name>.hir.json` holding the exact fixture bytes the compiler emits for
//    it, plus one terminating newline (see `golden_document`). The bytes ARE
//    the checker boundary: nothing is normalized, so any
//    change to NodeIds, ordering, whitespace, type text, or evidence text
//    fails the gate and must be reviewed as a boundary change. Regenerate
//    with `PRISM_ACCEPT_HIR_FIXTURES=1`, reviewing the diff like a snapshot;
//    a normal run never writes.
//
// 2. Semantic assertions. Independently of the byte comparison, each golden
//    is re-parsed as JSON and probed for the fact family it exists to pin
//    (field resolution, update paths, dictionary and superclass evidence,
//    numeric lanes, zonked node types, effect rows, handler residuals, unboxed
//    resolution), so
//    an accepted-but-hollow golden cannot silently drop a fact family.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

// The directory of paired source/golden fixtures, relative to the crate root.
const FIXTURE_DIR: &str = "tests/fixtures/hir";
// A fixture source is `<stem>.pr`; its golden is `<stem>.hir.json`.
const SOURCE_EXT: &str = "pr";
const GOLDEN_SUFFIX: &str = ".hir.json";
// Set to regenerate every golden (write-through-temp-then-rename); the
// explicit acceptance switch, named after the tier manifest's
// PRISM_ACCEPT_TIER_MANIFEST.
const HIR_FIXTURE_ACCEPT: &str = "PRISM_ACCEPT_HIR_FIXTURES";
// The schema tag every fixture document must carry. Deliberately re-typed
// here rather than imported from the compiler: the test parses the JSON
// independently, so a schema drift in the emitter cannot re-pin the value it
// is checked against.
const HIR_FIXTURE_SCHEMA: &str = "prism-hir-fixture-v2";
// The dump phase that renders the fixture.
const HIR_PHASE: &str = "hir";

const SRC: &str = "type Point = Point { x: Int, y: Int }\n\
                   fn get_x(p : Point) : Int = p.x\n\
                   fn main() : Unit = println(show(get_x(Point { x = 1, y = 2 })))\n";

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

// The fixture stems, sorted. Rejects a source without a golden and a golden
// without a source: an orphan on either side means a rename or deletion left
// the committed boundary and its input out of sync.
fn fixture_stems(accepting: bool) -> Vec<String> {
    let dir = fixture_dir();
    let mut sources = BTreeSet::new();
    let mut goldens = BTreeSet::new();
    for entry in fs::read_dir(&dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display())) {
        let path = entry.expect("fixture dir entry").path();
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .expect("fixture file name");
        if let Some(stem) = name.strip_suffix(GOLDEN_SUFFIX) {
            goldens.insert(stem.to_string());
        } else if let Some(stem) = name.strip_suffix(&format!(".{SOURCE_EXT}")) {
            sources.insert(stem.to_string());
        }
    }
    assert!(!sources.is_empty(), "no fixtures in {}", dir.display());
    let orphaned: Vec<_> = goldens.difference(&sources).collect();
    assert!(
        orphaned.is_empty(),
        "goldens without a source (delete or restore the .pr): {orphaned:?}"
    );
    // When accepting, a source without a golden is the expected first run.
    if !accepting {
        let missing: Vec<_> = sources.difference(&goldens).collect();
        assert!(
            missing.is_empty(),
            "sources without a golden (run with {HIR_FIXTURE_ACCEPT}=1 to generate): {missing:?}"
        );
    }
    sources.into_iter().collect()
}

// The committed golden document: the dump's bytes plus exactly one
// terminating newline. The repository's end-of-file hook requires every text
// file to end in a newline, so the terminator is part of the file format;
// the comparison is still exact bytes with no other normalization.
fn golden_document(dump: &str) -> String {
    format!("{dump}\n")
}

// Write a golden atomically: through a temporary sibling, then rename, so an
// interrupted acceptance never leaves a truncated golden behind.
fn write_golden(path: &Path, bytes: &str) {
    let tmp = path.with_extension("tmp");
    fs::write(&tmp, bytes).unwrap_or_else(|e| panic!("write {}: {e}", tmp.display()));
    fs::rename(&tmp, path).unwrap_or_else(|e| panic!("rename to {}: {e}", path.display()));
}

// Every node object in the fixture, in the document's own (NodeId) order.
fn nodes(doc: &Value) -> Vec<&Value> {
    doc["nodes"]
        .as_object()
        .expect("nodes object")
        .values()
        .collect()
}

// The `res` facts of a given kind.
fn res_of_kind<'a>(doc: &'a Value, kind: &str) -> Vec<&'a Value> {
    nodes(doc)
        .into_iter()
        .filter_map(|n| n.get("res"))
        .filter(|r| r["kind"] == kind)
        .collect()
}

// All evidence strings in the document, flattened.
fn evidence_strings(doc: &Value) -> Vec<String> {
    nodes(doc)
        .into_iter()
        .filter_map(|n| n.get("evidence"))
        .flat_map(|e| e.as_array().expect("evidence array").iter())
        .map(|d| d.as_str().expect("evidence string").to_string())
        .collect()
}

// All recorded numeric lanes in the document.
fn lanes(doc: &Value) -> Vec<String> {
    nodes(doc)
        .into_iter()
        .filter_map(|n| n.get("lane"))
        .map(|l| l.as_str().expect("lane string").to_string())
        .collect()
}

// The declaration object for `name`.
fn decl<'a>(doc: &'a Value, name: &str) -> &'a Value {
    doc["decls"]
        .as_array()
        .expect("decls array")
        .iter()
        .find(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no decl named {name}"))
}

// The per-fixture semantic probes: each golden must still carry the fact
// family it exists to pin. Byte equality alone would also pass on a hollow
// document accepted by mistake; these keep the families honest.
fn assert_fixture_facts(stem: &str, doc: &Value) {
    match stem {
        "field" => {
            let fields = res_of_kind(doc, "field");
            assert!(
                fields
                    .iter()
                    .any(|r| r["ctor"] == "Point" && r["index"] == 0 && r["arity"] == 2),
                "field: expected the Point.x resolution"
            );
            assert!(
                fields
                    .iter()
                    .any(|r| r["ctor"] == "Point" && r["index"] == 1 && r["arity"] == 2),
                "field: expected the Point.y resolution"
            );
            // Zonked node types are recorded alongside resolutions.
            assert!(
                nodes(doc).iter().any(|n| n["ty"] == "Int"),
                "field: expected a zonked Int node type"
            );
            assert_eq!(decl(doc, "get_x")["scheme"], "(Point) -> Int");
        }
        "update_paths" => {
            let paths = res_of_kind(doc, "paths");
            assert!(!paths.is_empty(), "update_paths: expected a paths fact");
            let chains = paths[0]["chains"].as_array().expect("chains array");
            // Two update paths: `pos.x` (a two-step chain through Player then
            // Vec2) and `hp` (a one-step chain).
            assert_eq!(chains.len(), 2, "expected one chain per update path");
            let deep = chains
                .iter()
                .find(|c| c.as_array().expect("chain").len() == 2)
                .expect("update_paths: expected the two-step pos.x chain");
            assert_eq!(deep[0]["ctor"], "Player");
            assert_eq!(deep[1]["ctor"], "Vec2");
        }
        "evidence" => {
            let dicts = evidence_strings(doc);
            assert!(
                dicts.iter().any(|d| d.contains("Super(")),
                "evidence: expected superclass evidence, got {dicts:?}"
            );
            assert!(
                dicts.iter().any(|d| d.contains("Param(")),
                "evidence: expected constraint-parameter evidence, got {dicts:?}"
            );
            assert!(
                dicts.iter().any(|d| d.contains("Global(")),
                "evidence: expected a global instance dictionary, got {dicts:?}"
            );
        }
        "numeric_lanes" => {
            // The default Int lane records nothing; the fixed lanes are the
            // fact. Each annotated position must have pinned its literal.
            let lanes = lanes(doc);
            for want in ["I64", "U64", "Float"] {
                assert!(
                    lanes.iter().any(|l| l == want),
                    "numeric_lanes: expected a {want} lane, got {lanes:?}"
                );
            }
        }
        "polymorphic_effects" => {
            let count = decl(doc, "count");
            let effects: Vec<_> = count["effects"]
                .as_array()
                .expect("effects array")
                .iter()
                .map(|e| e.as_str().expect("effect name"))
                .collect();
            assert_eq!(effects, ["Tick"], "count's declared effect row");
            // The row-polymorphic scheme keeps both the effect and its
            // quantified row tail.
            let scheme = decl(doc, "twice")["scheme"].as_str().expect("scheme");
            assert!(
                scheme.contains("Tick") && scheme.contains("forall"),
                "polymorphic_effects: twice's scheme keeps Tick and its row tail: {scheme}"
            );
            // main handles the effect away entirely.
            let main_effects = decl(doc, "main")["effects"]
                .as_array()
                .expect("effects array");
            assert!(
                main_effects.is_empty(),
                "polymorphic_effects: main's row is discharged, got {main_effects:?}"
            );
        }
        "handler_residual" => {
            let residuals: Vec<_> = nodes(doc)
                .into_iter()
                .filter_map(|node| node.get("handler_residual"))
                .collect();
            assert_eq!(residuals.len(), 1, "one checked handler residual fact");
            let residual = residuals[0];
            assert_eq!(residual["forwarded_operations"], serde_json::json!(["two"]));
            assert_eq!(residual["forwarded_effects"], serde_json::json!([]));
            assert_eq!(
                residual["residual_operations"],
                serde_json::json!(["three", "two"])
            );
            assert_eq!(residual["residual_effects"], serde_json::json!([]));
            assert_eq!(residual["open_row"], false);
        }
        "handler_residual_open" => {
            let residuals: Vec<_> = nodes(doc)
                .into_iter()
                .filter_map(|node| node.get("handler_residual"))
                .collect();
            assert_eq!(residuals.len(), 1, "one checked open handler residual fact");
            let residual = residuals[0];
            assert_eq!(residual["forwarded_operations"], serde_json::json!([]));
            assert_eq!(residual["forwarded_effects"], serde_json::json!(["Wrap"]));
            assert_eq!(residual["residual_operations"], serde_json::json!([]));
            assert_eq!(
                residual["residual_effects"],
                serde_json::json!(["Out", "Wrap"])
            );
            assert_eq!(residual["open_row"], true);
        }
        "unboxed_fields" => {
            let unboxed = res_of_kind(doc, "unboxed");
            assert!(
                unboxed.iter().any(|r| r["index"] == 0 && r["arity"] == 2),
                "unboxed_fields: expected the .#x projection"
            );
            assert!(
                unboxed.iter().any(|r| r["index"] == 1 && r["arity"] == 2),
                "unboxed_fields: expected the .#y projection"
            );
        }
        other => panic!("fixture {other} has no semantic assertions; add them here"),
    }
}

// The golden gate: every paired fixture dumps deterministically, matches its
// committed bytes exactly, parses as versioned JSON, and still carries its
// fact family. Under the acceptance switch it rewrites the goldens instead of
// comparing.
#[test]
fn hir_fixture_goldens_hold() {
    let accepting = env::var_os(HIR_FIXTURE_ACCEPT).is_some();
    let dir = fixture_dir();
    for stem in fixture_stems(accepting) {
        let src_path = dir.join(format!("{stem}.{SOURCE_EXT}"));
        let golden_path = dir.join(format!("{stem}{GOLDEN_SUFFIX}"));
        let src = fs::read_to_string(&src_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", src_path.display()));

        let out = prism::dump(HIR_PHASE, &src).unwrap_or_else(|e| panic!("{stem}: hir dump: {e}"));
        let again =
            prism::dump(HIR_PHASE, &src).unwrap_or_else(|e| panic!("{stem}: hir dump: {e}"));
        assert_eq!(
            out, again,
            "{stem}: hir fixture must be byte-identical across runs"
        );

        let document = golden_document(&out);
        if accepting {
            write_golden(&golden_path, &document);
            eprintln!("accepted {}", golden_path.display());
        } else {
            let golden = fs::read_to_string(&golden_path)
                .unwrap_or_else(|e| panic!("read {}: {e}", golden_path.display()));
            assert!(
                document == golden,
                "{stem}: hir fixture bytes diverge from the committed golden \
                 {GOLDEN_SUFFIX} (review as a checker-boundary change; regenerate \
                 with {HIR_FIXTURE_ACCEPT}=1)"
            );
        }

        // Independent parse: the document is valid JSON under the pinned
        // schema tag, and its fact family is present.
        let doc: Value = serde_json::from_str(&out).unwrap_or_else(|e| panic!("{stem}: JSON: {e}"));
        assert_eq!(doc["schema"], HIR_FIXTURE_SCHEMA, "{stem}: schema tag");
        assert_fixture_facts(&stem, &doc);
    }
}

#[test]
fn hir_fixture_carries_schema_and_facts() {
    let out = prism::dump(HIR_PHASE, &prism::with_prelude(SRC)).expect("hir dump");
    let doc: Value = serde_json::from_str(&out).expect("valid JSON");

    assert_eq!(doc["schema"], HIR_FIXTURE_SCHEMA);

    // The user's own declarations survive into the fixture with their schemes.
    let decls = doc["decls"].as_array().expect("decls array");
    assert!(decls
        .iter()
        .any(|d| d["name"] == "get_x" && d["scheme"] == "(Point) -> Int"));

    // The field access `p.x` recorded a resolution the fixture serves: the
    // `Point` constructor, field index 0, arity 2.
    let has_field = doc["nodes"]
        .as_object()
        .expect("nodes object")
        .values()
        .filter_map(|n| n.get("res"))
        .any(|r| {
            r["kind"] == "field" && r["ctor"] == "Point" && r["index"] == 0 && r["arity"] == 2
        });
    assert!(has_field, "expected the Point.x field resolution fact");
}

#[test]
fn hir_fixture_is_deterministic() {
    let src = prism::with_prelude(SRC);
    let a = prism::dump(HIR_PHASE, &src).expect("hir dump");
    let b = prism::dump(HIR_PHASE, &src).expect("hir dump");
    assert_eq!(a, b, "hir fixture must be byte-identical across runs");
}
