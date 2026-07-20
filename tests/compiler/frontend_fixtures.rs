// The front-end fixture seams: `dump tc-input`, `dump tc-facts`, and
// `dump elab-input`. Each is the semantic, versioned, deterministic boundary a
// Prism-written typechecker or elaborator starts from, mirroring the existing
// `core-json`/`core-hash`/`hir` fixtures. Coverage:
//
// 1. Determinism. Every phase dumps byte-identically across two runs (the same
//    property makes the export stable across checkout roots: spans are emitted
//    relative to the user source and no filesystem path enters the bytes).
// 2. Committed goldens. The positive source pairs with one golden per phase
//    holding the exact bytes; any drift is a reviewed boundary change. Regenerate
//    with PRISM_ACCEPT_FRONTEND_FIXTURES=1.
// 3. Positive version compatibility. Each golden carries its schema tag and the
//    compiler version, checked against independently re-typed constants.
// 4. Negative version compatibility. A committed mismatch fixture per schema is
//    well-formed JSON carrying a wrong tag that a versioned reader must reject.
// 5. Malformed input. A parse error and a type error are refused by every phase
//    rather than yielding a partial fixture.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

const FIXTURE_DIR: &str = "tests/fixtures/frontend";
const ACCEPT: &str = "PRISM_ACCEPT_FRONTEND_FIXTURES";
const POSITIVE_STEM: &str = "program";

// The three seams and their schema tags, re-typed independently of the compiler
// so an emitter schema drift cannot re-pin the value it is checked against.
const PHASES: [(&str, &str); 3] = [
    ("tc-input", "prism-tc-input-v1"),
    ("tc-facts", "prism-tc-facts-v1"),
    ("elab-input", "prism-elab-input-v1"),
];

// Sources every seam must refuse.
const MALFORMED: [&str; 2] = ["malformed_parse", "malformed_type"];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
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

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

// The golden gate: the positive source dumps deterministically through every seam,
// matches its committed bytes, parses as versioned JSON, and still carries the
// facts each seam exists to pin. Under the acceptance switch it rewrites goldens.
#[test]
fn frontend_seam_goldens_hold() {
    let accepting = env::var_os(ACCEPT).is_some();
    let dir = fixture_dir();
    let src = read(&dir.join(format!("{POSITIVE_STEM}.pr")));
    for (phase, schema) in PHASES {
        let out = prism::dump(phase, &src).unwrap_or_else(|e| panic!("{phase}: dump: {e}"));
        let again = prism::dump(phase, &src).unwrap_or_else(|e| panic!("{phase}: dump: {e}"));
        assert_eq!(
            out, again,
            "{phase}: fixture must be byte-identical across runs"
        );

        let golden_path = dir.join(format!("{POSITIVE_STEM}.{phase}.json"));
        let document = golden_document(&out);
        if accepting {
            write_golden(&golden_path, &document);
            eprintln!("accepted {}", golden_path.display());
        } else {
            let golden = read(&golden_path);
            assert!(
                document == golden,
                "{phase}: fixture bytes diverge from the committed golden \
                 (review as a front-end boundary change; regenerate with {ACCEPT}=1)"
            );
        }

        let doc: Value =
            serde_json::from_str(&out).unwrap_or_else(|e| panic!("{phase}: JSON: {e}"));
        assert_eq!(
            doc["schema"], schema,
            "{phase}: schema tag (positive version compatibility)"
        );
        assert_eq!(
            doc["compiler"],
            env!("CARGO_PKG_VERSION"),
            "{phase}: compiler version"
        );
        if !accepting {
            assert_phase_facts(phase, &doc);
        }
    }
}

// Per-seam semantic probes: each golden must still carry the fact family it exists
// to pin, so an accepted-but-hollow golden cannot silently drop a family.
fn assert_phase_facts(phase: &str, doc: &Value) {
    match phase {
        "tc-input" => assert_tc_input(doc),
        "tc-facts" => assert_tc_facts(doc),
        "elab-input" => {
            // Composes both halves under one envelope.
            assert_tc_input(&doc["input"]);
            assert_tc_facts(&doc["facts"]);
        }
        other => panic!("unknown seam {other}"),
    }
}

fn array<'a>(doc: &'a Value, key: &str) -> &'a Vec<Value> {
    doc[key]
        .as_array()
        .unwrap_or_else(|| panic!("expected array at {key}"))
}

// The resolved-declaration interface a checker reads.
fn assert_tc_input(doc: &Value) {
    // The record datatype and its constructor layout.
    let point = array(doc, "types")
        .iter()
        .find(|t| t["name"] == "Point")
        .expect("tc-input: Point datatype");
    let ctor = &array(point, "ctors")[0];
    assert_eq!(ctor["fields"], serde_json::json!(["x", "y"]));
    assert_eq!(ctor["args"], serde_json::json!(["Int", "Int"]));

    // The effect and its operation grade.
    let tick = array(doc, "effects")
        .iter()
        .find(|e| e["name"] == "Tick")
        .expect("tc-input: Tick effect");
    assert_eq!(array(tick, "ops")[0]["name"], "tick");
    assert_eq!(array(tick, "ops")[0]["grade"], "many");

    // The class and its instance.
    assert!(
        array(doc, "classes").iter().any(|c| c["name"] == "Same"),
        "tc-input: Same class"
    );
    assert!(
        array(doc, "instances")
            .iter()
            .any(|i| i["class"] == "Same" && i["head"] == "Int"),
        "tc-input: Same(Int) instance"
    );

    // The constrained function carries its constraint and a body NodeId that ties
    // it to the tc-facts node table.
    let alike = array(doc, "functions")
        .iter()
        .find(|f| f["name"] == "alike")
        .expect("tc-input: alike function");
    assert_eq!(alike["constraints"], serde_json::json!(["Same"]));
    assert!(alike["body"].is_u64(), "tc-input: alike body NodeId");
}

// The checker facts a Prism typechecker is diffed against.
fn assert_tc_facts(doc: &Value) {
    let decls = array(doc, "decls");
    assert!(
        decls
            .iter()
            .any(|d| d["name"] == "getx" && d["scheme"] == "(Point) -> Int"),
        "tc-facts: getx scheme"
    );
    // The effectful declaration keeps its row.
    assert!(
        decls
            .iter()
            .any(|d| d["name"] == "ticked" && d["effects"] == serde_json::json!(["Tick"])),
        "tc-facts: ticked effect row"
    );
    let nodes = doc["nodes"].as_object().expect("tc-facts: nodes object");
    // A field access resolved to the Point constructor.
    assert!(
        nodes
            .values()
            .filter_map(|n| n.get("res"))
            .any(|r| r["kind"] == "field" && r["ctor"] == "Point"),
        "tc-facts: Point field resolution"
    );
    // Dictionary evidence appears: a global instance dictionary and a
    // constraint-parameter dictionary.
    let evidence: Vec<String> = nodes
        .values()
        .filter_map(|n| n.get("evidence"))
        .flat_map(|e| e.as_array().expect("evidence array"))
        .map(|d| d.as_str().expect("evidence string").to_string())
        .collect();
    assert!(
        evidence.iter().any(|d| d.contains("Global(")),
        "tc-facts: a global instance dictionary, got {evidence:?}"
    );
    assert!(
        evidence.iter().any(|d| d.contains("Param(")),
        "tc-facts: a constraint-parameter dictionary, got {evidence:?}"
    );
}

// Every seam refuses malformed source rather than emitting a partial fixture.
#[test]
fn frontend_seam_refuses_malformed() {
    let dir = fixture_dir();
    for stem in MALFORMED {
        let src = read(&dir.join(format!("{stem}.pr")));
        for (phase, _) in PHASES {
            assert!(
                prism::dump(phase, &src).is_err(),
                "{phase}: must refuse malformed {stem}"
            );
        }
    }
}

// Negative version compatibility: each mismatch fixture is well-formed JSON but
// names a wrong schema tag, so a reader keyed on the versioned tag rejects it
// while still recognizing it as a (wrongly versioned) export.
#[test]
fn frontend_seam_rejects_version_mismatch() {
    let dir = fixture_dir();
    for (phase, schema) in PHASES {
        let path = dir.join(format!("{POSITIVE_STEM}.{phase}.mismatch.json"));
        let doc: Value = serde_json::from_str(&read(&path))
            .unwrap_or_else(|e| panic!("{phase} mismatch: JSON: {e}"));
        assert!(
            doc["schema"].is_string(),
            "{phase}: mismatch fixture still names a schema"
        );
        assert_ne!(
            doc["schema"], schema,
            "{phase}: mismatch fixture must not carry the current tag"
        );
    }
}
