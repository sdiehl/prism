// The resolved-syntax round trip, traversal, and checker-join gate: every
// committed `prism-resolved-syntax-v1` golden decodes into the typed
// `Syntax.Resolved` vocabulary, re-encodes byte-identically, and its function
// bodies are walked by the Prism-side uniplate `rnode_universe` to exactly the
// node set an independent JSON walk reaches. This is the "Prism reads Prism"
// acceptance gate for the resolved seam: the compiler's whole-program export
// and the standard library's decoder plus traversal agree on every byte and
// every node, and a wrong schema tag or an internally inconsistent document (a
// duplicated node id, a span past the source) is refused with a structured
// error rather than a partial document or a crash.
//
// The round-trip and traversal oracles run the committed harness
// `tests/fixtures/syntax/roundtrip.pr` through the interpreter, reading only the
// artifact bytes: no source file or compiler state is consulted, so those gates
// are a pure function of the golden and stay independent of the live exporter.
// They are decoder oracles, and a golden serves them for as long as its schema
// holds.
//
// The join gate is live on both sides. It dumps this compiler's resolved tree
// and its `prism-tc-facts-v1` fact table for the same stem, and checks that
// every leaf of the resolved body carries a fact under the same NodeId. That
// table is sparse (only a node the checker resolved, typed, or gave evidence to
// appears, so an interior let or match may be absent), but a leaf is always a
// settled reference or literal, so the leaf join is total.
//
// Both sides are live on purpose. Joining a committed tree against a live table
// tests something weaker than it appears to: the exported ids of a fixture's
// own functions are assigned after the prelude's, so any change to the standard
// library shifts them all, and because the fact table is dense a shifted leaf
// usually still lands on some unrelated node's fact. The gate then passes by
// coincidence and reports agreement between two seams that have drifted apart.
// The stale goldens this replaced had drifted by thirteen ids and still passed,
// until a shift happened to land twelve leaves on the table's sparse gaps.
// Live-versus-live cannot pass that way, and it stays true across a stdlib edit
// without a reseat, since the question is whether the two exporters agree now.
//
// What the goldens still owe is their shape, checked below with the build stamp
// and the node numbering punched out, since neither belongs to the document.
// Reseat with `PRISM_ACCEPT_RESOLVED_FIXTURES=1`.

use std::collections::HashSet;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, dump_at, interpret_io_on_with_args, with_prelude, Config};
use serde_json::Value;

use super::fixture_stems;

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "roundtrip.pr";
const ARTIFACT: &str = "resolved-syntax";
// The checker's fact-table seam the resolved leaves are joined against.
const FACTS_PHASE: &str = "tc-facts";
// Rewrites the committed goldens from the live exporter, for a reviewed
// boundary change or a release version bump.
const ACCEPT: &str = "PRISM_ACCEPT_RESOLVED_FIXTURES";

// Every resolved-syntax corpus stem, kept sorted. Each is a well-typed,
// self-contained fixture whose whole-program export is exactly its own
// functions, so the join against the live fact table is over just those nodes.
const STEMS: [&str; 5] = ["classes", "contracts", "decls", "patterns", "stable"];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

// Run the harness program over one artifact file in one mode, capturing stdout.
fn harness(artifact: &Path, mode: &str) -> String {
    let dir = fixture_dir();
    let src = fs::read_to_string(dir.join(HARNESS)).expect("harness source");
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

fn golden_path(stem: &str) -> PathBuf {
    fixture_dir().join(format!("{stem}.{ARTIFACT}.json"))
}

fn read_golden(stem: &str) -> String {
    fs::read_to_string(golden_path(stem))
        .unwrap_or_else(|e| panic!("{stem}.{ARTIFACT}: missing golden: {e}"))
}

// Every node id in a body tree, pre-order, as the exporter emits them.
fn collect_ids(node: &Value, out: &mut Vec<i64>) {
    out.push(node["id"].as_i64().expect("node id"));
    if let Some(children) = node["children"].as_array() {
        for c in children {
            collect_ids(c, out);
        }
    }
}

// The `resolved-nodes` header plus one id per line, ascending, as the harness
// prints it: the independent oracle the Prism-side traversal is diffed against.
fn expected_node_dump(golden: &str) -> String {
    let doc: Value = serde_json::from_str(golden).expect("golden JSON");
    let mut ids = Vec::new();
    for f in doc["functions"].as_array().expect("functions") {
        collect_ids(&f["body"], &mut ids);
    }
    ids.sort_unstable();
    let mut out = format!("count {}\n", ids.len());
    for id in ids {
        let _ = writeln!(out, "{id}");
    }
    out
}

// Decode then re-encode reproduces the exact golden bytes.
fn assert_stem_roundtrips(stem: &str) {
    let golden = read_golden(stem);
    let out = harness(&golden_path(stem), "resolved");
    assert_eq!(
        out, golden,
        "{stem}.{ARTIFACT}: decode + re-encode must reproduce the artifact bytes"
    );
}

// The Prism `rnode_universe` walk reaches exactly the golden's node id multiset.
fn assert_stem_traversal(stem: &str) {
    let golden = read_golden(stem);
    let out = harness(&golden_path(stem), "resolved-nodes");
    assert_eq!(
        out,
        expected_node_dump(&golden),
        "{stem}.{ARTIFACT}: rnode_universe must reach every exported node exactly once"
    );
}

// Every leaf id (a node the exporter emits with no children) of the golden's
// function bodies: the references and literals the checker resolves and types.
fn leaf_ids(node: &Value, out: &mut Vec<i64>) {
    match node["children"].as_array() {
        Some(children) if !children.is_empty() => {
            for c in children {
                leaf_ids(c, out);
            }
        }
        _ => out.push(node["id"].as_i64().expect("node id")),
    }
}

// One phase dumped for a stem by this compiler: the bare stem source under the
// prelude, resolved against the fixture roots. Both sides of the join are
// produced this way, from the same source through the same roots, so the two
// seams' NodeId identities are comparable by construction.
fn dump_stem(stem: &str, phase: &str) -> String {
    let src = fs::read_to_string(fixture_dir().join(format!("{stem}.pr")))
        .unwrap_or_else(|e| panic!("{stem}: source: {e}"));
    dump_at(phase, &with_prelude(&src), &fixture_dir())
        .unwrap_or_else(|e| panic!("{stem}.{phase}: dump: {e}"))
}

fn dump_stem_json(stem: &str, phase: &str) -> Value {
    serde_json::from_str(&dump_stem(stem, phase))
        .unwrap_or_else(|e| panic!("{stem}.{phase}: JSON: {e}"))
}

// The set of NodeId keys the live checker records a fact under for one stem.
fn tc_facts_ids(stem: &str) -> HashSet<i64> {
    dump_stem_json(stem, FACTS_PHASE)["nodes"]
        .as_object()
        .unwrap_or_else(|| panic!("{stem}.{FACTS_PHASE}: nodes object"))
        .keys()
        .map(|k| k.parse::<i64>().expect("decimal NodeId key"))
        .collect()
}

// The cross-seam join: every leaf of this compiler's resolved body carries a
// fact in its own checker's table under the same NodeId, so a Prism consumer
// can hang the type and resolution of each reference off the traversed tree by
// id. Both dumps are live; see the header for why a committed tree here would
// make the gate pass on coincidence.
fn assert_stem_join(stem: &str) {
    let doc = dump_stem_json(stem, ARTIFACT);
    let mut leaves = Vec::new();
    for f in doc["functions"].as_array().expect("functions") {
        leaf_ids(&f["body"], &mut leaves);
    }
    assert!(!leaves.is_empty(), "{stem}: golden bodies have no leaves");
    let facts = tc_facts_ids(stem);
    for id in leaves {
        assert!(
            facts.contains(&id),
            "{stem}: resolved leaf {id} has no {FACTS_PHASE} entry; the seams disagree on node identity"
        );
    }
}

macro_rules! stem_tests {
    ($($rt:ident, $tv:ident, $jn:ident => $stem:literal),+ $(,)?) => {
        $(
            #[test]
            fn $rt() { assert_stem_roundtrips($stem); }
            #[test]
            fn $tv() { assert_stem_traversal($stem); }
            #[test]
            fn $jn() { assert_stem_join($stem); }
        )+
    };
}

stem_tests! {
    resolved_roundtrip_classes, resolved_traversal_classes, resolved_join_classes => "classes",
    resolved_roundtrip_contracts, resolved_traversal_contracts, resolved_join_contracts => "contracts",
    resolved_roundtrip_decls, resolved_traversal_decls, resolved_join_decls => "decls",
    resolved_roundtrip_patterns, resolved_traversal_patterns, resolved_join_patterns => "patterns",
    resolved_roundtrip_stable, resolved_traversal_stable, resolved_join_stable => "stable",
}

// Every positive golden is a shape this compiler still writes. The round trip
// and the traversal read the golden and never the compiler, so without this a
// golden outlives its exporter and keeps proving the decoder handles bytes
// nothing emits any more, which is exactly when a silently added field would go
// unnoticed. Regenerate with the accept env, reviewing the diff like a snapshot.
#[test]
fn resolved_goldens_match_this_compiler() {
    let accept = env::var(ACCEPT).is_ok();
    let mut stale = Vec::new();
    for stem in STEMS {
        // Only the stamp comes out of the bytes that get written: a committed
        // golden keeps its node numbering, because the decoder oracles
        // re-encode it byte for byte and walk the ids it carries. The
        // comparison below erases that numbering as well, through
        // `comparable`, since the numbering is not the document's to own.
        let dump = format!("{}\n", super::seam::json(&dump_stem(stem, ARTIFACT)));
        if accept {
            fs::write(golden_path(stem), &dump).expect("rewrite golden");
            continue;
        }
        if comparable(&read_golden(stem)) != comparable(&dump) {
            stale.push(stem);
        }
    }
    assert!(
        stale.is_empty(),
        "resolved-syntax goldens no longer match this compiler's export \
         (review as a resolved-seam change; regenerate with {ACCEPT}=1): {}",
        stale.join(", ")
    );
}

// The shape a golden owes the live exporter: every structural field, with the
// build stamp and the node numbering punched out. Both belong to the
// compilation rather than the document, and both move for reasons the document
// cannot see (a release cut, an edit anywhere in the standard library).
fn comparable(doc: &str) -> String {
    super::seam::erase_node_ids(&super::seam::json(doc))
}

// The static stem list matches the fixture directory exactly, so adding a
// corpus file without extending the gate is a failure, not a silent skip.
#[test]
fn resolved_covers_every_stem() {
    let suffix = format!(".{ARTIFACT}.json");
    let found = fixture_stems(&fixture_dir(), &suffix, "mismatch");
    assert_eq!(
        found, STEMS,
        "resolved-syntax fixture stems and the static list have drifted apart"
    );
}

// The committed wrong-tag fixture is refused by the versioned Prism reader with
// the structured schema error, not decoded into a partial document.
#[test]
fn resolved_rejects_wrong_schema() {
    let out = harness(
        &fixture_dir().join(format!("mismatch.{ARTIFACT}.json")),
        "resolved",
    );
    assert!(
        out.starts_with("decode error: $.schema"),
        "expected the schema refusal, got: {out}"
    );
}

// Hostile bytes fail closed: malformed JSON and a well-formed but wrong-shaped
// document each surface a structured decode error, never a panic.
#[test]
fn resolved_refuses_hostile_input() {
    let dir = std::env::temp_dir();
    for (name, bytes) in [
        ("prism_resolved_hostile_bad.json", "not json at all {"),
        ("prism_resolved_hostile_empty.json", "{}"),
    ] {
        let path = dir.join(name);
        fs::write(&path, bytes).expect("write hostile fixture");
        let out = harness(&path, "resolved");
        assert!(
            out.starts_with("decode error:"),
            "{name}: expected a structured decode error, got: {out}"
        );
    }
}

// A well-formed document whose node ids or spans are internally inconsistent is
// refused with the structured error naming the fault, never decoded into a tree
// that would then mis-join. Each fixture derives from a clean golden with one
// injected fault: a duplicated node id, and a span running past the embedded
// source, so the decoder's identity and bounds invariants each fail closed.
#[test]
fn resolved_fails_closed_on_inconsistent_document() {
    for (fixture, needle) in [
        ("mismatch_dup_id", "duplicate node id"),
        ("mismatch_oob_span", "past source length"),
    ] {
        let out = harness(
            &fixture_dir().join(format!("{fixture}.{ARTIFACT}.json")),
            "resolved",
        );
        assert!(
            out.starts_with("decode error: $.functions") && out.contains(needle),
            "{fixture}: expected the structured `{needle}` refusal, got: {out}"
        );
    }
}
