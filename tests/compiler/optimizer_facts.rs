//! The optimizer fact sheet (`dump optimizer-facts`) over the committed
//! optimization fixtures under `examples/fixtures/compiler/`.
//!
//! Each fixture exists to prove a cost is real before any rewrite claims to
//! remove it, and these tests pin the baseline fact that carries that proof: a
//! constructor built behind a non-inlined call, a statically known closure
//! whose applications now collapse to direct calls, a wrapper that preserves
//! or duplicates its callback's use. A pass that later resolves one of these
//! must move the pinned number deliberately, never silently.

use std::{env, fs, path::Path, process};

use serde_json::Value;

const OPTIMIZER_FACTS: &str = "optimizer-facts";
const FIXTURE_DIR: &str = "examples/fixtures/compiler";
const FACTS_SCHEMA: &str = "prism-optimizer-facts-v2";

fn facts_text(stem: &str) -> String {
    let path = format!("{FIXTURE_DIR}/{stem}.pr");
    let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    prism::dump(OPTIMIZER_FACTS, &prism::with_prelude(&src))
        .unwrap_or_else(|e| panic!("dumping optimizer facts for `{path}` failed: {e:?}"))
}

fn facts(stem: &str) -> Value {
    serde_json::from_str(&facts_text(stem)).expect("optimizer facts are valid JSON")
}

fn row<'a>(doc: &'a Value, name: &str) -> &'a Value {
    doc["functions"]
        .as_array()
        .expect("optimizer facts carry a functions array")
        .iter()
        .find(|f| f["name"] == name)
        .unwrap_or_else(|| panic!("no fact row for `{name}`"))
}

fn count(row: &Value, field: &str) -> i64 {
    row[field]
        .as_i64()
        .unwrap_or_else(|| panic!("fact field `{field}` is a count"))
}

fn result(row: &Value) -> &str {
    row["result"].as_str().expect("result fact is a string")
}

fn callees(row: &Value) -> Vec<&str> {
    row["callees"]
        .as_array()
        .expect("callees is an array")
        .iter()
        .map(|c| c.as_str().expect("callee is a name"))
        .collect()
}

/// The envelope is versioned and self-describing, and the artifact is a pure
/// function of the source: two dumps of the same fixture are byte-identical.
#[test]
fn fact_sheet_is_versioned_and_deterministic() {
    let first = facts_text("ctor_cross_call");
    let doc: Value = serde_json::from_str(&first).unwrap();
    assert_eq!(doc["schema"], FACTS_SCHEMA);
    assert_eq!(doc["compiler"], env!("CARGO_PKG_VERSION"));
    assert_eq!(
        first,
        facts_text("ctor_cross_call"),
        "fact dump is not deterministic"
    );
}

/// A constructor relation crossing a non-inlined direct call: `mk` provably
/// returns `MkPair` at its interface, and `main` reaches it (and the projection
/// `first`) only through direct calls. The fact an interprocedural domain would
/// exploit is already visible; nothing today consumes it across the boundary.
#[test]
fn constructor_relation_crosses_an_uninlined_call() {
    let doc = facts("ctor_cross_call");
    assert_eq!(result(row(&doc, "mk")), "constructor: returns `MkPair`");
    let main = row(&doc, "main");
    assert!(callees(main).contains(&"mk") && callees(main).contains(&"first"));
    assert_eq!(count(main, "direct_calls"), 4);
    assert_eq!(count(main, "indirect_calls"), 0);
}

/// A statically known closure applied through a parameter devirtualizes: the
/// local lambda is hoisted to a single named definition and `apply_twice` is
/// cloned against it, so the executed path performs only direct calls. The
/// hoisted body exists exactly once, and the unspecialized original keeps its
/// indirect applications, proving the collapse cloned rather than rewrote.
#[test]
fn known_closure_becomes_direct_calls_without_duplication() {
    let doc = facts("known_closure");
    let clone = row(&doc, "apply_twice$hs1");
    assert_eq!(count(clone, "direct_calls"), 2);
    assert_eq!(count(clone, "indirect_calls"), 0);
    assert_eq!(callees(clone), vec!["main$ll1"]);
    let main = row(&doc, "main");
    assert_eq!(count(main, "indirect_calls"), 0);
    assert_eq!(callees(main), vec!["apply_twice$hs1"]);
    let hoisted = doc["functions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["name"].as_str().unwrap_or_default().contains("$ll"))
        .count();
    assert_eq!(hoisted, 1, "the lambda body is hoisted exactly once");
    let original = row(&doc, "apply_twice");
    assert_eq!(count(original, "indirect_calls"), 2);
}

/// An unboxed product built in one function and consumed in another: `polar`'s
/// interface fact is a freshly built product, `norm2` consumes it behind a
/// non-inlined boundary (two call sites each).
#[test]
fn unboxed_product_crosses_a_function_boundary() {
    let doc = facts("unboxed_cross");
    assert_eq!(
        result(row(&doc, "polar")),
        "product: returns a freshly built product"
    );
    assert_eq!(count(row(&doc, "main"), "direct_calls"), 4);
}

/// The once-use wrapper pair: `use_once` applies its callback exactly once and
/// `use_twice` twice, and the counts at the interface are what a callable
/// contract would carry. The executed path runs through specialized clones
/// whose direct-call counts carry the same multiplicity, so the once/twice
/// distinction survives devirtualization and stays visible at the interface.
#[test]
fn once_use_wrapper_preserves_and_loses_multiplicity() {
    let doc = facts("ho_once_wrapper");
    assert_eq!(count(row(&doc, "use_once"), "indirect_calls"), 1);
    assert_eq!(count(row(&doc, "use_twice"), "indirect_calls"), 2);
    assert_eq!(count(row(&doc, "use_once$hs1"), "direct_calls"), 1);
    assert_eq!(count(row(&doc, "use_twice$hs2"), "direct_calls"), 2);
}

/// An iterator over an opaque callback: `sum_with` folds through one indirect
/// application per element plus its own recursive direct call, and its result
/// joins over the two list arms. The executed path is a pair of clones, one
/// per hoisted callback, each folding through a direct call; the interface
/// still carries no allocation requirement, so the lean and allocating clones
/// read identically except for the callee they name.
#[test]
fn iterator_callback_stays_opaque_at_the_interface() {
    let doc = facts("iter_callback");
    let fold = row(&doc, "sum_with");
    assert_eq!(count(fold, "indirect_calls"), 1);
    assert!(
        callees(fold).contains(&"sum_with"),
        "recursive call is direct"
    );
    assert_eq!(result(fold), "unknown: joins over 2 branches");
    let lean = row(&doc, "sum_with$hs1");
    let allocating = row(&doc, "sum_with$hs2");
    assert_eq!(count(lean, "indirect_calls"), 0);
    assert_eq!(count(allocating, "indirect_calls"), 0);
    assert!(callees(lean).contains(&"main$ll1"));
    assert!(callees(allocating).contains(&"main$ll2"));
}

/// Exact-size construction through `range` and `map` versus a filtered case.
/// The mapped variant's element count is proven exact, so its main reaches
/// the frozen-array builder through the sized clone chain: the wrapper and
/// seed clones thread the count down to an entry that allocates the
/// destination once and a fill that writes by index, while the growable
/// originals remain for unproven sites. The filtered variant's cardinality is
/// only an upper bound, so it must keep the growable path unchanged.
#[test]
fn exact_size_construction_baseline() {
    let mapped = facts("exact_size_map");
    let filtered = facts("exact_size_filter");
    let mc = callees(row(&mapped, "main"));
    assert!(mc.contains(&"Data.List.map$hs1") && mc.contains(&"Data.List.range"));
    assert!(mc.contains(&"Data.Frozen.fz_of_list$xs1"));
    assert_eq!(
        row(&mapped, "Data.List.map$hs1")["summary"]["cardinality"],
        "exact count of param 0"
    );
    assert_eq!(
        callees(row(&mapped, "Data.Frozen.fz_of_list$xs1")),
        vec!["array_of_list$xs1"]
    );
    assert_eq!(
        callees(row(&mapped, "array_of_list$xs1")),
        vec!["push_all$xs1"]
    );
    assert_eq!(callees(row(&mapped, "push_all$xs1")), vec!["push_all$xs2"]);
    assert_eq!(
        callees(row(&mapped, "Data.Frozen.fz_of_list")),
        vec!["array_of_list"],
        "the growable original survives for unproven sites"
    );
    let fc = callees(row(&filtered, "main"));
    assert!(fc.contains(&"Data.List.filter$hs1"));
    assert!(
        !fc.iter().any(|c| c.contains("$xs")),
        "an upper bound never licenses the sized path"
    );
    assert!(callees(row(&filtered, "main$ll1")).contains(&"even"));
    assert_eq!(
        row(&filtered, "Data.List.filter$hs1")["summary"]["cardinality"],
        "at-most count of param 0"
    );
}

/// The effectful/mutating fixture: `observed` performs an effect operation and
/// an in-place array write between defining and using its facts. Its tail is an
/// honest scalar, but everything upstream of it must be forgotten; the row
/// pins the function's baseline shape so a speculative domain that starts
/// retaining facts across the kill points shows up as a deliberate change here.
#[test]
fn effectful_fixture_baseline_shape() {
    let doc = facts("opaque_kill");
    let observed = row(&doc, "observed");
    assert_eq!(
        result(observed),
        "scalar: returns a primitive arithmetic result"
    );
    let main = row(&doc, "main");
    assert_eq!(
        count(main, "indirect_calls"),
        1,
        "the handled action is a computed thunk"
    );
}

/// A `Vec128` value crossing a non-inlined native call: `dot2` has two call
/// sites and a scalar interface fact, so the vector argument crosses a real
/// boundary in Core.
#[test]
fn vector_value_crosses_an_uninlined_call() {
    let doc = facts("vec128_cross");
    assert_eq!(count(row(&doc, "main"), "direct_calls"), 2);
    assert_eq!(
        result(row(&doc, "dot2")),
        "scalar: returns a primitive arithmetic result"
    );
}

/// Each fact row carries the interprocedural summary computed over verified
/// typed Core: result shape, principal effects, an allocation bound, and the
/// capture state. The projection allocates nothing while the constructor
/// wrapper is unbounded, and only `main` carries the ambient IO row.
#[test]
fn summary_block_reports_typed_core_facts() {
    let doc = facts("ctor_cross_call");
    let mk = &row(&doc, "mk")["summary"];
    assert_eq!(mk["result"], "constructor `MkPair`");
    assert_eq!(mk["allocation"], "unbounded");
    assert_eq!(mk["effects"], "{}");
    let first = &row(&doc, "first")["summary"];
    assert_eq!(first["allocation"], "zero");
    assert_eq!(first["capture"], "no-closures");
    let main = &row(&doc, "main")["summary"];
    assert_eq!(main["effects"], "{IO}");
    assert_eq!(main["allocation"], "unbounded");
}

/// Deep type-property propagation: the immutable and mutable payloads flow
/// through the same generic `Cell` and the same projection `peek`, whose
/// interface fact cannot tell them apart today.
#[test]
fn deep_property_fixture_shares_one_projection() {
    let doc = facts("deep_immutable");
    let peek = row(&doc, "peek");
    assert_eq!(result(peek), "unknown: returns a locally bound value");
    let mc = callees(row(&doc, "main"));
    assert!(mc.contains(&"peek") && mc.contains(&"array_of_list$xs1"));
}

/// The encoded summary table is durably stored under the compiler cache and,
/// on a warm key, checked byte-for-byte against the stored copy inside the
/// dump itself. The second dump exercises that reconcile-hit path (a table
/// that failed to reproduce byte-identically fails the dump loudly), and the
/// rendered artifact must not move either.
#[test]
fn summaries_reused_from_the_store_are_byte_identical() {
    let store = env::temp_dir().join(format!("prism-function-summaries-{}", process::id()));
    let _ = fs::remove_dir_all(&store);
    let path = format!("{FIXTURE_DIR}/exact_size_map.pr");
    let src = prism::with_prelude(&fs::read_to_string(&path).unwrap());
    let roots = prism::default_roots(Path::new("."));
    let mut cfg = prism::Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(store.clone()));
    let cold = prism::dump_on(OPTIMIZER_FACTS, &src, &roots, &cfg).unwrap();
    let warm = prism::dump_on(OPTIMIZER_FACTS, &src, &roots, &cfg).unwrap();
    assert_eq!(cold, warm, "warm summaries diverged from the stored table");
    let _ = fs::remove_dir_all(&store);
}
