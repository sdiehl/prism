use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use prism::lineage::{
    record_fact, FactInput, FactLedger, FactOutcome, FactScope, QueryFact, QueryKind,
};
use prism::store::disk::Store;
use prism::{
    build_on_report, check_modules_on, with_prelude, CompilerSession, Config, NativeCacheStatus,
    SessionStats,
};

use crate::support::{assert_same_binary, require_cc, TempDir};

// The default worker count auto-detects host parallelism, so the sequential
// arm of each byte-diff oracle must pin one worker explicitly.
const SEQUENTIAL_QUERY_THREADS: usize = 1;
const PARALLEL_QUERY_THREADS: usize = 4;
const FINAL_EDIT_INDEX: usize = 4;
const NATIVE_OBJECT_QUERIES: &str = "queries/native-object";
const RUNTIME_OBJECT_QUERIES: &str = "queries/runtime-object";
const RETIRED_OPTIMIZED_SCC_QUERIES: &str = "queries/optimized-scc";
const LLVM_SCC_QUERIES: &str = "queries/llvm-scc-bitcode";
const CLOSURE_SUMMARY_QUERIES: &str = "queries/llvm-scc-closure-summary";
const RETIRED_EFFECT_PLAN_QUERIES: &str = "queries/effect-lowering-plan";
const RETIRED_EFFECT_RESULT_QUERIES: &str = "queries/effect-lowering-result";
const LINKED_NATIVE_RAW_QUERIES: &str = "queries/linked-native.raw";
const LINKED_NATIVE_SEMANTIC_QUERIES: &str = "queries/linked-native.semantic";

// Linked-artifact keys are output-path independent, so a rebuild of the same
// program is a whole-binary hit that never replays the backend queries. The
// corruption gates below need those queries to actually run, so they drop the
// linked bindings first, forcing the rebuild to re-derive the binary from the
// store's lower-level artifacts.
fn drop_linked_queries(root: &Path) {
    for kind in [LINKED_NATIVE_RAW_QUERIES, LINKED_NATIVE_SEMANTIC_QUERIES] {
        let dir = root.join(kind);
        if dir.exists() {
            fs::remove_dir_all(dir).unwrap();
        }
    }
}

// Query bindings sit one shard level below the kind directory
// (queries/<kind>/<2hex>/<rest>), so every direct reader walks that level.
fn query_files(root: &Path, kind: &str) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for shard in fs::read_dir(root.join(kind)).unwrap() {
        let shard = shard.unwrap();
        if !shard.file_type().unwrap().is_dir() {
            continue;
        }
        for entry in fs::read_dir(shard.path()).unwrap() {
            files.push(entry.unwrap().path());
        }
    }
    files.sort();
    files
}

fn query_count(root: &Path, kind: &str) -> usize {
    query_files(root, kind).len()
}

fn query_bindings(root: &Path, kind: &str) -> BTreeMap<String, String> {
    query_files(root, kind)
        .into_iter()
        .map(|path| {
            let shard = path.parent().unwrap().file_name().unwrap();
            let key = format!(
                "{}{}",
                shard.to_string_lossy(),
                path.file_name().unwrap().to_string_lossy()
            );
            (key, fs::read_to_string(path).unwrap())
        })
        .collect()
}

fn assert_bindings_contain(superset_root: &Path, subset_root: &Path, kind: &str, context: &str) {
    let superset = query_bindings(superset_root, kind);
    for (key, value) in query_bindings(subset_root, kind) {
        assert_eq!(
            superset.get(&key),
            Some(&value),
            "{context}: final query {kind}/{key} differs from the fresh build"
        );
    }
}

#[test]
fn persisted_fact_graph_spans_all_active_native_query_producers() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "query-fact-chain");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let before = with_prelude(concat!(
        "effect Tick\n",
        "  tick() : Int\n",
        "fn apply(f : (Int) -> Int, x : Int) : Int = f(x)\n",
        "fn work() : Int ! {Tick} = tick()\n",
        "fn run() : Int =\n",
        "  handle work() with\n",
        "    tick() resume k => k(41)\n",
        "    return r => r\n",
        "fn main() : Unit = println(run() + apply(\\(x) -> x + 1, 0))\n",
    ));
    let after = before.replace("k(41)", "k(42)");
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));

    for (index, source) in [before, after].into_iter().enumerate() {
        cfg.set_session(Some(CompilerSession::new()));
        check_modules_on(&source, &roots, &cfg).unwrap();
        build_on_report(&source, &roots, &tmp.join(format!("program-{index}")), &cfg).unwrap();
    }

    let store = Store::open_or_create(tmp.store_root()).unwrap();
    let ledger = FactLedger::load(&store, &FactScope::of_roots(&roots)).unwrap();
    let kinds = ledger
        .diff()
        .entries
        .iter()
        .filter_map(|entry| entry.current.as_ref().map(|fact| fact.kind))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        kinds,
        [
            QueryKind::Module,
            QueryKind::BackendScc,
            QueryKind::ClosurePlan,
            QueryKind::Object,
            QueryKind::Link,
        ]
        .into_iter()
        .collect(),
        "one fact graph must explain the five active native query producers"
    );
    assert!(
        ledger
            .diff()
            .entries
            .iter()
            .filter_map(|entry| entry.current.as_ref())
            .all(|fact| !fact.inputs.is_empty()),
        "every durable query fact must name its semantic input identity"
    );
}

#[test]
fn warm_native_build_materializes_byte_identical_binary() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "warm");
    let src = with_prelude("fn main() = println(40 + 2)");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));
    cfg.update_flags(|flags| flags.query_threads = SEQUENTIAL_QUERY_THREADS);

    let bin = tmp.join("program");
    let first = build_on_report(&src, &roots, &bin, &cfg).unwrap();
    assert_eq!(first.cache, NativeCacheStatus::Write);
    assert_eq!(first.bitcode_cache, NativeCacheStatus::Write);
    assert!(first.definition_hashes.is_some());
    assert_eq!(
        first.cache_explanation(),
        "linked artifact and LLVM bitcode keys changed"
    );
    let native_objects = query_count(&tmp.store_root(), NATIVE_OBJECT_QUERIES);
    let runtime_objects = query_count(&tmp.store_root(), RUNTIME_OBJECT_QUERIES);
    let llvm_sccs = query_count(&tmp.store_root(), LLVM_SCC_QUERIES);
    let closure_summaries = query_count(&tmp.store_root(), CLOSURE_SUMMARY_QUERIES);
    assert!(native_objects > 1);
    assert!(llvm_sccs > 1);
    assert!(closure_summaries > 0);
    assert!(runtime_objects > 1);
    assert!(
        !tmp.store_root()
            .join(RETIRED_OPTIMIZED_SCC_QUERIES)
            .exists(),
        "the mid-end optimizer must publish no durable query family"
    );
    assert!(!tmp.store_root().join(RETIRED_EFFECT_PLAN_QUERIES).exists());
    assert!(!tmp
        .store_root()
        .join(RETIRED_EFFECT_RESULT_QUERIES)
        .exists());
    let cold = fs::read(&bin).unwrap();
    let cold_run = Command::new(&bin).output().unwrap();
    let cold_trace = prism::ObservationTrace::from_process(
        &cold_run.stdout,
        &cold_run.stderr,
        cold_run.status.code().unwrap(),
    );
    fs::remove_file(&bin).unwrap();

    let second = build_on_report(&src, &roots, &bin, &cfg).unwrap();
    assert_eq!(second.cache, NativeCacheStatus::Hit);
    assert_eq!(second.bitcode_cache, NativeCacheStatus::Disabled);
    assert!(second.definition_hashes.is_none());
    assert_eq!(second.cache_explanation(), "linked artifact key matched");
    assert_same_binary(
        "warm link hit vs cold build",
        &cold,
        &fs::read(&bin).unwrap(),
    );
    assert!(!bin.with_extension("bc").exists());
    let warm_run = Command::new(&bin).output().unwrap();
    let warm_trace = prism::ObservationTrace::from_process(
        &warm_run.stdout,
        &warm_run.stderr,
        warm_run.status.code().unwrap(),
    );
    assert_eq!(
        warm_trace, cold_trace,
        "cold and warm builds must be unobservable"
    );

    let mut parallel_cfg = cfg.clone();
    parallel_cfg.update_flags(|flags| flags.query_threads = PARALLEL_QUERY_THREADS);
    fs::remove_file(&bin).unwrap();
    let parallel = build_on_report(&src, &roots, &bin, &parallel_cfg).unwrap();
    assert_eq!(parallel.cache, NativeCacheStatus::Hit);
    assert_same_binary(
        "parallel workers vs cold build",
        &cold,
        &fs::read(&bin).unwrap(),
    );
    let parallel_run = Command::new(&bin).output().unwrap();
    assert_eq!(
        prism::ObservationTrace::from_process(
            &parallel_run.stdout,
            &parallel_run.stderr,
            parallel_run.status.code().unwrap(),
        ),
        warm_trace,
        "sequential and parallel query scheduling must be unobservable"
    );

    // The linked key is output-path independent: the same program built to a
    // new destination is a whole-binary hit, byte-identical to the first.
    let relocated = tmp.join("relocated");
    let relocation = build_on_report(&src, &roots, &relocated, &cfg).unwrap();
    assert_eq!(relocation.cache, NativeCacheStatus::Hit);
    assert_eq!(relocation.bitcode_cache, NativeCacheStatus::Disabled);
    assert_eq!(
        relocation.cache_explanation(),
        "linked artifact key matched"
    );
    assert_same_binary(
        "relocated output vs cold build",
        &cold,
        &fs::read(&relocated).unwrap(),
    );
    assert_eq!(
        query_count(&tmp.store_root(), NATIVE_OBJECT_QUERIES),
        native_objects
    );
    assert_eq!(
        query_count(&tmp.store_root(), RUNTIME_OBJECT_QUERIES),
        runtime_objects
    );

    fs::remove_file(&bin).unwrap();
    let formatted_only = format!("{src}\n-- query identity ignores trivia\n");
    let semantic = build_on_report(&formatted_only, &roots, &bin, &cfg).unwrap();
    assert_eq!(semantic.cache, NativeCacheStatus::Hit);
    assert!(semantic.definition_hashes.is_some());
    assert_same_binary(
        "formatting-only edit vs cold build",
        &cold,
        &fs::read(&bin).unwrap(),
    );
    assert_eq!(
        query_count(&tmp.store_root(), LLVM_SCC_QUERIES),
        llvm_sccs,
        "formatting-only edits must write no backend SCC artifacts"
    );
    assert_eq!(
        query_count(&tmp.store_root(), CLOSURE_SUMMARY_QUERIES),
        closure_summaries,
        "formatting-only edits must write no closure summaries"
    );

    fs::remove_file(&bin).unwrap();
    let changed = with_prelude("fn main() = println(40 + 3)");
    let changed_report = build_on_report(&changed, &roots, &bin, &cfg).unwrap();
    assert_eq!(changed_report.cache, NativeCacheStatus::Write);
    let changed_llvm_sccs = query_count(&tmp.store_root(), LLVM_SCC_QUERIES);
    assert_eq!(
        changed_llvm_sccs - llvm_sccs,
        2,
        "only the changed backend SCC and the explicit global metadata plan move"
    );
    let changed_closure_summaries = query_count(&tmp.store_root(), CLOSURE_SUMMARY_QUERIES);
    assert_eq!(
        changed_closure_summaries - closure_summaries,
        1,
        "only the changed backend SCC may write a new closure summary"
    );
    let changed_native_objects = query_count(&tmp.store_root(), NATIVE_OBJECT_QUERIES);
    assert_eq!(
        changed_native_objects - native_objects,
        2,
        "only changed backend artifacts may compile new native objects"
    );
    let changed_cached = fs::read(&bin).unwrap();
    assert_ne!(changed_cached, cold);
    let cached_run = Command::new(&bin).output().unwrap();
    let cached_trace = prism::ObservationTrace::from_process(
        &cached_run.stdout,
        &cached_run.stderr,
        cached_run.status.code().unwrap(),
    );

    fs::remove_file(&bin).unwrap();
    cfg.update_flags(|flags| flags.compiler_cache = false);
    let report = build_on_report(&changed, &roots, &bin, &cfg).unwrap();
    assert_eq!(report.cache, NativeCacheStatus::Disabled);
    let uncached = fs::read(&bin).unwrap();
    assert_same_binary("cache disabled vs cache warm", &changed_cached, &uncached);
    let uncached_run = Command::new(&bin).output().unwrap();
    assert_eq!(
        prism::ObservationTrace::from_process(
            &uncached_run.stdout,
            &uncached_run.stderr,
            uncached_run.status.code().unwrap(),
        ),
        cached_trace
    );

    let whole = tmp.join("whole-program");
    cfg.update_flags(|flags| flags.scc_backend = false);
    let whole_report = build_on_report(&changed, &roots, &whole, &cfg).unwrap();
    assert_eq!(whole_report.cache, NativeCacheStatus::Disabled);
    assert!(!fs::read(&whole).unwrap().is_empty());
    let whole_run = Command::new(whole).output().unwrap();
    assert_eq!(
        prism::ObservationTrace::from_process(
            &whole_run.stdout,
            &whole_run.stderr,
            whole_run.status.code().unwrap(),
        ),
        cached_trace,
        "backend partitioning must be unobservable"
    );
}

#[test]
fn typed_route_second_build_preserves_warm_cache_artifacts() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "typed-shadow-report");
    let src = with_prelude(include_str!("../../examples/imperative.pr"));
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));

    let cold_bin = tmp.join("cold");
    let cold_report = build_on_report(&src, &roots, &cold_bin, &cfg).unwrap();
    assert_eq!(cold_report.cache, NativeCacheStatus::Write);
    assert_eq!(cold_report.bitcode_cache, NativeCacheStatus::Write);
    let cold_run = Command::new(&cold_bin).output().unwrap();
    let cold_trace = prism::ObservationTrace::from_process(
        &cold_run.stdout,
        &cold_run.stderr,
        cold_run.status.code().unwrap(),
    );
    let semantic_bindings = [LLVM_SCC_QUERIES, CLOSURE_SUMMARY_QUERIES]
        .into_iter()
        .filter(|kind| tmp.store_root().join(kind).is_dir())
        .map(|kind| (kind, query_bindings(&tmp.store_root(), kind)))
        .collect::<Vec<_>>();
    assert!(
        !tmp.store_root().join(RETIRED_EFFECT_PLAN_QUERIES).exists()
            && !tmp
                .store_root()
                .join(RETIRED_EFFECT_RESULT_QUERIES)
                .exists(),
        "typed effect lowering must publish no retired legacy query family"
    );

    // Drop the linked bindings so the rebuild exercises the warm bitcode
    // level instead of returning the whole cached binary.
    drop_linked_queries(&tmp.store_root());
    let observed_bin = tmp.join("observed");
    let observed_report = build_on_report(&src, &roots, &observed_bin, &cfg).unwrap();
    assert_eq!(observed_report.cache, NativeCacheStatus::Write);
    assert_eq!(observed_report.bitcode_cache, NativeCacheStatus::Hit);
    let observed_bytes = fs::read(&observed_bin).unwrap();
    let observed_run = Command::new(&observed_bin).output().unwrap();
    assert_eq!(
        prism::ObservationTrace::from_process(
            &observed_run.stdout,
            &observed_run.stderr,
            observed_run.status.code().unwrap(),
        ),
        cold_trace,
        "a second typed-route build must not change program behavior"
    );
    for (kind, cold_bindings) in semantic_bindings {
        assert_eq!(
            query_bindings(&tmp.store_root(), kind),
            cold_bindings,
            "a second typed-route build changed semantic cache artifacts for {kind}"
        );
    }

    fs::remove_file(&observed_bin).unwrap();
    let warm_report = build_on_report(&src, &roots, &observed_bin, &cfg).unwrap();
    assert_eq!(
        warm_report.cache,
        NativeCacheStatus::Hit,
        "an unchanged input must reuse the final artifact"
    );
    assert_eq!(warm_report.bitcode_cache, NativeCacheStatus::Disabled);
    assert_same_binary(
        "warm rebuild vs observed build",
        &observed_bytes,
        &fs::read(observed_bin).unwrap(),
    );
}

#[test]
fn incremental_store_reaches_the_fresh_final_artifacts() {
    require_cc();
    let incremental = TempDir::new("compiler-cache", "incremental-oracle");
    let fresh = TempDir::new("compiler-cache", "fresh-oracle");
    let parallel = TempDir::new("compiler-cache", "parallel-oracle");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let base = with_prelude(
        "fn dormant(x : Int) : Int = x * 2\n\
         fn hidden(x : Int) : Int = x + 1\n\
         fn api(x : Int) : Int = hidden(x)\n\
         fn main() : Unit = println(api(41))\n",
    );
    let formatted = format!("{base}\n-- trivia-only edit\n");
    let private_edit = formatted.replace("x + 1", "x + 2");
    let interface_edit = private_edit
        .replace(
            "fn api(x : Int) : Int = hidden(x)",
            "fn api(x : Int, y : Int) : Int = hidden(x) + y",
        )
        .replace("println(api(41))", "println(api(39, 1))");
    let final_source =
        interface_edit.replace("println(api(39, 1))", "println(api(39, 1) + dormant(1))");

    let mut incremental_cfg = Config::default();
    incremental_cfg.update_flags(|flags| flags.compiler_cache = true);
    incremental_cfg.update_flags(|flags| flags.store_path = Some(incremental.store_root()));
    incremental_cfg.update_flags(|flags| flags.query_threads = SEQUENTIAL_QUERY_THREADS);
    for (index, source) in [
        base,
        formatted,
        private_edit,
        interface_edit,
        final_source.clone(),
    ]
    .into_iter()
    .enumerate()
    {
        let output = if index == FINAL_EDIT_INDEX {
            incremental.join("program")
        } else {
            incremental.join(format!("history-{index}"))
        };
        build_on_report(&source, &roots, &output, &incremental_cfg).unwrap();
    }
    let incremental_bin = incremental.join("program");

    let mut fresh_cfg = Config::default();
    fresh_cfg.update_flags(|flags| flags.compiler_cache = true);
    fresh_cfg.update_flags(|flags| flags.store_path = Some(fresh.store_root()));
    fresh_cfg.update_flags(|flags| flags.query_threads = SEQUENTIAL_QUERY_THREADS);
    let fresh_bin = fresh.join("program");
    build_on_report(&final_source, &roots, &fresh_bin, &fresh_cfg).unwrap();

    let mut parallel_cfg = fresh_cfg.clone();
    parallel_cfg.update_flags(|flags| flags.query_threads = PARALLEL_QUERY_THREADS);
    parallel_cfg.update_flags(|flags| flags.store_path = Some(parallel.store_root()));
    let parallel_bin = parallel.join("program");
    build_on_report(&final_source, &roots, &parallel_bin, &parallel_cfg).unwrap();

    let incremental_bytes = fs::read(&incremental_bin).unwrap();
    let fresh_bytes = fs::read(&fresh_bin).unwrap();
    let parallel_bytes = fs::read(&parallel_bin).unwrap();
    assert_same_binary(
        "incremental store vs fresh store",
        &fresh_bytes,
        &incremental_bytes,
    );
    assert_same_binary(
        "parallel workers vs fresh store",
        &fresh_bytes,
        &parallel_bytes,
    );

    let run = |path: &Path| {
        let output = Command::new(path).output().unwrap();
        prism::ObservationTrace::from_process(
            &output.stdout,
            &output.stderr,
            output.status.code().unwrap(),
        )
    };
    let fresh_trace = run(&fresh_bin);
    assert_eq!(run(&incremental_bin), fresh_trace);
    assert_eq!(run(&parallel_bin), fresh_trace);

    for kind in [
        LLVM_SCC_QUERIES,
        CLOSURE_SUMMARY_QUERIES,
        NATIVE_OBJECT_QUERIES,
        RUNTIME_OBJECT_QUERIES,
    ] {
        assert_bindings_contain(
            &incremental.store_root(),
            &fresh.store_root(),
            kind,
            "incremental store",
        );
        assert_eq!(
            query_bindings(&parallel.store_root(), kind),
            query_bindings(&fresh.store_root(), kind),
            "parallel worker count changed final {kind} artifacts"
        );
    }
    prism::verify_backend_recomposition_on(&final_source, &roots, &fresh_cfg).unwrap();
}

#[test]
fn sequential_and_parallel_scc_artifacts_are_identical() {
    require_cc();
    let sequential = TempDir::new("compiler-cache", "scc-sequential");
    let parallel = TempDir::new("compiler-cache", "scc-parallel");
    let src = with_prelude(
        "fn left(x : Int) = x + 1\nfn right(x : Int) = x * 2\nfn main() = println(left(20) + right(10))",
    );
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut sequential_cfg = Config::default();
    sequential_cfg.update_flags(|flags| flags.compiler_cache = true);
    sequential_cfg.update_flags(|flags| flags.store_path = Some(sequential.store_root()));
    sequential_cfg.update_flags(|flags| flags.query_threads = SEQUENTIAL_QUERY_THREADS);
    let mut parallel_cfg = sequential_cfg.clone();
    parallel_cfg.update_flags(|flags| flags.query_threads = PARALLEL_QUERY_THREADS);
    parallel_cfg.update_flags(|flags| flags.store_path = Some(parallel.store_root()));

    let sequential_bin = sequential.join("program");
    let parallel_bin = parallel.join("program");
    build_on_report(&src, &roots, &sequential_bin, &sequential_cfg).unwrap();
    build_on_report(&src, &roots, &parallel_bin, &parallel_cfg).unwrap();
    assert_eq!(
        query_bindings(&sequential.store_root(), LLVM_SCC_QUERIES),
        query_bindings(&parallel.store_root(), LLVM_SCC_QUERIES),
        "worker count must not alter backend SCC keys or bitcode identities"
    );
    assert_eq!(
        query_bindings(&sequential.store_root(), CLOSURE_SUMMARY_QUERIES),
        query_bindings(&parallel.store_root(), CLOSURE_SUMMARY_QUERIES),
        "worker count must not alter closure summary identities"
    );
    assert_same_binary(
        "sequential SCC backend vs parallel SCC backend",
        &fs::read(sequential_bin).unwrap(),
        &fs::read(parallel_bin).unwrap(),
    );
}

#[test]
fn unreachable_scc_is_not_reused_after_it_becomes_reachable() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "scc-dead-to-live");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let before = with_prelude(
        "fn hidden() : Int = 41\n\
         fn main() : Unit = println(0)\n",
    );
    let after = with_prelude(
        "fn hidden() : Int = 41\n\
         fn main() : Unit = println(hidden() + 1)\n",
    );
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));

    let before_bin = tmp.join("before");
    build_on_report(&before, &roots, &before_bin, &cfg).unwrap();
    let before_output = Command::new(before_bin).output().unwrap();
    assert_eq!(before_output.stdout, b"0\n");

    let before_queries = query_bindings(&tmp.store_root(), LLVM_SCC_QUERIES);
    let after_bin = tmp.join("after");
    build_on_report(&after, &roots, &after_bin, &cfg).unwrap();
    let after_queries = query_bindings(&tmp.store_root(), LLVM_SCC_QUERIES);
    assert!(
        after_queries.len() > before_queries.len(),
        "making an SCC reachable must create a distinct backend query"
    );
    let after_output = Command::new(after_bin).output().unwrap();
    assert_eq!(after_output.stdout, b"42\n");
}

#[test]
fn closure_body_edit_preserves_dispatch_shards() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "closure-shards");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    // A closure passed to `apply` as a literal is a known callee the specializer
    // devirtualizes, and a devirtualized program has no dispatch shards left to
    // preserve. Each closure is instead fetched from an array cell at an index
    // only recursion can produce: the optimizer tracks no facts through mutable
    // cells, so the callee stays unknown and the shards this test watches exist.
    let before = with_prelude(
        "fn apply(f : (Int) -> Int, x : Int) = f(x)\n\
         fn spin(n : Int) : Int = if n <= 0 then 0 else spin(n - 1)\n\
         fn left() = apply(array_get(array_of_list(Cons(\\(x) -> x + 1, Nil)), spin(1)), 20)\n\
         fn right() = apply(array_get(array_of_list(Cons(\\(x) -> x * 2, Nil)), spin(1)), 10)\n\
         fn main() = println(left() + right())\n",
    );
    let after = before.replace("x + 1", "x + 2");
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));

    build_on_report(&before, &roots, &tmp.join("before"), &cfg).unwrap();
    let before_queries = query_bindings(&tmp.store_root(), LLVM_SCC_QUERIES);
    let before_summaries = query_bindings(&tmp.store_root(), CLOSURE_SUMMARY_QUERIES);
    build_on_report(&after, &roots, &tmp.join("after"), &cfg).unwrap();
    let after_queries = query_bindings(&tmp.store_root(), LLVM_SCC_QUERIES);
    let after_summaries = query_bindings(&tmp.store_root(), CLOSURE_SUMMARY_QUERIES);
    assert_eq!(
        after_summaries.len() - before_summaries.len(),
        2,
        "a closure-body edit writes only its affected SCC closure-summary cone"
    );
    assert_eq!(
        after_queries.len() - before_queries.len(),
        3,
        "a closure-body edit moves its optimized backend cone and native metadata, not stable-tag dispatch shards"
    );
    let output = Command::new(tmp.join("after")).output().unwrap();
    assert_eq!(output.stdout, b"42\n");
}

#[test]
fn scc_backend_matches_the_whole_program_oracle() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "scc-whole-oracle");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    for (index, example) in [
        "examples/accum.pr",
        "examples/eff_poly.pr",
        "tests/cases/run/wire_laws.pr",
    ]
    .into_iter()
    .enumerate()
    {
        let src = with_prelude(&fs::read_to_string(example).unwrap());
        let mut scc_cfg = Config::default();
        scc_cfg.update_flags(|flags| flags.compiler_cache = false);
        prism::verify_backend_recomposition_on(&src, &roots, &scc_cfg).unwrap();
        scc_cfg.update_flags(|flags| flags.quiet = true);
        let scc_bin = tmp.join(format!("scc-{index}"));
        build_on_report(&src, &roots, &scc_bin, &scc_cfg).unwrap();

        let mut whole_cfg = scc_cfg.clone();
        whole_cfg.update_flags(|flags| flags.scc_backend = false);
        let whole_bin = tmp.join(format!("whole-{index}"));
        build_on_report(&src, &roots, &whole_bin, &whole_cfg).unwrap();

        let scc = Command::new(scc_bin).output().unwrap();
        let whole = Command::new(whole_bin).output().unwrap();
        assert_eq!(
            prism::ObservationTrace::from_process(
                &scc.stdout,
                &scc.stderr,
                scc.status.code().unwrap(),
            ),
            prism::ObservationTrace::from_process(
                &whole.stdout,
                &whole.stderr,
                whole.status.code().unwrap(),
            ),
            "SCC backend diverged from whole-program codegen for {example}"
        );
    }
}

#[test]
fn effectful_build_publishes_no_legacy_effect_queries_and_retires_stale_facts() {
    require_cc();
    let fresh = TempDir::new("compiler-cache", "no-effect-query");
    let upgrade = TempDir::new("compiler-cache", "retire-effect-query");
    let body = fs::read_to_string("examples/eff_state.pr").unwrap();
    let src = with_prelude(&body);
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.effect_tier = prism::EffectTier::FreeMonad);
    cfg.update_flags(|flags| flags.store_path = Some(fresh.store_root()));
    cfg.set_session(Some(CompilerSession::new()));

    let first_bin = fresh.join("first");
    let first_report = build_on_report(&src, &roots, &first_bin, &cfg).unwrap();
    assert_eq!(first_report.bitcode_cache, NativeCacheStatus::Write);
    assert!(!fresh
        .store_root()
        .join(RETIRED_EFFECT_PLAN_QUERIES)
        .exists());
    assert!(!fresh
        .store_root()
        .join(RETIRED_EFFECT_RESULT_QUERIES)
        .exists());
    let first = Command::new(&first_bin).output().unwrap();
    let first_bytes = fs::read(&first_bin).unwrap();
    fs::remove_file(&first_bin).unwrap();
    let second_report = build_on_report(&src, &roots, &first_bin, &cfg).unwrap();
    assert_eq!(second_report.cache, NativeCacheStatus::Hit);
    assert_eq!(second_report.bitcode_cache, NativeCacheStatus::Disabled);
    let second = Command::new(&first_bin).output().unwrap();
    assert_same_binary(
        "session warm rebuild vs first build",
        &first_bytes,
        &fs::read(&first_bin).unwrap(),
    );
    assert_eq!(second.stdout, first.stdout);
    assert_eq!(second.stderr, first.stderr);
    assert_eq!(second.status.code(), first.status.code());
    assert!(cfg
        .session()
        .unwrap()
        .decisions()
        .iter()
        .all(|decision| decision.kind != QueryKind::Effect));

    let stale_plan = upgrade.store_root().join(RETIRED_EFFECT_PLAN_QUERIES);
    let stale_result = upgrade.store_root().join(RETIRED_EFFECT_RESULT_QUERIES);
    fs::create_dir_all(&stale_plan).unwrap();
    fs::create_dir_all(&stale_result).unwrap();
    fs::write(stale_plan.join("legacy-plan"), "stale plan binding").unwrap();
    fs::write(stale_result.join("legacy-result"), "stale result binding").unwrap();
    let store = Store::open_or_create(upgrade.store_root()).unwrap();
    let scope = FactScope::of_roots(&roots);
    let legacy_effect = QueryFact {
        kind: QueryKind::Effect,
        identity: "whole-program:legacy".to_string(),
        inputs: vec![FactInput {
            name: "query-key".to_string(),
            identity: "legacy-key".to_string(),
        }],
        output: Some("legacy-output".to_string()),
        outcome: FactOutcome::Hit,
        reasons: Vec::new(),
    };
    record_fact(&store, &scope, legacy_effect.clone()).unwrap();

    let mut upgrade_cfg = cfg;
    upgrade_cfg.update_flags(|flags| flags.store_path = Some(upgrade.store_root()));
    upgrade_cfg.set_session(Some(CompilerSession::new()));
    let upgrade_bin = upgrade.join("program");
    build_on_report(&src, &roots, &upgrade_bin, &upgrade_cfg).unwrap();
    assert!(upgrade_cfg
        .session()
        .unwrap()
        .decisions()
        .iter()
        .all(|decision| decision.kind != QueryKind::Effect));
    // The planted bindings sit flat under their kind directories, the shape a
    // real pre-sharding store leaves behind. A build must not touch them: a
    // flat relic is invisible to the sharded read path and its removal belongs
    // to `store gc` alone.
    assert_eq!(
        fs::read_to_string(stale_plan.join("legacy-plan")).unwrap(),
        "stale plan binding",
        "old plan bindings are inert and remain Store-GC-owned"
    );
    assert_eq!(
        fs::read_to_string(stale_result.join("legacy-result")).unwrap(),
        "stale result binding",
        "old result bindings are inert and remain Store-GC-owned"
    );
    let ledger = FactLedger::load(&store, &scope).unwrap();
    assert!(
        ledger
            .current
            .facts()
            .iter()
            .all(|fact| fact.kind != QueryKind::Effect),
        "the upgraded compiler must retire stale current Effect facts"
    );
    assert_eq!(
        ledger
            .previous
            .get(QueryKind::Effect, "whole-program:legacy"),
        Some(&legacy_effect)
    );
    let upgraded = Command::new(upgrade_bin).output().unwrap();
    assert_eq!(
        prism::ObservationTrace::from_process(
            &upgraded.stdout,
            &upgraded.stderr,
            upgraded.status.code().unwrap(),
        ),
        prism::ObservationTrace::from_process(
            &first.stdout,
            &first.stderr,
            first.status.code().unwrap(),
        )
    );
}

#[test]
fn corrupt_backend_scc_is_rejected() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "corrupt-backend-scc");
    let src = with_prelude("fn main() = println(40 + 2)");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));

    build_on_report(&src, &roots, &tmp.join("first"), &cfg).unwrap();
    let query = query_files(&tmp.store_root(), LLVM_SCC_QUERIES)
        .into_iter()
        .next()
        .unwrap();
    let binding = fs::read_to_string(query).unwrap();
    let object_hash = binding.lines().nth(1).unwrap();
    let object = tmp
        .store_root()
        .join("objects")
        .join(&object_hash[..2])
        .join(&object_hash[2..]);
    fs::write(object, b"corrupt").unwrap();
    drop_linked_queries(&tmp.store_root());

    let error = build_on_report(&src, &roots, &tmp.join("relocated"), &cfg).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("backend SCC bitcode object hash mismatch"),
        "unexpected error: {error}"
    );
}

#[test]
fn corrupt_backend_closure_summary_is_rejected() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "corrupt-closure-summary");
    let src = with_prelude("fn main() = println((\\(x) -> x + 1)(41))");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut cfg = Config::default();
    cfg.update_flags(|flags| flags.compiler_cache = true);
    cfg.update_flags(|flags| flags.store_path = Some(tmp.store_root()));

    build_on_report(&src, &roots, &tmp.join("first"), &cfg).unwrap();
    let query = query_files(&tmp.store_root(), CLOSURE_SUMMARY_QUERIES)
        .into_iter()
        .next()
        .unwrap();
    let binding = fs::read_to_string(query).unwrap();
    let object_hash = binding.lines().nth(1).unwrap();
    let object = tmp
        .store_root()
        .join("objects")
        .join(&object_hash[..2])
        .join(&object_hash[2..]);
    fs::write(object, b"corrupt").unwrap();
    drop_linked_queries(&tmp.store_root());

    let error = build_on_report(&src, &roots, &tmp.join("relocated"), &cfg).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("backend SCC closure summary object hash mismatch"),
        "unexpected error: {error}"
    );
}

#[test]
fn session_semantic_hit_matches_cold_native_build() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "session-semantic");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let session = CompilerSession::new();
    let mut cfg = Config::default().with_session(session.clone());
    cfg.update_flags(|flags| flags.compiler_cache = false);
    let bin = tmp.join("program");
    let source = with_prelude("fn main() = println(42)\n");
    let formatted = format!("{source}\n-- formatting-only edit\n");

    let first = build_on_report(&source, &roots, &bin, &cfg).unwrap();
    assert_eq!(first.cache, NativeCacheStatus::Disabled);
    let cold = fs::read(&bin).unwrap();
    fs::remove_file(&bin).unwrap();
    let second = build_on_report(&formatted, &roots, &bin, &cfg).unwrap();
    assert_eq!(second.cache, NativeCacheStatus::Disabled);
    assert_same_binary(
        "session semantic hit vs cold build",
        &cold,
        &fs::read(&bin).unwrap(),
    );
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 1,
            misses: 1,
            writes: 2
        }
    );
}
