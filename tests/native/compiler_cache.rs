use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::process::Command;

use prism::lineage::{
    record_fact, FactInput, FactLedger, FactOutcome, FactScope, QueryFact, QueryKind,
};
use prism::store::disk::Store;
use prism::{
    build_on_report, check_modules_on, with_prelude, CompilerSession, Config, NativeCacheStatus,
    SessionStats,
};

use crate::support::{require_cc, TempDir};

const PARALLEL_QUERY_THREADS: usize = 4;
const FINAL_EDIT_INDEX: usize = 4;
const NATIVE_OBJECT_QUERIES: &str = "queries/native-object";
const RUNTIME_OBJECT_QUERIES: &str = "queries/runtime-object";
const OPTIMIZED_SCC_QUERIES: &str = "queries/optimized-scc";
const LLVM_SCC_QUERIES: &str = "queries/llvm-scc-bitcode";
const CLOSURE_SUMMARY_QUERIES: &str = "queries/llvm-scc-closure-summary";
const RETIRED_EFFECT_PLAN_QUERIES: &str = "queries/effect-lowering-plan";
const RETIRED_EFFECT_RESULT_QUERIES: &str = "queries/effect-lowering-result";

fn query_bindings(root: &Path, kind: &str) -> BTreeMap<String, String> {
    fs::read_dir(root.join(kind))
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            (
                entry.file_name().to_string_lossy().into_owned(),
                fs::read_to_string(entry.path()).unwrap(),
            )
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
    cfg.flags.quiet = true;
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

    for (index, source) in [before, after].into_iter().enumerate() {
        cfg.session = Some(CompilerSession::new());
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
            QueryKind::Optimizer,
            QueryKind::BackendScc,
            QueryKind::ClosurePlan,
            QueryKind::Object,
            QueryKind::Link,
        ]
        .into_iter()
        .collect(),
        "one fact graph must explain the six active native query producers"
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
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

    let bin = tmp.join("program");
    let first = build_on_report(&src, &roots, &bin, &cfg).unwrap();
    assert_eq!(first.cache, NativeCacheStatus::Write);
    assert_eq!(first.bitcode_cache, NativeCacheStatus::Write);
    assert_eq!(
        first.cache_explanation(),
        "linked artifact and LLVM bitcode keys changed"
    );
    let native_objects = fs::read_dir(tmp.store_root().join(NATIVE_OBJECT_QUERIES))
        .unwrap()
        .count();
    let runtime_objects = fs::read_dir(tmp.store_root().join(RUNTIME_OBJECT_QUERIES))
        .unwrap()
        .count();
    let optimized_sccs = fs::read_dir(tmp.store_root().join(OPTIMIZED_SCC_QUERIES))
        .unwrap()
        .count();
    let llvm_sccs = fs::read_dir(tmp.store_root().join(LLVM_SCC_QUERIES))
        .unwrap()
        .count();
    let closure_summaries = fs::read_dir(tmp.store_root().join(CLOSURE_SUMMARY_QUERIES))
        .unwrap()
        .count();
    assert!(native_objects > 1);
    assert!(llvm_sccs > 1);
    assert!(closure_summaries > 0);
    assert!(runtime_objects > 1);
    assert!(optimized_sccs > 1);
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
    assert_eq!(second.cache_explanation(), "linked artifact key matched");
    assert_eq!(fs::read(&bin).unwrap(), cold);
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
    parallel_cfg.flags.query_threads = PARALLEL_QUERY_THREADS;
    fs::remove_file(&bin).unwrap();
    let parallel = build_on_report(&src, &roots, &bin, &parallel_cfg).unwrap();
    assert_eq!(parallel.cache, NativeCacheStatus::Hit);
    assert_eq!(fs::read(&bin).unwrap(), cold);
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

    let relocated = tmp.join("relocated");
    let relocation = build_on_report(&src, &roots, &relocated, &cfg).unwrap();
    assert_eq!(relocation.cache, NativeCacheStatus::Write);
    assert_eq!(relocation.bitcode_cache, NativeCacheStatus::Hit);
    assert_eq!(
        relocation.cache_explanation(),
        "linked artifact key changed; LLVM bitcode key matched"
    );
    assert_eq!(
        fs::read_dir(tmp.store_root().join(NATIVE_OBJECT_QUERIES))
            .unwrap()
            .count(),
        native_objects
    );
    assert_eq!(
        fs::read_dir(tmp.store_root().join(RUNTIME_OBJECT_QUERIES))
            .unwrap()
            .count(),
        runtime_objects
    );
    assert_eq!(
        fs::read_dir(tmp.store_root().join(OPTIMIZED_SCC_QUERIES))
            .unwrap()
            .count(),
        optimized_sccs
    );

    fs::remove_file(&bin).unwrap();
    let formatted_only = format!("{src}\n-- query identity ignores trivia\n");
    let semantic = build_on_report(&formatted_only, &roots, &bin, &cfg).unwrap();
    assert_eq!(semantic.cache, NativeCacheStatus::Hit);
    assert_eq!(fs::read(&bin).unwrap(), cold);
    assert_eq!(
        fs::read_dir(tmp.store_root().join(OPTIMIZED_SCC_QUERIES))
            .unwrap()
            .count(),
        optimized_sccs,
        "formatting-only edits must write no semantic SCC artifacts"
    );
    assert_eq!(
        fs::read_dir(tmp.store_root().join(LLVM_SCC_QUERIES))
            .unwrap()
            .count(),
        llvm_sccs,
        "formatting-only edits must write no backend SCC artifacts"
    );
    assert_eq!(
        fs::read_dir(tmp.store_root().join(CLOSURE_SUMMARY_QUERIES))
            .unwrap()
            .count(),
        closure_summaries,
        "formatting-only edits must write no closure summaries"
    );

    fs::remove_file(&bin).unwrap();
    let changed = with_prelude("fn main() = println(40 + 3)");
    let changed_report = build_on_report(&changed, &roots, &bin, &cfg).unwrap();
    assert_eq!(changed_report.cache, NativeCacheStatus::Write);
    assert!(
        fs::read_dir(tmp.store_root().join(OPTIMIZED_SCC_QUERIES))
            .unwrap()
            .count()
            > optimized_sccs,
        "a semantic edit must write its affected SCC cone"
    );
    let changed_llvm_sccs = fs::read_dir(tmp.store_root().join(LLVM_SCC_QUERIES))
        .unwrap()
        .count();
    assert_eq!(
        changed_llvm_sccs - llvm_sccs,
        2,
        "only the changed backend SCC and the explicit global metadata plan move"
    );
    let changed_closure_summaries = fs::read_dir(tmp.store_root().join(CLOSURE_SUMMARY_QUERIES))
        .unwrap()
        .count();
    assert_eq!(
        changed_closure_summaries - closure_summaries,
        1,
        "only the changed backend SCC may write a new closure summary"
    );
    let changed_native_objects = fs::read_dir(tmp.store_root().join(NATIVE_OBJECT_QUERIES))
        .unwrap()
        .count();
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
    cfg.flags.compiler_cache = false;
    let report = build_on_report(&changed, &roots, &bin, &cfg).unwrap();
    assert_eq!(report.cache, NativeCacheStatus::Disabled);
    let uncached = fs::read(&bin).unwrap();
    assert_eq!(uncached, changed_cached);
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
    cfg.flags.scc_backend = false;
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
    cfg.flags.compiler_cache = true;
    cfg.flags.quiet = true;
    cfg.flags.store_path = Some(tmp.store_root());

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
    let semantic_bindings = [
        OPTIMIZED_SCC_QUERIES,
        LLVM_SCC_QUERIES,
        CLOSURE_SUMMARY_QUERIES,
    ]
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
    assert_eq!(fs::read(observed_bin).unwrap(), observed_bytes);
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
    incremental_cfg.flags.compiler_cache = true;
    incremental_cfg.flags.store_path = Some(incremental.store_root());
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
    fresh_cfg.flags.compiler_cache = true;
    fresh_cfg.flags.store_path = Some(fresh.store_root());
    let fresh_bin = fresh.join("program");
    build_on_report(&final_source, &roots, &fresh_bin, &fresh_cfg).unwrap();

    let mut parallel_cfg = fresh_cfg.clone();
    parallel_cfg.flags.query_threads = PARALLEL_QUERY_THREADS;
    parallel_cfg.flags.store_path = Some(parallel.store_root());
    let parallel_bin = parallel.join("program");
    build_on_report(&final_source, &roots, &parallel_bin, &parallel_cfg).unwrap();

    let incremental_bytes = fs::read(&incremental_bin).unwrap();
    let fresh_bytes = fs::read(&fresh_bin).unwrap();
    let parallel_bytes = fs::read(&parallel_bin).unwrap();
    assert_eq!(incremental_bytes, fresh_bytes);
    assert_eq!(parallel_bytes, fresh_bytes);

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
        OPTIMIZED_SCC_QUERIES,
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
    sequential_cfg.flags.compiler_cache = true;
    sequential_cfg.flags.store_path = Some(sequential.store_root());
    let mut parallel_cfg = sequential_cfg.clone();
    parallel_cfg.flags.query_threads = PARALLEL_QUERY_THREADS;
    parallel_cfg.flags.store_path = Some(parallel.store_root());

    let sequential_bin = sequential.join("program");
    let parallel_bin = parallel.join("program");
    build_on_report(&src, &roots, &sequential_bin, &sequential_cfg).unwrap();
    build_on_report(&src, &roots, &parallel_bin, &parallel_cfg).unwrap();
    assert_eq!(
        query_bindings(&sequential.store_root(), OPTIMIZED_SCC_QUERIES),
        query_bindings(&parallel.store_root(), OPTIMIZED_SCC_QUERIES),
        "worker count must not alter SCC keys or artifact identities"
    );
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
    assert_eq!(
        fs::read(sequential_bin).unwrap(),
        fs::read(parallel_bin).unwrap()
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
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

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
    let before = with_prelude(
        "fn apply(f : (Int) -> Int, x : Int) = f(x)\n\
         fn left() = apply(\\(x) -> x + 1, 20)\n\
         fn right() = apply(\\(x) -> x * 2, 10)\n\
         fn main() = println(left() + right())\n",
    );
    let after = before.replace("x + 1", "x + 2");
    let mut cfg = Config::default();
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

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
        scc_cfg.flags.compiler_cache = false;
        prism::verify_backend_recomposition_on(&src, &roots, &scc_cfg).unwrap();
        scc_cfg.flags.quiet = true;
        let scc_bin = tmp.join(format!("scc-{index}"));
        build_on_report(&src, &roots, &scc_bin, &scc_cfg).unwrap();

        let mut whole_cfg = scc_cfg.clone();
        whole_cfg.flags.scc_backend = false;
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
    cfg.flags.quiet = true;
    cfg.flags.compiler_cache = true;
    cfg.flags.effect_tier = prism::EffectTier::FreeMonad;
    cfg.flags.store_path = Some(fresh.store_root());
    cfg.session = Some(CompilerSession::new());

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
    assert_eq!(fs::read(&first_bin).unwrap(), first_bytes);
    assert_eq!(second.stdout, first.stdout);
    assert_eq!(second.stderr, first.stderr);
    assert_eq!(second.status.code(), first.status.code());
    assert!(cfg
        .session
        .as_ref()
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
    upgrade_cfg.flags.store_path = Some(upgrade.store_root());
    upgrade_cfg.session = Some(CompilerSession::new());
    let upgrade_bin = upgrade.join("program");
    build_on_report(&src, &roots, &upgrade_bin, &upgrade_cfg).unwrap();
    assert!(upgrade_cfg
        .session
        .as_ref()
        .unwrap()
        .decisions()
        .iter()
        .all(|decision| decision.kind != QueryKind::Effect));
    assert_eq!(
        query_bindings(&upgrade.store_root(), RETIRED_EFFECT_PLAN_QUERIES),
        BTreeMap::from([("legacy-plan".to_string(), "stale plan binding".to_string())]),
        "old plan bindings are inert and remain Store-GC-owned"
    );
    assert_eq!(
        query_bindings(&upgrade.store_root(), RETIRED_EFFECT_RESULT_QUERIES),
        BTreeMap::from([(
            "legacy-result".to_string(),
            "stale result binding".to_string()
        )]),
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
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

    build_on_report(&src, &roots, &tmp.join("first"), &cfg).unwrap();
    let query = fs::read_dir(tmp.store_root().join(LLVM_SCC_QUERIES))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let binding = fs::read_to_string(query).unwrap();
    let object_hash = binding.lines().nth(1).unwrap();
    let object = tmp
        .store_root()
        .join("objects")
        .join(&object_hash[..2])
        .join(&object_hash[2..]);
    fs::write(object, b"corrupt").unwrap();

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
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

    build_on_report(&src, &roots, &tmp.join("first"), &cfg).unwrap();
    let query = fs::read_dir(tmp.store_root().join(CLOSURE_SUMMARY_QUERIES))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let binding = fs::read_to_string(query).unwrap();
    let object_hash = binding.lines().nth(1).unwrap();
    let object = tmp
        .store_root()
        .join("objects")
        .join(&object_hash[..2])
        .join(&object_hash[2..]);
    fs::write(object, b"corrupt").unwrap();

    let error = build_on_report(&src, &roots, &tmp.join("relocated"), &cfg).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("backend SCC closure summary object hash mismatch"),
        "unexpected error: {error}"
    );
}

#[test]
fn corrupt_optimized_scc_is_rejected() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "corrupt-optimized-scc");
    let src = with_prelude("fn main() = println(40 + 2)");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut cfg = Config::default();
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(tmp.store_root());

    build_on_report(&src, &roots, &tmp.join("first"), &cfg).unwrap();
    let query = fs::read_dir(tmp.store_root().join(OPTIMIZED_SCC_QUERIES))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let binding = fs::read_to_string(query).unwrap();
    let object_hash = binding.lines().nth(1).unwrap();
    let object = tmp
        .store_root()
        .join("objects")
        .join(&object_hash[..2])
        .join(&object_hash[2..]);
    fs::write(object, b"corrupt").unwrap();

    let error = build_on_report(&src, &roots, &tmp.join("relocated"), &cfg).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("optimized SCC object hash mismatch"),
        "unexpected error: {error}"
    );
}

#[test]
fn session_semantic_hit_matches_cold_native_build() {
    require_cc();
    let tmp = TempDir::new("compiler-cache", "session-semantic");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let session = CompilerSession::new();
    let mut cfg = Config {
        session: Some(session.clone()),
        ..Config::default()
    };
    cfg.flags.compiler_cache = false;
    let bin = tmp.join("program");
    let source = with_prelude("fn main() = println(42)\n");
    let formatted = format!("{source}\n-- formatting-only edit\n");

    let first = build_on_report(&source, &roots, &bin, &cfg).unwrap();
    assert_eq!(first.cache, NativeCacheStatus::Disabled);
    let cold = fs::read(&bin).unwrap();
    fs::remove_file(&bin).unwrap();
    let second = build_on_report(&formatted, &roots, &bin, &cfg).unwrap();
    assert_eq!(second.cache, NativeCacheStatus::Disabled);
    assert_eq!(fs::read(&bin).unwrap(), cold);
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 1,
            misses: 1,
            writes: 2
        }
    );
}
