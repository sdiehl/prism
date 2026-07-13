use std::collections::BTreeMap;
use std::fs;

use prism::{check_modules_on, CompilerSession, Config, DynFlags, Root, SessionStats};

const SEQUENTIAL_THREADS: usize = 1;
const PARALLEL_THREADS: usize = 4;
const ROOT: &str = "import A\nfn main() : Int = A.total()\n";
const BEFORE_VALUE: i64 = 41;
const AFTER_VALUE: i64 = 42;
const EXPECTED_CUTOFF_HITS: u64 = 3;
const EXPECTED_CUTOFF_MISSES: u64 = 5;
const EXPECTED_CUTOFF_WRITES: u64 = 5;
const CHECKED_BODY_QUERY_DIR: &str = "queries/checked-body";
const MODULE_DECISION_DIR: &str = "decisions/query-facts";
const CORRUPT_QUERY_ENTRY: &str = "prism-query-index-v1\nnot-a-hash\n";

fn roots(b_value: i64) -> Vec<Root> {
    vec![Root::source_bundle(
        "modules".to_string(),
        BTreeMap::from([
            (
                "A".to_string(),
                "import B\nimport C\npub fn total() : Int = B.value() + C.value()\n".to_string(),
            ),
            (
                "B".to_string(),
                format!("pub fn value() : Int = {b_value}\n"),
            ),
            ("C".to_string(), "pub fn value() : Int = 1\n".to_string()),
        ]),
    )]
}

fn config(threads: usize) -> Config {
    Config {
        flags: DynFlags {
            query_threads: threads,
            compiler_cache: false,
            ..DynFlags::default()
        },
        ..Config::default()
    }
}

fn session_config(threads: usize, session: CompilerSession) -> Config {
    Config {
        session: Some(session),
        ..config(threads)
    }
}

#[test]
fn module_queries_typecheck_from_interfaces_in_deterministic_parallel_layers() {
    let sequential =
        check_modules_on(ROOT, &roots(BEFORE_VALUE), &config(SEQUENTIAL_THREADS)).unwrap();
    let parallel = check_modules_on(ROOT, &roots(BEFORE_VALUE), &config(PARALLEL_THREADS)).unwrap();

    let sequential_interfaces = sequential
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module.interface.to_json().unwrap()))
        .collect::<Vec<_>>();
    let parallel_interfaces = parallel
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module.interface.to_json().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(parallel_interfaces, sequential_interfaces);
    assert_eq!(parallel.decisions, sequential.decisions);
    assert_eq!(
        parallel
            .root
            .decls
            .first()
            .expect("parallel root")
            .ty
            .show(),
        sequential
            .root
            .decls
            .first()
            .expect("sequential root")
            .ty
            .show()
    );
}

#[test]
fn private_dependency_edit_preserves_importer_interfaces() {
    let session = CompilerSession::new();
    let cfg = session_config(PARALLEL_THREADS, session.clone());
    let before = check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).unwrap();
    let after = check_modules_on(ROOT, &roots(AFTER_VALUE), &cfg).unwrap();
    let before_interfaces = before
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module.interface.digest.as_str()))
        .collect::<Vec<_>>();
    let after_interfaces = after
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module.interface.digest.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(after_interfaces, before_interfaces);
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: EXPECTED_CUTOFF_HITS,
            misses: EXPECTED_CUTOFF_MISSES,
            writes: EXPECTED_CUTOFF_WRITES
        }
    );
}

#[test]
fn prelude_backed_project_modules_use_the_cached_standard_foundation() {
    let source = prism::with_prelude(ROOT);
    let mut module_roots = roots(BEFORE_VALUE);
    module_roots.push(Root::Embedded(prism::stdlib::STDLIB));
    let report = check_modules_on(&source, &module_roots, &config(PARALLEL_THREADS)).unwrap();
    assert!(report.modules.iter().any(|module| module.name == "A"));
    assert!(report.root.decls.iter().any(|decl| decl.name == "main"));
}

#[test]
fn durable_checked_bodies_rehydrate_without_typechecking() {
    let store =
        std::env::temp_dir().join(format!("prism-module-interfaces-{}", std::process::id()));
    let _ = fs::remove_dir_all(&store);
    let mut cfg = config(PARALLEL_THREADS);
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(store.clone());

    let cold = check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).unwrap();
    assert_eq!(cold.modules.len(), 3);
    assert!(!cold.root_reused);
    assert!(cold.decisions.iter().all(|decision| !decision.reused));
    assert!(cold
        .decisions
        .iter()
        .all(|decision| { decision.reasons == ["no previous successful module query"] }));

    let warm = check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).unwrap();
    assert_eq!(warm.modules.len(), cold.modules.len());
    assert!(warm.root_reused);
    assert!(warm.modules.iter().all(|module| module.reused));
    assert!(warm.decisions.iter().all(|decision| decision.reused));
    assert!(warm
        .decisions
        .iter()
        .all(|decision| decision.reasons.is_empty()));
    assert_eq!(
        warm.root
            .decls
            .first()
            .expect("warm root declaration")
            .ty
            .show(),
        cold.root
            .decls
            .first()
            .expect("cold root declaration")
            .ty
            .show()
    );
    assert_eq!(
        warm.root.eff_ops.keys().collect::<Vec<_>>(),
        cold.root.eff_ops.keys().collect::<Vec<_>>()
    );

    let private_edit = check_modules_on(ROOT, &roots(AFTER_VALUE), &cfg).unwrap();
    assert!(private_edit.root_reused);
    let b_decision = private_edit
        .decisions
        .iter()
        .find(|decision| decision.module == "B")
        .expect("B decision");
    assert!(!b_decision.reused);
    assert_eq!(
        b_decision.reasons,
        [
            "module tokens changed",
            "public interface remained unchanged"
        ]
    );
    assert!(private_edit
        .decisions
        .iter()
        .filter(|decision| decision.module != "B")
        .all(|decision| decision.reused));
    assert_eq!(
        private_edit
            .modules
            .iter()
            .filter(|module| !module.reused)
            .map(|module| module.name.as_str())
            .collect::<Vec<_>>(),
        vec!["B"]
    );
    fs::remove_dir_all(store).unwrap();
}

#[test]
fn durable_checked_hir_rehydrates_resolution_facts() {
    let store = std::env::temp_dir().join(format!("prism-checked-hir-{}", std::process::id()));
    let _ = fs::remove_dir_all(&store);
    let module_roots = vec![Root::source_bundle(
        "hir-modules".to_string(),
        BTreeMap::from([(
            "B".to_string(),
            "pub type Point = Point { x: Int }\n\
             pub fn point() : Point = Point { x = 42 }\n\
             pub fn read(p : Point) : Int = p.x\n"
                .to_string(),
        )]),
    )];
    let mut cfg = config(PARALLEL_THREADS);
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(store.clone());
    let root = "import B\nfn main() : Int = B.read(B.point())\n";

    let cold = check_modules_on(root, &module_roots, &cfg).unwrap();
    let warm = check_modules_on(root, &module_roots, &cfg).unwrap();
    assert_eq!(cold.modules.len(), 1);
    assert!(warm.modules[0].reused);
    assert!(prism::hir::lint::lint_hir(&prism::hir::build(&warm.modules[0].checked)).is_empty());
    let read_type = |module: &prism::CheckedModule| {
        module
            .checked
            .decls
            .iter()
            .find(|decl| decl.name == "B.read")
            .expect("B.read declaration")
            .ty
            .show()
    };
    assert_eq!(read_type(&cold.modules[0]), read_type(&warm.modules[0]));
    fs::remove_dir_all(store).unwrap();
}

#[test]
fn deriving_module_uses_interface_scope_and_durable_checked_body() {
    let store = std::env::temp_dir().join(format!("prism-derived-body-{}", std::process::id()));
    let _ = fs::remove_dir_all(&store);
    let mut module_roots = vec![Root::source_bundle(
        "derived-modules".to_string(),
        BTreeMap::from([(
            "Shape".to_string(),
            "pub type Shape = Circle(Int) | Square(Int) deriving (Eq)\n\
             pub fn circle(n : Int) : Shape = Circle(n)\n"
                .to_string(),
        )]),
    )];
    module_roots.push(Root::Embedded(prism::stdlib::STDLIB));
    let source = prism::with_prelude(
        "import Shape\nfn main() : Bool = eq(Shape.circle(1), Shape.circle(1))\n",
    );
    let mut cfg = config(PARALLEL_THREADS);
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(store.clone());

    let cold = check_modules_on(&source, &module_roots, &cfg).unwrap();
    assert_eq!(cold.modules.len(), 1);
    assert_eq!(cold.modules[0].name, "Shape");
    let warm = check_modules_on(&source, &module_roots, &cfg).unwrap();
    assert!(warm.modules[0].reused);
    assert!(prism::hir::lint::lint_hir(&prism::hir::build(&warm.modules[0].checked)).is_empty());
    fs::remove_dir_all(store).unwrap();
}

#[test]
fn malformed_module_decision_is_rejected() {
    let store = std::env::temp_dir().join(format!(
        "prism-module-decisions-corrupt-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&store);
    let mut cfg = config(PARALLEL_THREADS);
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(store.clone());
    check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).unwrap();

    let decision = fs::read_dir(store.join(MODULE_DECISION_DIR))
        .unwrap()
        .next()
        .expect("module decision")
        .unwrap()
        .path();
    fs::write(decision, b"not-a-decision").unwrap();
    let error = check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).unwrap_err();
    assert!(error
        .to_string()
        .contains("query decision has an unknown format"));
    fs::remove_dir_all(store).unwrap();
}

#[test]
fn malformed_durable_checked_body_query_is_rejected() {
    let store = std::env::temp_dir().join(format!(
        "prism-module-interfaces-corrupt-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&store);
    let mut cfg = config(PARALLEL_THREADS);
    cfg.flags.compiler_cache = true;
    cfg.flags.store_path = Some(store.clone());
    check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).unwrap();

    let query = fs::read_dir(store.join(CHECKED_BODY_QUERY_DIR))
        .unwrap()
        .next()
        .expect("checked body query")
        .unwrap()
        .path();
    fs::write(query, CORRUPT_QUERY_ENTRY).unwrap();
    assert!(check_modules_on(ROOT, &roots(BEFORE_VALUE), &cfg).is_err());
    fs::remove_dir_all(store).unwrap();
}
