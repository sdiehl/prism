//! Permanent compatibility gates for typed Core.
//!
//! The erasure boundary may move without changing the erased program or its
//! content identity. This test stays independent of the snapshot harness so the
//! compatibility boundary can run in isolation.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use prism::error::{
    Error, ErrorCode, TYPED_CORE_CONSTRUCTION, TYPED_CORE_ENVIRONMENT, TYPED_CORE_ERASURE,
    TYPED_CORE_SPECIALIZATION, TYPED_CORE_VERIFICATION,
};

// The production CLI compiles on an 8 MiB main-thread stack. Debug builds of
// this whole-corpus gate can exceed libtest's smaller worker stack after many
// sequential compilations even though the same corpus passes in release and
// each case passes in isolation. Match the public compiler's finite budget for
// the two corpus gates; focused tests stay on libtest's normal stack so a real
// recursion regression remains visible.
const COMPILER_STACK: usize = 8 * 1024 * 1024;

fn on_compiler_stack(gate: fn()) {
    let result = std::thread::Builder::new()
        .name("typed-spine-corpus".into())
        .stack_size(COMPILER_STACK)
        .spawn(gate)
        .expect("spawning typed-spine corpus gate")
        .join();
    if let Err(payload) = result {
        std::panic::resume_unwind(payload);
    }
}

#[test]
fn typed_erasure_preserves_corpus_core_identity() {
    on_compiler_stack(typed_erasure_preserves_corpus_core_identity_on_compiler_stack);
}

fn typed_erasure_preserves_corpus_core_identity_on_compiler_stack() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = prism::default_roots(root);
    let mut linted_cfg = prism::Config {
        opt: prism::OptLevel::O1,
        ..prism::Config::default()
    };
    linted_cfg.flags.warn_dupes = prism::WarnDupes::Off;
    linted_cfg.flags.warn_stdlib_dupes = prism::WarnDupes::Off;
    linted_cfg.flags.core_lint = true;
    let mut crossed = 0usize;
    let mut crossed_newtypes = 0usize;

    for path in corpus_files(root) {
        let relative = path.strip_prefix(root).expect("corpus path under root");
        let src = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{}: {error}", relative.display()));
        let full = prism::with_prelude(&src);
        let declares_newtype = src
            .lines()
            .any(|line| line.trim_start().starts_with("newtype "));
        let linted = prism::dump_on("core", &full, &roots, &linted_cfg);

        // This public path crosses typed construction, independent
        // verification, and exact erasure equality. Some type-correct negative
        // fixtures intentionally fail a later elaboration precondition; only
        // programs that reach the identity boundary enter this relational gate.
        let dumped = match prism::dump("core-hash", &full) {
            Ok(dumped) => dumped,
            Err(error) => {
                if let Some(canonical) = typed_spine_error_code(&error) {
                    assert_eq!(
                        error.code(),
                        canonical,
                        "{}: typed-spine variant drifted from its canonical code",
                        relative.display()
                    );
                    panic!(
                        "{}: typed spine rejected corpus input: {error}",
                        relative.display()
                    );
                }
                match linted {
                    Ok(_) => panic!(
                        "{}: linted Core front accepted input rejected by the typed identity route: {error}",
                        relative.display()
                    ),
                    Err(linted) => {
                        assert_eq!(
                            error.code(),
                            linted.code(),
                            "{}: expected-negative classification differs between linted Core and typed identity routes",
                            relative.display()
                        );
                        continue;
                    }
                }
            }
        };

        // `store_def_inputs` is the other public, pre-optimization identity
        // front door. Agreement catches a driver route that accidentally hashes
        // a different erased boundary even if each route is deterministic by
        // itself.
        let (_, hashes, _) = prism::store_def_inputs(&full).unwrap_or_else(|error| {
            if let Some(canonical) = typed_spine_error_code(&error) {
                assert_eq!(
                    error.code(),
                    canonical,
                    "{}: store route's typed-spine variant drifted from its canonical code",
                    relative.display()
                );
            }
            panic!("{}: store identity route: {error}", relative.display())
        });
        let mut rows: Vec<_> = hashes.iter().collect();
        rows.sort_by(|(left, _), (right, _)| left.as_str().cmp(right.as_str()));
        let mut store_dump = String::new();
        for (name, hash) in rows {
            writeln!(
                store_dump,
                "{}  {}",
                &hash[..prism::core::HASH_PREFIX_HEX],
                name.as_str()
            )
            .unwrap();
        }
        assert_eq!(
            dumped,
            store_dump,
            "{}: public Core identity routes diverged",
            relative.display()
        );

        crossed += 1;
        crossed_newtypes += usize::from(declares_newtype);
    }

    assert!(
        crossed > 0,
        "no corpus program crossed the typed elaboration boundary"
    );
    assert!(
        crossed_newtypes > 0,
        "no successful newtype-bearing corpus program crossed the typed identity boundary"
    );
}

// The identity gate above deliberately stops before optimization. This second
// gate drives the public FULL front end at an explicit default O1, where
// EraseNewtypes and Specialize form the routed leading prefix and therefore
// cross the typed verifiers plus the E9994/E9993 compatibility differentials.
#[test]
fn full_front_crosses_typed_newtype_prefix_across_corpus() {
    on_compiler_stack(full_front_crosses_typed_newtype_prefix_across_corpus_on_compiler_stack);
}

fn full_front_crosses_typed_newtype_prefix_across_corpus_on_compiler_stack() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = prism::default_roots(root);
    let mut cfg = prism::Config {
        opt: prism::OptLevel::O1,
        ..prism::Config::default()
    };
    cfg.flags.warn_dupes = prism::WarnDupes::Off;
    cfg.flags.warn_stdlib_dupes = prism::WarnDupes::Off;
    let mut linted_cfg = cfg.clone();
    // Core lint gives this gate an independent checker over the same typed
    // route: accepted sources must emit identical Core, while expected
    // negatives must fail under the same canonical diagnostic identity.
    linted_cfg.flags.core_lint = true;
    let mut crossed = 0usize;
    let mut crossed_newtypes = 0usize;
    let mut crossed_specialization = 0usize;

    for path in corpus_files(root) {
        let relative = path.strip_prefix(root).expect("corpus path under root");
        let src = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{}: {error}", relative.display()));
        let full = prism::with_prelude(&src);
        let declares_newtype = src
            .lines()
            .any(|line| line.trim_start().starts_with("newtype "));

        let linted = prism::dump_on("core", &full, &roots, &linted_cfg);
        let typed = prism::dump_on("core", &full, &roots, &cfg);
        match (linted, typed) {
            (_, Err(error)) if typed_spine_error_code(&error).is_some() => {
                let canonical = typed_spine_error_code(&error).expect("matched typed error");
                assert_eq!(
                    error.code(),
                    canonical,
                    "{}: full front's typed-spine variant drifted from its canonical code",
                    relative.display()
                );
                panic!(
                    "{}: typed optimizer prefix rejected corpus input: {error}",
                    relative.display()
                );
            }
            (Ok(linted), Ok(typed)) => {
                assert_eq!(
                    typed,
                    linted,
                    "{}: typed and linted FULL fronts emitted different Core",
                    relative.display()
                );
                crossed += 1;
                crossed_newtypes += usize::from(declares_newtype);
                crossed_specialization += usize::from(typed.contains("$sp"));
            }
            (Err(linted), Ok(_)) => {
                panic!(
                    "{}: typed FULL front accepted input rejected by linted route: {linted}",
                    relative.display()
                );
            }
            (Ok(_), Err(error)) => {
                panic!(
                    "{}: linted FULL front accepted input rejected by typed route: {error}",
                    relative.display()
                );
            }
            (Err(linted), Err(typed)) => {
                assert_eq!(
                    typed.code(),
                    linted.code(),
                    "{}: expected-negative classification differs between linted and typed routes",
                    relative.display()
                );
                if let Some(canonical) = typed_spine_error_code(&typed) {
                    assert_eq!(
                        typed.code(),
                        canonical,
                        "{}: full front's typed-spine variant drifted from its canonical code",
                        relative.display()
                    );
                }
            }
        }
    }

    assert!(crossed > 0, "no corpus program crossed typed EraseNewtypes");
    assert!(
        crossed_newtypes > 0,
        "no successful newtype-bearing corpus program crossed typed EraseNewtypes"
    );
    assert!(
        crossed_specialization > 0,
        "no successful corpus program produced a clone through typed Specialize"
    );
}

#[test]
fn polymorphic_nullary_builder_keeps_one_live_specialized_clone() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = prism::default_roots(root);
    let source = r"import Blit (..)

fn copy_one(src : s, dst : s) : s given Blit(s) = blit(src, 0, 1, dst, 0)

fn ints() : Int =
  array_get(copy_one(array_new(1, 1), array_new(1, 2)), 0)

fn bools() : Bool =
  array_get(copy_one(array_new(1, true), array_new(1, false)), 0)

fn bool_score() : Int = if bools() then 1 else 0

fn main() : Int = ints() + bool_score()
";
    let full = prism::with_prelude(source);
    let typed_cfg = prism::Config {
        opt: prism::OptLevel::O1,
        ..prism::Config::default()
    };
    let mut linted_cfg = typed_cfg.clone();
    linted_cfg.flags.core_lint = true;

    let typed = prism::dump_on("core", &full, &roots, &typed_cfg)
        .expect("typed O1 polymorphic-builder front");
    let linted = prism::dump_on("core", &full, &roots, &linted_cfg)
        .expect("linted O1 polymorphic-builder front");
    assert_eq!(typed, linted, "typed and linted polymorphic specialization");

    let clones = typed
        .lines()
        .filter(|line| line.starts_with("fn copy_one$sp"))
        .count();
    assert_eq!(
        clones, 1,
        "two instantiations of the same polymorphic nullary builder share one clone"
    );

    let o0_cfg = prism::Config {
        opt: prism::OptLevel::O0,
        ..prism::Config::default()
    };
    let o0 = prism::dump_on("core", &full, &roots, &o0_cfg).expect("typed O0 front");
    assert!(
        !o0.contains("copy_one$sp"),
        "O0 must stop after typed EraseNewtypes"
    );

    let mut disabled_cfg = typed_cfg;
    disabled_cfg.flags.no_specialize = true;
    disabled_cfg
        .disabled
        .push(prism::core::CorePass::Specialize);
    let disabled = prism::dump_on("core", &full, &roots, &disabled_cfg)
        .expect("typed O1 front with specialization disabled");
    assert!(
        !disabled.contains("copy_one$sp"),
        "--no-specialize must stop the typed prefix after EraseNewtypes"
    );
}

#[test]
fn higher_order_predicate_under_local_var_retains_its_open_row() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = prism::default_roots(root);
    let source = r"fn scan(start : Int, pred) : Int =
  var i := start
  while i < 3 && pred(i) do
    i += 1
  i

fn main() : Int = scan(0, \(x) -> x < 2)
";
    let full = prism::with_prelude(source);
    let typed_cfg = prism::Config {
        opt: prism::OptLevel::O1,
        ..prism::Config::default()
    };
    let mut linted_cfg = typed_cfg.clone();
    linted_cfg.flags.core_lint = true;

    let typed = prism::dump_on("core", &full, &roots, &typed_cfg)
        .expect("typed higher-order local-var front");
    let linted = prism::dump_on("core", &full, &roots, &linted_cfg)
        .expect("linted higher-order local-var front");
    assert_eq!(typed, linted, "typed local-var row erasure");
}

#[test]
fn effect_polymorphic_traverse_stays_compatibility_exact() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = prism::default_roots(root);
    let source = fs::read_to_string(root.join("examples/effectful_traverse.pr"))
        .expect("effectful traverse example");
    let full = prism::with_prelude(&source);
    let typed_cfg = prism::Config {
        opt: prism::OptLevel::O1,
        ..prism::Config::default()
    };
    let mut linted_cfg = typed_cfg.clone();
    linted_cfg.flags.core_lint = true;
    let typed = prism::dump_on("core", &full, &roots, &typed_cfg)
        .expect("typed effect-polymorphic traverse front");
    let linted = prism::dump_on("core", &full, &roots, &linted_cfg)
        .expect("linted effect-polymorphic traverse front");
    assert_eq!(typed, linted, "typed effect-polymorphic specialization");
}

const fn typed_spine_error_code(error: &Error) -> Option<ErrorCode> {
    match error {
        Error::TypedCoreEnvironment(_) => Some(TYPED_CORE_ENVIRONMENT),
        Error::TypedCoreConstruction(_) => Some(TYPED_CORE_CONSTRUCTION),
        Error::TypedCoreVerification(_) => Some(TYPED_CORE_VERIFICATION),
        Error::TypedCoreErasure(_) => Some(TYPED_CORE_ERASURE),
        Error::TypedCoreSpecialization(_) => Some(TYPED_CORE_SPECIALIZATION),
        _ => None,
    }
}

// There is intentionally no direct `verify` call here yet. `TypedCore`'s
// builders are private and the only externally reachable phase is
// `TypedCore<Elaborated>`, whose builder, verifier, and erasure all run inside
// the identity front doors above. When EffectLowered, Owned, or ReuseLowered
// gains a public driver boundary, add its before/after relational check here;
// do not add a reseatable aggregate corpus hash.
fn corpus_files(root: &Path) -> Vec<PathBuf> {
    fn collect(directory: &Path, files: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(directory)
            .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        {
            let path = entry.expect("corpus directory entry").path();
            if path.is_dir() {
                collect(&path, files);
            } else if path.extension().and_then(|extension| extension.to_str()) == Some("pr") {
                files.push(path);
            }
        }
    }

    let mut files = Vec::new();
    for directory in ["tests/cases", "examples", "lib"] {
        collect(&root.join(directory), &mut files);
    }
    files.sort();
    files
}
