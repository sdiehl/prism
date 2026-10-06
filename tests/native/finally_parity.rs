// A handler's `finally` clause, native. Whole-program free-monad lowering
// honours it everywhere; state fusion honours it unless a catching clause does
// something, since an abandoned cleanup there runs as the abort propagates;
// pure lowering takes a bracket in a program that performs nothing. The other
// rungs decline it, so on every forced floor the native run must observe what
// the interpreter does, cleanup lines included and in the same order. The
// clause's degenerate sibling, a handler that catches nothing and has no
// cleanup, rides along: it is plain sequencing on every rung.

use std::path::{Path, PathBuf};

use prism::{EffectStrategy, EffectTier};

use crate::support::{check_native_parity, parallel_check, require_cc, source};

const FIXTURES: &str = "tests/fixtures/language/finally";

// The programs and the rung each lands on when no floor is forced.
const PROGRAMS: &[(&str, EffectStrategy)] = &[
    ("well_typed", EffectStrategy::StateFusion),
    ("pure_bracket", EffectStrategy::Pure),
    ("abandoned", EffectStrategy::StateFusion),
    ("resumed_across", EffectStrategy::StateFusion),
    ("nested", EffectStrategy::StateFusion),
    ("return_aborts", EffectStrategy::WholeProgramFreeMonad),
    ("masked", EffectStrategy::WholeProgramFreeMonad),
    ("reentered", EffectStrategy::WholeProgramFreeMonad),
    ("once_clauses", EffectStrategy::StateFusion),
    ("replayed", EffectStrategy::WholeProgramFreeMonad),
    ("catches_nothing", EffectStrategy::StateFusion),
    ("loud_catcher", EffectStrategy::WholeProgramFreeMonad),
];

fn paths() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURES);
    PROGRAMS
        .iter()
        .map(|(name, _)| root.join(format!("{name}.pr")))
        .collect()
}

#[test]
fn cleanup_programs_land_on_the_rungs_that_honour_the_clause() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for ((name, expected), path) in PROGRAMS.iter().zip(paths()) {
        let tier = prism::effect_strategy_full(&source(&path), root)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(tier, *expected, "{name}");
    }
}

#[test]
fn cleanup_programs_agree_with_the_interpreter_on_every_floor() {
    require_cc();
    let paths = paths();
    let roots = prism::default_roots(Path::new("."));
    let mut fails = Vec::new();
    for &tier in &EffectTier::ALL {
        let cfg = crate::forced(tier, true);
        let tag = format!("finally-{}", tier.label());
        let (roots, cfg) = (&roots, &cfg);
        fails.extend(parallel_check(&paths, |case| {
            check_native_parity(case, &tag, |full, bin| {
                prism::build_on(full, roots, bin, cfg)
            })
        }));
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
