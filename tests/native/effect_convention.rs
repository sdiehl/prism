//! Runtime witnesses for callable conventions across handler and data boundaries.

use std::path::Path;
use std::process::Command;

use prism::driver::effect_strategy_on;
use prism::{
    build_on, default_roots, BackendOpt, Config, EffectStrategy, EffectTier, ObservationTrace,
    OptLevel,
};

use crate::support::{
    check_native_parity, interpreted, leak_free, program_stderr, require_cc, source, TempDir,
    CHECK_LEAKS,
};

const MIXED_CYCLE_CASE: &str = "tests/fixtures/tier_cross/mixed_arity_effect_cycle.pr";
const MIXED_CYCLE_OUTPUT: &str = "15\n";
const DEEP_CYCLE_COUNT: &str = "1000000";
const INTERPRETER_CYCLE_COUNT: &str = "37";
const UNERASED_LOOP_CASES: &[&str] = &[
    "examples/collatz.pr",
    "examples/lexer.pr",
    "tests/cases/run/loop_break.pr",
    "tests/cases/run/while_compound.pr",
];

#[test]
fn pure_closures_can_capture_reified_resumptions() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(root);
    for (opt, backend) in [
        (OptLevel::O0, BackendOpt::O0),
        (OptLevel::default(), BackendOpt::default()),
    ] {
        let mut cfg = Config::default();
        cfg.update_flags(|flags| {
            flags.compiler_cache = false;
            flags.quiet = true;
            flags.erasures = false;
            flags.consolidate = true;
            flags.reify = true;
            flags.opt_level = opt;
            flags.backend_opt = backend;
        });
        let tag = format!("captured-resumption-{opt:?}-{backend:?}");
        for case in UNERASED_LOOP_CASES {
            check_native_parity(&root.join(case), &tag, |source, output| {
                build_on(source, &roots, output, &cfg)
            })
            .unwrap_or_else(|error| panic!("{case}, {tag}: {error}"));
        }
    }
}

/// The literal observations also guard against both compiler paths agreeing
/// on the same wrong answer. Each source is checked by the interpreter first.
const CASES: &[(&str, &str)] = &[
    ("reified_stream_consumer", "true\nfalse\n"),
    ("stored_resume_consumer", "13\n"),
    ("newtype_callable_instantiations", "7\n8\n"),
    ("reified_alias_foreign_row", "605\n"),
    ("reified_after_handle", "305\n"),
    ("reified_inside_handle", "310\n"),
    ("reified_mixed_instantiations", "317\n"),
    ("reified_separate_handlers", "317\n"),
];

#[test]
fn callable_conventions_preserve_observations_across_handlers_and_data() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(root);
    for &(case, expected) in CASES {
        let path = root
            .join("tests/fixtures/tier_cross")
            .join(format!("{case}.pr"));
        let full = source(&path);
        assert_eq!(interpreted(&full), expected, "{case}: interpreter witness");
        for (opt, backend) in [
            (OptLevel::O0, BackendOpt::O0),
            (OptLevel::default(), BackendOpt::default()),
        ] {
            // Explicit controls survive changes to the production defaults.
            for (label, consolidate, reify) in [
                ("cascade", false, false),
                ("direct", true, false),
                ("reified", true, true),
            ] {
                let mut cfg = Config::default();
                cfg.update_flags(|flags| {
                    flags.compiler_cache = false;
                    flags.quiet = true;
                    flags.effect_tier = EffectTier::Auto;
                    flags.consolidate = consolidate;
                    flags.reify = reify;
                    flags.trampoline = true;
                    flags.opt_level = opt;
                    flags.backend_opt = backend;
                });
                let tag = format!("callable-{label}-{opt:?}-{backend:?}");
                if reify {
                    assert_eq!(
                        effect_strategy_on(&full, root, &cfg).unwrap(),
                        EffectStrategy::StateFusion,
                        "{case}, {tag}: the reified implementation must be exercised"
                    );
                }
                check_native_parity(&path, &tag, |source, output| {
                    build_on(source, &roots, output, &cfg)
                })
                .unwrap_or_else(|error| panic!("{case}, {tag}: {error}"));
            }
        }
    }
}

#[test]
fn mixed_arity_effect_cycles_run_in_constant_stack() {
    require_cc();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roots = default_roots(root);
    let full = source(&root.join(MIXED_CYCLE_CASE));
    assert_eq!(full.matches(DEEP_CYCLE_COUNT).count(), 1);
    // The small traversal checks the literal answer against the interpreter;
    // native executions retain the depth that exposes unbounded stack growth.
    let small = full.replacen(DEEP_CYCLE_COUNT, INTERPRETER_CYCLE_COUNT, 1);
    assert_eq!(interpreted(&small), MIXED_CYCLE_OUTPUT);
    let expected = ObservationTrace::from_process(MIXED_CYCLE_OUTPUT.as_bytes(), b"", 0);
    for (opt, backend) in [
        (OptLevel::O0, BackendOpt::O0),
        (OptLevel::default(), BackendOpt::default()),
    ] {
        for reify in [false, true] {
            let mut cfg = Config::default();
            cfg.update_flags(|flags| {
                flags.compiler_cache = false;
                flags.quiet = true;
                flags.effect_tier = if reify {
                    EffectTier::Auto
                } else {
                    EffectTier::WholeProgramFreeMonad
                };
                flags.consolidate = true;
                flags.reify = reify;
                flags.trampoline = true;
                flags.opt_level = opt;
                flags.backend_opt = backend;
            });
            let tag = format!("mixed-cycle-{reify}-{opt:?}-{backend:?}");
            let strategy = if reify {
                EffectStrategy::StateFusion
            } else {
                EffectStrategy::WholeProgramFreeMonad
            };
            assert_eq!(
                effect_strategy_on(&full, root, &cfg).unwrap(),
                strategy,
                "{tag}: the intended implementation must be exercised"
            );
            let temp = TempDir::new("effect-convention", &tag);
            let binary = temp.join("program");
            build_on(&full, &roots, &binary, &cfg).unwrap_or_else(|error| panic!("{tag}: {error}"));
            let run = Command::new(&binary)
                .env(CHECK_LEAKS, "1")
                .output()
                .unwrap();
            let exit = run
                .status
                .code()
                .unwrap_or_else(|| panic!("{tag}: native process faulted: {}", run.status));
            let stderr = String::from_utf8_lossy(&run.stderr);
            assert_eq!(
                ObservationTrace::from_process(
                    &run.stdout,
                    program_stderr(&stderr).as_bytes(),
                    exit,
                ),
                expected,
                "{tag}: wrong observation trace"
            );
            assert!(leak_free(&stderr), "{tag}: {stderr}");
        }
    }
}
