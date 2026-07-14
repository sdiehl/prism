//! Compile-time baseline corpus.
//!
//! A pinned, feature-spanning set of example programs, each measured end to end
//! through `core_of` (lex, parse, resolve, desugar, typecheck, elaborate, and the
//! pre-optimizer). The point is a stable baseline: later perf work compares
//! against recorded numbers rather than guesses, so add programs deliberately and
//! keep the set fixed, so one label means the same thing release over release.

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use std::hint::black_box;

// (label, source), chosen to span distinct front-end costs: tail recursion,
// dictionary passing, effect handlers, stream fusion, expression parsing, a
// self-balancing structure, divide and conquer, backtracking, bignum arithmetic,
// a tagless-final encoding, and one large program for scaling.
const CORPUS: &[(&str, &str)] = &[
    ("accum", include_str!("../examples/accum.pr")),
    ("classes", include_str!("../examples/classes.pr")),
    ("effects", include_str!("../examples/effects.pr")),
    ("stream_fuse", include_str!("../examples/stream_fuse.pr")),
    ("calc", include_str!("../examples/calc.pr")),
    ("json", include_str!("../examples/json.pr")),
    ("rbtree", include_str!("../examples/rbtree.pr")),
    ("mergesort", include_str!("../examples/mergesort.pr")),
    ("queens", include_str!("../examples/queens.pr")),
    ("bignum", include_str!("../examples/bignum.pr")),
    ("tagless", include_str!("../examples/tagless.pr")),
    ("boids", include_str!("../examples/boids.pr")),
];

fn compile(c: &mut Criterion) {
    let mut group = c.benchmark_group("core_of");
    for (name, src) in CORPUS {
        // A program that stops compiling would silently turn into an error-path
        // timing and poison the baseline; fail loudly instead.
        assert!(
            prism::core_of(src).is_ok(),
            "corpus program `{name}` no longer compiles"
        );
        group.bench_with_input(BenchmarkId::from_parameter(name), src, |b, src| {
            b.iter(|| prism::core_of(black_box(src)).expect("compile"));
        });
    }
    group.finish();
}

fn session_config() -> prism::Config {
    prism::Config {
        session: Some(prism::CompilerSession::new()),
        ..prism::Config::default()
    }
}

fn query_compile(c: &mut Criterion) {
    let source = prism::with_prelude(include_str!("../examples/accum.pr"));
    let edited = format!("{source}\n-- pinned small edit\n");
    let roots = [prism::Root::Embedded(prism::stdlib::STDLIB)];
    let mut group = c.benchmark_group("query_compile");

    group.bench_function("cold", |b| {
        b.iter_batched(
            session_config,
            |cfg| prism::check_on_in(black_box(&source), &roots, &cfg).expect("cold check"),
            BatchSize::SmallInput,
        );
    });

    let warm_cfg = session_config();
    prism::check_on_in(&source, &roots, &warm_cfg).expect("seed warm check");
    group.bench_function("warm", |b| {
        b.iter(|| prism::check_on_in(black_box(&source), &roots, &warm_cfg).expect("warm check"));
    });

    group.bench_function("small_edit", |b| {
        b.iter_batched(
            || {
                let cfg = session_config();
                prism::check_on_in(&source, &roots, &cfg).expect("seed small-edit check");
                cfg
            },
            |cfg| prism::check_on_in(black_box(&edited), &roots, &cfg).expect("edited check"),
            BatchSize::SmallInput,
        );
    });
    group.finish();
}

criterion_group!(benches, compile, query_compile);
criterion_main!(benches);
