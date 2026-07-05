//! The concurrent swarm behind the chaos counter (B5). These pin the headline
//! the counter renders: N hostile seeded-shuffle schedules of the same fibers
//! over the same channel land on a byte-identical final state, while the
//! interleavings genuinely differ. The claim (all schedules agree) is the
//! determinism theorem made observable; the count is only budget-bounded.

use std::fs;

const MAIN_SPLIT: &str = "-- @chaos:main-below";

fn kernel() -> String {
    let src = fs::read_to_string("examples/chaos_swarm.pr").expect("read examples/chaos_swarm.pr");
    src.split(MAIN_SPLIT)
        .next()
        .expect("chaos_swarm.pr carries the chaos split marker")
        .to_string()
}

fn run(main: &str) -> String {
    let full = prism::with_prelude(&format!("{}\n{main}\n", kernel()));
    prism::interpret(&full)
        .expect("chaos_swarm interprets cleanly")
        .term
}

#[test]
fn every_schedule_agrees() {
    // The reference is seed index 0; a batch of 40 schedules must ALL match it.
    // `batch_report` returns "<agreed> <count> <refhash>" on its first line.
    let out = run("fn main() = print(batch_report(0, 40, n_workers))");
    let header = out.lines().next().expect("batch report header");
    let fields: Vec<&str> = header.split(' ').collect();
    assert_eq!(fields[0], fields[1], "every schedule must agree ({header})");
    assert_eq!(fields[1], "40", "the batch ran the requested 40 schedules");
}

#[test]
fn interleavings_actually_differ() {
    // The two sample schedules the report prints must not be identical: if the
    // shuffle produced the same order the demo would be claiming order-
    // independence over a single order, which proves nothing.
    let out = run("fn main() = print(batch_report(0, 2, n_workers))");
    let lines: Vec<&str> = out.lines().collect();
    assert_ne!(
        lines[1], lines[2],
        "distinct seeds must yield distinct interleavings"
    );
}

#[test]
fn one_schedule_is_deterministic() {
    // A single seed is a pure function: same seed, byte-identical schedule and
    // final state, which is what lets the browser replay a schedule.
    let a = run("fn main() = print(batch_report(3, 1, n_workers))");
    let b = run("fn main() = print(batch_report(3, 1, n_workers))");
    assert_eq!(a, b, "a fixed seed must reproduce exactly");
}
