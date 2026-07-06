//! The boids swarm the browser determinism scrubber replays. These pin the
//! property the scrubber's honesty rests on: frame N is a pure function of the
//! step index, byte-identical on every run and independent of how it is reached.

use std::fs;

// Mirrors the sentinel in examples/boids.pr and src/wasm.rs: everything above it
// is the pure kernel the browser reuses, and only the example's own `main` is
// below it. The browser and these tests both append their own entry point.
const MAIN_SPLIT: &str = "-- @scrubber:main-below";

// The boids kernel with the example's `main` stripped, ready for a fresh entry
// point that prints whatever frame the caller wants.
fn kernel() -> String {
    let src = fs::read_to_string("examples/boids.pr").expect("read examples/boids.pr");
    src.split(MAIN_SPLIT)
        .next()
        .expect("boids.pr carries the scrubber split marker")
        .to_string()
}

// Interpret the kernel under `main` and return its exact printed transcript,
// the same bytes the wasm `boids_run` hands the browser.
fn run(main: &str) -> String {
    let full = prism::with_prelude(&format!("{}\n{main}\n", kernel()));
    prism::interpret(&full)
        .expect("boids interprets cleanly")
        .term
}

#[test]
fn trajectory_is_deterministic() {
    let a = run("fn main() = print(run_trace(40))");
    let b = run("fn main() = print(run_trace(40))");
    assert_eq!(
        a, b,
        "same seed and step count must yield the byte-identical trajectory"
    );

    let lines: Vec<&str> = a.lines().collect();
    assert_eq!(
        lines.len(),
        42,
        "a header line plus 41 frames (steps 0..=40)"
    );
    assert_eq!(
        lines[0], "100000 100000",
        "header is the toroidal world size"
    );
    assert_eq!(lines[1].split(' ').count(), 32, "32 boids per frame");
}

#[test]
fn replay_to_n_is_pure() {
    // The scrubber's contract: dragging to frame N shows exactly the state that
    // results from replaying steps 0..N. `run_trace` builds the whole trajectory
    // with a left scan; `frame_at` recomputes frame N alone by iterating `step`.
    // The two paths must agree, so the playhead position is a pure function of N.
    let trace = run("fn main() = print(run_trace(25))");
    let frame_n = run("fn main() = print(frame_obs(frame_at(25)))");
    let nth = trace
        .lines()
        .nth(26)
        .expect("frame 25 line (header + steps 0..25)");
    assert_eq!(
        nth,
        frame_n.trim_end(),
        "replay-to-N must equal the independently recomputed frame N"
    );
}
