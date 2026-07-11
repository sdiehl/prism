//! The double pendulum the browser determinism scrubber replays. These check
//! the property the scrubber's honesty rests on: frame N is a pure function of
//! the step index, byte-identical on every run, and the symplectic integrator
//! holds energy, so the chaos on screen is dynamics rather than integrator drift.

use std::fs;

// Mirrors the sentinel in examples/pendulum.pr and src/wasm.rs: everything above
// it is the pure kernel the browser reuses, and only the example's own `main` is
// below it. The browser and these tests both append their own entry point.
const MAIN_SPLIT: &str = "-- @scrubber:main-below";

fn kernel() -> String {
    let src = fs::read_to_string("examples/pendulum.pr").expect("read examples/pendulum.pr");
    src.split(MAIN_SPLIT)
        .next()
        .expect("pendulum.pr carries the scrubber split marker")
        .to_string()
}

// Interpret the kernel under `main` and return its exact printed transcript, the
// same bytes the wasm `pendulum_run` hands the browser.
fn run(main: &str) -> String {
    let full = prism::with_prelude(&format!("{}\n{main}\n", kernel()));
    prism::interpret(&full)
        .expect("pendulum interprets cleanly")
        .term
}

#[test]
fn trajectory_is_deterministic() {
    let a = run("fn main() = print(run_trace(60))");
    let b = run("fn main() = print(run_trace(60))");
    assert_eq!(
        a, b,
        "the chaotic trajectory must replay to byte-identical output"
    );

    let lines: Vec<&str> = a.lines().collect();
    assert_eq!(
        lines.len(),
        62,
        "a reach header plus 61 frames (steps 0..=60)"
    );
    assert_eq!(
        lines[0], "2.00000",
        "header is the pendulum's maximum reach"
    );
    assert_eq!(
        lines[1].split(',').count(),
        4,
        "each frame is x1,y1,x2,y2 bob positions"
    );
}

#[test]
fn replay_to_n_is_pure() {
    // The scrubber's contract: dragging to frame N shows exactly the state that
    // results from replaying from step 0. `run_trace` builds the whole trajectory
    // with a left scan; `frame_at` recomputes frame N alone by iterating the
    // integrator. The two paths must agree, so the playhead is a pure function of N.
    let trace = run("fn main() = print(run_trace(40))");
    let frame_n = run("fn main() = print(obs(frame_at(40)))");
    let nth = trace
        .lines()
        .nth(41)
        .expect("frame 40 line (reach header + steps 0..40)");
    assert_eq!(
        nth,
        frame_n.trim_end(),
        "replay-to-N must equal the independently recomputed frame N"
    );
}

#[test]
fn integrator_conserves_energy() {
    // The honesty claim: the on-screen chaos is the dynamics, not the integrator
    // pumping energy in. Over the full 300-frame demo window (6 s of simulated
    // time) the total energy must stay within a fraction of a percent of its
    // initial value. A bug in the forces or a too-coarse step shows up here.
    let drift = run("fn main() = print(show_float_prec(energy(frame_at(300)) - energy(init), 4))");
    let d: f64 = drift.trim().parse().expect("energy drift is a float");
    assert!(
        d.abs() < 0.05,
        "energy drifted by {d} over 300 frames; expected under 0.05 (E0 is ~21.7)"
    );
}
