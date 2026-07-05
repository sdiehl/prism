//! The run-from-state contract the branching-timelines demo (B5) rests on. The
//! scrubber replays to N; branching continues a run FROM a (perturbed) frame N.
//! These pin what makes the two side-by-side timelines honest: a branch is a
//! pure function of its forked state and step count, and an unperturbed fork is
//! exactly the tail of the base run, so the shared prefix is real, not painted.

use std::fs;

// Mirrors the sentinel in examples/boids.pr and src/wasm.rs: the pure kernel the
// browser reuses is everything above it.
const MAIN_SPLIT: &str = "-- @scrubber:main-below";

fn kernel() -> String {
    let src = fs::read_to_string("examples/boids.pr").expect("read examples/boids.pr");
    src.split(MAIN_SPLIT)
        .next()
        .expect("boids.pr carries the scrubber split marker")
        .to_string()
}

fn run(main: &str) -> String {
    let full = prism::with_prelude(&format!("{}\n{main}\n", kernel()));
    prism::interpret(&full)
        .expect("boids interprets cleanly")
        .term
}

// Turn one full-state frame line ("x,y,vx,vy x,y,vx,vy ...") into the Prism list
// literal `[(x,y,vx,vy), ...]` the run-from driver takes, exactly as the wasm
// `boids_run_from` export does. The frontend forks by handing such a literal
// (after perturbing it) to `run_trace_from`.
fn swarm_literal(frame: &str) -> String {
    let tuples: Vec<String> = frame.split_whitespace().map(|b| format!("({b})")).collect();
    format!("[{}]", tuples.join(","))
}

#[test]
fn run_from_state_is_pure() {
    // Continuing from the same swarm and step count is byte-identical: a branch
    // reproduces exactly, which is the whole determinism claim of the demo.
    let full = run("fn main() = print(run_trace_full(20))");
    let mid = full.lines().nth(11).expect("full frame at step 10");
    let lit = swarm_literal(mid);
    let a = run(&format!("fn main() = print(run_trace_from({lit}, 15))"));
    let b = run(&format!("fn main() = print(run_trace_from({lit}, 15))"));
    assert_eq!(
        a, b,
        "same forked state and step count must replay identically"
    );
}

#[test]
fn unperturbed_fork_is_the_base_tail() {
    // Fork at step N WITHOUT perturbing: continuing from frame N must reproduce
    // the base run's steps N.. exactly. This is what makes the shared prefix and
    // the seam at the fork honest (the branch only diverges because of the poke,
    // never because run-from-state drifts from replay-to-N).
    let full = run("fn main() = print(run_trace_full(30))");
    let lines: Vec<&str> = full.lines().collect();
    let fork_at = 12;
    let lit = swarm_literal(lines[fork_at + 1]); // +1 for the header line
    let cont = run(&format!(
        "fn main() = print(run_trace_from({lit}, {}))",
        30 - fork_at
    ));
    let cont_lines: Vec<&str> = cont.lines().collect();
    assert_eq!(cont_lines[0], "100000 100000", "same header");
    // cont frame k is base frame (fork_at + k); the base tail starts at line
    // (fork_at + 1) after the header.
    for k in 0..=(30 - fork_at) {
        assert_eq!(
            cont_lines[k + 1],
            lines[fork_at + 1 + k],
            "unperturbed continuation must equal the base run at step {}",
            fork_at + k
        );
    }
}

#[test]
fn perturbing_one_boid_diverges() {
    // Reversing one boid's velocity (the demo's poke) must eventually change the
    // observable flock: a single perturbed agent cascades. Without divergence the
    // branch would be a visual duplicate and the interaction would be a lie.
    let full = run("fn main() = print(run_trace_full(40))");
    let lines: Vec<&str> = full.lines().collect();
    let fork_at = 10;
    let base_frame = lines[fork_at + 1];

    // Reverse boid 0's vx,vy, leave the rest untouched (mirrors branch.ts perturb).
    let boids: Vec<&str> = base_frame.split_whitespace().collect();
    let first: Vec<i64> = boids[0].split(',').map(|f| f.parse().unwrap()).collect();
    let poked = format!("{},{},{},{}", first[0], first[1], -first[2], -first[3]);
    let mut perturbed = vec![poked];
    perturbed.extend(boids[1..].iter().map(|s| (*s).to_string()));
    let lit = swarm_literal(&perturbed.join(" "));

    let base_tail = run(&format!(
        "fn main() = print(run_trace_from({}, {}))",
        swarm_literal(base_frame),
        40 - fork_at
    ));
    let poked_run = run(&format!(
        "fn main() = print(run_trace_from({lit}, {}))",
        40 - fork_at
    ));
    assert_ne!(
        base_tail, poked_run,
        "reversing one boid must change the trajectory within the window"
    );
}
