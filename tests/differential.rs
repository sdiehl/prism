//! The differential oracles: optimizer-configuration equivalence, effect-tier
//! equivalence, typed-spine erasure identity, the Lean model cross-check,
//! replay determinism, and the runtime scrubber and suspension suites.

mod support;

#[path = "differential/determinism.rs"]
mod determinism;
#[path = "opt_equiv/gate.rs"]
mod gate;
#[path = "differential/lean_fuzz.rs"]
mod lean_fuzz;
#[path = "tier_equiv/gate.rs"]
mod tier_gate;
#[path = "differential/typed_spine.rs"]
mod typed_spine;

#[path = "runtime/boids_branch.rs"]
mod boids_branch;
#[path = "runtime/boids_scrubber.rs"]
mod boids_scrubber;
#[path = "runtime/chaos_swarm.rs"]
mod chaos_swarm;
#[path = "runtime/cli_replay.rs"]
mod cli_replay;
#[path = "runtime/kont_suspend.rs"]
mod kont_suspend;
#[path = "runtime/pendulum_scrubber.rs"]
mod pendulum_scrubber;
#[path = "runtime/showcase.rs"]
mod showcase;
#[path = "runtime/stable_block.rs"]
mod stable_block;
#[path = "runtime/time_json.rs"]
mod time_json;
