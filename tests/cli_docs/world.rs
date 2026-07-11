//! The kernel contracts the PRISM WORLD resident rests on. The shared cellular
//! universe is honest only if these hold: a law's identity is its rule (two
//! different rules are two different content hashes), the evolution is a pure
//! function of seed, law, and tick count (so two same-origin tabs converge to
//! the same state hash), the seed frame is law-independent (so switching a law
//! moves only downstream state, never the shared past), and forking from a grid
//! reproduces exactly (so a branch is real, not painted).

use std::fs;

// Mirrors the sentinel in examples/world.pr and src/wasm.rs: the pure kernel the
// browser reuses is everything above it.
const MAIN_SPLIT: &str = "-- @world:main-below";
const WIDTH: usize = 16;
const HEIGHT: usize = 12;

fn kernel() -> String {
    let src = fs::read_to_string("examples/world.pr").expect("read examples/world.pr");
    src.split(MAIN_SPLIT)
        .next()
        .expect("world.pr carries the world split marker")
        .to_string()
}

fn run(main: &str) -> String {
    let full = prism::with_prelude(&format!("{}\n{main}\n", kernel()));
    prism::interpret(&full)
        .expect("world interprets cleanly")
        .term
}

// The trajectory driver the wasm `world_run` export builds: evolve a seed under
// a law for `ticks` generations, one `<hash> <bits>` line per tick.
fn trace(law: &str, seed: &str, ticks: usize) -> String {
    run(&format!(
        "fn main() = print(trace({WIDTH}, {HEIGHT}, grid_of(\"{seed}\"), step_{law}, {ticks}))"
    ))
}

// A seed that churns under both laws so their evolutions have a chance to
// diverge: an R-pentomino near the centre of a WIDTHxHEIGHT torus.
fn seed() -> String {
    let mut g = vec![b'0'; WIDTH * HEIGHT];
    let (cx, cy) = (WIDTH / 2, HEIGHT / 2);
    for (dx, dy) in [(1, 0), (2, 0), (0, 1), (1, 1), (1, 2)] {
        g[(cy + dy) * WIDTH + (cx + dx)] = b'1';
    }
    String::from_utf8(g).unwrap()
}

// The content hash of a law's step function, exactly as `world_law_hash` reports
// it: the `hash  name` line from the core-hash dump.
fn law_hash(law: &str) -> String {
    let full = prism::with_prelude(&kernel());
    let dump = prism::dump("core-hash", &full).expect("core-hash dump");
    let name = format!("step_{law}");
    dump.lines()
        .find_map(|l| {
            let (hash, def) = l.split_once("  ")?;
            (def.trim() == name).then(|| hash.trim().to_string())
        })
        .unwrap_or_else(|| panic!("no core hash for {name}"))
}

#[test]
fn law_identity_is_its_rule() {
    // Conway and HighLife share survival but differ on birth, so they are two
    // different laws and must carry two different content hashes: this is what
    // makes "the law hash moved" an honest signal when a client switches rules.
    assert_ne!(
        law_hash("conway"),
        law_hash("highlife"),
        "a different birth rule must be a different law hash"
    );
}

#[test]
fn evolution_is_deterministic() {
    // The same seed, law, and tick count evolve to byte-identical frames (hashes
    // included), so two same-origin tabs converge on the same state hash with no
    // coordination.
    let a = trace("conway", &seed(), 24);
    let b = trace("conway", &seed(), 24);
    assert_eq!(a, b, "same seed and law must replay identically");
}

#[test]
fn switching_a_law_moves_only_downstream_state() {
    // The seed frame (tick 0) is the state before any law runs, so it is
    // law-independent: switching the rule cannot rewrite the shared past. The
    // later frames do diverge, or the two rules would be indistinguishable.
    let conway = trace("conway", &seed(), 24);
    let highlife = trace("highlife", &seed(), 24);
    let cw: Vec<&str> = conway.lines().collect();
    let hl: Vec<&str> = highlife.lines().collect();
    assert_eq!(
        cw[0], hl[0],
        "the seed frame (and its hash) must not depend on the law"
    );
    assert_ne!(
        conway, highlife,
        "two different laws must produce different trajectories from the same seed"
    );
}

#[test]
fn forking_from_a_grid_is_pure() {
    // A branch is a pure function of its forked grid and tick count: re-running
    // from the same grid state is byte-identical, and an unperturbed fork at
    // tick N is exactly the tail of the base run, so the shared prefix is real.
    let base = trace("conway", &seed(), 20);
    let lines: Vec<&str> = base.lines().collect();
    let fork_at = 8;
    // A frame line is "<hash> <bits>"; the grid to continue from is its bits.
    let grid = lines[fork_at].split(' ').nth(1).expect("frame bits");
    let a = trace("conway", grid, 20 - fork_at);
    let b = trace("conway", grid, 20 - fork_at);
    assert_eq!(a, b, "same forked grid must replay identically");
    let cont: Vec<&str> = a.lines().collect();
    for k in 0..=(20 - fork_at) {
        assert_eq!(
            cont[k],
            lines[fork_at + k],
            "an unperturbed fork must equal the base run at tick {}",
            fork_at + k
        );
    }
}
