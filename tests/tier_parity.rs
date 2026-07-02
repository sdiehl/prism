// Tier-invisibility oracle: the effect-lowering cascade is a pure cost
// decision, so forcing a program onto a slower tier must not change one byte
// of observable output. `PRISM_EFFECT_TIER` (here set programmatically via
// `Config.flags.effect_tier`) caps the cascade; for every corpus program whose
// forced classification differs from its natural one, this gate builds the
// forced native binary and diffs its stdout (and leak report) against the
// interpreter. `tests/parity.rs` pins native(auto) == interp over the same
// corpus, so the two gates together give native(auto) == native(forced):
// tier-vs-tier agreement, enforced rather than argued.
//
// Programs whose classification does not move under forcing are skipped: their
// forced build is byte-identical to the natural one parity.rs already diffs.
// A floor on the exercised count keeps the oracle from going vacuous if the
// forcing knob or the strategy classifier silently breaks.

use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::{env, fs, thread};

use prism::{default_roots, Config, EffectTier};

mod common;
use common::{corpus, interpreted, require_cc, source};

fn forced(tier: EffectTier) -> Config {
    let mut cfg = Config::from_env();
    cfg.flags.effect_tier = tier;
    cfg
}

// Build `case` under the forced tier and diff its run against the interpreter,
// mirroring parity.rs (stdout byte equality, zero leaked cells).
fn check_forced(case: &Path, tag: &str, cfg: &Config) -> Result<(), String> {
    let full = source(case);
    let stem = case.file_stem().unwrap().to_string_lossy();
    let bin = env::temp_dir().join(format!("prism_tier_{tag}_{}_{stem}", std::process::id()));
    let fail = |msg: String| {
        for ext in ["bc", "ll"] {
            let _ = fs::remove_file(bin.with_extension(ext));
        }
        let _ = fs::remove_file(&bin);
        Err(msg)
    };
    if let Err(e) = prism::build_on(&full, &default_roots(Path::new(".")), &bin, cfg) {
        return fail(format!(
            "{}: forced {tag} build failed: {e}",
            case.display()
        ));
    }
    let out = match Command::new(&bin).env("PRISM_CHECK_LEAKS", "1").output() {
        Ok(o) => o,
        Err(e) => return fail(format!("{}: spawn failed: {e}", case.display())),
    };
    for ext in ["bc", "ll"] {
        let _ = fs::remove_file(bin.with_extension(ext));
    }
    let _ = fs::remove_file(&bin);
    let got = String::from_utf8_lossy(&out.stdout);
    let want = interpreted(&full);
    if got != want {
        return Err(format!(
            "forced {tag} output diverges for {}:\n  native: {got:?}\n  interp: {want:?}",
            case.display()
        ));
    }
    let leak = String::from_utf8_lossy(&out.stderr);
    let leak_line = leak
        .lines()
        .find(|l| l.contains("cells leaked"))
        .unwrap_or("")
        .trim();
    if leak_line != "prism: 0 cells leaked" {
        return Err(format!(
            "forced {tag}: {} did not free all cells: {}",
            case.display(),
            leak.trim()
        ));
    }
    Ok(())
}

// Force `tier` over the corpus, exercising exactly the programs whose lowering
// strategy moves under the cap, and require at least `floor` of them so the
// oracle cannot silently become vacuous.
fn run_forced(tag: &str, tier: EffectTier, floor: usize) {
    require_cc();
    let auto_cfg = Config::from_env();
    let forced_cfg = forced(tier);
    let base = Path::new(".");
    let cases: Vec<_> = corpus()
        .into_iter()
        .filter(|case| {
            let full = source(case);
            let auto = prism::effect_strategy_on(&full, base, &auto_cfg);
            let hard = prism::effect_strategy_on(&full, base, &forced_cfg);
            match (auto, hard) {
                (Ok(a), Ok(h)) => a != h,
                // A strategy error under exactly one config is itself a tier
                // divergence; keep the case so the build surfaces it.
                _ => true,
            }
        })
        .collect();
    assert!(
        cases.len() >= floor,
        "forcing {tag} moved only {} corpus programs off their natural tier \
         (floor {floor}); the forcing knob or strategy classifier likely broke",
        cases.len()
    );
    let next = AtomicUsize::new(0);
    let fails: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let threads = thread::available_parallelism()
        .map_or(4, std::num::NonZeroUsize::get)
        .min(cases.len());
    thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                let Some(case) = cases.get(i) else { break };
                if let Err(e) = check_forced(case, tag, &forced_cfg) {
                    fails.lock().unwrap().push(e);
                }
            });
        }
    });
    let fails = fails.into_inner().unwrap();
    assert!(
        fails.is_empty(),
        "{} of {} forced-{tag} cases diverged from the interpreter:\n{}",
        fails.len(),
        cases.len(),
        fails.join("\n")
    );
}

#[test]
fn forced_free_monad_matches_interpreter() {
    run_forced("free-monad", EffectTier::FreeMonad, 10);
}

#[test]
fn forced_state_matches_interpreter() {
    run_forced("state", EffectTier::State, 3);
}
