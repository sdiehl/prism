// Cross-tier handler-equivalence oracle: the generative generalization of the
// duplicate-handler-clause bug. The effect-lowering cascade is a pure cost
// decision, so a handler-using program must produce byte-identical output no
// matter which rung fires: evidence fusion (auto), state fusion (state), or
// whole-program free-monad reification (free-monad). The original divergence (a
// duplicate clause only the free-monad lowering observed) would surface here as
// one tier disagreeing with the interpreter.
//
// This is a curated set of well-typed, deterministic handler programs, each
// commented with the handler shape it exercises, run under every forced tier and
// diffed against the interpreter oracle. It complements native/tier_parity.rs
// (which forces tiers over the whole runnable corpus but only exercises programs
// whose classification moves under the cap): here every program is checked on
// every tier unconditionally, so a divergence that does not change the natural
// classification is still caught. Forcing a tier is a native-codegen concern (the
// interpreter does not lower effects, so it is the tier-invariant reference), so
// this reuses the exact native build/run/diff/leak path via `support`.

use std::path::{Path, PathBuf};
use std::{env, fs};

use prism::{default_roots, Config, EffectTier};

use crate::support::{check_native_parity, parallel_check, require_cc};

// The tiers the cascade enumerates, slowest cap last. Every program's native
// output on each of these must equal the interpreter's single reference output.
const TIERS: &[EffectTier] = &[EffectTier::Auto, EffectTier::State, EffectTier::FreeMonad];

// `Config::from_env` with the effect-lowering tier capped, exactly as
// native/tier_parity.rs forces a tier (equivalent to setting `PRISM_EFFECT_TIER`).
fn forced(tier: EffectTier) -> Config {
    let mut cfg = Config::from_env();
    cfg.flags.effect_tier = tier;
    cfg
}

// The curated corpus: `(name, prelude-free source)`. The harness prepends the
// prelude via `support::source`, mirroring tests/cases/run/*.pr. Each program is
// well-typed, takes no input, and prints only `Int`s, so its output is a pure
// function of the source. The comment on each names the handler shape it exercises.
// An unmarked op is `many` (multishot-capable); `once` resumes exactly once in
// tail position; `never` discards the continuation. A clause may use a grade at
// least as restrictive as the op's declared grade.
const PROGRAMS: &[(&str, &str)] = &[
    // Single-op handler with an explicit-continuation clause and a `return` arm.
    (
        "single_return",
        "\
effect Reader
  ask(Unit) : Int
fn use_env(x) : Int ! {Reader} = x + ask(())
fn main() =
  println(handle use_env(10) with {
    ask(u) resume k => k(5),
    return r => r
  })
",
    ),
    // Single-op handler with NO `return` arm (the identity return is implicit);
    // the result type is checked by `run`'s signature.
    (
        "no_return",
        "\
effect Reader
  ask(Unit) : Int
fn use_env(x) : Int ! {Reader} = x + ask(())
fn run() : Int =
  handle use_env(10) with {
    ask(u) resume k => k(5)
  }
fn main() = println(run())
",
    ),
    // Multi-op handler: two ops of one effect (get/put), both resumed once.
    (
        "multi_op",
        "\
effect Store
  get(Unit) : Int
  put(Int) : Unit
fn prog() : Int ! {Store} =
  let a = get(())
  put(a + 1)
  let b = get(())
  a + b
fn main() =
  println(handle prog() with {
    get(u) resume k => k(7),
    put(v) resume k => k(()),
    return r => r
  })
",
    ),
    // A `once`-graded op: the clause resumes exactly once, in tail position, and
    // the continuation is never named. Two performs, one clause.
    (
        "once_grade",
        "\
effect Ask
  once ask(Unit) : Int
fn asker() : Int ! {Ask} =
  let a = ask(())
  let b = ask(())
  a + b
fn main() =
  println(handle asker() with {
    once ask(u) => 21,
    return r => r
  })
",
    ),
    // A `never`-graded op: the clause resumes zero times (the captured
    // continuation is discarded and the clause body becomes the handler result).
    // Exercised on both the taken and untaken abort path.
    (
        "never_grade",
        "\
effect Abort
  never abort(Unit) : Int
fn aborter(n) : Int ! {Abort} =
  if n < 0 then abort(()) else n * 2
fn main() =
  println(handle aborter(5) with {
    never abort(u) => 0,
    return r => r
  })
  println(handle aborter(0 - 1) with {
    never abort(u) => 999,
    return r => r
  })
",
    ),
    // Multishot: the clause resumes its continuation many times (once per
    // candidate) and concatenates the outcomes. `k` is an ordinary closure.
    (
        "multishot",
        "\
effect Amb
  choose(Int) : Int
fn pick() : Int ! {Amb} =
  let a = choose(2)
  let b = choose(2)
  a + b
fn solutions() =
  handle pick() with
    choose(m) resume k => flatten(map(\\(i) -> k(i), range(0, m)))
    return r => Cons(r, Nil)
fn main() =
  let s = solutions()
  println(length(s))
  println(sum(s))
",
    ),
    // Multishot with a pruning `reject` arm alongside the resuming `choose` arm:
    // a search that both branches and dead-ends within one handler.
    (
        "multishot_prune",
        "\
effect Amb
  choose(Int) : Int
  reject(Unit) : Int
fn triple(n) : Int ! {Amb} =
  let a = choose(n)
  let b = choose(n)
  if a > 0 && a <= b && a + b == 4 then a * 10 + b else reject(())
fn solutions(n) =
  handle triple(n) with
    choose(m) resume k => flatten(map(\\(i) -> k(i), range(0, m)))
    reject(u) resume k => Nil
    return r => Cons(r, Nil)
fn main() =
  let s = solutions(5)
  println(length(s))
  println(sum(s))
",
    ),
    // Nested handlers: an Ask handler wrapping the body, itself inside a Log
    // handler, so each performs to a different enclosing region.
    (
        "nested",
        "\
effect Ask
  ask(Unit) : Int
effect Log
  log(Int) : Unit
fn work() : Int ! {Ask, Log} =
  let a = ask(())
  log(a)
  a + 1
fn run() =
  handle (handle work() with {
      ask(u) resume k => k(10),
      return r => r
    }) with
    log(n) resume k => k(())
    return r => r
fn main() = println(run())
",
    ),
    // Nested handlers with non-tail resumption: the inner clause binds the
    // resume's result, prints it, then keeps computing, and its body performs Log
    // known only to the outer handler, so resumptions forward out and back.
    (
        "nested_nontail",
        "\
effect Ask
  ask(Unit) : Int
effect Log
  log(Int) : Unit
fn work() : Int ! {Ask, Log} =
  let a = ask(())
  log(a)
  let b = ask(())
  log(b)
  a + b
fn run() =
  handle (handle work() with {
      ask(u) resume k => let r = k(10) in let _ = println(r) in r + 100,
      return r => r * 2
    }) with
    log(n) resume k =>
      println(n)
      k(())
    return r => r
fn main() = println(run())
",
    ),
    // A single handler mixing all three grades: `once ask`, a many `double`
    // (explicit tail resume), and `never quit` (discards the continuation).
    (
        "mixed_grades",
        "\
effect Mix
  ask() : Int
  double(Int) : Int
  quit(Int) : Int
fn mixed(n) : Int ! {Mix} =
  let a = ask()
  let b = double(a + n)
  if b > 50 then quit(b) else 0
  a + b
fn run_mixed(n) =
  handle mixed(n) with
    once ask() => 10
    double(x) resume k => k(x * 2)
    never quit(code) => 0 - code
    return r => r
fn main() =
  println(run_mixed(20))
  println(run_mixed(1))
",
    ),
    // Parameter-passing state handler: each clause returns a function of the
    // threaded state and the `return` arm closes over it. Exercises the state
    // accumulator lowering (get/put threaded as a parameter).
    (
        "param_state",
        "\
effect St
  get(Unit) : Int
  put(Int) : Unit
fn counter() : Int ! {St} =
  put(get(()) + 10)
  put(get(()) + 5)
  get(())
fn run() =
  handle counter() with
    get(u) resume k => \\(s) -> k(s)(s)
    put(v) resume k => \\(s) -> k(())(v)
    return r => \\(_s) -> r
fn main() = println(run()(0))
",
    ),
];

// A per-process scratch directory the program `.pr` files are written into,
// removed when the guard drops.
struct Scratch {
    dir: PathBuf,
}

impl Scratch {
    fn new() -> Self {
        let dir = env::temp_dir().join(format!("prism_tier_handler_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        Self { dir }
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

// Materialize each program as a `<name>.pr` file, then, for every tier, build it
// native under that forced tier and diff stdout, exit code, and the leak report
// against the tier-invariant interpreter reference. Any single (program, tier)
// divergence is a real tier-observability bug and fails here.
#[test]
fn handlers_agree_across_tiers() {
    require_cc();
    let scratch = Scratch::new();
    let paths: Vec<PathBuf> = PROGRAMS
        .iter()
        .map(|(name, src)| {
            let path = scratch.dir.join(format!("{name}.pr"));
            fs::write(&path, src).unwrap();
            path
        })
        .collect();
    let roots = default_roots(Path::new("."));

    let mut fails = Vec::new();
    for &tier in TIERS {
        let cfg = forced(tier);
        let tag = format!("tier-handler-{}", tier.label());
        let roots = &roots;
        let cfg = &cfg;
        fails.extend(parallel_check(&paths, |case| {
            check_native_parity(case, &tag, |full, bin| {
                prism::build_on(full, roots, bin, cfg)
            })
        }));
    }
    assert!(
        fails.is_empty(),
        "{} of {} (program x tier) handler checks diverged from the interpreter; \
         a tier that disagrees means the effect lowering became observable:\n{}",
        fails.len(),
        PROGRAMS.len() * TIERS.len(),
        fails.join("\n")
    );
}
