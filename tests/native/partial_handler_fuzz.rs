//! Deterministic generative gate for residual-handler forwarding.
//!
//! The fragment deliberately stays small enough for every generated case to run
//! under every lowering tier. A failure is greedily shrunk before the test prints
//! the minimal Prism reproducer, so a regression can be promoted directly into
//! the permanent corpus.

use std::fmt::Write as _;
use std::path::Path;
use std::{fs, iter};

use prism::{default_roots, Config, EffectTier};

use crate::support::{check_native_parity, require_cc, TempDir};

const TIERS: &[EffectTier] = &[EffectTier::Auto, EffectTier::State, EffectTier::FreeMonad];
const GENERATED_CASES: usize = 6;
const SEED: u64 = 0x7061_7274_6961_6c21;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Left,
    Right,
}

impl Op {
    const fn name(self) -> &'static str {
        match self {
            Self::Left => "left",
            Self::Right => "right",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Call {
    op: Op,
    argument: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Candidate {
    calls: Vec<Call>,
    handled: Op,
    inner_delta: u8,
    outer_left_delta: u8,
    outer_right_delta: u8,
    post_resume: u8,
    return_delta: u8,
}

impl Candidate {
    fn render(&self) -> String {
        let mut source = String::from(
            "effect Probe\n  left(Int) : Int\n  right(Int) : Int\n\n\
             fn work() : Int ! {Probe} =\n",
        );
        for (index, call) in self.calls.iter().enumerate() {
            writeln!(
                source,
                "  let v{index} = {}({})",
                call.op.name(),
                call.argument
            )
            .unwrap();
        }
        let sum = (0..self.calls.len())
            .map(|index| format!("v{index}"))
            .collect::<Vec<_>>()
            .join(" + ");
        writeln!(source, "  {sum}\n").unwrap();

        let handled = self.handled.name();
        writeln!(source, "fn run() : Int =").unwrap();
        writeln!(source, "  handle (handle work() with partial {{").unwrap();
        writeln!(
            source,
            "    {handled}(x) resume k => let r = k(x + {}) in r + {},",
            self.inner_delta, self.post_resume
        )
        .unwrap();
        writeln!(
            source,
            "    return r => r + {}\n  }}) with {{",
            self.return_delta
        )
        .unwrap();
        writeln!(
            source,
            "    left(x) resume k => k(x + {}),",
            self.outer_left_delta
        )
        .unwrap();
        writeln!(
            source,
            "    right(x) resume k => k(x + {}),",
            self.outer_right_delta
        )
        .unwrap();
        source.push_str("    return r => r\n  }\n\nfn main() = println(run())\n");
        source
    }

    fn reductions(&self) -> Vec<Self> {
        let mut out = Vec::new();
        for index in 0..self.calls.len() {
            let mut calls = self.calls.clone();
            calls.remove(index);
            if calls.iter().any(|call| call.op == Op::Left)
                && calls.iter().any(|call| call.op == Op::Right)
            {
                let mut reduced = self.clone();
                reduced.calls = calls;
                out.push(reduced);
            }
        }
        for index in 0..self.calls.len() {
            if self.calls[index].argument != 0 {
                let mut reduced = self.clone();
                reduced.calls[index].argument = 0;
                out.push(reduced);
            }
        }
        for field in 0..5 {
            let mut reduced = self.clone();
            let value = match field {
                0 => &mut reduced.inner_delta,
                1 => &mut reduced.outer_left_delta,
                2 => &mut reduced.outer_right_delta,
                3 => &mut reduced.post_resume,
                _ => &mut reduced.return_delta,
            };
            if *value != 0 {
                *value = 0;
                out.push(reduced);
            }
        }
        out
    }
}

struct Lcg(u64);

impl Lcg {
    const fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    const fn small(&mut self) -> u8 {
        ((self.next() >> 32) % 17) as u8
    }
}

fn generate() -> Vec<Candidate> {
    let mut rng = Lcg(SEED);
    (0..GENERATED_CASES)
        .map(|_| {
            let extra = (rng.next() % 4) as usize;
            let calls = iter::once(Call {
                op: Op::Left,
                argument: rng.small(),
            })
            .chain(iter::once(Call {
                op: Op::Right,
                argument: rng.small(),
            }))
            .chain((0..extra).map(|_| Call {
                op: if rng.next() & 1 == 0 {
                    Op::Left
                } else {
                    Op::Right
                },
                argument: rng.small(),
            }))
            .collect();
            Candidate {
                calls,
                handled: if rng.next() & 1 == 0 {
                    Op::Left
                } else {
                    Op::Right
                },
                inner_delta: rng.small(),
                outer_left_delta: rng.small(),
                outer_right_delta: rng.small(),
                // A nonzero value makes resumption observably non-tail.
                post_resume: rng.small().max(1),
                return_delta: rng.small(),
            }
        })
        .collect()
}

fn forced(tier: EffectTier) -> Config {
    let mut config = Config::from_env();
    config.flags.effect_tier = tier;
    config.flags.compiler_cache = false;
    config
}

fn check_candidate(candidate: &Candidate, path: &Path) -> Result<(), String> {
    fs::write(path, candidate.render()).unwrap();
    let roots = default_roots(Path::new("."));
    for &tier in TIERS {
        let config = forced(tier);
        let tag = format!("partial-fuzz-{}", tier.label());
        check_native_parity(path, &tag, |full, binary| {
            prism::build_on(full, &roots, binary, &config)
        })?;
    }
    Ok(())
}

fn shrink(mut candidate: Candidate, path: &Path, mut failure: String) -> (Candidate, String) {
    loop {
        let mut smaller = None;
        for reduced in candidate.reductions() {
            if let Err(error) = check_candidate(&reduced, path) {
                smaller = Some((reduced, error));
                break;
            }
        }
        let Some((reduced, error)) = smaller else {
            return (candidate, failure);
        };
        candidate = reduced;
        failure = error;
    }
}

#[test]
fn generated_partial_handlers_agree_across_all_tiers() {
    require_cc();
    let scratch = TempDir::new("partial-handler-fuzz", "cases");
    let path = scratch.join("candidate.pr");
    for (index, candidate) in generate().into_iter().enumerate() {
        if let Err(failure) = check_candidate(&candidate, &path) {
            let (minimal, failure) = shrink(candidate, &path, failure);
            panic!(
                "generated partial-handler case {index} diverged after shrinking:\n{failure}\n\nminimal reproducer:\n{}",
                minimal.render()
            );
        }
    }
}
