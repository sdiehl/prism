// Randomized oracle for the pattern-match compiler. For each case we generate a
// well-typed `match` over a small tree type plus a boolean column (the shape of
// the first-match bug: a wildcard column interleaved with constructor/scalar
// arms), run it through the interpreter, and compare the arm it selects against a
// naive first-match reference computed here. The match compiler has no other
// differential oracle, so this guards the specialization rewrite against
// first-match and exhaustiveness regressions.
//
// Cases the type-checker rejects (an earlier arm shadowing a later one is a hard
// error) are skipped: the defect this guards against is a wrong runtime *value*
// among reachable arms, never a compile error, so only accepted-and-run cases can
// expose it.

// Short names (`a`/`b`/`x`/`y` tree children, `p`/`v` pattern/value) match the
// lib crate's own allowance and read best for this tiny pattern algebra.
#![allow(clippy::many_single_char_names)]

use std::fmt::Write as _;

use prism::interpret;

// Deterministic xorshift64* so a failure reproduces from its seed.
struct Rng(u64);

impl Rng {
    const fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u32) -> u32 {
        // The modulo is `< n`, so it always fits in `u32`.
        u32::try_from(self.next() % u64::from(n)).expect("modulo < n fits u32")
    }
    const fn flip(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

// Values of `type T = L | N(T, T)`.
enum V {
    L,
    N(Box<Self>, Box<Self>),
}

// Patterns over T: a variable is treated exactly as a wildcard for selection.
enum P {
    Wild,
    Var,
    L,
    N(Box<Self>, Box<Self>),
}

// A boolean column pattern.
enum B {
    Wild,
    Lit(bool),
}

fn gen_val(r: &mut Rng, depth: u32) -> V {
    if depth == 0 || r.below(3) == 0 {
        V::L
    } else {
        V::N(
            Box::new(gen_val(r, depth - 1)),
            Box::new(gen_val(r, depth - 1)),
        )
    }
}

fn gen_pat(r: &mut Rng, depth: u32) -> P {
    match r.below(if depth == 0 { 3 } else { 4 }) {
        0 => P::Wild,
        1 => P::Var,
        2 => P::L,
        _ => P::N(
            Box::new(gen_pat(r, depth - 1)),
            Box::new(gen_pat(r, depth - 1)),
        ),
    }
}

const fn p_total(p: &P) -> bool {
    matches!(p, P::Wild | P::Var)
}

// One arm: a T-pattern and a bool-pattern. Never let both be total, or the arm
// covers everything and makes the trailing catch-all an (illegal) unreachable
// arm; that just shrinks the yield without adding coverage.
fn gen_arm(r: &mut Rng) -> (P, B) {
    let tp = gen_pat(r, 2);
    let bp = if r.flip() { B::Wild } else { B::Lit(r.flip()) };
    if p_total(&tp) && matches!(bp, B::Wild) {
        (tp, B::Lit(r.flip()))
    } else {
        (tp, bp)
    }
}

fn m_t(p: &P, v: &V) -> bool {
    match (p, v) {
        (P::Wild | P::Var, _) | (P::L, V::L) => true,
        (P::N(a, b), V::N(x, y)) => m_t(a, x) && m_t(b, y),
        _ => false,
    }
}

const fn m_b(p: &B, v: bool) -> bool {
    match p {
        B::Wild => true,
        B::Lit(b) => *b == v,
    }
}

fn render_val(v: &V) -> String {
    match v {
        V::L => "L".into(),
        V::N(a, b) => format!("N({}, {})", render_val(a), render_val(b)),
    }
}

// Render a pattern, giving each variable occurrence a distinct name so a repeated
// binder never appears (which would be an illegal non-linear pattern).
fn render_pat(p: &P, next: &mut u32) -> String {
    match p {
        P::Wild => "_".into(),
        P::Var => {
            let n = *next;
            *next += 1;
            format!("v{n}")
        }
        P::L => "L".into(),
        P::N(a, b) => format!("N({}, {})", render_pat(a, next), render_pat(b, next)),
    }
}

fn render_bpat(p: &B) -> String {
    match p {
        B::Wild => "_".into(),
        B::Lit(true) => "true".into(),
        B::Lit(false) => "false".into(),
    }
}

// First-match reference: the 1-based index of the first arm both columns match,
// or 0 for the trailing catch-all.
fn reference(arms: &[(P, B)], vt: &V, vb: bool) -> usize {
    arms.iter()
        .position(|(tp, bp)| m_t(tp, vt) && m_b(bp, vb))
        .map_or(0, |i| i + 1)
}

fn source(arms: &[(P, B)], vt: &V, vb: bool) -> String {
    let mut body = String::from("type T = L | N(T, T)\nfn test(p) =\n  match p of\n");
    for (i, (tp, bp)) in arms.iter().enumerate() {
        let mut next = 0;
        writeln!(
            body,
            "    ({}, {}) => {}",
            render_pat(tp, &mut next),
            render_bpat(bp),
            i + 1
        )
        .unwrap();
    }
    body.push_str(
        r"    (_, _) => 0

",
    );
    write!(
        body,
        "fn main() : Unit ! {{IO}} =\n  println(test(({}, {})))\n",
        render_val(vt),
        if vb { "true" } else { "false" }
    )
    .unwrap();
    body
}

#[test]
fn match_compiler_selects_first_match() {
    let mut ran = 0u32;
    for seed in 1..=400u64 {
        let mut r = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
        let n_arms = 1 + r.below(3) as usize;
        let arms: Vec<(P, B)> = (0..n_arms).map(|_| gen_arm(&mut r)).collect();
        let vt = gen_val(&mut r, 3);
        let vb = r.flip();

        let src = source(&arms, &vt, vb);
        // Skip cases the type-checker rejects (a shadowed later arm); they cannot
        // exercise a wrong-value bug. The program is self-contained (`println` is a
        // builtin), so no prelude is needed -- keeping each case cheap.
        let Ok(run) = interpret(&src) else {
            continue;
        };
        ran += 1;
        let got: usize = run
            .term
            .trim()
            .parse()
            .unwrap_or_else(|_| panic!("non-integer output {:?} for source:\n{src}", run.term));
        let want = reference(&arms, &vt, vb);
        assert_eq!(
            got, want,
            "seed {seed}: match selected arm {got}, first-match is {want}\n{src}"
        );
    }
    assert!(
        ran >= 100,
        "oracle ran only {ran} cases; generator is too rejective"
    );
}
