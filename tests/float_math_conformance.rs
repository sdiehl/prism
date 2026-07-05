//! Owned-numerics conformance: the vendored libm behind every `FloatOp` must
//! produce byte-identical results in the interpreter and the native runtime,
//! across the hard cases (subnormals, extremes, argument reduction near multiples
//! of pi/2, signed zero, NaN, +-inf) and a deterministic bulk sweep.
//!
//! Determinism, not correct rounding, is the contract: this gate does not check
//! the results against a true real value, only that the two backends agree. They
//! agree by construction, since both call the same `prism_m_*` symbols (the
//! interpreter FFIs them, native codegen calls them) -- but the two are compiled
//! by different clang invocations (the `cc` crate builds the copy linked into
//! this test binary; a fresh `write_runtime` + clang builds the copy the shim
//! links), so this pins that the same source compiled twice, with the pinned
//! `-ffp-contract=off`, is bit-identical. A flag leak or ABI mismatch fails here.
//!
//! The C side runs out of process (the runtime owns `main`): a shim reads
//! `(op, x_bits, y_bits)` records from stdin and prints the result bits, the same
//! path a compiled program's float ops take.

// A conformance harness trips a handful of pedantic/nursery lints by nature:
// literal tables of hard-case constants, fn-pointer op tables, and float
// bit-twiddling. Allowed as a block here rather than per-site noise.
#![allow(
    clippy::unreadable_literal,
    clippy::excessive_precision,
    clippy::type_complexity,
    clippy::missing_const_for_fn,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::float_cmp
)]

use std::fmt::Write as _;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use prism::eval::owned_math as m;

// The op table, shared by the C shim's switch and the Rust reference below. Order
// is the wire tag; keep the two in lockstep.
const UNARY: &[(&str, fn(f64) -> f64)] = &[
    ("prism_m_sin", m::sin),
    ("prism_m_cos", m::cos),
    ("prism_m_tan", m::tan),
    ("prism_m_asin", m::asin),
    ("prism_m_acos", m::acos),
    ("prism_m_atan", m::atan),
    ("prism_m_sinh", m::sinh),
    ("prism_m_cosh", m::cosh),
    ("prism_m_tanh", m::tanh),
    ("prism_m_exp", m::exp),
    ("prism_m_exp2", m::exp2),
    ("prism_m_expm1", m::expm1),
    ("prism_m_log", m::log),
    ("prism_m_log2", m::log2),
    ("prism_m_log10", m::log10),
    ("prism_m_log1p", m::log1p),
    ("prism_m_cbrt", m::cbrt),
];
const BINARY: &[(&str, fn(f64, f64) -> f64)] = &[
    ("prism_m_pow", m::pow),
    ("prism_m_atan2", m::atan2),
    ("prism_m_hypot", m::hypot),
    ("prism_m_fmod", m::fmod),
];

const SWEEP: u64 = 20_000;

fn cc() -> String {
    std::env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn have_cc() -> bool {
    Command::new(cc())
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

// The hard-case f64 bit patterns every op is checked on: named specials, the
// argument-reduction danger zone around multiples of pi/2, subnormals, and the
// range extremes.
fn hard_cases() -> Vec<u64> {
    let mut v: Vec<f64> = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -0.5,
        2.0,
        0.1,
        std::f64::consts::PI,
        std::f64::consts::FRAC_PI_2,
        std::f64::consts::FRAC_PI_4,
        std::f64::consts::TAU,
        -std::f64::consts::FRAC_PI_2,
        1e-8,
        1e8,
        1e300,
        1e-300,
        5e-324,                  // smallest positive subnormal
        2.2250738585072009e-308, // largest subnormal
        2.2250738585072014e-308, // smallest normal
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        f64::EPSILON,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        100.0,
        -100.0,
        1000000.0,
    ];
    // Near multiples of pi/2, where trig argument reduction is hardest.
    for k in 1..=12i32 {
        let base = std::f64::consts::FRAC_PI_2 * f64::from(k);
        v.push(base);
        v.push(base + 1e-12);
        v.push(base - 1e-12);
    }
    v.iter().map(|d| d.to_bits()).collect()
}

// The full record stream: every op over the hard cases and a seeded sweep. Unary
// ops ignore `y`; binary ops pair each swept `x` with the next swept value.
fn records() -> Vec<(u8, u64, u64)> {
    let n_ops = UNARY.len() + BINARY.len();
    let mut recs = Vec::new();
    let hard = hard_cases();
    for op in 0..n_ops as u8 {
        for &xb in &hard {
            for &yb in &hard {
                recs.push((op, xb, yb));
                if op < UNARY.len() as u8 {
                    break; // unary: one y is enough
                }
            }
        }
    }
    let sweep: u64 = std::env::var("PRISM_MATH_SWEEP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(SWEEP);
    let mut state = 0x0BAD_F00D_D15E_A5E5u64;
    for _ in 0..sweep {
        let xb = splitmix64(&mut state);
        let yb = splitmix64(&mut state);
        for op in 0..n_ops as u8 {
            recs.push((op, xb, yb));
        }
    }
    recs
}

fn reference(op: u8, xb: u64, yb: u64) -> u64 {
    let x = f64::from_bits(xb);
    let r = if (op as usize) < UNARY.len() {
        UNARY[op as usize].1(x)
    } else {
        BINARY[op as usize - UNARY.len()].1(x, f64::from_bits(yb))
    };
    r.to_bits()
}

fn build_helper() -> PathBuf {
    let stem = format!("prism_math_conf_{}", std::process::id());
    let dir = std::env::temp_dir().join(&stem);
    std::fs::create_dir_all(&dir).unwrap();
    let rt_sources = prism::codegen::rt::write_runtime(&dir).unwrap();
    let shim = dir.join(format!("{stem}.c"));
    let bin = dir.join(&stem);

    // The shim declares the owned math surface, dispatches on the op tag, and
    // prints each result's raw bits. A record is one u8 tag then two little-endian
    // u64 operand bit patterns.
    let mut decls = String::new();
    for (sym, _) in UNARY {
        let _ = writeln!(decls, "double {sym}(double);");
    }
    for (sym, _) in BINARY {
        let _ = writeln!(decls, "double {sym}(double,double);");
    }
    let mut unary_arms = String::new();
    for (i, (sym, _)) in UNARY.iter().enumerate() {
        let _ = writeln!(unary_arms, "case {i}: r = {sym}(x); break;");
    }
    let mut binary_arms = String::new();
    for (i, (sym, _)) in BINARY.iter().enumerate() {
        let _ = writeln!(
            binary_arms,
            "case {}: r = {sym}(x, y); break;",
            i + UNARY.len()
        );
    }
    std::fs::write(
        &shim,
        format!(
            "#include <stdio.h>\n#include <stdint.h>\n#include <string.h>\n\
             {decls}\
             long prism_main(void) {{\n\
             unsigned char op; uint64_t xb, yb;\n\
             while (fread(&op, 1, 1, stdin) == 1) {{\n\
             if (fread(&xb, 8, 1, stdin) != 1) break;\n\
             if (fread(&yb, 8, 1, stdin) != 1) break;\n\
             double x, y; memcpy(&x, &xb, 8); memcpy(&y, &yb, 8);\n\
             double r = 0; switch (op) {{\n{unary_arms}{binary_arms}default: break; }}\n\
             uint64_t rb; memcpy(&rb, &r, 8);\n\
             printf(\"%016llx\\n\", (unsigned long long)rb);\n\
             }}\n return 1;\n}}\n"
        ),
    )
    .unwrap();
    let out = Command::new(cc())
        .args(["-O2", "-ffp-contract=off", "-w"])
        .arg(&shim)
        .args(&rt_sources)
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("failed to invoke C compiler");
    assert!(
        out.status.success(),
        "compiling the math conformance helper failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    bin
}

#[test]
fn native_float_math_matches_interpreter() {
    if !have_cc() {
        eprintln!("skipping math conformance: C compiler `{}` not found", cc());
        return;
    }
    let bin = build_helper();
    let recs = records();

    let mut child = Command::new(&bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to spawn math conformance helper");
    let mut stdin = child.stdin.take().unwrap();
    let feed: Vec<u8> = recs
        .iter()
        .flat_map(|(op, xb, yb)| {
            let mut b = vec![*op];
            b.extend_from_slice(&xb.to_le_bytes());
            b.extend_from_slice(&yb.to_le_bytes());
            b
        })
        .collect();
    let writer = std::thread::spawn(move || {
        stdin.write_all(&feed).unwrap();
        drop(stdin);
    });
    let mut stdout = String::new();
    child
        .stdout
        .take()
        .unwrap()
        .read_to_string(&mut stdout)
        .unwrap();
    writer.join().unwrap();
    assert!(child.wait().unwrap().success());
    let _ = std::fs::remove_file(&bin);

    let native: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        native.len(),
        recs.len(),
        "helper emitted the wrong line count"
    );

    let mut mismatches = 0usize;
    let mut first = None;
    for ((op, xb, yb), got) in recs.iter().zip(native.iter()) {
        let want = reference(*op, *xb, *yb);
        // Two NaN results with differing payloads are still both NaN; the contract
        // is on the value, and Prism only produces quiet NaNs, so compare bits
        // directly (this also pins the quiet-NaN bit pattern is stable).
        if format!("{want:016x}") != *got {
            mismatches += 1;
            if first.is_none() {
                let name = if (*op as usize) < UNARY.len() {
                    UNARY[*op as usize].0
                } else {
                    BINARY[*op as usize - UNARY.len()].0
                };
                first = Some(format!(
                    "{name}(x=0x{xb:016x}, y=0x{yb:016x}): interp 0x{want:016x} != native 0x{got}"
                ));
            }
        }
    }
    assert_eq!(
        mismatches,
        0,
        "{mismatches} of {} results diverged; first: {}",
        recs.len(),
        first.unwrap_or_default()
    );
}
