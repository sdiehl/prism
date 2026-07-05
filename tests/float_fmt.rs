//! Float-formatter parity: the C runtime's in-repo shortest-round-trip
//! formatter (`prism_shortest_digits`/`prism_fmt_float` in `runtime/prism_rt.c`)
//! must print every `f64` byte-for-byte identically to the interpreter's canonical
//! `fmt_g` (`src/eval`). Owning the digit selection in-repo replaces the old
//! reliance on libc's `snprintf`/`strtod` agreeing with Rust's formatter, so
//! this gate asserts the two agree by construction across a hard-case corpus
//! plus a wide deterministic bit-pattern sweep, not by libc's grace.
//!
//! The C side is exercised out-of-process: `runtime/prism_rt.c` owns `main`
//! (which calls `prism_main`), so it cannot be linked into a Rust test binary.
//! Instead a tiny shim supplying `prism_main` is compiled against the real
//! runtime, reads raw little-endian f64 bit patterns from stdin, and prints one
//! formatted line per value through the same `prism_show_float` path a compiled
//! program uses.

// This file is deliberately a table of edge-case float literals: full-precision
// spellings and unseparated digit runs are the point, not a style slip.
#![allow(
    clippy::unreadable_literal,
    clippy::excessive_precision,
    clippy::missing_const_for_fn,
    clippy::approx_constant,
    clippy::cast_precision_loss
)]

use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

// Pseudo-random bit patterns swept through both formatters. The default keeps
// the gate quick in the normal suite; PRISM_FLOAT_SWEEP scales it to millions
// for a nightly or local deep run (validated to 5,000,000 during development).
const SWEEP: u64 = 300_000;

fn cc() -> String {
    std::env::var("PRISM_CC").unwrap_or_else(|_| "clang".into())
}

fn have_cc() -> bool {
    Command::new(cc())
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

// A splitmix64 step: a well-mixed deterministic sequence so the sweep is the
// same set of doubles on every machine and every run.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

// The corpus of bit patterns to check: named hard cases, structured families
// (every power of two, powers of ten, mantissa neighborhoods of boundaries),
// then the pseudo-random sweep.
fn corpus() -> Vec<u64> {
    let mut v: Vec<f64> = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        2.0,
        0.5,
        0.1,
        0.2,
        0.3,
        0.1 + 0.2,
        1.5,
        2.5,
        100.0,
        1234.5678,
        1e23,
        1e-23,
        1e100,
        1e-100,
        5e-324,                  // smallest positive subnormal
        4.9406564584124654e-324, // same, decimal spelling
        2.2250738585072009e-308, // largest subnormal
        2.2250738585072014e-308, // smallest normal
        1.7976931348623157e308,  // DBL_MAX
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        f64::EPSILON,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        9.109383632e-31,
        6.022140857e23,
        3.141592653589793,
        2.718281828459045,
    ];
    // Small integers and their negatives, exercising the integer-valued path.
    for i in 0..=1000i64 {
        v.push(i as f64);
        v.push(-(i as f64));
        v.push(i as f64 + 0.5);
    }
    let mut bits: Vec<u64> = v.iter().map(|d| d.to_bits()).collect();

    // Every power of two (subnormal through DBL_MAX): the unequal-gap case where
    // the lower rounding boundary is half the upper.
    for e in -1074i32..=1023 {
        bits.push((2.0f64).powi(e).to_bits());
    }
    // Powers of ten within range.
    for e in -323i32..=308 {
        let d = format!("1e{e}").parse::<f64>().unwrap();
        bits.push(d.to_bits());
    }
    // Mantissa neighborhoods around the subnormal/normal boundary and near
    // powers of two, where shortest-digit ties are most likely.
    for base in [0u64, 1u64 << 52, 0x7FE_0000_0000_0000] {
        for d in 0..2048u64 {
            bits.push(base.wrapping_add(d));
        }
    }

    // Deterministic pseudo-random sweep across the full 64-bit pattern space.
    let n: u64 = std::env::var("PRISM_FLOAT_SWEEP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(SWEEP);
    let mut state = 0x1234_5678_9ABC_DEF0u64;
    for _ in 0..n {
        bits.push(splitmix64(&mut state));
    }
    bits
}

fn build_helper() -> PathBuf {
    let stem = format!("prism_float_fmt_{}", std::process::id());
    let dir = std::env::temp_dir().join(&stem);
    std::fs::create_dir_all(&dir).unwrap();
    // Compile the split runtime modules from the one canonical list, the same
    // sources the native backend links. `prism_libm.c`'s `prism_m_*` wrappers
    // reference the namespaced `prism_v_*` math symbols, which live only in the
    // vendored libm archive, so link that too (the same bytes the interpreter and
    // native backend link); linking the runtime sources alone leaves them undefined.
    let rt_sources = prism::codegen::rt::write_runtime(&dir).unwrap();
    let libm_archive = prism::codegen::rt::write_libm_archive(&dir).unwrap();
    let shim = dir.join(format!("{stem}.c"));
    let bin = dir.join(&stem);
    // The shim provides prism_main (the runtime's main calls it), reads raw
    // little-endian f64 bit patterns from stdin, and prints each through the
    // real show-float path (print_str appends a newline).
    std::fs::write(
        &shim,
        "#include <stdio.h>\n\
         #include <stdint.h>\n\
         long prism_show_float(long);\n\
         void print_str(long);\n\
         long prism_main(void) {\n\
         uint64_t bits;\n\
         while (fread(&bits, 8, 1, stdin) == 1) print_str(prism_show_float((long)bits));\n\
         return 1;\n\
         }\n",
    )
    .unwrap();
    let out = Command::new(cc())
        .args(["-O2", "-w"])
        .arg(&shim)
        .args(&rt_sources)
        .arg(&libm_archive)
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("failed to invoke C compiler");
    assert!(
        out.status.success(),
        "compiling the float-formatter helper failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    bin
}

#[test]
fn native_float_format_matches_interpreter() {
    if !have_cc() {
        eprintln!(
            "skipping float_fmt: C compiler `{}` not found (set PRISM_CC)",
            cc()
        );
        return;
    }
    let bin = build_helper();
    let cases = corpus();

    // Feed the child from a thread while draining stdout on this one, so a full
    // pipe buffer cannot deadlock the exchange.
    let mut child = Command::new(&bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to spawn float-formatter helper");
    let mut stdin = child.stdin.take().unwrap();
    let feed: Vec<u8> = cases.iter().flat_map(|b| b.to_le_bytes()).collect();
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

    let native: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        native.len(),
        cases.len(),
        "helper emitted {} lines for {} inputs",
        native.len(),
        cases.len()
    );

    let mut mismatches = 0usize;
    let mut first: Option<String> = None;
    for (bits, got) in cases.iter().zip(native.iter()) {
        let d = f64::from_bits(*bits);
        let want = prism::eval::fmt_g(d);
        if want != *got {
            mismatches += 1;
            if first.is_none() {
                first = Some(format!(
                    "bits=0x{bits:016x} value={d:?}: interpreter {want:?} != native {got:?}"
                ));
            }
        }
    }
    let _ = std::fs::remove_file(&bin);
    assert_eq!(
        mismatches,
        0,
        "{mismatches} of {} floats formatted differently; first: {}",
        cases.len(),
        first.unwrap_or_default()
    );
}
