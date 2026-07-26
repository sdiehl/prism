//! Single-shot lexer driver: read one file, run one layer over it, print the
//! token count and the nanoseconds the layer took.
//!
//! Its twin is `benches/lexbench.pr`, which does the same work in the same shape
//! with the Prism-language lexer. `scripts/lexperf.py` runs the pair over one
//! corpus and reports the Prism-to-Rust throughput and peak-memory ratio per
//! layer.
//!
//! Only this side reports its own elapsed time. Reading a clock from Prism means
//! installing an effect handler around the measured region, and a handler
//! changes the tier the whole program lowers at, so the Prism twin would time
//! the handler rather than the lexer; the harness times it from the outside and
//! subtracts process startup instead. This side is timed internally because a
//! whole run here is microseconds, which process startup would swamp. The gap
//! between the two methods is one file read and one process launch, and it is
//! several orders of magnitude below the difference being measured.

use std::env;
use std::fs;
use std::process::exit;
use std::time::Instant;

use prism::lex::{lex, lex_raw};

const LAYER_RAW: &str = "raw";
const LAYER_LAYOUT: &str = "layout";
const USAGE: &str = "usage: lexbench <file> <raw|layout>";
// A misuse of the driver, distinct from a source file that legitimately fails
// to lex.
const EXIT_USAGE: i32 = 2;
const EXIT_LEX: i32 = 1;

fn main() {
    let mut args = env::args().skip(1);
    let (Some(path), Some(layer)) = (args.next(), args.next()) else {
        eprintln!("{USAGE}");
        exit(EXIT_USAGE);
    };
    let src = fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("{path}: {e}");
        exit(EXIT_USAGE);
    });
    let start = Instant::now();
    let tokens = match layer.as_str() {
        LAYER_RAW => lex_raw(&src),
        LAYER_LAYOUT => lex(&src),
        other => {
            eprintln!("{USAGE}: unknown layer `{other}`");
            exit(EXIT_USAGE);
        }
    };
    let elapsed = start.elapsed().as_nanos();
    match tokens {
        Ok((toks, _)) => println!("{} {elapsed}", toks.len()),
        Err(e) => {
            eprintln!("{path}: {e}");
            exit(EXIT_LEX);
        }
    }
}
