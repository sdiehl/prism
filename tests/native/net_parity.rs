// The socket boundary has two implementations, `src/eval/net.rs` and
// `runtime/prism_net.c`, and the whole point of the classification table between
// them is that a program cannot tell which one it is talking to. These fixtures
// are the oracle for that: each is run through the interpreter and through a
// native binary, and the two must print the same bytes.
//
// They live under `examples/fixtures/` rather than in the corpus because the
// corpus is diffed on every backend and tier combination, and a program that
// opens sockets does not belong in a sweep that wide. Their expected output is
// written out here rather than snapshotted, because what is being pinned is a
// contract (which refusal each mistake earns), not a rendering.

use std::path::{Path, PathBuf};

use prism::error::Error;
use prism::{build_on, default_roots, Config};

use crate::support::{check_native_parity, interpreted, require_cc, source};

const LOOPBACK: &str = "\
local same
peer loopback
recv hello, prism
reply 12
";

// One line per classified refusal, in the order the fixture provokes them.
const CLASSIFY: &str = "\
recv-on-listener Net.Closed
accept-on-stream Net.Closed
peer-of-listener Net.Closed
recv-zero Net.Invalid
recv-negative Net.Invalid
recv-unmeetable Net.Limit
send-at-end 0
send-past-end Net.Invalid
send-negative Net.Invalid
stale-listener Net.Closed
stale-stream Net.Closed
never-issued Net.Closed
refused Net.Refused
no-port Net.Invalid
port-too-large Net.Invalid
no-host Net.Invalid
unbracketed-v6 Net.Invalid
";

const HANDLES: &str = "\
h1 live
h2 live
h3 -
";

fn fixture(name: &str) -> PathBuf {
    Path::new("examples/fixtures/net").join(name)
}

fn quiet() -> Config {
    let mut cfg = Config::from_env();
    cfg.update_flags(|flags| flags.quiet = true);
    cfg.update_flags(|flags| flags.compiler_cache = false);
    cfg
}

fn build(src: &str, out: &Path) -> Result<(), Error> {
    build_on(src, &default_roots(Path::new(".")), out, &quiet())
}

// Interpret the fixture, pin what it printed, then diff a native build of it
// against that same interpreted run. The pin is what makes a change of meaning
// visible: without it two tiers could agree on the wrong answer.
fn both_tiers(name: &str, want: &str) {
    require_cc();
    let case = fixture(name);
    let got = interpreted(&source(&case));
    assert_eq!(got, want, "{name}: interpreted output changed");
    if let Err(e) = check_native_parity(&case, "net", build) {
        panic!("{e}");
    }
}

#[test]
fn loopback_round_trip_matches_interpreter() {
    both_tiers("loopback.pr", LOOPBACK);
}

#[test]
fn classified_refusals_match_interpreter() {
    both_tiers("classify.pr", CLASSIFY);
}

#[test]
fn handle_numbering_matches_interpreter() {
    both_tiers("handles.pr", HANDLES);
}

/// A second run on the same thread starts from an empty table and numbers its
/// handles from one, even though the first left a listener open. Only the
/// interpreter can be asked this, since each native run is its own process; the
/// interpreter is the tier where a table could survive a program, so it is the
/// tier where it must be shown not to.
#[test]
fn a_run_does_not_inherit_the_last_ones_sockets() {
    let full = source(&fixture("handles.pr"));
    assert_eq!(interpreted(&full), HANDLES);
    assert_eq!(interpreted(&full), HANDLES);
}

/// `Net` is recorded but not replayable: a socket read has no answer in a trace
/// without the peer that produced it. The existing replayable-effect rule is
/// what enforces that, because `Net` was never added to the set it allows, so a
/// durable function that touches the network is rejected before it can perform
/// live traffic on resume.
#[test]
fn a_replayable_function_may_not_touch_the_network() {
    let src = "\
import Net (Net, receive, with_tcp_connection)

replayable fn fetch() : Unit ! {Net} =
  let _r = with_tcp_connection(\"127.0.0.1:9\", \\(s) -> receive(s, 8))
  ()

fn main() : Unit ! {IO} = println(\"unreached\")
";
    let e =
        prism::interpret(&prism::with_prelude(src)).expect_err("replayable Net must be rejected");
    let text = e.to_string();
    assert!(text.contains("replayable"), "wrong diagnostic: {text}");
    assert!(text.contains("Net.Net"), "wrong effect named: {text}");
}
