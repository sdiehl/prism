//! One bundle, two operating-system processes, one computation.
//!
//! `examples/fixtures/net/teleport_tcp.pr` is the program. Run as `whole` it
//! counts from 1 to 10 in one process. Run as `send` it counts to 5, reaches
//! `teleport`, and hands the sealed rest of the count to a TCP transport. Run as
//! `receive` it binds a loopback port, reads one length-framed envelope, leaves
//! the network scope, and lands what arrived. The gate is that the sender's
//! output followed by the receiver's output is the uninterrupted run, byte for
//! byte, produced by two processes that share nothing but a socket.
//!
//! The refusals matter as much as the success, so they are here too: an envelope
//! from other code, a frame that stops early, one that claims more than the
//! reader will hold, one that claims nothing, one whose body is not an envelope,
//! and a transport with nowhere to connect.
//!
//! Every child is spawned through [`Kid`], which drains both of its pipes on
//! background threads and kills what it owns on drop, so a failed assertion
//! cannot leave a listener bound or an interpreter running.

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use crate::support::TempDir;

const FIXTURE: &str = "examples/fixtures/net/teleport_tcp.pr";

/// What the sender prints before the cut, and what the receiver prints after it.
const PREFIX: &str = "step 1\nstep 2\nstep 3\nstep 4\nstep 5\n";
const SUFFIX: &str = "step 6\nstep 7\nstep 8\nstep 9\nstep 10\n";

/// How long a child may take to reach a line of output, and how long it may take
/// to exit once its peer is done. This is a hang bound and not a latency target:
/// a `prism run` type-checks the prelude before it binds anything, and a loaded
/// machine is allowed to be slow at that. What it rules out is a test that waits
/// forever on a peer that will never speak.
const BOUND: Duration = Duration::from_mins(3);

/// A child `prism run` with both pipes drained on background threads, so neither
/// stream can fill and stall the child while the test waits on the other.
struct Kid {
    child: Child,
    err: Receiver<String>,
    out: Option<JoinHandle<String>>,
    seen: Vec<String>,
    reaped: bool,
}

/// What a child left behind once it exited.
struct Done {
    ok: bool,
    stdout: String,
    stderr: String,
}

impl Kid {
    fn spawn(program: &Path, args: &[&str]) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_prism"))
            .arg("run")
            .arg(program)
            .arg("--")
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn prism run");
        let mut stdout = child.stdout.take().expect("piped stdout");
        let stderr = child.stderr.take().expect("piped stderr");
        let out = thread::spawn(move || {
            let mut text = String::new();
            let _ = stdout.read_to_string(&mut text);
            text
        });
        let (tx, err) = mpsc::channel();
        thread::spawn(move || {
            for line in BufReader::new(stderr).lines().map_while(Result::ok) {
                if tx.send(line).is_err() {
                    break;
                }
            }
        });
        Self {
            child,
            err,
            out: Some(out),
            seen: Vec::new(),
            reaped: false,
        }
    }

    /// The next standard-error line starting with `prefix`, within the bound.
    /// Lines that do not match are kept rather than dropped, so a failure reports
    /// the whole of what the child said instead of the part that was awaited.
    fn await_line(&mut self, prefix: &str) -> String {
        let deadline = Instant::now() + BOUND;
        loop {
            let left = deadline.saturating_duration_since(Instant::now());
            let Ok(line) = self.err.recv_timeout(left) else {
                panic!(
                    "no {prefix:?} line within {BOUND:?}; stderr was {:?}",
                    self.seen
                );
            };
            let matched = line.starts_with(prefix);
            self.seen.push(line.clone());
            if matched {
                return line;
            }
        }
    }

    fn finish(mut self) -> Done {
        let deadline = Instant::now() + BOUND;
        let status = loop {
            match self.child.try_wait().expect("wait on prism run") {
                Some(status) => break status,
                None if Instant::now() >= deadline => {
                    let _ = self.child.kill();
                    let _ = self.child.wait();
                    self.reaped = true;
                    panic!("no exit within {BOUND:?}; stderr was {:?}", self.seen);
                }
                None => thread::sleep(Duration::from_millis(25)),
            }
        };
        self.reaped = true;
        let stdout = self
            .out
            .take()
            .expect("stdout reader")
            .join()
            .expect("stdout thread");
        // The child is gone, so its end of the pipe is closed and this drains to
        // the last line rather than to the timeout.
        while let Ok(line) = self.err.recv_timeout(Duration::from_secs(1)) {
            self.seen.push(line);
        }
        Done {
            ok: status.success(),
            stdout,
            stderr: std::mem::take(&mut self.seen).join("\n"),
        }
    }
}

impl Drop for Kid {
    fn drop(&mut self) {
        if !self.reaped {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

impl Done {
    /// What the program itself printed. `prism run` echoes the value `main`
    /// returned on a final line, which is the CLI reporting rather than program
    /// output; left in, it would land in the middle of the concatenation this
    /// gate is about.
    fn printed(&self) -> &str {
        self.stdout
            .strip_suffix("=> ()\n")
            .unwrap_or_else(|| panic!("no run echo at the end of {:?}", self.stdout))
    }
}

fn fixture() -> PathBuf {
    Path::new(FIXTURE).to_path_buf()
}

/// The address the receiver's listener was given. It arrives on standard error
/// on purpose: standard output is the numbered result this gate concatenates.
fn address_of(kid: &mut Kid) -> String {
    let line = kid.await_line("address ");
    line["address ".len()..].to_string()
}

fn whole_run() -> String {
    let done = Kid::spawn(&fixture(), &["whole"]).finish();
    assert!(done.ok, "the uninterrupted run failed: {}", done.stderr);
    done.printed().to_string()
}

/// The whole gate: two processes, one socket, and a run that is cut in half and
/// still adds up. `extra` is passed to both roles, which is how the same
/// exchange is driven over one-byte reads and writes.
fn split_run(extra: &[&str]) {
    let program = fixture();
    let mut receiving = vec!["receive"];
    receiving.extend_from_slice(extra);
    let mut receiver = Kid::spawn(&program, &receiving);
    let address = address_of(&mut receiver);
    let mut sending = vec!["send", address.as_str()];
    sending.extend_from_slice(extra);
    let sent = Kid::spawn(&program, &sending).finish();
    let landed = receiver.finish();

    assert!(sent.ok, "sender failed: {}", sent.stderr);
    assert!(landed.ok, "receiver failed: {}", landed.stderr);
    assert!(
        sent.stderr.contains("place Ok(())"),
        "the transport did not report delivery: {}",
        sent.stderr
    );
    assert!(
        landed.stderr.contains("land ok"),
        "the receiver did not land the envelope: {}",
        landed.stderr
    );
    // The halves are checked before their sum, because the sum alone would also
    // hold if one process had run the whole thing and the other none of it.
    assert_eq!(sent.printed(), PREFIX, "the sender ran past the cut");
    assert_eq!(
        landed.printed(),
        SUFFIX,
        "the receiver did not land at the cut"
    );
    assert_eq!(
        format!("{}{}", sent.printed(), landed.printed()),
        whole_run(),
        "the two halves are not the uninterrupted run"
    );
}

/// Start a receiver and hand its listener one hand-written frame. The client is a
/// plain socket rather than the fixture's own sender because the point is to
/// write frames the sender never would.
fn receiver_given(frame: &[u8]) -> Done {
    let mut receiver = Kid::spawn(&fixture(), &["receive"]);
    let address = address_of(&mut receiver);
    {
        let mut sock = TcpStream::connect(&address).expect("connect to the receiver");
        sock.write_all(frame).expect("write the frame");
        sock.flush().expect("flush the frame");
    }
    receiver.finish()
}

fn refused(frame: &[u8], expected: &str) {
    let done = receiver_given(frame);
    assert!(
        done.ok,
        "the receiver did not exit cleanly: {}",
        done.stderr
    );
    assert!(
        done.stderr.contains(expected),
        "expected {expected:?}, got {:?}",
        done.stderr
    );
    assert_eq!(done.printed(), "", "a refused envelope still printed");
}

#[test]
fn a_continuation_crosses_two_processes_and_the_halves_rejoin() {
    split_run(&[]);
}

#[test]
fn the_same_exchange_survives_one_byte_reads_and_writes() {
    split_run(&["slow"]);
}

#[test]
fn an_envelope_from_other_code_is_refused_rather_than_landed() {
    let dir = TempDir::new("teleport-tcp", "foreign");
    // The same program with one constant changed, which is a different bundle and
    // so a different code identity. Nothing about the frame changes: what the
    // receiver refuses is what the envelope is, not how it arrived.
    let source = std::fs::read_to_string(FIXTURE).expect("read the fixture");
    let variant = source.replace("let last_step : Int = 10", "let last_step : Int = 11");
    assert_ne!(variant, source, "the constant this rewrite names has moved");
    let other = dir.join("teleport_tcp.pr");
    std::fs::write(&other, variant).expect("write the variant");

    let mut receiver = Kid::spawn(&fixture(), &["receive"]);
    let address = address_of(&mut receiver);
    let sent = Kid::spawn(&other, &["send", address.as_str()]).finish();
    let landed = receiver.finish();

    // Delivery succeeded: the envelope crossed the socket and was refused after
    // it arrived, which is the only place code identity can be checked.
    assert!(
        sent.stderr.contains("place Ok(())"),
        "the foreign envelope was not delivered: {}",
        sent.stderr
    );
    assert!(
        landed.stderr.contains("land Teleport.Foreign"),
        "expected a foreign refusal, got {:?}",
        landed.stderr
    );
    assert_eq!(landed.printed(), "", "a foreign envelope was landed anyway");
}

#[test]
fn a_peer_that_closes_before_the_header_is_an_end_of_stream() {
    refused(&[], "receive Net.Closed");
}

#[test]
fn a_frame_that_stops_short_of_its_own_length_is_refused() {
    // A header claiming 64 bytes, eight bytes of body, and then the close.
    let mut frame = vec![0, 0, 0, 64];
    frame.extend_from_slice(b"12345678");
    refused(&frame, "receive Net.Closed");
}

#[test]
fn a_frame_larger_than_the_reader_will_hold_is_refused_at_its_header() {
    // One byte past the fixture's bound, refused before anything is read for it.
    refused(&[0, 0x10, 0, 1], "receive Net.Limit");
}

#[test]
fn a_frame_claiming_no_body_is_refused() {
    refused(&[0, 0, 0, 0], "receive Net.Invalid");
}

#[test]
fn a_well_framed_body_that_is_not_an_envelope_is_refused_by_the_codec() {
    let mut frame = vec![0, 0, 0, 8];
    frame.extend_from_slice(b"garbage!");
    refused(&frame, "land Teleport.Malformed");
}

#[test]
fn a_transport_with_nowhere_to_connect_reports_undelivered() {
    // A port learned by binding it and then letting it go. Something else may
    // take it in between, which is why the assertion is that the transport
    // refused rather than which refusal the kernel chose.
    let address = {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind a loopback port");
        listener
            .local_addr()
            .expect("read the bound address")
            .to_string()
    };
    let sent = Kid::spawn(&fixture(), &["send", address.as_str()]).finish();
    assert!(sent.ok, "the sender did not exit cleanly: {}", sent.stderr);
    assert!(
        sent.stderr.contains("connect Net."),
        "the transport did not report why: {}",
        sent.stderr
    );
    assert!(
        sent.stderr.contains("place Err(Teleport.Undelivered)"),
        "expected an undelivered placement, got {:?}",
        sent.stderr
    );
    // The prefix still ran. A placement that failed is not a run that was undone.
    assert_eq!(sent.printed(), PREFIX, "the prefix did not run");
}
