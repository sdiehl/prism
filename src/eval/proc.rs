//! The interpreter's half of the child-process boundary (`runtime/prism_proc.c`
//! is the native half). One call runs a graph of stages to completion: resolve
//! each program on the parent's `PATH`, spawn it with its standard output piped
//! into the next stage, feed the first stage its input, drain the last stage's
//! output and every stage's error stream under their limits and the deadline,
//! and reap every child. A single command is the graph of one stage. The
//! requests and responses are the byte layouts `lib/std/Proc.pr` encodes and
//! decodes.
//!
//! The two halves have to answer the same request with the same response, so
//! every choice the host could make differently is made here explicitly rather
//! than left to `std::process`: the program is resolved before spawning (its
//! own lookup would search the child's `PATH` once the environment is edited),
//! and a stream is over its limit exactly when the child has written more than
//! the limit to it, whatever size the reads came back in.

// Without a process host (wasm) every request is refused before it is read, so
// the decoded fields and most outcome tags exist only for the unix host. The
// codec still compiles there so both targets share one wire layout.
#![cfg_attr(not(unix), expect(dead_code))]

// The classification codes, in step with the `#define`s at the top of
// `runtime/prism_proc.c` and with `proc_error` in `lib/std/Proc.pr`.
const OTHER: i64 = 0;
const NOT_FOUND: i64 = 1;
const DENIED: i64 = 2;
const INVALID: i64 = 3;
const LIMIT: i64 = 4;

const VERSION: u64 = 1;
const MAX_CAPTURE: u64 = 256 * 1024 * 1024;

/// The outcome tags of the response, in `proc_status` order.
#[derive(Clone, Copy)]
enum Status {
    Exited(i64),
    Signaled(i64),
    SpawnFailed(i64),
    OutputLimit(u8),
    Deadline,
    Aborted(i64),
}

// What becomes of one of the child's output streams.
#[derive(Clone, Copy)]
enum Policy {
    Discard,
    Capture(u64),
}

struct Stage {
    program: String,
    args: Vec<String>,
    cwd: Option<String>,
    clean: bool,
    edits: Vec<(String, Option<String>)>,
    stdin: Option<Vec<u8>>,
    outputs: [Policy; 2],
}

struct Request {
    stages: Vec<Stage>,
    deadline_ms: Option<u64>,
}

/// What a graph produced: each stage's status, the last stage's output, and
/// each stage's error stream.
struct Answer {
    statuses: Vec<Status>,
    out: Vec<u8>,
    errs: Vec<Vec<u8>>,
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn uv(&mut self) -> Option<u64> {
        let mut value: u64 = 0;
        for shift in (0..64).step_by(7) {
            let byte = *self.bytes.get(self.at)?;
            self.at += 1;
            value |= u64::from(byte & 0x7f).checked_shl(shift)?;
            if byte < 0x80 {
                return Some(value);
            }
        }
        None
    }

    fn bytes(&mut self) -> Option<Vec<u8>> {
        let n = usize::try_from(self.uv()?).ok()?;
        let end = self.at.checked_add(n)?;
        let out = self.bytes.get(self.at..end)?.to_vec();
        self.at = end;
        Some(out)
    }

    // A string the child will see: valid UTF-8 (it came from a Prism `String`)
    // and free of NUL, which no host can pass through an `exec`.
    fn text(&mut self) -> Option<String> {
        let s = String::from_utf8(self.bytes()?).ok()?;
        (!s.contains('\0')).then_some(s)
    }

    fn output(&mut self) -> Option<Policy> {
        match self.uv()? {
            0 => Some(Policy::Discard),
            1 => self.uv().filter(|n| *n <= MAX_CAPTURE).map(Policy::Capture),
            _ => None,
        }
    }

    fn stage(&mut self) -> Option<Stage> {
        let program = self.text().filter(|p| !p.is_empty())?;
        let args = (0..self.uv()?)
            .map(|_| self.text())
            .collect::<Option<_>>()?;
        let cwd = match self.uv()? {
            0 => None,
            1 => Some(self.text()?),
            _ => return None,
        };
        let clean = match self.uv()? {
            0 => false,
            1 => true,
            _ => return None,
        };
        let edits = (0..self.uv()?)
            .map(|_| {
                let op = self.uv()?;
                let key = self.text().filter(|k| !k.is_empty() && !k.contains('='))?;
                match op {
                    0 => Some((key, Some(self.text()?))),
                    1 => Some((key, None)),
                    _ => None,
                }
            })
            .collect::<Option<_>>()?;
        let stdin = match self.uv()? {
            0 => None,
            1 => Some(self.bytes()?),
            _ => return None,
        };
        let outputs = [self.output()?, self.output()?];
        Some(Stage {
            program,
            args,
            cwd,
            clean,
            edits,
            stdin,
            outputs,
        })
    }

    // The deadline closes every request; a request is only accepted whole.
    fn finish(&mut self, stages: Vec<Stage>) -> Option<Request> {
        let deadline_ms = self.uv()?.checked_sub(1);
        (self.at == self.bytes.len()).then_some(Request {
            stages,
            deadline_ms,
        })
    }
}

fn decode(bytes: &[u8]) -> Option<Request> {
    let mut r = Reader { bytes, at: 0 };
    if r.uv()? != VERSION {
        return None;
    }
    let stage = r.stage()?;
    r.finish(vec![stage])
}

// A pipeline is one or more stages; only the first may be fed, since every
// later stage reads the one before it.
fn decode_pipeline(bytes: &[u8]) -> Option<Request> {
    let mut r = Reader { bytes, at: 0 };
    if r.uv()? != VERSION {
        return None;
    }
    let n = r.uv().filter(|n| *n >= 1 && *n <= bytes.len() as u64)?;
    let stages: Vec<Stage> = (0..n).map(|_| r.stage()).collect::<Option<_>>()?;
    if stages.iter().skip(1).any(|s| s.stdin.is_some()) {
        return None;
    }
    r.finish(stages)
}

/// The program names a request runs, for the provenance event: one for a
/// command, every stage's joined by ` | ` for a pipeline, and empty when the
/// request does not decode.
pub(super) fn program_of(req: &[u8], pipeline: bool) -> String {
    let request = if pipeline {
        decode_pipeline(req)
    } else {
        decode(req)
    };
    request.map_or_else(String::new, |r| {
        let names: Vec<&str> = r.stages.iter().map(|s| s.program.as_str()).collect();
        names.join(" | ")
    })
}

fn put_uv(buf: &mut Vec<u8>, mut n: u64) {
    while n >= 0x80 {
        buf.push(u8::try_from(n & 0x7f).unwrap_or(0) | 0x80);
        n >>= 7;
    }
    buf.push(u8::try_from(n).unwrap_or(0));
}

fn put_status(buf: &mut Vec<u8>, status: Status) {
    let (tag, n) = match status {
        Status::Exited(c) => (0, c),
        Status::Signaled(s) => (1, s),
        Status::SpawnFailed(e) => (2, e),
        Status::OutputLimit(s) => (3, i64::from(s)),
        Status::Deadline => (4, 0),
        Status::Aborted(e) => (5, e),
    };
    put_uv(buf, tag);
    put_uv(buf, u64::try_from(n).unwrap_or(0));
}

fn put_bytes(buf: &mut Vec<u8>, bytes: &[u8]) {
    put_uv(buf, bytes.len() as u64);
    buf.extend_from_slice(bytes);
}

/// Run the command `req` and answer the encoded response. Never fails: a
/// request that does not decode is a `SpawnFailed(Invalid)` like any other
/// refusal.
pub(super) fn collect(req: &[u8]) -> Vec<u8> {
    let a = decode(req).map_or_else(
        || Answer {
            statuses: vec![Status::SpawnFailed(INVALID)],
            out: Vec::new(),
            errs: vec![Vec::new()],
        },
        |r| host::run(&r),
    );
    let mut buf = Vec::with_capacity(a.out.len() + a.errs[0].len() + 16);
    put_uv(&mut buf, VERSION);
    put_status(&mut buf, a.statuses[0]);
    put_bytes(&mut buf, &a.out);
    put_bytes(&mut buf, &a.errs[0]);
    buf
}

/// Run the pipeline `req` and answer the encoded response. A request that does
/// not decode answers as one stage refused as invalid.
pub(super) fn collect_pipeline(req: &[u8]) -> Vec<u8> {
    let a = decode_pipeline(req).map_or_else(
        || Answer {
            statuses: vec![Status::SpawnFailed(INVALID)],
            out: Vec::new(),
            errs: vec![Vec::new()],
        },
        |r| host::run(&r),
    );
    let mut buf = Vec::with_capacity(a.out.len() + 16);
    put_uv(&mut buf, VERSION);
    put_uv(&mut buf, a.statuses.len() as u64);
    for status in &a.statuses {
        put_status(&mut buf, *status);
    }
    put_bytes(&mut buf, &a.out);
    for err in &a.errs {
        put_bytes(&mut buf, err);
    }
    buf
}

#[cfg(unix)]
mod host {
    use std::ffi::OsStr;
    use std::io::{ErrorKind, Write as _};
    use std::os::unix::ffi::OsStrExt as _;
    use std::os::unix::fs::PermissionsExt as _;
    use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
    use std::path::{Path, PathBuf};
    use std::process::{Child, ChildStdout, Command, Stdio};
    use std::sync::mpsc;
    use std::time::{Duration, Instant};

    use super::{Answer, Policy, Request, Stage, Status, DENIED, LIMIT, NOT_FOUND, OTHER};

    const CHUNK: usize = 1 << 16;
    const POLL: Duration = Duration::from_millis(1);

    fn executable(p: &Path) -> bool {
        p.metadata()
            .is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
    }

    // The parent's `PATH`, absolute entries only; a name with a `/` is not
    // searched for.
    fn resolve(program: &str) -> Option<PathBuf> {
        if program.contains('/') {
            return Some(PathBuf::from(program));
        }
        let path = std::env::var_os("PATH")?;
        path.as_bytes()
            .split(|b| *b == b':')
            .map(|dir| Path::new(OsStr::from_bytes(dir)))
            .filter(|dir| dir.is_absolute())
            .map(|dir| dir.join(program))
            .find(|cand| executable(cand))
    }

    fn classify(e: &std::io::Error) -> i64 {
        match e.kind() {
            ErrorKind::NotFound => NOT_FOUND,
            ErrorKind::PermissionDenied => DENIED,
            ErrorKind::WouldBlock | ErrorKind::OutOfMemory => LIMIT,
            _ if e.raw_os_error().is_some_and(|n| OUT_OF_FILES.contains(&n)) => LIMIT,
            _ => OTHER,
        }
    }

    // ENFILE and EMFILE, which are the same numbers on every Unix: the host is
    // out of descriptors, not refusing.
    const OUT_OF_FILES: [i32; 2] = [23, 24];

    // A stream is drained into a slot: slot 0 is the last stage's output and
    // slot 1 + i is stage i's error stream.
    enum Event {
        Done(usize, Vec<u8>),
        Over(usize),
        Failed,
    }

    fn drain(mut pipe: impl std::io::Read, slot: usize, limit: u64, tx: &mpsc::Sender<Event>) {
        let mut data = Vec::new();
        let mut chunk = vec![0u8; CHUNK];
        loop {
            match pipe.read(&mut chunk) {
                Ok(0) => {
                    let _ = tx.send(Event::Done(slot, data));
                    return;
                }
                Ok(n) => {
                    data.extend_from_slice(&chunk[..n]);
                    if data.len() as u64 > limit {
                        let _ = tx.send(Event::Over(slot));
                        return;
                    }
                }
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                Err(_) => {
                    let _ = tx.send(Event::Failed);
                    return;
                }
            }
        }
    }

    fn piped(on: bool) -> Stdio {
        if on {
            Stdio::piped()
        } else {
            Stdio::null()
        }
    }

    // Spawn stage `s`. Its input is the stage before it, or the feed for the
    // first stage; a stage whose upstream never started reads an empty input.
    fn spawn(s: &Stage, upstream: Option<Stdio>, last: bool) -> Result<Child, i64> {
        let program = resolve(&s.program).ok_or(NOT_FOUND)?;
        let mut cmd = Command::new(program);
        cmd.arg0(&s.program).args(&s.args);
        if let Some(dir) = &s.cwd {
            cmd.current_dir(dir);
        }
        if s.clean {
            cmd.env_clear();
        }
        for (key, value) in &s.edits {
            match value {
                Some(v) => cmd.env(key, v),
                None => cmd.env_remove(key),
            };
        }
        let capture = |p: Policy| matches!(p, Policy::Capture(_));
        cmd.stdin(upstream.unwrap_or_else(|| piped(s.stdin.is_some())))
            .stdout(piped(!last || capture(s.outputs[0])))
            .stderr(piped(capture(s.outputs[1])));
        cmd.spawn().map_err(|e| classify(&e))
    }

    // The host has given up on the graph: every child it started is killed and
    // reaped, and the streams are dropped, since what any stage had written by
    // then depends on scheduling. For the same reason every stage that started
    // answers `halt`, even one that had already exited; a stage that never
    // started keeps its refusal. Killing a child already reaped is a no-op.
    fn halted(
        children: &mut [Option<Child>],
        mut statuses: Vec<Status>,
        halt: impl Fn(usize) -> Status,
    ) -> Answer {
        for (i, child) in children.iter_mut().enumerate() {
            if let Some(c) = child {
                let _ = c.kill();
                let _ = c.wait();
                statuses[i] = halt(i);
            }
        }
        let n = statuses.len();
        Answer {
            statuses,
            out: Vec::new(),
            errs: vec![Vec::new(); n],
        }
    }

    pub(super) fn run(r: &Request) -> Answer {
        let n = r.stages.len();
        let deadline = r
            .deadline_ms
            .map(|ms| Instant::now() + Duration::from_millis(ms));
        let mut statuses = vec![Status::Aborted(OTHER); n];
        let mut children: Vec<Option<Child>> = Vec::with_capacity(n);
        let mut streams: Vec<(usize, Box<dyn std::io::Read + Send>, u64)> = Vec::new();
        let mut upstream: Option<ChildStdout> = None;
        for (i, s) in r.stages.iter().enumerate() {
            let last = i + 1 == n;
            let input = (i > 0).then(|| upstream.take().map_or_else(Stdio::null, Stdio::from));
            let mut child = match spawn(s, input, last) {
                Ok(c) => c,
                Err(code) => {
                    statuses[i] = Status::SpawnFailed(code);
                    children.push(None);
                    continue;
                }
            };
            // A child that stops reading closes its input early; that is its
            // choice, not a failure, so a broken pipe ends the write quietly.
            // The writer is detached: it finishes when the child's end closes,
            // which a kill does.
            if let (Some(mut sink), Some(bytes)) = (child.stdin.take(), s.stdin.clone()) {
                std::thread::spawn(move || {
                    let _ = sink.write_all(&bytes);
                });
            }
            if last {
                if let (Some(p), Policy::Capture(limit)) = (child.stdout.take(), s.outputs[0]) {
                    streams.push((0, Box::new(p), limit));
                }
            } else {
                upstream = child.stdout.take();
            }
            if let (Some(p), Policy::Capture(limit)) = (child.stderr.take(), s.outputs[1]) {
                streams.push((1 + i, Box::new(p), limit));
            }
            children.push(Some(child));
        }
        let (tx, rx) = mpsc::channel();
        let mut open = streams.len();
        for (slot, pipe, limit) in streams {
            let tx = tx.clone();
            std::thread::spawn(move || drain(pipe, slot, limit, &tx));
        }
        drop(tx);
        let mut captured = vec![Vec::new(); n + 1];
        while open > 0 {
            let event = match deadline {
                None => rx.recv().map_err(|_| ()),
                Some(at) => match rx.recv_timeout(at.saturating_duration_since(Instant::now())) {
                    Ok(ev) => Ok(ev),
                    Err(mpsc::RecvTimeoutError::Timeout) => {
                        return halted(&mut children, statuses, |_| Status::Deadline)
                    }
                    Err(mpsc::RecvTimeoutError::Disconnected) => Err(()),
                },
            };
            match event {
                Ok(Event::Done(slot, data)) => {
                    captured[slot] = data;
                    open -= 1;
                }
                Ok(Event::Over(slot)) => {
                    let (stage, stream) = if slot == 0 { (n - 1, 0) } else { (slot - 1, 1) };
                    return halted(&mut children, statuses, |i| {
                        if i == stage {
                            Status::OutputLimit(stream)
                        } else {
                            Status::Aborted(LIMIT)
                        }
                    });
                }
                Ok(Event::Failed) | Err(()) => {
                    return halted(&mut children, statuses, |_| Status::Aborted(OTHER))
                }
            }
        }
        for i in 0..n {
            let Some(child) = children[i].as_mut() else {
                continue;
            };
            let waited = loop {
                let Some(at) = deadline else {
                    break child.wait().ok();
                };
                match child.try_wait() {
                    Ok(Some(s)) => break Some(s),
                    Ok(None) if Instant::now() >= at => {
                        return halted(&mut children, statuses, |_| Status::Deadline)
                    }
                    Ok(None) => std::thread::sleep(POLL),
                    Err(_) => break None,
                }
            };
            let Some(status) = waited else {
                return halted(&mut children, statuses, |_| Status::Aborted(OTHER));
            };
            statuses[i] = match (status.code(), status.signal()) {
                (Some(c), _) => Status::Exited(i64::from(c)),
                (None, Some(s)) => Status::Signaled(i64::from(s)),
                (None, None) => Status::Aborted(OTHER),
            };
        }
        let out = std::mem::take(&mut captured[0]);
        Answer {
            statuses,
            out,
            errs: captured.split_off(1),
        }
    }
}

#[cfg(not(unix))]
mod host {
    use super::{Answer, Request, Status, OTHER};

    pub(super) fn run(r: &Request) -> Answer {
        let n = r.stages.len();
        Answer {
            statuses: vec![Status::SpawnFailed(OTHER); n],
            out: Vec::new(),
            errs: vec![Vec::new(); n],
        }
    }
}
