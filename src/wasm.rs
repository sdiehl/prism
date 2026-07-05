//! Browser entry points for the interpreter playground.
//!
//! The whole compiler front-end and tree-walking interpreter run in wasm. Only
//! the LLVM/MLIR back-ends are absent (the `native` feature is off in a wasm
//! build).
use logos::Logos;
use wasm_bindgen::prelude::*;

use std::collections::HashSet;
use std::fmt::Write as _;
use std::path::Path;

use crate::lex::Token;
use crate::resolve::default_roots;
use crate::{
    check, example_program, format as fmt_src, interpret, namespace_root, off_platform_builtins,
    resume_on, suspend_line_cuts, suspend_on, with_prelude, Config, SuspendResult,
};

// The web host owns the effects. A browser can serve more of them than it might
// seem: `print` is buffered and `read_line` host-fed, the `Random` capability is
// a deterministic SplitMix64 stream (pure arithmetic, identical to the native
// oracle), and the `Env` capability reads an empty environment (`getenv` returns
// "", no args). What it genuinely cannot provide is host file IO and process
// control. A snippet declares its platform by which builtins it reaches in the
// elaborated core, and a use of an unservable one is reported up front rather
// than failing silently at runtime. The check runs after type-checking and
// elaboration so indirection like `let f = read_file; f()` is caught as soundly
// as a direct `read_file(..)` call.

// Off-platform builtins the browser can still serve with a sensible default: the
// `Env` capability inputs answer from an empty environment. (`Random` never
// reaches this list; it lowers to a pure `Rand` node the interpreter evaluates.)
const BROWSER_SERVABLE: &[&str] = &["getenv", "args_count", "arg"];

/// Run a snippet and return its captured `print` transcript verbatim.
///
/// The exact bytes emitted, the same the differential oracle compares. On any
/// front-end or runtime error, returns the rendered diagnostic instead.
#[wasm_bindgen]
#[must_use]
pub fn run(src: &str) -> String {
    // A doc snippet without `main` (a bare expression or `let`-block) is wrapped
    // as an implicit `main`; when wrapped, its result value is shown (`=> v`)
    // since it prints nothing. A full program is run and its transcript shown.
    let program = example_program(src);
    let wrapped = program != src;
    let full = with_prelude(&program);
    match off_platform_builtins(&full, Path::new(".")) {
        Ok(off) => {
            let blocked: Vec<_> = off
                .into_iter()
                .filter(|b| !BROWSER_SERVABLE.contains(b))
                .collect();
            if !blocked.is_empty() {
                return format!(
                    "error: the web platform cannot provide host file or process IO here: {}",
                    blocked.join(", ")
                );
            }
        }
        Err(e) => return format!("error: {e}"),
    }
    match interpret(&full) {
        // A full program: the exact transcript (real emitted newlines,
        // byte-for-byte what the oracle compares). A wrapped expression: the
        // value, after any transcript it produced.
        Ok(r) => {
            if wrapped {
                let v = r.value.show();
                if r.term.is_empty() {
                    format!("=> {v}")
                } else {
                    format!("{}\n=> {v}", r.term.trim_end_matches('\n'))
                }
            } else {
                r.term
            }
        }
        Err(e) => format!("error: {e}"),
    }
}

// The scrubber-style residents (boids, pendulum). Each example's definitions are
// shared verbatim with its terminal corpus form; the browser appends its own
// `main` that prints the whole trajectory, so nothing about the motion depends on
// which entry point runs it. The split marker fences off the example's own `main`
// so the two entry points never collide in one program. The same sentinel lives
// in the examples and in tests/*_scrubber.rs.
const SCRUBBER_MAIN_SPLIT: &str = "-- @scrubber:main-below";
const BOIDS_SRC: &str = include_str!("../examples/boids.pr");
const PENDULUM_SRC: &str = include_str!("../examples/pendulum.pr");

// The chaos-counter swarm: a concurrent fiber swarm over a channel under a
// seeded-shuffle scheduler. Its kernel (everything above the sentinel) is reused
// verbatim; the browser appends a `main` that reports one batch of schedules.
const CHAOS_MAIN_SPLIT: &str = "-- @chaos:main-below";
const CHAOS_SRC: &str = include_str!("../examples/chaos_swarm.pr");

// Slice a scrubber resident's kernel (everything above the sentinel) and run it
// under a `main` that prints the whole trajectory for `steps` frames. Both
// residents expose a `run_trace(n)` with the same contract.
fn scrubber_trace(src: &str, steps: u32) -> String {
    let defs = src.split(SCRUBBER_MAIN_SPLIT).next().unwrap_or(src);
    let driver = format!("{defs}\nfn main() = print(run_trace({steps}))\n");
    match interpret(&with_prelude(&driver)) {
        Ok(r) => r.term,
        Err(e) => format!("error: {e}"),
    }
}

/// Run the boids swarm for `steps` deterministic steps and return the whole
/// trajectory as text.
///
/// The first line is `W H` (the toroidal world dimensions); each following line
/// is one frame, a space-separated list of `x,y` integer positions. Frame N is
/// `step` composed N times on the seeded swarm, a pure function of the index, so
/// the browser scrubber positions its playhead at any frame by replaying to it.
/// On any front-end or runtime error, returns the rendered diagnostic instead.
#[wasm_bindgen]
#[must_use]
pub fn boids_run(steps: u32) -> String {
    scrubber_trace(BOIDS_SRC, steps)
}

/// Run the boids swarm for `steps` steps and return the whole trajectory in
/// FULL state: like [`boids_run`], but each boid is `x,y,vx,vy` (position and
/// velocity), not just `x,y`.
///
/// The velocity is what a branching timeline needs: to fork at frame N and
/// continue the run, the frontend perturbs that frame's full state and hands it
/// to [`boids_run_from`]. Positions alone cannot be continued (one `step` reads
/// each boid's velocity), so the branch demo drives on this trajectory.
#[wasm_bindgen]
#[must_use]
pub fn boids_run_full(steps: u32) -> String {
    let defs = BOIDS_SRC
        .split(SCRUBBER_MAIN_SPLIT)
        .next()
        .unwrap_or(BOIDS_SRC);
    let driver = format!("{defs}\nfn main() = print(run_trace_full({steps}))\n");
    match interpret(&with_prelude(&driver)) {
        Ok(r) => r.term,
        Err(e) => format!("error: {e}"),
    }
}

/// Continue the boids swarm from an arbitrary state `state` for `steps` steps,
/// returning the full-state trajectory (`boids_run_full`'s format) from that
/// state.
///
/// `state` is one full-state frame: a space-separated list of `x,y,vx,vy`
/// integer boids, exactly a line of [`boids_run_full`]'s output. The branching
/// demo forks a timeline by taking frame N of the base run, perturbing one boid,
/// and passing the perturbed frame here. Because `run_trace_from` is a pure
/// function of the swarm and the step count, replaying a branch with the same
/// perturbed state is byte-identical: that is the determinism claim the two
/// side-by-side timelines rest on. A malformed `state` returns an `error:` line.
#[wasm_bindgen]
#[must_use]
pub fn boids_run_from(state: &str, steps: u32) -> String {
    let swarm = match boids_state_literal(state) {
        Ok(lit) => lit,
        Err(e) => return format!("error: {e}"),
    };
    let defs = BOIDS_SRC
        .split(SCRUBBER_MAIN_SPLIT)
        .next()
        .unwrap_or(BOIDS_SRC);
    let driver = format!("{defs}\nfn main() = print(run_trace_from({swarm}, {steps}))\n");
    match interpret(&with_prelude(&driver)) {
        Ok(r) => r.term,
        Err(e) => format!("error: {e}"),
    }
}

// How many integers describe one boid in a full-state frame: `x,y,vx,vy`.
const BOID_FIELDS: usize = 4;

// Parse a full-state frame ("x,y,vx,vy x,y,vx,vy ...") into a Prism list literal
// of 4-tuples, `[(x,y,vx,vy), ...]`, validating every field is an integer so a
// hand-edited or truncated state is rejected up front rather than producing a
// parse error deep in the generated driver. The ints are re-emitted verbatim, so
// the swarm the frontend forked is the swarm the kernel continues.
fn boids_state_literal(state: &str) -> Result<String, String> {
    let mut tuples: Vec<String> = Vec::new();
    for boid in state.split_whitespace() {
        let fields: Vec<&str> = boid.split(',').collect();
        if fields.len() != BOID_FIELDS {
            return Err(format!("malformed boid state '{boid}' (want x,y,vx,vy)"));
        }
        for f in &fields {
            if f.parse::<i64>().is_err() {
                return Err(format!("non-integer boid field '{f}'"));
            }
        }
        tuples.push(format!("({})", fields.join(",")));
    }
    if tuples.is_empty() {
        return Err("empty boid state".to_string());
    }
    Ok(format!("[{}]", tuples.join(",")))
}

/// Run the double pendulum for `steps` frames and return the whole trajectory as
/// text.
///
/// The first line is the maximum reach (rod length + rod length), so the renderer
/// can scale the pivot's disk to the canvas; each following line is one frame,
/// `x1,y1,x2,y2`, the two bob centers with the pivot at the origin and y pointing
/// down. Frame N is the symplectic integrator composed N times on the chaotic
/// initial condition, a pure function of the index, so the scrubber positions its
/// playhead at any frame by replaying to it. Every op is IEEE Float over the
/// vendored libm, so the chaos is bit-identical on every backend and every replay.
/// On any front-end or runtime error, returns the rendered diagnostic instead.
#[wasm_bindgen]
#[must_use]
pub fn pendulum_run(steps: u32) -> String {
    scrubber_trace(PENDULUM_SRC, steps)
}

/// Run one batch of `count` hostile schedules of the concurrent swarm, starting
/// at seed index `start`, and report how many landed on the reference final
/// state.
///
/// Returns three lines: `<agreed> <count> <refhash>` (agreed is how many of the
/// batch's schedules matched the global reference hash; it is always `count`,
/// which is the determinism claim), then the interleaving of the batch's first
/// two schedules as space-separated fiber ids. Each schedule is a distinct
/// seeded-shuffle of the same fibers over the same channel, so the two
/// interleavings differ while the hash does not. The browser calls this in
/// growing batches to tick a progressive counter without freezing the tab: the
/// count is what the frame budget affords, but every schedule genuinely agrees.
/// On any error, returns the rendered diagnostic instead.
#[wasm_bindgen]
#[must_use]
pub fn chaos_run(start: u32, count: u32) -> String {
    let defs = CHAOS_SRC
        .split(CHAOS_MAIN_SPLIT)
        .next()
        .unwrap_or(CHAOS_SRC);
    let driver = format!("{defs}\nfn main() = print(batch_report({start}, {count}, n_workers))\n");
    match interpret(&with_prelude(&driver)) {
        Ok(r) => r.term,
        Err(e) => format!("error: {e}"),
    }
}

// The teleport resident: a small deterministic program the browser suspends into
// a `kont` envelope in one tab and resumes in another. It prints a labeled,
// self-evidently continued sequence (one line per step, each naming its running
// index) so that when the second tab resumes it visibly carries the same count
// forward rather than restarting. The program is baked in so both tabs share one
// bundle: the receiving tab re-derives its code identity and refuses an envelope
// from any other program.
const TELEPORT_SRC: &str = "\
fn count(i, last) =\n\
\x20 if i > last then\n\
\x20   ()\n\
\x20 else\n\
\x20   println(\"step {i}: {i} squared is {i * i}\")\n\
\x20   count(i + 1, last)\n\
\n\
fn main() = count(1, 10)\n";

fn teleport_full() -> String {
    with_prelude(TELEPORT_SRC)
}

/// The baked teleport program's source, for the read-only panel beside the demo.
#[wasm_bindgen]
#[must_use]
pub fn teleport_source() -> String {
    TELEPORT_SRC.to_string()
}

fn teleport_roots() -> Vec<crate::resolve::Root> {
    default_roots(Path::new("."))
}

/// The code-identity digest (namespace root) of the baked teleport program.
///
/// Both tabs compute this from the same embedded source, so it is the hash the
/// receiver checks an incoming envelope against; the demo shows it as the proof
/// that teleport verifies code identity, not just moves bytes.
#[wasm_bindgen]
#[must_use]
pub fn teleport_bundle() -> String {
    namespace_root(&teleport_full(), &teleport_roots()).unwrap_or_else(|e| format!("error: {e}"))
}

/// The machine-step budget to pass [`teleport_prefix`]/[`teleport_suspend`] to
/// pause after each printed line, one entry per interior line boundary.
///
/// Lets the demo's control read in lines ("pause after line 3") rather than opaque
/// machine steps: the slider indexes this list. The last line is omitted because
/// pausing there is a completed run with nothing to teleport.
#[wasm_bindgen]
#[must_use]
pub fn teleport_cuts() -> Vec<u32> {
    suspend_line_cuts(&teleport_full(), &teleport_roots(), &Config::from_env()).map_or_else(
        |_| Vec::new(),
        |cuts| {
            cuts.into_iter()
                .filter_map(|c| u32::try_from(c).ok())
                .collect()
        },
    )
}

/// The teleport program's output up to `steps` machine steps.
///
/// This is what the sending tab has printed by the moment it suspends; followed by
/// [`teleport_resume`]'s output, it reproduces an uninterrupted run byte for byte.
#[wasm_bindgen]
#[must_use]
pub fn teleport_prefix(steps: u32) -> String {
    let mut out: Vec<u8> = Vec::new();
    let mut input = std::io::empty();
    match suspend_on(
        &teleport_full(),
        &teleport_roots(),
        &mut out,
        &mut input,
        steps as usize,
        &Config::from_env(),
    ) {
        Ok(_) => String::from_utf8_lossy(&out).into_owned(),
        Err(e) => format!("error: {e}"),
    }
}

/// Suspend the teleport program after `steps` machine steps and return the whole
/// continuation as `kont` envelope bytes: the value that flies between tabs.
///
/// An empty result means the program finished before `steps` (nothing left to
/// teleport). The bytes are the exact wire the receiver decodes; the animation
/// shows them literally.
#[wasm_bindgen]
#[must_use]
pub fn teleport_suspend(steps: u32) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut input = std::io::empty();
    match suspend_on(
        &teleport_full(),
        &teleport_roots(),
        &mut out,
        &mut input,
        steps as usize,
        &Config::from_env(),
    ) {
        Ok(SuspendResult::Suspended(bytes)) => bytes,
        // Completed before the budget, or a fault: nothing to teleport.
        _ => Vec::new(),
    }
}

/// Resume a `kont` envelope in the receiving tab and return the continued output.
///
/// The envelope is decoded totally (hostile bytes are rejected, not trusted) and
/// its bundle digest is checked against this program's freshly derived code
/// identity, so an envelope from a different program is refused by hash before a
/// step runs. On success the returned suffix, following the sender's prefix,
/// reproduces an uninterrupted run.
#[wasm_bindgen]
#[must_use]
pub fn teleport_resume(bytes: &[u8]) -> String {
    let mut out: Vec<u8> = Vec::new();
    let mut input = std::io::empty();
    match resume_on(
        &teleport_full(),
        &teleport_roots(),
        bytes,
        &mut out,
        &mut input,
        &Config::from_env(),
    ) {
        Ok(_) => String::from_utf8_lossy(&out).into_owned(),
        Err(e) => format!("error: {e}"),
    }
}

/// Pretty-print a snippet, or return the parse/lex error as text.
#[wasm_bindgen]
#[must_use]
pub fn fmt(src: &str) -> String {
    fmt_src(src).unwrap_or_else(|e| format!("error: {e}"))
}

// Coarse highlight category for one lexed token, matched in `web/index.html`.
const fn tok_class(t: &Token) -> &'static str {
    use Token::{
        Alias, As, Borrow, Catch, Class, Comment, Ctl, Deriving, Do, Effect, Elif, Else, False,
        Final, Float, Fn, For, Forall, Fun, Handle, Handler, Ident, If, Import, In, Instance, Int,
        InterpEnd, InterpMid, InterpStart, KwBool, KwChar, KwError, KwFloat, KwI64, KwInt,
        KwString, KwU64, KwUnit, Let, Mask, Match, Newtype, Of, Opaque, Pattern, Pub, QualName,
        Return, StringLit, Then, Throw, True, Try, Type, UIdent, Val, Var, Where, With,
    };
    match t {
        Fn | Pub | Import | As | Type | Newtype | Opaque | Effect | KwError | Throw | Try
        | Catch | Alias | Class | Instance | Pattern | Deriving | Where | Handle | With
        | Handler | Mask | Ctl | Final | Fun | Val | Return | Let | Var | Borrow | In | For
        | Do | If | Then | Else | Elif | Match | Of | Forall => "kw",
        True | False => "lit",
        KwInt | KwBool | KwUnit | KwFloat | KwChar | KwString | KwI64 | KwU64 => "ty",
        UIdent(_) | QualName(_) => "ctor",
        Int(_) | Float(_) => "num",
        Token::CharLit(_) | StringLit(_) | InterpStart(_) | InterpMid(_) | InterpEnd(_) => "str",
        Comment(_) => "com",
        Ident(_) => "id",
        _ => "op",
    }
}

/// A JSON array of `{s,e,c}` (byte start, byte end, highlight class) for every
/// token in `src`, for editor syntax highlighting. Lex errors are skipped here;
/// they surface through [`diagnostics`].
#[wasm_bindgen]
#[must_use]
pub fn tokens(src: &str) -> String {
    let parts: Vec<String> = Token::lexer(src)
        .spanned()
        .filter_map(|(res, sp)| {
            res.ok().map(|t| {
                format!(
                    r#"{{"s":{},"e":{},"c":"{}"}}"#,
                    sp.start,
                    sp.end,
                    tok_class(&t)
                )
            })
        })
        .collect();
    format!("[{}]", parts.join(","))
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < u32::from(crate::ASCII_PRINTABLE_LO) => {
                write!(out, "\\u{:04x}", c as u32).unwrap();
            }
            c => out.push(c),
        }
    }
    out
}

/// Compiler diagnostics for `src` as JSON.
///
/// Each entry is `{s,e,line,col,endLine,endCol,kind,msg}` with spans in the
/// snippet's own coordinates (the prepended prelude is subtracted). A hard
/// error aborts the front-end at the first one, so on failure this carries a
/// single `*Error` entry; on success it carries the type checker's non-fatal
/// `Warning`s (orphan/overlapping instances), of which there may be several.
#[wasm_bindgen]
#[must_use]
pub fn diagnostics(src: &str) -> String {
    let full = with_prelude(src);
    let pre = with_prelude("").len();
    let user = &full[pre..];
    // Render one diagnostic object for a raw `[raw_s, raw_e)` span into `full`,
    // rebased into the snippet's own coordinates. Spans that land entirely in
    // the prepended prelude have no place to point and are dropped.
    let entry = |raw_s: usize, raw_e: usize, kind: &str, msg: &str| -> Option<String> {
        if raw_e < pre {
            return None;
        }
        let s = raw_s.saturating_sub(pre).min(user.len());
        let end = raw_e.saturating_sub(pre).max(s + 1).min(user.len()).max(s);
        let (line, col) = crate::error::line_col(user, s);
        let (eline, ecol) = crate::error::line_col(user, end);
        Some(format!(
            r#"{{"s":{s},"e":{end},"line":{line},"col":{col},"endLine":{eline},"endCol":{ecol},"kind":"{}","msg":"{}"}}"#,
            json_escape(kind),
            json_escape(msg),
        ))
    };
    let objs: Vec<String> = match check(&full) {
        Err(e) => {
            let (raw_s, raw_e) = e
                .primary_span()
                .map_or((full.len(), full.len()), |r| (r.start, r.end));
            entry(raw_s, raw_e, e.kind(), &e.to_string())
                .into_iter()
                .collect()
        }
        Ok(checked) => checked
            .warnings
            .iter()
            .filter_map(|w| entry(w.span.start, w.span.end, "Warning", &w.msg))
            .collect(),
    };
    format!("[{}]", objs.join(","))
}

/// The fully lowered CBPV core IR of the snippet's own functions.
///
/// Prelude elided: effects lowered, reference counting and FBIP reuse applied.
/// The lowest-level view the browser can produce. The LLVM back-end is native
/// only.
#[wasm_bindgen]
#[must_use]
pub fn core_ir(src: &str) -> String {
    match crate::core_ir(src) {
        Ok(ir) => ir,
        Err(e) => format!("error: {e}"),
    }
}

/// The top-level type signatures of the snippet's own declarations (prelude
/// signatures elided), or the front-end error as text.
#[wasm_bindgen]
#[must_use]
pub fn dump(src: &str) -> String {
    let prelude: HashSet<String> = match check(&with_prelude("")) {
        Ok(c) => c.decls.iter().map(|d| d.name.clone()).collect(),
        Err(e) => return format!("error: {e}"),
    };
    match check(&with_prelude(src)) {
        Ok(c) => c
            .decls
            .iter()
            .filter(|d| !prelude.contains(&d.name))
            .map(|d| format!("{} : {}", d.name, d.ty.show()))
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("error: {e}"),
    }
}

/// The snippet's own definitions as a content-addressed Merkle DAG.
///
/// Returns a JSON array of `{name, hash, deps}` with the prelude elided: `hash`
/// is the short content hash of the definition's elaborated core, and `deps`
/// names the other user definitions it references. A definition's hash folds in
/// its dependencies' hashes, so editing one definition moves its hash and the
/// hash of everything that transitively depends on it, while independent code
/// keeps its address. This is the same addressing `dump core-hash` and the
/// on-disk store use; the browser only renders it. On a front-end error, returns
/// `{"error": "..."}`.
#[wasm_bindgen]
#[must_use]
pub fn hash_defs(src: &str) -> String {
    let err = |m: &str| serde_json::json!({ "error": m }).to_string();
    // Parse a `dump namespace` export (taken over elaborated core) into its doc.
    let namespace = |full: &str| -> Result<serde_json::Value, String> {
        let ns = crate::dump("namespace", full).map_err(|e| format!("{e}"))?;
        serde_json::from_str::<serde_json::Value>(&ns)
            .map_err(|_| "could not read namespace export".to_string())
    };
    let names_of = |doc: &serde_json::Value| -> Vec<String> {
        doc.get("defs")
            .and_then(serde_json::Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(|d| d.pointer("/meta/name").and_then(serde_json::Value::as_str))
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default()
    };
    // Names present with only the prelude compiled: everything here is library.
    // The namespace export is over elaborated core, where the prelude expands into
    // many mangled defs (instance methods, derived functions), so eliding by these
    // core-level names, not surface declarations, leaves exactly the user's own
    // definitions. A user-defined instance is absent here and so is kept.
    let prelude: HashSet<String> = match namespace(&with_prelude("")) {
        Ok(v) => names_of(&v).into_iter().collect(),
        Err(e) => return err(&e),
    };
    let doc = match namespace(&with_prelude(src)) {
        Ok(v) => v,
        Err(e) => return err(&e),
    };
    let Some(defs) = doc.get("defs").and_then(serde_json::Value::as_array) else {
        return err("namespace export had no defs");
    };
    // The namespace export lists a definition's dependencies by content hash
    // (names erased), so a hash -> name index over every definition, prelude
    // included, turns those edges back into the names the graph draws.
    let name_by_hash: std::collections::HashMap<&str, &str> = defs
        .iter()
        .filter_map(|d| Some((d.get("hash")?.as_str()?, d.pointer("/meta/name")?.as_str()?)))
        .collect();
    let mut out: Vec<serde_json::Value> = Vec::new();
    for d in defs {
        let name = match d.pointer("/meta/name").and_then(serde_json::Value::as_str) {
            Some(n) if !prelude.contains(n) => n,
            _ => continue,
        };
        let hash = d
            .get("hash")
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default();
        let short = &hash[..hash.len().min(crate::core::HASH_PREFIX_HEX)];
        let mut dep_names: Vec<&str> = d
            .pointer("/anon/deps")
            .and_then(serde_json::Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(serde_json::Value::as_str)
                    .filter_map(|h| name_by_hash.get(h).copied())
                    .filter(|n| !prelude.contains(*n))
                    .collect()
            })
            .unwrap_or_default();
        dep_names.sort_unstable();
        dep_names.dedup();
        out.push(serde_json::json!({ "name": name, "hash": short, "deps": dep_names }));
    }
    serde_json::Value::Array(out).to_string()
}

// The memo nodes of the incremental demand graph, in the order the demo lists
// them. `a`, `b`, `c` are the sources; the rest are derivations. Kept beside the
// program the export builds so the two never drift.
const INCR_MEMOS: &[&str] = &["total", "peak", "scaled", "alert", "board"];

/// One re-demand of a fixed incremental demand graph, for the
/// incremental-computation gallery resident.
///
/// The graph is three source cells `a`, `b`, `c` feeding `total = a + b + c`,
/// `peak = max(a, b, c)`, `scaled = total * 2`, `alert = peak * 10`, and
/// `board = scaled + alert`. The `payload` is `{"prev": {a,b,c} | null, "next":
/// {a,b,c}}`. With `prev` null this is the cold first demand: every derivation
/// recomputes. Otherwise it runs the real `Incr` engine with `prev`, changes the
/// sources to `next`, re-demands `board`, and classifies each cell: a derivation
/// whose body re-ran is `recomputed` if its value changed and `cutoff` if the
/// value was unchanged (so its dependents were spared), and one whose body never
/// ran is `cached`. Returns JSON `{"nodes": [{"name","value","state"}]}` or
/// `{"error": "..."}`.
#[wasm_bindgen]
#[must_use]
pub fn incr_run(payload: &str) -> String {
    let fail = |m: &str| serde_json::json!({ "error": m }).to_string();
    let doc: serde_json::Value = match serde_json::from_str(payload) {
        Ok(v) => v,
        Err(_) => return fail("could not read the payload"),
    };
    let read = |o: Option<&serde_json::Value>, k: &str| {
        o.and_then(|v| v.get(k))
            .and_then(serde_json::Value::as_i64)
            .unwrap_or(0)
    };
    let next = doc.get("next");
    let (na, nb, nc) = (read(next, "a"), read(next, "b"), read(next, "c"));
    let prev = doc.get("prev").filter(|v| !v.is_null());

    // Build the program. Every memo body prints `f:<name>` when it runs, so the
    // lines after the STEP marker name exactly the memos the engine re-ran on the
    // change. `p:` lines carry the pre-change values, `v:` the post-change ones, so
    // a re-run that produced an unchanged value is distinguishable from a real
    // recompute.
    let emit = |tag: char| {
        INCR_MEMOS.iter().fold(String::new(), |mut s, m| {
            let _ = writeln!(
                s,
                "  let _ = println(concat(\"{tag}:{m}=\", show_int(get({m}))))"
            );
            s
        })
    };
    let emit_p = emit('p');
    let emit_v = emit('v');
    let defs = "\
  let total = memo(\\() -> let _ = println(\"f:total\") in get(a) + get(b) + get(c))\n\
  let peak = memo(\\() -> let _ = println(\"f:peak\") in max(get(a), max(get(b), get(c))))\n\
  let scaled = memo(\\() -> let _ = println(\"f:scaled\") in get(total) * 2)\n\
  let alert = memo(\\() -> let _ = println(\"f:alert\") in get(peak) * 10)\n\
  let board = memo(\\() -> let _ = println(\"f:board\") in get(scaled) + get(alert))\n";
    let (pa, pb, pc, cold) = prev.map_or((na, nb, nc, true), |p| {
        (
            read(Some(p), "a"),
            read(Some(p), "b"),
            read(Some(p), "c"),
            false,
        )
    });
    let body = if cold {
        format!(
            "fn cells() =\n  let a = input({na})\n  let b = input({nb})\n  let c = input({nc})\n{defs}  let _ = get(board)\n  let _ = println(\"STEP\")\n{emit_v}  ()\n"
        )
    } else {
        format!(
            "fn cells() =\n  let a = input({pa})\n  let b = input({pb})\n  let c = input({pc})\n{defs}  let _ = get(board)\n{emit_p}  let _ = println(\"STEP\")\n  let _ = set(a, {na})\n  let _ = set(b, {nb})\n  let _ = set(c, {nc})\n  let _ = get(board)\n{emit_v}  ()\n"
        )
    };
    let src = format!("import Incr (..)\n{body}pub fn main() = run_incr(\\() -> cells())\n");

    let term = match interpret(&with_prelude(&src)) {
        Ok(r) => r.term,
        Err(e) => return fail(&format!("{e}")),
    };
    let step = term.split("STEP\n").nth(1).unwrap_or_default();
    let mut fired: HashSet<&str> = HashSet::new();
    let mut prev_val: std::collections::HashMap<&str, i64> = std::collections::HashMap::new();
    let mut next_val: std::collections::HashMap<&str, i64> = std::collections::HashMap::new();
    for line in step.lines() {
        if let Some(n) = line.strip_prefix("f:") {
            fired.insert(n);
        } else if let Some(kv) = line.strip_prefix("v:") {
            if let Some((k, v)) = kv.split_once('=') {
                if let Ok(n) = v.parse() {
                    next_val.insert(k, n);
                }
            }
        }
    }
    for line in term.split("STEP\n").next().unwrap_or_default().lines() {
        if let Some(kv) = line.strip_prefix("p:") {
            if let Some((k, v)) = kv.split_once('=') {
                if let Ok(n) = v.parse() {
                    prev_val.insert(k, n);
                }
            }
        }
    }

    let src_names = [("a", na, pa), ("b", nb, pb), ("c", nc, pc)];
    let mut nodes: Vec<serde_json::Value> = Vec::new();
    for (name, nv, pv) in src_names {
        let state = if cold || nv == pv {
            "unchanged"
        } else {
            "changed"
        };
        nodes.push(serde_json::json!({ "name": name, "value": nv, "state": state }));
    }
    for &m in INCR_MEMOS {
        let value = next_val.get(m).copied().unwrap_or(0);
        let state = if cold {
            "recomputed"
        } else if fired.contains(m) {
            if prev_val.get(m) == next_val.get(m) {
                "cutoff"
            } else {
                "recomputed"
            }
        } else {
            "cached"
        };
        nodes.push(serde_json::json!({ "name": m, "value": value, "state": state }));
    }
    serde_json::json!({ "nodes": nodes }).to_string()
}
