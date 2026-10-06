//! Browser entry points for the interpreter playground.
//!
//! The whole compiler front-end and tree-walking interpreter run in wasm. Only
//! the LLVM/MLIR back-ends are absent (the `native` feature is off in a wasm
//! build).
use crate::DumpPhase;
use wasm_bindgen::prelude::*;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::io;
use std::path::Path;

use serde_json::Value;

use crate::core::HASH_PREFIX_HEX;
use crate::error::line_col;
use crate::eval::Observed;
use crate::lex::highlight::token_spans;
use crate::resolve::{default_roots, Root};
use crate::{
    check, example_program, format as fmt_src, interpret, interpret_on, namespace_identity,
    off_platform_builtins, resume_on, suspend_line_cuts, suspend_on, with_prelude, Config,
    SuspendResult,
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
    run_on_roots(src, &default_roots(Path::new(".")))
}

/// Run a snippet whose imports may resolve against an in-memory module bundle.
///
/// `names` and `sources` are parallel: `names[i]` is the dotted module path
/// (`Tc`, `Data.Util`) that `sources[i]` provides. The docs' package pages ship
/// their package sources this way, so a block that says `import Tc (..)` runs
/// in the browser exactly as it does inside the package project. Bundle
/// modules take priority over the embedded stdlib, mirroring a package's own
/// source layout.
#[wasm_bindgen]
#[must_use]
pub fn run_with_modules(src: &str, names: Vec<String>, sources: Vec<String>) -> String {
    if names.len() != sources.len() {
        return "error: module names and sources differ in length".to_string();
    }
    let modules: BTreeMap<String, String> = names.into_iter().zip(sources).collect();
    let mut roots = vec![Root::source_bundle("docs-bundle".to_string(), modules)];
    roots.extend(default_roots(Path::new(".")));
    run_on_roots(src, &roots)
}

fn run_on_roots(src: &str, roots: &[Root]) -> String {
    // A doc snippet without `main` (a bare expression or `let`-block) is wrapped
    // as an implicit `main`. What it shows is what its doctest expectation
    // holds: the transcript if it printed, otherwise its value (`=> v`).
    let program = example_program(src);
    let full = with_prelude(&program);
    match off_platform_builtins(&full, roots) {
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
    match interpret_on(&full, roots) {
        // The transcript is the exact bytes emitted, what the oracle compares.
        Ok(r) => match r.observed() {
            Observed::Printed(term) => term,
            Observed::Value(v) => format!("=> {v}"),
        },
        Err(e) => format!("error: {e}"),
    }
}

// The residents the browser drives. Each example's definitions above its
// sentinel are shared verbatim with its terminal corpus form, and the page
// supplies the expression its own `main` prints, so nothing about the behaviour
// depends on which entry point runs it. The sentinel fences off the example's
// own `main` so the two never collide in one program; the same sentinels live in
// the examples and in their acceptance tests.
const RESIDENTS: &[(&str, &str, &str)] = &[
    (
        "boids",
        include_str!("../../examples/boids.pr"),
        "-- @scrubber:main-below",
    ),
    (
        "pendulum",
        include_str!("../../examples/pendulum.pr"),
        "-- @scrubber:main-below",
    ),
    (
        "world",
        include_str!("../../examples/world.pr"),
        "-- @world:main-below",
    ),
    (
        "chaos",
        include_str!("../../examples/chaos_swarm.pr"),
        "-- @chaos:main-below",
    ),
];

// A resident's whole example source and its kernel (everything above the
// sentinel).
fn resident(name: &str) -> Result<(&'static str, &'static str), String> {
    RESIDENTS
        .iter()
        .find(|(id, _, _)| *id == name)
        .map(|(_, src, split)| (*src, src.split(split).next().unwrap_or(src)))
        .ok_or_else(|| format!("unknown resident '{name}'"))
}

/// The Prism kernel of a resident, exactly as it runs, so a page's source face
/// shows the real definitions rather than a paraphrase.
#[wasm_bindgen]
#[must_use]
pub fn resident_source(name: &str) -> String {
    resident(name).map_or_else(|e| format!("error: {e}"), |(_, k)| k.trim_end().to_string())
}

/// Run a resident's kernel under `fn main() = print(<expr>)` and return the
/// printed term, or an `error:` line for an unknown resident or any front-end or
/// runtime failure.
///
/// The page owns the call: boids and pendulum replay `run_trace(n)`, the branch
/// demo continues `run_trace_from(swarm, n)`, the world evolves `trace(...)`, and
/// the chaos counter reports `batch_report(start, count, n_workers)`. Every
/// kernel function is pure in its arguments, so the same expression is the same
/// bytes on every replay.
#[wasm_bindgen]
#[must_use]
pub fn resident_run(name: &str, expr: &str) -> String {
    let kernel = match resident(name) {
        Ok((_, k)) => k,
        Err(e) => return format!("error: {e}"),
    };
    let driver = format!("{kernel}\nfn main() = print({expr})\n");
    match interpret(&with_prelude(&driver)) {
        Ok(r) => r.term,
        Err(e) => format!("error: {e}"),
    }
}

/// The content hash of one definition in a resident, the identity a page shows
/// for it (the world shows its law's `step_*` function).
///
/// It is the compiler's own Merkle hash of the elaborated Core, so it moves when
/// and only when the definition's behaviour moves. Returns an `error:` line for
/// an unknown resident or definition, or a front-end failure.
#[wasm_bindgen]
#[must_use]
pub fn resident_hash(name: &str, def: &str) -> String {
    let src = match resident(name) {
        Ok((src, _)) => src,
        Err(e) => return format!("error: {e}"),
    };
    let ns = match crate::dump(DumpPhase::Namespace, &with_prelude(src)) {
        Ok(s) => s,
        Err(e) => return format!("error: {e}"),
    };
    let doc: serde_json::Value = match serde_json::from_str(&ns) {
        Ok(v) => v,
        Err(_) => return "error: could not read namespace export".to_string(),
    };
    let hash = doc.get("defs").and_then(Value::as_array).and_then(|defs| {
        defs.iter().find_map(|d| {
            let name = d.pointer("/meta/name").and_then(Value::as_str)?;
            if name == def {
                d.get("hash").and_then(Value::as_str)
            } else {
                None
            }
        })
    });
    hash.map_or_else(
        || format!("error: resident '{name}' has no '{def}' definition"),
        |h| h[..h.len().min(HASH_PREFIX_HEX)].to_string(),
    )
}

// The teleport resident: a small deterministic program the browser suspends into
// a `kont` envelope in one tab and resumes in another. It prints a labeled,
// self-evidently continued sequence (one line per step, each naming its running
// index) so that when the second tab resumes it visibly carries the same count
// forward rather than restarting. The program is baked in so both tabs share one
// bundle: the receiving tab re-derives its code identity and refuses an envelope
// from any other program.
const TELEPORT_SRC: &str = include_str!("../../examples/fixtures/runtime/teleport.pr");

fn teleport_full() -> String {
    with_prelude(TELEPORT_SRC)
}

/// The baked teleport program's source, for the read-only panel beside the demo.
#[wasm_bindgen]
#[must_use]
pub fn teleport_source() -> String {
    TELEPORT_SRC.to_string()
}

fn teleport_roots() -> Vec<Root> {
    default_roots(Path::new("."))
}

/// The code-identity digest (namespace root) of the baked teleport program.
///
/// Both tabs compute this from the same embedded source, so it is the hash the
/// receiver checks an incoming envelope against. This proves code identity during
/// teleport.
#[wasm_bindgen]
#[must_use]
pub fn teleport_bundle() -> String {
    namespace_identity(&teleport_full(), &teleport_roots()).map_or_else(
        |e| format!("error: {e}"),
        |identity| identity.root.into_string(),
    )
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
    let mut input = io::empty();
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
    let mut input = io::empty();
    match suspend_on(
        &teleport_full(),
        &teleport_roots(),
        &mut out,
        &mut input,
        steps as usize,
        &Config::from_env(),
    ) {
        Ok(SuspendResult::Suspended { bytes, .. }) => bytes,
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
    let mut input = io::empty();
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

/// A JSON array of `{s,e,c}` (byte start, byte end, highlight class) for every
/// token in `src`, for editor syntax highlighting. Lex errors are skipped here;
/// they surface through [`diagnostics`].
#[wasm_bindgen]
#[must_use]
pub fn tokens(src: &str) -> String {
    let parts: Vec<String> = token_spans(src)
        .into_iter()
        .map(|(start, end, class)| format!(r#"{{"s":{start},"e":{end},"c":"{class}"}}"#))
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
        let (line, col) = line_col(user, s);
        let (eline, ecol) = line_col(user, end);
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
            .reports
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

/// The versioned checked-HIR fixture for the snippet.
///
/// This is the deterministic JSON emitted by `dump hir` (schema
/// `prism-hir-fixture-v2`). It carries per-declaration schemes and effect rows,
/// plus per-node resolution, dictionary, numeric-lane, zonked-type, and handler
/// residual-operation facts.
///
/// The prelude is prepended so snippets that reference it type-check; the
/// browser strips the prelude declarations for display the same way the Core IR
/// view does. On a front-end error, returns the rendered diagnostic as text.
#[wasm_bindgen]
#[must_use]
pub fn dump_hir(src: &str) -> String {
    match crate::dump_at(DumpPhase::Hir, &with_prelude(src), Path::new(".")) {
        Ok(fixture) => fixture,
        Err(e) => format!("error: {e}"),
    }
}

/// The top-level type signatures of the snippet's own declarations (prelude
/// signatures elided), or the front-end error as text.
#[wasm_bindgen]
#[must_use]
pub fn dump(src: &str) -> String {
    let prelude: HashSet<String> = match check(&with_prelude("")) {
        Ok(c) => c.defs.decls.iter().map(|d| d.name.clone()).collect(),
        Err(e) => return format!("error: {e}"),
    };
    match check(&with_prelude(src)) {
        Ok(c) => c
            .defs
            .decls
            .iter()
            .filter(|d| !prelude.contains(&d.name))
            .map(|d| format!("{} : {}", d.name, c.show_sig(d)))
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
        let ns = crate::dump(DumpPhase::Namespace, full).map_err(|e| format!("{e}"))?;
        serde_json::from_str::<serde_json::Value>(&ns)
            .map_err(|_| "could not read namespace export".to_string())
    };
    let names_of = |doc: &serde_json::Value| -> Vec<String> {
        doc.get("defs")
            .and_then(Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(|d| d.pointer("/meta/name").and_then(Value::as_str))
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
    let Some(defs) = doc.get("defs").and_then(Value::as_array) else {
        return err("namespace export had no defs");
    };
    // The namespace export lists a definition's dependencies by content hash
    // (names erased), so a hash -> name index over every definition, prelude
    // included, turns those edges back into the names the graph draws.
    let name_by_hash: HashMap<&str, &str> = defs
        .iter()
        .filter_map(|d| Some((d.get("hash")?.as_str()?, d.pointer("/meta/name")?.as_str()?)))
        .collect();
    let mut out: Vec<serde_json::Value> = Vec::new();
    for d in defs {
        let name = match d.pointer("/meta/name").and_then(Value::as_str) {
            Some(n) if !prelude.contains(n) => n,
            _ => continue,
        };
        let hash = d.get("hash").and_then(Value::as_str).unwrap_or_default();
        let short = &hash[..hash.len().min(HASH_PREFIX_HEX)];
        let mut dep_names: Vec<&str> = d
            .pointer("/anon/deps")
            .and_then(Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(Value::as_str)
                    .filter_map(|h| name_by_hash.get(h).copied())
                    .filter(|n| !prelude.contains(*n))
                    .collect()
            })
            .unwrap_or_default();
        dep_names.sort_unstable();
        dep_names.dedup();
        out.push(serde_json::json!({ "name": name, "hash": short, "deps": dep_names }));
    }
    Value::Array(out).to_string()
}

// The memo nodes of the incremental demand graph, in the order the demo lists
// them. `a`, `b`, `c` are the sources; the rest are derivations. Kept beside the
// program the export builds so the two never drift.
const INCR_MEMOS: &[&str] = &["total", "peak", "scaled", "alert", "board"];
const INCR_RESIDENT_SRC: &str = include_str!("../../examples/fixtures/runtime/incr_resident.pr");
const INCR_STEP_MARKER: &str = "STEP\n";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IncrNodeState {
    Changed,
    Unchanged,
    Cached,
    Recomputed,
    Cutoff,
}

impl IncrNodeState {
    const fn label(self) -> &'static str {
        match self {
            Self::Changed => "changed",
            Self::Unchanged => "unchanged",
            Self::Cached => "cached",
            Self::Recomputed => "recomputed",
            Self::Cutoff => "cutoff",
        }
    }
}

enum IncrTraceRow<'a> {
    Fired(&'a str),
    Previous(&'a str, i64),
    Value(&'a str, i64),
}

fn parse_incr_row(line: &str) -> Result<IncrTraceRow<'_>, &'static str> {
    let (tag, body) = line
        .split_once(':')
        .ok_or("incremental trace row has no tag")?;
    match tag {
        "f" if !body.is_empty() => Ok(IncrTraceRow::Fired(body)),
        "p" => {
            let (name, value) = body
                .split_once('=')
                .ok_or("incremental value row has no separator")?;
            let value = value
                .parse()
                .map_err(|_| "incremental value is not an integer")?;
            Ok(IncrTraceRow::Previous(name, value))
        }
        "v" => {
            let (name, value) = body
                .split_once('=')
                .ok_or("incremental value row has no separator")?;
            let value = value
                .parse()
                .map_err(|_| "incremental value is not an integer")?;
            Ok(IncrTraceRow::Value(name, value))
        }
        _ => Err("unknown incremental trace row"),
    }
}

struct IncrTrace<'a> {
    fired: HashSet<&'a str>,
    previous: HashMap<&'a str, i64>,
    values: HashMap<&'a str, i64>,
}

fn parse_incr_trace(term: &str) -> Result<IncrTrace<'_>, &'static str> {
    let (previous_rows, step_rows) = term
        .split_once(INCR_STEP_MARKER)
        .ok_or("incremental trace has no step marker")?;
    let mut trace = IncrTrace {
        fired: HashSet::new(),
        previous: HashMap::new(),
        values: HashMap::new(),
    };
    for line in previous_rows.lines().filter(|line| !line.is_empty()) {
        match parse_incr_row(line)? {
            IncrTraceRow::Previous(name, value) => {
                trace.previous.insert(name, value);
            }
            // The cold first demand runs every memo body to establish the prior
            // values, so its fire lines land in the pre-step section. They report
            // that initial computation, not the re-demand under observation, and
            // only the post-step fires classify the incremental step, so these are
            // ignored here.
            IncrTraceRow::Fired(_) => {}
            IncrTraceRow::Value(_, _) => {
                return Err("value row before incremental step marker");
            }
        }
    }
    for line in step_rows.lines().filter(|line| !line.is_empty()) {
        match parse_incr_row(line)? {
            IncrTraceRow::Fired(name) => {
                trace.fired.insert(name);
            }
            IncrTraceRow::Value(name, value) => {
                trace.values.insert(name, value);
            }
            IncrTraceRow::Previous(_, _) => {
                return Err("previous row after incremental step marker");
            }
        }
    }
    Ok(trace)
}

fn incr_resident_source(pa: i64, pb: i64, pc: i64, na: i64, nb: i64, nc: i64) -> String {
    let replacements = [
        ("let incr_prev_a = 3", format!("let incr_prev_a = {pa}")),
        ("let incr_prev_b = 7", format!("let incr_prev_b = {pb}")),
        ("let incr_prev_c = 5", format!("let incr_prev_c = {pc}")),
        ("let incr_next_a = 6", format!("let incr_next_a = {na}")),
        ("let incr_next_b = 7", format!("let incr_next_b = {nb}")),
        ("let incr_next_c = 5", format!("let incr_next_c = {nc}")),
    ];
    replacements.into_iter().fold(
        INCR_RESIDENT_SRC.to_owned(),
        |src, (needle, replacement)| src.replace(needle, &replacement),
    )
}

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
            .and_then(Value::as_i64)
            .unwrap_or(0)
    };
    let next = doc.get("next");
    let (na, nb, nc) = (read(next, "a"), read(next, "b"), read(next, "c"));
    let prev = doc.get("prev").filter(|v| !v.is_null());

    let (pa, pb, pc, cold) = prev.map_or((na, nb, nc, true), |p| {
        (
            read(Some(p), "a"),
            read(Some(p), "b"),
            read(Some(p), "c"),
            false,
        )
    });
    let src = incr_resident_source(pa, pb, pc, na, nb, nc);

    let term = match interpret(&with_prelude(&src)) {
        Ok(r) => r.term,
        Err(e) => return fail(&format!("{e}")),
    };
    let trace = match parse_incr_trace(&term) {
        Ok(trace) => trace,
        Err(message) => return fail(message),
    };

    let src_names = [("a", na, pa), ("b", nb, pb), ("c", nc, pc)];
    let mut nodes: Vec<serde_json::Value> = Vec::new();
    for (name, nv, pv) in src_names {
        let state = if cold || nv == pv {
            IncrNodeState::Unchanged
        } else {
            IncrNodeState::Changed
        };
        nodes.push(serde_json::json!({ "name": name, "value": nv, "state": state.label() }));
    }
    for &m in INCR_MEMOS {
        let value = trace.values.get(m).copied().unwrap_or(0);
        let state = if cold {
            IncrNodeState::Recomputed
        } else if trace.fired.contains(m) {
            if trace.previous.get(m) == trace.values.get(m) {
                IncrNodeState::Cutoff
            } else {
                IncrNodeState::Recomputed
            }
        } else {
            IncrNodeState::Cached
        };
        nodes.push(serde_json::json!({ "name": m, "value": value, "state": state.label() }));
    }
    serde_json::json!({ "nodes": nodes }).to_string()
}

// Browser-path regression guard, run on the wasm target under node in CI. The
// playground compiles and runs every snippet in wasm, where the durable store's
// filesystem calls are unsupported; a `cargo check` proves the wasm build
// compiles but never runs it, so a default-path host syscall slips through.
// Executing an effectful program end to end through `run` catches any such
// syscall (a store open, a clock read): the compile path itself must complete
// without reaching for a filesystem the browser does not have.
#[cfg(all(test, target_arch = "wasm32"))]
mod wasm_smoke {
    use wasm_bindgen_test::wasm_bindgen_test;

    // Effects, a handler, and IO: enough of the compile path to open the durable
    // cache if it is ever left enabled on wasm. Its output is deterministic.
    const EFFECTFUL: &str = "\
effect Ask
  once ask(Unit) : Int

fn f() : Unit ! {IO} = println(\"f\")

fn g() : Int ! {Ask} = ask(())

fn foo() : Int ! {IO, Ask} =
  f()
  g()

fn bar() : Int ! {IO} =
  handle foo() with
    once ask(u) => 7

fn main() = println(bar())";

    #[wasm_bindgen_test]
    fn effectful_snippet_runs_without_host_io() {
        let out = super::run(EFFECTFUL);
        assert!(
            !out.contains("operation not supported") && !out.contains("error:"),
            "wasm run reached an unsupported host syscall: {out}"
        );
        assert!(
            out.contains('f') && out.contains('7'),
            "unexpected output: {out}"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incr_resident_source_interprets() {
        let src = incr_resident_source(3, 7, 5, 6, 7, 5);
        let term = interpret(&with_prelude(&src))
            .expect("included incremental resident must parse, check, and run")
            .term;

        assert!(term.contains("STEP\n"), "{term}");
        assert!(term.contains("v:total=18"), "{term}");
        assert!(term.contains("v:peak=7"), "{term}");
        assert!(term.contains("v:board=106"), "{term}");
    }

    // The cold first demand runs every memo body, so its fire lines land before
    // the step marker; the trace parser must read past them and still classify the
    // re-demand. This is the exact drift that dead-paged the resident.
    #[test]
    fn incr_trace_survives_cold_demand_fires() {
        let src = incr_resident_source(3, 7, 5, 6, 7, 5);
        let term = interpret(&with_prelude(&src))
            .expect("resident must run")
            .term;
        let trace = parse_incr_trace(&term).expect("trace must parse past cold-demand fires");
        // Lowering a from 3 to 6 keeps peak at 7, so peak re-runs to the same value
        // (a cutoff) and alert never fires (served from cache).
        assert!(trace.fired.contains("peak"), "peak should re-run");
        assert!(!trace.fired.contains("alert"), "alert should be cached");
        assert_eq!(trace.previous.get("peak"), Some(&7));
        assert_eq!(trace.values.get("board"), Some(&106));
    }

    // The public export the incremental resident calls: a warm re-demand must
    // return classified nodes, not an error, and mark the cutoff.
    #[test]
    fn incr_run_classifies_warm_demand() {
        let out = incr_run(r#"{"prev":{"a":3,"b":7,"c":5},"next":{"a":6,"b":7,"c":5}}"#);
        let doc: serde_json::Value = serde_json::from_str(&out).expect("valid json");
        assert!(doc.get("error").is_none(), "unexpected error: {out}");
        let nodes = doc.get("nodes").and_then(Value::as_array).expect("nodes");
        let state_of = |name: &str| -> String {
            nodes
                .iter()
                .find(|n| n.get("name").and_then(Value::as_str) == Some(name))
                .and_then(|n| n.get("state").and_then(Value::as_str))
                .unwrap_or_default()
                .to_string()
        };
        assert_eq!(state_of("a"), "changed");
        assert_eq!(state_of("peak"), "cutoff");
        assert_eq!(state_of("alert"), "cached");
        assert_eq!(state_of("board"), "recomputed");
    }
}
