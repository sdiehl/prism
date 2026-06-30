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
use crate::{check, format as fmt_src, interpret, off_platform_builtins, with_prelude};

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

/// Run a snippet and return its captured `print` transcript verbatim (the exact
/// bytes emitted, the same the differential oracle compares). On any front-end
/// or runtime error, returns the rendered diagnostic instead.
#[wasm_bindgen]
#[must_use]
pub fn run(src: &str) -> String {
    let full = with_prelude(src);
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
        // The exact transcript (real emitted newlines, byte-for-byte what the
        // oracle compares), not a per-value newline join.
        Ok(r) => r.term,
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
            c if (c as u32) < 0x20 => write!(out, "\\u{:04x}", c as u32).unwrap(),
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

/// The fully lowered CBPV core IR of the snippet's own functions (prelude
/// elided): effects lowered, reference counting and FBIP reuse applied. The
/// lowest-level view the browser can produce. The LLVM back-end is native only.
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
