//! An mdbook preprocessor that classifies and live-checks every `prism` code
//! block, so the rendered book can badge each block by what the compiler makes of
//! it: runnable, type-checks, does not run, a bare signature, or unchecked.
//!
//! mdbook turns each token of a fence info string into a CSS class on the emitted
//! `<code>` element, so the block's category reaches the theme's JavaScript with
//! no HTML rewriting and highlighting and the copy button intact. This
//! preprocessor reads the declared attributes, type-checks the body where that
//! applies (it runs after the built-in `links` preprocessor, so `{{#include}}`
//! is already expanded), and rewrites the fence to carry a normalized kind and a
//! verified status: `prism,run,ok`, `prism,check,ok`, `prism,norun,ok`,
//! `prism,sig`, `prism,def`, `prism,ignore`, `prism,cfail,ok`, or a `*,err` when
//! a block that should type-check does not.

use std::path::Path;

use serde_json::Value;

use crate::driver::{example_program, with_prelude};
use crate::error::Error;
use crate::names::ENTRY_POINT;
use crate::resolve::default_roots;

use super::check_quiet;

// The first whitespace/comma-separated token of a fence info string.
fn lang_of(info: &str) -> &str {
    info.split([',', ' ']).next().unwrap_or("").trim()
}

// Whether the info string carries an attribute token (after the language).
fn has_attr(info: &str, attr: &str) -> bool {
    info.split([',', ' ']).skip(1).any(|t| t.trim() == attr)
}

// The generator tags a reference block with an `h-<hex>` content-hash token;
// keep it on the rewritten fence so the theme can render the hash pill beside the
// block's badge. Returns `,h-<hex>` (ready to append) or an empty string.
fn hash_suffix(info: &str) -> String {
    info.split([',', ' '])
        .map(str::trim)
        .find(|t| {
            t.strip_prefix("h-")
                .is_some_and(|h| !h.is_empty() && h.bytes().all(|b| b.is_ascii_hexdigit()))
        })
        .map_or_else(String::new, |t| format!(",{t}"))
}

// Classify one `prism` block body: the rewritten info string and an optional
// failure message when a block that was expected to type-check did not.
fn classify(info: &str, body: &str) -> (String, Option<String>) {
    // Reference blocks the generator emits: never run, never checked.
    if has_attr(info, "sig") {
        return (format!("prism,sig{}", hash_suffix(info)), None);
    }
    if has_attr(info, "def") {
        return (format!("prism,def{}", hash_suffix(info)), None);
    }
    if has_attr(info, "ignore") {
        return ("prism,ignore".into(), None);
    }

    let roots = default_roots(Path::new("."));
    // A bare expression or `let`-block is wrapped as an implicit `main`, so it
    // counts as runnable rather than merely type-checking.
    let program = example_program(body);
    let checked = check_quiet(&with_prelude(&program), &roots);
    let snippet: String = body
        .split_whitespace()
        .take(6)
        .collect::<Vec<_>>()
        .join(" ");

    if has_attr(info, "compile_fail") {
        return match checked {
            Ok(_) => (
                "prism,cfail,err".into(),
                Some(format!("compile_fail block compiled: {snippet}")),
            ),
            Err(_) => ("prism,cfail,ok".into(), None),
        };
    }
    if has_attr(info, "no_run") {
        return match checked {
            Ok(_) => ("prism,norun,ok".into(), None),
            Err(e) => ("prism,norun,err".into(), Some(format!("{snippet}: {e}"))),
        };
    }
    match checked {
        Ok(c) => {
            let kind = if c.decls.iter().any(|d| d.name == ENTRY_POINT) {
                "run"
            } else {
                "check"
            };
            (format!("prism,{kind},ok"), None)
        }
        Err(e) => ("prism,check,err".into(), Some(format!("{snippet}: {e}"))),
    }
}

// A fence opener (```/~~~ optionally followed by an info string). Returns the
// marker and the info string.
fn fence_open(line: &str) -> Option<(&str, &str)> {
    let t = line.trim_start();
    for marker in ["```", "~~~"] {
        if let Some(rest) = t.strip_prefix(marker) {
            // A closing fence has no info; only openers carry one, but either way
            // the caller distinguishes open from close by nesting state.
            return Some((marker, rest.trim()));
        }
    }
    None
}

fn is_fence(line: &str, marker: &str) -> bool {
    line.trim_start().starts_with(marker)
}

/// Rewrite every `prism` fence in `content`, returning the new markdown and any
/// failures (a block that should type-check but does not).
pub(crate) fn annotate_markdown(content: &str) -> (String, Vec<String>) {
    let lines: Vec<&str> = content.lines().collect();
    let mut out = String::new();
    let mut warnings = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let Some((marker, info)) = fence_open(lines[i]) else {
            out.push_str(lines[i]);
            out.push('\n');
            i += 1;
            continue;
        };
        // Collect the block body up to the closing fence of the same marker.
        let indent = &lines[i][..lines[i].len() - lines[i].trim_start().len()];
        let mut body = String::new();
        let mut j = i + 1;
        while j < lines.len() && !is_fence(lines[j], marker) {
            body.push_str(lines[j]);
            body.push('\n');
            j += 1;
        }
        if lang_of(info) == "prism" {
            let (new_info, warn) = classify(info, &body);
            if let Some(w) = warn {
                warnings.push(w);
            }
            out.push_str(indent);
            out.push_str(marker);
            out.push_str(&new_info);
        } else {
            out.push_str(lines[i]);
        }
        out.push('\n');
        out.push_str(&body);
        if j < lines.len() {
            out.push_str(lines[j]);
            out.push('\n');
        }
        i = j + 1;
    }
    (out, warnings)
}

// Walk the mdbook section tree, rewriting each chapter's content in place.
fn walk(items: &mut Vec<Value>, warnings: &mut Vec<String>) {
    for item in items {
        let Some(chapter) = item.get_mut("Chapter") else {
            continue;
        };
        if let Some(content) = chapter.get("content").and_then(Value::as_str) {
            let (new, mut w) = annotate_markdown(content);
            warnings.append(&mut w);
            chapter["content"] = Value::String(new);
        }
        if let Some(subs) = chapter.get_mut("sub_items").and_then(Value::as_array_mut) {
            walk(subs, warnings);
        }
    }
}

/// Run the preprocessor over the `[context, book]` JSON mdbook passes on stdin,
/// returning the rewritten book JSON and any failures.
///
/// # Errors
/// Fails if the input is not the expected mdbook preprocessor JSON.
pub fn preprocess_book(input: &str) -> Result<(String, Vec<String>), Error> {
    let parsed: Value = serde_json::from_str(input)
        .map_err(|e| Error::Codegen(format!("mdbook preprocessor input: {e}")))?;
    let mut book = parsed
        .get(1)
        .cloned()
        .ok_or_else(|| Error::Codegen("mdbook preprocessor: expected [context, book]".into()))?;
    let mut warnings = Vec::new();
    // The book's chapter array is `items` (older mdbook used `sections`).
    let key = if book.get("items").is_some() {
        "items"
    } else {
        "sections"
    };
    if let Some(items) = book.get_mut(key).and_then(Value::as_array_mut) {
        walk(items, &mut warnings);
    }
    let json = serde_json::to_string(&book)
        .map_err(|e| Error::Codegen(format!("mdbook preprocessor output: {e}")))?;
    Ok((json, warnings))
}
