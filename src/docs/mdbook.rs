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
//!
//! It also owns the generated sections' book structure: SUMMARY.md lists only
//! each generated index chapter (the stdlib reference, and one per package
//! under `packages/`), and the generated per-module pages beside an index are
//! injected as its sub-chapters here (`inject_generated`), ordered by the
//! index's own module list. Regenerating a reference (`just docs-gen`,
//! `just docs-packages`) is therefore the only step that adds a module to the
//! book; SUMMARY.md never changes.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use super::typespans::{TypeSpan, TypeSpans, TYPESPANS_FORMAT};
use crate::driver::{dump_on, example_program, with_prelude, Config};
use crate::error::Error;
use crate::lex::{
    highlight::{tok_class, COMMENT_CLASS},
    lex_raw,
};
use crate::names::ENTRY_POINT;
use crate::resolve::{default_roots, Root};

use super::check_quiet;
use super::doctest::{imported, is_hidden, runnable, split_imports, unhide, MOD_ATTR};

// The stdlib index chapter: the only stdlib entry SUMMARY.md carries. Its
// sibling module pages become sub-chapters at build time via `inject_generated`.
const STDLIB_INDEX: &str = "stdlib/index.md";
// The book-relative directory the per-package generated references live in;
// each `packages/<name>/index.md` chapter is a generated index like the
// stdlib's, and its sibling module pages are injected the same way.
const PACKAGES_DIR: &str = "packages/";
const INDEX_PAGE: &str = "/index.md";

// Whether a chapter source path is a generated-reference index whose sibling
// module pages should be injected as sub-chapters: the stdlib index, or a
// package index beneath `packages/` (the `packages/index.md` landing page
// itself is hand-written prose, not a generated index).
fn generated_index(source_path: &str) -> bool {
    source_path == STDLIB_INDEX
        || source_path
            .strip_prefix(PACKAGES_DIR)
            .is_some_and(|rest| rest.ends_with(INDEX_PAGE))
}

// The `- [Title](./page.md)` module links of the generated stdlib index, in
// order. Only same-directory `.md` targets count; anything else on the page is
// prose. This is the contract with the generator's index writer: the index's
// module list is the single source of chapter order.
fn index_links(content: &str) -> Vec<(String, String)> {
    let mut links = Vec::new();
    for line in content.lines() {
        let Some(rest) = line.trim_start().strip_prefix("- [") else {
            continue;
        };
        let Some((title, rest)) = rest.split_once("](") else {
            continue;
        };
        let Some((target, _)) = rest.split_once(')') else {
            continue;
        };
        let target = target.trim().trim_start_matches("./");
        if target.strip_suffix(".md").is_some() && !target.contains('/') {
            links.push((title.to_string(), target.to_string()));
        }
    }
    links
}

// Every chapter source path already in the book, so injection never duplicates
// a page a SUMMARY.md might still list explicitly.
fn collect_source_paths(items: &[Value], out: &mut BTreeSet<String>) {
    for item in items {
        let Some(ch) = item.get("Chapter") else {
            continue;
        };
        if let Some(p) = ch.get("source_path").and_then(Value::as_str) {
            out.insert(p.to_string());
        }
        if let Some(subs) = ch.get("sub_items").and_then(Value::as_array) {
            collect_source_paths(subs, out);
        }
    }
}

// Append a generated reference's module pages as sub-chapters of its index
// chapter (the stdlib index, and each package index; see `generated_index`),
// reading their markdown from `src_dir` (the book's source directory; mdbook
// only loads SUMMARY chapters itself). Runs before `walk`, so injected pages
// get their fences annotated like any hand-listed chapter. Warns when an index
// chapter carries no module links at all, since that silently empties its
// section (`PRISM_MDBOOK_STRICT` turns the warning into a build failure).
fn inject_generated(
    items: &mut [Value],
    src_dir: &Path,
    existing: &BTreeSet<String>,
    warnings: &mut Vec<String>,
) -> Result<(), Error> {
    for item in items.iter_mut() {
        let Some(ch) = item.get_mut("Chapter") else {
            continue;
        };
        let source_path = ch
            .get("source_path")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        if !generated_index(&source_path) {
            if let Some(subs) = ch.get_mut("sub_items").and_then(Value::as_array_mut) {
                inject_generated(subs, src_dir, existing, warnings)?;
            }
            continue;
        }
        // The directory the index's module pages sit in, from the index's own
        // path: `stdlib/index.md` -> `stdlib`, `packages/tzdb/index.md` ->
        // `packages/tzdb`. Every `generated_index` path ends with the index
        // page, the stdlib's included.
        let Some(dir) = source_path.strip_suffix(INDEX_PAGE) else {
            continue;
        };
        let dir = dir.to_string();
        let links = index_links(ch.get("content").and_then(Value::as_str).unwrap_or(""));
        if links.is_empty() {
            warnings.push(format!(
                "generated index ({source_path}) lists no module pages; its chapters were not injected"
            ));
            continue;
        }
        let parent_name = ch
            .get("name")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        let parent_number: Vec<Value> = ch
            .get("number")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        let Some(subs) = ch.get_mut("sub_items").and_then(Value::as_array_mut) else {
            continue;
        };
        for (title, page) in links {
            let path = format!("{dir}/{page}");
            if path == source_path || existing.contains(&path) {
                continue;
            }
            let body = fs::read_to_string(src_dir.join(&path)).map_err(|e| {
                Error::CodegenDocs(format!("mdbook preprocessor: read {path}: {e}"))
            })?;
            let mut number = parent_number.clone();
            number.push(json!(subs.len() + 1));
            subs.push(json!({ "Chapter": {
                "name": title,
                "content": body,
                "number": number,
                "sub_items": [],
                "path": path,
                "source_path": path,
                "parent_names": [parent_name],
            }}));
        }
    }
    Ok(())
}

// The first whitespace/comma-separated token of a fence info string.
fn lang_of(info: &str) -> &str {
    info.split([',', ' ']).next().unwrap_or("").trim()
}

// Whether the info string carries an attribute token (after the language).
fn has_attr(info: &str, attr: &str) -> bool {
    info.split([',', ' ']).skip(1).any(|t| t.trim() == attr)
}

// The enclosing module named by a `mod=` attribute, or "" (a hand-written book
// example runs against the prelude alone). Stamped by the stdlib page renderer.
fn mod_attr(info: &str) -> &str {
    info.split([',', ' '])
        .skip(1)
        .find_map(|t| t.trim().strip_prefix(MOD_ATTR))
        .unwrap_or("")
}

// The compilable text of a fence body: hidden-line markers stripped so `# `
// setup lines participate in the program.
fn compile_of(body: &str) -> String {
    let mut out = String::new();
    for line in body.lines() {
        out.push_str(unhide(line));
        out.push('\n');
    }
    out
}

// The reader-visible text of a fence body: hidden lines dropped entirely.
fn display_of(body: &str) -> String {
    let mut out = String::new();
    for line in body.lines() {
        if !is_hidden(line) {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
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
// `extra_roots` are searched before the book root: empty for ordinary
// chapters, the package source directories for a page under `packages/`.
fn classify(
    info: &str,
    body: &str,
    book_root: &Path,
    extra_roots: &[PathBuf],
) -> (String, Option<String>) {
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

    // Resolve a block's imports against the book root the preprocessor context
    // gave us, not the process CWD (which need not be the book directory). A
    // package page's blocks additionally see the repository's package sources,
    // ahead of the book root, so `import Tzdb (..)` resolves the way it does
    // inside the package project.
    let mut roots = default_roots(book_root);
    for dir in extra_roots.iter().rev() {
        roots.insert(0, Root::Dir(dir.clone()));
    }
    // A bare expression or `let`-block is wrapped as an implicit `main`, so it
    // counts as runnable rather than merely type-checking. The program is the
    // same one the doctest runner builds: hidden lines unhidden and the stamped
    // module (if any) glob-imported.
    let program = runnable(mod_attr(info), &compile_of(body));
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
            let kind = if c.defs.decls.iter().any(|d| d.name == ENTRY_POINT) {
                "run"
            } else {
                "check"
            };
            (format!("prism,{kind},ok"), None)
        }
        Err(e) => ("prism,check,err".into(), Some(format!("{snippet}: {e}"))),
    }
}

// Map byte boundaries in the full doctest program back to the source a reader
// sees. The program may carry a module-import prefix (the `mod=` stamp), an
// implicit `fn main()` wrapper, and unhidden `# ` setup lines; all three are
// program-only bytes that stay `None`, so they can never leak into a
// reader-visible tooltip range. Visible lines are byte-identical between the
// fence body, the compiled program, and the displayed text, so they map 1:1.
fn example_source_map(body: &str, program: &str, prefix: usize, skip: usize) -> Vec<Option<usize>> {
    const HEADER: &str = "fn main() =\n";
    if body == program {
        return (0..=body.len()).map(Some).collect();
    }
    let lines = body.lines().collect::<Vec<_>>();
    let compile_lines = lines.iter().map(|l| unhide(l)).collect::<Vec<_>>();
    let mut map = vec![None; program.len() + 1];
    // Leading example-own import lines are hoisted into the program prefix; a
    // visible one still occupies display bytes (untooltipped), so it advances
    // the display cursor without mapping.
    let mut shown = 0;
    for line in &lines[..skip.min(lines.len())] {
        if !is_hidden(line) {
            shown += line.len() + 1;
        }
    }
    // Whether the program's tail is the wrapped form (header plus two-space
    // indent per line) or the remaining code verbatim (the example defines main).
    let remaining = &compile_lines[skip.min(lines.len())..];
    let mut rest = remaining.join("\n");
    if !remaining.is_empty() {
        rest.push('\n');
    }
    let wrapped_form = program[prefix..] != rest;
    let mut pos = prefix + if wrapped_form { HEADER.len() } else { 0 };
    for (index, line) in compile_lines.iter().enumerate().skip(skip) {
        if wrapped_form {
            pos += 2; // indentation inserted by `example_program`
        }
        let visible = !is_hidden(lines[index]);
        if visible {
            for byte in 0..=line.len() {
                if let Some(slot) = map.get_mut(pos + byte) {
                    *slot = Some(shown + byte);
                }
            }
        }
        pos += line.len();
        if visible {
            shown += line.len();
        }
        if index + 1 < lines.len() {
            if visible {
                if let Some(slot) = map.get_mut(pos) {
                    *slot = Some(shown);
                }
                shown += 1;
            }
            pos += 1;
        }
    }
    map
}

// Run the one canonical extraction (`dump typespans`), then project any
// implicit-main, import-prefix, or hidden-line offsets back onto the exact
// fence bytes readers see. `extra_roots` mirrors `classify`'s: package source
// directories for a block on a package page, empty everywhere else.
fn analyze_types(body: &str, info: &str, extra_roots: &[PathBuf]) -> Result<TypeSpans, Error> {
    let mut roots = default_roots(Path::new("."));
    for dir in extra_roots.iter().rev() {
        roots.insert(0, Root::Dir(dir.clone()));
    }
    let compile = compile_of(body);
    let (skip, rest) = split_imports(&compile);
    let program = runnable(mod_attr(info), &compile);
    let prefix = program.len() - example_program(&rest).len();
    let source_map = example_source_map(body, &program, prefix, skip);
    let display_len = display_of(body).len();
    let full = with_prelude(&program);
    let json = dump_on("typespans", &full, &roots, &Config::default())?;
    let analyzed = TypeSpans::from_json(&json).map_err(Error::CodegenDocs)?;
    let mut spans = analyzed
        .spans
        .into_iter()
        .filter_map(|span| {
            let start = source_map.get(span.start).copied().flatten()?;
            let end = source_map.get(span.end).copied().flatten()?;
            (start < end && end <= display_len).then_some(TypeSpan {
                start,
                end,
                rendered: span.rendered,
                level: span.level,
            })
        })
        .collect::<Vec<_>>();
    spans.sort_by(|a, b| {
        (a.start, std::cmp::Reverse(a.end), &a.rendered).cmp(&(
            b.start,
            std::cmp::Reverse(b.end),
            &b.rendered,
        ))
    });
    Ok(TypeSpans {
        format: TYPESPANS_FORMAT.to_string(),
        spans,
    })
}

fn escape_html(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(ch),
        }
    }
    out
}

struct HtmlNode<'a> {
    span: &'a TypeSpan,
    children: Vec<usize>,
}

fn render_plain(
    source: &str,
    start: usize,
    end: usize,
    tokens: &[(usize, &'static str, usize)],
    out: &mut String,
) {
    let mut cursor = start;
    for &(lo, class, hi) in tokens {
        if hi <= start || lo >= end {
            continue;
        }
        let lo = lo.max(start);
        let hi = hi.min(end);
        if cursor < lo {
            out.push_str(&escape_html(&source[cursor..lo]));
        }
        if lo < hi {
            if let Some(class) = hljs_class(class) {
                out.push_str("<span class=\"");
                out.push_str(class);
                out.push_str("\">");
                out.push_str(&escape_html(&source[lo..hi]));
                out.push_str("</span>");
            } else {
                out.push_str(&escape_html(&source[lo..hi]));
            }
            cursor = hi;
        }
    }
    if cursor < end {
        out.push_str(&escape_html(&source[cursor..end]));
    }
}

// Use exactly the classes highlight.js emits for an ordinary Prism block. The
// active tooltip range may add a background, but baking types must never own or
// alter the book's syntax color scheme.
const fn hljs_class(class: &str) -> Option<&'static str> {
    match class.as_bytes() {
        b"kw" => Some("hljs-keyword"),
        b"lit" => Some("hljs-literal"),
        b"ty" | b"ctor" => Some("hljs-type"),
        b"num" => Some("hljs-number"),
        b"str" => Some("hljs-string"),
        b"com" => Some("hljs-comment"),
        _ => None,
    }
}

fn render_html_node(
    index: usize,
    source: &str,
    arena: &[HtmlNode<'_>],
    tokens: &[(usize, &'static str, usize)],
    out: &mut String,
) {
    let node = &arena[index];
    // Non-value levels (type constructors, classes, type variables, effects,
    // typed holes) carry a `data-level` the theme styles and prefixes.
    let level = node.span.level.tag();
    if level.is_empty() {
        out.push_str("<span class=\"prism-type-span\" tabindex=\"0\" data-type=\"");
    } else {
        out.push_str("<span class=\"prism-type-span prism-level-");
        out.push_str(level);
        out.push_str("\" tabindex=\"0\" data-level=\"");
        out.push_str(level);
        out.push_str("\" data-type=\"");
    }
    out.push_str(&escape_html(&node.span.rendered));
    out.push_str("\" aria-label=\"");
    out.push_str(&escape_html(&node.span.rendered));
    out.push_str("\">");
    let mut cursor = node.span.start;
    for &child in &node.children {
        let child_span = arena[child].span;
        render_plain(source, cursor, child_span.start, tokens, out);
        render_html_node(child, source, arena, tokens, out);
        cursor = child_span.end;
    }
    render_plain(source, cursor, node.span.end, tokens, out);
    out.push_str("</span>");
}

fn html_classes(info: &str) -> String {
    let mut classes = vec![
        "language-prism".to_string(),
        "hljs".to_string(),
        "prism-typed".to_string(),
    ];
    classes.extend(
        info.split(',')
            .skip(1)
            .map(str::trim)
            .filter(|part| {
                !part.is_empty()
                    && part
                        .bytes()
                        .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            })
            .map(str::to_string),
    );
    classes.join(" ")
}

// Classified spans for one snippet: the semantic tokens and the comments.
//
// The lexer files comments in the trivia table rather than the token stream, so
// a renderer that paints them has to put the two back together. Merging here
// rather than at each call site is what keeps a comment from rendering as
// unclassed text that inherits the color of the code around it.
fn highlight_spans(body: &str) -> Result<Vec<(usize, &'static str, usize)>, Error> {
    let (tokens, trivia) = lex_raw(body)?;
    let comments = trivia
        .events()
        .iter()
        .filter(|event| !event.trivia.is_blank())
        .map(|event| (event.span.start, COMMENT_CLASS, event.span.end));
    let mut spans = tokens
        .iter()
        .filter(|(start, _, end)| start < end)
        .map(|(start, token, end)| (*start, tok_class(token), *end))
        .chain(comments)
        .collect::<Vec<_>>();
    // `render_plain` walks its spans once against a single cursor, so they have
    // to arrive in source order. Comments and tokens never overlap.
    spans.sort_unstable_by_key(|&(start, _, _)| start);
    Ok(spans)
}

// Pre-render one tooltip block: ordinary highlight.js classes produced from the
// real lexer and properly nested surface
// expression ranges. The compact payload is embedded unchanged for the shared
// browser/Wasm schema even though the static spans need no Wasm producer.
fn typed_html(
    body: &str,
    info: &str,
    analyzed: &TypeSpans,
    browser_source: &str,
) -> Result<String, Error> {
    let tokens = highlight_spans(body)?;

    let mut arena: Vec<HtmlNode<'_>> = Vec::new();
    let mut roots = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    for span in &analyzed.spans {
        while stack
            .last()
            .is_some_and(|&parent| span.start >= arena[parent].span.end)
        {
            stack.pop();
        }
        let index = arena.len();
        arena.push(HtmlNode {
            span,
            children: Vec::new(),
        });
        if let Some(&parent) = stack.last() {
            if span.end <= arena[parent].span.end {
                arena[parent].children.push(index);
            } else {
                return Err(Error::CodegenDocs("crossing typed-tooltip ranges".into()));
            }
        } else {
            roots.push(index);
        }
        stack.push(index);
    }

    let payload =
        serde_json::to_string(analyzed).map_err(|error| Error::CodegenDocs(error.to_string()))?;
    let mut rendered = String::new();
    let mut cursor = 0;
    for root in roots {
        let span = arena[root].span;
        render_plain(body, cursor, span.start, &tokens, &mut rendered);
        render_html_node(root, body, &arena, &tokens, &mut rendered);
        cursor = span.end;
    }
    render_plain(body, cursor, body.len(), &tokens, &mut rendered);
    Ok(format!(
        "<pre class=\"prism-typed-block\"><code class=\"{}\" data-prism-source=\"{}\" data-typespans=\"{}\">{rendered}</code></pre>\n",
        html_classes(info),
        escape_html(browser_source),
        escape_html(&payload),
    ))
}

// Bake lexer-based highlighting for a `prism` block that gets no typed
// tooltips (reference `sig`/`def` blocks, `ignore`, `compile_fail`, and blocks
// that fail to check): the same token classes the typed renderer uses, with no
// spans payload. Even a snippet that cannot type-check is at least colored.
// Falls back to the plain fence when the snippet does not lex.
fn plain_html(body: &str, info: &str, browser_source: &str) -> Result<String, Error> {
    let tokens = highlight_spans(body)?;
    let mut rendered = String::new();
    render_plain(body, 0, body.len(), &tokens, &mut rendered);
    Ok(format!(
        "<pre class=\"prism-typed-block\"><code class=\"{}\" data-prism-source=\"{}\">{rendered}</code></pre>\n",
        html_classes(info),
        escape_html(browser_source),
    ))
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
pub(crate) fn annotate_markdown(
    content: &str,
    book_root: &Path,
    extra_roots: &[PathBuf],
) -> (String, Vec<String>) {
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
            let (new_info, warn) = classify(info, &body, book_root, extra_roots);
            let checked_ok = warn.is_none() && new_info.split(',').any(|part| part == "ok");
            if let Some(w) = warn {
                warnings.push(w);
            }
            let tooltip_eligible = !has_attr(info, "compile_fail")
                && !has_attr(info, "ignore")
                && !has_attr(info, "sig")
                && !has_attr(info, "def");
            // Readers see the display text: hidden `# ` setup lines are compiled
            // above but never rendered.
            let display = display_of(&body);
            // Preserve the hidden setup and implicit module import for the Run
            // button and shared playground link without showing that boilerplate.
            let browser_source = imported(mod_attr(info), &compile_of(&body));
            if tooltip_eligible && checked_ok {
                match analyze_types(&body, info, extra_roots)
                    .and_then(|types| typed_html(&display, &new_info, &types, &browser_source))
                {
                    Ok(html) => {
                        out.push_str(indent);
                        out.push_str(&html);
                        i = j + 1;
                        continue;
                    }
                    Err(error) => warnings.push(format!("typed tooltip block: {error}")),
                }
            }
            // No tooltips for this block; bake plain lexer highlighting so
            // every prism snippet is at least colored. A snippet that does not
            // even lex falls back to the plain fence and is reported: a
            // warning normally, a build failure under `PRISM_MDBOOK_STRICT`
            // (the same escalation every preprocessor warning gets).
            match plain_html(&display, &new_info, &browser_source) {
                Ok(html) => {
                    out.push_str(indent);
                    out.push_str(&html);
                    i = j + 1;
                    continue;
                }
                Err(error) => {
                    let snippet: String = display
                        .split_whitespace()
                        .take(6)
                        .collect::<Vec<_>>()
                        .join(" ");
                    warnings.push(format!("prism block does not lex ({snippet}): {error}"));
                }
            }
            out.push_str(indent);
            out.push_str(marker);
            out.push_str(&new_info);
            out.push('\n');
            out.push_str(&display);
        } else {
            out.push_str(lines[i]);
            out.push('\n');
            out.push_str(&body);
        }
        if j < lines.len() {
            out.push_str(lines[j]);
            out.push('\n');
        }
        i = j + 1;
    }
    (out, warnings)
}

// The source directories of the repository's packages, for resolving a package
// page's doc blocks: every `<repo>/packages/*/src` that exists, in name order.
// The book root is `<repo>/docs`, so the packages tree is its sibling.
fn package_src_dirs(book_root: &Path) -> Vec<PathBuf> {
    let Some(repo) = book_root.parent() else {
        return Vec::new();
    };
    let Ok(entries) = fs::read_dir(repo.join(PACKAGES_DIR.trim_end_matches('/'))) else {
        return Vec::new();
    };
    let mut dirs: Vec<PathBuf> = entries
        .filter_map(Result::ok)
        .map(|e| e.path().join("src"))
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    dirs
}

// The module bundle a package page ships for its Run buttons: every `.pr`
// under each package `src`, keyed by dotted module path, as one JSON script
// tag. The browser passes the bundle to `run_with_modules`, so a block that
// imports a package module runs against the same sources the page's checks
// resolved against instead of failing to resolve the import. The `</` escape
// keeps a source that happens to contain the sequence from closing the tag.
fn package_bundle_html(package_dirs: &[PathBuf]) -> Option<String> {
    fn collect(dir: &Path, prefix: &[String], out: &mut serde_json::Map<String, Value>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<PathBuf> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
        entries.sort();
        for p in entries {
            let Some(stem) = p.file_stem().and_then(|s| s.to_str()) else {
                continue;
            };
            if p.is_dir() {
                let mut pre = prefix.to_vec();
                pre.push(stem.to_string());
                collect(&p, &pre, out);
            } else if p.extension().and_then(|e| e.to_str()) == Some(crate::driver::SOURCE_EXT) {
                if let Ok(src) = fs::read_to_string(&p) {
                    let mut key = prefix.to_vec();
                    key.push(stem.to_string());
                    out.insert(key.join("."), Value::String(src));
                }
            }
        }
    }
    let mut modules = serde_json::Map::new();
    for dir in package_dirs {
        collect(dir, &[], &mut modules);
    }
    if modules.is_empty() {
        return None;
    }
    let json = Value::Object(modules).to_string().replace("</", "<\\/");
    Some(format!(
        "\n\n<script type=\"application/json\" class=\"prism-modules\">{json}</script>\n"
    ))
}

// Walk the mdbook section tree, rewriting each chapter's content in place. A
// chapter under `packages/` gets the package source roots for its doc blocks
// (and ships the module bundle for its Run buttons); every other chapter
// resolves against the book root and stdlib alone.
fn walk(
    items: &mut Vec<Value>,
    warnings: &mut Vec<String>,
    book_root: &Path,
    package_dirs: &[PathBuf],
    bundle: Option<&str>,
) {
    for item in items {
        let Some(chapter) = item.get_mut("Chapter") else {
            continue;
        };
        let in_packages = chapter
            .get("source_path")
            .and_then(Value::as_str)
            .is_some_and(|p| p.starts_with(PACKAGES_DIR));
        let extras = if in_packages { package_dirs } else { &[] };
        if let Some(content) = chapter.get("content").and_then(Value::as_str) {
            let (mut new, mut w) = annotate_markdown(content, book_root, extras);
            if in_packages {
                if let Some(tag) = bundle {
                    new.push_str(tag);
                }
            }
            warnings.append(&mut w);
            chapter["content"] = Value::String(new);
        }
        if let Some(subs) = chapter.get_mut("sub_items").and_then(Value::as_array_mut) {
            walk(subs, warnings, book_root, package_dirs, bundle);
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
        .map_err(|e| Error::CodegenDocs(format!("mdbook preprocessor input: {e}")))?;
    let mut book = parsed.get(1).cloned().ok_or_else(|| {
        Error::CodegenDocs("mdbook preprocessor: expected [context, book]".into())
    })?;
    // The book's markdown source directory, from the preprocessor context (the
    // stdlib injection reads module pages from it; mdbook itself only loads
    // chapters SUMMARY.md names).
    let ctx = parsed.get(0);
    let root = ctx
        .and_then(|c| c.get("root"))
        .and_then(Value::as_str)
        .unwrap_or(".");
    let src = ctx
        .and_then(|c| c.pointer("/config/book/src"))
        .and_then(Value::as_str)
        .unwrap_or("src");
    let src_dir = Path::new(root).join(src);
    let mut warnings = Vec::new();
    // The book's chapter array is `items` (older mdbook used `sections`).
    let key = if book.get("items").is_some() {
        "items"
    } else {
        "sections"
    };
    if let Some(items) = book.get_mut(key).and_then(Value::as_array_mut) {
        let mut existing = BTreeSet::new();
        collect_source_paths(items, &mut existing);
        inject_generated(items, &src_dir, &existing, &mut warnings)?;
        let package_dirs = package_src_dirs(Path::new(root));
        let bundle = package_bundle_html(&package_dirs);
        walk(
            items,
            &mut warnings,
            Path::new(root),
            &package_dirs,
            bundle.as_deref(),
        );
    }
    let json = serde_json::to_string(&book)
        .map_err(|e| Error::CodegenDocs(format!("mdbook preprocessor output: {e}")))?;
    Ok((json, warnings))
}

#[cfg(test)]
mod tests {
    use std::env;
    use std::fs;
    use std::path::Path;
    use std::process;
    use std::slice;

    use super::{annotate_markdown, package_bundle_html};

    // The bundle a package page ships: every `.pr` under the package sources,
    // keyed by dotted module path, in one script tag whose JSON can never close
    // the tag early. The browser hands the map to `run_with_modules`, so a key
    // that drifted from the dotted import spelling would break every package
    // Run button at once.
    #[test]
    fn package_bundle_keys_are_dotted_and_tag_safe() {
        let dir = env::temp_dir().join(format!("prism-bundle-test-{}", process::id()));
        let nested = dir.join("Deep");
        fs::create_dir_all(&nested).unwrap();
        fs::write(dir.join("Tc.pr"), "-- s = \"</script>\"\n").unwrap();
        fs::write(nested.join("Util.pr"), "fn u() : Int = 1\n").unwrap();
        let html = package_bundle_html(slice::from_ref(&dir)).expect("bundle");
        fs::remove_dir_all(&dir).unwrap();
        assert!(html.contains("class=\"prism-modules\""));
        assert!(
            html.contains("\"Tc\""),
            "top-level module keyed by stem: {html}"
        );
        assert!(
            html.contains("\"Deep.Util\""),
            "nested module keyed dotted: {html}"
        );
        assert!(
            !html.contains("</script>\""),
            "closing tag must be escaped: {html}"
        );
    }

    // Comments are lexed as trivia, so a renderer reading the token stream alone
    // emits them unclassed and they inherit the color of the surrounding code.
    // Both bake paths merge the trivia table back in; check each one.
    #[test]
    fn comments_are_classed_in_both_bake_paths() {
        for markdown in [
            "```prism\n-- a comment\nfn add(x : Int) : Int = x + 2\n```\n",
            "```prism,compile_fail\n-- a comment\nfn bad() : Int = true\n```\n",
        ] {
            let (rendered, warnings) = annotate_markdown(markdown, Path::new("."), &[]);
            assert!(warnings.is_empty(), "{warnings:?}");
            assert!(
                rendered.contains("<span class=\"hljs-comment\">-- a comment</span>"),
                "comment left unclassed: {rendered}"
            );
        }
    }

    #[test]
    fn compiling_block_bakes_theme_classes_and_nested_types_idempotently() {
        let markdown = "```prism\nfn add(x : Int) : Int = x + 2\n```\n";
        let (once, warnings) = annotate_markdown(markdown, Path::new("."), &[]);
        assert!(warnings.is_empty(), "{warnings:?}");
        assert!(once.contains("<pre class=\"prism-typed-block\">"));
        assert!(once.contains("class=\"language-prism hljs prism-typed check ok\""));
        assert!(once.contains("class=\"hljs-keyword\""));
        assert!(!once.contains("prism-tok"));
        assert!(once.contains("data-type=\"Int\""));
        assert!(once.contains(">add</span>"), "function name is typed");
        assert!(once.contains(">x</span>"), "function parameter is typed");
        assert!(once.contains("&quot;format&quot;:&quot;prism-typespans-v1&quot;"));
        assert!(!once.contains("```"));

        let (twice, warnings) = annotate_markdown(&once, Path::new("."), &[]);
        assert!(warnings.is_empty(), "{warnings:?}");
        assert_eq!(twice, once, "typed docs bake must be byte-idempotent");
    }

    #[test]
    fn stdlib_module_context_reaches_the_browser_runner() {
        let markdown = "```prism,mod=Data.Tensor\nstrides(new([2, 3], 0.0))\n```\n";
        let (rendered, warnings) = annotate_markdown(markdown, Path::new("."), &[]);
        assert!(warnings.is_empty(), "{warnings:?}");
        assert!(rendered.contains("class=\"language-prism hljs prism-typed run ok\""));
        assert!(rendered.contains(
            "data-prism-source=\"import Data.Tensor (..)\n\nstrides(new([2, 3], 0.0))\n\""
        ));
        assert!(rendered.contains(">strides</span>"));
    }

    #[test]
    fn compile_fail_blocks_are_never_analyzed_for_tooltips() {
        let markdown = "```prism,compile_fail\nfn bad() : Int = true\n```\n";
        let (rendered, warnings) = annotate_markdown(markdown, Path::new("."), &[]);
        assert!(warnings.is_empty(), "{warnings:?}");
        // Plain lexer highlighting is baked (every prism snippet is colored),
        // but never a typespans payload: no analysis ran.
        assert!(rendered.contains("prism-typed-block"));
        assert!(rendered.contains("cfail ok"));
        assert!(!rendered.contains("data-typespans"));
        assert!(!rendered.contains("data-type=\""));
    }
}
