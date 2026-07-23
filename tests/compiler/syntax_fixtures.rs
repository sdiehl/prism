// The two versioned syntax seams: `dump syntax-tokens` and `dump surface-syntax`.
// Each is the deterministic boundary a Prism-written lexer, layout pass, or
// parser is diffed against, mirroring the front-end fixture seams. Coverage:
//
// 1. Determinism. Every phase dumps byte-identically across two runs.
// 2. Committed goldens. Each positive corpus file pairs with one golden per
//    phase holding the exact bytes; any drift is a reviewed boundary change.
//    Regenerate with PRISM_ACCEPT_SYNTAX_FIXTURES=1.
// 3. Positive version compatibility. Each golden carries its schema tag and the
//    compiler version, checked against independently re-typed constants.
// 4. Negative version compatibility. A committed mismatch fixture per schema is
//    well-formed JSON carrying a wrong tag that a versioned reader must reject.
// 5. Malformed input. A lex error refuses both seams; a parse error refuses the
//    surface seam while the token seam still exports (lexing succeeded), so the
//    two failure boundaries stay distinct.
// 6. The cover invariant. Raw token spans plus comment trivia spans are
//    ascending, disjoint, in bounds, and tile the embedded source up to
//    whitespace: the token-level statement of losslessness.
// 7. Repository-wide properties. Every example and test case that lexes/parses
//    also satisfies determinism, schema, and the cover invariant.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const ACCEPT: &str = "PRISM_ACCEPT_SYNTAX_FIXTURES";

// The two seams and their schema tags, re-typed independently of the compiler
// so an emitter schema drift cannot re-pin the value it is checked against.
const PHASES: [(&str, &str); 2] = [
    ("syntax-tokens", "prism-syntax-tokens-v1"),
    ("surface-syntax", "prism-surface-syntax-v1"),
];

// The corpus-wide walk must actually visit a corpus; a floor guards against a
// silently empty glob reading as "covered everything".
const CORPUS_FLOOR: usize = 100;

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

// The committed golden: the dump's bytes plus exactly one terminating newline, so
// the file satisfies the end-of-file hook while the comparison stays exact bytes.
fn golden_document(dump: &str) -> String {
    format!("{dump}\n")
}

// Write a golden atomically (temp then rename) so an interrupted acceptance never
// leaves a truncated golden behind.
fn write_golden(path: &Path, bytes: &str) {
    let tmp = path.with_extension("tmp");
    fs::write(&tmp, bytes).unwrap_or_else(|e| panic!("write {}: {e}", tmp.display()));
    fs::rename(&tmp, path).unwrap_or_else(|e| panic!("rename to {}: {e}", path.display()));
}

// The positive corpus stems: every committed `.pr` fixture except the malformed
// negatives, sorted for a stable iteration order.
fn positive_stems() -> Vec<String> {
    let mut stems: Vec<String> = fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .filter_map(Result::ok)
        .filter_map(|e| {
            let name = e.file_name().into_string().ok()?;
            let stem = name.strip_suffix(".pr")?;
            (!stem.starts_with("malformed")).then(|| stem.to_string())
        })
        .collect();
    stems.sort_unstable();
    assert!(!stems.is_empty(), "no positive syntax fixtures found");
    stems
}

// The golden gate: every corpus file dumps deterministically through both seams,
// matches its committed bytes, parses as versioned JSON, and still carries the
// facts its family exists to pin. Under the acceptance switch it rewrites goldens.
#[test]
fn syntax_seam_goldens_hold() {
    let accepting = env::var_os(ACCEPT).is_some();
    let dir = fixture_dir();
    for stem in positive_stems() {
        let src = read(&dir.join(format!("{stem}.pr")));
        for (phase, schema) in PHASES {
            let out =
                prism::dump(phase, &src).unwrap_or_else(|e| panic!("{stem}.{phase}: dump: {e}"));
            let again =
                prism::dump(phase, &src).unwrap_or_else(|e| panic!("{stem}.{phase}: dump: {e}"));
            assert_eq!(
                out, again,
                "{stem}.{phase}: fixture must be byte-identical across runs"
            );

            let golden_path = dir.join(format!("{stem}.{phase}.json"));
            let document = golden_document(&out);
            if accepting {
                write_golden(&golden_path, &document);
                eprintln!("accepted {}", golden_path.display());
            } else {
                let golden = read(&golden_path);
                assert!(
                    document == golden,
                    "{stem}.{phase}: fixture bytes diverge from the committed golden \
                     (review as a syntax boundary change; regenerate with {ACCEPT}=1)"
                );
            }

            let doc: Value =
                serde_json::from_str(&out).unwrap_or_else(|e| panic!("{stem}.{phase}: JSON: {e}"));
            assert_eq!(doc["schema"], schema, "{stem}.{phase}: schema tag");
            assert_eq!(
                doc["compiler"],
                env!("CARGO_PKG_VERSION"),
                "{stem}.{phase}: compiler version"
            );
            assert_eq!(
                doc["source"]["text"], src,
                "{stem}.{phase}: embedded source must be the exact fixture bytes"
            );
            match phase {
                "syntax-tokens" => assert_tokens_doc(&stem, &doc),
                "surface-syntax" => assert_surface_doc(&stem, &doc),
                other => panic!("unknown seam {other}"),
            }
        }
    }
}

// -------------------------------------------------------------------------
// Token-seam probes
// -------------------------------------------------------------------------

// A node's `[lo, hi)` span as byte offsets, checked rather than cast.
fn span_bounds(node: &Value, ctx: &str) -> (usize, usize) {
    let bound = |i: usize| {
        let raw = node["span"][i]
            .as_u64()
            .unwrap_or_else(|| panic!("{ctx}: span[{i}]"));
        usize::try_from(raw).unwrap_or_else(|_| panic!("{ctx}: span[{i}] overflows usize"))
    };
    (bound(0), bound(1))
}

fn spans_of(rows: &Value, ctx: &str) -> Vec<(usize, usize)> {
    rows.as_array()
        .unwrap_or_else(|| panic!("{ctx}: expected an array"))
        .iter()
        .map(|r| span_bounds(r, ctx))
        .collect()
}

fn kinds_of(rows: &Value, ctx: &str) -> Vec<String> {
    rows.as_array()
        .unwrap_or_else(|| panic!("{ctx}: expected an array"))
        .iter()
        .map(|r| r["kind"].as_str().expect("kind string").to_string())
        .collect()
}

// The cover invariant: raw token spans plus non-blank trivia spans, in order,
// tile the source up to whitespace. Blank-line events are positional markers
// over bytes the gaps already account for, so they are excluded from the cover.
fn assert_token_cover(ctx: &str, doc: &Value) {
    let text = doc["source"]["text"].as_str().expect("source text");
    let mut spans = spans_of(&doc["raw"], ctx);
    let trivia = doc["trivia"].as_array().expect("trivia array");
    for t in trivia {
        if t["kind"] != "blank" {
            spans.push(span_bounds(t, ctx));
        }
    }
    spans.sort_unstable();
    let mut pos = 0;
    for (lo, hi) in spans {
        assert!(
            lo >= pos,
            "{ctx}: overlapping spans at byte {lo} (previous span ends at {pos})"
        );
        assert!(hi <= text.len(), "{ctx}: span [{lo}, {hi}) out of bounds");
        assert!(
            text[pos..lo].chars().all(char::is_whitespace),
            "{ctx}: uncovered non-whitespace bytes in [{pos}, {lo})"
        );
        pos = hi;
    }
    assert!(
        text[pos..].chars().all(char::is_whitespace),
        "{ctx}: uncovered non-whitespace tail after byte {pos}"
    );
}

fn assert_tokens_doc(stem: &str, doc: &Value) {
    let ctx = format!("{stem}.syntax-tokens");
    assert_token_cover(&ctx, doc);
    let raw = kinds_of(&doc["raw"], &ctx);
    let parse = kinds_of(&doc["parse"], &ctx);
    assert!(!raw.is_empty(), "{ctx}: raw stream is empty");
    assert!(
        raw.iter().all(|k| !k.is_empty()),
        "{ctx}: empty token kind name"
    );
    // Every fixture opens at least one layout block, and virtual tokens exist
    // only post-layout: the two streams must genuinely differ.
    assert!(
        parse.iter().any(|k| k == "v{"),
        "{ctx}: post-layout stream carries no virtual open"
    );
    assert!(
        !raw.iter().any(|k| k.starts_with('v') && k.len() == 2),
        "{ctx}: raw stream must carry no virtual tokens"
    );
    if stem == "interp" {
        for kind in ["istart", "iend"] {
            assert!(
                raw.iter().any(|k| k == kind),
                "{ctx}: expected an {kind} token from interpolation"
            );
        }
    }
}

// -------------------------------------------------------------------------
// Surface-seam probes
// -------------------------------------------------------------------------

// Whether any node in the tree carries the given `kind` tag.
fn contains_kind(v: &Value, kind: &str) -> bool {
    match v {
        Value::Object(m) => {
            m.get("kind").and_then(Value::as_str) == Some(kind)
                || m.values().any(|c| contains_kind(c, kind))
        }
        Value::Array(items) => items.iter().any(|c| contains_kind(c, kind)),
        _ => false,
    }
}

// Whether any object in the tree carries the given field.
fn contains_field(v: &Value, field: &str) -> bool {
    match v {
        Value::Object(m) => m.contains_key(field) || m.values().any(|c| contains_field(c, field)),
        Value::Array(items) => items.iter().any(|c| contains_field(c, field)),
        _ => false,
    }
}

// The node kinds each corpus family exists to pin, so an accepted-but-hollow
// golden cannot silently drop a family.
fn required_kinds(stem: &str) -> &'static [&'static str] {
    match stem {
        "decls" => &[
            "import",
            "data",
            "newtype",
            "type-synonym",
            "error",
            "const",
        ],
        "types" => &["effect", "fun", "unboxed-tuple", "unboxed-record", "forall"],
        "exprs" => &[
            "path-update",
            "read-path",
            "comprehension",
            "range",
            "compose",
            "opt-chain",
            "default",
            "hole",
            "marker",
        ],
        "patterns" => &["pattern", "ctor", "record", "wild"],
        "effects" => &[
            "handle",
            "named-handle",
            "mask",
            "var-decl",
            "assign",
            "index-assign",
            "while",
            "loop",
            "for",
            "transact",
            "probe",
            "try-catch",
            "throw",
            "break",
            "continue",
            "once",
            "val",
            "never",
        ],
        "classes" => &["class", "instance", "canonical"],
        "contracts" => &["logic-fn"],
        "stable" => &["stable"],
        "interp" => &["class", "instance", "effect"],
        _ => &[],
    }
}

// The field names a family's golden must carry beyond node kinds.
fn required_fields(stem: &str) -> &'static [&'static str] {
    match stem {
        "decls" => &["vis", "deprecated"],
        "types" => &["effects", "tail", "param_kinds"],
        "classes" => &["supers", "context", "constraints", "wheres"],
        "contracts" => &["requires", "ensures", "decreases", "total", "fip", "test"],
        "stable" => &["rungs", "migrations"],
        "exprs" => &["synth"],
        _ => &[],
    }
}

fn assert_surface_doc(stem: &str, doc: &Value) {
    let ctx = format!("{stem}.surface-syntax");
    let items = doc["items"]
        .as_array()
        .unwrap_or_else(|| panic!("{ctx}: items array"));
    assert!(!items.is_empty(), "{ctx}: no items");
    let text_len = doc["source"]["text"].as_str().expect("source text").len();
    let mut prev = 0;
    for item in items {
        assert!(
            item["kind"].is_string(),
            "{ctx}: item without a kind: {item}"
        );
        let (lo, hi) = span_bounds(item, &ctx);
        assert!(
            hi <= text_len,
            "{ctx}: item span [{lo}, {hi}) out of bounds"
        );
        assert!(lo >= prev, "{ctx}: items out of source order at byte {lo}");
        prev = lo;
    }
    for kind in required_kinds(stem) {
        assert!(
            contains_kind(doc, kind),
            "{ctx}: expected a `{kind}` node (the golden went hollow)"
        );
    }
    for field in required_fields(stem) {
        assert!(
            contains_field(doc, field),
            "{ctx}: expected a `{field}` field (the golden went hollow)"
        );
    }
}

// -------------------------------------------------------------------------
// Negatives
// -------------------------------------------------------------------------

// A lex error refuses both seams. A parse error refuses only the surface seam:
// the token seam still exports because lexing succeeded, which is exactly the
// boundary between the two artifacts.
#[test]
fn syntax_seam_refuses_malformed() {
    let dir = fixture_dir();
    let lex_bad = read(&dir.join("malformed_lex.pr"));
    for (phase, _) in PHASES {
        assert!(
            prism::dump(phase, &lex_bad).is_err(),
            "{phase}: must refuse a lex error"
        );
    }
    let parse_bad = read(&dir.join("malformed_parse.pr"));
    assert!(
        prism::dump("surface-syntax", &parse_bad).is_err(),
        "surface-syntax: must refuse a parse error"
    );
    assert!(
        prism::dump("syntax-tokens", &parse_bad).is_ok(),
        "syntax-tokens: a parse-only error still lexes, so the token seam exports"
    );
}

// Negative version compatibility: each mismatch fixture is well-formed JSON but
// names a wrong schema tag, so a reader keyed on the versioned tag rejects it
// while still recognizing it as a (wrongly versioned) export.
#[test]
fn syntax_seam_rejects_version_mismatch() {
    let dir = fixture_dir();
    for (phase, schema) in PHASES {
        let path = dir.join(format!("mismatch.{phase}.json"));
        let doc: Value = serde_json::from_str(&read(&path))
            .unwrap_or_else(|e| panic!("{phase} mismatch: JSON: {e}"));
        assert!(
            doc["schema"].is_string(),
            "{phase}: mismatch fixture still names a schema"
        );
        assert_ne!(
            doc["schema"], schema,
            "{phase}: mismatch fixture must not carry the current tag"
        );
    }
}

// -------------------------------------------------------------------------
// Repository-wide properties
// -------------------------------------------------------------------------

fn corpus_files() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    for dir in ["examples", "tests/cases", "tests/cases/run"] {
        let Ok(entries) = fs::read_dir(root.join(dir)) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "pr") {
                files.push(path);
            }
        }
    }
    files.sort_unstable();
    files
}

// Every repository program that lexes/parses must satisfy the seam properties.
// Files that fail to lex or parse (the negative corpus) are skipped: refusal is
// their correct behavior, pinned above.
#[test]
fn syntax_seam_corpus_properties() {
    let mut covered = 0_usize;
    for path in corpus_files() {
        let src = read(&path);
        let name = path.display();
        for (phase, schema) in PHASES {
            let Ok(out) = prism::dump(phase, &src) else {
                continue;
            };
            let again = prism::dump(phase, &src)
                .unwrap_or_else(|e| panic!("{name} {phase}: nondeterministic refusal: {e}"));
            assert_eq!(out, again, "{name} {phase}: nondeterministic dump");
            let doc: Value =
                serde_json::from_str(&out).unwrap_or_else(|e| panic!("{name} {phase}: JSON: {e}"));
            assert_eq!(doc["schema"], schema, "{name} {phase}: schema tag");
            if phase == "syntax-tokens" {
                assert_token_cover(&format!("{name}"), &doc);
            }
            covered += 1;
        }
    }
    assert!(
        covered >= CORPUS_FLOOR,
        "corpus walk covered only {covered} dumps; the glob went vacuous"
    );
}
