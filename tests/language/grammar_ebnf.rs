//! Keyword-coverage drift check for the published grammar.
//!
//! `models/grammar.ebnf` is hand-written documentation rendered into the spec by
//! mdbook anchor, and it drifts silently when the lexer gains a reserved word
//! nobody adds to the grammar (the audit found `replayable` and the `without
//! alloc` / `\ alloc` forms missing). This mirrors the nvim highlighter's
//! mirrored-keyword precedent: read the lexer's `#[token("...")]` spellings and
//! fail if the ebnf never mentions one as a terminal.
//!
//! Only the lexer -> ebnf direction is asserted. The reverse (an ebnf terminal
//! the lexer does not reserve) has legitimate members the lexer never tokenizes:
//! literal fragments in the lexical section (`i64`, `u64`, `e`, `n`, `t`, `r`)
//! and contextual words recognized positionally, not reserved (`Type`, `Row`,
//! `view`, `make`). Checking it would need an allow-list of those, so it is left
//! out; the drift that bites is a new reserved word going undocumented.

use std::fs;
use std::path::Path;

const TOKEN_SRC: &str = "src/lex/token.rs";
const EBNF_SRC: &str = "models/grammar.ebnf";
const TOKEN_ATTR: &str = "#[token(\"";

/// A terminal we count is a source-spelling keyword: an ASCII word starting with
/// a letter (reserved words plus the built-in type names). Operators, punctuation
/// and escaped-quote terminals fall outside this and are not compared.
fn is_word(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic())
        && s.chars().all(|c| c.is_ascii_alphanumeric())
}

/// Pull every `#[token("X")]` spelling out of the lexer source.
fn lexer_keywords(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = src;
    while let Some(i) = rest.find(TOKEN_ATTR) {
        rest = &rest[i + TOKEN_ATTR.len()..];
        if let Some(end) = rest.find('"') {
            let spelling = &rest[..end];
            if is_word(spelling) {
                out.push(spelling.to_string());
            }
            rest = &rest[end + 1..];
        }
    }
    out
}

/// Pull every quoted ASCII-word terminal out of the ebnf. Scanning for a `"`
/// then a run of alphanumerics closed by `"` sidesteps the escaped-quote
/// terminals (`"\""`, `"\\"`) in the lexical section, which otherwise mispair.
fn ebnf_word_terminals(src: &str) -> std::collections::HashSet<String> {
    let bytes = src.as_bytes();
    let mut out = std::collections::HashSet::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            let start = i + 1;
            let mut j = start;
            while j < bytes.len() && bytes[j].is_ascii_alphanumeric() {
                j += 1;
            }
            if j > start && j < bytes.len() && bytes[j] == b'"' {
                let word = &src[start..j];
                if is_word(word) {
                    out.insert(word.to_string());
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    out
}

#[test]
fn every_lexer_keyword_is_documented() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let token_src = fs::read_to_string(root.join(TOKEN_SRC)).expect("read lexer source");
    let ebnf_src = fs::read_to_string(root.join(EBNF_SRC)).expect("read grammar.ebnf");

    let keywords = lexer_keywords(&token_src);
    assert!(
        keywords.contains(&"replayable".to_string()),
        "extraction failed: lexer keywords should include `replayable`"
    );

    let documented = ebnf_word_terminals(&ebnf_src);
    let missing: Vec<&String> = keywords
        .iter()
        .filter(|k| !documented.contains(*k))
        .collect();
    assert!(
        missing.is_empty(),
        r"grammar.ebnf drift: the lexer reserves these words but the ebnf never mentions them as terminals: {missing:?}. Document each in models/grammar.ebnf (or, if intentionally undocumented, note why)."
    );
}
