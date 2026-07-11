//! A narrow, format-preserving editor for the `[dependencies]` table of a
//! `prism.toml`.
//!
//! `prism add` needs to add or replace one dependency key without disturbing the
//! rest of the file: comments, key ordering, blank lines, and the exact bytes of
//! every line it does not touch must survive. A general TOML re-emit cannot
//! promise that (it normalizes), and pulling in a format-preserving TOML crate
//! for a single append-or-replace is more dependency than the operation earns.
//! The parser below builds a small format-preserving document model whose lines
//! distinguish sections, assignments, comments, blanks, and opaque syntax. The
//! editor changes one assignment node or inserts one, then renders every untouched
//! node from its original bytes. Only the edited key's own line
//! changes; an inline comment on that one line is not preserved, because the line
//! is the thing being rewritten.

use std::fmt::Write as _;

use crate::project::{hash_pin, DepSource};

// A TOML section header is a line whose trimmed form is bracketed. `[dependencies]`
// is matched exactly so a subtable (`[dependencies.foo]`) or a neighbour section
// ends the span rather than being mistaken for it.
const DEPS_HEADER: &str = "[dependencies]";

#[derive(Clone, Debug, PartialEq, Eq)]
enum SectionName {
    Dependencies,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LineKind {
    Section(SectionName),
    Assignment(String),
    Blank,
    Comment,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ManifestLine {
    raw: String,
    kind: LineKind,
}

impl ManifestLine {
    fn parse(raw: String) -> Self {
        let content = trimmed(&raw);
        let kind = if content.is_empty() {
            LineKind::Blank
        } else if content.starts_with('#') {
            LineKind::Comment
        } else if is_section_header(content) {
            if content == DEPS_HEADER {
                LineKind::Section(SectionName::Dependencies)
            } else {
                LineKind::Section(SectionName::Other)
            }
        } else if let Some((key, _)) = content.split_once('=') {
            let key = key.trim();
            if key.is_empty() {
                LineKind::Other
            } else {
                LineKind::Assignment(key.to_string())
            }
        } else {
            LineKind::Other
        };
        Self { raw, kind }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ManifestDocument {
    lines: Vec<ManifestLine>,
}

impl ManifestDocument {
    fn parse(text: &str) -> Self {
        Self {
            lines: text
                .split_inclusive('\n')
                .map(|line| ManifestLine::parse(line.to_string()))
                .collect(),
        }
    }

    fn dependency_section(&self) -> Option<(usize, usize)> {
        let header = self
            .lines
            .iter()
            .position(|line| line.kind == LineKind::Section(SectionName::Dependencies))?;
        let end = self.lines[header + 1..]
            .iter()
            .position(|line| matches!(line.kind, LineKind::Section(_)))
            .map_or(self.lines.len(), |offset| header + 1 + offset);
        Some((header, end))
    }

    fn render(self) -> String {
        self.lines.into_iter().map(|line| line.raw).collect()
    }
}

/// The `prism.toml` right-hand side for a dependency source.
///
/// A bare pin string, or an inline table for the path and git forms; the single
/// place add-side source syntax is spelled, inverse to the parser in
/// [`crate::project`].
#[must_use]
pub fn render_source(source: &DepSource) -> String {
    match source {
        DepSource::Hash(hex) => format!("{:?}", hash_pin(hex)),
        DepSource::Path(p) => format!("{{ path = {:?} }}", p.display().to_string()),
        DepSource::Git { url, version } => {
            format!("{{ git = {url:?}, version = {version:?} }}")
        }
    }
}

/// Add or replace `name` in the `[dependencies]` table of `text`, returning the
/// edited document. `value` is the rendered right-hand side (see
/// [`render_source`]).
///
/// If the key exists its line is rewritten in place (indentation preserved); if
/// it does not, a line is appended at the end of the section; if the section is
/// absent it is created at the end of the file. Every line the edit does not
/// target is returned byte-for-byte unchanged.
#[must_use]
pub fn set_dependency(text: &str, name: &str, value: &str) -> String {
    let mut document = ManifestDocument::parse(text);
    let Some((header, end)) = document.dependency_section() else {
        return append_new_section(text, name, value);
    };

    if let Some(key_idx) = (header + 1..end).find(
        |&index| matches!(&document.lines[index].kind, LineKind::Assignment(key) if key == name),
    ) {
        let line = &mut document.lines[key_idx];
        line.raw = rewrite_line(&line.raw, name, value);
        line.kind = LineKind::Assignment(name.to_string());
        return document.render();
    }

    // Insert after section content but before its trailing blank separator.
    let insert_at = (header + 1..end)
        .rev()
        .find(|&index| document.lines[index].kind != LineKind::Blank)
        .map_or(header + 1, |index| index + 1);
    ensure_newline(&mut document.lines, insert_at);
    document.lines.insert(
        insert_at,
        ManifestLine {
            raw: format!("{name} = {value}\n"),
            kind: LineKind::Assignment(name.to_string()),
        },
    );
    document.render()
}

// Append a fresh `[dependencies]` section (with the one key) to a document that
// has none, separated from the existing body by a blank line.
fn append_new_section(text: &str, name: &str, value: &str) -> String {
    let mut out = String::from(text);
    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(DEPS_HEADER);
    out.push('\n');
    let _ = writeln!(out, "{name} = {value}");
    out
}

// Rewrite a key line as `<indent><name> = <value><eol>`, preserving the original
// line's leading indentation and terminator.
fn rewrite_line(seg: &str, name: &str, value: &str) -> String {
    let eol = line_eol(seg);
    let content = &seg[..seg.len() - eol.len()];
    let indent = &content[..content.len() - content.trim_start().len()];
    format!("{indent}{name} = {value}{eol}")
}

// Whether a line is a TOML section header (`[..]` or `[[..]]` when trimmed).
fn is_section_header(seg: &str) -> bool {
    let t = trimmed(seg);
    t.starts_with('[') && t.ends_with(']')
}

// A segment's line terminator: `\r\n`, `\n`, or empty for a final line with none.
fn line_eol(seg: &str) -> &str {
    if seg.ends_with("\r\n") {
        "\r\n"
    } else if seg.ends_with('\n') {
        "\n"
    } else {
        ""
    }
}

// A segment's content with any terminator and surrounding whitespace removed.
fn trimmed(seg: &str) -> &str {
    seg.trim_end_matches(['\r', '\n']).trim()
}

// Ensure the segment before an insertion point ends in a newline, so the inserted
// line begins on its own row even when the file's last line had no terminator.
fn ensure_newline(lines: &mut [ManifestLine], insert_at: usize) {
    if insert_at > 0 {
        let previous = &mut lines[insert_at - 1].raw;
        if !previous.ends_with('\n') {
            previous.push('\n');
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    const BASE: &str = r#"[package]
name = "app" # the app

[bin]
entry = "src/main.pr"

[dependencies]
geo = { path = "../geo" } # local dep
util = "../util"
"#;

    #[test]
    fn replaces_an_existing_key_in_place_touching_nothing_else() {
        let out = set_dependency(BASE, "util", "\"../vendored/util\"");
        // The one changed line is the target; every other byte is preserved,
        // including the `[package]` inline comment and the ordering.
        assert!(out.contains("util = \"../vendored/util\"\n"));
        assert!(out.contains("name = \"app\" # the app\n"));
        assert!(out.contains("geo = { path = \"../geo\" } # local dep\n"));
        // `util` stays in its original position after `geo`.
        let geo = out.find("geo =").unwrap();
        let util = out.find("util =").unwrap();
        assert!(geo < util);
    }

    #[test]
    fn appends_a_new_key_at_the_end_of_the_section() {
        let out = set_dependency(BASE, "http", "{ git = \"g/h\", version = \"2.0\" }");
        assert!(out.contains("http = { git = \"g/h\", version = \"2.0\" }\n"));
        // The new key lands inside `[dependencies]`, after the existing keys, not
        // after the file's trailing content.
        let deps = out.find("[dependencies]").unwrap();
        let http = out.find("http =").unwrap();
        assert!(deps < http);
        assert!(out.contains("util = \"../util\"\n"));
    }

    #[test]
    fn creates_the_section_when_absent() {
        let no_deps = r#"[package]
name = "a"

[bin]
entry = "s.pr"
"#;
        let out = set_dependency(no_deps, "geo", "{ path = \"../geo\" }");
        assert!(out.contains("[dependencies]\ngeo = { path = \"../geo\" }\n"));
        // The original body is untouched and the section is separated by a blank.
        assert!(out.starts_with("[package]\nname = \"a\"\n\n[bin]\nentry = \"s.pr\"\n"));
    }

    #[test]
    fn preserves_bytes_outside_the_edited_key_exactly() {
        // Everything but the rewritten `util` line must be byte-identical.
        let out = set_dependency(BASE, "util", "\"x\"");
        for line in BASE.lines() {
            if line.starts_with("util") {
                continue;
            }
            assert!(out.contains(line), "lost line: {line:?}");
        }
    }

    #[test]
    fn rendered_sources_round_trip_through_the_parser() {
        // The three rendered forms parse back to the source they came from, so the
        // writer and the manifest parser cannot drift.
        for (name, source) in [
            ("h", DepSource::Hash("9f86d081".to_string())),
            ("p", DepSource::Path(PathBuf::from("../geo"))),
            (
                "g",
                DepSource::Git {
                    url: "github.com/x/y".to_string(),
                    version: "2.0".to_string(),
                },
            ),
        ] {
            let doc = set_dependency(
                r#"[package]
name = "a"

[bin]
entry = "s.pr"
"#,
                name,
                &render_source(&source),
            );
            let m = crate::project::Manifest::parse(&doc).unwrap();
            let dep = m.dependencies.iter().find(|d| d.name == name).unwrap();
            assert_eq!(dep.source, source);
        }
    }
}
