//! Markdown rendering for one stdlib module page and the section index.
//!
//! Declarations are grouped into sections (types, classes, effects, instances,
//! values) but kept in source order within each. Function and value signatures
//! come from the typechecker's inferred `Type::show` (most stdlib functions have
//! no written signature); types, classes, and effects are rendered from the
//! surface AST with the shared `fmt::decl` printers so they read exactly as
//! written, `deriving` and all.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::fmt::decl::{fmt_class, fmt_data, fmt_effect, fmt_labels, fmt_ty};
use crate::syntax::ast::Program;

use super::doctest::{examples_in, Example};
use super::extract::extract;
use super::ModSpec;

// Page section, in the order sections appear on a module page.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Section {
    Type,
    Class,
    Effect,
    Instance,
    Value,
}

impl Section {
    const fn title(self) -> &'static str {
        match self {
            Self::Type => "Types",
            Self::Class => "Type Classes",
            Self::Effect => "Effects",
            Self::Instance => "Instances",
            Self::Value => "Functions and Values",
        }
    }
}

struct Entry {
    start: usize,
    section: Section,
    name: String,
    code: String,
}

// Every top-level declaration start in the file, sorted, so doc-comment
// association sees the true previous-declaration boundary even for private
// helpers that are not themselves rendered.
fn all_starts(p: &Program) -> Vec<usize> {
    let mut s: Vec<usize> = Vec::new();
    s.extend(p.imports.iter().map(|i| i.span.start));
    s.extend(p.types.iter().map(|d| d.span.start));
    s.extend(p.effects.iter().map(|d| d.span.start));
    s.extend(p.errors.iter().map(|d| d.span.start));
    s.extend(p.aliases.iter().map(|d| d.span.start));
    s.extend(p.synonyms.iter().map(|d| d.span.start));
    s.extend(p.classes.iter().map(|d| d.span.start));
    s.extend(p.instances.iter().map(|d| d.span.start));
    s.extend(p.canonicals.iter().map(|d| d.span.start));
    s.extend(p.patterns.iter().map(|d| d.span.start));
    s.extend(p.fns.iter().map(|d| d.span.start));
    s.sort_unstable();
    s.dedup();
    s
}

fn collect_entries(spec: &ModSpec, p: &Program, sigs: &BTreeMap<String, String>) -> Vec<Entry> {
    // The prelude has no `pub` markers (its names are global via prepending), so
    // every declaration is part of the surface; importable modules expose only
    // their exports. Instances are always global, hence always shown.
    let shown = |name: &str| spec.is_prelude || p.exports.contains(name);
    let mut es: Vec<Entry> = Vec::new();

    for d in &p.types {
        if shown(&d.name) {
            es.push(Entry {
                start: d.span.start,
                section: Section::Type,
                name: d.name.clone(),
                code: fmt_data(d),
            });
        }
    }
    for d in &p.synonyms {
        if shown(&d.name) {
            let params = if d.params.is_empty() {
                String::new()
            } else {
                format!("({})", d.params.join(", "))
            };
            es.push(Entry {
                start: d.span.start,
                section: Section::Type,
                name: d.name.clone(),
                code: format!("alias {}{params} = {}", d.name, fmt_ty(&d.ty)),
            });
        }
    }
    for d in &p.classes {
        if shown(&d.name) {
            es.push(Entry {
                start: d.span.start,
                section: Section::Class,
                name: d.name.clone(),
                code: fmt_class(d),
            });
        }
    }
    for d in &p.effects {
        if shown(&d.name) {
            es.push(Entry {
                start: d.span.start,
                section: Section::Effect,
                name: d.name.clone(),
                code: fmt_effect(d),
            });
        }
    }
    for d in &p.errors {
        if shown(&d.name) {
            let args: Vec<String> = d.params.iter().map(fmt_ty).collect();
            es.push(Entry {
                start: d.span.start,
                section: Section::Effect,
                name: d.name.clone(),
                code: format!("error {}({})", d.name, args.join(", ")),
            });
        }
    }
    for d in &p.aliases {
        if shown(&d.name) {
            es.push(Entry {
                start: d.span.start,
                section: Section::Effect,
                name: d.name.clone(),
                code: format!("alias {} = {{{}}}", d.name, fmt_labels(&d.labels)),
            });
        }
    }
    for d in &p.instances {
        es.push(Entry {
            start: d.span.start,
            section: Section::Instance,
            name: d.name.clone(),
            code: format!("instance {} : {}({})", d.name, d.class, fmt_ty(&d.head)),
        });
    }
    for d in &p.patterns {
        if shown(&d.name) {
            es.push(Entry {
                start: d.span.start,
                section: Section::Value,
                name: d.name.clone(),
                code: format!(
                    "pattern {}({}) for {}",
                    d.name,
                    d.params.join(", "),
                    d.for_ty
                ),
            });
        }
    }
    for d in &p.fns {
        if !shown(&d.name) {
            continue;
        }
        let key = if d.konst { "let" } else { "fn" };
        // The whole-stdlib typecheck qualifies an imported module's decls by their
        // module (`Data.Maybe.is_some`); the prelude's own decls stay bare. Try the
        // qualified name first, then the bare one.
        let qualified = format!("{}.{}", spec.dotted, d.name);
        let code = sigs
            .get(&qualified)
            .or_else(|| sigs.get(&d.name))
            .map_or_else(
                || {
                    format!(
                        "{key} {}({})",
                        d.name,
                        d.params
                            .iter()
                            .map(|x| x.name.clone())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                },
                |ty| format!("{} : {ty}", d.name),
            );
        es.push(Entry {
            start: d.span.start,
            section: Section::Value,
            name: d.name.clone(),
            code,
        });
    }

    es.sort_by_key(|e| e.start);
    es
}

// The fence tag for a generated reference block: `def` for a declaration body
// (its printed form opens with a declaration keyword), `sig` for a bare type
// signature. Both render as non-runnable reference; neither is a doctest.
fn block_tag(code: &str) -> &'static str {
    let kw = code.split_whitespace().next().unwrap_or("");
    if matches!(
        kw,
        "type" | "newtype" | "alias" | "class" | "effect" | "error" | "instance" | "pattern"
    ) {
        "def"
    } else {
        "sig"
    }
}

// The full content hash for a declaration, if one exists: a behavior hash for a
// function/value, a shape digest for a datatype/effect. Classes, instances, and
// aliases have none (see the module docs). Emitted as an `h-<hex>` fence token
// the theme turns into a subtle pill beside the block's `Σ` badge; the pill shows
// a short prefix but copies the full hash on click.
fn hash_class(hashes: &BTreeMap<String, String>, spec: &ModSpec, name: &str) -> String {
    let qualified = format!("{}.{}", spec.dotted, name);
    hashes
        .get(&qualified)
        .or_else(|| hashes.get(name))
        .map_or_else(String::new, |h| format!(",h-{h}"))
}

/// Render one module page, returning `(markdown, one-line summary, doctests)`.
/// `hashes` maps a value/type/effect/class name to its content hash; `inst_hashes`
/// does the same for instances (kept apart because instance names share the
/// lowercase namespace with values). Entries found tag their block with the hash.
pub(crate) fn page(
    spec: &ModSpec,
    program: &Program,
    trivia: &marginalia::TriviaTable,
    sigs: &BTreeMap<String, String>,
    hashes: &BTreeMap<String, String>,
    inst_hashes: &BTreeMap<String, String>,
) -> (String, String, Vec<Example>) {
    let docs = extract(trivia, &all_starts(program));
    let entries = collect_entries(spec, program, sigs);
    let mut examples: Vec<Example> = Vec::new();

    let mut out = String::new();
    let _ = writeln!(out, "# {}\n", spec.title);
    let _ = writeln!(
        out,
        "<!-- Generated by `prism docs` from `{}`. Do not edit by hand. -->\n",
        spec.source_path
    );
    if let Some(desc) = &docs.module {
        examples.extend(examples_in(&format!("{} (module)", spec.dotted), desc));
        let _ = writeln!(out, "{desc}\n");
    }

    for section in [
        Section::Type,
        Section::Class,
        Section::Effect,
        Section::Instance,
        Section::Value,
    ] {
        let in_section: Vec<&Entry> = entries.iter().filter(|e| e.section == section).collect();
        if in_section.is_empty() {
            continue;
        }
        let _ = writeln!(out, "## {}\n", section.title());
        // Instance identities live in a separate map (see the doc comment).
        let src = if section == Section::Instance {
            inst_hashes
        } else {
            hashes
        };
        for e in in_section {
            let _ = writeln!(out, "### `{}`\n", e.name);
            // A function/value type signature is a bare `name : T` (Sigma badge);
            // a type/class/effect/instance body is a declaration (reference). Both
            // are non-runnable reference blocks, not doctests. A trailing `h-<hex>`
            // token carries the content hash to the theme's badge row.
            let tag = block_tag(&e.code);
            let hclass = hash_class(src, spec, &e.name);
            let _ = writeln!(out, "```prism,{tag}{hclass}\n{}\n```\n", e.code);
            if let Some(doc) = docs.get(e.start) {
                examples.extend(examples_in(&format!("{}::{}", spec.dotted, e.name), doc));
                let _ = writeln!(out, "{doc}\n");
            }
        }
    }

    let summary = docs
        .module
        .as_deref()
        .and_then(|d| d.lines().next())
        .unwrap_or("")
        .to_string();
    // End with a single trailing newline (dprint-canonical).
    (format!("{}\n", out.trim_end()), summary, examples)
}

/// Render the landing page linking every module. `anchor`, when present, is a
/// Markdown block dropped in under the blurb (the stdlib's content fingerprint).
pub(crate) fn index(
    title: &str,
    blurb: &str,
    anchor: Option<&str>,
    entries: &[(String, String, String)],
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "# {title}\n");
    let _ = writeln!(out, "{blurb}\n");
    if let Some(anchor) = anchor {
        let _ = writeln!(out, "{anchor}\n");
    }
    // A heading (not just a blank line) between the anchor and the module list:
    // CommonMark merges two `-` bullet lists separated only by a blank line into
    // one continuous list, so without it the fingerprint bullets and the module
    // index would render as a single run-on list.
    let _ = writeln!(out, "## Modules\n");
    for (slug, title, summary) in entries {
        if summary.is_empty() {
            let _ = writeln!(out, "- [{title}](./{slug}.md)");
        } else {
            let _ = writeln!(out, "- [{title}](./{slug}.md) - {summary}");
        }
    }
    format!("{}\n", out.trim_end())
}
