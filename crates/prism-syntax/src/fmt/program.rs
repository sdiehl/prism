use std::collections::{BTreeMap, BTreeSet};

use marginalia::{BuiltinKind, Trivia};

use super::decl::{fmt_class, fmt_data, fmt_effect, fmt_import, fmt_labels, fmt_ty};
use super::lit::escape_str;
use super::{Fmt, Mode, Program};
use crate::kw;

impl Fmt<'_> {
    // Every top-level item rendered in place, as `(start, end, text)` in source
    // order. The one enumeration of what a program prints, shared by whole-file
    // formatting and by rendering a single declaration on its own.
    fn items(&self, prog: &Program) -> Vec<(usize, usize, String)> {
        let mut items: Vec<(usize, usize, String)> = Vec::new();
        // Restore the visibility marker the parser stripped into `prog.exports` /
        // `prog.opaques` (opaque implies exported, so it is checked first), then
        // the `deprecated "..."` annotation line the parser lifted into
        // `prog.deprecated`. The annotation prints above the (possibly `pub`-
        // marked) declaration, the canonical order the parser accepts.
        let pubd = |name: &str, s: String| {
            let s = if prog.opaques.contains(name) {
                format!("{} {s}", kw::OPAQUE)
            } else if prog.exports.contains(name) {
                format!("{} {s}", kw::PUB)
            } else {
                s
            };
            if let Some(msg) = prog.deprecated.get(name) {
                format!("{} \"{}\"\n{s}", kw::DEPRECATED, escape_str(msg))
            } else {
                s
            }
        };
        for i in &prog.imports {
            items.push((i.span.start, i.span.end, fmt_import(i)));
        }
        for d in &prog.types {
            items.push((d.span.start, d.span.end, pubd(&d.name, fmt_data(d))));
        }
        for e in &prog.effects {
            items.push((e.span.start, e.span.end, pubd(&e.name, fmt_effect(e))));
        }
        for e in &prog.errors {
            let line = if e.params.is_empty() {
                format!("{} {}", kw::ERROR, e.name)
            } else {
                let ps: Vec<String> = e.params.iter().map(fmt_ty).collect();
                format!("{} {}({})", kw::ERROR, e.name, ps.join(", "))
            };
            items.push((e.span.start, e.span.end, pubd(&e.name, line)));
        }
        for a in &prog.aliases {
            let line = format!("{} {} = {{{}}}", kw::ALIAS, a.name, fmt_labels(&a.labels));
            items.push((a.span.start, a.span.end, pubd(&a.name, line)));
        }
        for s in &prog.synonyms {
            let params = if s.params.is_empty() {
                String::new()
            } else {
                format!("({})", s.params.join(", "))
            };
            let line = format!("{} {}{} = {}", kw::ALIAS, s.name, params, fmt_ty(&s.ty));
            items.push((s.span.start, s.span.end, pubd(&s.name, line)));
        }
        for c in &prog.classes {
            items.push((c.span.start, c.span.end, pubd(&c.name, fmt_class(c))));
        }
        for sd in &prog.stable {
            items.push((sd.span.start, sd.span.end, self.fmt_stable(sd)));
        }
        for i in &prog.instances {
            items.push((i.span.start, i.span.end, self.fmt_instance(i)));
        }
        for c in &prog.canonicals {
            let line = format!(
                "{} {}({}) = {}",
                kw::CANONICAL,
                c.class,
                fmt_ty(&c.head),
                c.name
            );
            items.push((c.span.start, c.span.end, line));
        }
        for p in &prog.patterns {
            items.push((
                p.span.start,
                p.span.end,
                pubd(&p.name, self.fmt_pattern_decl(p)),
            ));
        }
        for f in &prog.fns {
            items.push((
                f.span.start,
                f.span.end,
                pubd(&f.name, self.fmt_fn(f, Mode::Layout)),
            ));
        }
        for f in &prog.logic_fns {
            let line = format!("{} {}", kw::LOGIC, self.fmt_fn(f, Mode::Layout));
            items.push((f.span.start, f.span.end, pubd(&f.name, line)));
        }
        items.sort_by_key(|(start, _, _)| *start);
        items
    }

    // Each top-level item on its own, keyed by source start offset and carrying
    // the comment block written directly above it. A comment group separated
    // from the item by a blank line belongs to what came before, not to it.
    pub(super) fn fmt_items(&self, prog: &Program) -> BTreeMap<usize, String> {
        let mut out = BTreeMap::new();
        let mut prev_end: usize = 0;
        for (start, end, s) in self.items(prog) {
            let mut lead = String::new();
            self.emit_leading_trivia(prev_end, start, &mut lead);
            let attached = lead.rsplit_once("\n\n").map_or(lead.as_str(), |(_, t)| t);
            out.insert(start, format!("{attached}{s}"));
            prev_end = end;
        }
        out
    }

    pub(super) fn fmt_program(&self, prog: &Program) -> String {
        let items = self.items(prog);
        let import_starts: BTreeSet<usize> = prog.imports.iter().map(|i| i.span.start).collect();
        let mut out = String::new();
        let mut prev_end: usize = 0;
        let mut prev_import = false;
        for (idx, (start, end, s)) in items.into_iter().enumerate() {
            let is_import = import_starts.contains(&start);
            let boundary = out.len();
            self.emit_leading_trivia(prev_end, start, &mut out);
            if idx > 0 {
                if prev_import && is_import {
                    // Consecutive imports form one tight block: no separating
                    // blank line, and any blank lines the source carried between
                    // two imports collapse. Comments between them survive.
                    let seg = out.split_off(boundary);
                    for line in seg.lines().filter(|l| !l.is_empty()) {
                        out.push_str(line);
                        out.push('\n');
                    }
                } else if !out[boundary..].starts_with('\n') {
                    // Every other pair of top-level declarations is separated by
                    // a blank line. The leading trivia already opens the gap with
                    // one when the source had it; otherwise insert one ahead of
                    // any attached doc comment so the comment stays with its
                    // declaration.
                    out.insert(boundary, '\n');
                }
            }
            out.push_str(&s);
            out.push('\n');
            prev_end = end;
            prev_import = is_import;
        }

        for ev in self.trivia.after(prev_end) {
            match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => {
                    out.push_str(text);
                    out.push('\n');
                }
                Trivia::Comment { .. } => {}
                Trivia::BlankLine => out.push('\n'),
            }
        }

        out
    }
}
