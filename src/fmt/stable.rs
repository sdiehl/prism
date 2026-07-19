use std::fmt::Write;

use super::decl::fmt_ty;
use super::{ConvDir, Converter, Fmt, Mode, Rung, StableDecl, INDENT};
use crate::kw;
use crate::syntax::ast::{Migration, MigrationDir, MigrationRoute};

impl Fmt<'_> {
    // A `stable` block, one rung, converter, or the migration table per entry
    // inside real braces (so the entries are comma-separated, like a class body).
    // Always multi-line, so the layout is a pure function of the tree and
    // round-trips idempotently; the per-rung `frozen "<digest>"` golden is
    // preserved verbatim.
    pub(super) fn fmt_stable(&self, sd: &StableDecl) -> String {
        let mut items: Vec<String> = Vec::new();
        for r in &sd.rungs {
            items.push(self.fmt_rung(r));
        }
        for c in &sd.converters {
            items.push(self.fmt_converter(c));
        }
        if !sd.migrations.is_empty() {
            items.push(self.fmt_migrations(&sd.migrations));
        }
        let body = items
            .iter()
            .map(|it| indent_lines(it))
            .collect::<Vec<_>>()
            .join(",\n");
        format!("{} {} {{\n{body}\n}}", kw::STABLE, sd.name)
    }

    // The migration table, one row per line. Rows carry no comma: each opens with
    // a rung name, so the parser needs no separator, and a single canonical layout
    // keeps the block idempotent under `prism fmt`.
    fn fmt_migrations(&self, migs: &[Migration]) -> String {
        let rows = migs
            .iter()
            .map(|m| format!("{INDENT}{}", self.fmt_migration_row(m)))
            .collect::<Vec<_>>()
            .join("\n");
        format!("{} {{\n{rows}\n}}", kw::MIGRATIONS)
    }

    fn fmt_migration_row(&self, m: &Migration) -> String {
        format!("{} -> {} = {}", m.from, m.to, self.fmt_route(&m.route))
    }

    fn fmt_route(&self, route: &MigrationRoute) -> String {
        match route {
            MigrationRoute::Auto => kw::AUTO.to_string(),
            MigrationRoute::Version(v) => format!(
                "{}({} = {}, {} = {})",
                kw::VERSION,
                kw::UPGRADE,
                self.fmt_dir(&v.upgrade),
                kw::DOWNGRADE,
                self.fmt_dir(&v.downgrade),
            ),
        }
    }

    fn fmt_dir(&self, dir: &MigrationDir) -> String {
        match dir {
            MigrationDir::Auto => kw::AUTO.to_string(),
            MigrationDir::Expr(e) => self.fmt_expr(e, 0, Mode::Flat),
        }
    }

    fn fmt_rung(&self, r: &Rung) -> String {
        let mut fields: Vec<String> = Vec::new();
        if let Some(base) = &r.base {
            fields.push(format!("..{base}"));
        }
        for f in &r.fields {
            let mut fld = format!("{}: {}", f.name, fmt_ty(&f.ty));
            if let Some(def) = &f.default {
                write!(fld, " = {}", self.fmt_expr(def, 0, Mode::Flat)).unwrap();
            }
            fields.push(fld);
        }
        let mut line = format!("{} = {{ {} }}", r.name, fields.join(", "));
        if let Some(digest) = &r.frozen {
            write!(line, " {} \"{digest}\"", kw::FROZEN).unwrap();
        }
        line
    }

    fn fmt_converter(&self, c: &Converter) -> String {
        let word = match c.dir {
            ConvDir::Upgrade => kw::UPGRADE,
            ConvDir::Downgrade => kw::DOWNGRADE,
        };
        let mut parts: Vec<String> = vec![format!("..{}", self.fmt_expr(&c.base, 0, Mode::Flat))];
        for (name, e) in &c.overrides {
            parts.push(format!("{name} = {}", self.fmt_expr(e, 0, Mode::Flat)));
        }
        let mut line = format!("{word} {} -> {} = {{ {} }}", c.from, c.to, parts.join(", "));
        if !c.drop_loss.is_empty() {
            write!(line, " {}({})", kw::DROP_LOSS, c.drop_loss.join(", ")).unwrap();
        }
        line
    }
}

// Indent every non-empty line of a stable-block entry by one level, so a
// single-line rung indents like before and the multi-line migration table nests
// its rows a further level in.
fn indent_lines(s: &str) -> String {
    s.lines()
        .map(|l| {
            if l.is_empty() {
                String::new()
            } else {
                format!("{INDENT}{l}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}
