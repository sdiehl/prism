use std::fmt::Write;

use super::decl::fmt_ty;
use super::{ConvDir, Converter, Fmt, Mode, Rung, StableDecl, INDENT};
use crate::kw;

impl Fmt<'_> {
    // A `stable` block, one rung or converter per line inside real braces (so the
    // entries are comma-separated, like a class body). Always multi-line, so the
    // layout is a pure function of the tree and round-trips idempotently; the
    // per-rung `frozen "<digest>"` golden is preserved verbatim.
    pub(super) fn fmt_stable(&self, sd: &StableDecl) -> String {
        let mut lines: Vec<String> = Vec::new();
        for r in &sd.rungs {
            lines.push(self.fmt_rung(r));
        }
        for c in &sd.converters {
            lines.push(self.fmt_converter(c));
        }
        let body = lines
            .iter()
            .map(|l| format!("{INDENT}{l}"))
            .collect::<Vec<_>>()
            .join(",\n");
        format!("{} {} {{\n{body}\n}}", kw::STABLE, sd.name)
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
