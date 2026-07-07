use super::{Fmt, Mode, INDENT};
use crate::kw;
use crate::syntax::ast::{Expr, PathOp, PathStep, S};

impl Fmt<'_> {
    pub(super) fn fmt_record_break(
        &self,
        name: &str,
        base: Option<&S<Expr>>,
        fields: &[(String, S<Expr>)],
        indent: usize,
    ) -> String {
        let inner = INDENT.repeat(indent + 1);
        let mut lines: Vec<String> = Vec::new();
        if let Some(value) = base {
            lines.push(format!(
                "{inner}..{}",
                self.fmt_expr(value, indent + 1, Mode::Flat)
            ));
        }
        for (field, value) in fields {
            lines.push(format!(
                "{inner}{field} = {}",
                self.fmt_expr(value, indent + 1, Mode::Flat)
            ));
        }
        format!(
            "{name} {{\n{}\n{}}}",
            lines.join(",\n"),
            INDENT.repeat(indent)
        )
    }

    pub(super) fn fmt_path_update_break(
        &self,
        e: &S<Expr>,
        base: &S<Expr>,
        updates: &[(Vec<PathStep>, PathOp)],
        indent: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let base_s = self.fmt_expr(base, indent + 1, Mode::Flat);
        let mut lines = vec![format!("{{ {base_s}")];
        for (index, (path, op)) in updates.iter().enumerate() {
            let Some(path_s) = self.fmt_path(path) else {
                return self.verbatim(e.span.start, e.span.end);
            };
            let (sigil, value) = match op {
                PathOp::Set(value) => (kw::EQ, value),
                PathOp::Modify(value) => (kw::TILDE, value),
            };
            let lead = if index == 0 { "|" } else { "," };
            let value_s = self.fmt_expr(value, indent + 1, Mode::Flat);
            lines.push(format!("{ind}{lead} {path_s} {sigil} {value_s}"));
        }
        lines.push(format!("{ind}}}"));
        lines.join("\n")
    }
}
