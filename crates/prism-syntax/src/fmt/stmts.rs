use super::breaks::{block_trailing_call, forces_break};
use super::{fits_at, indent_col, text_width, Expr, Fmt, Mode, Sugar, INDENT, S};
use crate::kw;

impl Fmt<'_> {
    pub(super) fn fmt_stmt(&self, e: &S<Expr>, indent: usize) -> String {
        if let Some(s) = self.fmt_open_if(e, indent) {
            return s;
        }
        if !block_trailing_call(e)
            && !forces_break(e)
            && !self.has_comments(e.span.start, e.span.end)
        {
            if let Some(s) = self.fmt_expr_inline(e, Mode::Layout) {
                if fits_at(indent_col(indent), &s) {
                    return s;
                }
            }
        }
        if let Some(s) = self.fmt_trailing(e, indent) {
            return s;
        }
        if matches!(e.node, Expr::Let(..)) {
            return format!("({})", self.fmt_expr(e, indent + 1, Mode::Flat));
        }
        self.fmt_expr_break(e, indent, Mode::Layout)
    }

    pub(super) fn fmt_let_line(
        &self,
        name: &str,
        value: &S<Expr>,
        indent: usize,
        from: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let head = format!("{ind}{} {name} = ", kw::LET);
        let breakable = !self.has_comments(from, value.span.end) && !forces_break(value);
        if breakable {
            if let Some(inline) = self.fmt_expr_inline(value, Mode::Layout) {
                if fits_at(text_width(&head), &inline) {
                    return format!("{head}{inline}");
                }
                let inner = INDENT.repeat(indent + 1);
                if fits_at(text_width(&inner), &inline) {
                    return format!("{ind}{} {name} =\n{inner}{inline}", kw::LET);
                }
            }
            // `try`/`catch` and `handle` have no mid-width form: the document
            // engine carries them as unbreakable flat text, so past the inline
            // width they lay out offside, matching their statement-position
            // rendering.
            if matches!(
                value.node,
                Expr::Handle(..) | Expr::Sugar(Sugar::TryCatch(..))
            ) {
                return format!(
                    "{ind}{} {name} =\n{}",
                    kw::LET,
                    self.fmt_block(value, indent + 1, from)
                );
            }
            if let Some(broken) = self.render_expr(value, text_width(&ind), text_width(&head)) {
                return format!("{head}{broken}");
            }
        }
        format!(
            "{ind}{} {name} =\n{}",
            kw::LET,
            self.fmt_block(value, indent + 1, from)
        )
    }

    // `let pat = value else fallback`: the binding line, then the value the
    // block takes when the pattern does not match. Both share the binding's
    // line when they fit; otherwise the fallback lays out offside under its own
    // `else`, the shape `transact` already uses for the same keyword.
    pub(super) fn fmt_let_else_line(
        &self,
        name: &str,
        value: &S<Expr>,
        fallback: &S<Expr>,
        indent: usize,
        from: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let head = self.fmt_let_line(name, value, indent, from);
        let breakable = !head.contains('\n')
            && !self.has_comments(value.span.end, fallback.span.end)
            && !forces_break(fallback);
        if breakable {
            if let Some(inline) = self.fmt_expr_inline(fallback, Mode::Layout) {
                let prefix = format!("{head} {} ", kw::ELSE);
                if fits_at(text_width(&prefix), &inline) {
                    return format!("{prefix}{inline}");
                }
            }
        }
        format!(
            "{head}\n{ind}{}\n{}",
            kw::ELSE,
            self.fmt_block(fallback, indent + 1, value.span.end)
        )
    }

    pub(super) fn fmt_transact_layout(
        &self,
        e: &S<Expr>,
        body: &S<Expr>,
        fallback: &S<Expr>,
        indent: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        format!(
            "{}\n{}\n{ind}{}\n{}",
            kw::TRANSACT,
            self.fmt_block(body, indent + 1, e.span.start),
            kw::ELSE,
            self.fmt_block(fallback, indent + 1, body.span.end)
        )
    }
}
