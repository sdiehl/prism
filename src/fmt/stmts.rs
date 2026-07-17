use super::breaks::{block_trailing_call, forces_break};
use super::{text_width, Expr, Fmt, Mode, Sugar, INDENT, LINE_WIDTH, S};
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
                if indent * INDENT.len() + text_width(&s) <= LINE_WIDTH {
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
                if text_width(&head) + text_width(&inline) <= LINE_WIDTH {
                    return format!("{head}{inline}");
                }
                let inner = INDENT.repeat(indent + 1);
                if text_width(&inner) + text_width(&inline) <= LINE_WIDTH {
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
