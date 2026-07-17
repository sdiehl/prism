use super::block::{arm_body, arm_head};
use super::breaks::{forces_break, wants_break};
use super::inline::as_compound_assign;
use super::pat::fmt_pat;
use super::{
    text_width, Arm, CatchArm, Expr, Fmt, HandlerArm, Mode, Qualifier, Sugar, INDENT, LINE_WIDTH, S,
};
use crate::kw;
use crate::syntax::ast::HandlerMode;

impl Fmt<'_> {
    pub(super) fn fmt_expr(&self, e: &S<Expr>, indent: usize, mode: Mode) -> String {
        if !wants_break(&e.node) {
            if let Some(s) = self.fmt_expr_inline(e, mode) {
                if indent * INDENT.len() + text_width(&s) <= LINE_WIDTH {
                    return s;
                }
            }
        }
        self.fmt_expr_break(e, indent, mode)
    }

    // Heads (if conditions, match scrutinees, handle bodies) sit before a layout
    // opener, so a multi-line head must be parenthesized to suppress layout.
    pub(super) fn fmt_head(&self, e: &S<Expr>, indent: usize) -> String {
        if !wants_break(&e.node) {
            if let Some(s) = self.fmt_expr_inline(e, Mode::Flat) {
                if indent * INDENT.len() + text_width(&s) + 16 <= LINE_WIDTH {
                    return s;
                }
            }
        }
        format!("({})", self.fmt_expr_break(e, indent + 1, Mode::Flat))
    }

    // `from` is the offset just past the arm's `=>`, so a comment on the line
    // below the arrow re-emits as the body's leading comment.
    pub(super) fn fmt_arm_body(
        &self,
        b: &S<Expr>,
        indent: usize,
        used: usize,
        from: usize,
    ) -> String {
        if !forces_break(b) && !self.has_comments(from, b.span.end) {
            if let Some(s) = self.fmt_expr_inline(b, Mode::Layout) {
                if used + 1 + text_width(&s) <= LINE_WIDTH {
                    return format!(" {s}");
                }
            }
        }
        format!("\n{}", self.fmt_block(b, indent + 1, from))
    }

    pub(super) fn fmt_guard(&self, a: &Arm, indent: usize) -> String {
        a.guard.as_ref().map_or_else(String::new, |g| {
            format!(
                " {} {}",
                kw::IF,
                self.fmt_expr_inline(g, Mode::Flat)
                    .unwrap_or_else(|| self.fmt_expr(g, indent, Mode::Flat))
            )
        })
    }

    pub(super) fn fmt_expr_break(&self, e: &S<Expr>, indent: usize, mode: Mode) -> String {
        match (&e.node, mode) {
            (Expr::Match(scrut, arms), Mode::Layout) => self.fmt_match_layout(scrut, arms, indent),
            (Expr::Match(s, arms), _) => self.fmt_match_flat(s, arms, indent, mode),
            (Expr::If(c, t, el), Mode::Layout) => self.fmt_if_layout(c, t, el, indent),
            (Expr::If(c, t, el), _) => self.fmt_if_flat(c, t, el, indent, mode),
            (Expr::Let(..), Mode::Layout) => {
                format!("({})", self.fmt_expr(e, indent + 1, Mode::Flat))
            }
            (Expr::Let(x, v, b), _) => self.fmt_let_break(x, v, b, indent, mode),
            (Expr::Pipe(x, f), _) => self
                .render_expr(e, indent * INDENT.len(), indent * INDENT.len())
                .unwrap_or_else(|| self.fmt_pipe_break(x, f, indent, mode)),
            // A flat call drops comments sitting between its arguments; when any
            // are present, reproduce the call from source so they survive.
            (Expr::Call(f, args), _) if self.has_comments(f.span.end, e.span.end) => {
                self.verbatim(e.span.start, e.span.end)
            }
            (Expr::Call(f, args), _) => self
                .render_expr(e, indent * INDENT.len(), indent * INDENT.len())
                .unwrap_or_else(|| self.fmt_call_flat(f, args, indent)),
            // Operator chains and collection literals break through the document
            // engine (one operand/element per line); the inline printer's flat
            // form is the fallback when a comment forces verbatim reprint.
            (Expr::Bin(..) | Expr::List(..) | Expr::Tuple(..), _) => self
                .render_expr(e, indent * INDENT.len(), indent * INDENT.len())
                .unwrap_or_else(|| {
                    self.fmt_expr_inline(e, Mode::Flat)
                        .unwrap_or_else(|| self.verbatim(e.span.start, e.span.end))
                }),
            (Expr::Handle(body, arms, HandlerMode::Partial), Mode::Layout) => {
                // The offside preprocessor opens a handler block directly after
                // `with`; the intervening `partial` marker therefore requires
                // explicit braces to remain parser-stable.
                self.fmt_handle_flat(body, arms, HandlerMode::Partial, indent, Mode::Layout)
            }
            (Expr::Handle(body, arms, handler_mode), Mode::Layout) => {
                self.fmt_handle_layout(body, arms, *handler_mode, indent)
            }
            (Expr::Sugar(Sugar::TryCatch(body, arms)), Mode::Layout) => {
                self.fmt_trycatch_layout(e, body, arms, indent)
            }
            (Expr::Sugar(Sugar::For(x, s, quals, body)), Mode::Layout) => {
                self.fmt_for_layout(x, s, quals, body, indent)
            }
            (Expr::Sugar(Sugar::Transact(body, fallback)), Mode::Layout) => {
                self.fmt_transact_layout(e, body, fallback, indent)
            }
            (Expr::Sugar(Sugar::Probe(name, body)), Mode::Layout) => format!(
                "{} {name:?} {}\n{}",
                kw::PROBE,
                kw::DO,
                self.fmt_block(body, indent + 1, body.span.start)
            ),
            (Expr::Sugar(Sugar::While(cond, body)), Mode::Layout) => {
                self.fmt_while_layout(cond.as_deref(), body, indent)
            }
            (Expr::Sugar(Sugar::VarDecl(..) | Sugar::NamedHandle(..)), _) => self
                .fmt_block(e, indent, e.span.start)
                .trim_start()
                .to_string(),
            (Expr::Sugar(Sugar::Assign(x, v)), _) => {
                if let Some((op, rhs)) = as_compound_assign(x, v) {
                    format!(
                        "{x} {}= {}",
                        op.spelling(),
                        self.fmt_expr(rhs, indent, Mode::Flat)
                    )
                } else {
                    format!(
                        "{x} {} {}",
                        kw::COLON_EQ,
                        self.fmt_expr(v, indent, Mode::Flat)
                    )
                }
            }
            (Expr::Handle(body, arms, handler_mode), _) => {
                self.fmt_handle_flat(body, arms, *handler_mode, indent, mode)
            }
            // A record literal too long for one line stacks one field per line,
            // brace-delimited (so layout is suppressed and it reparses), the
            // closing brace back at the record's own column.
            (Expr::RecordCreate(name, fields), _) => {
                self.fmt_record_break(name, None, fields, indent)
            }
            (Expr::RecordUpdate(base, name, fields), _) => {
                self.fmt_record_break(name, Some(base), fields, indent)
            }
            (Expr::RecordUpdatePath(base, ups), _) => {
                self.fmt_path_update_break(e, base, ups, indent)
            }
            _ => self
                .fmt_expr_inline(e, Mode::Flat)
                .unwrap_or_else(|| self.verbatim(e.span.start, e.span.end)),
        }
    }

    fn fmt_match_layout(&self, scrut: &S<Expr>, arms: &[Arm], indent: usize) -> String {
        let s = self.fmt_head(scrut, indent);
        // A comment above an arm sits between the previous arm's body and this
        // arm's pattern. The first arm's runs from the scrutinee end.
        let mut prev = scrut.span.end;
        let mut arm_strs: Vec<String> = Vec::with_capacity(arms.len());
        for a in arms {
            let lead = self.lead_comments(prev, a.pat.span.start, indent + 1);
            let head = format!(
                "{}{}{} {}",
                INDENT.repeat(indent + 1),
                fmt_pat(&a.pat, indent + 1),
                self.fmt_guard(a, indent + 1),
                kw::FAT_ARROW
            );
            let from = a.guard.as_ref().map_or(a.pat.span.end, |g| g.span.end);
            let body = self.fmt_arm_body(&a.body, indent + 1, text_width(&head), from);
            arm_strs.push(format!("{lead}{head}{body}"));
            prev = a.body.span.end;
        }
        format!("{} {s} {}\n{}", kw::MATCH, kw::OF, arm_strs.join("\n"))
    }

    fn fmt_match_flat(&self, s: &S<Expr>, arms: &[Arm], indent: usize, mode: Mode) -> String {
        let ind = INDENT.repeat(indent);
        let ind1 = INDENT.repeat(indent + 1);
        let s = self
            .fmt_expr_inline(s, mode)
            .unwrap_or_else(|| self.fmt_expr(s, indent, mode));
        let n = arms.len();
        let arm_strs: Vec<String> = arms
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let is_last = i + 1 == n;
                let trail = if is_last { "" } else { "," };
                let p = format!(
                    "{}{}",
                    fmt_pat(&a.pat, indent + 1),
                    self.fmt_guard(a, indent + 1)
                );
                let b_inline = self.fmt_expr_inline(&a.body, mode);
                if let Some(ref b) = b_inline {
                    let one_line = format!("{p} {} {b}", kw::FAT_ARROW);
                    if text_width(&ind1) + text_width(&one_line) + usize::from(!is_last)
                        <= LINE_WIDTH
                    {
                        return format!("{ind1}{one_line}{trail}");
                    }
                }
                let ind2 = INDENT.repeat(indent + 2);
                if let Some(ref b) = b_inline {
                    if text_width(&ind2) + text_width(b) + text_width(trail) <= LINE_WIDTH {
                        return format!("{ind1}{p} {}\n{ind2}{b}{trail}", kw::FAT_ARROW);
                    }
                }
                // Full break. The trailing comma stays on the closing token's line.
                let b_break = self.fmt_expr_break(&a.body, indent + 2, mode);
                format!("{ind1}{p} {}\n{ind2}{b_break}{trail}", kw::FAT_ARROW)
            })
            .collect();
        format!(
            "{} {s} {} {{\n{}\n{ind}}}",
            kw::MATCH,
            kw::OF,
            arm_strs.join("\n")
        )
    }

    fn fmt_if_layout(&self, c: &S<Expr>, t: &S<Expr>, el: &S<Expr>, indent: usize) -> String {
        let ind = INDENT.repeat(indent);
        let mut parts = vec![format!(
            "{} {} {}\n{}",
            kw::IF,
            self.fmt_head(c, indent),
            kw::THEN,
            self.fmt_block(t, indent + 1, c.span.end)
        )];
        // The `else` body's leading comments sit past the last `then` block.
        let mut last_then = t.span.end;
        let mut cur = el;
        while let Expr::If(c2, t2, e2) = &cur.node {
            parts.push(format!(
                "{ind}{} {} {}\n{}",
                kw::ELIF,
                self.fmt_head(c2, indent),
                kw::THEN,
                self.fmt_block(t2, indent + 1, c2.span.end)
            ));
            last_then = t2.span.end;
            cur = e2;
        }
        parts.push(format!(
            "{ind}{}\n{}",
            kw::ELSE,
            self.fmt_block(cur, indent + 1, last_then)
        ));
        parts.join("\n")
    }

    fn fmt_if_flat(
        &self,
        c: &S<Expr>,
        t: &S<Expr>,
        el: &S<Expr>,
        indent: usize,
        mode: Mode,
    ) -> String {
        let ind1 = INDENT.repeat(indent + 1);
        let c = self
            .fmt_expr_inline(c, mode)
            .unwrap_or_else(|| self.fmt_expr(c, indent, mode));
        let t = self.fmt_expr(t, indent + 1, mode);
        let el = self.fmt_expr(el, indent + 1, mode);
        format!(
            "{} {c}\n{ind1}{} {t}\n{ind1}{} {el}",
            kw::IF,
            kw::THEN,
            kw::ELSE
        )
    }

    fn fmt_let_break(
        &self,
        x: &str,
        v: &S<Expr>,
        b: &S<Expr>,
        indent: usize,
        mode: Mode,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let v = self.fmt_expr(v, indent, mode);
        let b = self.fmt_expr(b, indent, mode);
        format!("{} {x} = {v} {}\n{ind}{b}", kw::LET, kw::IN)
    }

    fn fmt_pipe_break(&self, x: &S<Expr>, f: &S<Expr>, indent: usize, mode: Mode) -> String {
        let ind = INDENT.repeat(indent);
        let x_s = if mode == Mode::Layout && matches!(x.node, Expr::Let(..)) {
            format!("({})", self.fmt_expr(x, indent + 1, Mode::Flat))
        } else {
            self.fmt_expr(x, indent, mode)
        };
        let f_s = self
            .fmt_expr_inline(f, Mode::Flat)
            .unwrap_or_else(|| self.fmt_expr(f, indent + 1, Mode::Flat));
        format!("{x_s}\n{ind}  {} {f_s}", kw::PIPE_RIGHT)
    }

    fn fmt_handle_layout(
        &self,
        body: &S<Expr>,
        arms: &[HandlerArm],
        handler_mode: HandlerMode,
        indent: usize,
    ) -> String {
        let body_s = self.fmt_head(body, indent);
        let marker = match handler_mode {
            HandlerMode::Exhaustive => "",
            HandlerMode::Partial => kw::PARTIAL,
        };
        format!(
            "{} {body_s} {}{}{}\n{}",
            kw::HANDLE,
            kw::WITH,
            if marker.is_empty() { "" } else { " " },
            marker,
            self.fmt_handler_arms(arms, indent + 1, body.span.end)
        )
    }

    fn fmt_trycatch_layout(
        &self,
        e: &S<Expr>,
        body: &S<Expr>,
        arms: &[CatchArm],
        indent: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let ind1 = INDENT.repeat(indent + 1);
        // A comment above a catch arm sits between the previous arm (or the try
        // body) and this arm. Each carries its own span.
        let mut prev = body.span.end;
        let mut arm_strs: Vec<String> = Vec::with_capacity(arms.len());
        for a in arms {
            let lead = self.lead_comments(prev, a.span.start, indent + 1);
            let head = if a.binders.is_empty() {
                format!("{ind1}{} {}", a.name, kw::FAT_ARROW)
            } else {
                format!(
                    "{ind1}{}({}) {}",
                    a.name,
                    a.binders.join(", "),
                    kw::FAT_ARROW
                )
            };
            let arm_body =
                self.fmt_arm_body(&a.body, indent + 1, text_width(&head), a.body.span.start);
            arm_strs.push(format!("{lead}{head}{arm_body}"));
            prev = a.body.span.end;
        }
        format!(
            "{}\n{}\n{ind}{}\n{}",
            kw::TRY,
            self.fmt_block(body, indent + 1, e.span.start),
            kw::CATCH,
            arm_strs.join("\n")
        )
    }

    fn fmt_for_layout(
        &self,
        x: &str,
        s: &S<Expr>,
        quals: &[Qualifier],
        body: &S<Expr>,
        indent: usize,
    ) -> String {
        // Each qualifier reads on its own line, indented under the source. `do`
        // closes the header and the body follows as an offside block.
        let s_s = self.fmt_head(s, indent);
        let qi = INDENT.repeat(indent + 2);
        let mut parts = vec![format!("{} {x} {} {s_s}", kw::FOR, kw::IN)];
        for q in quals {
            parts.push(format!("{qi}{}", self.fmt_qual(q, indent + 2)));
        }
        // The body's leading comments sit past the header (the last qualifier, or
        // the source when there are none).
        let from = quals.last().map_or(s.span.end, |q| match q {
            Qualifier::Guard(g) => g.span.end,
            Qualifier::Bind(_, e) => e.span.end,
        });
        format!(
            "{} {}\n{}",
            parts.join(",\n"),
            kw::DO,
            self.fmt_block(body, indent + 1, from)
        )
    }

    // `while cond do <block>` / `loop <block>`: the header closes (`do` for
    // `while`, nothing for `loop`) and the body follows as an offside block.
    fn fmt_while_layout(&self, cond: Option<&S<Expr>>, body: &S<Expr>, indent: usize) -> String {
        let (header, from) = cond.map_or_else(
            || (kw::LOOP.to_string(), body.span.start),
            |c| {
                (
                    format!("{} {} {}", kw::WHILE, self.fmt_head(c, indent), kw::DO),
                    c.span.end,
                )
            },
        );
        format!("{header}\n{}", self.fmt_block(body, indent + 1, from))
    }

    fn fmt_handle_flat(
        &self,
        body: &S<Expr>,
        arms: &[HandlerArm],
        handler_mode: HandlerMode,
        indent: usize,
        mode: Mode,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let ind1 = INDENT.repeat(indent + 1);
        let body_s = self.fmt_expr(body, indent, mode);
        let arm_strs: Vec<String> = arms
            .iter()
            .map(|arm| {
                format!(
                    "{} {}",
                    arm_head(arm, &ind1),
                    self.fmt_expr(arm_body(arm), indent + 1, mode)
                )
            })
            .collect();
        let marker = match handler_mode {
            HandlerMode::Exhaustive => "",
            HandlerMode::Partial => kw::PARTIAL,
        };
        format!(
            "{} {body_s} {}{}{} {{\n{}\n{ind}}}",
            kw::HANDLE,
            kw::WITH,
            if marker.is_empty() { "" } else { " " },
            marker,
            arm_strs.join(",\n")
        )
    }
}
