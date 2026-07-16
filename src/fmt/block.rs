use super::call::{
    call_shape, callee_parens, dot_parts, dot_recv_parens, is_with_call, paren_if, CallShape,
};
use super::pat::fmt_pat_inline;
use super::{
    text_width, Expr, Fmt, Grade, HandlerArm, Marker, Mode, Pattern, Sugar, SugarArm, INDENT, S,
};
use crate::kw;

// One offside statement and where the chain continues. `prev` is the byte offset
// the next statement's leading trivia begins at; `next` is the rest of the
// chain. `None` means `cur` is the block's trailing result expression.
struct BlockStep<'a> {
    rendered: String,
    prev: usize,
    next: &'a S<Expr>,
}

pub(super) const fn arm_body(arm: &HandlerArm) -> &S<Expr> {
    match arm {
        HandlerArm::Return(_, b)
        | HandlerArm::Op(_, _, _, b)
        | HandlerArm::Sugar(
            SugarArm::Once(_, _, b) | SugarArm::Never(_, _, b) | SugarArm::Val(_, b),
        ) => b,
    }
}

// A handler arm's head (everything up to and including the `=>`/`=`) at the
// given indent. The body is rendered separately, so both the flat and offside
// handler printers share one source of arm-head syntax.
pub(super) fn arm_head(arm: &HandlerArm, ind: &str) -> String {
    match arm {
        HandlerArm::Return(x, _) => format!("{ind}{} {x} {}", kw::RETURN, kw::FAT_ARROW),
        HandlerArm::Op(name, params, k, _) => {
            // The continuation prints after `resume`, in its visibly special
            // position, rather than as a trailing parameter.
            format!(
                "{ind}{}({}) {} {k} {}",
                name,
                params.join(", "),
                kw::RESUME,
                kw::FAT_ARROW
            )
        }
        HandlerArm::Sugar(SugarArm::Once(name, params, _)) => {
            format!(
                "{ind}{} {}({}) {}",
                Grade::Once.word(),
                name,
                params.join(", "),
                kw::FAT_ARROW
            )
        }
        HandlerArm::Sugar(SugarArm::Never(name, params, _)) => format!(
            "{ind}{} {}({}) {}",
            Grade::Never.word(),
            name,
            params.join(", "),
            kw::FAT_ARROW
        ),
        HandlerArm::Sugar(SugarArm::Val(x, _)) => format!("{ind}{} {x} =", kw::VAL),
    }
}

impl Fmt<'_> {
    pub(super) fn fmt_dot_recv(&self, recv: &S<Expr>, indent: usize) -> String {
        let s = self.fmt_expr(recv, indent, Mode::Flat);
        paren_if(dot_recv_parens(&recv.node), s)
    }

    // A call head in flat form: either `f(args)` or the restored `recv.f(rest)`.
    pub(super) fn fmt_call_flat(&self, f: &S<Expr>, args: &[S<Expr>], indent: usize) -> String {
        if let Some(s) = self.fmt_interp(f, args) {
            return s;
        }
        let flat_args = |xs: &[S<Expr>]| -> Vec<String> {
            xs.iter()
                .map(|a| self.fmt_expr(a, indent, Mode::Flat))
                .collect()
        };
        match call_shape(f, args) {
            CallShape::Recv(recv) => {
                format!("{}{}", self.fmt_dot_recv(recv, indent), kw::QUESTION)
            }
            CallShape::Dot((name, recv, rest)) => format!(
                "{}.{name}({})",
                self.fmt_dot_recv(recv, indent),
                flat_args(rest).join(", ")
            ),
            CallShape::Inst(inner, names, args) => {
                let inner_s = paren_if(
                    callee_parens(&inner.node),
                    self.fmt_expr(inner, indent, Mode::Flat),
                );
                let using = format!("{} {}", kw::USING, names.join(", "));
                if args.is_empty() {
                    format!("{inner_s}({using})")
                } else {
                    format!("{inner_s}({}, {using})", flat_args(args).join(", "))
                }
            }
            CallShape::Plain(f, args) => {
                let f_s = paren_if(callee_parens(&f.node), self.fmt_expr(f, indent, Mode::Flat));
                format!("{f_s}({})", flat_args(args).join(", "))
            }
        }
    }

    // One offside block: a let chain printed as indented statements. `from` is the
    // byte offset of the block opener, so comments between it and the first
    // statement (and between any two statements) re-emit at the block's indent.
    pub(super) fn fmt_block(&self, e: &S<Expr>, indent: usize, from: usize) -> String {
        let mut lines: Vec<String> = Vec::new();
        let mut prev = from;
        let mut cur = e;
        // Each statement re-emits with the comments recorded since the previous one
        // ended. Every continuation begins at `cur.span.start`, so trivia placement
        // is uniform and lives only here; the stepper renders the bare statement.
        while let Some(step) = self.block_step(cur, indent) {
            let lead = self.lead_comments(prev, cur.span.start, indent);
            let single_line = !step.rendered.contains('\n');
            let mut rendered = if lead.is_empty() {
                step.rendered
            } else {
                format!("{lead}{}", step.rendered)
            };
            prev = step.prev;
            // Keep a same-line trailing comment on the statement it follows rather
            // than relocating it onto its own line above the next statement.
            if single_line {
                if let Some((text, end)) = self.trailing_comment(prev) {
                    rendered.push_str("  ");
                    rendered.push_str(text);
                    prev = end;
                }
            }
            lines.push(rendered);
            cur = step.next;
            // The sentinel marks an ill-formed trailing `with`. Nothing follows.
            if matches!(&cur.node, Expr::Marker(Marker::With)) {
                return lines.join("\n");
            }
        }
        let lead = self.lead_comments(prev, cur.span.start, indent);
        let tail = format!("{}{}", INDENT.repeat(indent), self.fmt_stmt(cur, indent));
        lines.push(if lead.is_empty() {
            tail
        } else {
            format!("{lead}{tail}")
        });
        lines.join("\n")
    }

    fn block_step<'a>(&self, cur: &'a S<Expr>, indent: usize) -> Option<BlockStep<'a>> {
        let ind = INDENT.repeat(indent);
        let last_arm_end = |body: &'a S<Expr>, arms: &'a [HandlerArm]| {
            arms.last()
                .map_or(body.span.start, |a| arm_body(a).span.end)
        };
        let (rendered, prev, next) = match &cur.node {
            Expr::Let(x, v, b) => {
                let s = if x == "_" {
                    format!("{ind}{}", self.fmt_stmt(v, indent))
                } else {
                    self.fmt_let_line(x, v, indent, cur.span.start)
                };
                (s, v.span.end, b.as_ref())
            }
            Expr::Sugar(Sugar::VarDecl(x, v, b)) => (
                format!(
                    "{ind}{} {x} {} {}",
                    kw::VAR,
                    kw::COLON_EQ,
                    self.fmt_expr(v, indent, Mode::Flat)
                ),
                v.span.end,
                b.as_ref(),
            ),
            Expr::Call(f, args) if is_with_call(args) => {
                let (last, init) = args.split_last()?;
                let Expr::Lam(ps, body) = &last.node else {
                    return None;
                };
                let head = self.fmt_call_flat(f, init, indent);
                let bind = ps
                    .first()
                    .map_or(String::new(), |p| format!("{} {} ", p.name, kw::LARROW));
                (
                    format!("{ind}{} {bind}{head}", kw::WITH),
                    body.span.start,
                    body.as_ref(),
                )
            }
            Expr::Handle(body, arms, _) if cur.synth => (
                format!(
                    "{ind}{} {}\n{}",
                    kw::WITH,
                    kw::HANDLER,
                    self.fmt_handler_arms(arms, indent + 1, cur.span.start)
                ),
                last_arm_end(body, arms),
                body.as_ref(),
            ),
            Expr::Sugar(Sugar::NamedHandle(f, body, arms)) => (
                format!(
                    "{ind}{} {f} {} {}\n{}",
                    kw::WITH,
                    kw::LARROW,
                    kw::HANDLER,
                    self.fmt_handler_arms(arms, indent + 1, cur.span.start)
                ),
                last_arm_end(body, arms),
                body.as_ref(),
            ),
            // Pattern lets and `?` statements desugar to matches carrying the
            // synthetic marker. One arm restores `let pat =`, two restore `?`.
            Expr::Match(s, arms) if cur.synth && arms.len() == 1 => (
                self.fmt_let_line(&fmt_pat_inline(&arms[0].pat), s, indent, cur.span.start),
                arms[0].body.span.start,
                &arms[0].body,
            ),
            Expr::Match(s, arms) if cur.synth && arms.len() == 2 => {
                let v = self.fmt_expr(s, indent, Mode::Flat);
                let binder = match &arms[0].pat.node {
                    Pattern::Ctor(_, subs) => match subs.first().map(|p| &p.node) {
                        Some(Pattern::Var(x)) => Some(x.clone()),
                        _ => None,
                    },
                    _ => None,
                };
                let s = binder.map_or_else(
                    || format!("{ind}{v}{}", kw::QUESTION),
                    |x| format!("{ind}{} {x} = {v}{}", kw::LET, kw::QUESTION),
                );
                (s, arms[0].body.span.start, &arms[0].body)
            }
            _ => return None,
        };
        Some(BlockStep {
            rendered,
            prev,
            next,
        })
    }

    // A call whose last argument is a lambda prints as a trailing block:
    // `f(args) fn(x)` followed by the body as an offside block.
    pub(super) fn fmt_trailing(&self, e: &S<Expr>, indent: usize) -> Option<String> {
        let Expr::Call(f, args) = &e.node else {
            return None;
        };
        let (last, init) = args.split_last()?;
        let Expr::Lam(ps, body) = &last.node else {
            return None;
        };
        // A dot call whose only argument is the block keeps the parenless shape.
        let head = match dot_parts(f, init) {
            Some((name, recv, [])) => format!("{}.{name}", self.fmt_dot_recv(recv, indent)),
            _ => self.fmt_call_flat(f, init, indent),
        };
        let params = if ps.is_empty() {
            String::new()
        } else {
            let ps: Vec<String> = ps.iter().map(|p| self.fmt_param(p)).collect();
            format!("({})", ps.join(", "))
        };
        Some(format!(
            "{head} {}{params}\n{}",
            kw::FN,
            self.fmt_block(body, indent + 1, last.span.start)
        ))
    }

    // An `if`/`elif` chain whose final branch is `()` prints in statement
    // position without the `else`, the open form it parsed from.
    pub(super) fn fmt_open_if(&self, e: &S<Expr>, indent: usize) -> Option<String> {
        let mut arms = Vec::new();
        let mut cur = e;
        while let Expr::If(c, t, el) = &cur.node {
            arms.push((c, t));
            cur = el;
        }
        if arms.is_empty() || !matches!(cur.node, Expr::Unit) {
            return None;
        }
        let key = |i: usize| if i == 0 { kw::IF } else { kw::ELIF };
        let ind = INDENT.repeat(indent);
        let parts: Vec<String> = arms
            .iter()
            .enumerate()
            .map(|(i, (c, t))| {
                let lead = if i == 0 { String::new() } else { ind.clone() };
                format!(
                    "{lead}{} {} {}\n{}",
                    key(i),
                    self.fmt_head(c, indent),
                    kw::THEN,
                    self.fmt_block(t, indent + 1, c.span.end)
                )
            })
            .collect();
        Some(parts.join("\n"))
    }

    pub(super) fn fmt_handler_arms(
        &self,
        arms: &[HandlerArm],
        indent: usize,
        from: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        // Handler arms carry no head span, so a comment above an arm is recovered
        // from the gap between the previous arm's body and this arm's body. The
        // first arm reaches back to the block opener.
        let mut prev = from;
        let mut arm_strs: Vec<String> = Vec::with_capacity(arms.len());
        for arm in arms {
            let body = arm_body(arm);
            let head = arm_head(arm, &ind);
            let lead = self.lead_comments(prev, body.span.start, indent);
            let rendered = format!(
                "{head}{}",
                self.fmt_arm_body(body, indent, text_width(&head), body.span.start)
            );
            arm_strs.push(format!("{lead}{rendered}"));
            prev = body.span.end;
        }
        arm_strs.join("\n")
    }
}
