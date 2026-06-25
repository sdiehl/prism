use marginalia::{BuiltinKind, Trivia, TriviaTable};

use crate::error::Error;
use crate::kw;
use crate::parse::{parse, ParseResult};
use crate::syntax::ast::{
    Arm, CatchArm, Expr, HandlerArm, Marker, Pattern, Program, Qualifier, Sugar, SugarArm, Surface,
    S,
};

mod decl;
mod ops;
mod pat;
use decl::{fmt_class, fmt_data, fmt_effect, fmt_import, fmt_labels, fmt_ty};
use ops::{binop_prec, low_prec_operand, needs_left_paren, needs_right_paren};
use pat::{fmt_pat, fmt_pat_inline};

const INDENT: &str = "  ";
const LINE_WIDTH: usize = 80;

// Layout mode prints offside blocks. Flat is for bracketed contexts where
// virtual layout tokens are suppressed, so only inline let/braced arms parse.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Layout,
    Flat,
}

// The formatter's read-only context, threaded through every printer instead of
// living in thread-local state: the original source (for the verbatim fallback,
// since a formatter must never destroy code) and the comment/blank-line trivia
// (so the offside-block printers can re-emit trivia inside a function body, not
// just between declarations). Borrowing both keeps formatting reentrant and
// leaves no state to clear, so a panic mid-format cannot poison the next run.
pub(super) struct Fmt<'a> {
    source: &'a str,
    trivia: &'a TriviaTable,
}

/// # Errors
/// Fails when the source does not parse.
pub fn format(src: &str) -> Result<String, Error> {
    let ParseResult { program, trivia } = parse(src)?;
    let cx = Fmt {
        source: src,
        trivia: &trivia,
    };
    Ok(cx.fmt_program(&program))
}

/// # Errors
/// Fails when the source does not parse.
pub fn format_check(src: &str) -> Result<bool, Error> {
    let formatted = format(src)?;
    Ok(formatted == src)
}

const fn is_with_call(args: &[S<Expr>]) -> bool {
    matches!(args.last(), Some(a) if matches!(a.node, Expr::Lam(..)) && a.synth)
}

// A `Marker::Try` call head restores `e?`: the receiver is its single argument.
fn try_recv<'a>(f: &S<Expr>, args: &'a [S<Expr>]) -> Option<&'a S<Expr>> {
    match (&f.node, args) {
        (Expr::Marker(Marker::Try), [recv]) => Some(recv),
        _ => None,
    }
}

// UFCS dot calls carry the synthetic-span marker on the callee var. That is
// how the formatter restores `recv.f(args)` instead of `f(recv, args)`.
type DotCall<'a> = (&'a str, &'a S<Expr>, &'a [S<Expr>]);

fn dot_parts<'a>(f: &'a S<Expr>, args: &'a [S<Expr>]) -> Option<DotCall<'a>> {
    match &f.node {
        Expr::Var(name) if f.synth && !args.is_empty() => Some((name, &args[0], &args[1..])),
        _ => None,
    }
}

// A dot receiver must stay postfix-tight. Anything looser is parenthesized.
const fn dot_recv_parens(e: &Expr) -> bool {
    low_prec_operand(e)
        || matches!(
            e,
            Expr::Bin(..) | Expr::Handle(..) | Expr::Sugar(Sugar::Assign(..))
        )
}

// `(b.f)(1)` calls the field closure. Bare `b.f(1)` reparses as UFCS f(b, 1).
const fn callee_parens(e: &Expr) -> bool {
    low_prec_operand(e) || matches!(e, Expr::Handle(..) | Expr::FieldAccess(..))
}

// In statement position, `match` and `if` always lay out across lines, even
// when they would fit on one: their arms and branches read better stacked, the
// way other languages write them. Synth matches (pattern-let / `?` desugar) are
// excluded. The block printer restores those surfaces inline.
const fn forces_break(e: &S<Expr>) -> bool {
    matches!(
        e.node,
        Expr::Match(..) | Expr::If(..) | Expr::Sugar(Sugar::For(..))
    ) && !e.synth
}

// A call whose last argument is a lambda with a statement-shaped body: a
// sequence/binding (`Let`), a handler/match/if, or imperative sugar (`var`,
// `:=`, `throw`, `try`, `for`, `transact`, named `with`). Such a body reads
// better as the offside `f() fn(x)` block. A lambda whose body is a single
// value expression is left to print inline as `f(\x -> e)`.
fn block_trailing_call(e: &S<Expr>) -> bool {
    let Expr::Call(_, args) = &e.node else {
        return false;
    };
    let Some(Expr::Lam(_, body)) = args.last().map(|a| &a.node) else {
        return false;
    };
    matches!(
        body.node,
        Expr::Let(..)
            | Expr::Handle(..)
            | Expr::Match(..)
            | Expr::If(..)
            | Expr::Sugar(
                Sugar::VarDecl(..)
                    | Sugar::Assign(..)
                    | Sugar::Throw(..)
                    | Sugar::TryCatch(..)
                    | Sugar::For(..)
                    | Sugar::Transact(..)
                    | Sugar::NamedHandle(..)
            )
    )
}

fn fmt_float(f: f64) -> String {
    let s = format!("{f}");
    if f.is_finite() && !s.contains(['.', 'e', 'E']) {
        format!("{s}.0")
    } else {
        s
    }
}

fn fmt_char(c: char) -> String {
    let inner = match c {
        '\\' => "\\\\".into(),
        '\'' => "\\'".into(),
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        '\r' => "\\r".into(),
        c => c.to_string(),
    };
    format!("'{inner}'")
}

fn escape_str(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            c => out.push(c),
        }
    }
    out
}

// One offside statement and where the chain continues. `prev` is the byte offset
// the next statement's leading trivia begins at; `next` is the rest of the
// chain. `None` means `cur` is the block's trailing result expression.
struct BlockStep<'a> {
    rendered: String,
    prev: usize,
    next: &'a S<Expr>,
}

const fn arm_body(arm: &HandlerArm) -> &S<Expr> {
    match arm {
        HandlerArm::Return(_, b)
        | HandlerArm::Op(_, _, _, b)
        | HandlerArm::Sugar(
            SugarArm::Fun(_, _, b) | SugarArm::Final(_, _, b) | SugarArm::Val(_, b),
        ) => b,
    }
}

impl Fmt<'_> {
    fn verbatim(&self, start: usize, end: usize) -> String {
        self.source.get(start..end).unwrap_or_default().to_string()
    }

    // Line comments in `[lo, hi)`, each re-emitted on its own line at the given
    // indent and newline-terminated. A blank line between two comments is kept so
    // deliberately spaced comment groups survive; leading and trailing blanks are
    // dropped. Block comments carry no placeable layout, so they are skipped (the
    // same policy `emit_leading_trivia` uses at top level).
    fn lead_comments(&self, lo: usize, hi: usize, indent: usize) -> String {
        if lo >= hi {
            return String::new();
        }
        let ind = INDENT.repeat(indent);
        let mut out = String::new();
        let mut gap = false;
        for ev in self.trivia.between(lo, hi) {
            match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => {
                    if gap && !out.is_empty() {
                        out.push('\n');
                    }
                    gap = false;
                    out.push_str(&ind);
                    out.push_str(text);
                    out.push('\n');
                }
                Trivia::Comment { .. } => {}
                Trivia::BlankLine => gap = true,
            }
        }
        out
    }

    // Whether any line comment sits in `[lo, hi)`. The inline fast paths check
    // this before collapsing a node onto one line: a node carrying comments must
    // take the laid-out path so `lead_comments` has somewhere to place them.
    fn has_comments(&self, lo: usize, hi: usize) -> bool {
        lo < hi
            && self.trivia.between(lo, hi).any(|e| {
                matches!(
                    &e.trivia,
                    Trivia::Comment {
                        kind: BuiltinKind::Line,
                        ..
                    }
                )
            })
    }

    fn emit_leading_trivia(&self, lo: usize, hi: usize, out: &mut String) {
        for ev in self.trivia.between(lo, hi) {
            match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => {
                    out.push_str(text);
                    out.push('\n');
                }
                Trivia::Comment { .. } => {}
                Trivia::BlankLine => {
                    if !out.is_empty() {
                        out.push('\n');
                    }
                }
            }
        }
    }

    fn fmt_program(&self, prog: &Program) -> String {
        let mut items: Vec<(usize, usize, String)> = Vec::new();
        // Restore the visibility marker the parser stripped into `prog.exports` /
        // `prog.opaques` (opaque implies exported, so it is checked first).
        let pubd = |name: &str, s: String| {
            if prog.opaques.contains(name) {
                format!("{} {s}", kw::OPAQUE)
            } else if prog.exports.contains(name) {
                format!("{} {s}", kw::PUB)
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
        for i in &prog.instances {
            items.push((i.span.start, i.span.end, self.fmt_instance(i)));
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
        items.sort_by_key(|(start, _, _)| *start);

        let mut out = String::new();
        let mut prev_end: usize = 0;
        for (idx, (start, end, s)) in items.into_iter().enumerate() {
            let boundary = out.len();
            self.emit_leading_trivia(prev_end, start, &mut out);
            // Top-level declarations are always separated by a blank line. The
            // leading trivia already opens the gap with one when the source had it;
            // otherwise insert one ahead of any attached doc comment so the comment
            // stays with its declaration.
            if idx > 0 && !out[boundary..].starts_with('\n') {
                out.insert(boundary, '\n');
            }
            out.push_str(&s);
            out.push('\n');
            prev_end = end;
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

    fn fmt_dot_recv(&self, recv: &S<Expr>, indent: usize) -> String {
        let s = self.fmt_expr(recv, indent, Mode::Flat);
        if dot_recv_parens(&recv.node) {
            format!("({s})")
        } else {
            s
        }
    }

    // A call head in flat form: either `f(args)` or the restored `recv.f(rest)`.
    fn fmt_call_flat(&self, f: &S<Expr>, args: &[S<Expr>], indent: usize) -> String {
        if let Some(s) = self.fmt_interp(f, args) {
            return s;
        }
        if let Some(recv) = try_recv(f, args) {
            return format!("{}{}", self.fmt_dot_recv(recv, indent), kw::QUESTION);
        }
        if let Some((name, recv, rest)) = dot_parts(f, args) {
            let rest_s: Vec<String> = rest
                .iter()
                .map(|a| self.fmt_expr(a, indent, Mode::Flat))
                .collect();
            return format!(
                "{}.{name}({})",
                self.fmt_dot_recv(recv, indent),
                rest_s.join(", ")
            );
        }
        let f_s = self.fmt_expr(f, indent, Mode::Flat);
        let f_s = if callee_parens(&f.node) {
            format!("({f_s})")
        } else {
            f_s
        };
        let args_s: Vec<String> = args
            .iter()
            .map(|a| self.fmt_expr(a, indent, Mode::Flat))
            .collect();
        format!("{f_s}({})", args_s.join(", "))
    }

    // One offside block: a let chain printed as indented statements. `from` is the
    // byte offset of the block opener, so comments between it and the first
    // statement (and between any two statements) re-emit at the block's indent.
    fn fmt_block(&self, e: &S<Expr>, indent: usize, from: usize) -> String {
        let mut lines: Vec<String> = Vec::new();
        let mut prev = from;
        let mut cur = e;
        // Each statement re-emits with the comments recorded since the previous one
        // ended. Every continuation begins at `cur.span.start`, so trivia placement
        // is uniform and lives only here; the stepper renders the bare statement.
        while let Some(step) = self.block_step(cur, indent) {
            let lead = self.lead_comments(prev, cur.span.start, indent);
            lines.push(if lead.is_empty() {
                step.rendered
            } else {
                format!("{lead}{}", step.rendered)
            });
            prev = step.prev;
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
            Expr::Handle(body, arms) if cur.synth => (
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
    fn fmt_trailing(&self, e: &S<Expr>, indent: usize) -> Option<String> {
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
    fn fmt_open_if(&self, e: &S<Expr>, indent: usize) -> Option<String> {
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

    fn fmt_stmt(&self, e: &S<Expr>, indent: usize) -> String {
        if let Some(s) = self.fmt_open_if(e, indent) {
            return s;
        }
        // A trailing-lambda call with a simple body prints inline as `f(\x -> e)`;
        // one with a statement-shaped body keeps the offside `f() fn(x)` block.
        if !block_trailing_call(e)
            && !forces_break(e)
            && !self.has_comments(e.span.start, e.span.end)
        {
            if let Some(s) = self.fmt_expr_inline(e, Mode::Layout) {
                if indent * INDENT.len() + s.len() <= LINE_WIDTH {
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

    fn fmt_let_line(&self, x: &str, v: &S<Expr>, indent: usize, from: usize) -> String {
        let ind = INDENT.repeat(indent);
        if !self.has_comments(from, v.span.end) && !forces_break(v) {
            if let Some(s) = self.fmt_expr_inline(v, Mode::Layout) {
                let line = format!("{ind}{} {x} = {s}", kw::LET);
                if line.len() <= LINE_WIDTH {
                    return line;
                }
            }
        }
        format!(
            "{ind}{} {x} =\n{}",
            kw::LET,
            self.fmt_block(v, indent + 1, from)
        )
    }

    fn fmt_expr(&self, e: &S<Expr>, indent: usize, mode: Mode) -> String {
        if let Some(s) = self.fmt_expr_inline(e, mode) {
            if indent * INDENT.len() + s.len() <= LINE_WIDTH {
                return s;
            }
        }
        self.fmt_expr_break(e, indent, mode)
    }

    // `Interp` marker calls round-trip back to the literal: even args are segments,
    // odd args are holes printed inline between braces.
    fn fmt_interp(&self, f: &S<Expr>, args: &[S<Expr>]) -> Option<String> {
        if !matches!(&f.node, Expr::Marker(Marker::Interp)) {
            return None;
        }
        let mut out = String::from("\"");
        for (i, a) in args.iter().enumerate() {
            if i % 2 == 0 {
                let Expr::Str(s) = &a.node else {
                    return None;
                };
                out.push_str(&escape_str(s));
            } else {
                let h = self.fmt_expr_inline(a, Mode::Flat).unwrap_or_else(|| {
                    self.fmt_expr_break(a, 0, Mode::Flat)
                        .split_whitespace()
                        .collect::<Vec<_>>()
                        .join(" ")
                });
                out.push('{');
                out.push_str(&h);
                out.push('}');
            }
        }
        out.push('"');
        Some(out)
    }

    fn fmt_expr_inline(&self, e: &S<Expr>, mode: Mode) -> Option<String> {
        match &e.node {
            Expr::Int(n) => Some(n.to_string()),
            Expr::Float(f) => Some(fmt_float(*f)),
            Expr::Char(c) => Some(fmt_char(*c)),
            Expr::Bool(b) => Some(b.to_string()),
            Expr::Unit => Some("()".into()),
            Expr::Str(s) => Some(format!("\"{}\"", escape_str(s))),
            Expr::Var(x) => Some(x.clone()),
            Expr::Tuple(elems) => {
                let parts: Option<Vec<_>> = elems
                    .iter()
                    .map(|x| self.fmt_expr_inline(x, Mode::Flat))
                    .collect();
                parts.map(|p| format!("({})", p.join(", ")))
            }
            Expr::List(elems) if elems.is_empty() => Some("[]".into()),
            Expr::List(elems) => {
                let parts: Option<Vec<_>> = elems
                    .iter()
                    .map(|x| self.fmt_expr_inline(x, Mode::Flat))
                    .collect();
                parts.map(|p| format!("[{}]", p.join(", ")))
            }
            Expr::Bin(op, a, b) => {
                let p = binop_prec(*op);
                let a_paren = needs_left_paren(&a.node, *op, p);
                let b_paren = needs_right_paren(&b.node, *op, p);
                let a_s = self.fmt_expr_inline(a, if a_paren { Mode::Flat } else { mode })?;
                let b_s = self.fmt_expr_inline(b, if b_paren { Mode::Flat } else { mode })?;
                let a_s = if a_paren { format!("({a_s})") } else { a_s };
                let b_s = if b_paren { format!("({b_s})") } else { b_s };
                Some(format!("{a_s} {} {b_s}", op.spelling()))
            }
            Expr::If(..) => {
                let mut parts = Vec::new();
                let mut cur = e;
                while let Expr::If(c, t, el) = &cur.node {
                    let key = if parts.is_empty() { kw::IF } else { kw::ELIF };
                    let c = self.fmt_expr_inline(c, mode)?;
                    let t = self.fmt_expr_inline(t, mode)?;
                    parts.push(format!("{key} {c} {} {t}", kw::THEN));
                    cur = el;
                }
                parts.push(format!("{} {}", kw::ELSE, self.fmt_expr_inline(cur, mode)?));
                Some(parts.join(" "))
            }
            Expr::Call(f, args) => {
                if let Some(s) = self.fmt_interp(f, args) {
                    return Some(s);
                }
                if is_with_call(args) {
                    return None;
                }
                if let Some(recv) = try_recv(f, args) {
                    let recv_s = self.fmt_expr_inline(recv, Mode::Flat)?;
                    let recv_s = if dot_recv_parens(&recv.node) {
                        format!("({recv_s})")
                    } else {
                        recv_s
                    };
                    return Some(format!("{recv_s}{}", kw::QUESTION));
                }
                if let Some((name, recv, rest)) = dot_parts(f, args) {
                    let recv_s = self.fmt_expr_inline(recv, Mode::Flat)?;
                    let recv_s = if dot_recv_parens(&recv.node) {
                        format!("({recv_s})")
                    } else {
                        recv_s
                    };
                    let rest_s: Option<Vec<_>> = rest
                        .iter()
                        .map(|a| self.fmt_expr_inline(a, Mode::Flat))
                        .collect();
                    return rest_s.map(|a| format!("{recv_s}.{name}({})", a.join(", ")));
                }
                let f_s = self.fmt_expr_inline(f, mode)?;
                let f_s = if callee_parens(&f.node) {
                    format!("({f_s})")
                } else {
                    f_s
                };
                let args: Option<Vec<_>> = args
                    .iter()
                    .map(|a| self.fmt_expr_inline(a, Mode::Flat))
                    .collect();
                args.map(|a| format!("{f_s}({})", a.join(", ")))
            }
            Expr::Pipe(x, f) => {
                let x_s = self.fmt_expr_inline(x, mode)?;
                let f_s = self.fmt_expr_inline(f, mode)?;
                Some(format!("{x_s} {} {f_s}", kw::PIPE_RIGHT))
            }
            Expr::Let(x, v, b) => {
                if mode == Mode::Layout {
                    return None;
                }
                let v = self.fmt_expr_inline(v, mode)?;
                let b = self.fmt_expr_inline(b, mode)?;
                Some(format!("{} {x} = {v} {} {b}", kw::LET, kw::IN))
            }
            Expr::Lam(ps, body) => {
                if e.synth {
                    return None;
                }
                let ps: Vec<_> = ps.iter().map(|p| self.fmt_param(p)).collect();
                let body = self.fmt_expr_inline(body, Mode::Flat)?;
                Some(format!(
                    "{}({}) {} {body}",
                    kw::LAMBDA,
                    ps.join(", "),
                    kw::ARROW
                ))
            }
            Expr::Match(s, arms) => {
                // The sugar marker flags pattern-let and `?` desugars. Only the
                // block printer can restore those surfaces.
                if e.synth {
                    return None;
                }
                let s = self.fmt_expr_inline(s, mode)?;
                let arm_strs: Option<Vec<_>> = arms
                    .iter()
                    .map(|a| {
                        let p = fmt_pat_inline(&a.pat);
                        let g = match &a.guard {
                            Some(g) => format!(" {} {}", kw::IF, self.fmt_expr_inline(g, mode)?),
                            None => String::new(),
                        };
                        let b = self.fmt_expr_inline(&a.body, mode)?;
                        Some(format!("{p}{g} {} {b}", kw::FAT_ARROW))
                    })
                    .collect();
                arm_strs.map(|a| format!("{} {s} {} {{ {} }}", kw::MATCH, kw::OF, a.join(", ")))
            }
            Expr::FieldAccess(e, field) => {
                let e_s = self.fmt_expr_inline(e, mode)?;
                Some(format!("{e_s}.{field}"))
            }
            Expr::RecordCreate(name, fields) => {
                let fs: Option<Vec<_>> = fields
                    .iter()
                    .map(|(f, e)| {
                        self.fmt_expr_inline(e, Mode::Flat)
                            .map(|e_s| format!("{f} = {e_s}"))
                    })
                    .collect();
                fs.map(|fs| format!("{name} {{ {} }}", fs.join(", ")))
            }
            Expr::RecordUpdate(base, name, fields) => {
                let base_s = self.fmt_expr_inline(base, Mode::Flat)?;
                let fs: Option<Vec<_>> = fields
                    .iter()
                    .map(|(f, e)| {
                        self.fmt_expr_inline(e, Mode::Flat)
                            .map(|e_s| format!("{f} = {e_s}"))
                    })
                    .collect();
                fs.map(|fs| format!("{name} {{ ..{base_s}, {} }}", fs.join(", ")))
            }
            Expr::RecordUpdatePath(base, ups) => {
                let base_s = self.fmt_expr_inline(base, Mode::Flat)?;
                let us: Option<Vec<_>> = ups
                    .iter()
                    .map(|(p, e)| {
                        self.fmt_expr_inline(e, Mode::Flat)
                            .map(|e_s| format!("{} = {e_s}", p.join(".")))
                    })
                    .collect();
                us.map(|us| format!("{{ {base_s} | {} }}", us.join(", ")))
            }
            Expr::Inst(f, names) => {
                let f_s = self.fmt_expr_inline(f, mode)?;
                Some(format!("{f_s}[{}]", names.join(", ")))
            }
            Expr::Ann(inner, ty) => {
                let s = self.fmt_expr_inline(inner, Mode::Flat)?;
                Some(format!("({s} : {})", fmt_ty(ty)))
            }
            Expr::Mask(eff, body) => {
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                Some(format!("{}<{eff}>({b})", kw::MASK))
            }
            Expr::Sugar(s) => self.fmt_sugar_inline(s, mode),
            // A bare marker has no inline surface of its own: `Try`/`Interp` render
            // through their enclosing call (handled above), and `With` is the
            // trailing-`with` sentinel restored by the block printer.
            Expr::Handle(..) | Expr::Marker(_) => None,
        }
    }

    fn fmt_sugar_inline(&self, s: &Sugar<Surface>, mode: Mode) -> Option<String> {
        match s {
            Sugar::Default(a, b) => {
                let a_s = self.fmt_expr_inline(a, mode)?;
                let b_s = self.fmt_expr_inline(b, mode)?;
                Some(format!("{a_s} {} {b_s}", kw::QUESTION_QUESTION))
            }
            Sugar::Compose(forward, f, g) => {
                let f_s = self.fmt_expr_inline(f, mode)?;
                let g_s = self.fmt_expr_inline(g, mode)?;
                let op = if *forward {
                    kw::COMP_RIGHT
                } else {
                    kw::COMP_LEFT
                };
                Some(format!("{f_s} {op} {g_s}"))
            }
            Sugar::OptChain(e, field) => {
                let e_s = self.fmt_expr_inline(e, mode)?;
                Some(format!("{e_s}{}{field}", kw::QUESTION_DOT))
            }
            Sugar::Assign(x, v) => {
                let v_s = self.fmt_expr_inline(v, mode)?;
                Some(format!("{x} {} {v_s}", kw::COLON_EQ))
            }
            Sugar::Throw(name, args) => {
                if args.is_empty() {
                    return Some(format!("{} {name}", kw::THROW));
                }
                let parts: Option<Vec<_>> = args
                    .iter()
                    .map(|x| self.fmt_expr_inline(x, Mode::Flat))
                    .collect();
                parts.map(|p| format!("{} {name}({})", kw::THROW, p.join(", ")))
            }
            Sugar::TryCatch(body, arms) => {
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                let parts: Option<Vec<_>> = arms
                    .iter()
                    .map(|a| {
                        self.fmt_expr_inline(&a.body, Mode::Flat).map(|s| {
                            if a.binders.is_empty() {
                                format!("{} {} {s}", a.name, kw::FAT_ARROW)
                            } else {
                                format!(
                                    "{}({}) {} {s}",
                                    a.name,
                                    a.binders.join(", "),
                                    kw::FAT_ARROW
                                )
                            }
                        })
                    })
                    .collect();
                parts.map(|p| format!("{} {b} {} {{ {} }}", kw::TRY, kw::CATCH, p.join(", ")))
            }
            Sugar::For(x, s, quals, body) => {
                let s_s = self.fmt_expr_inline(s, Mode::Flat)?;
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                Some(format!(
                    "{} {x} {} {s_s}{} {} {b}",
                    kw::FOR,
                    kw::IN,
                    self.fmt_quals(quals)?,
                    kw::DO
                ))
            }
            Sugar::Comp(head, x, s, quals) => {
                let h = self.fmt_expr_inline(head, Mode::Flat)?;
                let s_s = self.fmt_expr_inline(s, Mode::Flat)?;
                Some(format!(
                    "[{h} {} {x} {} {s_s}{}]",
                    kw::FOR,
                    kw::IN,
                    self.fmt_quals(quals)?
                ))
            }
            Sugar::Transact(body, fallback) => {
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                let f = self.fmt_expr_inline(fallback, Mode::Flat)?;
                Some(format!("{} {b} {} {f}", kw::TRANSACT, kw::ELSE))
            }
            Sugar::Range(pre, hi) => {
                let parts: Option<Vec<_>> =
                    pre.iter().map(|e| self.fmt_expr_inline(e, mode)).collect();
                let hi_s = self.fmt_expr_inline(hi, mode)?;
                parts.map(|p| format!("[{}..{hi_s}]", p.join(", ")))
            }
            Sugar::VarDecl(..) | Sugar::NamedHandle(..) => None,
        }
    }

    // A single comprehension qualifier, for the stacked layout form.
    fn fmt_qual(&self, q: &Qualifier, indent: usize) -> String {
        match q {
            Qualifier::Guard(g) => {
                let g = self
                    .fmt_expr_inline(g, Mode::Flat)
                    .unwrap_or_else(|| self.fmt_expr(g, indent, Mode::Flat));
                format!("{} {g}", kw::IF)
            }
            Qualifier::Bind(y, e) => {
                let e = self
                    .fmt_expr_inline(e, Mode::Flat)
                    .unwrap_or_else(|| self.fmt_expr(e, indent, Mode::Flat));
                format!("{} {y} = {e}", kw::LET)
            }
        }
    }

    fn fmt_quals(&self, quals: &[Qualifier]) -> Option<String> {
        use std::fmt::Write;
        let mut out = String::new();
        for q in quals {
            match q {
                Qualifier::Guard(g) => {
                    write!(out, ", {} {}", kw::IF, self.fmt_expr_inline(g, Mode::Flat)?).ok()?;
                }
                Qualifier::Bind(y, e) => {
                    write!(
                        out,
                        ", {} {y} = {}",
                        kw::LET,
                        self.fmt_expr_inline(e, Mode::Flat)?
                    )
                    .ok()?;
                }
            }
        }
        Some(out)
    }

    // Heads (if conditions, match scrutinees, handle bodies) sit before a layout
    // opener, so a multi-line head must be parenthesized to suppress layout.
    fn fmt_head(&self, e: &S<Expr>, indent: usize) -> String {
        if let Some(s) = self.fmt_expr_inline(e, Mode::Flat) {
            if indent * INDENT.len() + s.len() + 16 <= LINE_WIDTH {
                return s;
            }
        }
        format!("({})", self.fmt_expr_break(e, indent + 1, Mode::Flat))
    }

    // `from` is the offset just past the arm's `=>`, so a comment on the line
    // below the arrow re-emits as the body's leading comment.
    fn fmt_arm_body(&self, b: &S<Expr>, indent: usize, used: usize, from: usize) -> String {
        if !forces_break(b) && !self.has_comments(from, b.span.end) {
            if let Some(s) = self.fmt_expr_inline(b, Mode::Layout) {
                if used + 1 + s.len() <= LINE_WIDTH {
                    return format!(" {s}");
                }
            }
        }
        format!("\n{}", self.fmt_block(b, indent + 1, from))
    }

    fn fmt_handler_arms(&self, arms: &[HandlerArm], indent: usize, from: usize) -> String {
        let ind = INDENT.repeat(indent);
        // Handler arms carry no head span, so a comment above an arm is recovered
        // from the gap between the previous arm's body and this arm's body. The
        // first arm reaches back to the block opener.
        let mut prev = from;
        let mut arm_strs: Vec<String> = Vec::with_capacity(arms.len());
        for arm in arms {
            let body = arm_body(arm);
            let head = match arm {
                HandlerArm::Return(x, _) => format!("{ind}{} {x} {}", kw::RETURN, kw::FAT_ARROW),
                HandlerArm::Op(name, params, k, _) => {
                    let mut ps: Vec<String> = params.clone();
                    ps.push(k.clone());
                    format!("{ind}{}({}) {}", name, ps.join(", "), kw::FAT_ARROW)
                }
                HandlerArm::Sugar(SugarArm::Fun(name, params, _)) => {
                    format!(
                        "{ind}{} {}({}) {}",
                        kw::FUN,
                        name,
                        params.join(", "),
                        kw::FAT_ARROW
                    )
                }
                HandlerArm::Sugar(SugarArm::Final(name, params, _)) => format!(
                    "{ind}{} {} {}({}) {}",
                    kw::FINAL,
                    kw::CTL,
                    name,
                    params.join(", "),
                    kw::FAT_ARROW
                ),
                HandlerArm::Sugar(SugarArm::Val(x, _)) => format!("{ind}{} {x} =", kw::VAL),
            };
            let lead = self.lead_comments(prev, body.span.start, indent);
            let rendered = format!(
                "{head}{}",
                self.fmt_arm_body(body, indent, head.len(), body.span.start)
            );
            arm_strs.push(format!("{lead}{rendered}"));
            prev = body.span.end;
        }
        arm_strs.join("\n")
    }

    fn fmt_guard(&self, a: &Arm, indent: usize) -> String {
        a.guard.as_ref().map_or_else(String::new, |g| {
            format!(
                " {} {}",
                kw::IF,
                self.fmt_expr_inline(g, Mode::Flat)
                    .unwrap_or_else(|| self.fmt_expr(g, indent, Mode::Flat))
            )
        })
    }

    fn fmt_expr_break(&self, e: &S<Expr>, indent: usize, mode: Mode) -> String {
        match (&e.node, mode) {
            (Expr::Match(scrut, arms), Mode::Layout) => self.fmt_match_layout(scrut, arms, indent),
            (Expr::Match(s, arms), _) => self.fmt_match_flat(s, arms, indent, mode),
            (Expr::If(c, t, el), Mode::Layout) => self.fmt_if_layout(c, t, el, indent),
            (Expr::If(c, t, el), _) => self.fmt_if_flat(c, t, el, indent, mode),
            (Expr::Let(..), Mode::Layout) => {
                format!("({})", self.fmt_expr(e, indent + 1, Mode::Flat))
            }
            (Expr::Let(x, v, b), _) => self.fmt_let_break(x, v, b, indent, mode),
            (Expr::Pipe(x, f), _) => self.fmt_pipe_break(x, f, indent, mode),
            (Expr::Call(f, args), _) => self.fmt_call_flat(f, args, indent),
            (Expr::Handle(body, arms), Mode::Layout) => self.fmt_handle_layout(body, arms, indent),
            (Expr::Sugar(Sugar::TryCatch(body, arms)), Mode::Layout) => {
                self.fmt_trycatch_layout(e, body, arms, indent)
            }
            (Expr::Sugar(Sugar::For(x, s, quals, body)), Mode::Layout) => {
                self.fmt_for_layout(x, s, quals, body, indent)
            }
            (Expr::Sugar(Sugar::Transact(body, fallback)), Mode::Layout) => {
                self.fmt_transact_layout(e, body, fallback, indent)
            }
            (Expr::Sugar(Sugar::VarDecl(..) | Sugar::NamedHandle(..)), _) => self
                .fmt_block(e, indent, e.span.start)
                .trim_start()
                .to_string(),
            (Expr::Sugar(Sugar::Assign(x, v)), _) => {
                format!(
                    "{x} {} {}",
                    kw::COLON_EQ,
                    self.fmt_expr(v, indent, Mode::Flat)
                )
            }
            (Expr::Handle(body, arms), _) => self.fmt_handle_flat(body, arms, indent, mode),
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
            let body = self.fmt_arm_body(&a.body, indent + 1, head.len(), from);
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
                    if ind1.len() + one_line.len() + usize::from(!is_last) <= LINE_WIDTH {
                        return format!("{ind1}{one_line}{trail}");
                    }
                }
                let ind2 = INDENT.repeat(indent + 2);
                if let Some(ref b) = b_inline {
                    if ind2.len() + b.len() + trail.len() <= LINE_WIDTH {
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

    fn fmt_handle_layout(&self, body: &S<Expr>, arms: &[HandlerArm], indent: usize) -> String {
        let body_s = self.fmt_head(body, indent);
        format!(
            "{} {body_s} {}\n{}",
            kw::HANDLE,
            kw::WITH,
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
            let arm_body = self.fmt_arm_body(&a.body, indent + 1, head.len(), a.body.span.start);
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

    fn fmt_transact_layout(
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

    fn fmt_handle_flat(
        &self,
        body: &S<Expr>,
        arms: &[HandlerArm],
        indent: usize,
        mode: Mode,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let ind1 = INDENT.repeat(indent + 1);
        let body_s = self.fmt_expr(body, indent, mode);
        let arm_strs: Vec<String> = arms
            .iter()
            .map(|arm| match arm {
                HandlerArm::Return(x, arm_body) => {
                    format!(
                        "{ind1}{} {x} {} {}",
                        kw::RETURN,
                        kw::FAT_ARROW,
                        self.fmt_expr(arm_body, indent + 1, mode)
                    )
                }
                HandlerArm::Op(name, params, k, arm_body) => {
                    let mut ps: Vec<String> = params.clone();
                    ps.push(k.clone());
                    format!(
                        "{ind1}{}({}) {} {}",
                        name,
                        ps.join(", "),
                        kw::FAT_ARROW,
                        self.fmt_expr(arm_body, indent + 1, mode)
                    )
                }
                HandlerArm::Sugar(SugarArm::Fun(name, params, arm_body)) => {
                    format!(
                        "{ind1}{} {}({}) {} {}",
                        kw::FUN,
                        name,
                        params.join(", "),
                        kw::FAT_ARROW,
                        self.fmt_expr(arm_body, indent + 1, mode)
                    )
                }
                HandlerArm::Sugar(SugarArm::Final(name, params, arm_body)) => {
                    format!(
                        "{ind1}{} {} {}({}) {} {}",
                        kw::FINAL,
                        kw::CTL,
                        name,
                        params.join(", "),
                        kw::FAT_ARROW,
                        self.fmt_expr(arm_body, indent + 1, mode)
                    )
                }
                HandlerArm::Sugar(SugarArm::Val(x, arm_body)) => {
                    format!(
                        "{ind1}{} {x} = {}",
                        kw::VAL,
                        self.fmt_expr(arm_body, indent + 1, mode)
                    )
                }
            })
            .collect();
        format!(
            "{} {body_s} {} {{\n{}\n{ind}}}",
            kw::HANDLE,
            kw::WITH,
            arm_strs.join(",\n")
        )
    }
}
