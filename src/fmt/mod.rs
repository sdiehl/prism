use std::fmt::Write;

use marginalia::{BuiltinKind, Trivia, TriviaTable};

use crate::error::Error;
use crate::kw;
use crate::parse::{parse, ParseResult};
use crate::syntax::ast::{
    Arm, BinOp, CatchArm, ConvDir, Converter, Expr, HandlerArm, Marker, PathOp, PathStep, Pattern,
    Program, Qualifier, Rung, Span, StableDecl, Sugar, SugarArm, Surface, S,
};

pub(crate) mod decl;
mod exprdoc;
mod ops;
mod pat;
use decl::{fmt_class, fmt_data, fmt_effect, fmt_import, fmt_labels, fmt_ty};
use ops::{
    binop_prec, low_prec_operand, needs_left_paren, needs_right_paren, neg_operand_needs_paren,
};
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

/// Reseat every `stable` block's per-rung shape golden, then format.
///
/// Each shipped rung's `frozen "<digest>"` badge is rewritten to its recomputed
/// shape digest and the current rung's badge is dropped. This is the loud reseat
/// path behind `prism wire --accept`, the analogue of `just snap` for the goldens.
///
/// # Errors
/// Fails when the source does not parse or a `stable` block is malformed.
pub fn format_wire_accept(src: &str) -> Result<String, Error> {
    let ParseResult {
        mut program,
        trivia,
    } = parse(src)?;
    for sd in &mut program.stable {
        let digests = crate::syntax::desugar::stable_rung_digests(sd)?;
        let total = sd.rungs.len();
        for (idx, rung) in sd.rungs.iter_mut().enumerate() {
            rung.frozen = if idx + 1 == total {
                None
            } else {
                digests
                    .iter()
                    .find(|(v, _)| v == &rung.name)
                    .map(|(_, d)| d.clone())
            };
        }
    }
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

// The structural shape of a call `f(args)` once its head is decoded. Both the
// flat/break printer (`fmt_call_flat`) and the inline printer decode through
// this one classifier so they can never disagree on how a call head reads; a
// missing arm here once let the break path drop a `using` clause, re-emitting
// `f(a, using I)` as `f(using I)(a)` and breaking format round-trip.
enum CallShape<'a> {
    Recv(&'a S<Expr>),                              // `recv?`
    Dot(DotCall<'a>),                               // `recv.name(rest)`
    Inst(&'a S<Expr>, &'a [String], &'a [S<Expr>]), // `inner(args, using names)`
    Plain(&'a S<Expr>, &'a [S<Expr>]),              // `f(args)`
}

// Decode a call head into its `CallShape`. Ordering is priority: a `?` receiver,
// then a UFCS dot call, then explicit instance selection, then a plain call.
fn call_shape<'a>(f: &'a S<Expr>, args: &'a [S<Expr>]) -> CallShape<'a> {
    if let Some(recv) = try_recv(f, args) {
        return CallShape::Recv(recv);
    }
    if let Some(dot) = dot_parts(f, args) {
        return CallShape::Dot(dot);
    }
    if let Expr::Inst(inner, names) = &f.node {
        return CallShape::Inst(inner, names, args);
    }
    CallShape::Plain(f, args)
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

// Wrap an already-rendered operand in parens when the surrounding precedence
// demands it.
fn paren_if(parens: bool, s: String) -> String {
    if parens {
        format!("({s})")
    } else {
        s
    }
}

// In statement position, `match` and `if` always lay out across lines, even
// when they would fit on one: their arms and branches read better stacked, the
// way other languages write them. Synth matches (pattern-let / `?` desugar) are
// excluded. The block printer restores those surfaces inline. Record and optic
// literals whose shape reads better stacked (`wants_break`) force layout too,
// so a dense or nested constructor never stays cramped on one line.
fn forces_break(e: &S<Expr>) -> bool {
    wants_break(&e.node)
        || matches!(
            e.node,
            Expr::Match(..) | Expr::If(..) | Expr::Sugar(Sugar::For(..) | Sugar::While(..))
        ) && !e.synth
}

// The most fields a record constructor keeps on one line; beyond this it stacks
// one field per line even when it would fit, for scannability.
const MAX_INLINE_RECORD_FIELDS: usize = 4;

// A record or optic literal reads better stacked across lines regardless of
// width. A record does when it carries more than `MAX_INLINE_RECORD_FIELDS`
// fields or nests another record constructor as a field value; a nested optic
// update does when it has several clauses and any path actually traverses
// (`each`/`?Ctor`/`where`/`[i]`), so the foci line up one per row.
fn wants_break(e: &Expr) -> bool {
    match e {
        Expr::RecordCreate(_, fields) | Expr::RecordUpdate(_, _, fields) => {
            fields.len() > MAX_INLINE_RECORD_FIELDS
                || fields.iter().any(|(_, v)| is_record_lit(&v.node))
        }
        Expr::RecordUpdatePath(_, ups) => {
            ups.len() > 1 && ups.iter().any(|(p, _)| p.iter().any(path_step_traverses))
        }
        _ => false,
    }
}

const fn is_record_lit(e: &Expr) -> bool {
    matches!(
        e,
        Expr::RecordCreate(..) | Expr::RecordUpdate(..) | Expr::RecordUpdatePath(..)
    )
}

const fn path_step_traverses(s: &PathStep) -> bool {
    matches!(
        s,
        PathStep::Each | PathStep::Case(_) | PathStep::Index(_) | PathStep::Where(_)
    )
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
                    | Sugar::While(..)
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

// The shared shape of `as_compound_assign`/`as_index_compound`: a synth
// `Bin(op, lhs, rhs)` with a compound-eligible op whose `lhs` matches the
// caller's target predicate. Returns the op and right operand, so the formatter
// restores `x <op>= rhs`; a hand-written `x := x + e` (non-synth `Bin`) returns
// `None` and keeps its explicit `:=` form.
fn as_compound(v: &S<Expr>, lhs_ok: impl Fn(&Expr) -> bool) -> Option<(BinOp, &S<Expr>)> {
    if !v.synth {
        return None;
    }
    let Expr::Bin(op, lhs, rhs) = &v.node else {
        return None;
    };
    (matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Rem) && lhs_ok(&lhs.node))
        .then_some((*op, rhs))
}

fn as_compound_assign<'a>(x: &str, v: &'a S<Expr>) -> Option<(BinOp, &'a S<Expr>)> {
    as_compound(v, |lhs| matches!(lhs, Expr::Var(n) if n == x))
}

// The index analogue of `as_compound_assign`: an `IndexAssign` whose value is a
// synth `Bin(op, Index(..), rhs)` (the shape `compound_stmt` builds), so the
// formatter restores `a[i] <op>= rhs`. A hand-written `a[i] := a[i] + e` (a
// non-synth `Bin`) keeps its explicit `:=` form.
fn as_index_compound(v: &S<Expr>) -> Option<(BinOp, &S<Expr>)> {
    as_compound(v, |lhs| matches!(lhs, Expr::Index(..)))
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

// A handler arm's head (everything up to and including the `=>`/`=`) at the
// given indent. The body is rendered separately, so both the flat and offside
// handler printers share one source of arm-head syntax.
fn arm_head(arm: &HandlerArm, ind: &str) -> String {
    match arm {
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
    }
}

impl Fmt<'_> {
    fn verbatim(&self, start: usize, end: usize) -> String {
        self.source.get(start..end).unwrap_or_default().to_string()
    }

    // Preserve the writer's numeric spelling verbatim: reprint a literal from
    // source when it carries a digit separator or an exponent (`1_000_000`,
    // `1e-25`, `1E3`), otherwise use the canonical rendering. Rewriting `1e3`
    // to `1000.0` would be meaning-preserving but erases the writer's chosen
    // notation, so scientific form is the writer's to keep. Idempotent either
    // way, since a reparsed literal re-slices to the same text.
    fn lit_text(&self, span: Span, canonical: impl FnOnce() -> String) -> String {
        let src = self.source.get(span.start..span.end).unwrap_or_default();
        if src.contains('_') || src.contains(['e', 'E']) {
            src.to_string()
        } else {
            canonical()
        }
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

    // A line comment that opens on the same source line as `after` (no newline
    // in between), i.e. a trailing comment like `let x = 1 -- note`. Returns its
    // text and the offset just past it, so the caller can both append it inline
    // and skip it when emitting the following statement's leading comments.
    fn trailing_comment(&self, after: usize) -> Option<(&str, usize)> {
        let eol = self.source[after..]
            .find('\n')
            .map_or(self.source.len(), |i| after + i);
        self.trivia
            .between(after, eol)
            .find_map(|ev| match &ev.trivia {
                Trivia::Comment {
                    kind: BuiltinKind::Line,
                    text,
                } => Some((text.as_str(), ev.span.end)),
                _ => None,
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

    // A `stable` block, one rung or converter per line inside real braces (so the
    // entries are comma-separated, like a class body). Always multi-line, so the
    // layout is a pure function of the tree and round-trips idempotently; the
    // per-rung `frozen "<digest>"` golden is preserved verbatim.
    fn fmt_stable(&self, sd: &StableDecl) -> String {
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

    fn fmt_program(&self, prog: &Program) -> String {
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
        paren_if(dot_recv_parens(&recv.node), s)
    }

    // A call head in flat form: either `f(args)` or the restored `recv.f(rest)`.
    fn fmt_call_flat(&self, f: &S<Expr>, args: &[S<Expr>], indent: usize) -> String {
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
    fn fmt_block(&self, e: &S<Expr>, indent: usize, from: usize) -> String {
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

    // The `let` break ladder (FMT.md rule 5): (1) the whole binding on one line;
    // (2) break after `=` with the value flat one indent in, when it fits there;
    // (3) keep `let x =` on the line and let the value break internally. A value
    // that must lay out offside (a record, a match/if, an imperative block) or
    // that carries comments skips (3) and takes the offside block.
    fn fmt_let_line(&self, x: &str, v: &S<Expr>, indent: usize, from: usize) -> String {
        let ind = INDENT.repeat(indent);
        let head = format!("{ind}{} {x} = ", kw::LET);
        let breakable = !self.has_comments(from, v.span.end) && !forces_break(v);
        if breakable {
            if let Some(s) = self.fmt_expr_inline(v, Mode::Layout) {
                if head.len() + s.len() <= LINE_WIDTH {
                    return format!("{head}{s}"); // rung 1
                }
                let inner = INDENT.repeat(indent + 1);
                if inner.len() + s.len() <= LINE_WIDTH {
                    return format!("{ind}{} {x} =\n{inner}{s}", kw::LET); // rung 2
                }
            }
            // rung 3: the value breaks with its head on the `let` line.
            if let Some(broken) = self.render_expr(v, ind.len(), head.len()) {
                return format!("{head}{broken}");
            }
        }
        format!(
            "{ind}{} {x} =\n{}",
            kw::LET,
            self.fmt_block(v, indent + 1, from)
        )
    }

    fn fmt_expr(&self, e: &S<Expr>, indent: usize, mode: Mode) -> String {
        if !wants_break(&e.node) {
            if let Some(s) = self.fmt_expr_inline(e, mode) {
                if indent * INDENT.len() + s.len() <= LINE_WIDTH {
                    return s;
                }
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

    // A path-update path. `Field`/`each`/`?Ctor` join with dots; an `[i]` index
    // attaches to the preceding step with no dot; a `where p` filter wraps the
    // step it follows as `(step where p)`, the form it parses from.
    fn fmt_path(&self, steps: &[PathStep]) -> Option<String> {
        // Each segment is (joins_with_dot, text). Index segments attach.
        let mut segs: Vec<(bool, String)> = Vec::new();
        let mut i = 0;
        while i < steps.len() {
            match &steps[i] {
                PathStep::Index(e) => {
                    segs.push((false, format!("[{}]", self.fmt_expr_inline(e, Mode::Flat)?)));
                    i += 1;
                }
                // A bare `where` not preceded by a step never parses; skip defensively.
                PathStep::Where(_) => i += 1,
                step => {
                    let base = match step {
                        PathStep::Field(f) => f.clone(),
                        PathStep::Each => kw::EACH.to_string(),
                        PathStep::Case(c) => format!("{}{c}", kw::QUESTION),
                        _ => unreachable!("index/where handled above"),
                    };
                    if let Some(PathStep::Where(p)) = steps.get(i + 1) {
                        let ps = self.fmt_expr_inline(p, Mode::Flat)?;
                        segs.push((true, format!("({base} {} {ps})", kw::WHERE)));
                        i += 2;
                    } else {
                        segs.push((true, base));
                        i += 1;
                    }
                }
            }
        }
        let mut out = String::new();
        for (k, (dot, text)) in segs.iter().enumerate() {
            if k > 0 && *dot {
                out.push('.');
            }
            out.push_str(text);
        }
        Some(out)
    }

    fn fmt_expr_inline(&self, e: &S<Expr>, mode: Mode) -> Option<String> {
        match &e.node {
            Expr::Int(n) => Some(self.lit_text(e.span, || n.to_string())),
            Expr::Float(f) => Some(self.lit_text(e.span, || fmt_float(*f))),
            Expr::Neg(inner) => {
                let paren = neg_operand_needs_paren(&inner.node);
                let s = self.fmt_expr_inline(inner, if paren { Mode::Flat } else { mode })?;
                let s = paren_if(paren, s);
                // A space keeps `- -x` (double negation) from colliding into the
                // `--` line-comment lexeme on reparse.
                let sep = if s.starts_with('-') { " " } else { "" };
                Some(format!("-{sep}{s}"))
            }
            Expr::Char(c) => Some(fmt_char(*c)),
            Expr::Bool(b) => Some(b.to_string()),
            Expr::Unit => Some("()".into()),
            Expr::Str(s) => Some(format!("\"{}\"", escape_str(s))),
            Expr::Var(x) => Some(x.clone()),
            // A delimited list collapses onto one line only when nothing inside
            // carries a comment; an interior `--` line comment cannot survive a
            // flat join, so refuse and let the break path emit it verbatim.
            Expr::Tuple(elems) => {
                if self.has_comments(e.span.start, e.span.end) {
                    return None;
                }
                let parts: Option<Vec<_>> = elems
                    .iter()
                    .map(|x| self.fmt_expr_inline(x, Mode::Flat))
                    .collect();
                parts.map(|p| format!("({})", p.join(", ")))
            }
            Expr::List(elems) if elems.is_empty() => Some("[]".into()),
            Expr::List(elems) => {
                if self.has_comments(e.span.start, e.span.end) {
                    return None;
                }
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
                let a_s = paren_if(a_paren, a_s);
                let b_s = paren_if(b_paren, b_s);
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
                // A comment between the arguments would be dropped by the flat
                // join below; refuse so the break path preserves it verbatim.
                if self.has_comments(f.span.end, e.span.end) {
                    return None;
                }
                let flat_args = |xs: &[S<Expr>]| -> Option<Vec<String>> {
                    xs.iter()
                        .map(|a| self.fmt_expr_inline(a, Mode::Flat))
                        .collect()
                };
                match call_shape(f, args) {
                    CallShape::Recv(recv) => {
                        let recv_s = self.fmt_expr_inline(recv, Mode::Flat)?;
                        let recv_s = paren_if(dot_recv_parens(&recv.node), recv_s);
                        Some(format!("{recv_s}{}", kw::QUESTION))
                    }
                    CallShape::Dot((name, recv, rest)) => {
                        let recv_s = self.fmt_expr_inline(recv, Mode::Flat)?;
                        let recv_s = paren_if(dot_recv_parens(&recv.node), recv_s);
                        flat_args(rest).map(|a| format!("{recv_s}.{name}({})", a.join(", ")))
                    }
                    // Explicit instance selection: fold the callee's names back into
                    // a trailing `using` clause on this call.
                    CallShape::Inst(inner, names, args) => {
                        let inner_s = self.fmt_expr_inline(inner, mode)?;
                        let inner_s = paren_if(callee_parens(&inner.node), inner_s);
                        flat_args(args).map(|a| {
                            let using = format!("{} {}", kw::USING, names.join(", "));
                            if a.is_empty() {
                                format!("{inner_s}({using})")
                            } else {
                                format!("{inner_s}({}, {using})", a.join(", "))
                            }
                        })
                    }
                    CallShape::Plain(f, args) => {
                        let f_s = self.fmt_expr_inline(f, mode)?;
                        let f_s = paren_if(callee_parens(&f.node), f_s);
                        flat_args(args).map(|a| format!("{f_s}({})", a.join(", ")))
                    }
                }
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
            Expr::Index(recv, key) => {
                let recv_s = self.fmt_expr_inline(recv, mode)?;
                let recv_s = paren_if(callee_parens(&recv.node), recv_s);
                let key_s = self.fmt_expr_inline(key, Mode::Flat)?;
                Some(format!("{recv_s}[{key_s}]"))
            }
            // Only produced by desugar, so the surface formatter never sees it;
            // a faithful fallback for completeness.
            Expr::IndexSet(recv, key, val) => {
                let recv_s = self.fmt_expr_inline(recv, mode)?;
                let key_s = self.fmt_expr_inline(key, Mode::Flat)?;
                let val_s = self.fmt_expr_inline(val, Mode::Flat)?;
                Some(format!("{recv_s}[{key_s}] {} {val_s}", kw::COLON_EQ))
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
                    .map(|(p, op)| {
                        let (sigil, e) = match op {
                            PathOp::Set(e) => (kw::EQ, e),
                            PathOp::Modify(e) => (kw::TILDE, e),
                        };
                        let ps = self.fmt_path(p)?;
                        let e_s = self.fmt_expr_inline(e, Mode::Flat)?;
                        Some(format!("{ps} {sigil} {e_s}"))
                    })
                    .collect();
                us.map(|us| format!("{{ {base_s} | {} }}", us.join(", ")))
            }
            // An `Inst` not wrapped in a call (rare): the parser only produces it
            // as a call callee, so this prints the bare zero-argument form.
            Expr::Inst(f, names) => {
                let f_s = self.fmt_expr_inline(f, mode)?;
                Some(format!("{f_s}({} {})", kw::USING, names.join(", ")))
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
            Sugar::ReadPath(base, steps) => {
                let base_s = self.fmt_expr_inline(base, mode)?;
                let path = self.fmt_path(steps)?;
                Some(format!("{base_s}.[{path}]"))
            }
            Sugar::Assign(x, v) => {
                if let Some((op, rhs)) = as_compound_assign(x, v) {
                    let rhs_s = self.fmt_expr_inline(rhs, mode)?;
                    Some(format!("{x} {}= {rhs_s}", op.spelling()))
                } else {
                    let v_s = self.fmt_expr_inline(v, mode)?;
                    Some(format!("{x} {} {v_s}", kw::COLON_EQ))
                }
            }
            Sugar::IndexAssign(recv, key, value) => {
                let recv_s = self.fmt_expr_inline(recv, mode)?;
                let recv_s = paren_if(callee_parens(&recv.node), recv_s);
                let key_s = self.fmt_expr_inline(key, Mode::Flat)?;
                if let Some((op, rhs)) = as_index_compound(value) {
                    let rhs_s = self.fmt_expr_inline(rhs, mode)?;
                    Some(format!("{recv_s}[{key_s}] {}= {rhs_s}", op.spelling()))
                } else {
                    let v_s = self.fmt_expr_inline(value, mode)?;
                    Some(format!("{recv_s}[{key_s}] {} {v_s}", kw::COLON_EQ))
                }
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
            Sugar::While(cond, body) => {
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                if let Some(c) = cond {
                    let c_s = self.fmt_expr_inline(c, Mode::Flat)?;
                    Some(format!("{} {c_s} {} {b}", kw::WHILE, kw::DO))
                } else {
                    Some(format!("{} {b}", kw::LOOP))
                }
            }
            Sugar::Break => Some(kw::BREAK.to_string()),
            Sugar::Continue => Some(kw::CONTINUE.to_string()),
            Sugar::Return(e) => {
                let e_s = self.fmt_expr_inline(e, mode)?;
                Some(format!("{} {e_s}", kw::RETURN))
            }
            Sugar::WithoutAlloc(body) => {
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                Some(format!("{} {} {b}", kw::WITHOUT, kw::ALLOC))
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
        if !wants_break(&e.node) {
            if let Some(s) = self.fmt_expr_inline(e, Mode::Flat) {
                if indent * INDENT.len() + s.len() + 16 <= LINE_WIDTH {
                    return s;
                }
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
            let head = arm_head(arm, &ind);
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
            (Expr::Sugar(Sugar::While(cond, body)), Mode::Layout) => {
                self.fmt_while_layout(cond.as_deref(), body, indent)
            }
            (Expr::Sugar(Sugar::WithoutAlloc(body)), Mode::Layout) => format!(
                "{} {}\n{}",
                kw::WITHOUT,
                kw::ALLOC,
                self.fmt_block(body, indent + 1, body.span.start)
            ),
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
            (Expr::Handle(body, arms), _) => self.fmt_handle_flat(body, arms, indent, mode),
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

    // Stack a record literal's fields one per line at `indent + 1`, an optional
    // `..base` spread first (a `RecordUpdate`), the closing `}` at `indent`. Only
    // reached from `fmt_expr` when the inline form overflows the width budget, so
    // a short record stays on one line and this is idempotent.
    fn fmt_record_break(
        &self,
        name: &str,
        base: Option<&S<Expr>>,
        fields: &[(String, S<Expr>)],
        indent: usize,
    ) -> String {
        let inner = INDENT.repeat(indent + 1);
        let mut lines: Vec<String> = Vec::new();
        if let Some(b) = base {
            lines.push(format!(
                "{inner}..{}",
                self.fmt_expr(b, indent + 1, Mode::Flat)
            ));
        }
        for (f, e) in fields {
            lines.push(format!(
                "{inner}{f} = {}",
                self.fmt_expr(e, indent + 1, Mode::Flat)
            ));
        }
        format!(
            "{name} {{\n{}\n{}}}",
            lines.join(",\n"),
            INDENT.repeat(indent)
        )
    }

    // A nested optic update stacked one clause per line, leading-delimiter style:
    //   { base
    //   | path op val
    //   , path op val
    //   }
    // The base sits alone on the opening line; the first clause is led by `|`, the
    // rest by `,`; the closing brace returns to the update's own column. The whole
    // form is brace-delimited, so it reparses to the same tree (idempotent). Falls
    // back to verbatim source if a path carries a sub-expression that cannot inline.
    fn fmt_path_update_break(
        &self,
        e: &S<Expr>,
        base: &S<Expr>,
        ups: &[(Vec<PathStep>, PathOp)],
        indent: usize,
    ) -> String {
        let ind = INDENT.repeat(indent);
        let base_s = self.fmt_expr(base, indent + 1, Mode::Flat);
        let mut lines = vec![format!("{{ {base_s}")];
        for (k, (p, op)) in ups.iter().enumerate() {
            let Some(ps) = self.fmt_path(p) else {
                return self.verbatim(e.span.start, e.span.end);
            };
            let (sigil, val) = match op {
                PathOp::Set(v) => (kw::EQ, v),
                PathOp::Modify(v) => (kw::TILDE, v),
            };
            let lead = if k == 0 { "|" } else { "," };
            let val_s = self.fmt_expr(val, indent + 1, Mode::Flat);
            lines.push(format!("{ind}{lead} {ps} {sigil} {val_s}"));
        }
        lines.push(format!("{ind}}}"));
        lines.join("\n")
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
            .map(|arm| {
                format!(
                    "{} {}",
                    arm_head(arm, &ind1),
                    self.fmt_expr(arm_body(arm), indent + 1, mode)
                )
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
