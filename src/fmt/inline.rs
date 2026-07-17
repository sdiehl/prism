use std::fmt::Write;

use super::call::{call_shape, callee_parens, dot_recv_parens, is_with_call, paren_if, CallShape};
use super::decl::fmt_ty;
use super::lit::{escape_str, fmt_char, fmt_float};
use super::ops::{binop_prec, needs_left_paren, needs_right_paren, neg_operand_needs_paren};
use super::pat::fmt_pat_inline;
use super::{BinOp, Expr, Fmt, Marker, Mode, PathOp, PathStep, Qualifier, Sugar, Surface, S};
use crate::kw;

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

pub(super) fn as_compound_assign<'a>(x: &str, v: &'a S<Expr>) -> Option<(BinOp, &'a S<Expr>)> {
    as_compound(v, |lhs| matches!(lhs, Expr::Var(n) if n == x))
}

// The index analogue of `as_compound_assign`: an `IndexAssign` whose value is a
// synth `Bin(op, Index(..), rhs)` (the shape `compound_stmt` builds), so the
// formatter restores `a[i] <op>= rhs`. A hand-written `a[i] := a[i] + e` (a
// non-synth `Bin`) keeps its explicit `:=` form.
fn as_index_compound(v: &S<Expr>) -> Option<(BinOp, &S<Expr>)> {
    as_compound(v, |lhs| matches!(lhs, Expr::Index(..)))
}

impl Fmt<'_> {
    // `Interp` marker calls round-trip back to the literal: even args are segments,
    // odd args are holes printed inline between braces.
    pub(super) fn fmt_interp(&self, f: &S<Expr>, args: &[S<Expr>]) -> Option<String> {
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
                    // Flatten a broken rendering to one line, collapsing only the
                    // newline indentation. Never touch spacing inside a token:
                    // `split_whitespace` here would rewrite a nested string literal
                    // "a   b" to "a b" and change the program's meaning.
                    self.fmt_expr_break(a, 0, Mode::Flat)
                        .lines()
                        .map(str::trim)
                        .filter(|line| !line.is_empty())
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
    pub(super) fn fmt_path(&self, steps: &[PathStep]) -> Option<String> {
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

    // The bracket-key text of an index expression. A multi-index bracket
    // `t[i, j]` parses as an `Index` whose key is a synthetic list literal (the
    // grammar marks it `synth`), so the formatter restores the written surface
    // by joining the elements rather than printing the list's own brackets; a
    // user-written list key `a[[1, 2]]` is not synthetic and keeps them.
    pub(super) fn index_key_inline(&self, key: &S<Expr>) -> Option<String> {
        if key.synth {
            if let Expr::List(es) = &key.node {
                let parts: Option<Vec<_>> = es
                    .iter()
                    .map(|e| self.fmt_expr_inline(e, Mode::Flat))
                    .collect();
                return Some(parts?.join(", "));
            }
        }
        self.fmt_expr_inline(key, Mode::Flat)
    }

    pub(super) fn fmt_expr_inline(&self, e: &S<Expr>, mode: Mode) -> Option<String> {
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
            Expr::Hole(name) => Some(format!("?{name}")),
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
            Expr::UnboxedField(e, field) => {
                let e_s = self.fmt_expr_inline(e, mode)?;
                Some(format!("{e_s}.#{field}"))
            }
            Expr::UnboxedTuple(elems) => {
                if self.has_comments(e.span.start, e.span.end) {
                    return None;
                }
                let parts: Option<Vec<_>> = elems
                    .iter()
                    .map(|x| self.fmt_expr_inline(x, Mode::Flat))
                    .collect();
                parts.map(|p| format!("#({})", p.join(", ")))
            }
            Expr::UnboxedRecord(fields) => {
                if self.has_comments(e.span.start, e.span.end) {
                    return None;
                }
                let parts: Option<Vec<_>> = fields
                    .iter()
                    .map(|(f, v)| Some(format!("{f} = {}", self.fmt_expr_inline(v, Mode::Flat)?)))
                    .collect();
                parts.map(|p| format!("#{{ {} }}", p.join(", ")))
            }
            Expr::Index(recv, key) => {
                let recv_s = self.fmt_expr_inline(recv, mode)?;
                let recv_s = paren_if(callee_parens(&recv.node), recv_s);
                let key_s = self.index_key_inline(key)?;
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
                let key_s = self.index_key_inline(key)?;
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
            Sugar::Probe(name, body) => {
                let b = self.fmt_expr_inline(body, Mode::Flat)?;
                Some(format!("{} {name:?} {} {b}", kw::PROBE, kw::DO))
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
            Sugar::VarDecl(..) | Sugar::NamedHandle(..) => None,
        }
    }

    // A single comprehension qualifier, for the stacked layout form.
    pub(super) fn fmt_qual(&self, q: &Qualifier, indent: usize) -> String {
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
}
