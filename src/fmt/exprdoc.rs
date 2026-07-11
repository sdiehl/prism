//! Expression layout as a `marginalia::pretty` document.
//!
//! This is the breaking engine the expression printer lacked: `expr_doc`
//! lowers a value expression to a `Doc` whose groups render flat when they fit
//! and explode to the house-style broken form when they do not, and
//! `render_expr` places that document into an already-indented slot. The value
//! forms it owns are calls, collection literals (list/tuple), operator chains
//! (binary and `|>`), and the postfix spine (field access, index, `?`, unary
//! minus); everything statement-shaped (match/if/handle/let sequences, records,
//! optics, the imperative sugars) stays with the offside string printers in
//! `mod.rs`, and a nested occurrence of one of those reaches `expr_doc` as its
//! flat inline rendering.
//!
//! House style: a broken delimited sequence puts one element per line with a
//! trailing comma, elements two indent units in from the line that opened the
//! group and the closing delimiter one unit in; a call whose final argument is a
//! delimited aggregate hugs (the parens do not break, the aggregate does); a
//! broken operator chain breaks before each operator at one indent unit, at the
//! lowest precedence present.
//!
//! Layout threads a `base` column: the column the line that opens a group starts
//! at, from which every nested indent is measured. Sequence elements and
//! operator operands are live nested documents; the engine's group-fit
//! measurement (marginalia 0.2.1) stops at the end of the current line, so each
//! nested group is measured against its own line rather than the whole document
//! tail. `base` survives for the one delegated form: a broken record splices the
//! string printer's absolute-column layout, which needs to know where its line
//! begins.

use marginalia::pretty::{
    comma, concat, flat_alt, group, indent, line, lparen, nil, pretty_at, punctuate, rparen,
    softline, space, text, Doc,
};

use super::breaks::wants_break;
use super::call::{call_shape, callee_parens, dot_recv_parens, is_with_call, CallShape};
use super::ops::{binop_prec, needs_left_paren, needs_right_paren, neg_operand_needs_paren};
use super::{Fmt, Mode, INDENT, LINE_WIDTH};
use crate::kw;
use crate::syntax::ast::{BinOp, Expr, S};

// One indent unit, in columns (the width of `INDENT`). Broken sequence elements
// sit two units in, the closing delimiter one unit in, and a broken operator
// leads at one unit; deriving all three from `INDENT` keeps the doc layout and
// the string printers on one definition of a level.
const UNIT: usize = INDENT.len();
const ITEM_NEST: usize = 2 * UNIT;
const CLOSE_NEST: usize = UNIT;
const OP_NEST: usize = UNIT;

// Indent by a column count. The layout engine's `indent` takes a signed delta;
// our nests are always small positive column counts, so the widening cannot
// wrap. Threading every nest through here keeps that the one conversion site.
#[allow(clippy::cast_possible_wrap)]
fn nest(cols: usize, d: Doc) -> Doc {
    indent(cols as isize, d)
}

// Wrap a rendered operand in parens when the surrounding precedence demands it,
// the doc analogue of `mod.rs::paren_if`.
fn paren_doc(parens: bool, d: Doc) -> Doc {
    if parens {
        concat([lparen(), d, rparen()])
    } else {
        d
    }
}

// A house-style delimited sequence: flat when it fits, else one element per line
// with a trailing comma, elements at `ITEM_NEST` and the closing delimiter at
// `CLOSE_NEST` from the line that opened the group. `pad` puts a space just
// inside the delimiters in the flat form (the brace shape); list, tuple, and
// argument parens leave it off.
fn seq_block(open: Doc, close: Doc, pad: bool, items: Vec<Doc>) -> Doc {
    let edge = if pad { line() } else { softline() };
    let between = concat([comma(), line()]);
    let body = concat(punctuate(&between, items));
    let trail = flat_alt(nil(), comma());
    group(concat([
        open,
        nest(ITEM_NEST, concat([edge.clone(), body, trail])),
        nest(CLOSE_NEST, concat([edge, close])),
    ]))
}

// A call whose final argument is a delimited aggregate does not break its own
// parens; the break happens inside the aggregate. Hugging chains
// through nested sole-argument calls, so a stack of wrapper functions around one
// list costs no indentation. A record is not huggable here: it reaches
// `expr_doc` as flat text, so it cannot supply the interior break.
fn call_hugs(last: &Expr) -> bool {
    match last {
        Expr::List(elems) => !elems.is_empty(),
        Expr::Tuple(_) => true,
        Expr::Call(_, args) => {
            !is_with_call(args) && args.last().is_some_and(|a| call_hugs(&a.node))
        }
        _ => false,
    }
}

impl Fmt<'_> {
    // An element or operand nested live in its parent: the parent's group
    // decides flat-versus-broken from the flat widths, and the operand's own
    // groups take their break decisions against their own line (the engine's
    // fit measurement stops at the line end). `paren` wraps it. `None`
    // propagates the inline printer's refusal (a comment, or an offside-only
    // nested form) so the caller can take the verbatim fallback.
    fn operand(&self, e: &S<Expr>, base: usize, paren: bool) -> Option<Doc> {
        Some(paren_doc(paren, self.expr_doc(e, base)?))
    }

    // Lower a value expression to a breakable document whose groups are measured
    // from column `base`. `None` when the expression carries a form that must be
    // reprinted verbatim (a comment) or laid out offside.
    pub(super) fn expr_doc(&self, e: &S<Expr>, base: usize) -> Option<Doc> {
        match &e.node {
            Expr::Neg(inner) => {
                let paren = neg_operand_needs_paren(&inner.node);
                let d = paren_doc(paren, self.expr_doc(inner, base)?);
                // A space keeps `- -x` from colliding into the `--` comment lexeme.
                let sep = if !paren && matches!(inner.node, Expr::Neg(_)) {
                    space()
                } else {
                    nil()
                };
                Some(concat([text("-"), sep, d]))
            }
            Expr::Bin(op, a, b) => self.bin_doc(*op, a, b, base),
            Expr::Pipe(x, f) => self.pipe_doc(x, f, base),
            Expr::Call(f, args) => self.call_doc(e, f, args, base),
            Expr::List(elems) if elems.is_empty() => Some(text("[]")),
            Expr::List(elems) => {
                if self.has_comments(e.span.start, e.span.end) {
                    return None;
                }
                let items = self.seq_items(elems, base)?;
                Some(seq_block(
                    text(kw::LBRACKET),
                    text(kw::RBRACKET),
                    false,
                    items,
                ))
            }
            Expr::Tuple(elems) => {
                if self.has_comments(e.span.start, e.span.end) {
                    return None;
                }
                let items = self.seq_items(elems, base)?;
                Some(seq_block(lparen(), rparen(), false, items))
            }
            Expr::FieldAccess(recv, field) => Some(concat([
                self.expr_doc(recv, base)?,
                text(format!(".{field}")),
            ])),
            Expr::Index(recv, key) => {
                let recv_d = paren_doc(callee_parens(&recv.node), self.expr_doc(recv, base)?);
                let key_s = self.index_key_inline(key)?;
                Some(concat([recv_d, text(format!("[{key_s}]"))]))
            }
            // A record nested in a value position (a call argument, an operand)
            // stays flat when it fits and otherwise stacks its fields, reusing the
            // string printer's layout (`fmt_record_break`) verbatim so a record in
            // statement position and one nested in an expression lay out alike. A
            // `wants_break` record breaks unconditionally, as it does elsewhere.
            Expr::RecordCreate(name, fields) => self.record_doc(e, name, None, fields, base),
            Expr::RecordUpdate(rec, name, fields) => {
                self.record_doc(e, name, Some(rec), fields, base)
            }
            // Everything else (atoms, optics, match/if/handle, lambdas, the
            // imperative sugars) rides in as its flat inline form.
            _ => self.fmt_expr_inline(e, Mode::Flat).map(text),
        }
    }

    // A record literal or update as a document, delegating the stacked form to
    // the string printer so it matches a statement-position record byte for byte.
    // `base` must be a whole number of indent units (every column this formatter
    // produces is); a stray offset falls back to the flat form rather than
    // mis-indenting.
    fn record_doc(
        &self,
        e: &S<Expr>,
        name: &str,
        rec: Option<&S<Expr>>,
        fields: &[(String, S<Expr>)],
        base: usize,
    ) -> Option<Doc> {
        let flat = self.fmt_expr_inline(e, Mode::Flat)?;
        if !base.is_multiple_of(INDENT.len()) {
            return Some(text(flat));
        }
        let broken = self.fmt_record_break(name, rec, fields, base / INDENT.len());
        if wants_break(&e.node) {
            Some(text(broken))
        } else {
            Some(group(flat_alt(text(flat), text(broken))))
        }
    }

    // Each element of a delimited sequence, nested at `base + ITEM_NEST` (the
    // column a broken element lands at).
    fn seq_items(&self, elems: &[S<Expr>], base: usize) -> Option<Vec<Doc>> {
        let inner = base + ITEM_NEST;
        elems
            .iter()
            .map(|x| self.operand(x, inner, false))
            .collect()
    }

    // A call as a document. Interp strings round-trip through the inline printer;
    // a trailing-`with` call and an explicit-instance (`using`) call decline the
    // document path (they keep the string printer's flat form), as does any call
    // carrying a comment between its arguments.
    fn call_doc(&self, e: &S<Expr>, f: &S<Expr>, args: &[S<Expr>], base: usize) -> Option<Doc> {
        if let Some(s) = self.fmt_interp(f, args) {
            return Some(text(s));
        }
        if is_with_call(args) || self.has_comments(f.span.end, e.span.end) {
            return None;
        }
        match call_shape(f, args) {
            CallShape::Recv(recv) => {
                let recv_d = paren_doc(dot_recv_parens(&recv.node), self.expr_doc(recv, base)?);
                Some(concat([recv_d, text(kw::QUESTION)]))
            }
            CallShape::Dot((name, recv, rest)) => {
                let recv_d = paren_doc(dot_recv_parens(&recv.node), self.expr_doc(recv, base)?);
                Some(concat([
                    recv_d,
                    text(format!(".{name}")),
                    self.args_doc(rest, base)?,
                ]))
            }
            // Explicit-instance selection folds a `using` clause into the parens;
            // its broken form is delicate, so keep it on the string printer.
            CallShape::Inst(..) => None,
            CallShape::Plain(f, args) => {
                let callee = paren_doc(callee_parens(&f.node), self.expr_doc(f, base)?);
                Some(concat([callee, self.args_doc(args, base)?]))
            }
        }
    }

    // A call's argument parens. When the final argument is a delimited aggregate
    // (and everything before it fits on the head line) the parens stay put and
    // the aggregate breaks inside; otherwise the whole argument list is one group
    // that breaks to one argument per line.
    fn args_doc(&self, args: &[S<Expr>], base: usize) -> Option<Doc> {
        if let Some((last, init)) = args.split_last() {
            if call_hugs(&last.node) {
                let mut parts = vec![lparen()];
                for a in init {
                    parts.push(text(self.fmt_expr_inline(a, Mode::Flat)?));
                    parts.push(text(", "));
                }
                parts.push(self.expr_doc(last, base)?);
                parts.push(rparen());
                return Some(concat(parts));
            }
        }
        let items = self.seq_items(args, base)?;
        Some(seq_block(lparen(), rparen(), false, items))
    }

    // A binary-operator chain. The left spine of one precedence level flattens
    // into a single group so the whole run breaks together, leading operator at
    // `OP_NEST`; a higher-precedence operand is its own nested layout that breaks
    // only if it overflows, and parenthesization matches the inline printer.
    fn bin_doc(&self, op: BinOp, a: &S<Expr>, b: &S<Expr>, base: usize) -> Option<Doc> {
        let p = binop_prec(op);
        // Walk the left spine, collecting operators and right operands until a
        // node that is not a same-precedence extension of the chain.
        let mut ops_rev: Vec<BinOp> = Vec::new();
        let mut operands_rev: Vec<&S<Expr>> = Vec::new();
        let mut op_cur = op;
        let mut left = a;
        let mut right = b;
        loop {
            operands_rev.push(right);
            ops_rev.push(op_cur);
            match &left.node {
                Expr::Bin(o2, l2, r2)
                    if binop_prec(*o2) == p && !needs_left_paren(&left.node, op_cur, p) =>
                {
                    op_cur = *o2;
                    right = r2;
                    left = l2;
                }
                _ => break,
            }
        }
        operands_rev.push(left);
        operands_rev.reverse();
        ops_rev.reverse();
        let ops = ops_rev;
        let operands = operands_rev;

        let inner = base + OP_NEST;
        let left_paren = needs_left_paren(&operands[0].node, ops[0], p);
        let mut parts = vec![self.operand(operands[0], base, left_paren)?];
        for (i, o) in ops.iter().enumerate() {
            let rhs = operands[i + 1];
            let rp = needs_right_paren(&rhs.node, *o, p);
            let od = self.operand(rhs, inner, rp)?;
            parts.push(nest(
                OP_NEST,
                concat([line(), text(o.spelling().to_string()), space(), od]),
            ));
        }
        Some(group(concat(parts)))
    }

    // A `|>` pipeline. Left-associative like a binary chain: the head expression,
    // then one `|> stage` per line at `OP_NEST` when the pipeline breaks. A `let`
    // head is parenthesized, matching the offside pipe printer.
    fn pipe_doc(&self, x: &S<Expr>, f: &S<Expr>, base: usize) -> Option<Doc> {
        let mut stages_rev: Vec<&S<Expr>> = vec![f];
        let mut head = x;
        while let Expr::Pipe(x2, f2) = &head.node {
            stages_rev.push(f2);
            head = x2;
        }
        stages_rev.reverse();
        let inner = base + OP_NEST;
        let head_paren = matches!(head.node, Expr::Let(..));
        let mut parts = vec![self.operand(head, base, head_paren)?];
        for stage in stages_rev {
            parts.push(nest(
                OP_NEST,
                concat([
                    line(),
                    text(kw::PIPE_RIGHT),
                    space(),
                    self.operand(stage, inner, false)?,
                ]),
            ));
        }
        Some(group(concat(parts)))
    }

    // Render a value expression into a slot that starts at column `col` on a line
    // whose own indentation is `line_cols` columns. Width is budgeted from `col`
    // (the true cursor), while broken lines indent relative to `line_cols`, so a
    // call opened after `let x = ` breaks its arguments in from the `let`, not
    // from the parenthesis. `None` when the expression declines the document path.
    pub(super) fn render_expr(&self, e: &S<Expr>, line_cols: usize, col: usize) -> Option<String> {
        let doc = self.expr_doc(e, line_cols)?;
        let shift = isize::try_from(line_cols).unwrap_or(0) - isize::try_from(col).unwrap_or(0);
        let doc = if shift == 0 { doc } else { indent(shift, doc) };
        Some(pretty_at(&doc, LINE_WIDTH, col))
    }
}
