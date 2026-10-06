//! Pattern formatting. Patterns reuse marginalia's `Doc` layout engine (rather
//! than the hand-rolled width checks the expression printer uses) for their
//! nested ctor/tuple/record structure.

use marginalia::pretty::{
    block, comma, concat, lbrace, lbracket, lparen, pretty_at, pretty_flat, rbrace, rbracket,
    rparen, text, Block, Doc,
};

use super::lit::{fmt_char, fmt_float};
use super::{tuple_items, INDENT, LINE_WIDTH};
use crate::ast::{Pattern, S};
use crate::kw;
use crate::names::{CONS, NIL};

// Alternatives of an or-pattern always print on one line: `|` has no bracketing
// delimiter to break against, so a wrapped alternation would not round-trip to
// the same layout and the formatter would stop being idempotent.
fn or_doc(alts: &[S<Pattern>]) -> Doc {
    let mut items: Vec<Doc> = Vec::with_capacity(alts.len() * 2 - 1);
    for (i, a) in alts.iter().enumerate() {
        if i > 0 {
            items.push(text(format!(" {} ", kw::BAR)));
        }
        items.push(pat_doc(a));
    }
    concat(items)
}

fn is_nil(p: &Pattern) -> bool {
    matches!(p, Pattern::Ctor(n, subs) if n == NIL && subs.is_empty())
}

fn as_cons(p: &Pattern) -> Option<(&S<Pattern>, &S<Pattern>)> {
    match p {
        Pattern::Ctor(n, subs) if n == CONS => match subs.as_slice() {
            [h, t] => Some((h, t)),
            _ => None,
        },
        _ => None,
    }
}

// The elements of a spine that ends in `Nil`, the shape `[a, b]` prints.
fn closed_list(p: &S<Pattern>) -> Option<Vec<&S<Pattern>>> {
    let mut elems = Vec::new();
    let mut cur = p;
    while let Some((h, t)) = as_cons(&cur.node) {
        elems.push(h);
        cur = t;
    }
    (!elems.is_empty() && is_nil(&cur.node)).then_some(elems)
}

// A list pattern prints as its sugar: a spine ending in `Nil` as `[a, b]`, any
// other spine as `a :: b :: rest`. Patterns have no grouping parens, so a cons
// cell whose operand would need them (an open cons head, or an alternation on
// either side) keeps the explicit constructor.
fn list_doc(p: &S<Pattern>) -> Option<Doc> {
    if let Some(elems) = closed_list(p) {
        return Some(block(
            lbracket(),
            rbracket(),
            &comma(),
            elems.into_iter().map(pat_doc),
        ));
    }
    let mut heads = Vec::new();
    let mut cur = p;
    while let Some((h, t)) = as_cons(&cur.node) {
        let bare = |x: &S<Pattern>| !matches!(x.node, Pattern::Or(_));
        let open_head = as_cons(&h.node).is_some() && closed_list(h).is_none();
        if open_head || !bare(h) || !bare(t) {
            break;
        }
        heads.push(h);
        cur = t;
    }
    if heads.is_empty() {
        return None;
    }
    let mut items: Vec<Doc> = Vec::with_capacity(heads.len() * 2 + 1);
    for h in heads {
        items.push(pat_doc(h));
        items.push(text(format!(" {} ", kw::COLON_COLON)));
    }
    items.push(pat_doc(cur));
    Some(concat(items))
}

fn pat_doc(p: &S<Pattern>) -> Doc {
    if is_nil(&p.node) {
        return text(format!("{}{}", kw::LBRACKET, kw::RBRACKET));
    }
    if let Some(d) = list_doc(p) {
        return d;
    }
    match &p.node {
        Pattern::Wild => text("_"),
        Pattern::Var(x) => text(x.clone()),
        Pattern::Int(n) => text(n.to_string()),
        Pattern::Float(f) => text(fmt_float(*f)),
        Pattern::Char(c) => text(fmt_char(*c)),
        Pattern::Bool(b) => text(b.to_string()),
        Pattern::Ctor(name, subs) if subs.is_empty() => text(name.clone()),
        Pattern::Ctor(name, subs) => concat([
            text(name.clone()),
            block(lparen(), rparen(), &comma(), subs.iter().map(pat_doc)),
        ]),
        Pattern::Tuple(subs) => block(
            lparen(),
            rparen(),
            &comma(),
            tuple_items(subs.iter().map(pat_doc), false),
        ),
        Pattern::Record(name, fields, spread) => {
            let mut items: Vec<Doc> = fields
                .iter()
                .map(|(f, sub)| concat([text(format!("{f} = ")), pat_doc(sub)]))
                .collect();
            if *spread {
                items.push(text(kw::DOT_DOT));
            }
            let style = Block::default().padded();
            let style = if *spread { style } else { style.trailing() };
            concat([
                text(format!("{name} ")),
                style.of(lbrace(), rbrace(), &comma(), items),
            ])
        }
        Pattern::Or(alts) => or_doc(alts),
    }
}

pub(super) fn fmt_pat_inline(p: &S<Pattern>) -> String {
    pretty_flat(&pat_doc(p))
}

pub(super) fn fmt_pat(p: &S<Pattern>, indent: usize) -> String {
    pretty_at(&pat_doc(p), LINE_WIDTH, indent * INDENT.len())
}
