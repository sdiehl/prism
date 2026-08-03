//! Pattern formatting. Patterns reuse marginalia's `Doc` layout engine (rather
//! than the hand-rolled width checks the expression printer uses) for their
//! nested ctor/tuple/record structure.

use marginalia::pretty::{
    block, comma, concat, lbrace, lparen, pretty_at, pretty_flat, rbrace, rparen, text, Block, Doc,
};

use super::lit::{fmt_char, fmt_float};
use super::{tuple_items, INDENT, LINE_WIDTH};
use crate::ast::{Pattern, S};
use crate::kw;

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

fn pat_doc(p: &S<Pattern>) -> Doc {
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
