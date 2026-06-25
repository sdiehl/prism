//! Pattern formatting. Patterns reuse marginalia's `Doc` layout engine (rather
//! than the hand-rolled width checks the expression printer uses) for their
//! nested ctor/tuple/record structure.

use marginalia::pretty::{
    block, comma, concat, lbrace, lparen, pretty_at, pretty_flat, rbrace, rparen, text, Block, Doc,
};

use super::{fmt_char, fmt_float, INDENT, LINE_WIDTH};
use crate::kw;
use crate::syntax::ast::{Pattern, S};

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
        Pattern::Tuple(subs) => block(lparen(), rparen(), &comma(), subs.iter().map(pat_doc)),
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
    }
}

pub(super) fn fmt_pat_inline(p: &S<Pattern>) -> String {
    pretty_flat(&pat_doc(p))
}

pub(super) fn fmt_pat(p: &S<Pattern>, indent: usize) -> String {
    pretty_at(&pat_doc(p), LINE_WIDTH, indent * INDENT.len())
}
