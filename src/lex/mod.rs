mod token;

use token::LexFail;
pub use token::Token;

use std::convert::Infallible;

use logos::Logos;
use marginalia::{TriviaLexer, TriviaTable};
use offsides::{LayoutConfig, LayoutLexer, LayoutMode, OpenerRule};

use crate::error::LexError;

pub type LexSpanned = (usize, Token, usize);

const fn opens_block(t: &Token) -> bool {
    matches!(
        t,
        Token::Eq
            | Token::Then
            | Token::Else
            | Token::FatArrow
            | Token::Of
            | Token::With
            | Token::Handler
            | Token::Fn
            | Token::Try
            | Token::Catch
            | Token::Transact
            | Token::Do
            | Token::Where
            // `loop <block>` opens directly; `while cond do <block>` opens at `do`.
            | Token::Loop
            // `without alloc <block>` opens after `alloc`; the conditional opener
            // rule keeps the postfix suffix (`: T without alloc = ..`) block-free.
            | Token::Alloc
    )
}

// `LexFail` offsets are absolute within the lexed slice; `base` is the
// slice's offset in `src` and `tok` the failing token's start.
const fn lift(e: LexFail, base: usize, tok: usize) -> LexError {
    match e {
        LexFail::Invalid => LexError::Invalid { offset: base + tok },
        LexFail::Hole { offset } => LexError::UnterminatedHole {
            offset: base + offset,
        },
        LexFail::Str { offset } => LexError::UnterminatedString {
            offset: base + offset,
        },
    }
}

// Interpolated literals split recursively, so a hole may itself contain one.
fn emit(
    start: usize,
    end: usize,
    tok: Token,
    src: &str,
    out: &mut Vec<LexSpanned>,
) -> Result<(), LexError> {
    if matches!(tok, Token::StringLit(_)) && token::has_hole(&src[start + 1..end - 1]) {
        split_interp(start, end, src, out)
    } else {
        out.push((start, tok, end));
        Ok(())
    }
}

// `"a {x} b"` splits into InterpStart("a ") / hole tokens / InterpEnd(" b").
// Segments are recooked here and hole text is re-lexed at its absolute offset,
// so spans inside holes point at the real source and the layout pass never
// sees a string-internal `{`.
fn split_interp(
    start: usize,
    end: usize,
    src: &str,
    out: &mut Vec<LexSpanned>,
) -> Result<(), LexError> {
    let inner: Vec<(usize, char)> = src[start + 1..end - 1]
        .char_indices()
        .map(|(i, c)| (start + 1 + i, c))
        .collect();
    let mut i = 0;
    let mut seg = String::new();
    let mut seg_from = start;
    let mut first = true;
    while i < inner.len() {
        let (p, c) = inner[i];
        match c {
            '\\' => {
                let &(ep, ec) = inner.get(i + 1).ok_or(LexError::Invalid { offset: p })?;
                seg.push(token::unescape(ec).ok_or(LexError::Invalid { offset: ep })?);
                i += 2;
            }
            '{' => {
                // The hole runs to its matching `}`, found by the shared automaton
                // so a nested string literal's quotes and braces are not miscounted.
                let Some((close, next)) = token::Scanner::scan_hole(&inner, i + 1) else {
                    return Err(LexError::UnterminatedHole { offset: p });
                };
                if src[p + 1..close].trim().is_empty() {
                    return Err(LexError::EmptyHole { offset: p });
                }
                let text = std::mem::take(&mut seg);
                let tok = if first {
                    Token::InterpStart(text)
                } else {
                    Token::InterpMid(text)
                };
                out.push((seg_from, tok, p + 1));
                first = false;
                for (res, sp) in Token::lexer(&src[p + 1..close]).spanned() {
                    match res {
                        Ok(t) => emit(p + 1 + sp.start, p + 1 + sp.end, t, src, out)?,
                        Err(e) => return Err(lift(e, p + 1, sp.start)),
                    }
                }
                seg_from = close;
                i = next;
            }
            c => {
                seg.push(c);
                i += 1;
            }
        }
    }
    out.push((seg_from, Token::InterpEnd(seg), end));
    Ok(())
}

/// # Errors
/// Fails on invalid tokens or unterminated strings.
pub fn lex_raw(src: &str) -> Result<(Vec<LexSpanned>, TriviaTable), LexError> {
    let mut split = Vec::new();
    for (res, span) in Token::lexer(src).spanned() {
        match res {
            Ok(tok) => emit(span.start, span.end, tok, src, &mut split)?,
            Err(e) => return Err(lift(e, 0, span.start)),
        }
    }
    let mut trivia = TriviaLexer::new(split.into_iter().map(Ok::<_, usize>), src);
    let mut clean = Vec::new();
    for item in &mut trivia {
        match item {
            Ok(t) => clean.push(t),
            Err(offset) => return Err(LexError::Invalid { offset }),
        }
    }
    let table = trivia.into_table();
    Ok((clean, table))
}

/// # Errors
/// Fails on invalid tokens, unterminated strings, or layout errors.
pub fn lex(src: &str) -> Result<(Vec<LexSpanned>, TriviaTable), LexError> {
    let (clean, table) = lex_raw(src)?;
    let cfg = LayoutConfig::new(opens_block)
        .with_mode(LayoutMode::Eager)
        .with_opener_rule(OpenerRule::Conditional)
        .with_brackets(
            |t| matches!(t, Token::LParen | Token::LBracket | Token::LBrace),
            |t| matches!(t, Token::RParen | Token::RBracket | Token::RBrace),
        )
        .with_carry_openers(|t| matches!(t, Token::Fn));
    // The layout pass only forwards errors from its input, which is infallible.
    let layered = LayoutLexer::new(clean.into_iter().map(Ok::<_, Infallible>), src, cfg);
    let tokens = layered
        .map(|r| match r {
            Ok(t) => t,
        })
        .collect();
    Ok((tokens, table))
}
