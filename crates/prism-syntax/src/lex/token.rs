use logos::Lexer;
use logos::Logos;

// Decode one single-character string/char escape to its char. The supported set
// is exactly what the formatter's re-escaper can reproduce, so every accepted
// escape round-trips: each decoded value maps back to one escape spelling.
//
// Numeric and unicode escapes (`\0`, `\xNN`, `\u{...}`) are deliberately absent.
// Each is many-to-one on the decoded value (`\x41`, `\u{41}`, and a bare `A` all
// decode to `A`), so the decoded string keeps no record of which spelling the
// writer used and the formatter would reprint the bare character rather than the
// escape, breaking idempotence. An unknown escape therefore returns None and the
// caller raises a clean lex error instead of silently decoding it.
pub(super) const fn unescape(c: char) -> Option<char> {
    Some(match c {
        'n' => '\n',
        't' => '\t',
        'r' => '\r',
        '"' => '"',
        '\\' => '\\',
        '{' => '{',
        '}' => '}',
        _ => return None,
    })
}

// An unescaped `{` marks an interpolated literal; its raw inner text is kept
// so the lexer split pass can recook segments and re-lex hole expressions.
pub(super) fn has_hole(inner: &str) -> bool {
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => {
                chars.next();
            }
            '{' => return true,
            _ => {}
        }
    }
    false
}

// A single regex cannot lex interpolated strings: a hole may contain nested
// string literals whose quotes and braces must not end the outer token. The
// callback scans from the opening quote with a stack of hole depths, one per
// string nesting level. `LexFail` offsets are absolute in the lexed slice.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum LexFail {
    #[default]
    Invalid,
    Hole {
        offset: usize,
    },
    Str {
        offset: usize,
    },
    // A digit separator `_` not flanked by two digits (leading, trailing,
    // doubled, or adjacent to `.`/`e`/an exponent sign). Offset is relative to
    // the lexed slice, lifted to an absolute source offset like the others.
    NumberSep {
        offset: usize,
    },
}

// The string/hole automaton, shared by the string-literal callback and the
// interpolation splitter: a stack of brace depths, one frame per string
// nesting level, with escapes skipped. `step` consumes one char and reports
// when the region closes (the outer quote for a string literal, the matching
// brace for a hole).
pub(super) struct Scanner {
    depth: Vec<usize>,
    quotes: Vec<usize>,
    braces: Vec<usize>,
    esc: bool,
    hole: bool,
}

impl Scanner {
    pub(super) fn string(open_quote: usize) -> Self {
        Self {
            depth: vec![0],
            quotes: vec![open_quote],
            braces: Vec::new(),
            esc: false,
            hole: false,
        }
    }

    pub(super) fn hole() -> Self {
        Self {
            depth: vec![1],
            quotes: Vec::new(),
            braces: Vec::new(),
            esc: false,
            hole: true,
        }
    }

    pub(super) fn step(&mut self, at: usize, c: char) -> bool {
        if std::mem::take(&mut self.esc) {
            return false;
        }
        // `depth` is non-empty for the whole scan: it starts non-empty and the
        // only `pop` (a closing quote) ends the scan via the `true` return. An
        // empty top frame can only mean the region already closed, so degrade
        // to "closed" / no-op rather than panic on malformed re-entry.
        let Some(&top) = self.depth.last() else {
            return true;
        };
        match c {
            '\\' => self.esc = true,
            '"' if top == 0 => {
                self.depth.pop();
                self.quotes.pop();
                return self.depth.is_empty();
            }
            '"' => {
                self.depth.push(0);
                self.quotes.push(at);
            }
            '{' => {
                if let Some(d) = self.depth.last_mut() {
                    *d += 1;
                }
                self.braces.push(at);
            }
            '}' if top > 0 => {
                if let Some(d) = self.depth.last_mut() {
                    *d -= 1;
                }
                self.braces.pop();
                return self.hole && self.depth == [0];
            }
            _ => {}
        }
        false
    }

    // Find the `}` that closes a hole whose text starts at `inner[from]`, driving
    // this automaton so a nested string literal's own quotes and braces never end
    // the hole early. `inner` is the string body as (absolute byte offset, char)
    // pairs. Returns the closing brace's byte offset and the index one past it in
    // `inner`, or None when the hole is never closed.
    pub(super) fn scan_hole(inner: &[(usize, char)], from: usize) -> Option<(usize, usize)> {
        let mut sc = Self::hole();
        let mut j = from;
        while let Some(&(at, c)) = inner.get(j) {
            j += 1;
            if sc.step(at, c) {
                return Some((at, j));
            }
        }
        None
    }

    // Runs on the malformed-input path (string or hole never closed), so it
    // must yield a diagnostic, never panic: an empty marker stack falls back
    // to the other region's opener, then to offset 0.
    pub(super) fn unterminated(&self) -> LexFail {
        if self.depth.last().is_some_and(|d| *d > 0) {
            match self.braces.last() {
                Some(&offset) => LexFail::Hole { offset },
                None => LexFail::Str {
                    offset: self.quotes.last().copied().unwrap_or(0),
                },
            }
        } else {
            match self.quotes.last() {
                Some(&offset) => LexFail::Str { offset },
                None => LexFail::Hole {
                    offset: self.braces.last().copied().unwrap_or(0),
                },
            }
        }
    }
}

fn parse_string(lex: &mut Lexer<'_, Token>) -> Result<String, LexFail> {
    let base = lex.span().end;
    let rem = lex.remainder();
    let mut sc = Scanner::string(base - 1);
    for (i, c) in rem.char_indices() {
        if sc.step(base + i, c) {
            lex.bump(i + 1);
            return cook(&rem[..i]);
        }
    }
    Err(sc.unterminated())
}

/// The opening delimiter of a raw multiline string, `r"""`. The `#[token]`
/// attribute below must spell it literally, since the derive macro takes only a
/// literal; `open_matches_token` pins the two together.
pub(crate) const RAW_OPEN: &str = "r\"\"\"";

/// The closing delimiter, `"""`: the opener without its `r`.
pub(crate) const RAW_CLOSE: &str = "\"\"\"";

/// Whether a raw multiline string opens at `at` in `src`. The lexer folds the
/// raw form into the ordinary string token, since a raw literal denotes an
/// ordinary string; this is how the two passes that must tell them apart do so:
/// the interpolation splitter (a raw body has no holes) and the formatter (a raw
/// body is reprinted as written).
pub(crate) fn starts_raw(src: &str, at: usize) -> bool {
    src.get(at..).is_some_and(|s| s.starts_with(RAW_OPEN))
}

// A raw multiline string runs verbatim to the next `"""`: no escapes, no
// interpolation, and no way to spell the closing delimiter inside the body.
fn parse_raw_string(lex: &mut Lexer<'_, Token>) -> Result<String, LexFail> {
    let rem = lex.remainder();
    let Some(end) = rem.find(RAW_CLOSE) else {
        return Err(LexFail::Str {
            offset: lex.span().start,
        });
    };
    lex.bump(end + RAW_CLOSE.len());
    Ok(dedent(&rem[..end]))
}

// The leading run of spaces and tabs, i.e. a line's indentation.
fn indent_of(line: &str) -> &str {
    let width = line
        .find(|c: char| c != ' ' && c != '\t')
        .unwrap_or(line.len());
    &line[..width]
}

// The longest prefix both indents share, so a body mixing spaces and tabs is
// stripped only as far as the two agree rather than by a count that would cut
// one line's tab off against another's space.
fn common_indent<'a>(a: &'a str, b: &str) -> &'a str {
    let width = a.bytes().zip(b.bytes()).take_while(|(x, y)| x == y).count();
    &a[..width]
}

// The body of a raw literal, laid out the way it reads in source: the newline
// each delimiter sits against is not part of the text, and the indentation the
// whole block shares is the source's, not the string's. What survives is the
// bytes and the newlines between them.
fn dedent(body: &str) -> String {
    let opened = body.strip_prefix(indent_of(body)).unwrap_or(body);
    let body = opened.strip_prefix('\n').unwrap_or(body);
    let closed = body.trim_end_matches([' ', '\t']);
    let body = closed.strip_suffix('\n').unwrap_or(body);
    // `split` rather than `lines`, so a body that ends in a newline keeps it and
    // a stray `\r` stays the byte the author wrote.
    let blank = |line: &&str| line.trim().is_empty();
    let margin = body
        .split('\n')
        .filter(|line| !blank(line))
        .map(indent_of)
        .reduce(common_indent)
        .unwrap_or_default();
    body.split('\n')
        .map(|line| {
            if blank(&line) {
                ""
            } else {
                line.strip_prefix(margin).unwrap_or(line)
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn parse_char(lex: &Lexer<'_, Token>) -> Option<char> {
    let s = lex.slice();
    let inner = &s[1..s.len() - 1];
    let mut cs = inner.chars();
    let c = cs.next()?;
    if c == '\\' {
        let e = cs.next()?;
        if e == '\'' {
            Some('\'')
        } else {
            unescape(e)
        }
    } else {
        Some(c)
    }
}

fn cook(inner: &str) -> Result<String, LexFail> {
    if has_hole(inner) {
        return Ok(inner.to_owned());
    }
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            let e = chars.next().and_then(unescape).ok_or(LexFail::Invalid)?;
            out.push(e);
        } else {
            out.push(c);
        }
    }
    Ok(out)
}
use marginalia::{BuiltinKind, Classify, TriviaPiece};

use crate::ast::{IntLit, Suffix};
use crate::kw;

// A digit separator `_` is admissible only flanked by two ASCII digits. Returns
// the byte offset (within `s`) of the first misplaced separator, catching the
// leading, trailing, doubled, and adjacent-to-`.`/`e`/sign cases in one rule.
fn bad_separator(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    b.iter().enumerate().find_map(|(i, &c)| {
        let flanked = c == b'_'
            && i > 0
            && b[i - 1].is_ascii_digit()
            && b.get(i + 1).is_some_and(u8::is_ascii_digit);
        (c == b'_' && !flanked).then_some(i)
    })
}

// Drop the digit separators so the numeric value parses. Callers validate
// placement with `bad_separator` first.
fn strip_separators(s: &str) -> String {
    s.chars().filter(|&c| c != '_').collect()
}

#[expect(
    clippy::needless_pass_by_ref_mut,
    reason = "the callback signature is fixed by the logos derive; this one \
              only reads the lexer"
)]
fn parse_float(lex: &mut Lexer<'_, Token>) -> Result<f64, LexFail> {
    let s = lex.slice();
    if let Some(off) = bad_separator(s) {
        return Err(LexFail::NumberSep {
            offset: lex.span().start + off,
        });
    }
    strip_separators(s).parse().map_err(|_| LexFail::Invalid)
}

#[expect(
    clippy::needless_pass_by_ref_mut,
    reason = "the callback signature is fixed by the logos derive; this one \
              only reads the lexer"
)]
fn parse_int(lex: &mut Lexer<'_, Token>) -> Result<IntLit, LexFail> {
    let s = lex.slice();
    let (digits, suffix) = match (s.strip_suffix("i64"), s.strip_suffix("u64")) {
        (Some(d), _) => (d, Suffix::I64),
        (None, Some(d)) => (d, Suffix::U64),
        (None, None) => (s, Suffix::None),
    };
    if let Some(off) = bad_separator(digits) {
        return Err(LexFail::NumberSep {
            offset: lex.span().start + off,
        });
    }
    // The regex guarantees `digits` is a non-empty run of digits and separators.
    let value = strip_separators(digits)
        .parse()
        .map_err(|_| LexFail::Invalid)?;
    Ok(IntLit { value, suffix })
}

#[derive(Clone, Debug, Logos, PartialEq)]
#[logos(skip r"[ \t\f\r\n]+", error = LexFail)]
pub enum Token {
    #[token("fn")]
    Fn,
    #[token("fip")]
    Fip,
    #[token("fbip")]
    Fbip,
    #[token("replayable")]
    Replayable,
    #[token("logic")]
    Logic,
    #[token("requires")]
    Requires,
    #[token("ensures")]
    Ensures,
    #[token("pub")]
    Pub,
    #[token("import")]
    Import,
    #[token("as")]
    As,
    #[token("type")]
    Type,
    #[token("newtype")]
    Newtype,
    #[token("stable")]
    Stable,
    #[token("opaque")]
    Opaque,
    #[token("effect")]
    Effect,
    #[token("error")]
    KwError,
    #[token("throw")]
    Throw,
    #[token("try")]
    Try,
    #[token("catch")]
    Catch,
    #[token("transact")]
    Transact,
    #[token("probe")]
    Probe,
    #[token("alias")]
    Alias,
    #[token("class")]
    Class,
    #[token("instance")]
    Instance,
    #[token("canonical")]
    Canonical,
    #[token("pattern")]
    Pattern,
    #[token("deriving")]
    Deriving,
    #[token("where")]
    Where,
    #[token("given")]
    Given,
    #[token("handle")]
    Handle,
    #[token("with")]
    With,
    #[token("handler")]
    Handler,
    #[token("mask")]
    Mask,
    #[token("val")]
    Val,
    #[token("return")]
    Return,
    #[token("let")]
    Let,
    #[token("var")]
    Var,
    #[token("borrow")]
    Borrow,
    #[token("in")]
    In,
    #[token("for")]
    For,
    #[token("while")]
    While,
    #[token("loop")]
    Loop,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("do")]
    Do,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("elif")]
    Elif,
    #[token("match")]
    Match,
    #[token("of")]
    Of,
    // Reserved only to spell the `each` traversal step in an update path.
    #[token("each")]
    Each,
    #[token("forall")]
    Forall,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("using")]
    Using,
    #[token("Int")]
    KwInt,
    #[token("Bool")]
    KwBool,
    #[token("Unit")]
    KwUnit,
    #[token("Float")]
    KwFloat,
    #[token("Char")]
    KwChar,
    #[token("String")]
    KwString,
    #[token("I64")]
    KwI64,
    #[token("U64")]
    KwU64,

    #[token("->")]
    Arrow,
    #[token("<-")]
    LArrow,
    #[token("=>")]
    FatArrow,
    #[token("==.")]
    EqDot,
    #[token("/=.")]
    NeDot,
    #[token("<=.")]
    LeDot,
    #[token(">=.")]
    GeDot,
    #[token("<.")]
    LtDot,
    #[token(">.")]
    GtDot,
    #[token("==")]
    EqEq,
    #[token("/=")]
    Ne,
    #[token("<=")]
    Le,
    #[token(">=")]
    Ge,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("=")]
    Eq,
    #[token("&&")]
    AmpAmp,
    #[token("||")]
    PipePipe,
    #[token("|>")]
    PipeRight,
    #[token(">>")]
    CompRight,
    #[token("<<")]
    CompLeft,
    #[token("|")]
    Bar,
    #[token("\\")]
    Lambda,
    #[token("+.")]
    PlusDot,
    #[token("-.")]
    MinusDot,
    // Compound assignment on a `var` (desugars to `x := x <op> e`). No `/=`
    // form: `/=` is already not-equal. Longest-match keeps these distinct from
    // the bare operators and the float-dot operators above.
    #[token("+=")]
    PlusEq,
    #[token("-=")]
    MinusEq,
    #[token("*=")]
    StarEq,
    #[token("%=")]
    PercentEq,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*.")]
    StarDot,
    #[token("*")]
    Star,
    #[token("/.")]
    SlashDot,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("^")]
    Caret,
    // The path-update modify operator, `{ r | f ~ g }`: apply `g` to the focus.
    #[token("~")]
    Tilde,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token(",")]
    Comma,
    #[token(":=")]
    ColonEq,
    #[token(":")]
    Colon,
    #[token("!")]
    Bang,
    // The usage-row sigil: `T @ fact`, `T @ {fact, fact}`. Only ever a free
    // token; `@` can never appear inside an identifier, which is what keeps the
    // internal mangled names (`op@f@n`, `Var@x@0`) unforgeable from source.
    #[token("@")]
    At,
    // The unboxed sigil. Admitted only in the unboxed-values surface: `#(...)`
    // unboxed tuples, `#{...}` unboxed records, and `e.#field` unboxed projection.
    // The grammar accepts it only in those positions, so `#` anywhere else is a
    // syntax error, and it can never sit inside an identifier: unboxed syntax is
    // always explicit at the use site.
    #[token("#")]
    Hash,
    #[token("..")]
    DotDot,
    #[token(".")]
    Dot,
    #[token("??")]
    QuestionQuestion,
    #[token("?.")]
    QuestionDot,
    #[token("?")]
    Question,

    // A digit separator `_` may sit between digits in the mantissa and exponent.
    // The mantissa's integer part must start with a digit (so a leading `_` stays
    // an identifier); the fractional and exponent runs admit `_` freely and the
    // callback rejects a misplaced one with a pointed message. Exponent notation
    // always denotes a Float, and the exponent sign lives here in the lexer, so it
    // never collides with the unary-minus operator.
    #[regex(
        r"[0-9][0-9_]*\.[0-9_]+([eE][+-]?[0-9_]+)?|[0-9][0-9_]*[eE][+-]?[0-9_]+",
        parse_float,
        priority = 4
    )]
    Float(f64),

    // The raw multiline form is the same token: it denotes an ordinary string,
    // and only its spelling differs. The literal here is `RAW_OPEN`, which the
    // derive macro cannot name.
    #[token("r\"\"\"", parse_raw_string, priority = 4)]
    #[token("\"", parse_string)]
    StringLit(String),

    #[regex(r"'(\\.|[^'\\\n])'", parse_char, priority = 4)]
    CharLit(char),

    #[regex(r"[0-9][0-9_]*(i64|u64)?", parse_int, priority = 3)]
    Int(IntLit),

    #[regex(r"[a-z_][A-Za-z0-9_]*", |l| l.slice().to_owned(), priority = 2)]
    Ident(String),

    #[regex(r"[A-Z][A-Za-z0-9_]*", |l| l.slice().to_owned(), priority = 2)]
    UIdent(String),

    // A dotted path led by an uppercase component: a module path in `import`
    // (`Data.Map`) or a single-qualifier reference at a use site (`Map.insert`,
    // `Map.Tree`). Lexed whole so `Foo.bar` never collides with field access.
    #[regex(r"[A-Z][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+", |l| l.slice().to_owned(), priority = 3)]
    QualName(String),

    #[regex(r"--[^\n]*", |l| l.slice().to_owned(), allow_greedy = true)]
    Comment(String),

    VOpen,
    VClose,
    VSemi,
    // A synthetic layout-block opener spliced in by the lexer after a `class`,
    // `instance`, or `effect` head, standing in for the `where` those forms
    // omit. It exists only to make the following indented members a layout body;
    // the layout pass consumes it as an opener and the lexer strips it before
    // the parser ever sees it, so no grammar rule mentions it.
    VHead,
    InterpStart(String),
    InterpMid(String),
    InterpEnd(String),
}

// The fixed tokens: every variant whose source spelling is one fixed string,
// each paired with the `kw` const that spells it. `Token::text` and the drift
// guards in this module's tests both expand from this one list, so a spelling
// cannot be recorded in one place and forgotten in the other. The enum's own
// `#[token("...")]` attributes cannot join it (the logos macro needs a literal,
// not a const), which is exactly what `spellings_round_trip` checks.
macro_rules! fixed_token_table {
    ($($variant:ident => $spelling:ident,)*) => {
        impl Token {
            const fn text(&self) -> &'static str {
                match self {
                    $(Self::$variant => kw::$spelling,)*
                    // Value-carrying and layout-virtual tokens have no fixed
                    // spelling; they are enumerated (rather than caught by `_`) so
                    // a newly added token cannot ship without an explicit spelling
                    // decision, either a row of the table or a name here.
                    Self::Float(_)
                    | Self::StringLit(_)
                    | Self::CharLit(_)
                    | Self::Int(_)
                    | Self::Ident(_)
                    | Self::UIdent(_)
                    | Self::QualName(_)
                    | Self::Comment(_)
                    | Self::VOpen
                    | Self::VClose
                    | Self::VSemi
                    | Self::VHead
                    | Self::InterpStart(_)
                    | Self::InterpMid(_)
                    | Self::InterpEnd(_) => "",
                }
            }
        }

        // Every fixed token paired with its canonical spelling, for the drift
        // guards. Generated from the same table as `Token::text`, so the guards
        // see every fixed token by construction rather than by hand.
        #[cfg(test)]
        fn fixed_tokens() -> Vec<(Token, &'static str)> {
            vec![$((Token::$variant, kw::$spelling)),*]
        }
    };
}

fixed_token_table! {
    Fn => FN,
    Fip => FIP,
    Fbip => FBIP,
    Replayable => REPLAYABLE,
    Logic => LOGIC,
    Requires => REQUIRES,
    Ensures => ENSURES,
    Pub => PUB,
    Import => IMPORT,
    As => AS,
    Type => TYPE,
    Newtype => NEWTYPE,
    Stable => STABLE,
    Opaque => OPAQUE,
    Effect => EFFECT,
    KwError => ERROR,
    Throw => THROW,
    Try => TRY,
    Catch => CATCH,
    Transact => TRANSACT,
    Probe => PROBE,
    Alias => ALIAS,
    Class => CLASS,
    Instance => INSTANCE,
    Canonical => CANONICAL,
    Pattern => PATTERN,
    Deriving => DERIVING,
    Where => WHERE,
    Given => GIVEN,
    Handle => HANDLE,
    With => WITH,
    Handler => HANDLER,
    Mask => MASK,
    Val => VAL,
    Return => RETURN,
    Let => LET,
    Var => VAR,
    Borrow => BORROW,
    In => IN,
    For => FOR,
    While => WHILE,
    Loop => LOOP,
    Break => BREAK,
    Continue => CONTINUE,
    Do => DO,
    If => IF,
    Then => THEN,
    Else => ELSE,
    Elif => ELIF,
    Match => MATCH,
    Of => OF,
    Each => EACH,
    Forall => FORALL,
    True => TRUE,
    False => FALSE,
    Using => USING,
    KwInt => TY_INT,
    KwBool => TY_BOOL,
    KwUnit => TY_UNIT,
    KwFloat => TY_FLOAT,
    KwChar => TY_CHAR,
    KwString => TY_STRING,
    KwI64 => TY_I64,
    KwU64 => TY_U64,
    Arrow => ARROW,
    LArrow => LARROW,
    FatArrow => FAT_ARROW,
    EqDot => EQ_DOT,
    NeDot => NE_DOT,
    LeDot => LE_DOT,
    GeDot => GE_DOT,
    LtDot => LT_DOT,
    GtDot => GT_DOT,
    EqEq => EQ_EQ,
    Ne => NE,
    Le => LE,
    Ge => GE,
    Lt => LT,
    Gt => GT,
    Eq => EQ,
    AmpAmp => AMP_AMP,
    PipePipe => PIPE_PIPE,
    PipeRight => PIPE_RIGHT,
    CompRight => COMP_RIGHT,
    CompLeft => COMP_LEFT,
    Bar => BAR,
    Lambda => LAMBDA,
    PlusDot => PLUS_DOT,
    MinusDot => MINUS_DOT,
    PlusEq => PLUS_EQ,
    MinusEq => MINUS_EQ,
    StarEq => STAR_EQ,
    PercentEq => PERCENT_EQ,
    Plus => PLUS,
    Minus => MINUS,
    StarDot => STAR_DOT,
    Star => STAR,
    SlashDot => SLASH_DOT,
    Slash => SLASH,
    Percent => PERCENT,
    Caret => CARET,
    LParen => LPAREN,
    RParen => RPAREN,
    LBrace => LBRACE,
    RBrace => RBRACE,
    LBracket => LBRACKET,
    RBracket => RBRACKET,
    Comma => COMMA,
    ColonEq => COLON_EQ,
    Colon => COLON,
    Bang => BANG,
    At => AT,
    Hash => HASH,
    DotDot => DOT_DOT,
    Dot => DOT,
    QuestionQuestion => QUESTION_QUESTION,
    QuestionDot => QUESTION_DOT,
    Question => QUESTION,
    Tilde => TILDE,
}

impl Token {
    /// The canonical wire name of this token kind, the spelling the versioned
    /// syntax artifacts use. Fixed tokens use their exact source spelling (via
    /// `Self::text`); value-carrying and virtual tokens use the grammar's
    /// terminal aliases, re-stated here as the one non-grammar home so an
    /// artifact reader and the grammar can never disagree. `Comment` and
    /// `VHead` never reach an artifact stream (comments are trivia, the head
    /// opener is consumed by the layout pass), but carry names so the mapping
    /// stays total.
    #[must_use]
    pub const fn wire_name(&self) -> &'static str {
        match self {
            Self::Ident(_) => "ident",
            Self::UIdent(_) => "uid",
            Self::QualName(_) => "qual",
            Self::Int(_) => "int",
            Self::Float(_) => "float",
            Self::CharLit(_) => "char",
            Self::StringLit(_) => "str",
            Self::InterpStart(_) => "istart",
            Self::InterpMid(_) => "imid",
            Self::InterpEnd(_) => "iend",
            Self::VOpen => "v{",
            Self::VClose => "v}",
            Self::VSemi => "v;",
            Self::VHead => "vhead",
            Self::Comment(_) => "comment",
            t => t.text(),
        }
    }

    /// The decoded payload of a value-carrying token, for the versioned syntax
    /// artifacts. `None` for fixed and virtual tokens. The original spelling is
    /// always recoverable from the token's source span; this is the decoded
    /// value (escapes resolved, digit separators stripped). Floats render via
    /// the shortest round-trip form so the payload is deterministic.
    #[must_use]
    pub fn wire_value(&self) -> Option<String> {
        match self {
            Self::Ident(s)
            | Self::UIdent(s)
            | Self::QualName(s)
            | Self::StringLit(s)
            | Self::InterpStart(s)
            | Self::InterpMid(s)
            | Self::InterpEnd(s)
            | Self::Comment(s) => Some(s.clone()),
            Self::Int(i) => Some(i.to_string()),
            Self::Float(x) => Some(format!("{x:?}")),
            Self::CharLit(c) => Some(c.to_string()),
            _ => None,
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(s) | Self::UIdent(s) => write!(f, "identifier '{s}'"),
            Self::QualName(s) => write!(f, "qualified name '{s}'"),
            Self::Int(_) => f.write_str("integer literal"),
            Self::Float(_) => f.write_str("float literal"),
            Self::CharLit(_) => f.write_str("char literal"),
            Self::StringLit(_) | Self::InterpStart(_) | Self::InterpMid(_) | Self::InterpEnd(_) => {
                f.write_str("string literal")
            }
            Self::Comment(_) => f.write_str("comment"),
            Self::VOpen | Self::VHead => f.write_str("start of block"),
            Self::VClose => f.write_str("end of block"),
            Self::VSemi => f.write_str("end of statement"),
            t => write!(f, "'{}'", t.text()),
        }
    }
}

impl offsides::Layout for Token {
    fn v_open() -> Self {
        Self::VOpen
    }
    fn v_close() -> Self {
        Self::VClose
    }
    fn v_sep() -> Self {
        Self::VSemi
    }
}

impl Eq for Token {}

impl std::hash::Hash for Token {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
    }
}

impl Classify for Token {
    fn trivia(&self) -> Option<TriviaPiece<'_>> {
        match self {
            Self::Comment(s) => Some(TriviaPiece {
                kind: BuiltinKind::Line,
                text: s,
            }),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{fixed_tokens, Token};
    use Token::{Ident, InterpEnd, InterpStart};

    use std::collections::HashSet;

    use crate::ast::{BigInt, IntLit, Suffix};
    use crate::error::LexError;
    use crate::lex::highlight::tok_class;

    // One raw literal is one ordinary string token: the body arrives with the
    // delimiter newlines and the shared indentation gone, the braces and
    // backslashes it contains are text rather than a hole or an escape, and the
    // source spelling reaches nobody but the formatter.
    #[test]
    fn a_raw_literal_is_a_string_token() {
        let raw = |s: &str| {
            let (toks, _) = crate::lex::lex_raw(s).unwrap_or_else(|e| panic!("`{s}`: {e:?}"));
            match toks.as_slice() {
                [(_, Token::StringLit(v), _)] => v.clone(),
                other => panic!("`{s}` did not lex to a single string: {other:?}"),
            }
        };
        assert_eq!(raw("r\"\"\"\n  a\n  b\n  \"\"\""), "a\nb");
        // A line indented past the margin keeps the difference; a blank line
        // contributes no margin of its own and comes back empty.
        assert_eq!(raw("r\"\"\"\n  a\n\n    b\n  \"\"\""), "a\n\n  b");
        // The newline before the closing delimiter is the delimiter's, so a
        // trailing newline in the value takes a blank line to spell.
        assert_eq!(raw("r\"\"\"\n  a\n\n  \"\"\""), "a\n");
        assert_eq!(raw("r\"\"\"one\"\"\""), "one");
        assert_eq!(raw("r\"\"\"{x} and \\n\"\"\""), "{x} and \\n");
        assert!(matches!(
            crate::lex::lex_raw("r\"\"\"never closed"),
            Err(LexError::UnterminatedString { .. })
        ));
    }

    // The `#[token]` attribute takes a literal, so the delimiter is spelled
    // twice; this is the seam that keeps the two spellings one delimiter.
    #[test]
    fn the_raw_delimiter_is_spelled_once() {
        let src = include_str!("token.rs");
        assert!(
            src.contains(&format!("#[token({:?}, parse_raw_string", super::RAW_OPEN)),
            "the raw-string token attribute no longer spells `RAW_OPEN`"
        );
        assert_eq!(super::RAW_OPEN, format!("r{}", super::RAW_CLOSE));
    }

    // Digit separators are cosmetic: they strip out to the same value in every
    // lane, and scientific notation always lexes to a Float. The exponent sign is
    // consumed by the lexer, so `1e-2` is one token, not `1e` minus `2`.
    #[test]
    fn numeric_separators_and_scientific() {
        let int = |s: &str| {
            let (toks, _) = crate::lex::lex_raw(s).unwrap_or_else(|e| panic!("`{s}`: {e:?}"));
            match toks.as_slice() {
                [(_, Token::Int(lit), _)] => lit.clone(),
                other => panic!("`{s}` did not lex to a single Int: {other:?}"),
            }
        };
        let float = |s: &str| {
            let (toks, _) = crate::lex::lex_raw(s).unwrap_or_else(|e| panic!("`{s}`: {e:?}"));
            match toks.as_slice() {
                [(_, Token::Float(f), _)] => *f,
                other => panic!("`{s}` did not lex to a single Float: {other:?}"),
            }
        };
        assert_eq!(int("1_000_000").value, BigInt::from(1_000_000));
        assert_eq!(int("1_000_000").suffix, Suffix::None);
        assert_eq!(int("10_00i64").suffix, Suffix::I64);
        assert_eq!(
            int("4_294_967_296u64").value,
            BigInt::from(4_294_967_296u64)
        );
        assert!((float("1_000.000_5") - 1000.0005).abs() < 1e-9);
        assert!((float("1e-2") - 0.01).abs() < 1e-12);
        assert!((float("1E3") - 1000.0).abs() < 1e-9);
        assert!((float("1_2.5e1_0") - 12.5e10).abs() < 1.0);
    }

    // A separator must sit between two digits; the misplaced forms are a pointed
    // lexer error, not a silent split into an identifier.
    #[test]
    fn bad_separators_rejected() {
        for s in ["1__0", "1000_", "1_.5", "1e_5", "1.5_"] {
            assert!(
                matches!(
                    crate::lex::lex_raw(s),
                    Err(LexError::NumberSeparator { .. })
                ),
                "`{s}` should be a NumberSeparator error"
            );
        }
    }

    // The reason the hole scanner is a stack automaton and not a brace count: a
    // string literal nested inside a hole carries its own `{`/`}`/`"`, none of
    // which may close the outer hole or string. Lex a hole containing a nested
    // interpolated string and confirm the outer literal splits into exactly one
    // start/end pair around re-lexed hole tokens (one of them itself a nested
    // start/end pair), with no stray brace ending the region early.
    #[test]
    fn hole_with_nested_interp_string() {
        let (toks, _) =
            crate::lex::lex_raw(r#""a {f("b {x} c")} d""#).expect("nested interp lexes");
        let kinds: Vec<&Token> = toks.iter().map(|(_, t, _)| t).collect();
        let starts = kinds.iter().filter(|t| matches!(t, InterpStart(_))).count();
        let ends = kinds.iter().filter(|t| matches!(t, InterpEnd(_))).count();
        // Two interpolated literals (the outer one and the one inside the hole),
        // each a balanced start..end pair: the nested `"`/`{`/`}` never ended the
        // outer region early, and the hole's `f(...)` re-lexed into real tokens.
        assert_eq!(starts, 2, "one InterpStart per interpolated literal");
        assert_eq!(ends, 2, "one InterpEnd per interpolated literal");
        assert!(
            kinds.iter().any(|t| matches!(t, Ident(s) if s == "f")),
            "the hole expression `f(..)` re-lexes to its own tokens"
        );
    }

    // The canonical spelling of every fixed token must (a) lex back to exactly
    // that token and (b) equal what `Token::text` reports. (a) guards the logos
    // attribute against drifting from its `kw` const; (b) guards `Token::text`.
    #[test]
    fn spellings_round_trip() {
        for (tok, spelling) in fixed_tokens() {
            let (toks, _) = crate::lex::lex_raw(spelling)
                .unwrap_or_else(|e| panic!("`{spelling}` failed to lex: {e:?}"));
            let lexed: Vec<&Token> = toks.iter().map(|(_, t, _)| t).collect();
            assert_eq!(
                lexed,
                vec![&tok],
                "`{spelling}` did not lex to a single {tok:?} \
                 (the logos #[token] attribute has drifted from its kw const)"
            );
            assert_eq!(
                tok.text(),
                spelling,
                "Token::text for {tok:?} disagrees with its kw const"
            );
        }
    }

    // No two fixed tokens may share a spelling.
    #[test]
    fn spellings_are_unique() {
        let mut spellings: Vec<&str> = fixed_tokens().iter().map(|(_, s)| *s).collect();
        spellings.sort_unstable();
        let n = spellings.len();
        spellings.dedup();
        assert_eq!(n, spellings.len(), "two fixed tokens share a spelling");
    }

    // The value-carrying and virtual tokens with their canonical wire names,
    // re-typed from the grammar's terminal aliases so the artifact vocabulary
    // and the grammar cannot drift apart silently.
    fn special_wire_names() -> Vec<(Token, &'static str)> {
        let int = IntLit {
            value: BigInt::from(0),
            suffix: Suffix::None,
        };
        vec![
            (Token::Ident(String::new()), "ident"),
            (Token::UIdent(String::new()), "uid"),
            (Token::QualName(String::new()), "qual"),
            (Token::Int(int), "int"),
            (Token::Float(0.0), "float"),
            (Token::CharLit('a'), "char"),
            (Token::StringLit(String::new()), "str"),
            (Token::InterpStart(String::new()), "istart"),
            (Token::InterpMid(String::new()), "imid"),
            (Token::InterpEnd(String::new()), "iend"),
            (Token::VOpen, "v{"),
            (Token::VClose, "v}"),
            (Token::VSemi, "v;"),
            (Token::VHead, "vhead"),
            (Token::Comment(String::new()), "comment"),
        ]
    }

    // Every token kind has a nonempty wire name, fixed tokens reuse their exact
    // spelling, the specials match the grammar's terminal aliases, and no two
    // kinds share a name. Together with `fixed_tokens` this covers the enum, so
    // the syntax artifacts' token vocabulary is pinned in one place.
    #[test]
    fn wire_names_total_and_unique() {
        let mut names: Vec<&str> = Vec::new();
        for (tok, spelling) in fixed_tokens() {
            assert_eq!(
                tok.wire_name(),
                spelling,
                "a fixed token's wire name must be its spelling"
            );
            names.push(spelling);
        }
        for (tok, expected) in special_wire_names() {
            assert_eq!(
                tok.wire_name(),
                expected,
                "{tok:?} wire name disagrees with the grammar terminal alias"
            );
            names.push(expected);
        }
        assert!(
            names.iter().all(|n| !n.is_empty()),
            "every wire name is nonempty"
        );
        let n = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(n, names.len(), "two token kinds share a wire name");
    }

    // Maximal identifier runs in `src`, as a set.
    fn words(src: &str) -> HashSet<&str> {
        src.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .filter(|w| !w.is_empty())
            .collect()
    }

    fn highlighter(rel: &str) -> String {
        let path = format!("{}/../../{rel}", env!("CARGO_MANIFEST_DIR"));
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
    }

    // The four keyword highlighters (this lexer's `tok_class`, the REPL
    // categorizer, the mdbook JS grammar, and the nvim syntax file) must agree on
    // the keyword vocabulary. `tok_class` and the REPL categorizer are exhaustive
    // `match`es, so the Rust compiler already pins those two: a new keyword token
    // that is not classified fails to compile. This test pins the two external
    // files, which the compiler cannot see: every fixed token the lexer paints as
    // a keyword, builtin type name, or boolean literal must also appear in each.
    //
    // The relation is subset, not equality: the external files may list contextual
    // keywords the lexer treats as ordinary identifiers (`total`, `assume`, the
    // handler verbs), so an extra word there is fine, a missing one is the drift.
    #[test]
    fn highlighter_keyword_lists_mirror_the_lexer() {
        let canonical: Vec<&'static str> = fixed_tokens()
            .into_iter()
            .filter(|(t, _)| matches!(tok_class(t), "kw" | "ty" | "lit"))
            .map(|(_, s)| s)
            .collect();

        // mdbook JS: the `keywords { keyword/literal/type }` object, which the
        // `contains:` array immediately follows.
        let js = highlighter("docs/theme/prism-highlight.js");
        let obj_start = js
            .find("keywords:")
            .expect("JS highlighter has a `keywords:` object");
        let obj_len = js[obj_start..]
            .find("contains:")
            .expect("the JS `keywords` object precedes the `contains:` array");
        let js_words = words(&js[obj_start..obj_start + obj_len]);

        // nvim: the vocabulary of every `syntax keyword prism*` line.
        let lua = highlighter("scripts/nvim/syntax/prism.lua");
        let lua_lines: String = lua
            .lines()
            .filter(|l| l.contains("syntax keyword"))
            .collect::<Vec<_>>()
            .join(" ");
        let lua_words = words(&lua_lines);

        for spelling in canonical {
            assert!(
                js_words.contains(spelling),
                "keyword `{spelling}` is missing from docs/theme/prism-highlight.js \
                 (its keyword list drifted from the lexer)"
            );
            assert!(
                lua_words.contains(spelling),
                "keyword `{spelling}` is missing from scripts/nvim/syntax/prism.lua \
                 (its keyword list drifted from the lexer)"
            );
        }
    }
}
