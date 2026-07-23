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

use crate::kw;
use crate::syntax::ast::{IntLit, Suffix};

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

// Logos callbacks must take `&mut Lexer` even when read-only.
#[allow(clippy::needless_pass_by_ref_mut)]
fn parse_float(lex: &mut Lexer<'_, Token>) -> Result<f64, LexFail> {
    let s = lex.slice();
    if let Some(off) = bad_separator(s) {
        return Err(LexFail::NumberSep {
            offset: lex.span().start + off,
        });
    }
    strip_separators(s).parse().map_err(|_| LexFail::Invalid)
}

// Logos callbacks must take `&mut Lexer` even when read-only.
#[allow(clippy::needless_pass_by_ref_mut)]
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

impl Token {
    const fn text(&self) -> &'static str {
        match self {
            Self::Fn => kw::FN,
            Self::Fip => kw::FIP,
            Self::Fbip => kw::FBIP,
            Self::Replayable => kw::REPLAYABLE,
            Self::Logic => kw::LOGIC,
            Self::Requires => kw::REQUIRES,
            Self::Ensures => kw::ENSURES,
            Self::Pub => kw::PUB,
            Self::Import => kw::IMPORT,
            Self::As => kw::AS,
            Self::Type => kw::TYPE,
            Self::Newtype => kw::NEWTYPE,
            Self::Stable => kw::STABLE,
            Self::Opaque => kw::OPAQUE,
            Self::Effect => kw::EFFECT,
            Self::KwError => kw::ERROR,
            Self::Throw => kw::THROW,
            Self::Try => kw::TRY,
            Self::Catch => kw::CATCH,
            Self::Transact => kw::TRANSACT,
            Self::Probe => kw::PROBE,
            Self::Alias => kw::ALIAS,
            Self::Class => kw::CLASS,
            Self::Instance => kw::INSTANCE,
            Self::Canonical => kw::CANONICAL,
            Self::Pattern => kw::PATTERN,
            Self::Deriving => kw::DERIVING,
            Self::Where => kw::WHERE,
            Self::Given => kw::GIVEN,
            Self::Handle => kw::HANDLE,
            Self::With => kw::WITH,
            Self::Handler => kw::HANDLER,
            Self::Mask => kw::MASK,
            Self::Val => kw::VAL,
            Self::Return => kw::RETURN,
            Self::Let => kw::LET,
            Self::Var => kw::VAR,
            Self::Borrow => kw::BORROW,
            Self::In => kw::IN,
            Self::For => kw::FOR,
            Self::While => kw::WHILE,
            Self::Loop => kw::LOOP,
            Self::Break => kw::BREAK,
            Self::Continue => kw::CONTINUE,
            Self::Do => kw::DO,
            Self::If => kw::IF,
            Self::Then => kw::THEN,
            Self::Else => kw::ELSE,
            Self::Elif => kw::ELIF,
            Self::Match => kw::MATCH,
            Self::Of => kw::OF,
            Self::Each => kw::EACH,
            Self::Forall => kw::FORALL,
            Self::True => kw::TRUE,
            Self::False => kw::FALSE,
            Self::Using => kw::USING,
            Self::KwInt => kw::TY_INT,
            Self::KwBool => kw::TY_BOOL,
            Self::KwUnit => kw::TY_UNIT,
            Self::KwFloat => kw::TY_FLOAT,
            Self::KwChar => kw::TY_CHAR,
            Self::KwString => kw::TY_STRING,
            Self::KwI64 => kw::TY_I64,
            Self::KwU64 => kw::TY_U64,
            Self::Arrow => kw::ARROW,
            Self::LArrow => kw::LARROW,
            Self::FatArrow => kw::FAT_ARROW,
            Self::EqDot => kw::EQ_DOT,
            Self::NeDot => kw::NE_DOT,
            Self::LeDot => kw::LE_DOT,
            Self::GeDot => kw::GE_DOT,
            Self::LtDot => kw::LT_DOT,
            Self::GtDot => kw::GT_DOT,
            Self::EqEq => kw::EQ_EQ,
            Self::Ne => kw::NE,
            Self::Le => kw::LE,
            Self::Ge => kw::GE,
            Self::Lt => kw::LT,
            Self::Gt => kw::GT,
            Self::Eq => kw::EQ,
            Self::AmpAmp => kw::AMP_AMP,
            Self::PipePipe => kw::PIPE_PIPE,
            Self::PipeRight => kw::PIPE_RIGHT,
            Self::CompRight => kw::COMP_RIGHT,
            Self::CompLeft => kw::COMP_LEFT,
            Self::Bar => kw::BAR,
            Self::Lambda => kw::LAMBDA,
            Self::PlusDot => kw::PLUS_DOT,
            Self::MinusDot => kw::MINUS_DOT,
            Self::PlusEq => kw::PLUS_EQ,
            Self::MinusEq => kw::MINUS_EQ,
            Self::StarEq => kw::STAR_EQ,
            Self::PercentEq => kw::PERCENT_EQ,
            Self::Plus => kw::PLUS,
            Self::Minus => kw::MINUS,
            Self::StarDot => kw::STAR_DOT,
            Self::Star => kw::STAR,
            Self::SlashDot => kw::SLASH_DOT,
            Self::Slash => kw::SLASH,
            Self::Percent => kw::PERCENT,
            Self::Caret => kw::CARET,
            Self::LParen => kw::LPAREN,
            Self::RParen => kw::RPAREN,
            Self::LBrace => kw::LBRACE,
            Self::RBrace => kw::RBRACE,
            Self::LBracket => kw::LBRACKET,
            Self::RBracket => kw::RBRACKET,
            Self::Comma => kw::COMMA,
            Self::ColonEq => kw::COLON_EQ,
            Self::Colon => kw::COLON,
            Self::Bang => kw::BANG,
            Self::At => kw::AT,
            Self::Hash => kw::HASH,
            Self::DotDot => kw::DOT_DOT,
            Self::Dot => kw::DOT,
            Self::QuestionQuestion => kw::QUESTION_QUESTION,
            Self::QuestionDot => kw::QUESTION_DOT,
            Self::Question => kw::QUESTION,
            Self::Tilde => kw::TILDE,
            // Value-carrying and layout-virtual tokens have no fixed spelling;
            // they are enumerated (rather than caught by `_`) so a newly added
            // token cannot ship without an explicit spelling decision here.
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
    use super::Token;
    use Token::{Ident, InterpEnd, InterpStart};

    use std::collections::HashSet;

    use crate::error::LexError;
    use crate::kw;
    use crate::lex::highlight::tok_class;
    use crate::syntax::ast::{BigInt, IntLit, Suffix};

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

    // Every fixed token paired with its canonical spelling. This is the bridge
    // the logos `#[token("...")]` attributes cannot express directly (the macro
    // needs a literal), so the test below makes each attribute verified against
    // the `kw` const rather than silently free to drift from it.
    fn fixed_tokens() -> Vec<(Token, &'static str)> {
        vec![
            (Token::Fn, kw::FN),
            (Token::Fip, kw::FIP),
            (Token::Fbip, kw::FBIP),
            (Token::Replayable, kw::REPLAYABLE),
            (Token::Logic, kw::LOGIC),
            (Token::Requires, kw::REQUIRES),
            (Token::Ensures, kw::ENSURES),
            (Token::Pub, kw::PUB),
            (Token::Import, kw::IMPORT),
            (Token::As, kw::AS),
            (Token::Type, kw::TYPE),
            (Token::Newtype, kw::NEWTYPE),
            (Token::Stable, kw::STABLE),
            (Token::Opaque, kw::OPAQUE),
            (Token::Effect, kw::EFFECT),
            (Token::KwError, kw::ERROR),
            (Token::Throw, kw::THROW),
            (Token::Try, kw::TRY),
            (Token::Catch, kw::CATCH),
            (Token::Transact, kw::TRANSACT),
            (Token::Probe, kw::PROBE),
            (Token::Alias, kw::ALIAS),
            (Token::Class, kw::CLASS),
            (Token::Instance, kw::INSTANCE),
            (Token::Canonical, kw::CANONICAL),
            (Token::Pattern, kw::PATTERN),
            (Token::Deriving, kw::DERIVING),
            (Token::Where, kw::WHERE),
            (Token::Given, kw::GIVEN),
            (Token::Handle, kw::HANDLE),
            (Token::With, kw::WITH),
            (Token::Handler, kw::HANDLER),
            (Token::Mask, kw::MASK),
            (Token::Val, kw::VAL),
            (Token::Return, kw::RETURN),
            (Token::Let, kw::LET),
            (Token::Var, kw::VAR),
            (Token::Borrow, kw::BORROW),
            (Token::In, kw::IN),
            (Token::For, kw::FOR),
            (Token::While, kw::WHILE),
            (Token::Loop, kw::LOOP),
            (Token::Break, kw::BREAK),
            (Token::Continue, kw::CONTINUE),
            (Token::Do, kw::DO),
            (Token::If, kw::IF),
            (Token::Then, kw::THEN),
            (Token::Else, kw::ELSE),
            (Token::Elif, kw::ELIF),
            (Token::Match, kw::MATCH),
            (Token::Of, kw::OF),
            (Token::Each, kw::EACH),
            (Token::Forall, kw::FORALL),
            (Token::True, kw::TRUE),
            (Token::False, kw::FALSE),
            (Token::Using, kw::USING),
            (Token::KwInt, kw::TY_INT),
            (Token::KwBool, kw::TY_BOOL),
            (Token::KwUnit, kw::TY_UNIT),
            (Token::KwFloat, kw::TY_FLOAT),
            (Token::KwChar, kw::TY_CHAR),
            (Token::KwString, kw::TY_STRING),
            (Token::KwI64, kw::TY_I64),
            (Token::KwU64, kw::TY_U64),
            (Token::Arrow, kw::ARROW),
            (Token::LArrow, kw::LARROW),
            (Token::FatArrow, kw::FAT_ARROW),
            (Token::EqDot, kw::EQ_DOT),
            (Token::NeDot, kw::NE_DOT),
            (Token::LeDot, kw::LE_DOT),
            (Token::GeDot, kw::GE_DOT),
            (Token::LtDot, kw::LT_DOT),
            (Token::GtDot, kw::GT_DOT),
            (Token::EqEq, kw::EQ_EQ),
            (Token::Ne, kw::NE),
            (Token::Le, kw::LE),
            (Token::Ge, kw::GE),
            (Token::Lt, kw::LT),
            (Token::Gt, kw::GT),
            (Token::Eq, kw::EQ),
            (Token::AmpAmp, kw::AMP_AMP),
            (Token::PipePipe, kw::PIPE_PIPE),
            (Token::PipeRight, kw::PIPE_RIGHT),
            (Token::CompRight, kw::COMP_RIGHT),
            (Token::CompLeft, kw::COMP_LEFT),
            (Token::Bar, kw::BAR),
            (Token::Lambda, kw::LAMBDA),
            (Token::PlusDot, kw::PLUS_DOT),
            (Token::MinusDot, kw::MINUS_DOT),
            (Token::PlusEq, kw::PLUS_EQ),
            (Token::MinusEq, kw::MINUS_EQ),
            (Token::StarEq, kw::STAR_EQ),
            (Token::PercentEq, kw::PERCENT_EQ),
            (Token::Plus, kw::PLUS),
            (Token::Minus, kw::MINUS),
            (Token::StarDot, kw::STAR_DOT),
            (Token::Star, kw::STAR),
            (Token::SlashDot, kw::SLASH_DOT),
            (Token::Slash, kw::SLASH),
            (Token::Percent, kw::PERCENT),
            (Token::LParen, kw::LPAREN),
            (Token::RParen, kw::RPAREN),
            (Token::LBrace, kw::LBRACE),
            (Token::RBrace, kw::RBRACE),
            (Token::LBracket, kw::LBRACKET),
            (Token::RBracket, kw::RBRACKET),
            (Token::Comma, kw::COMMA),
            (Token::ColonEq, kw::COLON_EQ),
            (Token::Colon, kw::COLON),
            (Token::Bang, kw::BANG),
            (Token::At, kw::AT),
            (Token::Hash, kw::HASH),
            (Token::DotDot, kw::DOT_DOT),
            (Token::Dot, kw::DOT),
            (Token::QuestionQuestion, kw::QUESTION_QUESTION),
            (Token::QuestionDot, kw::QUESTION_DOT),
            (Token::Question, kw::QUESTION),
            (Token::Tilde, kw::TILDE),
        ]
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
        let path = format!("{}/{rel}", env!("CARGO_MANIFEST_DIR"));
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
