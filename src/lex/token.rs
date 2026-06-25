use logos::Lexer;
use logos::Logos;

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

use crate::syntax::ast::{IntLit, Suffix};

// Logos callbacks must take `&mut Lexer` even when read-only.
#[allow(clippy::needless_pass_by_ref_mut)]
fn parse_float(lex: &mut Lexer<'_, Token>) -> Option<f64> {
    lex.slice().parse().ok()
}

// Logos callbacks must take `&mut Lexer` even when read-only.
#[allow(clippy::needless_pass_by_ref_mut)]
fn parse_int(lex: &mut Lexer<'_, Token>) -> Option<IntLit> {
    let s = lex.slice();
    let (digits, suffix) = match (s.strip_suffix("i64"), s.strip_suffix("u64")) {
        (Some(d), _) => (d, Suffix::I64),
        (None, Some(d)) => (d, Suffix::U64),
        (None, None) => (s, Suffix::None),
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some(IntLit {
        value: digits.parse().ok()?,
        suffix,
    })
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
    #[token("alias")]
    Alias,
    #[token("class")]
    Class,
    #[token("instance")]
    Instance,
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
    #[token("ctl")]
    Ctl,
    #[token("final")]
    Final,
    #[token("fun")]
    Fun,
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
    #[token("forall")]
    Forall,
    #[token("true")]
    True,
    #[token("false")]
    False,
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

    #[regex(
        r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?|[0-9]+[eE][+-]?[0-9]+",
        parse_float,
        priority = 4
    )]
    Float(f64),

    #[token("\"", parse_string)]
    StringLit(String),

    #[regex(r"'(\\.|[^'\\\n])'", parse_char, priority = 4)]
    CharLit(char),

    #[regex(r"[0-9]+(i64|u64)?", parse_int, priority = 3)]
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
    InterpStart(String),
    InterpMid(String),
    InterpEnd(String),
}

impl Token {
    const fn text(&self) -> &'static str {
        use crate::kw;
        match self {
            Self::Fn => kw::FN,
            Self::Fip => kw::FIP,
            Self::Fbip => kw::FBIP,
            Self::Pub => kw::PUB,
            Self::Import => kw::IMPORT,
            Self::As => kw::AS,
            Self::Type => kw::TYPE,
            Self::Newtype => kw::NEWTYPE,
            Self::Opaque => kw::OPAQUE,
            Self::Effect => kw::EFFECT,
            Self::KwError => kw::ERROR,
            Self::Throw => kw::THROW,
            Self::Try => kw::TRY,
            Self::Catch => kw::CATCH,
            Self::Transact => kw::TRANSACT,
            Self::Alias => kw::ALIAS,
            Self::Class => kw::CLASS,
            Self::Instance => kw::INSTANCE,
            Self::Pattern => kw::PATTERN,
            Self::Deriving => kw::DERIVING,
            Self::Where => kw::WHERE,
            Self::Given => kw::GIVEN,
            Self::Handle => kw::HANDLE,
            Self::With => kw::WITH,
            Self::Handler => kw::HANDLER,
            Self::Mask => kw::MASK,
            Self::Ctl => kw::CTL,
            Self::Final => kw::FINAL,
            Self::Fun => kw::FUN,
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
            Self::Forall => kw::FORALL,
            Self::True => kw::TRUE,
            Self::False => kw::FALSE,
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
            Self::DotDot => kw::DOT_DOT,
            Self::Dot => kw::DOT,
            Self::QuestionQuestion => kw::QUESTION_QUESTION,
            Self::QuestionDot => kw::QUESTION_DOT,
            Self::Question => kw::QUESTION,
            _ => "",
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
            Self::VOpen => f.write_str("start of block"),
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
    use crate::kw;

    // Every fixed token paired with its canonical spelling. This is the bridge
    // the logos `#[token("...")]` attributes cannot express directly (the macro
    // needs a literal), so the test below makes each attribute verified against
    // the `kw` const rather than silently free to drift from it.
    fn fixed_tokens() -> Vec<(Token, &'static str)> {
        vec![
            (Token::Fn, kw::FN),
            (Token::Fip, kw::FIP),
            (Token::Fbip, kw::FBIP),
            (Token::Pub, kw::PUB),
            (Token::Import, kw::IMPORT),
            (Token::As, kw::AS),
            (Token::Type, kw::TYPE),
            (Token::Newtype, kw::NEWTYPE),
            (Token::Opaque, kw::OPAQUE),
            (Token::Effect, kw::EFFECT),
            (Token::KwError, kw::ERROR),
            (Token::Throw, kw::THROW),
            (Token::Try, kw::TRY),
            (Token::Catch, kw::CATCH),
            (Token::Transact, kw::TRANSACT),
            (Token::Alias, kw::ALIAS),
            (Token::Class, kw::CLASS),
            (Token::Instance, kw::INSTANCE),
            (Token::Pattern, kw::PATTERN),
            (Token::Deriving, kw::DERIVING),
            (Token::Where, kw::WHERE),
            (Token::Given, kw::GIVEN),
            (Token::Handle, kw::HANDLE),
            (Token::With, kw::WITH),
            (Token::Handler, kw::HANDLER),
            (Token::Mask, kw::MASK),
            (Token::Ctl, kw::CTL),
            (Token::Final, kw::FINAL),
            (Token::Fun, kw::FUN),
            (Token::Val, kw::VAL),
            (Token::Return, kw::RETURN),
            (Token::Let, kw::LET),
            (Token::Var, kw::VAR),
            (Token::Borrow, kw::BORROW),
            (Token::In, kw::IN),
            (Token::For, kw::FOR),
            (Token::Do, kw::DO),
            (Token::If, kw::IF),
            (Token::Then, kw::THEN),
            (Token::Else, kw::ELSE),
            (Token::Elif, kw::ELIF),
            (Token::Match, kw::MATCH),
            (Token::Of, kw::OF),
            (Token::Forall, kw::FORALL),
            (Token::True, kw::TRUE),
            (Token::False, kw::FALSE),
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
            (Token::DotDot, kw::DOT_DOT),
            (Token::Dot, kw::DOT),
            (Token::QuestionQuestion, kw::QUESTION_QUESTION),
            (Token::QuestionDot, kw::QUESTION_DOT),
            (Token::Question, kw::QUESTION),
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
}
