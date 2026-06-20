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
        match self {
            Self::Fn => "fn",
            Self::Fip => "fip",
            Self::Fbip => "fbip",
            Self::Pub => "pub",
            Self::Import => "import",
            Self::As => "as",
            Self::Type => "type",
            Self::Newtype => "newtype",
            Self::Opaque => "opaque",
            Self::Effect => "effect",
            Self::KwError => "error",
            Self::Throw => "throw",
            Self::Try => "try",
            Self::Catch => "catch",
            Self::Transact => "transact",
            Self::Alias => "alias",
            Self::Class => "class",
            Self::Instance => "instance",
            Self::Pattern => "pattern",
            Self::Deriving => "deriving",
            Self::Where => "where",
            Self::Given => "given",
            Self::Handle => "handle",
            Self::With => "with",
            Self::Handler => "handler",
            Self::Mask => "mask",
            Self::Ctl => "ctl",
            Self::Final => "final",
            Self::Return => "return",
            Self::Let => "let",
            Self::Var => "var",
            Self::Borrow => "borrow",
            Self::In => "in",
            Self::For => "for",
            Self::Do => "do",
            Self::If => "if",
            Self::Then => "then",
            Self::Else => "else",
            Self::Elif => "elif",
            Self::Match => "match",
            Self::Of => "of",
            Self::Forall => "forall",
            Self::True => "true",
            Self::False => "false",
            Self::KwInt => "Int",
            Self::KwBool => "Bool",
            Self::KwUnit => "Unit",
            Self::KwFloat => "Float",
            Self::KwChar => "Char",
            Self::KwString => "String",
            Self::KwI64 => "I64",
            Self::KwU64 => "U64",
            Self::Arrow => "->",
            Self::LArrow => "<-",
            Self::FatArrow => "=>",
            Self::EqDot => "==.",
            Self::NeDot => "/=.",
            Self::LeDot => "<=.",
            Self::GeDot => ">=.",
            Self::LtDot => "<.",
            Self::GtDot => ">.",
            Self::EqEq => "==",
            Self::Ne => "/=",
            Self::Le => "<=",
            Self::Ge => ">=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Eq => "=",
            Self::AmpAmp => "&&",
            Self::PipePipe => "||",
            Self::PipeRight => "|>",
            Self::CompRight => ">>",
            Self::CompLeft => "<<",
            Self::Bar => "|",
            Self::Lambda => "\\",
            Self::PlusDot => "+.",
            Self::MinusDot => "-.",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::StarDot => "*.",
            Self::Star => "*",
            Self::SlashDot => "/.",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::Comma => ",",
            Self::ColonEq => ":=",
            Self::Colon => ":",
            Self::Bang => "!",
            Self::DotDot => "..",
            Self::Dot => ".",
            Self::QuestionQuestion => "??",
            Self::QuestionDot => "?.",
            Self::Question => "?",
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
