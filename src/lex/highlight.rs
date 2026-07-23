use super::Token;
use Token::{
    Alias, AmpAmp, Arrow, As, At, Bang, Bar, Borrow, Break, Canonical, Caret, Catch, CharLit,
    Class, Colon, ColonEq, Comma, Comment, CompLeft, CompRight, Continue, Deriving, Do, Dot,
    DotDot, Each, Effect, Elif, Else, Ensures, Eq, EqDot, EqEq, False, FatArrow, Fbip, Fip, Float,
    Fn, For, Forall, Ge, GeDot, Given, Gt, GtDot, Handle, Handler, Hash, Ident, If, Import, In,
    Instance, Int, InterpEnd, InterpMid, InterpStart, KwBool, KwChar, KwError, KwFloat, KwI64,
    KwInt, KwString, KwU64, KwUnit, LArrow, LBrace, LBracket, LParen, Lambda, Le, LeDot, Let,
    Logic, Loop, Lt, LtDot, Mask, Match, Minus, MinusDot, MinusEq, Ne, NeDot, Newtype, Of, Opaque,
    Pattern, Percent, PercentEq, PipePipe, PipeRight, Plus, PlusDot, PlusEq, Probe, Pub, QualName,
    Question, QuestionDot, QuestionQuestion, RBrace, RBracket, RParen, Replayable, Requires,
    Return, Slash, SlashDot, Stable, Star, StarDot, StarEq, StringLit, Then, Throw, Tilde,
    Transact, True, Try, Type, UIdent, Using, VClose, VHead, VOpen, VSemi, Val, Var, Where, While,
    With,
};

/// Coarse highlight category for one lexed token, matched in `web/index.html`.
///
/// Exhaustive by construction: every operator, delimiter, and layout-virtual
/// token is enumerated rather than caught by `_`, so a newly added `Token`
/// forces a highlight-category decision here the way `Token::text` forces a
/// spelling decision. The REPL categorizer, the mdbook JS highlighter, and the
/// nvim syntax file mirror this keyword set; the token drift test pins them.
#[must_use]
pub const fn tok_class(t: &Token) -> &'static str {
    match t {
        Fn | Pub | Import | As | Type | Newtype | Opaque | Effect | KwError | Throw | Try
        | Catch | Transact | Alias | Class | Instance | Canonical | Pattern | Deriving | Where
        | Handle | With | Handler | Mask | Val | Return | Let | Var | Borrow | In | For | Do
        | If | Then | Else | Elif | Match | Of | Forall | Probe | Replayable | Stable | Given
        | While | Loop | Break | Continue | Fip | Fbip | Each | Using | Logic | Requires
        | Ensures => "kw",
        True | False => "lit",
        KwInt | KwBool | KwUnit | KwFloat | KwChar | KwString | KwI64 | KwU64 => "ty",
        UIdent(_) | QualName(_) => "ctor",
        Int(_) | Float(_) => "num",
        CharLit(_) | StringLit(_) | InterpStart(_) | InterpMid(_) | InterpEnd(_) => "str",
        Comment(_) => "com",
        Ident(_) => "id",
        // Operators and delimiters, plus the layout-virtual tokens (`VOpen` and
        // friends) that the offside pass inserts and strips before the parser, so
        // no highlighter ever sees them; grouped here only to keep this match
        // exhaustive without a `_` that would silently mis-tag a new token.
        Arrow | LArrow | FatArrow | EqDot | NeDot | LeDot | GeDot | LtDot | GtDot | EqEq | Ne
        | Le | Ge | Lt | Gt | Eq | AmpAmp | PipePipe | PipeRight | CompRight | CompLeft | Bar
        | Lambda | PlusDot | MinusDot | PlusEq | MinusEq | StarEq | PercentEq | Plus | Minus
        | StarDot | Star | SlashDot | Slash | Percent | Caret | Tilde | LParen | RParen
        | LBrace | RBrace | LBracket | RBracket | Comma | ColonEq | Colon | Bang | At | Hash
        | DotDot | Dot | QuestionQuestion | QuestionDot | Question | VOpen | VClose | VSemi
        | VHead => "op",
    }
}
