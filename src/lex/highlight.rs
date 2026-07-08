use super::Token;
use Token::{
    Alias, As, Borrow, Break, Canonical, Catch, CharLit, Class, Comment, Continue, Ctl, Deriving,
    Do, Each, Effect, Elif, Else, False, Fbip, Final, Fip, Float, Fn, For, Forall, Fun, Given,
    Handle, Handler, Ident, If, Import, In, Instance, Int, InterpEnd, InterpMid, InterpStart,
    KwBool, KwChar, KwError, KwFloat, KwI64, KwInt, KwString, KwU64, KwUnit, Let, Loop, Mask,
    Match, Newtype, Of, Opaque, Pattern, Probe, Pub, QualName, Replayable, Return, Stable,
    StringLit, Then, Throw, Transact, True, Try, Type, UIdent, Using, Val, Var, Where, While, With,
};

/// Coarse highlight category for one lexed token, matched in `web/index.html`.
#[must_use]
pub const fn tok_class(t: &Token) -> &'static str {
    match t {
        Fn | Pub | Import | As | Type | Newtype | Opaque | Effect | KwError | Throw | Try
        | Catch | Transact | Alias | Class | Instance | Canonical | Pattern | Deriving | Where
        | Handle | With | Handler | Mask | Ctl | Final | Fun | Val | Return | Let | Var
        | Borrow | In | For | Do | If | Then | Else | Elif | Match | Of | Forall | Probe
        | Replayable | Stable | Given | While | Loop | Break | Continue | Fip | Fbip | Each
        | Using => "kw",
        True | False => "lit",
        KwInt | KwBool | KwUnit | KwFloat | KwChar | KwString | KwI64 | KwU64 => "ty",
        UIdent(_) | QualName(_) => "ctor",
        Int(_) | Float(_) => "num",
        CharLit(_) | StringLit(_) | InterpStart(_) | InterpMid(_) | InterpEnd(_) => "str",
        Comment(_) => "com",
        Ident(_) => "id",
        _ => "op",
    }
}
