//! Canonical source spellings for every fixed token.

pub(crate) const FN: &str = "fn";
pub(crate) const FIP: &str = "fip";
pub(crate) const FBIP: &str = "fbip";
pub(crate) const REPLAYABLE: &str = "replayable";
pub(crate) const LOGIC: &str = "logic";
pub(crate) const REQUIRES: &str = "requires";
pub(crate) const ENSURES: &str = "ensures";
pub(crate) const TEST: &str = "test";
pub(crate) const TOTAL: &str = "total";
pub(crate) const ASSUME: &str = "assume";
pub(crate) const DECREASES: &str = "decreases";
pub(crate) const DEPRECATED: &str = "deprecated";
pub(crate) const PUB: &str = "pub";
pub(crate) const IMPORT: &str = "import";
pub(crate) const AS: &str = "as";
pub(crate) const TYPE: &str = "type";
pub(crate) const NEWTYPE: &str = "newtype";
pub(crate) const STABLE: &str = "stable";
pub(crate) const UPGRADE: &str = "upgrade";
pub(crate) const DOWNGRADE: &str = "downgrade";
pub(crate) const DROP_LOSS: &str = "drop_loss";
pub(crate) const FROZEN: &str = "frozen";
// The migration-table block and its route words. All three are contextual
// idents (recognized only in a `stable` block body), never reserved words, so a
// program may still use `migrations`, `version`, or `auto` as ordinary names
// elsewhere.
pub(crate) const MIGRATIONS: &str = "migrations";
pub(crate) const VERSION: &str = "version";
pub(crate) const AUTO: &str = "auto";
pub(crate) const KIND_ROW: &str = "Row";
pub(crate) const KIND_NAT: &str = "Nat";
pub(crate) const OPAQUE: &str = "opaque";
pub(crate) const EFFECT: &str = "effect";
pub(crate) const ERROR: &str = "error";
pub(crate) const THROW: &str = "throw";
pub(crate) const TRY: &str = "try";
pub(crate) const CATCH: &str = "catch";
pub(crate) const TRANSACT: &str = "transact";
pub(crate) const PROBE: &str = "probe";
pub(crate) const ALIAS: &str = "alias";
pub(crate) const CLASS: &str = "class";
pub(crate) const INSTANCE: &str = "instance";
pub(crate) const CANONICAL: &str = "canonical";
pub(crate) const PATTERN: &str = "pattern";
pub(crate) const VIEW: &str = "view";
pub(crate) const MAKE: &str = "make";
pub(crate) const DERIVING: &str = "deriving";
pub(crate) const WHERE: &str = "where";
pub(crate) const GIVEN: &str = "given";
pub(crate) const HANDLE: &str = "handle";
pub(crate) const WITH: &str = "with";
pub(crate) const HANDLER: &str = "handler";
pub(crate) const PARTIAL: &str = "partial";
pub(crate) const MASK: &str = "mask";
pub(crate) const VAL: &str = "val";
pub(crate) const RETURN: &str = "return";
pub(crate) const RESUME: &str = "resume";
pub(crate) const LET: &str = "let";
pub(crate) const VAR: &str = "var";
pub(crate) const BORROW: &str = "borrow";
pub(crate) const IN: &str = "in";
pub(crate) const FOR: &str = "for";
pub(crate) const WHILE: &str = "while";
pub(crate) const LOOP: &str = "loop";
pub(crate) const BREAK: &str = "break";
pub(crate) const CONTINUE: &str = "continue";
pub(crate) const DO: &str = "do";
pub(crate) const IF: &str = "if";
pub(crate) const THEN: &str = "then";
pub(crate) const ELSE: &str = "else";
pub(crate) const ELIF: &str = "elif";
pub(crate) const MATCH: &str = "match";
pub(crate) const OF: &str = "of";
pub(crate) const EACH: &str = "each";
pub(crate) const FORALL: &str = "forall";
pub(crate) const TRUE: &str = "true";
pub(crate) const FALSE: &str = "false";
pub(crate) const USING: &str = "using";

pub(crate) const TY_INT: &str = "Int";
pub(crate) const TY_BOOL: &str = "Bool";
pub(crate) const TY_UNIT: &str = "Unit";
pub(crate) const TY_FLOAT: &str = "Float";
pub(crate) const TY_CHAR: &str = "Char";
pub(crate) const TY_STRING: &str = "String";
pub(crate) const TY_I64: &str = "I64";
pub(crate) const TY_U64: &str = "U64";
pub(crate) const TY_OR_NULL: &str = "OrNull";
pub(crate) const CTOR_NULL: &str = "Null";
pub(crate) const CTOR_THIS: &str = "This";
pub(crate) const OR_NULL_TAG: usize = 0;
pub(crate) const OR_THIS_TAG: usize = 1;

/// Whether `name` is one of the wired nullable's constructors. Every consumer
/// (codegen layout, reuse pairing) treats the pair as a unit: the one datatype
/// whose native form carries no cell, so the two names share one predicate
/// instead of being re-tested at each site.
pub(crate) fn is_or_null_ctor(name: &str) -> bool {
    name == CTOR_NULL || name == CTOR_THIS
}

pub(crate) const ARROW: &str = "->";
pub(crate) const LARROW: &str = "<-";
pub(crate) const FAT_ARROW: &str = "=>";
pub(crate) const EQ_DOT: &str = "==.";
pub(crate) const NE_DOT: &str = "/=.";
pub(crate) const LE_DOT: &str = "<=.";
pub(crate) const GE_DOT: &str = ">=.";
pub(crate) const LT_DOT: &str = "<.";
pub(crate) const GT_DOT: &str = ">.";
pub(crate) const EQ_EQ: &str = "==";
pub(crate) const NE: &str = "/=";
pub(crate) const LE: &str = "<=";
pub(crate) const GE: &str = ">=";
pub(crate) const LT: &str = "<";
pub(crate) const GT: &str = ">";
pub(crate) const EQ: &str = "=";
pub(crate) const AMP_AMP: &str = "&&";
pub(crate) const PIPE_PIPE: &str = "||";
pub(crate) const PIPE_RIGHT: &str = "|>";
pub(crate) const COMP_RIGHT: &str = ">>";
pub(crate) const COMP_LEFT: &str = "<<";
pub(crate) const BAR: &str = "|";
pub(crate) const LAMBDA: &str = "\\";
pub(crate) const PLUS_DOT: &str = "+.";
pub(crate) const MINUS_DOT: &str = "-.";
pub(crate) const PLUS_EQ: &str = "+=";
pub(crate) const MINUS_EQ: &str = "-=";
pub(crate) const STAR_EQ: &str = "*=";
pub(crate) const PERCENT_EQ: &str = "%=";
pub(crate) const PLUS: &str = "+";
pub(crate) const MINUS: &str = "-";
pub(crate) const STAR_DOT: &str = "*.";
pub(crate) const STAR: &str = "*";
pub(crate) const SLASH_DOT: &str = "/.";
pub(crate) const SLASH: &str = "/";
pub(crate) const PERCENT: &str = "%";
pub(crate) const CARET: &str = "^";
pub(crate) const COLON_EQ: &str = ":=";
pub(crate) const COLON: &str = ":";
pub(crate) const BANG: &str = "!";
pub(crate) const AT: &str = "@";
pub(crate) const HASH: &str = "#";
pub(crate) const DOT_DOT: &str = "..";
pub(crate) const DOT: &str = ".";
pub(crate) const QUESTION_QUESTION: &str = "??";
pub(crate) const QUESTION_DOT: &str = "?.";
pub(crate) const QUESTION: &str = "?";
pub(crate) const TILDE: &str = "~";

pub(crate) const LPAREN: &str = "(";
pub(crate) const RPAREN: &str = ")";
pub(crate) const LBRACE: &str = "{";
pub(crate) const RBRACE: &str = "}";
pub(crate) const LBRACKET: &str = "[";
pub(crate) const RBRACKET: &str = "]";
pub(crate) const COMMA: &str = ",";

pub(crate) const LINE_COMMENT: &str = "--";
