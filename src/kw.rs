//! Canonical source spellings for every fixed token.

pub const FN: &str = "fn";
pub const FIP: &str = "fip";
pub const FBIP: &str = "fbip";
pub const REPLAYABLE: &str = "replayable";
pub const DEPRECATED: &str = "deprecated";
pub const PUB: &str = "pub";
pub const IMPORT: &str = "import";
pub const AS: &str = "as";
pub const TYPE: &str = "type";
pub const NEWTYPE: &str = "newtype";
pub const STABLE: &str = "stable";
pub const UPGRADE: &str = "upgrade";
pub const DOWNGRADE: &str = "downgrade";
pub const DROP_LOSS: &str = "drop_loss";
pub const FROZEN: &str = "frozen";
pub const KIND_ROW: &str = "Row";
pub const KIND_NAT: &str = "Nat";
pub const KIND_TYPE: &str = "Type";
pub const OPAQUE: &str = "opaque";
pub const EFFECT: &str = "effect";
pub const ERROR: &str = "error";
pub const THROW: &str = "throw";
pub const TRY: &str = "try";
pub const CATCH: &str = "catch";
pub const TRANSACT: &str = "transact";
pub const PROBE: &str = "probe";
pub const ALIAS: &str = "alias";
pub const CLASS: &str = "class";
pub const INSTANCE: &str = "instance";
pub const CANONICAL: &str = "canonical";
pub const PATTERN: &str = "pattern";
// The two clause keywords of a `pattern` declaration: `view` (the single-argument
// forward direction) and `make` (the optional constructor direction). Contextual,
// like the pattern clauses themselves.
pub const VIEW: &str = "view";
pub const MAKE: &str = "make";
pub const DERIVING: &str = "deriving";
pub const WHERE: &str = "where";
pub const GIVEN: &str = "given";
pub const HANDLE: &str = "handle";
pub const WITH: &str = "with";
pub const HANDLER: &str = "handler";
// Contextual after `handle ... with`, so existing values named `partial` remain
// legal everywhere else.
pub const PARTIAL: &str = "partial";
pub const MASK: &str = "mask";
pub const VAL: &str = "val";
pub const RETURN: &str = "return";
// Contextual keyword: introduces the continuation binder in a multishot handler
// clause (`op(params) resume k => ...`). Special only in that clause position, so
// it stays usable as an ordinary identifier elsewhere.
pub const RESUME: &str = "resume";
pub const LET: &str = "let";
pub const VAR: &str = "var";
pub const BORROW: &str = "borrow";
pub const IN: &str = "in";
pub const FOR: &str = "for";
pub const WHILE: &str = "while";
pub const LOOP: &str = "loop";
pub const BREAK: &str = "break";
pub const CONTINUE: &str = "continue";
pub const DO: &str = "do";
pub const IF: &str = "if";
pub const THEN: &str = "then";
pub const ELSE: &str = "else";
pub const ELIF: &str = "elif";
pub const MATCH: &str = "match";
pub const OF: &str = "of";
pub const EACH: &str = "each";
pub const FORALL: &str = "forall";
pub const TRUE: &str = "true";
pub const FALSE: &str = "false";
pub const USING: &str = "using";

pub const TY_INT: &str = "Int";
pub const TY_BOOL: &str = "Bool";
pub const TY_UNIT: &str = "Unit";
pub const TY_FLOAT: &str = "Float";
pub const TY_CHAR: &str = "Char";
pub const TY_STRING: &str = "String";
pub const TY_I64: &str = "I64";
pub const TY_U64: &str = "U64";
// The non-allocating nullable and its two wired-in constructors. `OrNull(a)` is a
// built-in type head (not a prelude datatype); `Null` is the zero word and
// `This(v)` carries `v` with no wrapper cell.
pub const TY_OR_NULL: &str = "OrNull";
pub const CTOR_NULL: &str = "Null";
pub const CTOR_THIS: &str = "This";
// Constructor tags for the wired-in nullable, shared by elaboration (which builds
// the tagged cells), pattern lowering, and coverage (sibling tag order). `Null` is
// the nullary tag 0, `This` the unary tag 1.
pub const OR_NULL_TAG: usize = 0;
pub const OR_THIS_TAG: usize = 1;

pub const ARROW: &str = "->";
pub const LARROW: &str = "<-";
pub const FAT_ARROW: &str = "=>";
pub const EQ_DOT: &str = "==.";
pub const NE_DOT: &str = "/=.";
pub const LE_DOT: &str = "<=.";
pub const GE_DOT: &str = ">=.";
pub const LT_DOT: &str = "<.";
pub const GT_DOT: &str = ">.";
pub const EQ_EQ: &str = "==";
pub const NE: &str = "/=";
pub const LE: &str = "<=";
pub const GE: &str = ">=";
pub const LT: &str = "<";
pub const GT: &str = ">";
pub const EQ: &str = "=";
pub const AMP_AMP: &str = "&&";
pub const PIPE_PIPE: &str = "||";
pub const PIPE_RIGHT: &str = "|>";
pub const COMP_RIGHT: &str = ">>";
pub const COMP_LEFT: &str = "<<";
pub const BAR: &str = "|";
pub const LAMBDA: &str = "\\";
pub const PLUS_DOT: &str = "+.";
pub const MINUS_DOT: &str = "-.";
pub const PLUS_EQ: &str = "+=";
pub const MINUS_EQ: &str = "-=";
pub const STAR_EQ: &str = "*=";
pub const PERCENT_EQ: &str = "%=";
pub const PLUS: &str = "+";
pub const MINUS: &str = "-";
pub const STAR_DOT: &str = "*.";
pub const STAR: &str = "*";
pub const SLASH_DOT: &str = "/.";
pub const SLASH: &str = "/";
pub const PERCENT: &str = "%";
pub const CARET: &str = "^";
pub const COLON_EQ: &str = ":=";
pub const COLON: &str = ":";
pub const BANG: &str = "!";
pub const AT: &str = "@";
pub const HASH: &str = "#";
pub const DOT_DOT: &str = "..";
pub const DOT: &str = ".";
pub const QUESTION_QUESTION: &str = "??";
pub const QUESTION_DOT: &str = "?.";
pub const QUESTION: &str = "?";
pub const TILDE: &str = "~";

pub const LPAREN: &str = "(";
pub const RPAREN: &str = ")";
pub const LBRACE: &str = "{";
pub const RBRACE: &str = "}";
pub const LBRACKET: &str = "[";
pub const RBRACKET: &str = "]";
pub const COMMA: &str = ",";

// The line-comment marker: `--` opens a comment running to end of line. The lexer
// matches it through a regex literal inside a proc-macro attribute, which cannot
// name a const, so this is the shared spelling every other phase scans against.
pub const LINE_COMMENT: &str = "--";
