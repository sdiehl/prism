//! Operator spelling, precedence, and the parenthesization rules that keep a
//! reprinted binary-operator tree parsing back to the same shape.

use crate::ast::{BinOp, Expr, Sugar};

pub(super) const fn binop_prec(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Ne => 3,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 4,
        BinOp::Add | BinOp::Sub => 7,
        BinOp::Mul | BinOp::Div | BinOp::Rem => 8,
        BinOp::Pow => 9,
    }
}

// Path join `a </> b` and list cons `x :: xs` sit on the binary ladder between
// comparison and the additive operators, the join looser than cons. Both are
// sugar rather than a `BinOp`, but they parenthesize by the same precedence
// comparison as one.
pub(super) const PATH_PREC: u8 = 5;
pub(super) const CONS_PREC: u8 = 6;

// Whether an operand of `::` keeps its parens. The head is an additive operand
// and the tail recurses at the cons level (right associative), so a cons on the
// left must keep its parens and one on the right needs none.
pub(super) const fn cons_operand_needs_paren(child: &Expr, head: bool) -> bool {
    match child {
        Expr::Bin(op, ..) => binop_prec(*op) < CONS_PREC,
        Expr::Sugar(Sugar::Cons(..)) => head,
        Expr::Sugar(Sugar::PathJoin(..)) => true,
        _ => low_prec_operand(child),
    }
}

// Whether an operand of `</>` keeps its parens. The join is left associative
// over cons operands, so a join on the right keeps its parens, one on the left
// needs none, and a cons on either side needs none.
pub(super) const fn path_operand_needs_paren(child: &Expr, left: bool) -> bool {
    match child {
        Expr::Bin(op, ..) => binop_prec(*op) < PATH_PREC,
        Expr::Sugar(Sugar::PathJoin(..)) => !left,
        Expr::Sugar(Sugar::Cons(..)) => false,
        _ => low_prec_operand(child),
    }
}

// The three levels the grammar puts between the binary ladder and the forms it
// admits only at the top of an expression, loosest first: `??` (right
// associative) over `|>` over `>>`/`<<` (both left associative). Ordering the
// levels is what makes the parenthesization rule one comparison: an operand
// keeps its parens exactly when its own level is looser than the slot the
// grammar gives it, and every slot below is one of these five values.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Level {
    // A binary operator, a call, an atom: anything the grammar accepts as an
    // operand of `>>` without parens.
    Tight,
    Compose,
    Pipe,
    Default,
    // A form the grammar admits only at the top: it is parenthesized in every
    // operand slot there is.
    Top,
}

pub(super) const fn level(child: &Expr) -> Level {
    match child {
        Expr::Match(..) | Expr::If(..) | Expr::Let(..) | Expr::Lam(..) => Level::Top,
        Expr::Sugar(Sugar::Default(..)) => Level::Default,
        Expr::Pipe(..) => Level::Pipe,
        Expr::Sugar(Sugar::Compose(..)) => Level::Compose,
        _ => Level::Tight,
    }
}

// Whether an operand printed into a slot of level `slot` keeps its parens.
pub(super) fn needs_paren_at(child: &Expr, slot: Level) -> bool {
    level(child) > slot
}

// An operand of the binary ladder or of unary minus, both of which sit below
// every level above: `??` binds looser than arithmetic, so `(a ?? b) + c` must
// keep its parens (the counter idiom `m[k] := (m[k] ?? 0) + 1`).
pub(super) const fn low_prec_operand(child: &Expr) -> bool {
    !matches!(level(child), Level::Tight)
}

// Unary minus binds tighter than every binary operator except exponentiation
// (`^`, which binds tighter still) and looser than every application/
// projection/postfix form, so its operand keeps its parens exactly when it is a
// binary operator the grammar would otherwise regroup (`-(a + b)`) or a
// low-precedence form. A `^` operand needs none: `-a ^ b` already parses as
// `-(a ^ b)`, the mathematical convention. A tighter operand (a call, a
// projection, an atom, or a nested negation) needs none.
pub(super) const fn neg_operand_needs_paren(child: &Expr) -> bool {
    matches!(child, Expr::Bin(op, ..) if !matches!(op, BinOp::Pow))
        || matches!(child, Expr::Sugar(Sugar::Cons(..) | Sugar::PathJoin(..)))
        || low_prec_operand(child)
}

// Every comparison operator lives at one non-associative grammar level
// (`Cmp: Add CmpOp Add`), so a comparison can never be a direct operand of
// another comparison. The formatter must keep the parens on either side or the
// output stops parsing.
const fn is_cmp(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

pub(super) const fn needs_left_paren(child: &Expr, parent_op: BinOp, parent_prec: u8) -> bool {
    match child {
        Expr::Bin(op, ..) if is_cmp(*op) && is_cmp(parent_op) => true,
        Expr::Bin(op, ..) => {
            let cp = binop_prec(*op);
            // `^` is right-associative, so a same-precedence left operand (another
            // `^`) must be parenthesized to keep `(a ^ b) ^ c` from reparsing as
            // `a ^ (b ^ c)`. Every other level is left-associative, where a
            // same-precedence left operand is exactly the tree the unparenthesized
            // print reparses to, so the parens are redundant and go. The mirror
            // case is not symmetric: an equal-precedence *right* operand is not the
            // tree the print reparses to, which is why `needs_right_paren` keeps it.
            cp < parent_prec || (cp == parent_prec && matches!(parent_op, BinOp::Pow))
        }
        // Unary minus binds looser than `^`, so a negated base keeps its parens
        // (`(-2) ^ 2`); without them the print reparses as `-(2 ^ 2)`. Under any
        // other operator a negation binds tighter and needs none.
        Expr::Neg(..) => matches!(parent_op, BinOp::Pow),
        Expr::Sugar(Sugar::Cons(..)) => CONS_PREC < parent_prec,
        Expr::Sugar(Sugar::PathJoin(..)) => PATH_PREC < parent_prec,
        _ => low_prec_operand(child),
    }
}

pub(super) const fn needs_right_paren(child: &Expr, parent_op: BinOp, parent_prec: u8) -> bool {
    match child {
        Expr::Bin(op, ..) if is_cmp(*op) && is_cmp(parent_op) => true,
        Expr::Bin(op, ..) => {
            let cp = binop_prec(*op);
            if cp != parent_prec {
                return cp < parent_prec;
            }
            // Equal precedence. Under a left-associative parent, dropping the parens
            // reprints `parent(a, child(b, c))` as `a P b C c`, which reparses as
            // `child(parent(a, b), c)`: a different tree. The formatter has no types,
            // so it cannot know the two trees agree on the values at hand, and over
            // Float they do not, since neither addition nor multiplication
            // reassociates. So the parens stay, whatever the operator pair. The cost
            // is nil for unparenthesized source, which parses left-nested and so
            // presents no `Bin` right child at all.
            //
            // `^` is the one right-associative level: `a ^ b ^ c` already reparses to
            // the right-nested tree, so those parens are redundant and go.
            !matches!(parent_op, BinOp::Pow)
        }
        Expr::Sugar(Sugar::Cons(..)) => CONS_PREC < parent_prec,
        Expr::Sugar(Sugar::PathJoin(..)) => PATH_PREC < parent_prec,
        _ => low_prec_operand(child),
    }
}
