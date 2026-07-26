//! Operator spelling, precedence, and the parenthesization rules that keep a
//! reprinted binary-operator tree parsing back to the same shape.

use crate::ast::{BinOp, Expr, Sugar};

pub(super) const fn binop_prec(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Ne => 3,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 4,
        BinOp::Add | BinOp::Sub => 5,
        BinOp::Mul | BinOp::Div | BinOp::Rem => 6,
        BinOp::Pow => 7,
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
    matches!(child, Expr::Bin(op, ..) if !matches!(op, BinOp::Pow)) || low_prec_operand(child)
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
            // `a ^ (b ^ c)`.
            cp < parent_prec || (cp == parent_prec && matches!(parent_op, BinOp::Pow))
        }
        // Unary minus binds looser than `^`, so a negated base keeps its parens
        // (`(-2) ^ 2`); without them the print reparses as `-(2 ^ 2)`. Under any
        // other operator a negation binds tighter and needs none.
        Expr::Neg(..) => matches!(parent_op, BinOp::Pow),
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
            // Equal precedence, left-associative: `parent(a, child(b, c))` reprints as
            // `a P b C c` and reparses as `child(parent(a, b), c)`. That regrouping is
            // meaning-preserving only when the ops reassociate. An additive parent does
            // (`a + (b - c) == (a + b) - c`); a subtractive parent does not. A
            // multiplicative parent only does over a pure `*` child.
            match parent_op {
                // Subtractive/divisive parents keep parens because the regrouping
                // changes meaning.
                BinOp::Sub | BinOp::Div | BinOp::Rem => true,
                BinOp::Mul => matches!(*op, BinOp::Div | BinOp::Rem),
                _ => false,
            }
        }
        _ => low_prec_operand(child),
    }
}
