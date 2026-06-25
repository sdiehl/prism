//! Operator spelling, precedence, and the parenthesization rules that keep a
//! reprinted binary-operator tree parsing back to the same shape.

use crate::syntax::ast::{BinOp, Expr, Sugar};

pub(super) const fn binop_prec(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Ne | BinOp::Eqf | BinOp::Nef => 3,
        BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::Ltf
        | BinOp::Lef
        | BinOp::Gtf
        | BinOp::Gef => 4,
        BinOp::Add | BinOp::Sub | BinOp::Addf | BinOp::Subf => 5,
        BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Mulf | BinOp::Divf => 6,
        BinOp::Pow => 7,
    }
}

pub(super) const fn low_prec_operand(child: &Expr) -> bool {
    matches!(
        child,
        Expr::Match(..)
            | Expr::If(..)
            | Expr::Let(..)
            | Expr::Lam(..)
            | Expr::Pipe(..)
            | Expr::Sugar(Sugar::Compose(..))
    )
}

// Every comparison operator lives at one non-associative grammar level
// (`Cmp: Add CmpOp Add`), so a comparison can never be a direct operand of
// another comparison. The formatter must keep the parens on either side or the
// output stops parsing.
const fn is_cmp(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq
            | BinOp::Ne
            | BinOp::Eqf
            | BinOp::Nef
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Ltf
            | BinOp::Lef
            | BinOp::Gtf
            | BinOp::Gef
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
        _ => low_prec_operand(child),
    }
}

pub(super) const fn needs_right_paren(child: &Expr, parent_op: BinOp, parent_prec: u8) -> bool {
    match child {
        Expr::Bin(op, ..) if is_cmp(*op) && is_cmp(parent_op) => true,
        Expr::Bin(op, ..) => {
            let cp = binop_prec(*op);
            cp < parent_prec
                || (cp == parent_prec
                    && matches!(
                        parent_op,
                        BinOp::Sub | BinOp::Div | BinOp::Rem | BinOp::Subf | BinOp::Divf
                    ))
        }
        _ => low_prec_operand(child),
    }
}
