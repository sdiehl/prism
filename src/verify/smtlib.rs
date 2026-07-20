//! The portable SMT-LIB encoder. Given a well-formed [`Obligation`], it emits one
//! canonical standalone script whose `unsat` answer discharges the obligation:
//! declare the free variables and uninterpreted functions, assert the
//! assumptions and the negated goal, then a single `check-sat`. The bytes are a
//! pure function of the logical term. There are no comments, source paths, spans,
//! timestamps, or solver options in the semantic script, and no `push`/`pop`
//! session dependence, so formatting, checkout path, backend, and effect-lowering
//! tier all leave it unchanged. Operator symbols come from the registry; only the
//! SMT-LIB command grammar is spelled here.

use num_bigint::{BigInt, Sign};

use crate::verify::logic::{LogicExpr, Obligation};

/// The narrowest logic needed: linear integer arithmetic plus the Bool core,
/// widened to add uninterpreted functions only when the obligation declares any.
pub(crate) const fn logic_name(ob: &Obligation) -> &'static str {
    if ob.funcs.is_empty() {
        "QF_LIA"
    } else {
        "QF_UFLIA"
    }
}

/// Emit the canonical SMT-LIB script for `ob`. The caller must have proved `ob`
/// well-formed with [`crate::verify::wf::check`]; a malformed obligation would
/// produce a malformed script rather than a diagnostic.
pub(crate) fn encode(ob: &Obligation) -> String {
    let mut out = String::new();
    out.push_str("(set-logic ");
    out.push_str(logic_name(ob));
    out.push_str(")\n");
    for (i, sort) in ob.vars.iter().enumerate() {
        out.push_str("(declare-const x");
        out.push_str(&i.to_string());
        out.push(' ');
        out.push_str(sort.smtlib());
        out.push_str(")\n");
    }
    for (i, decl) in ob.funcs.iter().enumerate() {
        out.push_str("(declare-fun f");
        out.push_str(&i.to_string());
        out.push_str(" (");
        for (j, p) in decl.params.iter().enumerate() {
            if j > 0 {
                out.push(' ');
            }
            out.push_str(p.smtlib());
        }
        out.push_str(") ");
        out.push_str(decl.result.smtlib());
        out.push_str(")\n");
    }
    for a in &ob.assumptions {
        out.push_str("(assert ");
        term(&mut out, a);
        out.push_str(")\n");
    }
    out.push_str("(assert (not ");
    term(&mut out, &ob.goal);
    out.push_str("))\n");
    out.push_str("(check-sat)\n");
    out
}

/// Write one term as an S-expression.
fn term(out: &mut String, e: &LogicExpr) {
    match e {
        LogicExpr::Var(v) => {
            out.push('x');
            out.push_str(&v.0.to_string());
        }
        LogicExpr::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        LogicExpr::Int(n) => int_literal(out, n),
        LogicExpr::Builtin(b, args) => {
            out.push('(');
            out.push_str(b.symbol());
            for a in args {
                out.push(' ');
                term(out, a);
            }
            out.push(')');
        }
        LogicExpr::App(f, args) => {
            if args.is_empty() {
                out.push('f');
                out.push_str(&f.0.to_string());
            } else {
                out.push_str("(f");
                out.push_str(&f.0.to_string());
                for a in args {
                    out.push(' ');
                    term(out, a);
                }
                out.push(')');
            }
        }
    }
}

/// SMT-LIB has no negative numeral; a negative integer is `(- k)` for positive
/// `k`. Canonical decimal spelling, no separators or leading zeros.
fn int_literal(out: &mut String, n: &BigInt) {
    if n.sign() == Sign::Minus {
        out.push_str("(- ");
        out.push_str(&(-n).to_string());
        out.push(')');
    } else {
        out.push_str(&n.to_string());
    }
}
