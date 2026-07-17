use crate::syntax::ast::{Expr, PathStep, Sugar, S};

// In statement position, `match` and `if` always lay out across lines, even
// when they would fit on one: their arms and branches read better stacked, the
// way other languages write them. Synth matches (pattern-let / `?` desugar) are
// excluded. The block printer restores those surfaces inline. Record and optic
// literals whose shape reads better stacked (`wants_break`) force layout too,
// so a dense or nested constructor never stays cramped on one line.
pub(super) fn forces_break(e: &S<Expr>) -> bool {
    wants_break(&e.node)
        || matches!(
            e.node,
            Expr::Match(..)
                | Expr::If(..)
                | Expr::Sugar(Sugar::For(..) | Sugar::While(..) | Sugar::Transact(..))
        ) && !e.synth
}

// The most fields a record constructor keeps on one line; beyond this it stacks
// one field per line even when it would fit, for scannability.
const MAX_INLINE_RECORD_FIELDS: usize = 4;

// A record or optic literal reads better stacked across lines regardless of
// width. A record does when it carries more than `MAX_INLINE_RECORD_FIELDS`
// fields or nests another record constructor as a field value; a nested optic
// update does when it has several clauses and any path actually traverses
// (`each`/`?Ctor`/`where`/`[i]`), so the foci line up one per row.
pub(super) fn wants_break(e: &Expr) -> bool {
    match e {
        Expr::RecordCreate(_, fields) | Expr::RecordUpdate(_, _, fields) => {
            fields.len() > MAX_INLINE_RECORD_FIELDS
                || fields.iter().any(|(_, v)| contains_record_lit(&v.node))
        }
        Expr::RecordUpdatePath(_, ups) => {
            ups.len() > 1 && ups.iter().any(|(p, _)| p.iter().any(path_step_traverses))
        }
        // A `try`/`catch` that nests another handler or `try` (in the tried body
        // or a catch arm) reads as an unbroken run of inline braces; stack it so
        // the nesting is visible. The innermost, control-free `try` still prints
        // inline when short.
        Expr::Sugar(Sugar::TryCatch(body, arms)) => {
            contains_control(&body.node) || arms.iter().any(|a| contains_control(&a.body.node))
        }
        _ => false,
    }
}

const fn is_nested_control(e: &Expr) -> bool {
    matches!(e, Expr::Handle(..) | Expr::Sugar(Sugar::TryCatch(..)))
}

// Does `e` itself, or anything nested within it, open a handler or `try`/`catch`?
fn contains_control(e: &Expr) -> bool {
    if is_nested_control(e) {
        return true;
    }
    let mut found = false;
    e.each_child(&mut |child| {
        if !found {
            found = contains_control(&child.node);
        }
    });
    found
}

const fn is_record_lit(e: &Expr) -> bool {
    matches!(
        e,
        Expr::RecordCreate(..) | Expr::RecordUpdate(..) | Expr::RecordUpdatePath(..)
    )
}

fn contains_record_lit(e: &Expr) -> bool {
    if is_record_lit(e) {
        return true;
    }
    let mut found = false;
    e.each_child(&mut |child| {
        if !found {
            found = contains_record_lit(&child.node);
        }
    });
    found
}

const fn path_step_traverses(s: &PathStep) -> bool {
    matches!(
        s,
        PathStep::Each | PathStep::Case(_) | PathStep::Index(_) | PathStep::Where(_)
    )
}

// A call whose last argument is a lambda with a statement-shaped body: a
// sequence/binding (`Let`), a handler/match/if, or imperative sugar (`var`,
// `:=`, `throw`, `try`, `for`, `transact`, named `with`). Such a body reads
// better as the offside `f() fn(x)` block. A lambda whose body is a single
// value expression is left to print inline as `f(\x -> e)`.
pub(super) fn block_trailing_call(e: &S<Expr>) -> bool {
    let Expr::Call(_, args) = &e.node else {
        return false;
    };
    let Some(Expr::Lam(_, body)) = args.last().map(|a| &a.node) else {
        return false;
    };
    matches!(
        body.node,
        Expr::Let(..)
            | Expr::Handle(..)
            | Expr::Match(..)
            | Expr::If(..)
            | Expr::Sugar(
                Sugar::VarDecl(..)
                    | Sugar::Assign(..)
                    | Sugar::Throw(..)
                    | Sugar::TryCatch(..)
                    | Sugar::For(..)
                    | Sugar::While(..)
                    | Sugar::Transact(..)
                    | Sugar::Probe(..)
                    | Sugar::NamedHandle(..)
            )
    )
}
