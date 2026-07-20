//! Test-declaration signature checks. In test mode a `test fn` must take zero parameters, be
//! monomorphic, return `Unit`, and keep its effect row within the supported test
//! world (`Fail` and the ambient output channel `IO`). Violations are
//! declaration-local diagnostics naming the broken rule, reported at check time.
//!
//! The grammar only admits `test` on a `fn`, and a test is always private, so a
//! `pub test` or a `test` on a non-fn item is already rejected before here. This
//! module owns the remaining semantic rules.

use std::collections::BTreeSet;

use crate::error::TypeError;
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::types::{Checked, Type};

/// A validated test function, reduced to what discovery needs: its canonical
/// name.
#[derive(Clone, Debug)]
pub(crate) struct TestSignature {
    pub name: String,
}

/// The name of a test declared more than once in the user region of `full_src`,
/// or `None` when every test name is unique.
///
/// The checker keeps only the last of two same-named definitions, so a duplicate
/// test would silently vanish before `signatures_from` sees it. This runs on the
/// raw surface parse, where both declarations survive, so `prism test` can reject
/// the collision deterministically. Only the user region (past the prelude) is
/// scanned, so a shadowed prelude name is not mistaken for a redefinition.
#[must_use]
pub(crate) fn duplicate_test_name(full_src: &str) -> Option<String> {
    let program = crate::parse::parse(full_src).ok()?.program;
    let prelude_end = crate::error::SourceMap::new(full_src).prelude_len();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for decl in program
        .fns
        .iter()
        .filter(|d| d.test && d.span.start >= prelude_end)
    {
        if !seen.insert(decl.name.clone()) {
            return Some(decl.name.clone());
        }
    }
    None
}

/// Validate the test declarations of an already-elaborated test-mode program.
///
/// # Errors
/// A `TypeError` at the offending test declaration.
pub(crate) fn signatures_from(
    program: &Program<CorePhase>,
    checked: &Checked,
) -> Result<Vec<TestSignature>, TypeError> {
    // The compilation unit is always the root/entry module, so its own test
    // declarations keep bare canonical names. A test pulled in through an import
    // carries a `Module.`/`Module@` qualifier and belongs to that other module;
    // it is discovered when that module is compiled as its own unit, not here.
    let test_names: BTreeSet<&str> = program
        .fns
        .iter()
        .filter(|d| d.test && crate::names::bare_name(&d.name) == d.name)
        .map(|d| d.name.as_str())
        .collect();
    let mut out = Vec::new();
    for decl in &checked.decls {
        if !test_names.contains(decl.name.as_str()) {
            continue;
        }
        check_signature(decl)?;
        out.push(TestSignature {
            name: decl.name.clone(),
        });
    }
    Ok(out)
}

// The signature rules, evaluated over one checked declaration. Every failure names
// the rule.
//
// A well-formed test has the scheme `() -> Unit ! <row>` (possibly generalized
// over the ambient effect tail, and, when the body never returns, over the
// result). Monomorphism is enforced structurally: a test takes no parameters, so
// no value-type variable can enter through an argument; the only variable a
// well-formed test generalizes is the ambient effect tail (fine) or an
// unconstrained result of a never-returning body (`fail()`), which unifies with
// `Unit`. A parameter type variable would be caught by the zero-parameter rule.
fn check_signature(decl: &crate::types::DeclInfo) -> Result<(), TypeError> {
    let short = crate::names::bare_name(&decl.name);
    // A test may not be named `main`: the harness synthesizes a `main` entry that
    // calls the test, so a test named `main` would shadow itself and recurse.
    if short == crate::names::ENTRY_POINT {
        return Err(fail(
            short,
            "may not be named `main` (the reserved entry point)",
        ));
    }
    let (params, ret) = fun_shape(&decl.ty).ok_or_else(|| fail(short, "must be a function"))?;
    if params != 0 {
        return Err(fail(short, "must take no parameters"));
    }
    if !returns_unit(ret) {
        return Err(fail(
            short,
            &format!("must return Unit, found {}", ret.show()),
        ));
    }
    let residual = unsupported_effects(&decl.effects);
    if !residual.is_empty() {
        let available = super::TEST_WORLD_EFFECTS.join(", ");
        return Err(fail(
            short,
            &format!(
                "requires an unsupported test effect: {} (the test world handles: {available})",
                residual.join(", ")
            ),
        ));
    }
    Ok(())
}

// The parameter count and return type of a (possibly generalized) function
// scheme, or `None` when the scheme is not a function.
fn fun_shape(ty: &Type) -> Option<(usize, &Type)> {
    match strip_forall(ty) {
        Type::Fun(params, _, ret) => Some((params.len(), ret)),
        _ => None,
    }
}

fn strip_forall(ty: &Type) -> &Type {
    let mut ty = ty;
    loop {
        match ty {
            Type::Forall(_, body) | Type::RowForall(_, body) => ty = body,
            other => return other,
        }
    }
}

// The result is `Unit`, or an unconstrained variable from a body that never
// returns (a bare `fail()`), which unifies with `Unit`. A concrete non-Unit
// result is rejected.
fn returns_unit(ty: &Type) -> bool {
    matches!(strip_forall(ty), Type::Unit | Type::Var(_) | Type::Exist(_))
}

// The effect labels outside the supported test world, sorted for a deterministic
// diagnostic.
fn unsupported_effects(effects: &BTreeSet<crate::sym::Sym>) -> Vec<String> {
    let allowed: BTreeSet<&str> = super::TEST_WORLD_EFFECTS.iter().copied().collect();
    let mut residual: Vec<String> = effects
        .iter()
        .map(|sym| sym.as_str().to_string())
        .filter(|name| !allowed.contains(name.as_str()))
        .collect();
    residual.sort();
    residual.dedup();
    residual
}

fn fail(name: &str, rule: &str) -> TypeError {
    TypeError::TypeFailure {
        span: marginalia::Span::empty(0),
        msg: format!("test function `{name}` {rule}"),
    }
}
