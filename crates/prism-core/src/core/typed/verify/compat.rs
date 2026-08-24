use std::collections::BTreeMap;

use prism_common::sym::Sym;

use crate::types::ty::{EffRow, Label};
use crate::types::{repr_of_type, Type};

use super::super::violation::RowUnionError;
use super::super::{CompSig, CoreFnSig, CoreQuantifier, CoreType, LoweredType};
use super::subst::rename_fn_quantifier;

/// The canonical union of two effect rows, which the verifier uses wherever a
/// node's row is the join of its subterms'.
///
/// # Errors
/// [`RowUnionError`] showing both tails, when they are distinct open ones: the
/// union of two unknown remainders is not something the checker can prove.
pub fn union_rows(left: &EffRow, right: &EffRow) -> Result<EffRow, RowUnionError> {
    let tail = match (left.tail(), right.tail()) {
        (a, b) if a == b => a.clone(),
        (EffRow::Empty, other) | (other, EffRow::Empty) => other.clone(),
        (a, b) => {
            return Err(RowUnionError::OpenTails {
                left: a.clone(),
                right: b.clone(),
            });
        }
    };
    let mut labels: BTreeMap<Sym, Label> = BTreeMap::new();
    for label in left.labels().into_iter().chain(right.labels()) {
        match labels.get(&label.name) {
            Some(existing) if existing.args == label.args => {}
            Some(existing) if existing.args.is_empty() => {
                labels.insert(label.name, label.clone());
            }
            Some(_) if label.args.is_empty() => {}
            Some(existing) => {
                return Err(RowUnionError::Labels {
                    left: existing.clone(),
                    right: label.clone(),
                });
            }
            None => {
                labels.insert(label.name, label.clone());
            }
        }
    }
    Ok(EffRow::canonical(labels.into_values(), tail))
}

pub(super) fn core_subtype(actual: &CoreType, expected: &CoreType) -> bool {
    if actual == expected {
        return true;
    }
    match (actual, expected) {
        (CoreType::Source(actual), CoreType::Source(expected)) => source_repr_eq(actual, expected),
        (CoreType::Thunk(actual), CoreType::Thunk(expected)) => sig_subtype(actual, expected),
        (CoreType::Function(actual), CoreType::Function(expected)) => {
            fn_sig_subtype(actual, expected)
        }
        // Mutable cells and reuse tokens are invariant in their payload.
        (CoreType::Ref(actual), CoreType::Ref(expected))
        | (CoreType::ReuseToken(actual), CoreType::ReuseToken(expected)) => actual == expected,
        (CoreType::Lowered(actual), CoreType::Lowered(expected)) => actual == expected,
        _ => false,
    }
}

#[must_use]
pub fn lowered_representation_conversion(actual: &CoreType, expected: &CoreType) -> bool {
    let runtime_word = |ty: &CoreType| {
        matches!(
            ty,
            CoreType::Source(ty) if repr_of_type(ty).is_gc_value()
        ) || matches!(
            ty,
            CoreType::Thunk(_) | CoreType::Function(_) | CoreType::Ref(_)
        )
    };
    match (actual, expected) {
        (actual, CoreType::Lowered(LoweredType::Word)) if runtime_word(actual) => true,
        (CoreType::Lowered(LoweredType::Word), expected) if runtime_word(expected) => true,
        (CoreType::Source(Type::Unit), CoreType::Lowered(LoweredType::Queue(_))) => true,
        _ => false,
    }
}

#[must_use]
pub fn representation_preserving(actual: &CoreType, expected: &CoreType) -> bool {
    representation_preserving_by(actual, expected, row_reinterpretable)
}

/// The substitution-stable restriction of [`representation_preserving`]: the
/// target row's abstract tail absorbs nothing.
///
/// `row_reinterpretable`'s absorb rule is sound only at verification time,
/// when every remaining row variable is rigid for good; a pass that may still
/// substitute rows through the coercion's types (elaboration solving,
/// specialization, inlining) must not mint a cast a later instantiation can
/// turn into a concrete label vanishing into a smaller concrete row, which the
/// verifier rejects as laundering.
#[must_use]
pub fn representation_preserving_stable(actual: &CoreType, expected: &CoreType) -> bool {
    representation_preserving_by(actual, expected, |actual, expected| {
        let closed = EffRow::canonical(actual.labels().into_iter().cloned(), EffRow::Empty);
        row_included(&closed, expected)
    })
}

fn representation_preserving_by(
    actual: &CoreType,
    expected: &CoreType,
    rows: impl Fn(&EffRow, &EffRow) -> bool,
) -> bool {
    if matches!(
        (actual, expected),
        (CoreType::Source(Type::Int), CoreType::Source(Type::Char))
            | (CoreType::Source(Type::Char), CoreType::Source(Type::Int))
    ) {
        return true;
    }
    let (CoreType::Thunk(actual), CoreType::Thunk(expected)) = (actual, expected) else {
        return false;
    };
    let (CoreType::Function(actual_fn), CoreType::Function(expected_fn)) =
        (actual.result(), expected.result())
    else {
        return false;
    };
    let Some((actual_fn, expected_fn)) = alpha_align_fn_sigs(actual_fn, expected_fn) else {
        return false;
    };
    actual.effects() == expected.effects()
        && actual_fn.params() == expected_fn.params()
        && actual_fn.body().result() == expected_fn.body().result()
        && rows(actual_fn.body().effects(), expected_fn.body().effects())
}

/// Whether a representation-preserving coercion may relabel a thunk's inner
/// row from `actual` to `expected`. A target row with an abstract tail
/// absorbs anything: no consumer can prove purity from an open row, so no
/// effect is laundered by hiding it there (the evidence tier's flow-planned
/// recast relies on this). Against a concrete target, the source's own
/// abstract tail may instantiate away, but every concrete label the source
/// names must survive into the target. The one locally refutable laundering
/// shape, a concrete label vanishing into a smaller concrete row (`{IO}` to
/// `{}`), stays rejected: it would let a later pass treat an effectful thunk
/// as pure.
fn row_reinterpretable(actual: &EffRow, expected: &EffRow) -> bool {
    if matches!(expected.tail(), EffRow::Var(_)) {
        return true;
    }
    let closed = EffRow::canonical(actual.labels().into_iter().cloned(), EffRow::Empty);
    row_included(&closed, expected)
}

fn fn_sig_subtype(actual: &CoreFnSig, expected: &CoreFnSig) -> bool {
    let Some((actual, expected)) = alpha_align_fn_sigs(actual, expected) else {
        return false;
    };
    actual.params() == expected.params() && sig_subtype(actual.body(), expected.body())
}

/// Rename corresponding function quantifiers to shared fresh names before a
/// structural comparison. Quantifier spelling is not part of a Core type, and
/// substitution deliberately changes it to avoid capture.
fn alpha_align_fn_sigs(actual: &CoreFnSig, expected: &CoreFnSig) -> Option<(CoreFnSig, CoreFnSig)> {
    if actual.quantifiers().len() != expected.quantifiers().len() {
        return None;
    }
    if !actual
        .quantifiers()
        .iter()
        .zip(expected.quantifiers())
        .all(|(actual, expected)| {
            matches!(
                (actual, expected),
                (CoreQuantifier::Type(_), CoreQuantifier::Type(_))
                    | (CoreQuantifier::Row(_), CoreQuantifier::Row(_))
            )
        })
    {
        return None;
    }

    let mut actual = actual.clone();
    let mut expected = expected.clone();
    for index in 0..actual.quantifiers().len() {
        let fresh = Sym::fresh();
        actual = rename_fn_quantifier(&actual, index, fresh);
        expected = rename_fn_quantifier(&expected, index, fresh);
    }
    Some((actual, expected))
}

fn source_repr_eq(actual: &Type, expected: &Type) -> bool {
    if actual == expected
        || matches!(
            (actual, expected),
            (Type::Int, Type::Char) | (Type::Char, Type::Int)
        )
    {
        return true;
    }
    match (actual, expected) {
        (Type::Fun(ap, ae, ar), Type::Fun(ep, ee, er)) => {
            ap.len() == ep.len()
                && ap.iter().zip(ep).all(|(a, e)| source_repr_eq(a, e))
                && row_repr_eq(ae, ee)
                && source_repr_eq(ar, er)
        }
        (Type::Con(an, aa), Type::Con(en, ea)) if an == en && aa.len() == ea.len() => {
            aa.iter().zip(ea).all(|(a, e)| source_repr_eq(a, e))
        }
        (Type::App(ah, aa), Type::App(eh, ea)) => source_repr_eq(ah, eh) && source_repr_eq(aa, ea),
        (Type::Tuple(af), Type::Tuple(ef)) | (Type::UnboxedTuple(af), Type::UnboxedTuple(ef))
            if af.len() == ef.len() =>
        {
            af.iter().zip(ef).all(|(a, e)| source_repr_eq(a, e))
        }
        (Type::UnboxedRecord(af), Type::UnboxedRecord(ef)) if af.len() == ef.len() => af
            .iter()
            .zip(ef)
            .all(|((an, a), (en, e))| an == en && source_repr_eq(a, e)),
        (Type::OrNull(a), Type::OrNull(e)) => source_repr_eq(a, e),
        (Type::Row(a), Type::Row(e)) => row_repr_eq(a, e),
        (Type::Coeffect(a, ar), Type::Coeffect(e, er)) if ar == er => source_repr_eq(a, e),
        (Type::Forall(an, a), Type::Forall(en, e))
        | (Type::RowForall(an, a), Type::RowForall(en, e))
            if an == en =>
        {
            source_repr_eq(a, e)
        }
        _ => false,
    }
}

fn row_repr_eq(actual: &EffRow, expected: &EffRow) -> bool {
    actual.tail() == expected.tail()
        && actual.labels().len() == expected.labels().len()
        && actual.labels().iter().zip(expected.labels()).all(|(a, e)| {
            a.name == e.name
                && a.args.len() == e.args.len()
                && a.args
                    .iter()
                    .zip(&e.args)
                    .all(|(a, e)| source_repr_eq(a, e))
        })
}

fn sig_subtype(actual: &CompSig, expected: &CompSig) -> bool {
    core_subtype(actual.result(), expected.result())
        && row_included(actual.effects(), expected.effects())
}

pub(in crate::core::typed) fn row_included(actual: &EffRow, expected: &EffRow) -> bool {
    if actual == expected || actual == &EffRow::Empty {
        return true;
    }
    for label in actual.labels() {
        let Some(wanted) = expected.labels().into_iter().find(|wanted| {
            wanted.name == label.name
                && (wanted.args == label.args || wanted.args.is_empty() || label.args.is_empty())
        }) else {
            return false;
        };
        if label.args != wanted.args && !label.args.is_empty() && !wanted.args.is_empty() {
            return false;
        }
    }
    match actual.tail() {
        EffRow::Empty => true,
        EffRow::Var(name) => expected.tail() == &EffRow::Var(*name),
        // Existentials are independently rejected by `check_row`; they cannot
        // be evidence for subtyping.
        EffRow::Exist(_) | EffRow::Extend(..) => false,
    }
}
