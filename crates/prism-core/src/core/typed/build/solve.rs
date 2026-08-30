//! Constraint solving for reconstructed typed-Core witnesses.

use std::collections::{BTreeMap, BTreeSet};

use prism_common::sym::Sym;

use crate::types::ty::{EffRow, Label};
use crate::types::Type;

use super::super::verify::union_rows as canonical_union_rows;
use super::super::violation::{
    MetaKind, MetaVar, RowUnionError, SolveError, SolveRelation, Within,
};
use super::super::{CompSig, CoreFnSig, CoreInstantiation, CoreQuantifier, CoreType, LoweredType};
use super::env::lower_value_type;

#[derive(Clone, Default)]
pub(super) struct Solver {
    next: u32,
    pub(super) core: BTreeMap<u32, CoreType>,
    pub(super) types: BTreeMap<u32, Type>,
    rows: BTreeMap<u32, EffRow>,
    pub(super) int_defaults: BTreeSet<u32>,
    latent_defaults: BTreeSet<u32>,
    instantiation_rows: BTreeSet<u32>,
    shield_rows: BTreeSet<u32>,
    shield_alias: BTreeMap<u32, u32>,
}

impl Solver {
    pub(super) const fn fresh_core(&mut self) -> CoreType {
        let id = self.bump();
        CoreType::Source(Type::Exist(id))
    }

    pub(super) const fn fresh_type(&mut self) -> Type {
        let id = self.bump();
        Type::Exist(id)
    }

    pub(super) fn fresh_int_core(&mut self) -> CoreType {
        let id = self.bump();
        self.int_defaults.insert(id);
        CoreType::Source(Type::Exist(id))
    }

    // The row of a closure nothing has demanded yet. It is bounded below by
    // what the body performs and stays open for a consumer whose row the
    // closure helps determine; a consumer that merely admits more effects than
    // the body has must not make the closure describe itself as performing
    // them, so `subsume_row` leaves this variable at its lower bound.
    pub(super) fn fresh_latent_row(&mut self) -> EffRow {
        let id = self.bump();
        self.latent_defaults.insert(id);
        EffRow::Exist(id)
    }

    // Settle an undemanded closure's row at its lower bound. Resolution leaves
    // the variable bare only while no join from below has given it a label, so
    // the bound is the empty row; solving it keeps an unsolved variable out of
    // the structural comparisons a witness has to survive.
    fn settle_latent(&mut self, row: &EffRow) -> EffRow {
        if let EffRow::Exist(id) = self.resolve_row(row) {
            if self.latent_defaults.contains(&id) {
                self.rows.insert(id, EffRow::Empty);
                return EffRow::Empty;
            }
        }
        self.resolve_row(row)
    }

    pub(super) const fn fresh_row(&mut self) -> EffRow {
        let id = self.bump();
        EffRow::Exist(id)
    }

    const fn bump(&mut self) -> u32 {
        let id = self.next;
        self.next = self
            .next
            .checked_add(1)
            .expect("typed builder metavariable overflow");
        id
    }

    pub(super) fn fresh_instantiation(
        &mut self,
        quantifiers: &[CoreQuantifier],
    ) -> Vec<CoreInstantiation> {
        quantifiers
            .iter()
            .map(|quantifier| match quantifier {
                CoreQuantifier::Type(_) => CoreInstantiation::Type(self.fresh_type()),
                CoreQuantifier::Row(_) => {
                    let row = self.fresh_row();
                    if let EffRow::Exist(id) = row {
                        self.instantiation_rows.insert(id);
                    }
                    CoreInstantiation::Row(row)
                }
            })
            .collect()
    }

    pub(super) fn resolve_core(&self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Source(Type::Exist(id)) if self.core.contains_key(id) => {
                self.resolve_core(&self.core[id])
            }
            CoreType::Source(ty) => {
                let resolved = self.resolve_type(ty);
                if let Type::Exist(id) = resolved {
                    if let Some(core) = self.core.get(&id) {
                        return self.resolve_core(core);
                    }
                }
                lower_value_type(&resolved)
            }
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.resolve_sig(sig))),
            CoreType::Function(sig) => CoreType::Function(Box::new(self.resolve_fn_sig(sig))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.resolve_core(inner))),
            CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(self.resolve_core(inner))),
            CoreType::Lowered(kind) => CoreType::Lowered(match kind {
                LoweredType::Word => LoweredType::Word,
                LoweredType::Eff(row) => LoweredType::Eff(self.resolve_row(row)),
                LoweredType::Queue(row) => LoweredType::Queue(self.resolve_row(row)),
                LoweredType::QueueView(row) => LoweredType::QueueView(self.resolve_row(row)),
            }),
        }
    }

    // Reveal only enough structure to choose a Core typing rule. Keeping the
    // interior witnesses un-zonked is important for subsumption: an expected
    // function row may still carry the original flexible tail whose lower
    // bound has already accumulated labels from an earlier argument.
    pub(super) fn resolve_core_head(&self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Source(Type::Exist(id)) if self.core.contains_key(id) => {
                self.resolve_core_head(&self.core[id])
            }
            CoreType::Source(Type::Exist(_)) => {
                let resolved = self.resolve_type(match ty {
                    CoreType::Source(source) => source,
                    _ => unreachable!(),
                });
                if let Type::Exist(id) = resolved {
                    if let Some(core) = self.core.get(&id) {
                        return self.resolve_core_head(core);
                    }
                }
                lower_value_type(&resolved)
            }
            _ => ty.clone(),
        }
    }

    fn resolve_sig(&self, sig: &CompSig) -> CompSig {
        CompSig::new(
            self.resolve_core(sig.result()),
            self.resolve_row(sig.effects()),
        )
    }

    fn resolve_fn_sig(&self, sig: &CoreFnSig) -> CoreFnSig {
        CoreFnSig::new(
            sig.quantifiers().to_vec(),
            sig.params()
                .iter()
                .map(|ty| self.resolve_core(ty))
                .collect(),
            self.resolve_sig(sig.body()),
        )
    }

    pub(super) fn resolve_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Exist(id) if self.types.contains_key(id) => self.resolve_type(&self.types[id]),
            Type::Forall(name, body) => Type::Forall(*name, Box::new(self.resolve_type(body))),
            Type::RowForall(name, body) => {
                Type::RowForall(*name, Box::new(self.resolve_type(body)))
            }
            Type::Fun(params, row, result) => Type::Fun(
                params.iter().map(|ty| self.resolve_type(ty)).collect(),
                self.resolve_row(row),
                Box::new(self.resolve_type(result)),
            ),
            Type::Con(name, args) => {
                Type::Con(*name, args.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::App(head, arg) => Type::app(self.resolve_type(head), self.resolve_type(arg)),
            Type::Tuple(fields) => {
                Type::Tuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedTuple(fields) => {
                Type::UnboxedTuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::UnboxedRecord(fields) => Type::UnboxedRecord(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.resolve_type(ty)))
                    .collect(),
            ),
            Type::OrNull(inner) => Type::OrNull(Box::new(self.resolve_type(inner))),
            Type::Row(row) => Type::Row(self.resolve_row(row)),
            Type::Coeffect(inner, row) => {
                Type::Coeffect(Box::new(self.resolve_type(inner)), row.clone())
            }
            _ => ty.clone(),
        }
    }

    pub(super) fn resolve_row(&self, row: &EffRow) -> EffRow {
        // Collect the concrete head labels as written (resolving each label's
        // args), preserving their multiplicity: a `mask<E>` puts both of its `E`
        // copies here, and both must survive. Then resolve the tail variable
        // once and merge the head into it. The merge depends on what the tail
        // variable stands for. A quantifier instantiation (minted by
        // `fresh_instantiation`) sits under a declared head, so its content is
        // by construction the demand BEYOND that head (`subsume_row` consumes
        // one-to-one and routes only the surplus there): the head concatenates
        // onto it, preserving a genuinely stacked handler level. Every other
        // tail is ambient threading, where a head label merely coincides with
        // the same label surfaced by resolving the shared variable (a handler
        // arm's `{IO | outer}` whose outer row also absorbed that IO), so the
        // head MAX-merges into it (max(1,1) = 1) exactly as `union_rows` would.
        let mut head: Vec<Label> = Vec::new();
        let mut cur = row;
        loop {
            match cur {
                EffRow::Exist(id) if self.rows.contains_key(id) => {
                    let tail = self.resolve_row(&self.rows[id]);
                    // A shield alias exists precisely to keep a union-built
                    // row's surface tail ambient-kind. While its content is
                    // still an unsolved instantiation existential, resolving
                    // through it would re-expose the raw variable and let a
                    // later resolve concatenate; keep the alias as the
                    // terminal until the content is concrete.
                    if self.shield_rows.contains(id)
                        && matches!(&tail, EffRow::Exist(raw) if !self.rows.contains_key(raw))
                    {
                        return EffRow::canonical(head, EffRow::Exist(*id));
                    }
                    if self.instantiation_rows.contains(id) {
                        return EffRow::canonical(
                            head.into_iter().chain(tail.labels().into_iter().cloned()),
                            tail.tail().clone(),
                        );
                    }
                    let head_row = EffRow::canonical(head.iter().cloned(), EffRow::Empty);
                    // A shared label with clashing non-empty args falls back
                    // to concatenation, the pre-existing behavior there.
                    return canonical_union_rows(&head_row, &tail).unwrap_or_else(|_| {
                        EffRow::canonical(
                            head.into_iter().chain(tail.labels().into_iter().cloned()),
                            tail.tail().clone(),
                        )
                    });
                }
                EffRow::Extend(label, rest) => {
                    head.push(Label {
                        name: label.name,
                        args: label.args.iter().map(|ty| self.resolve_type(ty)).collect(),
                    });
                    cur = rest;
                }
                // Terminal tail: Empty, an unbound row var, or an unbound Exist.
                _ => return EffRow::canonical(head, cur.clone()),
            }
        }
    }

    pub(super) fn unify_core(
        &mut self,
        left: &CoreType,
        right: &CoreType,
    ) -> Result<(), SolveError> {
        let left = self.resolve_core(left);
        let right = self.resolve_core(right);
        if left == right {
            return Ok(());
        }
        match (&left, &right) {
            // Keep source metavariables in the source substitution table so
            // the same solution also zonks explicit type instantiations. The
            // Core table is reserved for a placeholder that is discovered to
            // have a genuinely non-source CBPV shape (Function/Thunk/etc.).
            (CoreType::Source(a), CoreType::Source(b)) => self.unify_type(a, b),
            (CoreType::Source(Type::Exist(id)), other)
            | (other, CoreType::Source(Type::Exist(id))) => {
                if core_occurs(*id, other) {
                    return Err(SolveError::Occurs {
                        meta: MetaVar {
                            kind: MetaKind::Core,
                            id: *id,
                        },
                        within: Within::Core(other.clone()),
                    });
                }
                self.core.insert(*id, other.clone());
                Ok(())
            }
            (CoreType::Thunk(a), CoreType::Thunk(b)) => self.unify_sig(a, b),
            (CoreType::Function(a), CoreType::Function(b)) => self.unify_fn_sig(a, b),
            (CoreType::Ref(a), CoreType::Ref(b))
            | (CoreType::ReuseToken(a), CoreType::ReuseToken(b)) => self.unify_core(a, b),
            _ => Err(SolveError::Core {
                relation: SolveRelation::Unify,
                operands: Box::new((left.clone(), right.clone())),
            }),
        }
    }

    fn unify_sig(&mut self, left: &CompSig, right: &CompSig) -> Result<(), SolveError> {
        self.unify_core(left.result(), right.result())
            .map_err(|error| error.at("computation result"))?;
        self.unify_row(left.effects(), right.effects())
            .map_err(|error| error.at("computation effects"))
    }

    fn unify_fn_sig(&mut self, left: &CoreFnSig, right: &CoreFnSig) -> Result<(), SolveError> {
        if left.quantifiers() != right.quantifiers() || left.params().len() != right.params().len()
        {
            return Err(SolveError::Signature {
                relation: SolveRelation::Unify,
                operands: Box::new((left.clone(), right.clone())),
            });
        }
        for (a, b) in left.params().iter().zip(right.params()) {
            self.unify_core(a, b)
                .map_err(|error| error.at("function parameter"))?;
        }
        self.unify_sig(left.body(), right.body())
            .map_err(|error| error.at("function body"))
    }

    pub(super) fn subsume_core(
        &mut self,
        actual: &CoreType,
        expected: &CoreType,
    ) -> Result<(), SolveError> {
        let actual = self.resolve_core_head(actual);
        let expected = self.resolve_core_head(expected);
        if actual == expected {
            return Ok(());
        }
        match (&actual, &expected) {
            (CoreType::Source(Type::Exist(_)), _) | (_, CoreType::Source(Type::Exist(_))) => {
                self.unify_core(&actual, &expected)
            }
            (CoreType::Source(a), CoreType::Source(b)) => self.unify_type(a, b),
            (CoreType::Thunk(a), CoreType::Thunk(b)) => self.subsume_sig(a, b),
            (CoreType::Function(a), CoreType::Function(b)) => self.subsume_fn_sig(a, b),
            (CoreType::Ref(a), CoreType::Ref(b))
            | (CoreType::ReuseToken(a), CoreType::ReuseToken(b)) => self.unify_core(a, b),
            _ => Err(SolveError::Core {
                relation: SolveRelation::Subtype,
                operands: Box::new((actual.clone(), expected.clone())),
            }),
        }
    }

    pub(super) fn subsume_sig(
        &mut self,
        actual: &CompSig,
        expected: &CompSig,
    ) -> Result<(), SolveError> {
        self.subsume_core(actual.result(), expected.result())?;
        self.subsume_row(actual.effects(), expected.effects())
    }

    fn subsume_fn_sig(
        &mut self,
        actual: &CoreFnSig,
        expected: &CoreFnSig,
    ) -> Result<(), SolveError> {
        if actual.quantifiers() != expected.quantifiers()
            || actual.params().len() != expected.params().len()
        {
            return Err(SolveError::Signature {
                relation: SolveRelation::Subtype,
                operands: Box::new((actual.clone(), expected.clone())),
            });
        }
        for (actual, expected) in actual.params().iter().zip(expected.params()) {
            self.unify_core(actual, expected)?;
        }
        self.subsume_sig(actual.body(), expected.body())
    }

    fn subsume_row(&mut self, actual: &EffRow, expected: &EffRow) -> Result<(), SolveError> {
        let flexible_expected = match expected.tail() {
            EffRow::Exist(id) => Some(*id),
            _ => None,
        };
        let actual = self.resolve_row(actual);
        let expected = self.resolve_row(expected);
        if actual == expected || actual == EffRow::Empty {
            return Ok(());
        }
        // An undemanded closure's latent row behaves like the empty row it is
        // about to become: resolution leaves it bare only while no join from
        // below has given it a label, and the empty row is included in every
        // upper bound, which is what the short circuit above already says about
        // a pure computation. Solving it here would instead copy the consumer's
        // row onto a closure that performs none of it, and a closure that
        // describes itself as effectful costs the evidence lowering. The one
        // demand that constrains more than an upper bound names labels and still has an
        // open tail: a container element or a parameter row this closure helps
        // determine, where the binder that names the closure records exactly
        // that row, so the two must stay the same variable.
        if let EffRow::Exist(id) = actual {
            let demanding =
                !expected.labels().is_empty() && matches!(expected.tail(), EffRow::Exist(_));
            if self.latent_defaults.contains(&id) && !demanding {
                return Ok(());
            }
        }
        if matches!(actual, EffRow::Exist(_)) || matches!(expected, EffRow::Exist(_)) {
            return self.unify_row(&actual, &expected);
        }
        // A row is a multiset: each expected occurrence covers exactly one
        // actual occurrence, so a demand `mask<E>` raised to two `E`s is
        // never absorbed by a single expected `E`. The first unconsumed
        // name-match wins, mirroring the source checker's `rewrite_row`. A
        // surplus occurrence is treated exactly like a label absent by name:
        // with a flexible expected tail it grows the variable through
        // `constrain_row_join` below, so a call-site row instantiation carries
        // the surplus copy (this is what lets the independent verifier enforce
        // multiplicity under rigid tails); against a closed or rigid-`Var`
        // tail it has no absorber and the subrow fails.
        let expected_labels = expected.labels();
        let mut consumed = vec![false; expected_labels.len()];
        let mut unmatched = Vec::new();
        for label in actual.labels() {
            let found = expected_labels
                .iter()
                .enumerate()
                .find(|(index, wanted)| !consumed[*index] && wanted.name == label.name);
            let Some((index, wanted)) = found else {
                if flexible_expected.is_some() {
                    unmatched.push(label.clone());
                    continue;
                }
                return Err(SolveError::Row {
                    relation: SolveRelation::Subrow,
                    left: actual.clone(),
                    right: expected.clone(),
                });
            };
            consumed[index] = true;
            if label.args.len() != wanted.args.len() {
                return Err(SolveError::LabelNotIncluded {
                    label: label.clone(),
                    row: expected.clone(),
                });
            }
            for (actual, expected) in label.args.iter().zip(&wanted.args) {
                self.unify_type(actual, expected)?;
            }
        }
        if let Some(id) = flexible_expected {
            return self.constrain_row_join(
                &EffRow::Exist(id),
                &EffRow::canonical(unmatched, actual.tail().clone()),
            );
        }
        match actual.tail() {
            EffRow::Empty => Ok(()),
            EffRow::Var(name) if expected.tail() == &EffRow::Var(*name) => Ok(()),
            actual_tail @ (EffRow::Var(_) | EffRow::Exist(_))
                if matches!(expected.tail(), EffRow::Exist(_)) =>
            {
                self.unify_row(actual_tail, expected.tail())
            }
            EffRow::Exist(_) => self.unify_row(actual.tail(), expected.tail()),
            _ => Err(SolveError::Row {
                relation: SolveRelation::Subrow,
                left: actual.clone(),
                right: expected.clone(),
            }),
        }
    }

    pub(super) fn unify_type(&mut self, left: &Type, right: &Type) -> Result<(), SolveError> {
        let left = self.resolve_type(left);
        let right = self.resolve_type(right);
        if left == right {
            return Ok(());
        }
        match (&left, &right) {
            // `Char` is represented by the integer lane and source coercions
            // such as `chr` are erased before CBPV elaboration. Keep that
            // representation equality available when a constraint arrives
            // only after an ANF producer has already fixed its witness.
            (Type::Int, Type::Char) | (Type::Char, Type::Int) => Ok(()),
            (Type::Exist(id), other) | (other, Type::Exist(id)) => {
                let mut occurs = BTreeSet::new();
                other.free_exist(&mut occurs);
                if occurs.contains(id) {
                    return Err(SolveError::Occurs {
                        meta: MetaVar {
                            kind: MetaKind::Source,
                            id: *id,
                        },
                        within: Within::Source(other.clone()),
                    });
                }
                // A source metavariable can already carry a richer CBPV shape
                // from an earlier ANF binding.  Reconcile that evidence before
                // recording its source-language view so row constraints are not
                // lost between the two solver tables.
                if let Some(actual) = self.core.get(id).cloned() {
                    self.subsume_core(&actual, &lower_value_type(other))?;
                }
                if self.int_defaults.contains(id) {
                    if let Type::Exist(other_id) = other {
                        self.int_defaults.insert(*other_id);
                    }
                }
                self.types.insert(*id, other.clone());
                Ok(())
            }
            (Type::Fun(ap, ae, ar), Type::Fun(bp, be, br)) if ap.len() == bp.len() => {
                for (a, b) in ap.iter().zip(bp) {
                    self.unify_type(a, b)?;
                }
                self.unify_row(ae, be)?;
                self.unify_type(ar, br)
            }
            (Type::Con(an, aa), Type::Con(bn, ba)) if an == bn && aa.len() == ba.len() => {
                for (a, b) in aa.iter().zip(ba) {
                    self.unify_type(a, b)?;
                }
                Ok(())
            }
            (Type::App(ah, aa), Type::App(bh, ba)) => {
                self.unify_type(ah, bh)?;
                self.unify_type(aa, ba)
            }
            (Type::Tuple(a), Type::Tuple(b)) | (Type::UnboxedTuple(a), Type::UnboxedTuple(b))
                if a.len() == b.len() =>
            {
                for (a, b) in a.iter().zip(b) {
                    self.unify_type(a, b)?;
                }
                Ok(())
            }
            (Type::UnboxedRecord(a), Type::UnboxedRecord(b)) if a.len() == b.len() => {
                for ((an, a), (bn, b)) in a.iter().zip(b) {
                    if an != bn {
                        return Err(SolveError::RecordField {
                            left: *an,
                            right: *bn,
                        });
                    }
                    self.unify_type(a, b)?;
                }
                Ok(())
            }
            (Type::OrNull(a), Type::OrNull(b)) => self.unify_type(a, b),
            (Type::Row(a), Type::Row(b)) => self.unify_row(a, b),
            (Type::Coeffect(a, ar), Type::Coeffect(b, br)) if ar == br => self.unify_type(a, b),
            _ => Err(SolveError::Source {
                operands: Box::new((left.clone(), right.clone())),
            }),
        }
    }

    pub(super) fn unify_row(&mut self, left: &EffRow, right: &EffRow) -> Result<(), SolveError> {
        let left = self.resolve_row(left);
        let right = self.resolve_row(right);
        if left == right {
            return Ok(());
        }
        match (&left, &right) {
            (EffRow::Exist(id), other) | (other, EffRow::Exist(id)) => {
                // A shield alias survives resolution while its content is an
                // unsolved instantiation existential, so a resolved row can
                // still surface a solved variable here. Unify through it: the
                // constraint must land on the underlying unsolved root, never
                // overwrite the alias link or install a two-step cycle.
                let id = self.row_root(*id);
                if let EffRow::Exist(o) = other {
                    if self.row_root(*o) == id {
                        return Ok(());
                    }
                }
                let mut occurs = BTreeSet::new();
                other.free_exist_row(&mut occurs);
                let occurs: BTreeSet<u32> = occurs.into_iter().map(|o| self.row_root(o)).collect();
                if occurs.contains(&id) {
                    // A resumed handler gives the least fixed-point equation
                    // `r = labels | r`. Effect rows are sets, so its solution is
                    // exactly `labels`; discard only the recursive tail.
                    if matches!(other.tail(), EffRow::Exist(t) if self.row_root(*t) == id) {
                        self.rows.insert(
                            id,
                            EffRow::canonical(other.labels().into_iter().cloned(), EffRow::Empty),
                        );
                        return Ok(());
                    }
                    return Err(SolveError::Occurs {
                        meta: MetaVar {
                            kind: MetaKind::Row,
                            id,
                        },
                        within: Within::Row(other.clone()),
                    });
                }
                // An undemanded closure's row keeps its mark across aliasing.
                // Solving it to a fresh variable would otherwise lose the fact
                // that nothing has demanded the closure yet, and the next
                // consumer to state a fixed row would have that row copied onto
                // a closure that performs none of it.
                if self.latent_defaults.contains(&id) {
                    if let EffRow::Exist(target) = other {
                        self.latent_defaults.insert(self.row_root(*target));
                    }
                }
                self.rows.insert(id, other.clone());
                Ok(())
            }
            _ => {
                if !matches!(left, EffRow::Extend(..)) && !matches!(right, EffRow::Extend(..)) {
                    return Err(SolveError::RowTails {
                        left: left.clone(),
                        right: right.clone(),
                    });
                }
                let left_labels = left.labels();
                let right_labels = right.labels();
                if left_labels.len() != right_labels.len() {
                    return Err(SolveError::Row {
                        relation: SolveRelation::Unify,
                        left: left.clone(),
                        right: right.clone(),
                    });
                }
                for (a, b) in left_labels.iter().zip(right_labels) {
                    if a.name != b.name || a.args.len() != b.args.len() {
                        return Err(SolveError::Row {
                            relation: SolveRelation::Unify,
                            left: left.clone(),
                            right: right.clone(),
                        });
                    }
                    for (a, b) in a.args.iter().zip(&b.args) {
                        self.unify_type(a, b)?;
                    }
                }
                self.unify_row(left.tail(), right.tail())
            }
        }
    }

    pub(super) fn union_rows(
        &mut self,
        left: &EffRow,
        right: &EffRow,
    ) -> Result<EffRow, SolveError> {
        // Empty is the identity of row union. Preserve a flexible row itself,
        // rather than resolving it to a snapshot of its current lower bound:
        // later constraints must remain visible to every parent that reused
        // this union.
        if left == &EffRow::Empty {
            return Ok(right.clone());
        }
        if right == &EffRow::Empty {
            return Ok(left.clone());
        }
        let left = self.resolve_row(left);
        let right = self.resolve_row(right);
        let labelled_open_side = [&left, &right]
            .into_iter()
            .any(|row| !row.labels().is_empty() && matches!(row.tail(), EffRow::Exist(_)));
        let tail = match (left.tail(), right.tail()) {
            (a, b) if a == b => a.clone(),
            (EffRow::Empty, other) | (other, EffRow::Empty) => other.clone(),
            (EffRow::Exist(id), other) | (other, EffRow::Exist(id)) => {
                self.unify_row(&EffRow::Exist(*id), other)?;
                self.resolve_row(&EffRow::Exist(*id))
            }
            (a, b) => {
                return Err(RowUnionError::OpenTails {
                    left: a.clone(),
                    right: b.clone(),
                }
                .into());
            }
        };
        // If either side already carries a shield alias for the reconciled
        // tail's root, keep that alias: reconciliation must not re-expose the
        // raw instantiation variable a previous union deliberately shielded.
        let tail = match tail {
            EffRow::Exist(id) if !self.shield_rows.contains(&id) => {
                let root = self.row_root(id);
                let side_alias = [left.tail(), right.tail()]
                    .into_iter()
                    .find_map(|t| match t {
                        EffRow::Exist(a)
                            if self.shield_rows.contains(a) && self.row_root(*a) == root =>
                        {
                            Some(*a)
                        }
                        _ => None,
                    });
                EffRow::Exist(side_alias.unwrap_or(id))
            }
            other => other,
        };
        // A union-built head is demand at the SAME handler level as the tail's
        // eventual content, while an instantiation existential's solved content
        // is demand BEYOND a declared head (which `resolve_row` concatenates).
        // Placing union labels directly over a bare instantiation tail would
        // therefore fabricate a stack claim and double the shared labels at
        // resolve time. Shield the tail behind a fresh ambient-kind alias so
        // the surface variable's kind matches the row's construction; a tail
        // inherited from a labelled open side is a scheme-substituted stack
        // row whose head genuinely sits above the tail, so it stays raw.
        let tail = match tail {
            EffRow::Exist(id) if self.instantiation_rows.contains(&id) && !labelled_open_side => {
                if let Some(alias_id) = self.shield_alias.get(&id) {
                    EffRow::Exist(*alias_id)
                } else {
                    let alias = self.fresh_row();
                    if let EffRow::Exist(alias_id) = alias {
                        self.rows.insert(alias_id, EffRow::Exist(id));
                        self.shield_rows.insert(alias_id);
                        self.shield_alias.insert(id, alias_id);
                    }
                    alias
                }
            }
            other => other,
        };
        // A row is a multiset: a label's multiplicity is the number of enclosing
        // handlers it demands, and `mask<E>` raises it by one. The union takes the
        // per-label MAX of the two sides rather than collapsing repeats, so a
        // masked effect's tunnelled copy survives the join. This mirrors the
        // checker-side `verify::compat::union_rows`; the two must agree, because
        // the row this constructs is later re-derived and checked by that one.
        // Per name: the reconciled label plus each side's occurrence count.
        let mut names: BTreeMap<Sym, (Label, usize, usize)> = BTreeMap::new();
        for (label, is_left) in left
            .labels()
            .into_iter()
            .map(|l| (l, true))
            .chain(right.labels().into_iter().map(|l| (l, false)))
        {
            match names.get_mut(&label.name) {
                Some((existing, cl, cr)) => {
                    if existing.args.len() == label.args.len() {
                        for (a, b) in existing.args.iter().zip(&label.args) {
                            self.unify_type(a, b)?;
                        }
                        existing.args = existing
                            .args
                            .iter()
                            .map(|ty| self.resolve_type(ty))
                            .collect();
                    } else {
                        // Generated local-state rows predate explicit typed-Core
                        // evidence: a checked function row names the effect while
                        // its operation node carries the recovered cell type.
                        // Preserve the richer witness when the other occurrence is
                        // precisely the legacy zero-argument spelling.
                        if existing.args.is_empty() {
                            existing.args.clone_from(&label.args);
                        } else if !label.args.is_empty() {
                            return Err(RowUnionError::Labels {
                                left: existing.clone(),
                                right: label.clone(),
                            }
                            .into());
                        }
                    }
                    *(if is_left { cl } else { cr }) += 1;
                }
                None => {
                    names.insert(
                        label.name,
                        (label.clone(), usize::from(is_left), usize::from(!is_left)),
                    );
                }
            }
        }
        let mut out: Vec<Label> = Vec::new();
        for (label, cl, cr) in names.into_values() {
            for _ in 0..cl.max(cr) {
                out.push(label.clone());
            }
        }
        Ok(EffRow::canonical(out, tail))
    }

    pub(super) fn join_core(
        &mut self,
        left: &CoreType,
        right: &CoreType,
    ) -> Result<CoreType, SolveError> {
        let left = self.resolve_core(left);
        let right = self.resolve_core(right);
        if left == right {
            return Ok(left);
        }
        match (&left, &right) {
            (CoreType::Source(Type::Exist(_)), _) | (_, CoreType::Source(Type::Exist(_))) => {
                self.unify_core(&left, &right)?;
                Ok(self.resolve_core(&left))
            }
            (CoreType::Source(a), CoreType::Source(b)) => {
                self.unify_type(a, b)?;
                Ok(CoreType::Source(self.resolve_type(a)))
            }
            (CoreType::Thunk(a), CoreType::Thunk(b)) => {
                Ok(CoreType::Thunk(Box::new(self.join_sig(a, b)?)))
            }
            (CoreType::Function(a), CoreType::Function(b)) => {
                Ok(CoreType::Function(Box::new(self.join_fn_sig(a, b)?)))
            }
            (CoreType::Ref(a), CoreType::Ref(b)) => {
                Ok(CoreType::Ref(Box::new(self.join_core(a, b)?)))
            }
            (CoreType::ReuseToken(a), CoreType::ReuseToken(b)) => {
                Ok(CoreType::ReuseToken(Box::new(self.join_core(a, b)?)))
            }
            _ => Err(SolveError::Core {
                relation: SolveRelation::Join,
                operands: Box::new((left.clone(), right.clone())),
            }),
        }
    }

    pub(super) fn constrain_join(
        &mut self,
        target: &CoreType,
        value: &CoreType,
    ) -> Result<(), SolveError> {
        if let CoreType::Source(Type::Exist(id)) = target {
            let current = self.resolve_core(target);
            let joined = if current == *target {
                self.resolve_core(value)
            } else {
                self.join_core(&current, value)?
            };
            if joined == *target {
                // A pending application can make a handler's result lower bound
                // be the same still-flexible metavariable. This is a vacuous
                // constraint, not the recursive type `?a = F(?a)`; leave it open
                // for the resumed application to solve.
                return Ok(());
            }
            if core_occurs(*id, &joined) {
                return Err(SolveError::Occurs {
                    meta: MetaVar {
                        kind: MetaKind::Core,
                        id: *id,
                    },
                    within: Within::Joined(joined),
                });
            }
            self.core.insert(*id, joined);
            Ok(())
        } else {
            let joined = self.join_core(target, value)?;
            if self.resolve_core(target) == joined {
                return Ok(());
            }
            // The expected type here is fixed, so this comparison is the last
            // word on the join: an undemanded closure's row that reached it
            // still open will never be widened, and settling it at its lower
            // bound is what keeps an unsolved variable out of the witness
            // rather than merely out of this check.
            let joined = self.settle_latents(&joined);
            if self.resolve_core(target) == joined {
                Ok(())
            } else {
                Err(SolveError::JoinExceeds {
                    operands: Box::new((joined, self.resolve_core(target))),
                })
            }
        }
    }

    // Settle every undemanded closure row inside a value type. See
    // `settle_latent`; the walk exists because such a row can sit under any
    // number of thunk and function layers.
    fn settle_latents(&mut self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.settle_latents_sig(sig))),
            CoreType::Function(sig) => CoreType::Function(Box::new(CoreFnSig::new(
                sig.quantifiers().to_vec(),
                sig.params()
                    .iter()
                    .map(|ty| self.settle_latents(ty))
                    .collect(),
                self.settle_latents_sig(sig.body()),
            ))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.settle_latents(inner))),
            CoreType::ReuseToken(inner) => {
                CoreType::ReuseToken(Box::new(self.settle_latents(inner)))
            }
            CoreType::Source(_) | CoreType::Lowered(_) => ty.clone(),
        }
    }

    fn settle_latents_sig(&mut self, sig: &CompSig) -> CompSig {
        let result = self.settle_latents(sig.result());
        let effects = self.settle_latent(sig.effects());
        CompSig::new(result, effects)
    }

    pub(super) fn constrain_row_join(
        &mut self,
        target: &EffRow,
        value: &EffRow,
    ) -> Result<(), SolveError> {
        if let EffRow::Exist(id) = target {
            let root = self.row_root(*id);
            if root != *id {
                return self.constrain_row_join(&EffRow::Exist(root), value);
            }
            let current = self.resolve_row(target);
            let value = self.resolve_row(value);
            if value == EffRow::Empty {
                // Subsuming a pure computation contributes no lower bound to
                // an open expected row.  Leave it flexible for later
                // arguments in the same application.
                return Ok(());
            }
            if current != *target {
                if let EffRow::Exist(tail) = current.tail() {
                    // The target's concrete head already discharges those
                    // levels: rows are multisets, so forwarding the whole
                    // value would re-demand the head from the tail and stack
                    // a duplicate copy onto it. Consume the head one-to-one
                    // and forward only the remainder.
                    let head: Vec<Label> = current.labels().into_iter().cloned().collect();
                    let mut consumed = vec![false; head.len()];
                    let mut remainder = Vec::new();
                    for label in value.labels() {
                        let found = head.iter().enumerate().find(|(index, wanted)| {
                            !consumed[*index]
                                && wanted.name == label.name
                                && wanted.args.len() == label.args.len()
                        });
                        let Some((index, wanted)) = found else {
                            remainder.push(label.clone());
                            continue;
                        };
                        consumed[index] = true;
                        let wanted = wanted.clone();
                        for (actual, expected) in label.args.iter().zip(&wanted.args) {
                            self.unify_type(actual, expected)?;
                        }
                    }
                    let remainder = EffRow::canonical(remainder, value.tail().clone());
                    return self.constrain_row_join(&EffRow::Exist(*tail), &remainder);
                }
            }
            let value = if matches!(value.tail(), EffRow::Exist(t) if self.row_root(*t) == *id) {
                // Rows denote sets, so `?r = {labels | ?r}` has the least
                // solution `{labels}`.  Closing only the recursive tail keeps
                // the concrete lower bound without installing a cyclic
                // substitution.
                EffRow::canonical(value.labels().into_iter().cloned(), EffRow::Empty)
            } else {
                value
            };
            let joined = if current == *target {
                value
            } else {
                self.union_rows(&current, &value)?
            };
            self.rows.insert(*id, joined);
            Ok(())
        } else {
            self.subsume_row(value, target)
        }
    }

    fn row_root(&self, mut id: u32) -> u32 {
        let mut seen = BTreeSet::new();
        while seen.insert(id) {
            let Some(EffRow::Exist(next)) = self.rows.get(&id) else {
                break;
            };
            id = *next;
        }
        id
    }

    fn join_sig(&mut self, left: &CompSig, right: &CompSig) -> Result<CompSig, SolveError> {
        Ok(CompSig::new(
            self.join_core(left.result(), right.result())?,
            self.union_rows(left.effects(), right.effects())?,
        ))
    }

    fn join_fn_sig(
        &mut self,
        left: &CoreFnSig,
        right: &CoreFnSig,
    ) -> Result<CoreFnSig, SolveError> {
        if left.quantifiers() != right.quantifiers() || left.params().len() != right.params().len()
        {
            return Err(SolveError::Signature {
                relation: SolveRelation::Join,
                operands: Box::new((left.clone(), right.clone())),
            });
        }
        for (a, b) in left.params().iter().zip(right.params()) {
            self.unify_core(a, b)?;
        }
        Ok(CoreFnSig::new(
            left.quantifiers().to_vec(),
            left.params()
                .iter()
                .map(|ty| self.resolve_core(ty))
                .collect(),
            self.join_sig(left.body(), right.body())?,
        ))
    }

    pub(super) fn zonk_instantiation(
        &self,
        instantiation: Vec<CoreInstantiation>,
    ) -> Vec<CoreInstantiation> {
        instantiation
            .into_iter()
            .map(|argument| match argument {
                CoreInstantiation::Type(ty) => CoreInstantiation::Type(self.resolve_type(&ty)),
                CoreInstantiation::Row(row) => CoreInstantiation::Row(self.resolve_row(&row)),
            })
            .collect()
    }
}

fn core_occurs(id: u32, ty: &CoreType) -> bool {
    fn source_occurs(id: u32, ty: &Type) -> bool {
        let mut types = BTreeSet::new();
        ty.free_exist(&mut types);
        types.contains(&id)
    }

    match ty {
        CoreType::Source(ty) => source_occurs(id, ty),
        CoreType::Thunk(sig) => {
            core_occurs(id, sig.result())
                || sig
                    .effects()
                    .labels()
                    .iter()
                    .any(|label| label.args.iter().any(|ty| source_occurs(id, ty)))
        }
        CoreType::Function(sig) => {
            sig.params().iter().any(|ty| core_occurs(id, ty))
                || core_occurs(id, sig.body().result())
                || sig
                    .body()
                    .effects()
                    .labels()
                    .iter()
                    .any(|label| label.args.iter().any(|ty| source_occurs(id, ty)))
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => core_occurs(id, inner),
        CoreType::Lowered(LoweredType::Word) => false,
        CoreType::Lowered(
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row),
        ) => row
            .labels()
            .iter()
            .any(|label| label.args.iter().any(|ty| source_occurs(id, ty))),
    }
}

pub(super) fn free_row_vars(
    row: &EffRow,
    type_vars: &mut BTreeSet<Sym>,
    row_vars: &mut BTreeSet<Sym>,
) {
    if let EffRow::Var(name) = row.tail() {
        row_vars.insert(*name);
    }
    for label in row.labels() {
        for argument in &label.args {
            argument.free_ty_vars(type_vars);
            argument.free_row_vars(row_vars);
        }
    }
}

pub(super) fn free_core_vars(
    ty: &CoreType,
    type_vars: &mut BTreeSet<Sym>,
    row_vars: &mut BTreeSet<Sym>,
) {
    match ty {
        CoreType::Source(ty) => {
            ty.free_ty_vars(type_vars);
            ty.free_row_vars(row_vars);
        }
        CoreType::Thunk(signature) => {
            free_core_vars(signature.result(), type_vars, row_vars);
            free_row_vars(signature.effects(), type_vars, row_vars);
        }
        CoreType::Function(signature) => {
            let mut nested_types = BTreeSet::new();
            let mut nested_rows = BTreeSet::new();
            for param in signature.params() {
                free_core_vars(param, &mut nested_types, &mut nested_rows);
            }
            free_core_vars(
                signature.body().result(),
                &mut nested_types,
                &mut nested_rows,
            );
            free_row_vars(
                signature.body().effects(),
                &mut nested_types,
                &mut nested_rows,
            );
            for quantifier in signature.quantifiers() {
                match quantifier {
                    CoreQuantifier::Type(name) => {
                        nested_types.remove(name);
                    }
                    CoreQuantifier::Row(name) => {
                        nested_rows.remove(name);
                    }
                }
            }
            type_vars.extend(nested_types);
            row_vars.extend(nested_rows);
        }
        CoreType::Ref(inner) | CoreType::ReuseToken(inner) => {
            free_core_vars(inner, type_vars, row_vars);
        }
        CoreType::Lowered(LoweredType::Word) => {}
        CoreType::Lowered(
            LoweredType::Eff(row) | LoweredType::Queue(row) | LoweredType::QueueView(row),
        ) => free_row_vars(row, type_vars, row_vars),
    }
}
