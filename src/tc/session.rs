//! The mutable state of one inference session.
//!
//! `Tc` carries every table the checker accumulates while walking a program:
//! the ordered solver context, deferred resolution queues, recorded node
//! facts, and the ambient effect/handler scopes. The types here are state
//! only; the algorithms that drive them live in `infer`, `context`,
//! `subsume`, and the other sibling modules.

use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::context::Renames;
use super::{
    Canon, ClassInfo, ConstrainedSchemes, CtorInfo, DataInfo, Dict, EffOpInfo, Env, FieldRef,
    InstInfo, InstKeys, PathRes,
};
use crate::error::{HoleReport, TypeError};
use crate::hir::HandlerResidual;
use crate::sym::Sym;
use crate::syntax::ast::NodeId;
use crate::types::ty::{EffRow, Effects, Label, Type};

// A declaration's span facts, held until its scheme is built: the node types to
// zonk and the effect rows to render tooltips from.
pub(super) type DeferredSpans = (Vec<(NodeId, Type)>, Vec<(NodeId, EffRow)>);

// A subsumption failure. `Fail` is a plain mismatch the caller renders with its
// own span and message. `Keep` is a mismatch that already carries its final,
// more precise message (a dimension clash naming both lengths): it survives a
// caller's structural override, taking only the caller's span. `Ice` is a broken
// internal invariant that must surface as a diagnostic instead of a raw backtrace.
pub(super) enum TcErr {
    Fail(String),
    Keep(String),
    Ice(String),
}

impl TcErr {
    // Attach a span: mismatches become located errors, ICEs pass through.
    pub(super) fn at(self, span: Span) -> TypeError {
        match self {
            Self::Fail(msg) | Self::Keep(msg) => TypeError::TypeFailure { span, msg },
            Self::Ice(msg) => TypeError::InternalInvariant { msg },
        }
    }

    // Replace a coarse mismatch message; a `Keep` message and ICEs pass through.
    pub(super) fn or_fail(self, msg: String) -> Self {
        match self {
            Self::Fail(_) => Self::Fail(msg),
            kept @ (Self::Keep(_) | Self::Ice(_)) => kept,
        }
    }

    // Replace a coarse mismatch with the caller's diagnostic. A `Keep` message is
    // preserved but adopts the fallback's span; ICEs pass through.
    pub(super) fn or(self, fallback: TypeError) -> TypeError {
        match self {
            Self::Fail(_) => fallback,
            Self::Keep(msg) => match fallback.span() {
                Some(&span) => TypeError::TypeFailure { span, msg },
                None => TypeError::TypeFailure {
                    span: Span::default(),
                    msg,
                },
            },
            Self::Ice(msg) => TypeError::InternalInvariant { msg },
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum Entry {
    Uni(Sym),
    RowUni(Sym),
    Ex(u32),
    Solved(u32, Type),
    Marker(u32),
    ExRow(u32),
    SolvedRow(u32, EffRow),
}

// One dispatch site: the constraints instantiated at `span`, resolved together
// into the site's dict vector at the end of the declaration.
pub(super) struct Wanted {
    // Identity of the dispatch site, the key its resolved dicts land under.
    pub(super) id: NodeId,
    // Source span, kept for the ambiguity/no-instance diagnostic's caret.
    pub(super) span: Span,
    pub(super) items: Vec<(String, Type, Option<String>)>,
}

// A deferred indexed read/write, resolved by head-type dispatch at the end of
// the declaration. `recv`/`key` are the synthed operand types (applied at
// resolution); `result` is the element existential to solve (and the read's
// result type); `val` is `Some(value type)` for a write (checked against the
// element type), `None` for a read (which also performs `Fail`).
pub(super) struct IndexOp {
    pub(super) span: Span,
    pub(super) recv_span: Span,
    pub(super) recv: Type,
    pub(super) key: Type,
    pub(super) result: u32,
    pub(super) val: Option<Type>,
}

// Inference-time form of a hole report. Types and the environment remain live
// until `resolve_all` has solved the surrounding constraints, then `flush_holes`
// zonks and serializes them before the checker context is reset.
pub(super) struct HoleSite {
    pub(super) name: String,
    pub(super) span: Span,
    pub(super) expected: Type,
    pub(super) effects: EffRow,
    pub(super) env: Env,
}

pub(super) struct Tc<'a> {
    pub(super) ctx: Vec<Entry>,
    pub(super) next: u32,
    pub(super) seeds: u32,
    pub(super) ctors: &'a BTreeMap<String, CtorInfo>,
    pub(super) data: &'a BTreeMap<String, DataInfo>,
    pub(super) eff_ops: &'a BTreeMap<String, EffOpInfo>,
    pub(super) field_res: BTreeMap<NodeId, FieldRef>,
    pub(super) unboxed_field: BTreeMap<NodeId, (usize, usize)>,
    pub(super) path_res: PathRes,
    pub(super) fixed: BTreeMap<NodeId, Type>,
    pub(super) span_types: BTreeMap<NodeId, Type>,
    // Canonical `type ! row` strings for the opt-in `dump typespans` analysis.
    // Ordinary checking leaves these tables empty, so tooltip collection cannot
    // perturb the established inference path or checked-HIR fixture.
    pub(super) track_tooltips: bool,
    pub(super) pending_tooltip_rows: Vec<(NodeId, EffRow)>,
    pub(super) tooltip_rows: BTreeMap<NodeId, String>,
    pub(super) method_effects: BTreeMap<Sym, Effects>,
    pub(super) touched_tooltip_rows: BTreeSet<u32>,
    pub(super) tooltip_row_scaffolds: BTreeSet<u32>,
    // Per-declaration principal-body-effect witnesses ([`BodyWitness`]),
    // recorded by `infer_body` and consumed by `finalize_fn`'s borrow rule.
    pub(super) body_witness: BTreeMap<String, BodyWitness>,
    pub(super) pending: Vec<(NodeId, Type)>,
    // The naming the declaration being flushed gave its own variables, so every
    // span inside it renders under one scheme instead of canonicalizing afresh
    // per node and calling the same variable `a` in one place and `c` in another.
    pub(super) decl_renames: Option<Renames>,
    // Hold each member's spans until the whole recursion group is solved. A later
    // sibling may still constrain an earlier member's parameters.
    pub(super) deferred_spans: std::collections::VecDeque<DeferredSpans>,
    pub(super) hole_sites: Vec<HoleSite>,
    pub(super) holes: Vec<HoleReport>,
    // Each `This(e)` site, with the span of the whole expression and the element
    // type synthesized for `e`. After inference solves every existential, the
    // element is zonked and checked to have a non-null, single-word representation
    // (`is_or_null_element`), so `OrNull` formed by inference is held to the same
    // soundness rule as a written `OrNull(a)` annotation. `Null` needs no entry:
    // it is the null word for any element.
    pub(super) or_null_sites: Vec<(Span, Type)>,
    pub(super) classes: &'a BTreeMap<Sym, ClassInfo>,
    pub(super) instances: &'a BTreeMap<Sym, InstInfo>,
    pub(super) inst_keys: &'a InstKeys,
    pub(super) canonical: &'a Canon,
    pub(super) constrained: ConstrainedSchemes,
    // The named function whose body is currently being checked, with its self
    // type and the class constraints in force. `None` when no self scope is
    // active: the Option makes the "not checking a named body" state explicit
    // and the non-nesting invariant enforceable by save/restore.
    pub(super) cur_self: Option<SelfRef>,
    pub(super) wanted: Vec<Wanted>,
    // Numeric/comparison operands left ambiguous: each (node id, span, operand
    // type, class) is resolved in one pass at the end of the declaration
    // (`resolve_all`), so a later use can fix the type before the default or
    // class obligation applies. `class` is `None` for arithmetic, or `Eq`/`Ord`
    // for comparisons whose resolved ADTs must raise a dictionary obligation.
    pub(super) num_default: Vec<(NodeId, Span, Type, Option<&'static str>)>,
    // Unary-minus operands left ambiguous at synth: resolved in the same
    // `resolve_all` pass as `num_default`, but the signed lanes differ. Negation
    // spans `Int`/`I64`/`Float` (a leftover existential defaults to `Int`), while
    // `U64` is rejected because it is unsigned. Kept separate from `num_default`,
    // whose integer operators reject a `Float` operand.
    pub(super) neg_default: Vec<(NodeId, Span, Type)>,
    // Indexed reads/writes (`a[i]`, `a[i] := v`) whose receiver type was not yet
    // resolved at synth (a `var`'s state existential is solved only once its
    // initializer is checked). Each is dispatched on the receiver's head type in
    // one pass at the end of the declaration (`resolve_all`, before `num_default`
    // so an index's element type is known to numeric defaulting).
    pub(super) index_ops: Vec<IndexOp>,
    pub(super) dicts: BTreeMap<NodeId, Vec<Dict>>,
    // Innermost-last instantiation scopes for parametric effects: each entry
    // ties an effect name to the type args in force (handler or latent row).
    pub(super) row_ctx: Vec<(Sym, Vec<Type>)>,
    // The ambient effect obligation: an open row existential (`tail`) that every
    // effectful action in the code under check unifies into, plus the concrete
    // labels already in its fixed prefix. A handler scopes a fresh one for its
    // body and discharges the labels it names. Set per declaration / per handler
    // body; `None` when no scope is active. Tail and prefix move in lockstep so
    // they cannot desync.
    pub(super) cur_row: Option<RowScope>,
    // Innermost-last stack of active handler bodies. A `mask<E>` marks the
    // nearest frame that handles `E` as not discharging it, so the masked
    // operation tunnels past that one handler and stays in the residual row
    // (the handler it skips is the innermost enclosing one, by construction).
    pub(super) handler_stack: Vec<HandlerFrame>,
    // Operation-local effect uses for the expression currently being checked.
    // Public rows remain effect-granular; this private summary lets adjacent
    // partial handlers cancel complementary, syntactically known operations.
    pub(super) operation_uses: OperationUses,
    // Exact summaries for handler continuation binders. Calling `resume` runs
    // the already-recorded residual body, so its deliberately open function row
    // must not turn a known local summary into an opaque one.
    //
    // Keyed on the row existential minted for the binder's type, never on its
    // spelling: the existential is fresh per handler clause and appears in
    // exactly one `Env` entry, so a nested clause cannot collide with an
    // enclosing one and an inner binding that shadows the continuation's name
    // cannot inherit its summary. `precise_call` performs the lookup through
    // `Env`, the scoping authority.
    pub(super) precise_calls: BTreeMap<u32, OperationUses>,
    // Every handler expression must produce exactly one checked-HIR residual
    // fact. The marker set lets the HIR lint detect a missing or stale fact.
    pub(super) handler_nodes: BTreeSet<NodeId>,
    pub(super) handler_residuals: BTreeMap<NodeId, HandlerResidual>,
    // Local `let` values generalized to a scheme with at least one type
    // quantifier, keyed by the bound expression's node. Core's `Bind` carries no
    // scheme, so elaboration expands these at each use instead of binding one
    // monotype; see `generalize_let`.
    pub(super) generalized_lets: BTreeSet<NodeId>,
}

// A private operation-level refinement of an effect row. Each effect maps to
// the operations this expression may perform. A call through a public function
// row contributes every declared operation of each named effect; direct op
// syntax contributes only that op. `open_row` preserves an unenumerable row
// tail and prevents a partial handler from claiming complete discharge.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct OperationUses {
    pub(super) by_effect: BTreeMap<Sym, EffectOperationUses>,
    pub(super) open_row: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum EffectOperationUses {
    Known(BTreeSet<Sym>),
    All,
}

impl OperationUses {
    pub(super) fn insert(&mut self, effect: Sym, operation: Sym) {
        match self
            .by_effect
            .entry(effect)
            .or_insert_with(|| EffectOperationUses::Known(BTreeSet::new()))
        {
            EffectOperationUses::Known(operations) => {
                operations.insert(operation);
            }
            EffectOperationUses::All => {}
        }
    }

    pub(super) fn insert_all(&mut self, effect: Sym) {
        self.by_effect.insert(effect, EffectOperationUses::All);
    }

    pub(super) fn merge(&mut self, other: Self) {
        self.open_row |= other.open_row;
        for (effect, operations) in other.by_effect {
            match (
                self.by_effect
                    .entry(effect)
                    .or_insert_with(|| EffectOperationUses::Known(BTreeSet::new())),
                operations,
            ) {
                (slot, EffectOperationUses::All) => *slot = EffectOperationUses::All,
                (EffectOperationUses::Known(into), EffectOperationUses::Known(from)) => {
                    into.extend(from);
                }
                (EffectOperationUses::All, EffectOperationUses::Known(_)) => {}
            }
        }
    }

    // Subtract the operations a handler discharges from this summary. `masked`
    // are the handled effects that keep a surplus copy on the residual row after
    // this handler cancelled one (a `mask` inside the body tunnelled a copy past
    // it): their operations are NOT subtracted, because they still flow to an
    // enclosing handler. The caller computes this as the live residual effects
    // intersected with the discharge candidates, so an effect present only
    // because a `partial` handler never discharged it is not counted as masked.
    pub(super) fn subtract(
        mut self,
        handled: &BTreeMap<Sym, BTreeSet<Sym>>,
        exhaustive: &BTreeSet<Sym>,
        masked: &BTreeSet<Sym>,
    ) -> Self {
        for (effect, operations) in handled {
            if masked.contains(effect) {
                continue;
            }
            let remove_effect = self
                .by_effect
                .get_mut(effect)
                .is_some_and(|uses| match uses {
                    EffectOperationUses::Known(uses) => {
                        for operation in operations {
                            uses.remove(operation);
                        }
                        uses.is_empty()
                    }
                    EffectOperationUses::All => exhaustive.contains(effect),
                });
            if remove_effect {
                self.by_effect.remove(effect);
            }
        }
        self
    }

    pub(super) fn operations(&self) -> Vec<Sym> {
        self.by_effect
            .values()
            .filter_map(|uses| match uses {
                EffectOperationUses::Known(operations) => Some(operations),
                EffectOperationUses::All => None,
            })
            .flatten()
            .copied()
            .collect()
    }

    pub(super) fn opaque_effects(&self) -> Vec<Sym> {
        self.by_effect
            .iter()
            .filter_map(|(effect, uses)| {
                matches!(uses, EffectOperationUses::All).then_some(*effect)
            })
            .collect()
    }
}

// One active handler while its body is checked: the effects its arms handle. A
// `mask` inside the body no longer needs recording here -- it adds a real copy
// of the effect to the multiset row, which this handler's single-occurrence
// discharge leaves a surplus of, so the tunnelled effect survives on the row
// itself rather than in a side channel.
pub(super) struct HandlerFrame {
    pub(super) handled: BTreeSet<Sym>,
}

// Ambient self-reference state for the body of a named declaration.
pub(super) struct SelfRef {
    pub(super) name: String,
    pub(super) self_ty: Type,
    pub(super) constraints: Vec<(String, Type)>,
}

// Open row existential tail plus the concrete labels in its fixed prefix.
// Absorbing a callee row skips the prefix labels so a direct named call does
// not duplicate a label. The prefix keeps whole labels, not bare names: the
// skip must equate a parametric label's arguments against the prefix's
// instantiation, or a lambda body performing `Tag(String)` under an arrow
// annotated `! {Tag(Int) | e}` would drop the label unchecked.
pub(super) struct RowScope {
    pub(super) tail: u32,
    pub(super) prefix: Vec<Label>,
    // The contextual permission reported at a hole. This is separate from the
    // mutable accumulator above: an explicitly pure context stays `{}` even
    // while the accumulator is represented by a fresh row existential.
    pub(super) expected: EffRow,
}

/// The recorded principal-body-effect witness of one function declaration: the
/// body's ambient effect row as inference solved it, read before
/// `default_open_rows` re-opens a pure row for context fit (which destroys the
/// closedness fact). `effects` are the concrete labels the body accumulated;
/// `closed` records that the row's tail stayed the declaration's own fresh
/// ambient (or emptied) rather than solving to a row that also flows through
/// the interface, so nothing the caller supplies can make the body perform or
/// suspend. The borrow rule consumes this witness directly instead of
/// reverse-engineering closedness from the generalized scheme.
pub(super) struct BodyWitness {
    pub(super) effects: Effects,
    pub(super) closed: bool,
}
