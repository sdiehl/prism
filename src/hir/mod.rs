//! The checked HIR: the self-contained artifact elaboration consumes.
//!
//! The typechecker historically communicated with elaboration through six
//! NodeId-keyed side tables on [`Checked`], joined at each expression by
//! `map.get(&e.id)`. Those tables are gone: checking now produces one
//! [`NodeFacts`] value (dense per-node semantic facts), and elaboration reads
//! it only through a [`CheckedHir`], built by [`build`] (the sole
//! constructor) and proof-checked by [`lint::lint_hir`] unconditionally in
//! debug and test builds.
//!
//! The carried families are resolution ([`NodeRes`]: field access, unboxed
//! projection, update paths), dictionary evidence, numeric lane selection,
//! zonked node types, and operation-local handler residual witnesses.
//!
//! There is deliberately no parallel elaboration path: elaboration constructs
//! its `CheckedHir` through [`build`] (whole programs) or [`build_for_expr`]
//! (the REPL's re-inferred expressions, which carry their own evidence).

pub mod lint;

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::sym::Sym;
use crate::syntax::ast::NodeId;
use crate::types::{Checked, Dict, DictTable, PathRes, Type};

/// A node's resolution fact: what checking decided this syntactic site means,
/// resolved to constructor-and-offset form so elaboration makes no new
/// type-system decisions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NodeRes {
    /// A record field access `e.f`: the constructor name, the field's index,
    /// and the constructor arity.
    Field(String, usize, usize),
    /// An unboxed record projection `e.#f`: the field's index in the record's
    /// type field order, and the record arity.
    UnboxedField(usize, usize),
    /// A record update path `e { p.q = v }`: one rebuild chain per path, each
    /// step a (constructor, field index, arity) triple.
    Paths(Vec<Vec<(String, usize, usize)>>),
}

/// Operation-local residual evidence for one checked handler expression.
///
/// `forwarded_operations` are operations used by the handled body but omitted
/// by this handler. `residual_operations` additionally includes effects used by
/// the handler arms. Public function rows remain effect-label rows; this fact is
/// the precise local witness consumed while moving elaboration onto typed Core.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandlerResidual {
    #[serde(default)]
    forwarded_operations: Vec<Sym>,
    #[serde(default)]
    forwarded_effects: Vec<Sym>,
    #[serde(default)]
    residual_operations: Vec<Sym>,
    #[serde(default)]
    residual_effects: Vec<Sym>,
    #[serde(default)]
    open_row: bool,
}

impl HandlerResidual {
    pub(crate) fn new(
        mut forwarded_operations: Vec<Sym>,
        mut forwarded_effects: Vec<Sym>,
        mut residual_operations: Vec<Sym>,
        mut residual_effects: Vec<Sym>,
        open_row: bool,
    ) -> Self {
        let canonicalize = |operations: &mut Vec<Sym>| {
            operations.sort_by_key(|operation| operation.as_str());
            operations.dedup();
        };
        canonicalize(&mut forwarded_operations);
        canonicalize(&mut forwarded_effects);
        canonicalize(&mut residual_operations);
        canonicalize(&mut residual_effects);
        Self {
            forwarded_operations,
            forwarded_effects,
            residual_operations,
            residual_effects,
            open_row,
        }
    }

    /// Operations the handled body forwards through this handler.
    #[must_use]
    pub fn forwarded_operations(&self) -> &[Sym] {
        &self.forwarded_operations
    }

    /// Effect labels whose body operation subset is opaque at this handler.
    #[must_use]
    pub fn forwarded_effects(&self) -> &[Sym] {
        &self.forwarded_effects
    }

    /// Operations remaining after body subtraction and handler-arm union.
    #[must_use]
    pub fn residual_operations(&self) -> &[Sym] {
        &self.residual_operations
    }

    /// Effect labels whose complete expression residual is opaque.
    #[must_use]
    pub fn residual_effects(&self) -> &[Sym] {
        &self.residual_effects
    }

    /// Whether an unenumerable row tail also remains.
    #[must_use]
    pub const fn has_open_row(&self) -> bool {
        self.open_row
    }
}

/// Every per-node semantic fact checking established, dense by `NodeId`.
///
/// The single cross-phase carrier of node-keyed checked state: resolution
/// facts, dictionary evidence at dispatch sites, the concrete numeric lane a
/// literal or operator site fixed to, and the zonked type synthesized for a
/// node. Constructed once by the checker ([`NodeFacts::from_tables`]) and
/// read only through a [`CheckedHir`].
#[derive(Clone, Debug, Default)]
pub struct NodeFacts {
    res: Vec<Option<NodeRes>>,
    evidence: Vec<Option<Vec<Dict>>>,
    lane: Vec<Option<Type>>,
    ty: Vec<Option<Type>>,
    // Presentation-only facts produced by the opt-in typed-tooltip checker.
    // They are intentionally outside the checked-HIR wire schema: elaboration
    // never reads them and existing HIR fixture bytes stay unchanged.
    tooltip: Vec<Option<String>>,
    handler_nodes: Vec<bool>,
    handler_residual: Vec<Option<HandlerResidual>>,
}

fn place_dense<T>(table: &mut Vec<Option<T>>, index: usize, value: Option<T>) {
    if table.len() <= index {
        table.resize_with(index + 1, || None);
    }
    table[index] = value;
}

fn dense<T>(m: BTreeMap<NodeId, T>) -> Vec<Option<T>> {
    let mut v: Vec<Option<T>> = Vec::new();
    for (id, fact) in m {
        let i = id.0 as usize;
        if v.len() <= i {
            v.resize_with(i + 1, || None);
        }
        v[i] = Some(fact);
    }
    v
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde skip_serializing_if requires a predicate over &bool"
)]
const fn is_false(value: &bool) -> bool {
    !*value
}

/// The facts recorded for one node, borrowed for iteration. The read shape the
/// versioned HIR fixture export walks: whichever of resolution, dictionary
/// evidence, numeric lane, zonked type, and handler residual checking recorded
/// for the node.
pub(crate) struct NodeFactRefs<'a> {
    pub res: Option<&'a NodeRes>,
    pub evidence: Option<&'a [Dict]>,
    pub lane: Option<&'a Type>,
    pub ty: Option<&'a Type>,
    pub handler_residual: Option<&'a HandlerResidual>,
}

#[derive(Serialize, Deserialize)]
struct NodeFactWire {
    id: u32,
    res: Option<NodeRes>,
    evidence: Option<Vec<Dict>>,
    lane: Option<String>,
    ty: Option<String>,
    #[serde(default, skip_serializing_if = "is_false")]
    handler: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    handler_residual: Option<HandlerResidual>,
}

impl NodeFacts {
    pub(crate) fn to_json(&self) -> Result<String, serde_json::Error> {
        let rows = self
            .iter()
            .map(|(id, facts)| NodeFactWire {
                id,
                res: facts.res.cloned(),
                evidence: facts.evidence.map(<[Dict]>::to_vec),
                lane: facts.lane.map(Type::show),
                ty: facts.ty.map(Type::show),
                handler: self
                    .handler_nodes
                    .get(id as usize)
                    .copied()
                    .unwrap_or(false),
                handler_residual: facts.handler_residual.cloned(),
            })
            .collect::<Vec<_>>();
        serde_json::to_string(&rows)
    }

    pub(crate) fn from_json(text: &str) -> Result<Self, String> {
        let rows: Vec<NodeFactWire> =
            serde_json::from_str(text).map_err(|error| error.to_string())?;
        if !rows.windows(2).all(|pair| pair[0].id < pair[1].id) {
            return Err("checked HIR facts are not in canonical node order".to_string());
        }
        let mut facts = Self::default();
        for row in rows {
            let index = row.id as usize;
            place_dense(&mut facts.res, index, row.res);
            place_dense(&mut facts.evidence, index, row.evidence);
            let parse = |value: Option<String>| {
                value
                    .map(|ty| {
                        crate::tc::parse_checked_signature("checked-body", &ty)
                            .map_err(|error| error.to_string())
                    })
                    .transpose()
            };
            place_dense(&mut facts.lane, index, parse(row.lane)?);
            place_dense(&mut facts.ty, index, parse(row.ty)?);
            if facts.handler_nodes.len() <= index {
                facts.handler_nodes.resize(index + 1, false);
            }
            facts.handler_nodes[index] = row.handler;
            place_dense(&mut facts.handler_residual, index, row.handler_residual);
        }
        Ok(facts)
    }

    /// Every node carrying at least one fact, in ascending `NodeId` order,
    /// paired with the facts recorded for it (the dense table index is the
    /// node's decimal id). The fixture export's sole read window onto the dense
    /// per-node tables.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (u32, NodeFactRefs<'_>)> {
        let n = self
            .res
            .len()
            .max(self.evidence.len())
            .max(self.lane.len())
            .max(self.ty.len())
            .max(self.handler_nodes.len())
            .max(self.handler_residual.len());
        (0..n).filter_map(move |i| {
            let refs = NodeFactRefs {
                res: self.res.get(i).and_then(Option::as_ref),
                evidence: self
                    .evidence
                    .get(i)
                    .and_then(Option::as_ref)
                    .map(Vec::as_slice),
                lane: self.lane.get(i).and_then(Option::as_ref),
                ty: self.ty.get(i).and_then(Option::as_ref),
                handler_residual: self.handler_residual.get(i).and_then(Option::as_ref),
            };
            let empty = refs.res.is_none()
                && refs.evidence.is_none()
                && refs.lane.is_none()
                && refs.ty.is_none()
                && !self.handler_nodes.get(i).copied().unwrap_or(false)
                && refs.handler_residual.is_none();
            // The dense index is the node's `NodeId`, itself a `u32`, so it fits.
            (!empty).then(|| (u32::try_from(i).expect("node index fits u32"), refs))
        })
    }

    /// Assemble from the checker's working tables, consuming them: the one
    /// conversion point between inference's incremental maps and the dense
    /// artifact elaboration reads.
    #[must_use]
    #[expect(
        clippy::too_many_arguments,
        reason = "the sole checked-HIR conversion keeps each inference fact family explicit"
    )]
    pub fn from_tables(
        field_res: BTreeMap<NodeId, (String, usize, usize)>,
        unboxed_field: BTreeMap<NodeId, (usize, usize)>,
        path_res: PathRes,
        fixed: BTreeMap<NodeId, Type>,
        span_types: BTreeMap<NodeId, Type>,
        dicts: DictTable,
        tooltips: BTreeMap<NodeId, String>,
        handler_nodes: BTreeSet<NodeId>,
        handler_residuals: BTreeMap<NodeId, HandlerResidual>,
    ) -> Self {
        let place = |res: &mut Vec<Option<NodeRes>>, id: NodeId, fact: NodeRes| {
            let i = id.0 as usize;
            if res.len() <= i {
                res.resize_with(i + 1, || None);
            }
            res[i] = Some(fact);
        };
        let mut res: Vec<Option<NodeRes>> = Vec::new();
        for (id, (c, i, n)) in field_res {
            place(&mut res, id, NodeRes::Field(c, i, n));
        }
        for (id, (idx, arity)) in unboxed_field {
            place(&mut res, id, NodeRes::UnboxedField(idx, arity));
        }
        for (id, chains) in path_res {
            place(&mut res, id, NodeRes::Paths(chains));
        }
        let handler_len = handler_nodes
            .iter()
            .map(|id| id.0 as usize + 1)
            .max()
            .unwrap_or(0);
        let mut dense_handler_nodes = vec![false; handler_len];
        for id in handler_nodes {
            dense_handler_nodes[id.0 as usize] = true;
        }
        Self {
            res,
            evidence: dense(dicts),
            lane: dense(fixed),
            ty: dense(span_types),
            tooltip: dense(tooltips),
            handler_nodes: dense_handler_nodes,
            handler_residual: dense(handler_residuals),
        }
    }

    /// The canonical `type ! effect-row` text computed for a tooltip node.
    pub(crate) fn tooltip(&self, id: NodeId) -> Option<&str> {
        self.tooltip.get(id.0 as usize).and_then(Option::as_deref)
    }
}

/// The checked HIR over one checked program.
///
/// The only view through which elaboration reads per-node facts. For the
/// REPL's re-inferred expressions, an evidence override carries the
/// expression's own dictionaries (its fresh `NodeId`s are disjoint from the
/// session program's).
#[derive(Debug)]
pub struct CheckedHir<'a> {
    pub checked: &'a Checked,
    facts: &'a NodeFacts,
    evidence_override: Option<Vec<Option<Vec<Dict>>>>,
}

impl<'a> CheckedHir<'a> {
    /// The resolution fact recorded for a node, if checking recorded one.
    #[must_use]
    pub fn res(&self, id: NodeId) -> Option<&NodeRes> {
        self.facts.res.get(id.0 as usize).and_then(Option::as_ref)
    }

    /// The dictionary evidence recorded at a dispatch site.
    #[must_use]
    pub fn evidence(&self, id: NodeId) -> Option<&[Dict]> {
        let table = self
            .evidence_override
            .as_ref()
            .unwrap_or(&self.facts.evidence);
        table
            .get(id.0 as usize)
            .and_then(Option::as_ref)
            .map(Vec::as_slice)
    }

    /// The concrete numeric lane a literal or operator site fixed to.
    #[must_use]
    pub fn lane(&self, id: NodeId) -> Option<&Type> {
        self.facts.lane.get(id.0 as usize).and_then(Option::as_ref)
    }

    /// The zonked type checking synthesized for a node.
    #[must_use]
    pub fn node_type(&self, id: NodeId) -> Option<&Type> {
        self.facts.ty.get(id.0 as usize).and_then(Option::as_ref)
    }

    /// The operation-local residual witness for a checked handler expression.
    #[must_use]
    pub fn handler_residual(&self, id: NodeId) -> Option<&'a HandlerResidual> {
        self.facts
            .handler_residual
            .get(id.0 as usize)
            .and_then(Option::as_ref)
    }
}

// Lint in debug and test builds; a violation is a compiler bug (checking
// recorded an inconsistent fact), never a user error. Not `const`: under test
// and debug the body calls the non-const `lint_hir`; clippy only sees the
// trivial release body.
#[allow(clippy::missing_const_for_fn)]
fn linted(hir: CheckedHir<'_>) -> CheckedHir<'_> {
    #[cfg(any(test, debug_assertions))]
    {
        let violations = lint::lint_hir(&hir);
        assert!(
            violations.is_empty(),
            "lint_hir: malformed checked HIR (compiler bug):\n{}",
            violations
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
    hir
}

/// Build the checked HIR over a checked program's own facts. The sole
/// whole-program constructor: elaboration consumes only what passed here.
#[must_use]
pub fn build(checked: &Checked) -> CheckedHir<'_> {
    linted(CheckedHir {
        checked,
        facts: &checked.facts,
        evidence_override: None,
    })
}

/// Build the checked HIR for a single re-inferred expression (the REPL).
///
/// The session program's facts, with the expression's own dictionary evidence
/// overriding the evidence table (its fresh `NodeId`s are meaningless against
/// the session's).
#[must_use]
pub fn build_for_expr<'a>(checked: &'a Checked, dicts: &DictTable) -> CheckedHir<'a> {
    linted(CheckedHir {
        checked,
        facts: &checked.facts,
        evidence_override: Some(dense(dicts.clone())),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::{parse, ParseResult};
    use crate::sym::Sym;
    use crate::syntax::desugar::desugar;
    use crate::types::{check, ClassInfo};

    fn checked(src: &str) -> Checked {
        let ParseResult { program, .. } = parse(src).expect("parses");
        let core = desugar(program).expect("desugars");
        check(&core).expect("checks")
    }

    const SRC: &str = "type Point = Point { x: Int, y: Int }\n\
                       fn get_x(p : Point) : Int = p.x\n\
                       fn main() : Unit = println(get_x(Point { x = 1, y = 2 }))\n";

    #[test]
    fn build_lints_clean_on_checked_output() {
        let c = checked(SRC);
        let hir = build(&c);
        assert!(lint::lint_hir(&hir).is_empty());
        // The field access recorded a resolution the HIR serves.
        assert!(c
            .facts
            .res
            .iter()
            .flatten()
            .any(|r| matches!(r, NodeRes::Field(ctor, 0, 2) if ctor == "Point")));
    }

    // Negative tests for the validation transition: a fabricated fact that
    // does not check against the constructor environment must be reported.
    #[test]
    fn lint_rejects_unknown_ctor() {
        let c = checked(SRC);
        let facts = NodeFacts {
            res: vec![Some(NodeRes::Field("NoSuchCtor".into(), 0, 2))],
            ..NodeFacts::default()
        };
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert_eq!(lint::lint_hir(&hir).len(), 1);
    }

    #[test]
    fn lint_rejects_wrong_arity_and_oob_index() {
        let c = checked(SRC);
        let facts = NodeFacts {
            res: vec![
                // Point's declared arity is 2, not 3.
                Some(NodeRes::Field("Point".into(), 0, 3)),
                // Index past the recorded arity.
                Some(NodeRes::UnboxedField(2, 2)),
                // An update path with an empty chain.
                Some(NodeRes::Paths(vec![vec![]])),
            ],
            ..NodeFacts::default()
        };
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert_eq!(lint::lint_hir(&hir).len(), 3);
    }

    #[test]
    fn lint_rejects_unknown_instance_evidence() {
        let c = checked(SRC);
        let facts = NodeFacts {
            evidence: vec![Some(vec![Dict::Global("NoSuchInst".into(), vec![])])],
            ..NodeFacts::default()
        };
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert_eq!(lint::lint_hir(&hir).len(), 1);
    }

    #[test]
    fn lint_rejects_super_index_out_of_bounds() {
        let mut c = checked(SRC);
        // A class with a single declared superclass; index 5 projects past it.
        c.classes.insert(
            Sym::from("Ord"),
            ClassInfo {
                param: Sym::from("a"),
                supers: vec![Sym::from("Eq")],
                methods: vec![],
            },
        );
        let facts = NodeFacts {
            // Param(0) inner is deliberately unjudged, so exactly one violation.
            evidence: vec![Some(vec![Dict::Super(
                Box::new(Dict::Param(0)),
                "Ord".into(),
                5,
            )])],
            ..NodeFacts::default()
        };
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert_eq!(lint::lint_hir(&hir).len(), 1);
    }

    // The lane and ty families are stored but not judged: both legitimately
    // retain unsolved existentials for under-determined sites, so an
    // existential in either must NOT be flagged.
    #[test]
    fn lint_ignores_existentials_in_lane_and_ty() {
        let c = checked(SRC);
        let facts = NodeFacts {
            lane: vec![Some(Type::Exist(0))],
            ty: vec![Some(Type::Exist(1))],
            ..NodeFacts::default()
        };
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert!(lint::lint_hir(&hir).is_empty());
    }

    const HANDLER_SRC: &str = r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {} =
  handle one() with partial {
    one() resume k => k(1),
    return r => r
  }";

    #[test]
    fn lint_rejects_missing_and_stale_handler_residuals() {
        let c = checked(HANDLER_SRC);
        let node = c
            .facts
            .handler_nodes
            .iter()
            .position(|marked| *marked)
            .expect("handler marker");

        let mut missing = c.facts.clone();
        missing.handler_residual[node] = None;
        let hir = CheckedHir {
            checked: &c,
            facts: &missing,
            evidence_override: None,
        };
        assert!(lint::lint_hir(&hir)
            .iter()
            .any(|violation| violation.msg.contains("missing its residual fact")));

        let mut stale = c.facts.clone();
        stale.handler_nodes[node] = false;
        let hir = CheckedHir {
            checked: &c,
            facts: &stale,
            evidence_override: None,
        };
        assert!(lint::lint_hir(&hir)
            .iter()
            .any(|violation| violation.msg.contains("non-handler node")));
    }

    #[test]
    fn lint_rejects_duplicate_handler_operations() {
        let c = checked(HANDLER_SRC);
        let node = c
            .facts
            .handler_nodes
            .iter()
            .position(|marked| *marked)
            .expect("handler marker");
        let mut facts = c.facts.clone();
        let operation = Sym::from("one");
        facts.handler_residual[node] = Some(HandlerResidual {
            forwarded_operations: vec![operation, operation],
            forwarded_effects: Vec::new(),
            residual_operations: vec![operation],
            residual_effects: Vec::new(),
            open_row: false,
        });
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert!(lint::lint_hir(&hir)
            .iter()
            .any(|violation| violation.msg.contains("not canonical")));
    }

    #[test]
    fn handler_residual_facts_roundtrip_through_checked_body_wire() {
        let c = checked(HANDLER_SRC);
        // Isolate this wire family: unrelated under-determined node types may
        // legitimately render `?rN`, which the checked-signature rehydrator does
        // not accept and is outside this roundtrip's contract.
        let source = NodeFacts {
            handler_nodes: c.facts.handler_nodes.clone(),
            handler_residual: c.facts.handler_residual.clone(),
            ..NodeFacts::default()
        };
        let json = source.to_json().expect("serialize handler facts");
        let facts = NodeFacts::from_json(&json).expect("deserialize handler facts");
        let hir = CheckedHir {
            checked: &c,
            facts: &facts,
            evidence_override: None,
        };
        assert!(lint::lint_hir(&hir).is_empty());
        assert!(facts.handler_residual.iter().flatten().any(|fact| {
            fact.forwarded_operations().is_empty()
                && fact.residual_operations().is_empty()
                && !fact.has_open_row()
        }));
    }
}
