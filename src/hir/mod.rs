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
//! and zonked node types.
//!
//! There is deliberately no parallel elaboration path: elaboration constructs
//! its `CheckedHir` through [`build`] (whole programs) or [`build_for_expr`]
//! (the REPL's re-inferred expressions, which carry their own evidence).

pub mod lint;

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

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

/// The facts recorded for one node, borrowed for iteration. The read shape the
/// versioned HIR fixture export walks: whichever of resolution, dictionary
/// evidence, numeric lane, and zonked type checking recorded for the node.
pub(crate) struct NodeFactRefs<'a> {
    pub res: Option<&'a NodeRes>,
    pub evidence: Option<&'a [Dict]>,
    pub lane: Option<&'a Type>,
    pub ty: Option<&'a Type>,
}

#[derive(Serialize, Deserialize)]
struct NodeFactWire {
    id: u32,
    res: Option<NodeRes>,
    evidence: Option<Vec<Dict>>,
    lane: Option<String>,
    ty: Option<String>,
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
            .max(self.ty.len());
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
            };
            let empty = refs.res.is_none()
                && refs.evidence.is_none()
                && refs.lane.is_none()
                && refs.ty.is_none();
            // The dense index is the node's `NodeId`, itself a `u32`, so it fits.
            (!empty).then(|| (u32::try_from(i).expect("node index fits u32"), refs))
        })
    }

    /// Assemble from the checker's working tables, consuming them: the one
    /// conversion point between inference's incremental maps and the dense
    /// artifact elaboration reads.
    #[must_use]
    pub fn from_tables(
        field_res: BTreeMap<NodeId, (String, usize, usize)>,
        unboxed_field: BTreeMap<NodeId, (usize, usize)>,
        path_res: PathRes,
        fixed: BTreeMap<NodeId, Type>,
        span_types: BTreeMap<NodeId, Type>,
        dicts: DictTable,
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
        Self {
            res,
            evidence: dense(dicts),
            lane: dense(fixed),
            ty: dense(span_types),
        }
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

impl CheckedHir<'_> {
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
}
