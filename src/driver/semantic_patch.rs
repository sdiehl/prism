//! Semantic judging for digest-pinned surface patches.
//!
//! This module deliberately sits in the driver: it consumes the exact identity
//! frontend, hash metadata, module interface, and dependency graph used by normal
//! compilation. A patch cannot accidentally invent a parallel checker or hash
//! regime.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::core::builtins::Builtin;
use crate::core::fbip::{borrow_sigs, fip_annots, Fips};
use crate::core::{hash_program, Comp, Core, DepGraph, Hashes, Value};
use crate::error::Error;
use crate::lineage::provenance::Observation;
use crate::patch::{
    extract_term, replace_term, PatchArtifact, PatchArtifactError, PatchTarget, DIGEST_HEX_LEN,
};
use crate::resolve::Root;
use crate::sym::Sym;
use crate::types::{show_effects, Checked};

use super::identity::{module_interface, namespace_root_of, ModuleInterface, ModuleInterfaceEntry};
use super::{elaborated, elaborated_validated, hash_meta, observe_run_on, Config};

pub const PATCH_FETCH_FORMAT: &str = "prism-patch-fetch-v1";
pub const PATCH_IMPACT_FORMAT: &str = "prism-patch-impact-v1";
pub const PATCH_DELTA_FORMAT: &str = "prism-patch-delta-v1";
pub const PATCH_REFUSAL_FORMAT: &str = "prism-patch-refusal-v1";
pub const PATCH_STAGE_FORMAT: &str = "prism-patch-stage-v1";
pub const PATCH_BEHAVIOR_CORPUS_FORMAT: &str = "prism-patch-behavior-corpus-v1";
pub const PATCH_BEHAVIOR_FORMAT: &str = "prism-patch-behavior-v1";

const DEFINITION_SHAPE_DOMAIN: &[u8] = b"prism-definition-shape-v1";
const DELTA_ADDRESS_DOMAIN: &[u8] = b"prism-patch-delta-address-v1";
const REFUSAL_ADDRESS_DOMAIN: &[u8] = b"prism-patch-refusal-address-v1";
const STAGE_ADDRESS_DOMAIN: &[u8] = b"prism-patch-stage-address-v1";
const BEHAVIOR_CORPUS_ADDRESS_DOMAIN: &[u8] = b"prism-patch-behavior-corpus-address-v1";
const BEHAVIOR_ADDRESS_DOMAIN: &[u8] = b"prism-patch-behavior-address-v1";

/// One dependency or importer identified by both canonical name and digest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DefinitionDigest {
    pub name: String,
    pub digest: String,
}

/// Read-side response for one owned definition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FetchReport {
    pub format: String,
    pub namespace: PatchTarget,
    pub target: PatchTarget,
    pub name: String,
    pub rendered: String,
    pub term: crate::patch::SurfaceTerm,
    pub core_hash: String,
    pub shape_digest: String,
    pub ty: String,
    pub effect_row: String,
    pub grade: String,
    pub dependencies: Vec<DefinitionDigest>,
}

impl FetchReport {
    /// Canonical JSON payload shared by the CLI and stdio protocol.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// Importer-cone response for a definition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImpactReport {
    pub format: String,
    pub target: PatchTarget,
    pub name: String,
    pub importers: Vec<DefinitionDigest>,
}

impl ImpactReport {
    /// Serialize this report as its canonical JSON payload.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// Exactly what the successful patch judgment proves.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceTier {
    pub level: u8,
    pub claim: String,
}

/// Before/after public-interface evidence. Successful v1 patches preserve it;
/// refusals carry the moved facts instead of minting a tier they cannot prove.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceDelta {
    pub before: String,
    pub after: String,
    pub changed: bool,
    pub rows: Vec<InterfaceRowDelta>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceRowDelta {
    pub kind: String,
    pub name: String,
    pub before: Option<String>,
    pub after: Option<String>,
}

/// The deterministic judgment returned by `patch apply` / protocol `submit`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeltaReport {
    pub format: String,
    pub digest: String,
    pub patch: String,
    pub base_namespace: PatchTarget,
    pub result_namespace: PatchTarget,
    pub target: PatchTarget,
    pub name: String,
    pub tier: EvidenceTier,
    pub term_digest_before: String,
    pub term_digest_after: String,
    pub core_hash_before: String,
    pub core_hash_after: String,
    pub shape_digest_before: String,
    pub shape_digest_after: String,
    pub effect_row_before: String,
    pub effect_row_after: String,
    pub grade_before: String,
    pub grade_after: String,
    pub interface: InterfaceDelta,
    pub importer_cone: Vec<DefinitionDigest>,
    pub claimed_delta: Option<serde_json::Value>,
    pub claimed_delta_status: String,
}

impl DeltaReport {
    /// Serialize this report as its canonical JSON payload.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// A stable machine-readable refusal naming the judgment that failed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PatchRefusal {
    pub format: String,
    pub digest: String,
    #[serde(flatten)]
    pub subject: Option<Box<PatchRefusalSubject>>,
    // Refusal text is variable-sized and rarely inspected on the success path.
    // Boxing it keeps every `Result<_, PatchRefusal>` cheap without changing the
    // flat JSON protocol or its content address.
    #[serde(flatten)]
    body: Box<PatchRefusalBody>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PatchRefusalSubject {
    pub patch: String,
    pub base_namespace: PatchTarget,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PatchRefusalBody {
    pub code: String,
    pub judgment: String,
    pub message: String,
    pub details: BTreeMap<String, String>,
}

impl std::ops::Deref for PatchRefusal {
    type Target = PatchRefusalBody;

    fn deref(&self) -> &Self::Target {
        &self.body
    }
}

impl PatchRefusal {
    /// Serialize this refusal as its canonical JSON payload.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    pub(crate) fn new(code: &str, judgment: &str, message: impl Into<String>) -> Self {
        let mut refusal = Self {
            format: PATCH_REFUSAL_FORMAT.to_string(),
            digest: String::new(),
            subject: None,
            body: Box::new(PatchRefusalBody {
                code: code.to_string(),
                judgment: judgment.to_string(),
                message: message.into(),
                details: BTreeMap::new(),
            }),
        };
        refusal.refresh_digest();
        refusal
    }

    fn detail(mut self, key: &str, value: impl Into<String>) -> Self {
        self.body.details.insert(key.to_string(), value.into());
        self.refresh_digest();
        self
    }

    fn subject(mut self, patch: &PatchArtifact) -> Self {
        self.subject = Some(Box::new(PatchRefusalSubject {
            patch: patch.digest.clone(),
            base_namespace: patch.base_namespace.clone(),
        }));
        self.refresh_digest();
        self
    }

    fn refresh_digest(&mut self) {
        let payload = RefusalPayload {
            format: &self.format,
            subject: &self.subject,
            code: &self.body.code,
            judgment: &self.body.judgment,
            message: &self.body.message,
            details: &self.body.details,
        };
        let bytes =
            serde_json::to_vec(&payload).expect("closed patch refusal protocol always serializes");
        self.digest = address(REFUSAL_ADDRESS_DOMAIN, &bytes);
    }
}

#[derive(Serialize)]
struct RefusalPayload<'a> {
    format: &'a str,
    subject: &'a Option<Box<PatchRefusalSubject>>,
    code: &'a str,
    judgment: &'a str,
    message: &'a str,
    details: &'a BTreeMap<String, String>,
}

/// One explicit input case in a behavior corpus. Ambient host reads and writes
/// are rejected before execution; stdin and argv are the complete open inputs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BehaviorCase {
    pub name: String,
    #[serde(default)]
    pub stdin: String,
    #[serde(default)]
    pub args: Vec<String>,
}

/// Content-addressed set of explicit interpreter inputs for old/new comparison.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BehaviorCorpus {
    pub format: String,
    pub digest: String,
    pub cases: Vec<BehaviorCase>,
}

impl BehaviorCorpus {
    /// Construct and address an explicit behavior corpus.
    ///
    /// # Errors
    /// Refuses empty corpora and empty or duplicate case names.
    pub fn new(cases: Vec<BehaviorCase>) -> Result<Self, PatchRefusal> {
        validate_behavior_cases(&cases)?;
        let digest = behavior_corpus_digest(PATCH_BEHAVIOR_CORPUS_FORMAT, &cases)?;
        Ok(Self {
            format: PATCH_BEHAVIOR_CORPUS_FORMAT.to_string(),
            digest,
            cases,
        })
    }

    /// Validate format, cases, and content address.
    ///
    /// # Errors
    /// Refuses foreign, malformed, or changed corpus artifacts.
    pub fn validate(&self) -> Result<(), PatchRefusal> {
        if self.format != PATCH_BEHAVIOR_CORPUS_FORMAT {
            return Err(PatchRefusal::new(
                "foreign-behavior-corpus",
                "decode-behavior-corpus",
                format!("unsupported behavior corpus format `{}`", self.format),
            ));
        }
        validate_behavior_cases(&self.cases)?;
        validate_digest(&self.digest, "behavior corpus")?;
        let expected = behavior_corpus_digest(&self.format, &self.cases)?;
        if self.digest != expected {
            return Err(PatchRefusal::new(
                "behavior-corpus-address-mismatch",
                "decode-behavior-corpus",
                "behavior corpus bytes do not match their content address",
            )
            .detail("expected", expected)
            .detail("found", self.digest.clone()));
        }
        Ok(())
    }
}

#[derive(Serialize)]
struct BehaviorCorpusPayload<'a> {
    format: &'a str,
    cases: &'a [BehaviorCase],
}

/// One old/new canonical trace pair in a behavior receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BehaviorCaseResult {
    pub name: String,
    pub before_trace: String,
    pub after_trace: String,
    pub before_observations: usize,
    pub after_observations: usize,
}

/// The first exact observation at which old and replacement executions differ.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BehaviorDivergence {
    pub case: String,
    pub index: usize,
    pub before: Option<Observation>,
    pub after: Option<Observation>,
}

/// Trace-corpus evidence attached to one already-typed patch judgment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BehaviorReceipt {
    pub format: String,
    pub digest: String,
    pub patch: String,
    pub judgment: String,
    pub base_namespace: PatchTarget,
    pub result_namespace: PatchTarget,
    pub corpus: String,
    pub relation: String,
    pub cases: Vec<BehaviorCaseResult>,
    pub first_divergence: Option<BehaviorDivergence>,
}

#[derive(Serialize)]
struct BehaviorReceiptPayload<'a> {
    format: &'a str,
    patch: &'a str,
    judgment: &'a str,
    base_namespace: &'a PatchTarget,
    result_namespace: &'a PatchTarget,
    corpus: &'a str,
    relation: &'a str,
    cases: &'a [BehaviorCaseResult],
    first_divergence: &'a Option<BehaviorDivergence>,
}

/// Durable staging payload written to the content-addressed store before commit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StagedPatch {
    pub format: String,
    pub digest: String,
    pub source_digest: String,
    pub patch: PatchArtifact,
    pub result_source: String,
    pub report: DeltaReport,
}

impl StagedPatch {
    /// Build a content-addressed staging record.
    ///
    /// # Errors
    /// Returns a refusal if the payload cannot be serialized.
    pub fn new(
        source_digest: String,
        patch: PatchArtifact,
        result_source: String,
        report: DeltaReport,
    ) -> Result<Self, PatchRefusal> {
        let payload = StagePayload {
            format: PATCH_STAGE_FORMAT,
            source_digest: &source_digest,
            patch: &patch,
            result_source: &result_source,
            report: &report,
        };
        let bytes = serde_json::to_vec(&payload).map_err(|error| serialization_refusal(&error))?;
        Ok(Self {
            format: PATCH_STAGE_FORMAT.to_string(),
            digest: address(STAGE_ADDRESS_DOMAIN, &bytes),
            source_digest,
            patch,
            result_source,
            report,
        })
    }

    /// Validate the stage version, embedded patch, and content address.
    ///
    /// # Errors
    /// Returns a structured refusal for any invalid boundary.
    pub fn validate(&self) -> Result<(), PatchRefusal> {
        if self.format != PATCH_STAGE_FORMAT {
            return Err(PatchRefusal::new(
                "foreign-stage-format",
                "decode-stage",
                format!("unsupported patch stage format `{}`", self.format),
            ));
        }
        self.patch
            .validate()
            .map_err(|error| artifact_refusal(&error))?;
        let payload = StagePayload {
            format: &self.format,
            source_digest: &self.source_digest,
            patch: &self.patch,
            result_source: &self.result_source,
            report: &self.report,
        };
        let bytes = serde_json::to_vec(&payload).map_err(|error| serialization_refusal(&error))?;
        let expected = address(STAGE_ADDRESS_DOMAIN, &bytes);
        if self.digest != expected {
            return Err(PatchRefusal::new(
                "stage-address-mismatch",
                "decode-stage",
                "staged patch bytes do not match their content address",
            )
            .detail("expected", expected)
            .detail("found", self.digest.clone()));
        }
        Ok(())
    }

    /// Serialize this stage as its canonical JSON payload.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

#[derive(Serialize)]
struct StagePayload<'a> {
    format: &'a str,
    source_digest: &'a str,
    patch: &'a PatchArtifact,
    result_source: &'a str,
    report: &'a DeltaReport,
}

struct SemanticState {
    checked: Checked,
    hashes: Hashes,
    graph: DepGraph,
    hash_meta: BTreeMap<Sym, String>,
    fips: Fips,
    namespace: PatchTarget,
    ambient_builtins: Vec<String>,
}

#[derive(Clone)]
struct DefinitionFacts {
    name: String,
    hash: String,
    shape: String,
    ty: String,
    effects: String,
    grade: String,
    dependencies: Vec<DefinitionDigest>,
    importers: Vec<DefinitionDigest>,
}

/// Fetch one owned definition by name or digest.
///
/// # Errors
/// Returns a structured refusal if the input does not check or the selector is
/// missing, ambiguous, or not owned by the entry source.
pub fn fetch_semantic_patch(
    entry_source: &str,
    full_source: &str,
    roots: &[Root],
    selector: &str,
) -> Result<FetchReport, PatchRefusal> {
    let state = semantic_state(full_source, roots, false)?;
    let symbol = resolve_selector(&state, selector)?;
    let facts = definition_facts(&state, symbol)?;
    let term = extract_term(entry_source, &facts.name).map_err(|error| {
        PatchRefusal::new(
            "definition-not-owned",
            "fetch-term",
            format!(
                "definition `{}` is not a uniquely owned declaration in this input: {error}",
                facts.name
            ),
        )
    })?;
    let rendered = term.render().map_err(|error| artifact_refusal(&error))?;
    Ok(FetchReport {
        format: PATCH_FETCH_FORMAT.to_string(),
        namespace: state.namespace,
        target: PatchTarget::new(facts.hash.clone()),
        name: facts.name,
        rendered,
        term,
        core_hash: facts.hash,
        shape_digest: facts.shape,
        ty: facts.ty,
        effect_row: facts.effects,
        grade: facts.grade,
        dependencies: facts.dependencies,
    })
}

/// Read the transitive importer cone by name or digest.
///
/// # Errors
/// Returns a structured refusal if the input does not check or the selector
/// cannot be resolved to one content-addressed definition.
pub fn impact_semantic_patch(
    full_source: &str,
    roots: &[Root],
    selector: &str,
) -> Result<ImpactReport, PatchRefusal> {
    let state = semantic_state(full_source, roots, false)?;
    let symbol = resolve_selector(&state, selector)?;
    let facts = definition_facts(&state, symbol)?;
    Ok(ImpactReport {
        format: PATCH_IMPACT_FORMAT.to_string(),
        target: PatchTarget::new(facts.hash),
        name: facts.name,
        importers: facts.importers,
    })
}

/// Judge a patch and return both its report and the canonical source projection
/// that may be staged for atomic commit.
///
/// # Errors
/// Returns a structured refusal if any artifact, compiler, identity, or
/// interface-preservation judgment fails.
pub fn apply_semantic_patch(
    entry_source: &str,
    full_source: &str,
    roots: &[Root],
    patch: &PatchArtifact,
) -> Result<(DeltaReport, String), PatchRefusal> {
    apply_semantic_patch_inner(entry_source, full_source, roots, patch)
        .map_err(|refusal| refusal.subject(patch))
}

fn apply_semantic_patch_inner(
    entry_source: &str,
    full_source: &str,
    roots: &[Root],
    patch: &PatchArtifact,
) -> Result<(DeltaReport, String), PatchRefusal> {
    patch.validate().map_err(|error| artifact_refusal(&error))?;
    let name = patch.replacement.name.clone();
    let before = semantic_state(full_source, roots, true)?;
    if before.namespace != patch.base_namespace {
        return Err(PatchRefusal::new(
            "stale-namespace",
            "base-namespace",
            "the semantic namespace moved after the patch was authored",
        )
        .detail("expected", patch.base_namespace.digest.clone())
        .detail("found", before.namespace.digest));
    }
    let symbol = resolve_selector(&before, &name)?;
    let before_facts = definition_facts(&before, symbol)?;
    if before_facts.hash != patch.target.digest {
        return Err(PatchRefusal::new(
            "stale-target",
            "target-digest",
            format!("definition `{name}` no longer has the digest pinned by the patch"),
        )
        .detail("expected", patch.target.digest.clone())
        .detail("found", before_facts.hash));
    }
    let current_term =
        extract_term(entry_source, &name).map_err(|error| artifact_refusal(&error))?;
    let result_source = replace_term(entry_source, &name, &patch.replacement)
        .map_err(|error| artifact_refusal(&error))?;
    let result_full = full_with_entry(full_source, &result_source);
    let after = semantic_state(&result_full, roots, true)?;
    let after_symbol = resolve_selector(&after, &name)?;
    let after_facts = definition_facts(&after, after_symbol)?;

    let interface_before = module_interface(entry_source, full_source, roots)
        .map_err(|error| compiler_refusal("interface-before", &error))?;
    let interface_after = module_interface(&result_source, &result_full, roots)
        .map_err(|error| compiler_refusal("interface-after", &error))?;
    let interface = interface_delta(&interface_before, &interface_after);

    // Tier 2 is explicitly interface-preserving. A checked but interface-moving
    // edit is useful information, but v1 must refuse rather than over-claim.
    if before_facts.shape != after_facts.shape
        || before_facts.effects != after_facts.effects
        || before_facts.grade != after_facts.grade
        || interface.changed
    {
        return Err(PatchRefusal::new(
            "interface-changed",
            "interface-preservation",
            format!("replacement for `{name}` changes facts required by its importers"),
        )
        .detail("shape-before", before_facts.shape)
        .detail("shape-after", after_facts.shape)
        .detail("effects-before", before_facts.effects)
        .detail("effects-after", after_facts.effects)
        .detail("grade-before", before_facts.grade)
        .detail("grade-after", after_facts.grade)
        .detail("interface-before", interface.before)
        .detail("interface-after", interface.after));
    }

    let tier = if current_term.digest == patch.replacement.digest {
        EvidenceTier {
            level: 0,
            claim: "digest-identical".to_string(),
        }
    } else if before_facts.hash == after_facts.hash {
        EvidenceTier {
            level: 1,
            claim: "core-equivalent".to_string(),
        }
    } else {
        EvidenceTier {
            level: 2,
            claim: "interface-preserved-core-changed".to_string(),
        }
    };
    let report = addressed_delta(&DeltaPayload {
        format: PATCH_DELTA_FORMAT,
        patch: &patch.digest,
        base_namespace: &patch.base_namespace,
        result_namespace: &after.namespace,
        target: &patch.target,
        name: &name,
        tier: &tier,
        term_digest_before: &current_term.digest,
        term_digest_after: &patch.replacement.digest,
        core_hash_before: &before_facts.hash,
        core_hash_after: &after_facts.hash,
        shape_digest_before: &before_facts.shape,
        shape_digest_after: &after_facts.shape,
        effect_row_before: &before_facts.effects,
        effect_row_after: &after_facts.effects,
        grade_before: &before_facts.grade,
        grade_after: &after_facts.grade,
        interface: &interface,
        importer_cone: &before_facts.importers,
        claimed_delta: &patch.claimed_delta,
        claimed_delta_status: "reserved-unjudged",
    })?;
    Ok((report, result_source))
}

/// Compare old and replacement executions over an explicit, content-addressed
/// interpreter input corpus.
///
/// The first version admits only programs without ambient host reads or
/// mutations. Stdin and argv are supplied by each case, console output is
/// captured, and the interpreter's RNG starts from its deterministic seed.
///
/// # Errors
/// Refuses malformed/stale patches and corpora, interface-moving replacements,
/// ambient host capabilities, and frontend failures. Runtime faults remain
/// terminal observations and therefore participate in the comparison.
pub fn verify_semantic_patch_behavior(
    entry_source: &str,
    full_source: &str,
    roots: &[Root],
    patch: &PatchArtifact,
    corpus: &BehaviorCorpus,
    cfg: &Config,
) -> Result<BehaviorReceipt, PatchRefusal> {
    verify_semantic_patch_behavior_inner(entry_source, full_source, roots, patch, corpus, cfg)
        .map_err(|refusal| refusal.subject(patch))
}

fn verify_semantic_patch_behavior_inner(
    entry_source: &str,
    full_source: &str,
    roots: &[Root],
    patch: &PatchArtifact,
    corpus: &BehaviorCorpus,
    cfg: &Config,
) -> Result<BehaviorReceipt, PatchRefusal> {
    corpus.validate()?;
    let (judgment, result_source) = apply_semantic_patch(entry_source, full_source, roots, patch)?;
    let result_full = full_with_entry(full_source, &result_source);
    let before = semantic_state(full_source, roots, true)?;
    let after = semantic_state(&result_full, roots, true)?;
    let ambient = before
        .ambient_builtins
        .iter()
        .chain(&after.ambient_builtins)
        .cloned()
        .collect::<BTreeSet<_>>();
    if !ambient.is_empty() {
        return Err(PatchRefusal::new(
            "ambient-behavior-input",
            "behavior-preflight",
            "behavior receipts require stdin/argv-only inputs in this version",
        )
        .detail(
            "builtins",
            ambient.into_iter().collect::<Vec<_>>().join(","),
        ));
    }

    // Behavior receipts use the unoptimized interpreter oracle. Optimization
    // equivalence is a separate gate and cannot influence patch classification.
    let mut oracle_cfg = cfg.clone();
    oracle_cfg.opt = crate::core::OptLevel::O0;
    oracle_cfg.passes = None;
    let mut cases = Vec::with_capacity(corpus.cases.len());
    let mut first_divergence = None;
    for case in &corpus.cases {
        let mut before_out = Vec::new();
        let mut before_input = std::io::Cursor::new(case.stdin.as_bytes());
        let before_run = observe_run_on(
            full_source,
            roots,
            &mut before_out,
            &mut before_input,
            &oracle_cfg,
            case.args.clone(),
        )
        .map_err(|error| compiler_refusal("behavior-before", &error))?;
        let mut after_out = Vec::new();
        let mut after_input = std::io::Cursor::new(case.stdin.as_bytes());
        let after_run = observe_run_on(
            &result_full,
            roots,
            &mut after_out,
            &mut after_input,
            &oracle_cfg,
            case.args.clone(),
        )
        .map_err(|error| compiler_refusal("behavior-after", &error))?;
        if first_divergence.is_none() {
            first_divergence = trace_divergence(
                &case.name,
                &before_run.canonical_trace.observations,
                &after_run.canonical_trace.observations,
            );
        }
        cases.push(BehaviorCaseResult {
            name: case.name.clone(),
            before_trace: before_run.canonical_trace.digest,
            after_trace: after_run.canonical_trace.digest,
            before_observations: before_run.canonical_trace.observations.len(),
            after_observations: after_run.canonical_trace.observations.len(),
        });
    }
    let relation = if first_divergence.is_some() {
        "behavior-changing"
    } else {
        "equivalent-on-corpus"
    };
    addressed_behavior(&BehaviorReceiptPayload {
        format: PATCH_BEHAVIOR_FORMAT,
        patch: &patch.digest,
        judgment: &judgment.digest,
        base_namespace: &judgment.base_namespace,
        result_namespace: &judgment.result_namespace,
        corpus: &corpus.digest,
        relation,
        cases: &cases,
        first_divergence: &first_divergence,
    })
}

#[derive(Serialize)]
struct DeltaPayload<'a> {
    format: &'a str,
    patch: &'a str,
    base_namespace: &'a PatchTarget,
    result_namespace: &'a PatchTarget,
    target: &'a PatchTarget,
    name: &'a str,
    tier: &'a EvidenceTier,
    term_digest_before: &'a str,
    term_digest_after: &'a str,
    core_hash_before: &'a str,
    core_hash_after: &'a str,
    shape_digest_before: &'a str,
    shape_digest_after: &'a str,
    effect_row_before: &'a str,
    effect_row_after: &'a str,
    grade_before: &'a str,
    grade_after: &'a str,
    interface: &'a InterfaceDelta,
    importer_cone: &'a [DefinitionDigest],
    claimed_delta: &'a Option<serde_json::Value>,
    claimed_delta_status: &'a str,
}

fn addressed_delta(payload: &DeltaPayload<'_>) -> Result<DeltaReport, PatchRefusal> {
    let bytes = serde_json::to_vec(payload).map_err(|error| serialization_refusal(&error))?;
    Ok(DeltaReport {
        format: payload.format.to_string(),
        digest: address(DELTA_ADDRESS_DOMAIN, &bytes),
        patch: payload.patch.to_string(),
        base_namespace: payload.base_namespace.clone(),
        result_namespace: payload.result_namespace.clone(),
        target: payload.target.clone(),
        name: payload.name.to_string(),
        tier: payload.tier.clone(),
        term_digest_before: payload.term_digest_before.to_string(),
        term_digest_after: payload.term_digest_after.to_string(),
        core_hash_before: payload.core_hash_before.to_string(),
        core_hash_after: payload.core_hash_after.to_string(),
        shape_digest_before: payload.shape_digest_before.to_string(),
        shape_digest_after: payload.shape_digest_after.to_string(),
        effect_row_before: payload.effect_row_before.to_string(),
        effect_row_after: payload.effect_row_after.to_string(),
        grade_before: payload.grade_before.to_string(),
        grade_after: payload.grade_after.to_string(),
        interface: payload.interface.clone(),
        importer_cone: payload.importer_cone.to_vec(),
        claimed_delta: payload.claimed_delta.clone(),
        claimed_delta_status: payload.claimed_delta_status.to_string(),
    })
}

fn addressed_behavior(
    payload: &BehaviorReceiptPayload<'_>,
) -> Result<BehaviorReceipt, PatchRefusal> {
    let bytes = serde_json::to_vec(payload).map_err(|error| serialization_refusal(&error))?;
    Ok(BehaviorReceipt {
        format: payload.format.to_string(),
        digest: address(BEHAVIOR_ADDRESS_DOMAIN, &bytes),
        patch: payload.patch.to_string(),
        judgment: payload.judgment.to_string(),
        base_namespace: payload.base_namespace.clone(),
        result_namespace: payload.result_namespace.clone(),
        corpus: payload.corpus.to_string(),
        relation: payload.relation.to_string(),
        cases: payload.cases.to_vec(),
        first_divergence: payload.first_divergence.clone(),
    })
}

fn behavior_corpus_digest(format: &str, cases: &[BehaviorCase]) -> Result<String, PatchRefusal> {
    let bytes = serde_json::to_vec(&BehaviorCorpusPayload { format, cases })
        .map_err(|error| serialization_refusal(&error))?;
    Ok(address(BEHAVIOR_CORPUS_ADDRESS_DOMAIN, &bytes))
}

fn validate_behavior_cases(cases: &[BehaviorCase]) -> Result<(), PatchRefusal> {
    if cases.is_empty() {
        return Err(PatchRefusal::new(
            "empty-behavior-corpus",
            "decode-behavior-corpus",
            "behavior corpus must contain at least one case",
        ));
    }
    let mut names = BTreeSet::new();
    for case in cases {
        if case.name.is_empty() {
            return Err(PatchRefusal::new(
                "empty-behavior-case",
                "decode-behavior-corpus",
                "behavior case names must not be empty",
            ));
        }
        if !names.insert(&case.name) {
            return Err(PatchRefusal::new(
                "duplicate-behavior-case",
                "decode-behavior-corpus",
                format!("duplicate behavior case `{}`", case.name),
            ));
        }
    }
    Ok(())
}

fn validate_digest(digest: &str, object: &str) -> Result<(), PatchRefusal> {
    if digest.len() == DIGEST_HEX_LEN
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        Ok(())
    } else {
        Err(PatchRefusal::new(
            "invalid-digest",
            "decode-artifact",
            format!("invalid {object} digest"),
        ))
    }
}

fn trace_divergence(
    case: &str,
    before: &[Observation],
    after: &[Observation],
) -> Option<BehaviorDivergence> {
    let shared = before.len().min(after.len());
    let index = (0..shared)
        .find(|index| before[*index] != after[*index])
        .or_else(|| (before.len() != after.len()).then_some(shared))?;
    Some(BehaviorDivergence {
        case: case.to_string(),
        index,
        before: before.get(index).cloned(),
        after: after.get(index).cloned(),
    })
}

fn full_with_entry(full_source: &str, entry_source: &str) -> String {
    let prefix_len = crate::error::SourceMap::new(full_source).prelude_len();
    let mut full = String::with_capacity(prefix_len + entry_source.len());
    full.push_str(&full_source[..prefix_len]);
    full.push_str(entry_source);
    full
}

fn semantic_state(
    source: &str,
    roots: &[Root],
    validated: bool,
) -> Result<SemanticState, PatchRefusal> {
    let result = if validated {
        elaborated_validated(source, roots)
    } else {
        elaborated(source, roots)
    };
    let (program, checked, core) = result.map_err(|error| compiler_refusal("elaborate", &error))?;
    let sigs = borrow_sigs(&program);
    let fips = fip_annots(&program);
    let metas = hash_meta(&checked, &sigs, &fips);
    let hashes = hash_program(&core, &metas);
    let graph = DepGraph::of(&core);
    let namespace = PatchTarget::new(
        namespace_root_of(&program, &checked, &core)
            .map_err(|error| compiler_refusal("namespace", &error))?
            .into_string(),
    );
    let ambient_builtins = ambient_builtins(&core);
    Ok(SemanticState {
        checked,
        hashes,
        graph,
        hash_meta: metas,
        fips,
        namespace,
        ambient_builtins,
    })
}

fn resolve_selector(state: &SemanticState, selector: &str) -> Result<Sym, PatchRefusal> {
    let digest = selector
        .strip_prefix(&format!("{}:", crate::core::HASH_SCHEME))
        .unwrap_or(selector);
    let digest_match = digest.len() == DIGEST_HEX_LEN
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase());
    let mut candidates = if digest_match {
        state
            .hashes
            .iter()
            .filter_map(|(name, hash)| (hash.as_str() == digest).then_some(*name))
            .collect::<Vec<_>>()
    } else {
        state.graph.resolve(selector)
    };
    candidates.sort_by_key(|symbol| symbol.as_str());
    candidates.dedup();
    match candidates.as_slice() {
        [symbol] => Ok(*symbol),
        [] => Err(PatchRefusal::new(
            "target-not-found",
            "locate-target",
            format!("no definition matches `{selector}`"),
        )),
        _ => Err(PatchRefusal::new(
            "target-ambiguous",
            "locate-target",
            format!("`{selector}` identifies more than one definition"),
        )
        .detail(
            "candidates",
            candidates
                .iter()
                .map(|symbol| symbol.as_str())
                .collect::<Vec<_>>()
                .join(","),
        )),
    }
}

fn definition_facts(state: &SemanticState, symbol: Sym) -> Result<DefinitionFacts, PatchRefusal> {
    let hash = state.hashes.get(&symbol).ok_or_else(|| {
        PatchRefusal::new(
            "target-not-content-addressed",
            "hash-target",
            format!("definition `{}` has no Core content hash", symbol.as_str()),
        )
    })?;
    let declaration = state
        .checked
        .decls
        .iter()
        .find(|declaration| declaration.name == symbol.as_str())
        .ok_or_else(|| {
            PatchRefusal::new(
                "target-not-value",
                "type-target",
                format!(
                    "definition `{}` is not a checked value declaration",
                    symbol.as_str()
                ),
            )
        })?;
    let meta = state.hash_meta.get(&symbol).ok_or_else(|| {
        PatchRefusal::new(
            "missing-shape",
            "shape-target",
            format!("definition `{}` has no interface shape", symbol.as_str()),
        )
    })?;
    let dependencies = digest_rows(state.graph.direct_deps(symbol), &state.hashes, "dependency")?;
    let importers = digest_rows(state.graph.dependents(symbol), &state.hashes, "importer")?;
    let grade = state
        .fips
        .get(&symbol)
        .and_then(|fip| fip.keyword())
        .unwrap_or("unrestricted")
        .to_string();
    Ok(DefinitionFacts {
        name: symbol.as_str().to_string(),
        hash: hash.as_str().to_string(),
        shape: definition_shape(meta),
        ty: declaration.ty.show(),
        effects: show_effects(&declaration.effects),
        grade,
        dependencies,
        importers,
    })
}

fn digest_rows(
    symbols: BTreeSet<Sym>,
    hashes: &Hashes,
    relation: &str,
) -> Result<Vec<DefinitionDigest>, PatchRefusal> {
    symbols
        .into_iter()
        .map(|symbol| {
            let digest = hashes.get(&symbol).ok_or_else(|| {
                PatchRefusal::new(
                    "missing-related-digest",
                    "read-lineage",
                    format!("{relation} `{}` has no content digest", symbol.as_str()),
                )
            })?;
            Ok(DefinitionDigest {
                name: symbol.as_str().to_string(),
                digest: digest.as_str().to_string(),
            })
        })
        .collect()
}

fn definition_shape(meta: &str) -> String {
    address(DEFINITION_SHAPE_DOMAIN, meta.as_bytes())
}

fn interface_delta(before: &ModuleInterface, after: &ModuleInterface) -> InterfaceDelta {
    let old = interface_rows(&before.entries);
    let new = interface_rows(&after.entries);
    let keys = old
        .keys()
        .chain(new.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let rows = keys
        .into_iter()
        .filter_map(|(kind, name)| {
            let before = old.get(&(kind.clone(), name.clone())).cloned();
            let after = new.get(&(kind.clone(), name.clone())).cloned();
            (before != after).then_some(InterfaceRowDelta {
                kind,
                name,
                before,
                after,
            })
        })
        .collect();
    InterfaceDelta {
        before: before.digest.clone(),
        after: after.digest.clone(),
        changed: before.digest != after.digest,
        rows,
    }
}

fn interface_rows(entries: &[ModuleInterfaceEntry]) -> BTreeMap<(String, String), String> {
    entries
        .iter()
        .map(|entry| {
            (
                (entry.kind.clone(), entry.name.clone()),
                entry.signature.clone(),
            )
        })
        .collect()
}

fn ambient_builtins(core: &Core) -> Vec<String> {
    const fn ambient(builtin: Builtin) -> bool {
        matches!(
            builtin,
            Builtin::ProbeEnabled
                | Builtin::Getenv
                | Builtin::ReadFile
                | Builtin::ReadBytesFile
                | Builtin::WriteBytesFile
                | Builtin::WriteFile
                | Builtin::FileExists
                | Builtin::AppendFile
                | Builtin::RemoveFile
                | Builtin::StoreGet
                | Builtin::StorePut
                | Builtin::StoreHas
                | Builtin::System
                | Builtin::WallNow
                | Builtin::MonoNow
        )
    }

    fn scan_value(value: &Value, out: &mut BTreeSet<String>) {
        match value {
            Value::Thunk(body) => comp(body, out),
            Value::Ctor(_, _, fields) | Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                for field in fields {
                    scan_value(field, out);
                }
            }
            Value::UnboxedRecord(fields) => {
                for (_, field) in fields {
                    scan_value(field, out);
                }
            }
            Value::Var(_)
            | Value::Int(_)
            | Value::I64(_)
            | Value::U64(_)
            | Value::Float(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::Unit => {}
        }
    }

    fn comp(node: &Comp, out: &mut BTreeSet<String>) {
        if let Comp::StrBuiltin(builtin, _) = node {
            if ambient(*builtin) {
                out.insert(builtin.name().to_string());
            }
        }
        match node {
            Comp::Return(v)
            | Comp::Force(v)
            | Comp::Error(v)
            | Comp::FloatBuiltin(_, v)
            | Comp::Neg(_, v)
            | Comp::UnboxedProject(v, _)
            | Comp::Dup(v)
            | Comp::Drop(v)
            | Comp::Reuse(_, v)
            | Comp::RefNew(v)
            | Comp::RefGet(v) => scan_value(v, out),
            Comp::RefSet(cell, v) | Comp::InitAt(cell, v) => {
                scan_value(cell, out);
                scan_value(v, out);
            }
            Comp::WithReuse { freed, body, .. } => {
                scan_value(freed, out);
                comp(body, out);
            }
            Comp::Prim(_, left, right) => {
                scan_value(left, out);
                scan_value(right, out);
            }
            Comp::Bind(bound, _, body) => {
                comp(bound, out);
                comp(body, out);
            }
            Comp::App(function, args) => {
                comp(function, out);
                for arg in args {
                    scan_value(arg, out);
                }
            }
            Comp::If(condition, then_body, else_body) => {
                scan_value(condition, out);
                comp(then_body, out);
                comp(else_body, out);
            }
            Comp::Call(_, args)
            | Comp::Do(_, args)
            | Comp::StrBuiltin(_, args)
            | Comp::Io(_, args) => {
                for arg in args {
                    scan_value(arg, out);
                }
            }
            Comp::Lam(_, body) | Comp::Mask(_, body) => comp(body, out),
            Comp::Case(scrutinee, arms) => {
                scan_value(scrutinee, out);
                for (_, body) in arms {
                    comp(body, out);
                }
            }
            Comp::Handle {
                body,
                return_body,
                ops,
                ..
            } => {
                comp(body, out);
                if let Some(return_body) = return_body {
                    comp(return_body, out);
                }
                for op in ops {
                    comp(&op.body, out);
                }
            }
        }
    }

    let reachable = crate::core::reachable_fns(core);
    let mut out = BTreeSet::new();
    for function in core
        .fns
        .iter()
        .filter(|function| reachable.contains(&function.name))
    {
        comp(&function.body, &mut out);
    }
    out.into_iter().collect()
}

fn compiler_refusal(judgment: &str, error: &Error) -> PatchRefusal {
    PatchRefusal::new(error.code().as_str(), judgment, error.to_string())
}

fn artifact_refusal(error: &PatchArtifactError) -> PatchRefusal {
    PatchRefusal::new("invalid-artifact", "decode-artifact", error.to_string())
}

fn serialization_refusal(error: &serde_json::Error) -> PatchRefusal {
    PatchRefusal::new("serialization", "serialize-artifact", error.to_string())
}

fn address(domain: &[u8], payload: &[u8]) -> String {
    let mut hasher = blake3::Hasher::new();
    for field in [domain, payload] {
        hasher.update(&(field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    hasher.finalize().to_hex().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::patch::SurfaceTerm;
    use crate::{default_roots, with_prelude};
    use std::path::Path;

    const SOURCE: &str = "pub fn inc(x : Int) : Int = x + 1\n\nfn caller() : Int = inc(4)\n";

    fn roots() -> Vec<Root> {
        default_roots(Path::new("."))
    }

    fn artifact(replacement: &str) -> PatchArtifact {
        let full = with_prelude(SOURCE);
        let fetch = fetch_semantic_patch(SOURCE, &full, &roots(), "inc").unwrap();
        PatchArtifact::new(
            fetch.namespace,
            fetch.target,
            SurfaceTerm::from_source(replacement).unwrap(),
            None,
        )
        .unwrap()
    }

    #[test]
    fn fetch_and_impact_return_digest_addressed_facts() {
        let full = with_prelude(SOURCE);
        let fetch = fetch_semantic_patch(SOURCE, &full, &roots(), "inc").unwrap();
        assert_eq!(fetch.name, "inc");
        assert_eq!(fetch.target.digest, fetch.core_hash);
        assert_eq!(fetch.effect_row, "{}");
        let impact = impact_semantic_patch(&full, &roots(), &fetch.core_hash).unwrap();
        assert_eq!(impact.name, "inc");
        assert!(impact.importers.iter().any(|row| row.name == "caller"));
    }

    #[test]
    fn evidence_tiers_distinguish_noop_normalization_and_change() {
        let full = with_prelude(SOURCE);
        let no_op = artifact("pub fn inc(x : Int) : Int = x + 1\n");
        let (report, _) = apply_semantic_patch(SOURCE, &full, &roots(), &no_op).unwrap();
        assert_eq!(report.tier.level, 0);

        let renamed = artifact("pub fn inc(y : Int) : Int = y + 1\n");
        let (report, _) = apply_semantic_patch(SOURCE, &full, &roots(), &renamed).unwrap();
        assert_eq!(report.tier.level, 1);

        let changed = artifact("pub fn inc(x : Int) : Int = x + 2\n");
        let (report, result) = apply_semantic_patch(SOURCE, &full, &roots(), &changed).unwrap();
        assert_eq!(report.tier.level, 2);
        assert!(result.contains("x + 2"));
        assert_eq!(report.importer_cone[0].name, "caller");
    }

    #[test]
    fn stale_and_interface_moving_patches_are_structured_refusals() {
        let full = with_prelude(SOURCE);
        let mut stale = artifact("pub fn inc(x : Int) : Int = x + 2\n");
        stale.target.digest = "0".repeat(64);
        stale.digest = crate::patch::PatchArtifact::new(
            stale.base_namespace.clone(),
            stale.target.clone(),
            stale.replacement.clone(),
            None,
        )
        .unwrap()
        .digest;
        let refusal = apply_semantic_patch(SOURCE, &full, &roots(), &stale).unwrap_err();
        assert_eq!(refusal.code, "stale-target");
        let encoded = refusal.to_json().unwrap();
        let decoded: PatchRefusal = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded, refusal);

        let moving = artifact("pub fn inc(x : Bool) : Bool = x\n");
        let refusal = apply_semantic_patch(SOURCE, &full, &roots(), &moving).unwrap_err();
        assert_eq!(refusal.code, "E1022");
        assert_eq!(refusal.judgment, "elaborate");
    }
}
