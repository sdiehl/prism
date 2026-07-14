use std::collections::{BTreeMap, BTreeSet};
use std::io;

use serde::{Deserialize, Serialize};

use crate::core::{
    effective_passes, hash_program, lint_core, lower_effects, run_opt_spec, shallow_hashes, Core,
    CoreFn, CorePass, ElaboratedCore, LoweredCore, OpGrades, PassStage,
};
use crate::error::Error;
use crate::lineage::{FactOutcome, QueryKind};
use crate::store::disk::{resolve_store_path, Store};
use crate::sym::Sym;
use crate::types::CtorInfo;

use super::identity::compiler_binary_fingerprint;
use super::input::field;
use super::scheduler::QueryScheduler;
use super::session::QueryDecision;
use super::Config;

const OPT_SCC_QUERY: &str = "optimized-scc";
const OPT_SCC_QUERY_SCHEMA: &[u8] = b"prism-optimized-scc-query-v3";
const OPT_SCC_FORMAT: &str = "prism-optimized-scc-fixed-point-v1";
const MAX_OPT_SCC_ARTIFACT_BYTES: usize = 64 * 1024;
const EFFECT_PLAN_QUERY: &str = "effect-lowering-plan";
const EFFECT_PLAN_QUERY_SCHEMA: &[u8] = b"prism-effect-lowering-plan-query-v1";
const EFFECT_PLAN_FORMAT: &str = "prism-effect-lowering-projection-v1";
const MAX_EFFECT_PLAN_ARTIFACT_BYTES: usize = 1024 * 1024;
const EFFECT_RESULT_QUERY: &str = "effect-lowering-result";
const EFFECT_RESULT_QUERY_SCHEMA: &[u8] = b"prism-effect-lowering-result-query-v1";
const EFFECT_RESULT_FORMAT: &str = "prism-effect-lowering-result-v1";
const MAX_EFFECT_RESULT_ARTIFACT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Serialize, Deserialize)]
struct OptimizedSccArtifact {
    format: String,
    key: String,
    stage: String,
    pass: String,
    input_members: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct EffectLoweringPlan {
    format: String,
    key: String,
    input_members: Vec<String>,
    retained_members: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct EffectLoweringResult {
    format: String,
    key: String,
    input_members: Vec<String>,
    output: Core,
    added_ctors: Vec<String>,
    warning: Option<String>,
}

struct SccQueryIdentity {
    compiler: String,
    artifact: String,
}

type EffectLowered = (LoweredCore, BTreeMap<String, CtorInfo>, Option<String>);

struct SccPassQuery<'a> {
    store: &'a Store,
    newtype_ctors: &'a BTreeSet<Sym>,
    stage: PassStage,
    pass: CorePass,
    pipeline_fingerprint: &'a str,
    identity: &'a SccQueryIdentity,
    cfg: &'a Config,
}

pub(super) fn run_opt_queries(
    core: &Core,
    newtype_ctors: &BTreeSet<Sym>,
    stage: PassStage,
    cfg: &Config,
) -> Result<Core, Error> {
    let passes = effective_passes(
        cfg.opt,
        cfg.passes.as_ref(),
        stage,
        &cfg.disabled,
        &cfg.flags,
    );
    if !cache_enabled(cfg)
        || cfg.flags.core_lint
        || cfg.flags.opt_stats
        || cfg.flags.dump_core.is_some()
    {
        return Ok(run_opt_spec(core, newtype_ctors, &passes, stage, &[], &cfg.flags).0);
    }

    let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
    let identity = SccQueryIdentity {
        compiler: compiler_binary_fingerprint()?.to_string(),
        artifact: cfg.artifact_identity_for("frontend").fingerprint(),
    };
    let pipeline_fingerprint = crate::core::pass_fingerprint(
        cfg.opt,
        cfg.passes.as_ref(),
        stage,
        &cfg.disabled,
        &cfg.flags,
    );
    let mut current = core.clone();
    for pass in passes {
        current = if pass.is_scc_local() {
            run_local_pass(
                &current,
                &SccPassQuery {
                    store: &store,
                    newtype_ctors,
                    stage,
                    pass,
                    pipeline_fingerprint: &pipeline_fingerprint,
                    identity: &identity,
                    cfg,
                },
            )?
        } else {
            run_opt_spec(&current, newtype_ctors, &[pass], stage, &[], &cfg.flags).0
        };
    }
    Ok(current)
}

fn effect_identity(core: &Core) -> String {
    let mut names = core
        .fns
        .iter()
        .map(|function| function.name.as_str())
        .collect::<Vec<_>>();
    names.sort_unstable();
    let mut hasher = blake3::Hasher::new();
    for name in names {
        field(&mut hasher, name.as_bytes());
    }
    let digest = hasher.finalize().to_hex();
    format!("whole-program:{}", &digest[..16])
}

// The single predicate for "may this build read or write the durable store".
// Both query lowering here and the module interface cache consult it, so the
// wasm carve-out and the flag logic live in exactly one place.
//
// The store is a filesystem cache; wasm32 (the browser playground) has no
// persistent filesystem and each compile is ephemeral, so opening it would fail
// `create_dir_all` with an unsupported-platform error. The cache is
// observationally invisible, so skipping it there changes nothing.
pub(super) const fn cache_enabled(cfg: &Config) -> bool {
    cfg.flags.compiler_cache && !cfg.flags.store && cfg!(not(target_arch = "wasm32"))
}

pub(super) fn lower_effect_queries(
    core: &ElaboratedCore,
    ctors: &BTreeMap<String, CtorInfo>,
    grades: &OpGrades,
    cfg: &Config,
) -> Result<EffectLowered, Error> {
    if !cache_enabled(cfg) {
        return lower_effects(core, ctors, &cfg.flags, grades).map_err(Error::from);
    }
    let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
    let key = effect_plan_key(core, ctors, grades, cfg)?;
    if let Some(retained) = load_effect_plan(&store, &key, core)? {
        if let Some(session) = &cfg.session {
            session.record_hit();
            session.record_decision(QueryDecision::new(
                QueryKind::Effect,
                effect_identity(core),
                key.clone(),
                FactOutcome::Hit,
                store.get_query(EFFECT_PLAN_QUERY, &key)?,
                Vec::new(),
            ));
        }
        return Ok((LoweredCore(Core { fns: retained }), ctors.clone(), None));
    }
    let result_key = effect_result_key(core, ctors, grades, cfg)?;
    if let Some(result) = load_effect_result(&store, &result_key, core, ctors)? {
        if let Some(session) = &cfg.session {
            session.record_hit();
            session.record_decision(QueryDecision::new(
                QueryKind::Effect,
                effect_identity(core),
                result_key.clone(),
                FactOutcome::Hit,
                store.get_query(EFFECT_RESULT_QUERY, &result_key)?,
                Vec::new(),
            ));
        }
        return Ok(result);
    }
    if let Some(session) = &cfg.session {
        session.record_miss();
    }
    let result = lower_effects(core, ctors, &cfg.flags, grades).map_err(Error::from)?;
    let written = if is_projection(core, ctors, &result) {
        store_effect_plan(&store, &key, core, &result.0)?
    } else if let Some(added_ctors) = constructor_delta(ctors, &result.1) {
        store_effect_result(
            &store,
            &result_key,
            core,
            &result.0,
            added_ctors,
            result.2.as_deref(),
        )?
    } else {
        false
    };
    if let Some(session) = &cfg.session {
        if written {
            session.record_write();
        }
        let (query, query_key) = if is_projection(core, ctors, &result) {
            (EFFECT_PLAN_QUERY, &key)
        } else {
            (EFFECT_RESULT_QUERY, &result_key)
        };
        session.record_decision(QueryDecision::new(
            QueryKind::Effect,
            effect_identity(core),
            query_key.clone(),
            if written {
                FactOutcome::Write
            } else {
                FactOutcome::Miss
            },
            store.get_query(query, query_key)?,
            vec!["strategy, reachability, grades, or lowering flags changed".to_string()],
        ));
    }
    Ok(result)
}

fn effect_plan_key(
    core: &ElaboratedCore,
    ctors: &BTreeMap<String, CtorInfo>,
    grades: &OpGrades,
    cfg: &Config,
) -> Result<String, Error> {
    let input_digests = hash_program(core, &BTreeMap::new());
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, EFFECT_PLAN_QUERY_SCHEMA);
    field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut hasher,
        cfg.artifact_identity_for("frontend")
            .fingerprint()
            .as_bytes(),
    );
    for function in &core.fns {
        field(&mut hasher, function.name.as_str().as_bytes());
        field(&mut hasher, input_digests[&function.name].as_bytes());
    }
    field(&mut hasher, format!("{ctors:?}").as_bytes());
    field(&mut hasher, format!("{grades:?}").as_bytes());
    Ok(hasher.finalize().to_hex().to_string())
}

fn effect_result_key(
    core: &ElaboratedCore,
    ctors: &BTreeMap<String, CtorInfo>,
    grades: &OpGrades,
    cfg: &Config,
) -> Result<String, Error> {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, EFFECT_RESULT_QUERY_SCHEMA);
    field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut hasher,
        cfg.artifact_identity_for("frontend")
            .fingerprint()
            .as_bytes(),
    );
    let exact_core = serde_json::to_vec(&core.0)
        .map_err(|_| corrupt("could not encode effect-lowering query input"))?;
    field(&mut hasher, &exact_core);
    field(&mut hasher, format!("{ctors:?}").as_bytes());
    field(&mut hasher, format!("{grades:?}").as_bytes());
    Ok(hasher.finalize().to_hex().to_string())
}

fn load_effect_plan(
    store: &Store,
    key: &str,
    core: &ElaboratedCore,
) -> Result<Option<Vec<CoreFn>>, Error> {
    let Some(object_hash) = store.get_query(EFFECT_PLAN_QUERY, key)? else {
        return Ok(None);
    };
    let bytes = store.get(&object_hash)?;
    if bytes.len() > MAX_EFFECT_PLAN_ARTIFACT_BYTES {
        return Err(corrupt("effect-lowering plan exceeds the size limit"));
    }
    if blake3::hash(&bytes).to_hex().as_str() != object_hash {
        return Err(corrupt("effect-lowering plan object hash mismatch"));
    }
    let plan: EffectLoweringPlan = serde_json::from_slice(&bytes)
        .map_err(|error| corrupt(&format!("malformed effect-lowering plan: {error}")))?;
    let input_members = core
        .fns
        .iter()
        .map(|function| function.name.as_str().to_string())
        .collect::<Vec<_>>();
    if plan.format != EFFECT_PLAN_FORMAT || plan.key != key || plan.input_members != input_members {
        return Err(corrupt("effect-lowering plan failed validation"));
    }
    let by_name = core
        .fns
        .iter()
        .map(|function| (function.name.as_str(), function))
        .collect::<BTreeMap<_, _>>();
    let mut seen = BTreeSet::new();
    let mut retained = Vec::with_capacity(plan.retained_members.len());
    for name in &plan.retained_members {
        if !seen.insert(name.as_str()) {
            return Err(corrupt("effect-lowering plan repeats a retained member"));
        }
        let Some(function) = by_name.get(name.as_str()) else {
            return Err(corrupt("effect-lowering plan names an absent member"));
        };
        retained.push((*function).clone());
    }
    Ok(Some(retained))
}

fn is_projection(
    input: &ElaboratedCore,
    input_ctors: &BTreeMap<String, CtorInfo>,
    result: &EffectLowered,
) -> bool {
    if &result.1 != input_ctors || result.2.is_some() {
        return false;
    }
    let input_by_name = input
        .fns
        .iter()
        .map(|function| (function.name, function))
        .collect::<BTreeMap<_, _>>();
    result.0.fns.iter().all(|function| {
        input_by_name
            .get(&function.name)
            .is_some_and(|input| *input == function)
    })
}

fn store_effect_plan(
    store: &Store,
    key: &str,
    input: &ElaboratedCore,
    output: &LoweredCore,
) -> Result<bool, Error> {
    let plan = EffectLoweringPlan {
        format: EFFECT_PLAN_FORMAT.to_string(),
        key: key.to_string(),
        input_members: input
            .fns
            .iter()
            .map(|function| function.name.as_str().to_string())
            .collect(),
        retained_members: output
            .fns
            .iter()
            .map(|function| function.name.as_str().to_string())
            .collect(),
    };
    let bytes =
        serde_json::to_vec(&plan).map_err(|_| corrupt("could not encode effect-lowering plan"))?;
    if bytes.len() > MAX_EFFECT_PLAN_ARTIFACT_BYTES {
        return Ok(false);
    }
    let object_hash = blake3::hash(&bytes).to_hex().to_string();
    store.put(&object_hash, &bytes)?;
    store.put_query(EFFECT_PLAN_QUERY, key, &object_hash)?;
    Ok(true)
}

fn constructor_delta(
    input: &BTreeMap<String, CtorInfo>,
    output: &BTreeMap<String, CtorInfo>,
) -> Option<Vec<String>> {
    if input
        .iter()
        .any(|(name, ctor)| output.get(name) != Some(ctor))
    {
        return None;
    }
    Some(
        output
            .keys()
            .filter(|name| !input.contains_key(*name))
            .cloned()
            .collect(),
    )
}

fn load_effect_result(
    store: &Store,
    key: &str,
    input: &ElaboratedCore,
    input_ctors: &BTreeMap<String, CtorInfo>,
) -> Result<Option<EffectLowered>, Error> {
    let Some(object_hash) = store.get_query(EFFECT_RESULT_QUERY, key)? else {
        return Ok(None);
    };
    let bytes = store.get(&object_hash)?;
    if bytes.len() > MAX_EFFECT_RESULT_ARTIFACT_BYTES {
        return Err(corrupt("effect-lowering result exceeds the size limit"));
    }
    if blake3::hash(&bytes).to_hex().as_str() != object_hash {
        return Err(corrupt("effect-lowering result object hash mismatch"));
    }
    let mut deserializer = serde_json::Deserializer::from_slice(&bytes);
    deserializer.disable_recursion_limit();
    let artifact =
        EffectLoweringResult::deserialize(serde_stacker::Deserializer::new(&mut deserializer))
            .map_err(|error| corrupt(&format!("malformed effect-lowering result: {error}")))?;
    deserializer
        .end()
        .map_err(|error| corrupt(&format!("malformed effect-lowering result: {error}")))?;
    let input_members = input
        .fns
        .iter()
        .map(|function| function.name.as_str().to_string())
        .collect::<Vec<_>>();
    if artifact.format != EFFECT_RESULT_FORMAT
        || artifact.key != key
        || artifact.input_members != input_members
    {
        return Err(corrupt("effect-lowering result failed validation"));
    }
    let mut names = BTreeSet::new();
    if artifact
        .output
        .fns
        .iter()
        .any(|function| !names.insert(function.name))
    {
        return Err(corrupt("effect-lowering result repeats a function"));
    }
    lint_core(&artifact.output, PassStage::Late)
        .map_err(|_| corrupt("effect-lowering result contains invalid Core"))?;
    let mut ctors = input_ctors.clone();
    let mut added = BTreeSet::new();
    for name in &artifact.added_ctors {
        if input_ctors.contains_key(name)
            || !added.insert(name.as_str())
            || !crate::core::effect_lower::add_synthetic_ctor(&mut ctors, name)
        {
            return Err(corrupt(
                "effect-lowering result has an invalid constructor delta",
            ));
        }
    }
    Ok(Some((
        LoweredCore(artifact.output),
        ctors,
        artifact.warning,
    )))
}

fn store_effect_result(
    store: &Store,
    key: &str,
    input: &ElaboratedCore,
    output: &LoweredCore,
    added_ctors: Vec<String>,
    warning: Option<&str>,
) -> Result<bool, Error> {
    let artifact = EffectLoweringResult {
        format: EFFECT_RESULT_FORMAT.to_string(),
        key: key.to_string(),
        input_members: input
            .fns
            .iter()
            .map(|function| function.name.as_str().to_string())
            .collect(),
        output: output.0.clone(),
        added_ctors,
        warning: warning.map(ToString::to_string),
    };
    let bytes = serde_json::to_vec(&artifact)
        .map_err(|_| corrupt("could not encode effect-lowering result"))?;
    if bytes.len() > MAX_EFFECT_RESULT_ARTIFACT_BYTES {
        return Ok(false);
    }
    let object_hash = blake3::hash(&bytes).to_hex().to_string();
    store.put(&object_hash, &bytes)?;
    store.put_query(EFFECT_RESULT_QUERY, key, &object_hash)?;
    Ok(true)
}

fn optimizer_identity(group: &[CoreFn], stage: PassStage, pass: CorePass) -> String {
    let mut members = group
        .iter()
        .map(|function| function.name.as_str())
        .collect::<Vec<_>>();
    members.sort_unstable();
    format!(
        "{}:{}:{}",
        stage_name(stage),
        pass.name(),
        members.join(",")
    )
}

fn run_local_pass(core: &Core, query: &SccPassQuery<'_>) -> Result<Core, Error> {
    let shallow = shallow_hashes(core, &BTreeMap::new());
    let by_name = core
        .fns
        .iter()
        .map(|function| (function.name, function))
        .collect::<BTreeMap<_, _>>();
    let groups = crate::core::scc_groups(core)
        .into_iter()
        .map(|members| {
            members
                .iter()
                .map(|name| (*by_name[name]).clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let results =
        QueryScheduler::new(query.cfg.flags.query_threads).map_ordered(&groups, |group| {
            let key = query_key(group, &shallow, query);
            let identity = optimizer_identity(group, query.stage, query.pass);
            if load_fixed_point(query.store, &key, group, query.stage, query.pass)? {
                if let Some(session) = &query.cfg.session {
                    session.record_hit();
                    session.record_decision(QueryDecision::new(
                        QueryKind::Optimizer,
                        identity,
                        key.clone(),
                        FactOutcome::Hit,
                        query.store.get_query(OPT_SCC_QUERY, &key)?,
                        Vec::new(),
                    ));
                }
                return Ok(group.clone());
            }
            if let Some(session) = &query.cfg.session {
                session.record_miss();
            }
            let output = run_opt_spec(
                &Core { fns: group.clone() },
                query.newtype_ctors,
                &[query.pass],
                query.stage,
                &[],
                &query.cfg.flags,
            )
            .0
            .fns;
            let fixed_point = output == *group;
            if fixed_point {
                store_fixed_point(query.store, &key, group, query.stage, query.pass)?;
            }
            if let Some(session) = &query.cfg.session {
                if fixed_point {
                    session.record_write();
                }
                session.record_decision(QueryDecision::new(
                    QueryKind::Optimizer,
                    identity,
                    key.clone(),
                    if fixed_point {
                        FactOutcome::Write
                    } else {
                        FactOutcome::Miss
                    },
                    query.store.get_query(OPT_SCC_QUERY, &key)?,
                    vec!["SCC input or optimization pass fingerprint changed".to_string()],
                ));
            }
            Ok::<Vec<CoreFn>, Error>(output)
        });
    let mut transformed = BTreeMap::<Sym, CoreFn>::new();
    for result in results {
        for function in result? {
            transformed.insert(function.name, function);
        }
    }
    let fns = core
        .fns
        .iter()
        .map(|function| {
            transformed
                .remove(&function.name)
                .expect("SCC-local pass preserves definitions")
        })
        .collect();
    Ok(Core { fns })
}

fn query_key(group: &[CoreFn], shallow: &crate::core::Hashes, query: &SccPassQuery<'_>) -> String {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, OPT_SCC_QUERY_SCHEMA);
    field(&mut hasher, query.identity.compiler.as_bytes());
    field(&mut hasher, query.identity.artifact.as_bytes());
    field(&mut hasher, stage_name(query.stage).as_bytes());
    field(&mut hasher, query.pass.name().as_bytes());
    field(&mut hasher, query.pipeline_fingerprint.as_bytes());
    for function in group {
        field(&mut hasher, function.name.as_str().as_bytes());
        field(&mut hasher, shallow[&function.name].as_bytes());
    }
    if query.pass == CorePass::EraseNewtypes {
        for ctor in query.newtype_ctors {
            field(&mut hasher, ctor.as_str().as_bytes());
        }
    }
    hasher.finalize().to_hex().to_string()
}

fn load_fixed_point(
    store: &Store,
    key: &str,
    input: &[CoreFn],
    stage: PassStage,
    pass: CorePass,
) -> Result<bool, Error> {
    let Some(object_hash) = store.get_query(OPT_SCC_QUERY, key)? else {
        return Ok(false);
    };
    let bytes = store.get(&object_hash)?;
    if bytes.len() > MAX_OPT_SCC_ARTIFACT_BYTES {
        return Err(corrupt("optimized SCC artifact exceeds the size limit"));
    }
    if blake3::hash(&bytes).to_hex().as_str() != object_hash {
        return Err(corrupt("optimized SCC object hash mismatch"));
    }
    let artifact: OptimizedSccArtifact = serde_json::from_slice(&bytes)
        .map_err(|error| corrupt(&format!("malformed optimized SCC artifact: {error}")))?;
    let names = input
        .iter()
        .map(|function| function.name.as_str().to_string())
        .collect::<Vec<_>>();
    if artifact.format != OPT_SCC_FORMAT
        || artifact.key != key
        || artifact.stage != stage_name(stage)
        || artifact.pass != pass.name()
        || artifact.input_members != names
    {
        return Err(corrupt("optimized SCC artifact failed validation"));
    }
    Ok(true)
}

fn store_fixed_point(
    store: &Store,
    key: &str,
    input: &[CoreFn],
    stage: PassStage,
    pass: CorePass,
) -> Result<(), Error> {
    let artifact = OptimizedSccArtifact {
        format: OPT_SCC_FORMAT.to_string(),
        key: key.to_string(),
        stage: stage_name(stage).to_string(),
        pass: pass.name().to_string(),
        input_members: input
            .iter()
            .map(|function| function.name.as_str().to_string())
            .collect(),
    };
    let bytes = serde_json::to_vec(&artifact)
        .map_err(|_| corrupt("could not encode optimized SCC artifact"))?;
    let object_hash = blake3::hash(&bytes).to_hex().to_string();
    store.put(&object_hash, &bytes)?;
    store.put_query(OPT_SCC_QUERY, key, &object_hash)?;
    Ok(())
}

const fn stage_name(stage: PassStage) -> &'static str {
    match stage {
        PassStage::PreLowering => "pre",
        PassStage::Late => "late",
    }
}

fn corrupt(message: &str) -> Error {
    Error::Io(io::Error::new(io::ErrorKind::InvalidData, message))
}
