use std::collections::{BTreeMap, BTreeSet};
use std::io;

use serde::{Deserialize, Serialize};

use crate::core::{
    effective_passes, run_opt_spec, shallow_hashes, Core, CoreFn, CorePass, PassStage,
};
use crate::error::Error;
use crate::lineage::{FactOutcome, QueryKind};
use crate::store::disk::{resolve_store_path, Store};
use crate::sym::Sym;

use super::identity::compiler_binary_fingerprint;
use super::input::field;
use super::scheduler::QueryScheduler;
use super::session::QueryDecision;
use super::Config;

const OPT_SCC_QUERY: &str = "optimized-scc";
// The `-vN` here is a cache-bust counter, not a compat version: it is hashed into
// the query key so a format change misses stale entries. No old version or
// compatibility reader is used.
const OPT_SCC_QUERY_SCHEMA: &[u8] = b"prism-optimized-scc-query-v3";
const OPT_SCC_FORMAT: &str = "prism-optimized-scc-fixed-point-v1";
const MAX_OPT_SCC_ARTIFACT_BYTES: usize = 64 * 1024;

#[derive(Debug, Serialize, Deserialize)]
struct OptimizedSccArtifact {
    format: String,
    key: String,
    stage: String,
    pass: String,
    input_members: Vec<String>,
}

struct SccQueryIdentity {
    compiler: String,
    artifact: String,
}

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
    let pipeline_fingerprint = crate::core::pass_fingerprint(
        cfg.opt,
        cfg.passes.as_ref(),
        stage,
        &cfg.disabled,
        &cfg.flags,
    );
    run_opt_queries_resolved(
        core,
        newtype_ctors,
        stage,
        &passes,
        &pipeline_fingerprint,
        cfg,
    )
}

fn run_opt_queries_resolved(
    core: &Core,
    newtype_ctors: &BTreeSet<Sym>,
    stage: PassStage,
    passes: &[CorePass],
    pipeline_fingerprint: &str,
    cfg: &Config,
) -> Result<Core, Error> {
    if !cache_enabled(cfg)
        || cfg.flags.core_lint
        || cfg.flags.opt_stats
        || cfg.flags.dump_core.is_some()
    {
        return Ok(run_opt_spec(core, newtype_ctors, passes, stage, &[], &cfg.flags).0);
    }

    let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
    let identity = SccQueryIdentity {
        compiler: compiler_binary_fingerprint()?.to_string(),
        artifact: cfg.artifact_identity_for("frontend").fingerprint(),
    };
    let mut current = core.clone();
    for &pass in passes {
        current = if pass.is_scc_local() {
            run_local_pass(
                &current,
                &SccPassQuery {
                    store: &store,
                    newtype_ctors,
                    stage,
                    pass,
                    pipeline_fingerprint,
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

// The single predicate for "may this build read or write the durable store".
// Optimizer queries here and the module interface cache consult it, so the wasm
// carve-out and the flag logic live in exactly one place.
//
// The store is a filesystem cache; wasm32 (the browser playground) has no
// persistent filesystem and each compile is ephemeral, so opening it would fail
// `create_dir_all` with an unsupported-platform error. The cache is
// observationally invisible, so skipping it there changes nothing.
pub(super) const fn cache_enabled(cfg: &Config) -> bool {
    cfg.flags.compiler_cache && !cfg.flags.store && cfg!(not(target_arch = "wasm32"))
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
            transformed.remove(&function.name).ok_or_else(|| {
                Error::InternalInvariant(format!(
                    "SCC-local pass dropped definition `{}`",
                    function.name.as_str()
                ))
            })
        })
        .collect::<Result<Vec<CoreFn>, Error>>()?;
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
