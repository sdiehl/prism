use std::collections::{BTreeMap, BTreeSet};
use std::io;

use serde::{Deserialize, Serialize};

use crate::core::typed::specialize::specialize as specialize_typed;
use crate::core::typed::{
    cse as cse_typed, erase_newtypes as erase_newtypes_typed, fuse as fuse_typed,
    inline as inline_typed, simplify as simplify_typed,
};
use crate::core::{
    effective_passes, lint_core, pass_fingerprint, scc_groups, typed_verification_error,
    verify_typed_core, Core, CorePass, PassStage, PassStats, TypedCore, TypedCoreFn,
    TypedCorePhase, VerifyEnv,
};
use crate::error::Error;
use crate::flags::DynFlags;
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
// compatibility reader is used. v4: keys cover the typed witnesses, so a stored
// fixed point certifies the TYPED pass, not only its erased shadow.
const OPT_SCC_QUERY_SCHEMA: &[u8] = b"prism-optimized-scc-query-v4";
const OPT_SCC_FORMAT: &str = "prism-optimized-scc-fixed-point-v2";
const MAX_OPT_SCC_ARTIFACT_BYTES: usize = 64 * 1024;

// Typed passes recurse over witness-carrying trees; scheduler workers start on
// small stacks, so each per-group pass run grows its own.
const TYPED_PASS_STACK: usize = 64 * 1024 * 1024;

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

struct TypedSccQuery<'a> {
    store: &'a Store,
    newtype_ctors: &'a BTreeSet<Sym>,
    env: &'a VerifyEnv,
    stage: PassStage,
    pass: CorePass,
    pipeline_fingerprint: &'a str,
    identity: &'a SccQueryIdentity,
    cfg: &'a Config,
}

// Run one stage of the optimization pipeline over typed Core: verify the input,
// run each pass in order, and verify after every pass. SCC-local passes go
// through the durable fixed-point cache when it is enabled; the diagnostic
// switches (Core Lint, per-pass dumps, tick stats) force the plain route, which
// serves them from the erased view at every pass boundary.
pub(super) fn run_typed_opt_queries<P: TypedCorePhase>(
    typed: TypedCore<P>,
    env: &VerifyEnv,
    newtype_ctors: &BTreeSet<Sym>,
    stage: PassStage,
    cfg: &Config,
) -> Result<TypedCore<P>, Error> {
    let passes = effective_passes(
        cfg.opt(),
        cfg.passes.as_ref(),
        stage,
        &cfg.disabled,
        &cfg.flags,
    );
    let pipeline_fingerprint = pass_fingerprint(
        cfg.opt(),
        cfg.passes.as_ref(),
        stage,
        &cfg.disabled,
        &cfg.flags,
    );
    verify_typed_core(&typed, env).map_err(typed_verification_error)?;
    if !cache_enabled(cfg)
        || cfg.flags.core_lint
        || cfg.flags.opt_stats
        || cfg.flags.dump_core.is_some()
    {
        return run_typed_stage_plain(typed, env, newtype_ctors, stage, &passes, &cfg.flags);
    }

    let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
    let identity = SccQueryIdentity {
        compiler: compiler_binary_fingerprint()?.to_string(),
        artifact: cfg.artifact_identity_for("frontend").fingerprint(),
    };
    let mut current = typed;
    for &pass in &passes {
        reject_off_stage(pass, stage)?;
        current = if pass.is_scc_local() {
            run_typed_local_pass(
                current,
                &TypedSccQuery {
                    store: &store,
                    newtype_ctors,
                    env,
                    stage,
                    pass,
                    pipeline_fingerprint: &pipeline_fingerprint,
                    identity: &identity,
                    cfg,
                },
            )?
        } else {
            run_typed_pass(pass, current, newtype_ctors, env)?.0
        };
        verify_typed_core(&current, env).map_err(typed_verification_error)?;
    }
    Ok(current)
}

// The uncached route: whole-program passes in order, with the diagnostic
// switches served from the erased view exactly as the erased pipeline served
// them (same dump labels and ordinals, same lint panic, same tick report).
fn run_typed_stage_plain<P: TypedCorePhase>(
    typed: TypedCore<P>,
    env: &VerifyEnv,
    newtype_ctors: &BTreeSet<Sym>,
    stage: PassStage,
    passes: &[CorePass],
    flags: &DynFlags,
) -> Result<TypedCore<P>, Error> {
    let lint = |core: &Core, after: &str| {
        if flags.core_lint {
            if let Err(errs) = lint_core(core, stage) {
                panic!(
                    "PRISM_CORE_LINT: ill-formed Core after {after}:\n{}",
                    errs.join("\n")
                );
            }
        }
    };
    let dump_sink = flags.dump_core.clone();
    let dump_run = crate::core::opt::next_dump_run();
    let mut ord = 0;
    let mut stats = PassStats::default();
    if dump_sink.is_some() || flags.core_lint {
        let erased = typed.clone().erase();
        if let Some(sink) = &dump_sink {
            crate::core::opt::dump_core(sink, dump_run, ord, "input", &erased);
            ord += 1;
        }
        lint(&erased, "<input>");
    }
    let mut current = typed;
    for &pass in passes {
        reject_off_stage(pass, stage)?;
        let (next, ticks) = run_typed_pass(pass, current, newtype_ctors, env)?;
        stats.record(pass.name(), ticks);
        if dump_sink.is_some() || flags.core_lint {
            let erased = next.clone().erase();
            lint(&erased, pass.name());
            if let Some(sink) = &dump_sink {
                crate::core::opt::dump_core(sink, dump_run, ord, pass.name(), &erased);
                ord += 1;
            }
        }
        verify_typed_core(&next, env).map_err(typed_verification_error)?;
        current = next;
    }
    if flags.opt_stats {
        eprint!("{}", stats.report());
    }
    Ok(current)
}

// A pass outside its stage is a driver routing bug, never a user error.
fn reject_off_stage(pass: CorePass, stage: PassStage) -> Result<(), Error> {
    if pass.stage() == stage {
        Ok(())
    } else {
        Err(Error::InternalInvariant(format!(
            "typed optimizer stage runner rejected {}",
            pass.name()
        )))
    }
}

fn run_typed_pass<P: TypedCorePhase>(
    pass: CorePass,
    core: TypedCore<P>,
    newtype_ctors: &BTreeSet<Sym>,
    env: &VerifyEnv,
) -> Result<(TypedCore<P>, u64), Error> {
    Ok(match pass {
        CorePass::Fuse => {
            let (next, stats) = fuse_typed(core);
            (next, stats.ticks())
        }
        CorePass::EraseNewtypes => {
            let (next, stats) = erase_newtypes_typed(core, newtype_ctors, env);
            (next, stats.ticks())
        }
        CorePass::Specialize => {
            let (next, stats) = specialize_typed(core).map_err(Error::from)?;
            (next, stats.ticks())
        }
        CorePass::Simplify => {
            let (next, stats) = simplify_typed(core).map_err(Error::from)?;
            (next, stats.ticks())
        }
        CorePass::Inline => {
            let (next, stats) = inline_typed(core);
            (next, stats.ticks())
        }
        CorePass::Cse => {
            let (next, stats) = cse_typed(core);
            (next, stats.ticks())
        }
    })
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

fn optimizer_identity(members: &[Sym], stage: PassStage, pass: CorePass) -> String {
    let mut names = members.iter().map(|name| name.as_str()).collect::<Vec<_>>();
    names.sort_unstable();
    format!("{}:{}:{}", stage_name(stage), pass.name(), names.join(","))
}

// One SCC-local pass over the whole typed program: skip every SCC group whose
// typed content is a recorded fixed point for this pass, run the pass on the
// remaining groups (each definition transforms independently, so per-group runs
// compose to the whole-program result), and record the fresh fixed points.
fn run_typed_local_pass<P: TypedCorePhase>(
    core: TypedCore<P>,
    query: &TypedSccQuery<'_>,
) -> Result<TypedCore<P>, Error> {
    let erased = core.clone().erase();
    let groups = scc_groups(&erased);
    let digests = core
        .functions()
        .iter()
        .map(|function| (function.name(), typed_digest(function)))
        .collect::<BTreeMap<_, _>>();

    let mut skip = BTreeSet::new();
    let mut pending: Vec<(Vec<Sym>, String)> = Vec::new();
    for members in groups {
        let key = typed_query_key(&members, &digests, query);
        if load_fixed_point(query.store, &key, &members, query.stage, query.pass)? {
            if let Some(session) = &query.cfg.session {
                session.record_hit();
                session.record_decision(QueryDecision::new(
                    QueryKind::Optimizer,
                    optimizer_identity(&members, query.stage, query.pass),
                    key.clone(),
                    FactOutcome::Hit,
                    query.store.get_query(OPT_SCC_QUERY, &key)?,
                    Vec::new(),
                ));
            }
            skip.extend(members);
        } else {
            if let Some(session) = &query.cfg.session {
                session.record_miss();
            }
            pending.push((members, key));
        }
    }

    let mut kept = BTreeMap::new();
    let mut to_run = BTreeMap::new();
    for function in core.into_functions() {
        if skip.contains(&function.name()) {
            kept.insert(function.name(), function);
        } else {
            to_run.insert(function.name(), function);
        }
    }

    let inputs = pending
        .iter()
        .map(|(members, _)| {
            members
                .iter()
                .map(|member| to_run[member].clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let results =
        QueryScheduler::new(query.cfg.flags.query_threads).map_ordered(&inputs, |group| {
            stacker::maybe_grow(TYPED_PASS_STACK, TYPED_PASS_STACK, || {
                run_typed_pass(
                    query.pass,
                    TypedCore::<P>::from_functions(group.clone()),
                    query.newtype_ctors,
                    query.env,
                )
                .map(|(next, _)| next.into_functions())
            })
        });

    let mut transformed = BTreeMap::<Sym, TypedCoreFn>::new();
    for (((members, key), input), result) in pending.iter().zip(&inputs).zip(results) {
        let output = result?;
        let fixed_point = output == *input;
        if fixed_point {
            store_fixed_point(query.store, key, members, query.stage, query.pass)?;
        }
        if let Some(session) = &query.cfg.session {
            if fixed_point {
                session.record_write();
            }
            session.record_decision(QueryDecision::new(
                QueryKind::Optimizer,
                optimizer_identity(members, query.stage, query.pass),
                key.clone(),
                if fixed_point {
                    FactOutcome::Write
                } else {
                    FactOutcome::Miss
                },
                query.store.get_query(OPT_SCC_QUERY, key)?,
                vec!["SCC input or optimization pass fingerprint changed".to_string()],
            ));
        }
        for function in output {
            transformed.insert(function.name(), function);
        }
    }

    // Rebuild in original program order (the erased view preserves it exactly).
    let fns = erased
        .fns
        .iter()
        .map(|function| {
            let name = function.name;
            kept.remove(&name).map_or_else(
                || {
                    transformed.remove(&name).ok_or_else(|| {
                        Error::InternalInvariant(format!(
                            "SCC-local pass dropped definition `{}`",
                            name.as_str()
                        ))
                    })
                },
                Ok,
            )
        })
        .collect::<Result<Vec<_>, Error>>()?;
    Ok(TypedCore::from_functions(fns))
}

fn typed_query_key(
    members: &[Sym],
    digests: &BTreeMap<Sym, String>,
    query: &TypedSccQuery<'_>,
) -> String {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, OPT_SCC_QUERY_SCHEMA);
    field(&mut hasher, query.identity.compiler.as_bytes());
    field(&mut hasher, query.identity.artifact.as_bytes());
    field(&mut hasher, stage_name(query.stage).as_bytes());
    field(&mut hasher, query.pass.name().as_bytes());
    field(&mut hasher, query.pipeline_fingerprint.as_bytes());
    for name in members {
        field(&mut hasher, name.as_str().as_bytes());
        field(&mut hasher, digests[name].as_bytes());
    }
    if query.pass == CorePass::EraseNewtypes {
        for ctor in query.newtype_ctors {
            field(&mut hasher, ctor.as_str().as_bytes());
        }
    }
    hasher.finalize().to_hex().to_string()
}

// `Debug` is the digest encoding on purpose: the compiler binary fingerprint is
// a key field, so the rendering only has to be stable within one binary, and
// every typed node renders structurally (interned symbols print their strings,
// all collections are ordered), so equal functions always hash equal.
fn typed_digest(function: &TypedCoreFn) -> String {
    blake3::hash(format!("{function:?}").as_bytes())
        .to_hex()
        .to_string()
}

fn load_fixed_point(
    store: &Store,
    key: &str,
    members: &[Sym],
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
    let names = members
        .iter()
        .map(|name| name.as_str().to_string())
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
    members: &[Sym],
    stage: PassStage,
    pass: CorePass,
) -> Result<(), Error> {
    let artifact = OptimizedSccArtifact {
        format: OPT_SCC_FORMAT.to_string(),
        key: key.to_string(),
        stage: stage_name(stage).to_string(),
        pass: pass.name().to_string(),
        input_members: members
            .iter()
            .map(|name| name.as_str().to_string())
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
