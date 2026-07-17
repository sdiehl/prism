use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::codegen::{
    emit_llvm_closure_plan_shard_bc, emit_llvm_native_kont_plan_bc, emit_llvm_scc_bc,
    llvm_scc_closure_summary, native_kont_state_map, plan_llvm_closures_from_summaries,
    ClosurePlanShard, ClosureSummary, SccBitcodeError,
};
use crate::core::traverse::Visit;
use crate::core::{
    reachable_fns, shallow_hashes, Comp, Core, CorePat, DepGraph, LoweredCore, Value,
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

const LLVM_SCC_QUERY: &str = "llvm-scc-bitcode";
// The `-v2` is a cache-bust counter, not a compat version: hashed into the query
// key so a format change misses stale entries. No old version is read back.
const LLVM_SCC_QUERY_SCHEMA: &[u8] = b"prism-llvm-scc-bitcode-query-v2";
const LLVM_SCC_OBJECT_FORMAT: &str = "prism-llvm-scc-bitcode-v1";
const CLOSURE_SUMMARY_QUERY: &str = "llvm-scc-closure-summary";
const CLOSURE_SUMMARY_FORMAT: &str = "prism-llvm-scc-closure-summary-v1";
const MAX_LLVM_SCC_BYTES: usize = 64 * 1024 * 1024;
const MAX_CLOSURE_SUMMARY_BYTES: usize = 1024 * 1024;
const SCC_MEMBER_UNREACHABLE: u8 = 0;
const SCC_MEMBER_REACHABLE: u8 = 1;

pub(super) struct SccBitcode {
    pub paths: Vec<PathBuf>,
    pub all_hit: bool,
}

struct SccJob {
    members: Vec<Sym>,
    key: String,
    path: PathBuf,
}

struct SccJobOutput {
    path: PathBuf,
    hit: bool,
    closure_summary: ClosureSummary,
    closure_summary_hit: bool,
}

pub(super) fn materialize_scc_bitcode(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    native_kont_table: &str,
    directory: &Path,
    cfg: &Config,
) -> Result<Option<SccBitcode>, Error> {
    if !cfg.flags.scc_backend || cfg.flags.native_kont_frames {
        return Ok(None);
    }
    fs::create_dir_all(directory)?;
    let store = if cfg.flags.compiler_cache && !cfg.flags.store {
        Some(Store::open_or_create(resolve_store_path(
            cfg.flags.store_path.as_deref(),
        ))?)
    } else {
        None
    };
    let shallow = shallow_hashes(core, &BTreeMap::new());
    let groups = crate::core::scc_groups(core);
    let dependencies = DepGraph::of(core);
    let jobs = groups
        .iter()
        .enumerate()
        .map(|(index, members)| {
            Ok(SccJob {
                members: members.clone(),
                key: scc_key(core, ctors, members, &shallow, &dependencies, cfg)?,
                path: directory.join(format!("scc-{index}.bc")),
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let outputs = QueryScheduler::new(cfg.flags.query_threads).map_ordered(&jobs, |job| {
        let selected = job.members.iter().copied().collect::<BTreeSet<_>>();
        let (closure_summary, closure_summary_hit) = if let Some(store) = &store {
            if let Some(summary) = load_closure_summary(store, &job.key)? {
                record_hit(cfg);
                record_query(
                    cfg,
                    QueryKind::ClosurePlan,
                    &format!("summary:{}", member_identity(&job.members)),
                    &job.key,
                    FactOutcome::Hit,
                    store.get_query(CLOSURE_SUMMARY_QUERY, &job.key)?,
                    "",
                );
                (summary, true)
            } else {
                record_miss(cfg);
                let summary = llvm_scc_closure_summary(core, ctors, &selected)
                    .map_err(Error::CodegenBackend)?;
                let written = store_closure_summary(store, &job.key, &summary)?;
                if written {
                    record_write(cfg);
                }
                record_query(
                    cfg,
                    QueryKind::ClosurePlan,
                    &format!("summary:{}", member_identity(&job.members)),
                    &job.key,
                    if written {
                        FactOutcome::Write
                    } else {
                        FactOutcome::Miss
                    },
                    store.get_query(CLOSURE_SUMMARY_QUERY, &job.key)?,
                    "SCC closure inputs changed",
                );
                (summary, false)
            }
        } else {
            (
                llvm_scc_closure_summary(core, ctors, &selected).map_err(Error::CodegenBackend)?,
                false,
            )
        };
        if let Some(store) = &store {
            if load(store, &job.key, &job.path)? {
                record_hit(cfg);
                record_query(
                    cfg,
                    QueryKind::BackendScc,
                    &member_identity(&job.members),
                    &job.key,
                    FactOutcome::Hit,
                    store.get_query(LLVM_SCC_QUERY, &job.key)?,
                    "",
                );
                return Ok(SccJobOutput {
                    path: job.path.clone(),
                    hit: true,
                    closure_summary,
                    closure_summary_hit,
                });
            }
        }
        match emit_llvm_scc_bc(core, ctors, &selected, "", false, &job.path) {
            Ok(()) => {
                if let Some(store) = &store {
                    record_miss(cfg);
                    let written = store_result(store, &job.key, &job.path)?;
                    if written {
                        record_write(cfg);
                    }
                    record_query(
                        cfg,
                        QueryKind::BackendScc,
                        &member_identity(&job.members),
                        &job.key,
                        if written {
                            FactOutcome::Write
                        } else {
                            FactOutcome::Miss
                        },
                        store.get_query(LLVM_SCC_QUERY, &job.key)?,
                        "SCC input, dependency ABI, or constructor layout changed",
                    );
                }
                Ok(SccJobOutput {
                    path: job.path.clone(),
                    hit: false,
                    closure_summary,
                    closure_summary_hit,
                })
            }
            Err(SccBitcodeError::Codegen(error)) => Err(Error::CodegenBackend(error)),
        }
    });
    let mut paths = Vec::with_capacity(groups.len() + 2);
    let mut summaries = Vec::with_capacity(groups.len());
    let mut all_hit = true;
    for output in outputs {
        let output = output?;
        all_hit &= output.hit && output.closure_summary_hit;
        paths.push(output.path);
        summaries.push(output.closure_summary);
    }

    let closure_plan = plan_llvm_closures_from_summaries(core, ctors, &summaries)
        .map_err(Error::CodegenBackend)?;
    for (shard, fingerprint) in closure_plan.shards() {
        let (kind, name) = match shard {
            ClosurePlanShard::Adapters => ("closure-adapters", "closure-adapters.bc".to_string()),
            ClosurePlanShard::Dispatch(arity) => {
                ("closure-dispatch", format!("closure-dispatch-{arity}.bc"))
            }
        };
        let key = global_plan_key(kind, &fingerprint, cfg)?;
        let path = directory.join(&name);
        if let Some(store) = &store {
            if load(store, &key, &path)? {
                record_hit(cfg);
                record_query(
                    cfg,
                    QueryKind::ClosurePlan,
                    &name,
                    &key,
                    FactOutcome::Hit,
                    store.get_query(LLVM_SCC_QUERY, &key)?,
                    "",
                );
            } else {
                all_hit = false;
                record_miss(cfg);
                emit_llvm_closure_plan_shard_bc(core, ctors, &closure_plan, shard, &path)
                    .map_err(Error::CodegenBackend)?;
                let written = store_result(store, &key, &path)?;
                if written {
                    record_write(cfg);
                }
                record_query(
                    cfg,
                    QueryKind::ClosurePlan,
                    &name,
                    &key,
                    if written {
                        FactOutcome::Write
                    } else {
                        FactOutcome::Miss
                    },
                    store.get_query(LLVM_SCC_QUERY, &key)?,
                    "closure plan changed",
                );
            }
        } else {
            all_hit = false;
            emit_llvm_closure_plan_shard_bc(core, ctors, &closure_plan, shard, &path)
                .map_err(Error::CodegenBackend)?;
        }
        paths.push(path);
    }

    let plan_key = native_kont_plan_key(core, native_kont_table, cfg)?;
    let plan_path = directory.join("native-kont-plan.bc");
    if let Some(store) = &store {
        if load(store, &plan_key, &plan_path)? {
            record_hit(cfg);
            record_query(
                cfg,
                QueryKind::ClosurePlan,
                "native-kont-plan",
                &plan_key,
                FactOutcome::Hit,
                store.get_query(LLVM_SCC_QUERY, &plan_key)?,
                "",
            );
        } else {
            all_hit = false;
            record_miss(cfg);
            emit_llvm_native_kont_plan_bc(core, native_kont_table, &plan_path)
                .map_err(Error::CodegenBackend)?;
            let written = store_result(store, &plan_key, &plan_path)?;
            if written {
                record_write(cfg);
            }
            record_query(
                cfg,
                QueryKind::ClosurePlan,
                "native-kont-plan",
                &plan_key,
                if written {
                    FactOutcome::Write
                } else {
                    FactOutcome::Miss
                },
                store.get_query(LLVM_SCC_QUERY, &plan_key)?,
                "native continuation metadata changed",
            );
        }
    } else {
        all_hit = false;
        emit_llvm_native_kont_plan_bc(core, native_kont_table, &plan_path)
            .map_err(Error::CodegenBackend)?;
    }
    paths.push(plan_path);
    Ok(Some(SccBitcode { paths, all_hit }))
}

fn scc_key(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    members: &[Sym],
    shallow: &crate::core::Hashes,
    dependencies: &DepGraph,
    cfg: &Config,
) -> Result<String, Error> {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, LLVM_SCC_QUERY_SCHEMA);
    field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut hasher,
        cfg.artifact_identity_for("llvm-scc")
            .fingerprint()
            .as_bytes(),
    );
    let reachable = reachable_fns(core);
    for member in members {
        field(&mut hasher, member.as_str().as_bytes());
        field(&mut hasher, shallow[member].as_bytes());
        let reachability = if reachable.contains(member) {
            SCC_MEMBER_REACHABLE
        } else {
            SCC_MEMBER_UNREACHABLE
        };
        field(&mut hasher, &[reachability]);
    }

    // Cross-SCC calls depend on the direct callee's symbol and arity, never its
    // body. Constructor layout depends only on constructors this SCC allocates
    // or matches. These are semantic Core facts, not name parsing.
    let arities = core
        .fns
        .iter()
        .map(|function| (function.name, function.params.len()))
        .collect::<BTreeMap<_, _>>();
    let mut direct = BTreeSet::new();
    for member in members {
        direct.extend(dependencies.direct_deps(*member));
    }
    for dependency in direct {
        field(&mut hasher, dependency.as_str().as_bytes());
        field(&mut hasher, &arities[&dependency].to_le_bytes());
    }
    let by_name = core
        .fns
        .iter()
        .map(|function| (function.name, function))
        .collect::<BTreeMap<_, _>>();
    let mut used_ctors = UsedConstructors::default();
    for member in members {
        used_ctors.visit_comp(&by_name[member].body);
    }
    for ctor in used_ctors.names {
        field(&mut hasher, ctor.as_str().as_bytes());
        if let Some(info) = ctors.get(ctor.as_str()) {
            field(&mut hasher, format!("{info:?}").as_bytes());
        }
    }
    Ok(hasher.finalize().to_hex().to_string())
}

#[derive(Default)]
struct UsedConstructors {
    names: BTreeSet<Sym>,
}

impl Visit for UsedConstructors {
    fn visit_comp(&mut self, computation: &Comp) {
        if let Comp::Case(_, arms) = computation {
            for (pattern, _) in arms {
                if let CorePat::Ctor(name, _) = pattern {
                    self.names.insert(*name);
                }
            }
        }
        self.descend_comp(computation);
    }

    fn visit_value(&mut self, value: &Value) {
        if let Value::Ctor(name, _, _) = value {
            self.names.insert(*name);
        }
        self.descend_value(value);
    }
}

fn native_kont_plan_key(
    core: &Core,
    native_kont_table: &str,
    cfg: &Config,
) -> Result<String, Error> {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, LLVM_SCC_QUERY_SCHEMA);
    field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut hasher,
        cfg.artifact_identity_for("llvm-scc")
            .fingerprint()
            .as_bytes(),
    );
    field(&mut hasher, b"native-kont-plan");
    field(&mut hasher, native_kont_table.as_bytes());
    field(
        &mut hasher,
        native_kont_state_map(core, native_kont_table).as_bytes(),
    );
    Ok(hasher.finalize().to_hex().to_string())
}

fn global_plan_key(kind: &str, fingerprint: &str, cfg: &Config) -> Result<String, Error> {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, LLVM_SCC_QUERY_SCHEMA);
    field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut hasher,
        cfg.artifact_identity_for("llvm-scc")
            .fingerprint()
            .as_bytes(),
    );
    field(&mut hasher, kind.as_bytes());
    field(&mut hasher, fingerprint.as_bytes());
    Ok(hasher.finalize().to_hex().to_string())
}

fn load_closure_summary(store: &Store, key: &str) -> Result<Option<ClosureSummary>, Error> {
    let Some(object_hash) = store.get_query(CLOSURE_SUMMARY_QUERY, key)? else {
        return Ok(None);
    };
    let bytes = store.get(&object_hash)?;
    if bytes.len() > MAX_CLOSURE_SUMMARY_BYTES {
        return Err(corrupt(
            "backend SCC closure summary exceeds the size limit",
        ));
    }
    if blake3::hash(&bytes).to_hex().as_str() != object_hash {
        return Err(corrupt("backend SCC closure summary object hash mismatch"));
    }
    let prefix = format!("{CLOSURE_SUMMARY_FORMAT}\n{key}\n");
    let Some(payload) = bytes.strip_prefix(prefix.as_bytes()) else {
        return Err(corrupt("backend SCC closure summary failed validation"));
    };
    let summary: ClosureSummary = serde_json::from_slice(payload)
        .map_err(|error| corrupt(&format!("malformed backend SCC closure summary: {error}")))?;
    if !summary.validate() {
        return Err(corrupt("backend SCC closure summary failed validation"));
    }
    Ok(Some(summary))
}

fn store_closure_summary(
    store: &Store,
    key: &str,
    summary: &ClosureSummary,
) -> Result<bool, Error> {
    let payload = serde_json::to_vec(summary).map_err(|error| {
        corrupt(&format!(
            "could not encode backend SCC closure summary: {error}"
        ))
    })?;
    let mut bytes = format!("{CLOSURE_SUMMARY_FORMAT}\n{key}\n").into_bytes();
    bytes.extend_from_slice(&payload);
    if bytes.len() > MAX_CLOSURE_SUMMARY_BYTES {
        return Ok(false);
    }
    let object_hash = blake3::hash(&bytes).to_hex().to_string();
    store.put(&object_hash, &bytes)?;
    store.put_query(CLOSURE_SUMMARY_QUERY, key, &object_hash)?;
    Ok(true)
}

fn load(store: &Store, key: &str, path: &Path) -> Result<bool, Error> {
    let Some(object_hash) = store.get_query(LLVM_SCC_QUERY, key)? else {
        return Ok(false);
    };
    let bytes = store.get(&object_hash)?;
    if bytes.len() > MAX_LLVM_SCC_BYTES {
        return Err(corrupt("backend SCC bitcode exceeds the size limit"));
    }
    if blake3::hash(&bytes).to_hex().as_str() != object_hash {
        return Err(corrupt("backend SCC bitcode object hash mismatch"));
    }
    let prefix = format!("{LLVM_SCC_OBJECT_FORMAT}\n{key}\n");
    let Some(bitcode) = bytes.strip_prefix(prefix.as_bytes()) else {
        return Err(corrupt("backend SCC bitcode failed validation"));
    };
    fs::write(path, bitcode)?;
    Ok(true)
}

fn store_result(store: &Store, key: &str, path: &Path) -> Result<bool, Error> {
    let bitcode = fs::read(path)?;
    let mut bytes = format!("{LLVM_SCC_OBJECT_FORMAT}\n{key}\n").into_bytes();
    bytes.extend_from_slice(&bitcode);
    if bytes.len() > MAX_LLVM_SCC_BYTES {
        return Ok(false);
    }
    let object_hash = blake3::hash(&bytes).to_hex().to_string();
    store.put(&object_hash, &bytes)?;
    store.put_query(LLVM_SCC_QUERY, key, &object_hash)?;
    Ok(true)
}

fn member_identity(members: &[Sym]) -> String {
    let mut names = members
        .iter()
        .map(|member| member.as_str())
        .collect::<Vec<_>>();
    names.sort_unstable();
    names.join(",")
}

fn record_query(
    cfg: &Config,
    kind: QueryKind,
    identity: &str,
    key: &str,
    outcome: FactOutcome,
    output: Option<String>,
    reason: &str,
) {
    if let Some(session) = &cfg.session {
        session.record_decision(QueryDecision::new(
            kind,
            identity.to_string(),
            key.to_string(),
            outcome,
            output,
            (outcome != FactOutcome::Hit)
                .then(|| reason.to_string())
                .into_iter()
                .collect(),
        ));
    }
}

fn record_hit(cfg: &Config) {
    if let Some(session) = &cfg.session {
        session.record_hit();
    }
}

fn record_miss(cfg: &Config) {
    if let Some(session) = &cfg.session {
        session.record_miss();
    }
}

fn record_write(cfg: &Config) {
    if let Some(session) = &cfg.session {
        session.record_write();
    }
}

fn corrupt(message: &str) -> Error {
    Error::Io(io::Error::new(io::ErrorKind::InvalidData, message))
}
