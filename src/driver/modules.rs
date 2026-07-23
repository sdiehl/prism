use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use crate::error::Error;
use crate::hir::NodeFacts;
use crate::lineage::QueryFact;
use crate::parse::parse;
use crate::resolve::{load, resolve_loaded_module_units, Module, Root};
use crate::store::disk::{resolve_store_path, Store, Written};
use crate::syntax::ast::{Core as CorePhase, Program};
use crate::syntax::desugar::desugar_with_scope;
use crate::types::{check_seeded, Checked, DeclInfo, TypecheckSeed};
use serde::{Deserialize, Serialize};

use super::decision::{persist_facts, DecisionTracker, ModuleQueryDecision};
use super::downstream::cache_enabled;
use super::identity::{
    compiler_binary_fingerprint, module_interface_from_checked, stdlib_typecheck_seed,
    ModuleInterface,
};
use super::input::field;
use super::scheduler::QueryScheduler;
use super::{Config, PRELUDE, ROOT_MODULE_NAME};

const MODULE_CHECK_QUERY_SCHEMA: &[u8] = b"prism-module-check-query-v1";
const CHECKED_INTERFACE_QUERY_SCHEMA: &[u8] = b"prism-checked-interface-query-v1";
const CHECKED_INTERFACE_QUERY: &str = "checked-interface";
// v4 never publishes a body whose inferred declarations or node facts still
// contain unification metavariables. Such a body cannot be parsed back as a
// checked signature and a cache must never turn a valid cold build into a
// warm-build failure.
const CHECKED_BODY_QUERY_SCHEMA: &[u8] = b"prism-checked-body-query-v4";
const CHECKED_BODY_QUERY: &str = "checked-body";
// v2 carries the checked handler-residual facts (known operations, opaque
// effect labels, and an open-row marker). A v1 body cannot be promoted by
// defaulting those facts away: typed residual lowering must never reconstruct
// operation provenance from an effect-label-only interface.
const CHECKED_BODY_FORMAT: &str = "prism-checked-body-v2";
const STANDARD_FOUNDATION_SCHEMA: &[u8] = b"prism-standard-foundation-input-v1";
const INJECTED_FOUNDATION_NAME: &str = "__query_injected_foundation";
const INJECTED_FOUNDATION_SOURCE: &str = "fn __query_injected_foundation() : Unit = ()\n";

/// Remove `test fn` declarations from a program under production mode; retain
/// them under test mode. The single production-neutrality chokepoint shared by
/// the single-file front (`front::prepare_resolved_front`) and the project module
/// check (`check_modules_on`), so a test-only edit cannot move any production
/// interface hash, Core hash, or backend artifact, and the two paths cannot drift.
pub(super) fn strip_tests_for_mode(mode: super::BuildMode, program: &mut Program) {
    if mode == super::BuildMode::Production {
        program.fns.retain(|d| !d.test);
    }
}

// A ready module's per-artifact table lookup as a structured error, not a
// map-index panic. Readiness comes from the resolved key set, so a miss is a
// broken pass invariant that must surface as a diagnostic rather than abort.
fn missing_ready_artifact(module: &str, artifact: &str) -> Error {
    Error::ResolveModule(format!("ready module `{module}` is missing its {artifact}"))
}

/// One independently checked source module and its public cutoff artifact.
#[derive(Clone, Debug)]
pub struct CheckedModule {
    pub name: String,
    pub checked: Checked,
    pub interface: ModuleInterface,
    /// True when this checked body was rehydrated rather than typechecked now.
    pub reused: bool,
}

/// Result of checking a root through independently scheduled module queries.
#[derive(Clone, Debug)]
pub struct ModuleCheckReport {
    pub root: Checked,
    /// True when the root checked body was rehydrated from the durable store.
    pub root_reused: bool,
    pub modules: Vec<CheckedModule>,
    /// Deterministically ordered reuse/recompilation explanations.
    pub decisions: Vec<ModuleQueryDecision>,
}

struct ModuleJob {
    key: Option<String>,
    interface_key: Option<String>,
    body_key: Option<String>,
    name: String,
    entry: Program,
    resolved: Program,
    seed: TypecheckSeed,
    decision: DecisionTracker,
}

/// Typecheck a module DAG from dependency interfaces rather than merged bodies.
///
/// Independent ready modules run through the deterministic query scheduler. A
/// module-import cycle falls back to the existing whole-program checker: it is
/// semantically authoritative until checked bodies define an SCC module boundary.
/// Successful module queries are memoized in the command session by raw module bytes and dependency-interface
/// digests, so a private dependency edit cannot invalidate its importers.
///
/// # Errors
/// Fails on loading, resolution, malformed interface metadata, or any local
/// type error. A cyclic module graph is not an error here: it takes the
/// whole-program fallback documented above, and only that checker's own
/// failures surface.
pub fn check_modules_on(
    src: &str,
    roots: &[Root],
    cfg: &Config,
) -> Result<ModuleCheckReport, Error> {
    let mut root_entry = parse(src)?.program;
    let foundation = if src.starts_with(PRELUDE) {
        stdlib_typecheck_seed()?
    } else {
        injected_typecheck_seed()?
    };
    let foundation_identity = standard_foundation_identity(src);
    let mut loaded = load(&root_entry, roots)?;
    // Production neutrality: a project check must be byte-identical whether or not
    // any module carries `test fn` declarations, since a module's checked
    // interface digest feeds its importers and the durable module cache. Tests are
    // stripped from every loaded module and the root before their programs derive
    // the interface exports, the checked bodies, and the query keys. Only
    // `prism test` selects `BuildMode::Test`, which retains them so the harness can
    // check and run the test supplements. The single-file front does the same at
    // its own resolve boundary; both call [`strip_tests_for_mode`], so the two
    // production views cannot drift.
    strip_tests_for_mode(cfg.mode, &mut root_entry);
    for module in &mut loaded {
        strip_tests_for_mode(cfg.mode, &mut module.prog);
    }
    let shipped = embedded_std_modules(&loaded);
    let entries = loaded
        .iter()
        .map(|module| (module.path.join("."), module.prog.clone()))
        .collect::<BTreeMap<_, _>>();
    let sources = loaded
        .iter()
        .map(|module| (module.path.join("."), module.source.clone()))
        .collect::<BTreeMap<_, _>>();
    let dependencies = module_dependencies(&loaded, &shipped);
    let (mut root_resolved, resolved) = resolve_loaded_module_units(root_entry.clone(), loaded)?;
    let mut root_interface_entry = root_entry.clone();
    if src.starts_with(PRELUDE) {
        strip_prelude_declarations(&mut root_resolved, src);
        let imports = std::mem::take(&mut root_interface_entry.imports);
        strip_prelude_declarations(&mut root_interface_entry, src);
        root_interface_entry.imports = imports;
    }
    let resolved = resolved
        .into_iter()
        .map(|module| (module.path.join("."), module.prog))
        .collect::<BTreeMap<_, _>>();

    let mut pending = resolved
        .keys()
        .filter(|name| !shipped.contains(*name))
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut interfaces = BTreeMap::<String, ModuleInterface>::new();
    let mut checked_modules = BTreeMap::<String, CheckedModule>::new();
    let mut decisions = Vec::new();
    // Facts are buffered here and committed once, only after the whole DAG is
    // known acyclic. The import-cycle fallback returns before the commit, so no
    // per-module fact the empty report disowns can reach the durable ledger.
    let mut pending_facts: Vec<QueryFact> = Vec::new();
    while !pending.is_empty() {
        let ready = pending
            .iter()
            .filter(|name| {
                dependencies
                    .get(*name)
                    .is_none_or(|deps| deps.iter().all(|dep| interfaces.contains_key(dep)))
            })
            .cloned()
            .collect::<Vec<_>>();
        if ready.is_empty() {
            return Ok(ModuleCheckReport {
                root: super::check_on_in(src, roots, cfg)?,
                root_reused: false,
                modules: Vec::new(),
                decisions: Vec::new(),
            });
        }

        let mut jobs = Vec::new();
        for name in ready {
            let dep_names = dependencies.get(&name).cloned().unwrap_or_default();
            let deps = dep_names.iter();
            let source = sources
                .get(&name)
                .ok_or_else(|| missing_ready_artifact(&name, "source"))?;
            let decision = DecisionTracker::new(
                &name,
                source,
                dep_names.iter(),
                &interfaces,
                &foundation_identity,
                roots,
                cfg,
            )?;
            let key = module_query_key(
                &name,
                source,
                deps.clone(),
                &interfaces,
                &foundation_identity,
                cfg,
            )?;
            let interface_key = checked_interface_key(
                &name,
                source,
                deps.clone(),
                &interfaces,
                &foundation_identity,
                cfg,
            )?;
            let body_key = checked_body_key(
                &name,
                source,
                deps.clone(),
                &interfaces,
                &foundation_identity,
                cfg,
            )?;
            let seed = seeded_dependencies(deps.clone(), &interfaces, &foundation)?;
            if let Some(session) = &cfg.session {
                if let Some(mut module) = session.lookup_module(&key) {
                    module.reused = true;
                    session.record_hit();
                    pending.remove(&name);
                    let (module_decision, fact) = decision.finish(&module.interface.digest, true);
                    decisions.push(module_decision);
                    pending_facts.extend(fact);
                    interfaces.insert(name.clone(), module.interface.clone());
                    checked_modules.insert(name, module);
                    continue;
                }
                session.record_miss();
            }
            if let Some(cache) = DurableInterfaceCache::open(cfg)? {
                if let Some(module) = cache.load_body(&body_key, &name, &seed)? {
                    if let Some(session) = &cfg.session {
                        session.record_hit();
                        session.insert_module(key.clone(), module.clone());
                    }
                    pending.remove(&name);
                    let (module_decision, fact) = decision.finish(&module.interface.digest, true);
                    decisions.push(module_decision);
                    pending_facts.extend(fact);
                    interfaces.insert(name.clone(), module.interface.clone());
                    checked_modules.insert(name, module);
                    continue;
                }
                if let Some(interface) = cache.load(&interface_key)? {
                    if let Some(session) = &cfg.session {
                        session.record_hit();
                    }
                    pending.remove(&name);
                    let (module_decision, fact) = decision.finish(&interface.digest, true);
                    decisions.push(module_decision);
                    pending_facts.extend(fact);
                    interfaces.insert(name, interface);
                    continue;
                }
            }
            let entry = entries
                .get(&name)
                .ok_or_else(|| missing_ready_artifact(&name, "entry program"))?
                .clone();
            let resolved_program = resolved
                .get(&name)
                .ok_or_else(|| missing_ready_artifact(&name, "resolved program"))?
                .clone();
            jobs.push(ModuleJob {
                key: cfg.session.as_ref().map(|_| key),
                interface_key: durable_interface_key(cfg, interface_key),
                body_key: durable_interface_key(cfg, body_key),
                name: name.clone(),
                entry,
                resolved: resolved_program,
                seed,
                decision,
            });
        }
        let results =
            QueryScheduler::new(cfg.flags.query_threads).map_ordered(&jobs, check_module_job);
        for (job, result) in jobs.into_iter().zip(results) {
            let (module, body) = result?;
            if let (Some(session), Some(key)) = (&cfg.session, &job.key) {
                session.insert_module(key.clone(), module.clone());
                session.record_write();
            }
            if let Some(cache) = DurableInterfaceCache::open(cfg)? {
                if let Some(key) = &job.interface_key {
                    cache.store(key, &module.interface)?;
                }
                if let (Some(key), Some(body)) = (&job.body_key, body.as_ref()) {
                    cache.store_body(key, body)?;
                }
            }
            pending.remove(&module.name);
            let (module_decision, fact) = job.decision.finish(&module.interface.digest, false);
            decisions.push(module_decision);
            pending_facts.extend(fact);
            interfaces.insert(module.name.clone(), module.interface.clone());
            checked_modules.insert(module.name.clone(), module);
        }
    }

    let root_dependencies = root_entry
        .imports
        .iter()
        .map(|import| import.path.join("."))
        .filter(|name| !shipped.contains(name))
        .collect::<BTreeSet<_>>();
    let root_key = module_query_key(
        ROOT_MODULE_NAME,
        src,
        root_dependencies.iter(),
        &interfaces,
        &foundation_identity,
        cfg,
    )?;
    let root_interface_key = checked_interface_key(
        ROOT_MODULE_NAME,
        src,
        root_dependencies.iter(),
        &interfaces,
        &foundation_identity,
        cfg,
    )?;
    let root_body_key = checked_body_key(
        ROOT_MODULE_NAME,
        src,
        root_dependencies.iter(),
        &interfaces,
        &foundation_identity,
        cfg,
    )?;
    let root_seed = seeded_dependencies(root_dependencies.iter(), &interfaces, &foundation)?;
    let root_decision = DecisionTracker::new(
        ROOT_MODULE_NAME,
        src,
        root_dependencies.iter(),
        &interfaces,
        &foundation_identity,
        roots,
        cfg,
    )?;
    let (root, root_reused, root_interface) = if let Some(session) = &cfg.session {
        if let Some(module) = session.lookup_module(&root_key) {
            session.record_hit();
            (module.checked, true, module.interface.digest)
        } else {
            session.record_miss();
            if let Some(module) =
                load_cached_body(cfg, &root_body_key, ROOT_MODULE_NAME, &root_seed)?
            {
                session.record_hit();
                session.insert_module(root_key, module.clone());
                (module.checked, true, module.interface.digest)
            } else {
                let (module, body) =
                    check_root_job(&root_interface_entry, root_resolved, &root_seed)?;
                session.insert_module(root_key, module.clone());
                session.record_write();
                store_root_artifacts(
                    cfg,
                    &root_interface_key,
                    &root_body_key,
                    &module.interface,
                    body.as_ref(),
                )?;
                (module.checked, false, module.interface.digest)
            }
        }
    } else if let Some(module) =
        load_cached_body(cfg, &root_body_key, ROOT_MODULE_NAME, &root_seed)?
    {
        (module.checked, true, module.interface.digest)
    } else {
        let (module, body) = check_root_job(&root_interface_entry, root_resolved, &root_seed)?;
        store_root_artifacts(
            cfg,
            &root_interface_key,
            &root_body_key,
            &module.interface,
            body.as_ref(),
        )?;
        (module.checked, false, module.interface.digest)
    };
    let (root_module_decision, root_fact) = root_decision.finish(&root_interface, root_reused);
    decisions.push(root_module_decision);
    pending_facts.extend(root_fact);
    decisions.sort_by(|left, right| left.module.cmp(&right.module));
    // The DAG is acyclic (the cycle fallback returns earlier), so committing the
    // buffered facts now cannot leave the ledger describing a disowned result.
    persist_facts(roots, cfg, pending_facts)?;
    Ok(ModuleCheckReport {
        root,
        root_reused,
        modules: checked_modules.into_values().collect(),
        decisions,
    })
}

fn injected_typecheck_seed() -> Result<TypecheckSeed, Error> {
    static CACHE: OnceLock<TypecheckSeed> = OnceLock::new();
    if let Some(seed) = CACHE.get() {
        return Ok(seed.clone());
    }
    let program = desugar_with_scope(
        parse(INJECTED_FOUNDATION_SOURCE)?.program,
        &BTreeMap::new(),
        &BTreeMap::new(),
    )?;
    let checked = check_seeded(&program, &TypecheckSeed::default())?;
    let mut seed = TypecheckSeed::from_checked(&checked);
    let name = crate::sym::Sym::from(INJECTED_FOUNDATION_NAME);
    seed.env.remove(&name);
    seed.constrained.remove(&name);
    let _ = CACHE.set(seed.clone());
    Ok(CACHE.get().cloned().unwrap_or(seed))
}

fn strip_prelude_declarations(program: &mut Program, src: &str) {
    let prelude_end = crate::error::SourceMap::new(src).prelude_len();
    program.imports.clear();
    program
        .types
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .effects
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .errors
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .aliases
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .synonyms
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .classes
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .instances
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .stable
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .canonicals
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .patterns
        .retain(|declaration| declaration.span.start >= prelude_end);
    program
        .fns
        .retain(|declaration| declaration.span.start >= prelude_end);
    let declarations = program
        .fns
        .iter()
        .map(|declaration| declaration.name.clone())
        .chain(
            program
                .types
                .iter()
                .map(|declaration| declaration.name.clone()),
        )
        .chain(
            program
                .effects
                .iter()
                .map(|declaration| declaration.name.clone()),
        )
        .chain(
            program
                .classes
                .iter()
                .map(|declaration| declaration.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    program.exports.retain(|name| declarations.contains(name));
    program
        .opaques
        .retain(|name| program.exports.contains(name));
    program
        .deprecated
        .retain(|name, _| program.exports.contains(name));
}

fn desugar_scope(seed: &TypecheckSeed) -> (BTreeMap<String, String>, BTreeMap<String, String>) {
    let classes = seed
        .classes
        .keys()
        .map(|name| {
            (
                crate::names::bare_name(name.as_str()).to_string(),
                name.to_string(),
            )
        })
        .collect();
    let values = seed
        .env
        .keys()
        .map(|name| {
            (
                crate::names::bare_name(name.as_str()).to_string(),
                name.to_string(),
            )
        })
        .collect();
    (classes, values)
}

fn check_module_job(job: &ModuleJob) -> Result<(CheckedModule, Option<CheckedBody>), Error> {
    let (classes, values) = desugar_scope(&job.seed);
    let program = desugar_with_scope(job.resolved.clone(), &classes, &values)?;
    let checked = check_seeded(&program, &job.seed)?;
    let interface = module_interface_from_checked(&job.entry, Some(&job.name), &program, &checked)?;
    let body = CheckedBody::new(&job.entry, Some(&job.name), &program, &checked, &interface)?;
    Ok((
        CheckedModule {
            name: job.name.clone(),
            checked,
            interface,
            reused: false,
        },
        body,
    ))
}

fn check_root_job(
    entry: &Program,
    resolved: Program,
    seed: &TypecheckSeed,
) -> Result<(CheckedModule, Option<CheckedBody>), Error> {
    let (classes, values) = desugar_scope(seed);
    let program = desugar_with_scope(resolved, &classes, &values)?;
    let checked = check_seeded(&program, seed)?;
    let interface = module_interface_from_checked(entry, None, &program, &checked)?;
    let body = CheckedBody::new(entry, None, &program, &checked, &interface)?;
    Ok((
        CheckedModule {
            name: ROOT_MODULE_NAME.to_string(),
            checked,
            interface,
            reused: false,
        },
        body,
    ))
}

fn embedded_std_modules(modules: &[Module]) -> BTreeSet<String> {
    let embedded = crate::stdlib::STDLIB
        .iter()
        .map(|(name, source)| (*name, *source))
        .collect::<BTreeMap<_, _>>();
    modules
        .iter()
        .filter(|module| {
            embedded
                .get(module.path.join(".").as_str())
                .is_some_and(|source| **source == module.source)
        })
        .map(|module| module.path.join("."))
        .collect()
}

fn seeded_dependencies<I, S>(
    dependencies: I,
    interfaces: &BTreeMap<String, ModuleInterface>,
    foundation: &TypecheckSeed,
) -> Result<TypecheckSeed, Error>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let mut seed = foundation.clone();
    seed.extend(dependency_seed(dependencies, interfaces)?);
    Ok(seed)
}

fn module_dependencies(
    modules: &[Module],
    shipped: &BTreeSet<String>,
) -> BTreeMap<String, BTreeSet<String>> {
    let available = modules
        .iter()
        .map(|module| module.path.join("."))
        .filter(|name| !shipped.contains(name))
        .collect::<BTreeSet<_>>();
    modules
        .iter()
        .map(|module| {
            let dependencies = module
                .prog
                .imports
                .iter()
                .map(|import| import.path.join("."))
                .filter(|name| available.contains(name))
                .collect();
            (module.path.join("."), dependencies)
        })
        .collect()
}

fn standard_foundation_identity(src: &str) -> String {
    if !src.starts_with(PRELUDE) {
        return String::new();
    }
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, STANDARD_FOUNDATION_SCHEMA);
    field(&mut hasher, PRELUDE.as_bytes());
    for (name, source) in crate::stdlib::STDLIB {
        field(&mut hasher, name.as_bytes());
        field(&mut hasher, source.as_bytes());
    }
    hasher.finalize().to_hex().to_string()
}

#[derive(Clone, Serialize, Deserialize)]
struct CheckedBody {
    format: String,
    public_interface: ModuleInterface,
    seed_interface: ModuleInterface,
    decls: Vec<DeclWire>,
    facts: String,
    seeds: u32,
    digest: String,
}

#[derive(Clone, Serialize, Deserialize)]
struct DeclWire {
    name: String,
    params: Vec<String>,
    ty: String,
    effects: Vec<String>,
}

#[derive(Serialize)]
struct CheckedBodyPayload<'a> {
    format: &'a str,
    public_interface: &'a ModuleInterface,
    seed_interface: &'a ModuleInterface,
    decls: &'a [DeclWire],
    facts: &'a str,
    seeds: u32,
}

fn body_is_surface_rehydratable(decls: &[DeclWire], facts: &str) -> bool {
    decls.iter().all(|decl| !decl.ty.contains('?')) && !facts.contains('?')
}

impl CheckedBody {
    fn new(
        entry: &Program,
        module_path: Option<&str>,
        program: &Program<CorePhase>,
        checked: &Checked,
        public_interface: &ModuleInterface,
    ) -> Result<Option<Self>, Error> {
        if !checked.warnings.is_empty() {
            return Ok(None);
        }
        let mut body_entry = entry.clone();
        body_entry.exports = program
            .fns
            .iter()
            .map(|declaration| crate::names::bare_name(&declaration.name).to_string())
            .chain(
                program
                    .types
                    .iter()
                    .map(|declaration| crate::names::bare_name(&declaration.name).to_string()),
            )
            .chain(
                program
                    .effects
                    .iter()
                    .map(|declaration| crate::names::bare_name(&declaration.name).to_string()),
            )
            .chain(
                program
                    .classes
                    .iter()
                    .map(|declaration| crate::names::bare_name(&declaration.name).to_string()),
            )
            .filter(|name| {
                name != crate::names::FAIL_OP
                    && name != crate::names::FAIL_EFFECT
                    && name != crate::names::BREAK_EFFECT
                    && name != crate::names::CONTINUE_EFFECT
                    && name != crate::names::RETURN_EFFECT
            })
            .collect();
        body_entry.opaques.clear();
        let seed_interface =
            module_interface_from_checked(&body_entry, module_path, program, checked)?;
        let decls = checked
            .decls
            .iter()
            .filter(|decl| crate::names::bare_name(&decl.name) != crate::names::FAIL_OP)
            .map(|decl| {
                let mut effects = decl
                    .effects
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                effects.sort();
                DeclWire {
                    name: decl.name.clone(),
                    params: decl.params.clone(),
                    ty: decl.ty.show(),
                    effects,
                }
            })
            .collect::<Vec<_>>();
        // Private inferred helpers can retain an open row meta in either their
        // declaration or a HIR node fact after the public interface is closed.
        // The checked-body wire format is a rehydratable artifact, not a debug
        // dump: skip this optional cache until both are surface-parseable. The
        // interface cache remains usable and the module is checked again next
        // build.
        let facts = checked
            .facts
            .to_json()
            .map_err(|error| Error::ResolveModule(format!("serialize checked HIR: {error}")))?;
        if !body_is_surface_rehydratable(&decls, &facts) {
            return Ok(None);
        }
        let digest = checked_body_digest(
            public_interface,
            &seed_interface,
            &decls,
            &facts,
            checked.seeds,
        )?;
        Ok(Some(Self {
            format: CHECKED_BODY_FORMAT.to_string(),
            public_interface: public_interface.clone(),
            seed_interface,
            decls,
            facts,
            seeds: checked.seeds,
            digest,
        }))
    }

    fn into_checked(self, base: &TypecheckSeed) -> Result<(Checked, ModuleInterface), Error> {
        if self.format != CHECKED_BODY_FORMAT {
            return Err(Error::ResolveModule(format!(
                "unsupported checked body format {:?}",
                self.format
            )));
        }
        let derived = checked_body_digest(
            &self.public_interface,
            &self.seed_interface,
            &self.decls,
            &self.facts,
            self.seeds,
        )?;
        if self.digest != derived {
            return Err(Error::ResolveModule(format!(
                "checked body digest is {}, derived {derived}",
                self.digest
            )));
        }
        let mut seed = base.clone();
        seed.extend(
            self.seed_interface
                .rehydrate()
                .map_err(Error::ResolveModule)?
                .typecheck_seed(),
        );
        let decls = self
            .decls
            .into_iter()
            .map(|decl| {
                Ok(DeclInfo {
                    name: decl.name.clone(),
                    params: decl.params,
                    ty: crate::tc::parse_checked_signature(&decl.name, &decl.ty)
                        .map_err(|error| Error::ResolveModule(error.to_string()))?,
                    effects: decl
                        .effects
                        .into_iter()
                        .map(crate::sym::Sym::from)
                        .collect(),
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let facts = NodeFacts::from_json(&self.facts).map_err(Error::ResolveModule)?;
        let checked = Checked {
            env: seed.env,
            data: seed.data,
            ctors: seed.ctors,
            decls,
            eff_ops: seed.eff_ops,
            facts,
            classes: seed.classes,
            instances: seed.instances,
            inst_keys: seed.inst_keys,
            canonical: seed.canonical,
            methods: seed.methods,
            constrained: seed.constrained,
            seeds: self.seeds,
            warnings: Vec::new(),
            holes: Vec::new(),
        };
        Ok((checked, self.public_interface))
    }
}

fn checked_body_digest(
    public_interface: &ModuleInterface,
    seed_interface: &ModuleInterface,
    decls: &[DeclWire],
    facts: &str,
    seeds: u32,
) -> Result<String, Error> {
    let bytes = serde_json::to_vec(&CheckedBodyPayload {
        format: CHECKED_BODY_FORMAT,
        public_interface,
        seed_interface,
        decls,
        facts,
        seeds,
    })
    .map_err(|error| Error::ResolveModule(format!("serialize checked body: {error}")))?;
    Ok(blake3::hash(&bytes).to_hex().to_string())
}

struct DurableInterfaceCache {
    store: Store,
}

impl DurableInterfaceCache {
    fn open(cfg: &Config) -> Result<Option<Self>, Error> {
        if !cache_enabled(cfg) {
            return Ok(None);
        }
        Ok(Some(Self {
            store: Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?,
        }))
    }

    fn load(&self, key: &str) -> Result<Option<ModuleInterface>, Error> {
        let Some(output) = self.store.get_query(CHECKED_INTERFACE_QUERY, key)? else {
            return Ok(None);
        };
        let bytes = self.store.get(&output)?;
        let actual = blake3::hash(&bytes).to_hex().to_string();
        if actual != output {
            return Err(Error::ResolveModule(format!(
                "checked interface object hashes to {actual}, expected {output}"
            )));
        }
        let text = std::str::from_utf8(&bytes).map_err(|error| {
            Error::ResolveModule(format!("checked interface is not UTF-8: {error}"))
        })?;
        let interface = ModuleInterface::from_json(text).map_err(Error::ResolveModule)?;
        interface.rehydrate().map_err(Error::ResolveModule)?;
        Ok(Some(interface))
    }

    fn load_body(
        &self,
        key: &str,
        name: &str,
        seed: &TypecheckSeed,
    ) -> Result<Option<CheckedModule>, Error> {
        let Some(output) = self.store.get_query(CHECKED_BODY_QUERY, key)? else {
            return Ok(None);
        };
        let bytes = self.store.get(&output)?;
        let actual = blake3::hash(&bytes).to_hex().to_string();
        if actual != output {
            return Err(Error::ResolveModule(format!(
                "checked body object hashes to {actual}, expected {output}"
            )));
        }
        let body: CheckedBody = serde_json::from_slice(&bytes)
            .map_err(|error| Error::ResolveModule(format!("decode checked body: {error}")))?;
        let (checked, interface) = body.into_checked(seed)?;
        Ok(Some(CheckedModule {
            name: name.to_string(),
            checked,
            interface,
            reused: true,
        }))
    }

    fn store_body(&self, key: &str, body: &CheckedBody) -> Result<(), Error> {
        let bytes = serde_json::to_vec(body)
            .map_err(|error| Error::ResolveModule(format!("serialize checked body: {error}")))?;
        let output = blake3::hash(&bytes).to_hex().to_string();
        match self.store.put(&output, &bytes)? {
            Written::New | Written::Hit => {}
        }
        self.store.put_query(CHECKED_BODY_QUERY, key, &output)?;
        Ok(())
    }

    fn store(&self, key: &str, interface: &ModuleInterface) -> Result<(), Error> {
        let bytes = interface
            .to_json()
            .map_err(|error| Error::ResolveModule(format!("serialize checked interface: {error}")))?
            .into_bytes();
        let output = blake3::hash(&bytes).to_hex().to_string();
        match self.store.put(&output, &bytes)? {
            Written::New | Written::Hit => {}
        }
        self.store
            .put_query(CHECKED_INTERFACE_QUERY, key, &output)?;
        Ok(())
    }
}

fn durable_interface_key(cfg: &Config, key: String) -> Option<String> {
    (cfg.flags.compiler_cache && !cfg.flags.store).then_some(key)
}

fn load_cached_body(
    cfg: &Config,
    key: &str,
    name: &str,
    seed: &TypecheckSeed,
) -> Result<Option<CheckedModule>, Error> {
    let Some(cache) = DurableInterfaceCache::open(cfg)? else {
        return Ok(None);
    };
    cache.load_body(key, name, seed)
}

fn store_root_artifacts(
    cfg: &Config,
    interface_key: &str,
    body_key: &str,
    interface: &ModuleInterface,
    body: Option<&CheckedBody>,
) -> Result<(), Error> {
    let Some(cache) = DurableInterfaceCache::open(cfg)? else {
        return Ok(());
    };
    cache.store(interface_key, interface)?;
    if let Some(body) = body {
        cache.store_body(body_key, body)?;
    }
    Ok(())
}

fn checked_body_key<'a>(
    name: &str,
    source: &str,
    dependencies: impl IntoIterator<Item = &'a String>,
    interfaces: &BTreeMap<String, ModuleInterface>,
    foundation_identity: &str,
    cfg: &Config,
) -> Result<String, Error> {
    query_key(
        CHECKED_BODY_QUERY_SCHEMA,
        name,
        source,
        dependencies,
        interfaces,
        foundation_identity,
        cfg,
    )
}

fn checked_interface_key<'a>(
    name: &str,
    source: &str,
    dependencies: impl IntoIterator<Item = &'a String>,
    interfaces: &BTreeMap<String, ModuleInterface>,
    foundation_identity: &str,
    cfg: &Config,
) -> Result<String, Error> {
    query_key(
        CHECKED_INTERFACE_QUERY_SCHEMA,
        name,
        source,
        dependencies,
        interfaces,
        foundation_identity,
        cfg,
    )
}

fn module_query_key<'a>(
    name: &str,
    source: &str,
    dependencies: impl IntoIterator<Item = &'a String>,
    interfaces: &BTreeMap<String, ModuleInterface>,
    foundation_identity: &str,
    cfg: &Config,
) -> Result<String, Error> {
    query_key(
        MODULE_CHECK_QUERY_SCHEMA,
        name,
        source,
        dependencies,
        interfaces,
        foundation_identity,
        cfg,
    )
}

fn query_key<'a>(
    schema: &[u8],
    name: &str,
    source: &str,
    dependencies: impl IntoIterator<Item = &'a String>,
    interfaces: &BTreeMap<String, ModuleInterface>,
    foundation_identity: &str,
    cfg: &Config,
) -> Result<String, Error> {
    let mut hasher = blake3::Hasher::new();
    field(&mut hasher, schema);
    field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
    field(&mut hasher, foundation_identity.as_bytes());
    field(&mut hasher, name.as_bytes());
    field(&mut hasher, source.as_bytes());
    field(
        &mut hasher,
        cfg.artifact_identity_for("module-check")
            .fingerprint()
            .as_bytes(),
    );
    for dependency in dependencies {
        let interface = interfaces.get(dependency).ok_or_else(|| {
            Error::ResolveModule(format!(
                "missing checked interface for module `{dependency}`"
            ))
        })?;
        field(&mut hasher, dependency.as_bytes());
        field(&mut hasher, interface.digest.as_bytes());
    }
    Ok(hasher.finalize().to_hex().to_string())
}

fn dependency_seed<I, S>(
    dependencies: I,
    interfaces: &BTreeMap<String, ModuleInterface>,
) -> Result<TypecheckSeed, Error>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let mut seed = TypecheckSeed::default();
    for dependency in dependencies {
        let dependency = dependency.as_ref();
        let interface = interfaces.get(dependency).ok_or_else(|| {
            Error::ResolveModule(format!(
                "missing checked interface for module `{dependency}`"
            ))
        })?;
        seed.extend(
            interface
                .rehydrate()
                .map_err(Error::ResolveModule)?
                .typecheck_seed(),
        );
    }
    Ok(seed)
}

#[cfg(test)]
mod checked_body_tests {
    use super::{body_is_surface_rehydratable, DeclWire};

    use std::slice::from_ref;

    #[test]
    fn unresolved_type_metavariables_are_not_surface_rehydratable() {
        let closed = DeclWire {
            name: "closed".to_string(),
            params: Vec::new(),
            ty: "() -> Int ! {}".to_string(),
            effects: Vec::new(),
        };
        let open = DeclWire {
            name: "open".to_string(),
            params: Vec::new(),
            ty: "() -> Int ! {?r3}".to_string(),
            effects: Vec::new(),
        };
        assert!(body_is_surface_rehydratable(from_ref(&closed), "[]"));
        assert!(!body_is_surface_rehydratable(&[open], "[]"));
        assert!(!body_is_surface_rehydratable(
            &[closed],
            r#"[{"ty":"() -> Int ! {?r3}"}]"#,
        ));
    }
}
