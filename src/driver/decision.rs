//! The module-query decision boundary: each module check records one
//! [`QueryFact`] into the workspace's persisted fact ledger and explains a
//! recompilation by diffing that fact against the previous recording.
//!
//! The fact carries the module query's ordered semantic inputs (compiler,
//! configuration, semantic foundation, token and byte source identities, and
//! each dependency's interface digest), the produced interface digest as its
//! output identity, and the hit/miss/write/cutoff outcome. Reasons are derived
//! from the previous/current input alignment, so the explanation persisted with
//! the fact equals the one a later offline graph diff reproduces.

use std::collections::BTreeMap;

use crate::error::Error;
use crate::lineage::{
    changed_inputs, outcome_of, record_fact, FactInput, FactLedger, FactScope, InputDelta,
    QueryFact, QueryKind,
};
use crate::resolve::Root;
use crate::store::disk::{resolve_store_path, Store};

use super::identity::{compiler_binary_fingerprint, ModuleInterface};
use super::input::semantic_source_digest;
use super::Config;

// Canonical module-query input slot names, in recording order. One home; the
// dependency prefix has a tested inverse below, never re-parsed elsewhere.
const INPUT_COMPILER: &str = "compiler";
const INPUT_CONFIGURATION: &str = "configuration";
const INPUT_FOUNDATION: &str = "foundation";
const INPUT_SEMANTIC_SOURCE: &str = "semantic-source";
const INPUT_SOURCE: &str = "source";
const DEPENDENCY_INPUT_PREFIX: &str = "dependency:";
// The configuration context the module checker keys its artifact identity on.
const MODULE_CHECK_CONTEXT: &str = "module-check";

fn dependency_input(name: &str) -> String {
    format!("{DEPENDENCY_INPUT_PREFIX}{name}")
}

fn dependency_name_of(input: &str) -> Option<&str> {
    input.strip_prefix(DEPENDENCY_INPUT_PREFIX)
}

/// Explanation of one module query observed during the current command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleQueryDecision {
    pub module: String,
    pub reused: bool,
    pub reasons: Vec<String>,
}

pub(super) struct DecisionTracker {
    store: Option<Store>,
    scope: FactScope,
    previous: Option<QueryFact>,
    module: String,
    inputs: Vec<FactInput>,
}

impl DecisionTracker {
    pub(super) fn new<'a>(
        module: &str,
        source: &str,
        dependencies: impl IntoIterator<Item = &'a String>,
        interfaces: &BTreeMap<String, ModuleInterface>,
        foundation: &str,
        roots: &[Root],
        cfg: &Config,
    ) -> Result<Self, Error> {
        let mut inputs = vec![
            FactInput {
                name: INPUT_COMPILER.to_string(),
                identity: compiler_binary_fingerprint()?.to_string(),
            },
            FactInput {
                name: INPUT_CONFIGURATION.to_string(),
                identity: cfg
                    .artifact_identity_for(MODULE_CHECK_CONTEXT)
                    .fingerprint(),
            },
            FactInput {
                name: INPUT_FOUNDATION.to_string(),
                identity: foundation.to_string(),
            },
            FactInput {
                name: INPUT_SEMANTIC_SOURCE.to_string(),
                identity: semantic_source_digest(source)?,
            },
            FactInput {
                name: INPUT_SOURCE.to_string(),
                identity: blake3::hash(source.as_bytes()).to_hex().to_string(),
            },
        ];
        // Name-sorted dependency slots, so the input order is a pure function
        // of the dependency set.
        let dependencies: BTreeMap<&String, &ModuleInterface> = dependencies
            .into_iter()
            .map(|name| (name, &interfaces[name]))
            .collect();
        for (name, interface) in dependencies {
            inputs.push(FactInput {
                name: dependency_input(name),
                identity: interface.digest.clone(),
            });
        }
        let scope = FactScope::of_roots(roots);
        let store = if cfg.flags.compiler_cache && !cfg.flags.store {
            Some(Store::open_or_create(resolve_store_path(
                cfg.flags.store_path.as_deref(),
            ))?)
        } else {
            None
        };
        let previous = match &store {
            Some(store) => FactLedger::load(store, &scope)?
                .current
                .get(QueryKind::Module, module)
                .cloned(),
            None => None,
        };
        Ok(Self {
            store,
            scope,
            previous,
            module: module.to_string(),
            inputs,
        })
    }

    pub(super) fn finish(
        self,
        interface: &str,
        reused: bool,
    ) -> Result<ModuleQueryDecision, Error> {
        let outcome = outcome_of(self.previous.as_ref(), Some(interface), reused);
        let mut fact = QueryFact {
            kind: QueryKind::Module,
            identity: self.module,
            inputs: self.inputs,
            output: Some(interface.to_string()),
            outcome,
            reasons: Vec::new(),
        };
        if !reused {
            fact.reasons = module_reasons(self.previous.as_ref(), &fact);
        }
        if let Some(store) = &self.store {
            record_fact(store, &self.scope, fact.clone())?;
        }
        Ok(ModuleQueryDecision {
            module: fact.identity,
            reused,
            reasons: fact.reasons,
        })
    }
}

// The module-specific phrasing of a previous/current fact alignment. The same
// derivation fills the persisted fact's reason data and reproduces offline.
fn module_reasons(previous: Option<&QueryFact>, current: &QueryFact) -> Vec<String> {
    let Some(previous) = previous else {
        return vec!["no previous successful module query".to_string()];
    };
    let changes = changed_inputs(previous, current);
    let tokens_changed = changes
        .iter()
        .any(|change| change.name == INPUT_SEMANTIC_SOURCE);
    let mut reasons = Vec::new();
    for change in &changes {
        let reason = match change.name.as_str() {
            INPUT_COMPILER => Some("compiler executable changed".to_string()),
            INPUT_CONFIGURATION => Some("compiler configuration changed".to_string()),
            INPUT_FOUNDATION => Some("semantic foundation changed".to_string()),
            INPUT_SEMANTIC_SOURCE => Some("module tokens changed".to_string()),
            INPUT_SOURCE => {
                (!tokens_changed).then(|| "source bytes changed without token changes".to_string())
            }
            name => dependency_name_of(name).map(|dep| match change.delta {
                InputDelta::Added => format!("dependency `{dep}` was added"),
                InputDelta::Removed => format!("dependency `{dep}` was removed"),
                InputDelta::Changed => format!("dependency interface `{dep}` changed"),
            }),
        };
        if let Some(reason) = reason {
            reasons.push(reason);
        }
    }
    if reasons.is_empty() {
        reasons.push("query artifact was absent or rejected".to_string());
    }
    if previous
        .output
        .as_deref()
        .is_some_and(|output| !output.is_empty())
        && previous.output == current.output
    {
        reasons.push("public interface remained unchanged".to_string());
    }
    reasons
}

#[cfg(test)]
mod tests {
    use super::{dependency_input, dependency_name_of};

    // The dependency slot prefix must round-trip: it is the one string shared
    // between fact recording and reason phrasing.
    #[test]
    fn dependency_input_name_round_trips() {
        let input = dependency_input("Data.List");
        assert_eq!(dependency_name_of(&input), Some("Data.List"));
        assert_eq!(dependency_name_of("source"), None);
    }
}
