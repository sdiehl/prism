//! Entry-point closure over the checked surface program.
//!
//! A root program with a `main` reaches only part of the prelude and of the
//! modules it imports. The checker still judges the whole program (its
//! diagnostics and interface facts stay complete), but everything the entry
//! point cannot reach is dropped here, before elaboration, so the elaborator,
//! the validators, the identity hash, and the mid-end see only definitions
//! that can execute. The pre-optimizer reachability cut on Core does the same
//! job after elaboration; this pass moves that boundary in front of it for the
//! executable presets.
//!
//! Liveness is read from checked facts rather than from names alone:
//!
//! - a `Var` occurrence names a top-level function or constant;
//! - the per-node dictionary evidence names every instance dictionary a
//!   constrained use site or an operator resolves to, with its context and
//!   superclass dictionaries;
//! - an index or indexed assignment reaches the accessor the receiver's
//!   checked type selects, the same fact the elaborator dispatches on;
//! - a live instance reaches its method bodies.
//!
//! Root-file definitions and instances are always kept (the user's namespace is
//! the compile's subject, reached or not), as are every type, effect, class,
//! alias, and canonical declaration. The one prelude helper the elaborator
//! names with neither a surface occurrence nor a type to dispatch on (the
//! string escaper behind structural printing) is a root as well.

use std::collections::{BTreeMap, BTreeSet};

use crate::names::{module_of, ENTRY_POINT, STR_ESCAPE_FN};
use crate::syntax::ast::{Core as CorePhase, Decl, Expr, InstanceDecl, Program, S};
use crate::types::{Checked, Dict};
use crate::wired::Indexable;

// Prelude functions the elaborator calls by name with no surface occurrence
// and no receiver type to select them.
const ELABORATOR_ROOTS: &[&str] = &[STR_ESCAPE_FN];

/// Drop every imported or prelude definition the root program cannot reach.
///
/// A program without a root `main` is returned unchanged: a library module, a
/// REPL session, or a test-only file has no single entry to close over.
pub(super) fn entry_closure(
    mut program: Program<CorePhase>,
    checked: &Checked,
) -> Program<CorePhase> {
    let prelude_end = program.prelude_end;
    // Root-file definitions keep bare names (the root is the empty-path module)
    // and sit past the prepended prelude; imported ones carry a module path.
    let root_fn =
        |d: &Decl<CorePhase>| module_of(&d.name).is_empty() && d.span.start >= prelude_end;
    let root_instance =
        |i: &InstanceDecl<CorePhase>| i.module.is_empty() && i.span.start >= prelude_end;
    if !program
        .fns
        .iter()
        .any(|d| d.name == ENTRY_POINT && root_fn(d))
    {
        return program;
    }
    let (fns, instances) = {
        let mut live = Liveness::new(&program, checked);
        for d in program.fns.iter().filter(|d| root_fn(d)) {
            live.reach_fn(d);
        }
        for name in ELABORATOR_ROOTS {
            live.reach_fn_named(name);
        }
        for i in program.instances.iter().filter(|i| root_instance(i)) {
            live.reach_instance(i);
        }
        live.run()
    };
    program.fns.retain(|d| root_fn(d) || fns.contains(&d.name));
    program
        .instances
        .retain(|i| root_instance(i) || instances.contains(&i.name));
    program
}

struct Liveness<'a> {
    fns: BTreeMap<&'a str, &'a Decl<CorePhase>>,
    instances: BTreeMap<&'a str, &'a InstanceDecl<CorePhase>>,
    checked: &'a Checked,
    live_fns: BTreeSet<&'a str>,
    live_instances: BTreeSet<&'a str>,
    work: Vec<&'a S<Expr<CorePhase>>>,
}

impl<'a> Liveness<'a> {
    fn new(program: &'a Program<CorePhase>, checked: &'a Checked) -> Self {
        Self {
            fns: program.fns.iter().map(|d| (d.name.as_str(), d)).collect(),
            instances: program
                .instances
                .iter()
                .map(|i| (i.name.as_str(), i))
                .collect(),
            checked,
            live_fns: BTreeSet::new(),
            live_instances: BTreeSet::new(),
            work: Vec::new(),
        }
    }

    fn reach_fn(&mut self, d: &'a Decl<CorePhase>) {
        if self.live_fns.insert(d.name.as_str()) {
            self.push_decl(d);
        }
    }

    fn reach_fn_named(&mut self, name: &str) {
        if let Some(d) = self.fns.get(name).copied() {
            self.reach_fn(d);
        }
    }

    fn reach_instance(&mut self, i: &'a InstanceDecl<CorePhase>) {
        if self.live_instances.insert(i.name.as_str()) {
            for m in &i.methods {
                self.push_decl(m);
            }
        }
    }

    // Every expression a declaration owns, including its verification clauses:
    // a function the contracts alone mention stays available to the prover.
    fn push_decl(&mut self, d: &'a Decl<CorePhase>) {
        self.work.push(&d.body);
        self.work.extend(d.wheres.iter().map(|(_, e)| e));
        self.work.extend(d.requires.iter());
        self.work.extend(d.ensures.iter().map(|(_, e)| e));
        self.work.extend(d.decreases.iter());
    }

    // The container an index-sugar receiver was checked at, if any.
    fn indexable(&self, recv: &S<Expr<CorePhase>>) -> Option<Indexable> {
        self.checked
            .facts
            .node_type(recv.id)
            .and_then(Indexable::classify)
    }

    fn reach_dict(&mut self, dict: &Dict) {
        match dict {
            Dict::Global(name, context) => {
                if let Some(i) = self.instances.get(name.as_str()).copied() {
                    self.reach_instance(i);
                }
                for d in context {
                    self.reach_dict(d);
                }
            }
            Dict::Super(inner, _, _) => self.reach_dict(inner),
            Dict::Tuple(parts) => {
                for d in parts {
                    self.reach_dict(d);
                }
            }
            Dict::Param(_) => {}
        }
    }

    fn run(mut self) -> (BTreeSet<String>, BTreeSet<String>) {
        while let Some(e) = self.work.pop() {
            match &e.node {
                Expr::Var(name) => self.reach_fn_named(name),
                Expr::Index(recv, _) => {
                    if let Some(kind) = self.indexable(recv) {
                        self.reach_fn_named(kind.getter());
                    }
                }
                Expr::IndexSet(recv, _, _) => {
                    if let Some(name) = self.indexable(recv).and_then(Indexable::setter) {
                        self.reach_fn_named(name);
                    }
                }
                _ => {}
            }
            if let Some(dicts) = self.checked.facts.evidence(e.id) {
                for d in dicts {
                    self.reach_dict(d);
                }
            }
            e.node.each_child(&mut |child| self.work.push(child));
        }
        (
            self.live_fns.iter().map(ToString::to_string).collect(),
            self.live_instances
                .iter()
                .map(ToString::to_string)
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::super::front::{run_front, FrontRequest};
    use super::super::{with_prelude, Config};
    use crate::names::{ENTRY_POINT, STR_ESCAPE_FN};
    use crate::resolve::Root;
    use crate::stdlib::STDLIB;
    use crate::syntax::ast::{Core as CorePhase, Program};
    use crate::types::Checked;
    use crate::wired::Indexable;

    const SHOW_CLASS: &str = "Show";

    fn full_front(src: &str) -> (Program<CorePhase>, Checked) {
        let (program, checked, _, _, _) = run_front(
            &with_prelude(src),
            &[Root::Embedded(STDLIB)],
            &Config::default(),
            FrontRequest::Full,
        )
        .expect("full front")
        .into_typed_pre();
        (program, checked)
    }

    fn names(program: &Program<CorePhase>) -> BTreeSet<&str> {
        program.fns.iter().map(|d| d.name.as_str()).collect()
    }

    #[test]
    fn main_keeps_only_its_closure() {
        let (program, checked) = full_front("fn main() = println(\"hello\")\n");
        let kept = names(&program);
        assert!(kept.contains(ENTRY_POINT));
        assert!(kept.contains(STR_ESCAPE_FN));
        assert!(
            program.fns.len() * 4 < checked.defs.decls.len(),
            "{} of {} definitions kept",
            program.fns.len(),
            checked.defs.decls.len()
        );
    }

    #[test]
    fn root_definitions_survive_unreached() {
        let (program, _) =
            full_front("fn unused(x : Int) : Int = x + 1\nfn main() = println(\"hello\")\n");
        assert!(names(&program).contains("unused"));
    }

    #[test]
    fn index_sugar_keeps_the_receivers_accessor() {
        let (program, _) = full_front(
            "fn main() : Unit ! {IO} =\n  let xs = [1, 2, 3]\n  println(show(xs[1] ?? 0))\n",
        );
        assert!(names(&program).contains(Indexable::List.getter()));
    }

    #[test]
    fn a_program_without_main_is_left_whole() {
        let (program, checked) = full_front("fn helper(x : Int) : Int = x + 1\n");
        assert_eq!(program.fns.len(), checked.defs.decls.len());
    }

    #[test]
    fn dictionary_evidence_keeps_dispatched_instances() {
        let whole = full_front("fn helper(x : Int) : Int = x + 1\n")
            .0
            .instances
            .len();
        let (program, _) = full_front("fn main() = println(show([1, 2, 3]))\n");
        assert!(program.instances.iter().any(|i| i.class == SHOW_CLASS));
        assert!(program.instances.len() < whole);
    }
}
