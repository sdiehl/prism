//! Call-graph dependency analysis over `prog.fns`: the strongly-connected
//! components that order type inference, and the self-recursion test that gates
//! the polymorphic-recursion hint. This is structural (who references whom), not
//! an effect analysis: effect rows are discovered by principal inference, so the
//! old syntactic effect set-pass that once lived here is gone.

use crate::syntax::ast::{Core, Decl, Expr, HandlerArm, Pattern, Program, S};

/// The strongly-connected components of `prog.fns`'s call graph, in dependency
/// order (every component a callee belongs to precedes the components that call
/// it). Each component is a recursion group: a singleton for an acyclic
/// definition (with a self-edge for self-recursion), or several members for a
/// mutually recursive cluster. Checking a component only after its callees lets
/// a forward reference (notably one into a stdlib module merged after the
/// prelude) see a generalized type rather than a structure-free stub, and lets a
/// mutually recursive group be inferred against shared monomorphic variables.
///
/// Members within a component are returned in declaration order. References are
/// collected with lexical scope: a name bound by a parameter, lambda, `let`,
/// match pattern, or handler clause shadows the same-named top-level function, so
/// it is not a dependency. This matters for principal inference, not just
/// performance: a spurious edge would merge a callee into its caller's component,
/// switching it from generalize-then-instantiate to monomorphic mutual recursion
/// and so changing the inferred (effect) type.
#[must_use]
pub(crate) fn dep_sccs(prog: &Program<Core>) -> Vec<Vec<usize>> {
    let names: std::collections::BTreeMap<&str, usize> = prog
        .fns
        .iter()
        .enumerate()
        .map(|(i, d)| (d.name.as_str(), i))
        .collect();
    // Callee indices per function, deduped and in increasing order so the shared
    // Tarjan walks them deterministically. It returns the components callee-first.
    let deps: Vec<Vec<usize>> = prog
        .fns
        .iter()
        .map(|d| {
            let mut refs = std::collections::BTreeSet::new();
            // Seed the in-scope names with this function's own parameters: a
            // reference that a parameter shadows resolves to the parameter, not
            // the same-named top-level function.
            let mut bound: Vec<&str> = d.params.iter().map(|p| p.name.as_str()).collect();
            collect_refs(&d.body, &names, &mut bound, &mut refs);
            refs.into_iter().collect()
        })
        .collect();
    crate::scc::tarjan_scc(&deps)
}

/// Whether a declaration's body refers to its own name: direct self-recursion,
/// i.e. a singleton strongly-connected component with a self-edge. Used only to
/// decide whether a body's type error warrants the polymorphic-recursion remedy
/// hint. A parameter that shadows the function's own name is not a recursive
/// call, so the parameters seed the in-scope names here too.
#[must_use]
pub(crate) fn is_self_recursive(d: &Decl<Core>) -> bool {
    let names: std::collections::BTreeMap<&str, usize> =
        std::iter::once((d.name.as_str(), 0)).collect();
    let mut refs = std::collections::BTreeSet::new();
    let mut bound: Vec<&str> = d.params.iter().map(|p| p.name.as_str()).collect();
    collect_refs(&d.body, &names, &mut bound, &mut refs);
    !refs.is_empty()
}

// Every top-level function `e` references, by canonical name, respecting lexical
// scope: `bound` is the stack of names in scope at `e` (callers seed it with the
// enclosing function's parameters), and a reference to a bound name is skipped
// because it resolves to that local binding, not the same-named top-level
// function. Constructors, effect ops, and builtins are not in `names`, so they
// fall out regardless.
fn collect_refs<'a>(
    e: &'a S<Expr<Core>>,
    names: &std::collections::BTreeMap<&str, usize>,
    bound: &mut Vec<&'a str>,
    out: &mut std::collections::BTreeSet<usize>,
) {
    match &e.node {
        Expr::Var(n) => {
            if !bound.contains(&n.as_str()) {
                if let Some(&i) = names.get(n.as_str()) {
                    out.insert(i);
                }
            }
        }
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Str(_) => {}
        Expr::Bin(_, a, b) | Expr::Index(a, b) | Expr::Pipe(a, b) => {
            collect_refs(a, names, bound, out);
            collect_refs(b, names, bound, out);
        }
        Expr::If(c, t, e2) => {
            collect_refs(c, names, bound, out);
            collect_refs(t, names, bound, out);
            collect_refs(e2, names, bound, out);
        }
        // Non-recursive `let`: the binder scopes over the body only, not its value.
        Expr::Let(name, v, b) => {
            collect_refs(v, names, bound, out);
            bound.push(name.as_str());
            collect_refs(b, names, bound, out);
            bound.pop();
        }
        Expr::Lam(params, b) => {
            let base = bound.len();
            bound.extend(params.iter().map(|p| p.name.as_str()));
            collect_refs(b, names, bound, out);
            bound.truncate(base);
        }
        Expr::FieldAccess(b, _)
        | Expr::Inst(b, _)
        | Expr::Ann(b, _)
        | Expr::Mask(_, b)
        | Expr::Neg(b) => {
            collect_refs(b, names, bound, out);
        }
        Expr::Call(f, args) => {
            collect_refs(f, names, bound, out);
            for a in args {
                collect_refs(a, names, bound, out);
            }
        }
        Expr::Match(s, arms) => {
            collect_refs(s, names, bound, out);
            for arm in arms {
                let base = bound.len();
                collect_pat_binders(&arm.pat, bound);
                if let Some(g) = &arm.guard {
                    collect_refs(g, names, bound, out);
                }
                collect_refs(&arm.body, names, bound, out);
                bound.truncate(base);
            }
        }
        Expr::List(xs) | Expr::Tuple(xs) => {
            for x in xs {
                collect_refs(x, names, bound, out);
            }
        }
        Expr::IndexSet(a, b, c) => {
            collect_refs(a, names, bound, out);
            collect_refs(b, names, bound, out);
            collect_refs(c, names, bound, out);
        }
        Expr::RecordCreate(_, fields) => {
            for (_, v) in fields {
                collect_refs(v, names, bound, out);
            }
        }
        Expr::RecordUpdate(base, _, fields) => {
            collect_refs(base, names, bound, out);
            for (_, v) in fields {
                collect_refs(v, names, bound, out);
            }
        }
        Expr::RecordUpdatePath(base, ups) => {
            collect_refs(base, names, bound, out);
            for (_, op) in ups {
                collect_refs(op.expr(), names, bound, out);
            }
        }
        Expr::Handle(body, arms) => {
            collect_refs(body, names, bound, out);
            for arm in arms {
                let base = bound.len();
                let sub = match arm {
                    // The return binder scopes over its clause body.
                    HandlerArm::Return(r, e2) => {
                        bound.push(r.as_str());
                        e2
                    }
                    // An op clause binds the operation parameters and the
                    // continuation over its body.
                    HandlerArm::Op(_, params, k, e2) => {
                        bound.extend(params.iter().map(String::as_str));
                        bound.push(k.as_str());
                        e2
                    }
                    #[expect(
                        clippy::uninhabited_references,
                        reason = "Never is uninhabited in Core"
                    )]
                    HandlerArm::Sugar(never) => match *never {},
                };
                collect_refs(sub, names, bound, out);
                bound.truncate(base);
            }
        }
        #[expect(
            clippy::uninhabited_references,
            reason = "Never is uninhabited in Core"
        )]
        Expr::Sugar(never) | Expr::Marker(never) => match *never {},
    }
}

// Push every variable a pattern binds onto `bound`. Constructor and record names
// are not binders; only `Var` and the variables of nested sub-patterns are.
fn collect_pat_binders<'a>(p: &'a S<Pattern>, bound: &mut Vec<&'a str>) {
    match &p.node {
        Pattern::Var(n) => bound.push(n.as_str()),
        Pattern::Ctor(_, args) | Pattern::Tuple(args) => {
            for a in args {
                collect_pat_binders(a, bound);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, sub) in fields {
                collect_pat_binders(sub, bound);
            }
        }
        Pattern::Wild
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Char(_)
        | Pattern::Bool(_) => {}
    }
}
