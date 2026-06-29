//! Call-graph dependency analysis over `prog.fns`: the strongly-connected
//! components that order type inference, and the self-recursion test that gates
//! the polymorphic-recursion hint. This is structural (who references whom), not
//! an effect analysis: effect rows are discovered by principal inference, so the
//! old syntactic effect set-pass that once lived here is gone.

use crate::syntax::ast::{Core, Decl, Expr, HandlerArm, Program, S};

/// The strongly-connected components of `prog.fns`'s call graph, in dependency
/// order (every component a callee belongs to precedes the components that call
/// it). Each component is a recursion group: a singleton for an acyclic
/// definition (with a self-edge for self-recursion), or several members for a
/// mutually recursive cluster. Checking a component only after its callees lets
/// a forward reference (notably one into a stdlib module merged after the
/// prelude) see a generalized type rather than a structure-free stub, and lets a
/// mutually recursive group be inferred against shared monomorphic variables.
///
/// Members within a component are returned in declaration order. A shadowing
/// local that happens to share a top-level name only adds a spurious edge, which
/// is sound (it can never drop a real dependency).
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
            collect_refs(&d.body, &names, &mut refs);
            refs.into_iter().collect()
        })
        .collect();
    crate::scc::tarjan_scc(&deps)
}

/// Whether a declaration's body refers to its own name: direct self-recursion,
/// i.e. a singleton strongly-connected component with a self-edge. Used only to
/// decide whether a body's type error warrants the polymorphic-recursion remedy
/// hint, so the over-approximation from a same-named shadowing local is harmless.
#[must_use]
pub(crate) fn is_self_recursive(d: &Decl<Core>) -> bool {
    let names: std::collections::BTreeMap<&str, usize> =
        std::iter::once((d.name.as_str(), 0)).collect();
    let mut refs = std::collections::BTreeSet::new();
    collect_refs(&d.body, &names, &mut refs);
    !refs.is_empty()
}

// Every top-level function `e` references, by canonical name. Constructors,
// effect ops, builtins, and locals are not in `names`, so they fall out; the
// over-approximation from a same-named shadowing local is harmless.
fn collect_refs(
    e: &S<Expr<Core>>,
    names: &std::collections::BTreeMap<&str, usize>,
    out: &mut std::collections::BTreeSet<usize>,
) {
    let mut go = |e| collect_refs(e, names, out);
    match &e.node {
        Expr::Var(n) => {
            if let Some(&i) = names.get(n.as_str()) {
                out.insert(i);
            }
        }
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Str(_) => {}
        Expr::Bin(_, a, b) | Expr::Index(a, b) | Expr::Pipe(a, b) => {
            go(a);
            go(b);
        }
        Expr::If(c, t, e2) => {
            go(c);
            go(t);
            go(e2);
        }
        Expr::Let(_, v, b) => {
            go(v);
            go(b);
        }
        Expr::Lam(_, b)
        | Expr::FieldAccess(b, _)
        | Expr::Inst(b, _)
        | Expr::Ann(b, _)
        | Expr::Mask(_, b) => go(b),
        Expr::Call(f, args) => {
            go(f);
            for a in args {
                go(a);
            }
        }
        Expr::Match(s, arms) => {
            go(s);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    go(g);
                }
                go(&arm.body);
            }
        }
        Expr::List(xs) | Expr::Tuple(xs) => {
            for x in xs {
                go(x);
            }
        }
        Expr::IndexSet(a, b, c) => {
            go(a);
            go(b);
            go(c);
        }
        Expr::RecordCreate(_, fields) => {
            for (_, v) in fields {
                go(v);
            }
        }
        Expr::RecordUpdate(base, _, fields) => {
            go(base);
            for (_, v) in fields {
                go(v);
            }
        }
        Expr::RecordUpdatePath(base, ups) => {
            go(base);
            for (_, op) in ups {
                go(op.expr());
            }
        }
        Expr::Handle(body, arms) => {
            go(body);
            for arm in arms {
                match arm {
                    HandlerArm::Return(_, e2) | HandlerArm::Op(_, _, _, e2) => go(e2),
                    #[expect(
                        clippy::uninhabited_references,
                        reason = "Never is uninhabited in Core"
                    )]
                    HandlerArm::Sugar(never) => match *never {},
                }
            }
        }
        #[expect(
            clippy::uninhabited_references,
            reason = "Never is uninhabited in Core"
        )]
        Expr::Sugar(never) | Expr::Marker(never) => match *never {},
    }
}
