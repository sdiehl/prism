//! Termination ranking obligations: from a `total fn`'s `decreases`
//! measure, its preconditions, and the path conditions of each recursive call,
//! generate the nonnegative-integer ranking obligations whose `unsat` discharges
//! termination, reusing the SMT substrate that partial-correctness contracts use.
//!
//! For a self-recursive `total fn f` with measure `m` over its parameters and
//! preconditions `R`, and for each recursive-call edge under path condition `P`
//! with measure `m'` (the measure evaluated at the recursive arguments):
//!
//! ```text
//! entry:  R        =>  m  >= 0
//! edge:   R and P  =>  m' >= 0
//! edge:   R and P  =>  m' <  m
//! ```
//!
//! A separate obligation `R and P => Rg[args]` discharges a callee `g`'s
//! precondition where the body calls a contracted function, so a totality proof
//! that consumes `g` also shows the call stays inside `g`'s domain.
//!
//! Generation is solver-free and deterministic: an ineligible measure, parameter,
//! path condition, or argument leaves the function *pending* with a precise reason,
//! never "non-total". The obligations are the same `Obligation`/`SmtQuery` artifacts
//! contracts use, so `smtlib`/`normalize`/`query` carry them and the `solver`
//! adapter discharges them from [`crate::verify::run`]. Termination stays a
//! certificate family distinct from partial correctness: the two only combine into
//! total correctness when both close.

use std::collections::{BTreeMap, BTreeSet};

use crate::syntax::ast::{Decl, Expr, Program, Total, S};
use crate::util::scc::tarjan_scc;
use crate::verify::check::{self, Checker};
use crate::verify::logic::{LogicExpr, LogicSort, Obligation};
use crate::verify::query::SmtQuery;
use crate::verify::wf;

/// The role of one ranking obligation, for diagnostics and the SMT dump banner.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum RankKind {
    /// `R => m >= 0`: the measure is nonnegative on entry.
    EntryNonneg,
    /// `R and P => m' >= 0`: the measure stays nonnegative at recursive edge `i`.
    EdgeNonneg(usize),
    /// `R and P => m' < m`: the measure strictly decreases at recursive edge `i`.
    EdgeDecrease(usize),
    /// `R and P => Rg[args]`: callee `g`'s precondition holds at a call site.
    CallPrecondition(String),
}

impl RankKind {
    /// The one-line label for the `dump smt` banner and the failed-ranking report.
    pub(crate) fn label(&self) -> String {
        match self {
            Self::EntryNonneg => "entry: measure >= 0".to_string(),
            Self::EdgeNonneg(i) => format!("edge #{i}: measure >= 0"),
            Self::EdgeDecrease(i) => format!("edge #{i}: measure decreases"),
            Self::CallPrecondition(callee) => format!("call `{callee}`: precondition"),
        }
    }
}

/// One well-formed ranking obligation: its role and the SMT obligation to discharge.
pub(crate) struct RankObligation {
    pub(crate) kind: RankKind,
    pub(crate) ob: Obligation,
}

/// The ranking analysis of one measured `total fn`.
pub(crate) struct FnRanking {
    pub(crate) name: String,
    pub(crate) status: RankStatus,
}

pub(crate) enum RankStatus {
    /// The measure is well-formed; one obligation per role, ready to discharge.
    /// `edges` is the number of recursive-call edges the obligations cover.
    Obligations {
        edges: usize,
        obligations: Vec<RankObligation>,
    },
    /// The measure or an edge is outside the ranking fragment; a precise reason.
    Pending(String),
}

/// Analyze every `total fn` (not `assume total`) carrying a `decreases` measure.
/// Solver-free: a function never becomes a source error here, only obligations or a
/// pending reason.
pub(crate) fn generate(prog: &Program) -> Vec<FnRanking> {
    // A malformed logical declaration is reported by the contract checker; here it
    // just means ranking cannot run, so every measured function is pending.
    let Ok(checker) = Checker::build(prog) else {
        return prog
            .fns
            .iter()
            .filter(|d| measured(d))
            .map(|d| FnRanking {
                name: d.name.clone(),
                status: RankStatus::Pending(
                    "the module's logical declarations did not check".to_string(),
                ),
            })
            .collect();
    };
    let index: BTreeMap<&str, usize> = prog
        .fns
        .iter()
        .enumerate()
        .map(|(i, d)| (d.name.as_str(), i))
        .collect();
    let by_name: BTreeMap<&str, &Decl> = prog.fns.iter().map(|d| (d.name.as_str(), d)).collect();
    // Direct-call graph over top-level functions, for mutual-recursion detection: a
    // measured function in a multi-member SCC is mutual recursion, which needs one
    // SCC-wide measure and stays pending (admitting each member alone is unsound).
    let adj: Vec<Vec<usize>> = prog
        .fns
        .iter()
        .map(|d| direct_callees(&d.body, &index))
        .collect();
    let mutual: BTreeSet<usize> = tarjan_scc(&adj)
        .into_iter()
        .filter(|scc| scc.len() > 1)
        .flatten()
        .collect();

    prog.fns
        .iter()
        .enumerate()
        .filter(|(_, d)| measured(d))
        .map(|(i, d)| {
            let status = if mutual.contains(&i) {
                RankStatus::Pending("mutual recursion is not supported yet".to_string())
            } else {
                let measure = d
                    .decreases
                    .as_ref()
                    .expect("measured filter guarantees a measure");
                analyze(&checker, &by_name, d, measure)
            };
            FnRanking {
                name: d.name.clone(),
                status,
            }
        })
        .collect()
}

/// A `total fn` (proof obligation, not a trusted assumption) with a ranking measure.
fn measured(d: &Decl) -> bool {
    d.total == Total::Prove && d.decreases.is_some()
}

/// The indices of the top-level functions `body` directly calls, in increasing
/// order. A call whose head is not a named function (a constructor, primitive, or
/// higher-order value) is not an edge here.
fn direct_callees(body: &S<Expr>, index: &BTreeMap<&str, usize>) -> Vec<usize> {
    let mut sites = Vec::new();
    collect_sites(body, &mut Vec::new(), &mut sites);
    sites
        .iter()
        .filter_map(|s| index.get(s.callee.as_str()).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn analyze(
    checker: &Checker,
    by_name: &BTreeMap<&str, &Decl>,
    d: &Decl,
    measure_expr: &S<Expr>,
) -> RankStatus {
    // A lambda, an indirect call, or a call to a higher-order parameter could hide a
    // recursive call from the direct-call model, so a function whose recursion runs
    // through a closure would show zero edges and be unsoundly "verified". Reject
    // such a body as pending before generating any obligation.
    if let Err(reason) = first_order_body(d) {
        return RankStatus::Pending(reason);
    }
    let Some(params) = check::logical_param_sorts(d) else {
        return RankStatus::Pending(
            "a parameter is not `Int`/`Bool`, outside the ranking fragment".to_string(),
        );
    };
    let requires = match elab_clauses(checker, d, &params, &d.requires) {
        Ok(r) => r,
        Err(reason) => return RankStatus::Pending(reason),
    };
    let Ok((measure, msort)) = checker.elab_expr(d, &params, measure_expr) else {
        return RankStatus::Pending(
            "the measure is outside the linear-integer ranking fragment".to_string(),
        );
    };
    if msort != LogicSort::Int {
        return RankStatus::Pending("the measure is not an integer".to_string());
    }

    let mut sites = Vec::new();
    collect_sites(&d.body, &mut Vec::new(), &mut sites);

    let mut obligations = Vec::new();
    // Entry: R => m >= 0.
    obligations.push(RankObligation {
        kind: RankKind::EntryNonneg,
        ob: implication(&params, &requires, &[], nonneg(measure.clone())),
    });

    let mut edge = 0usize;
    for site in &sites {
        let self_call = site.callee == d.name;
        let callee = by_name.get(site.callee.as_str());
        // A non-recursive callee only matters when it carries a precondition to
        // discharge; a constructor, effect op, or contract-free helper is skipped.
        if !self_call && callee.is_none_or(|c| c.requires.is_empty()) {
            continue;
        }
        let path = match elab_path(checker, d, &params, &site.conds) {
            Ok(p) => p,
            Err(reason) => return RankStatus::Pending(reason),
        };
        if self_call {
            if site.args.len() != params.len() {
                return RankStatus::Pending("a recursive call is partially applied".to_string());
            }
            let args = match elab_args(checker, d, &params, &site.args, &params) {
                Ok(a) => a,
                Err(reason) => return RankStatus::Pending(reason),
            };
            let m_prime = check::subst(&measure, &args);
            obligations.push(RankObligation {
                kind: RankKind::EdgeNonneg(edge),
                ob: implication(&params, &requires, &path, nonneg(m_prime.clone())),
            });
            obligations.push(RankObligation {
                kind: RankKind::EdgeDecrease(edge),
                ob: implication(
                    &params,
                    &requires,
                    &path,
                    LogicExpr::lt(m_prime, measure.clone()),
                ),
            });
            edge += 1;
        } else {
            // Call-site precondition: discharge the callee's `requires` at the
            // instantiated arguments, so consuming the callee's totality is sound.
            let callee = callee.expect("checked is_none_or above");
            let Some(callee_params) = check::logical_param_sorts(callee) else {
                return RankStatus::Pending(format!(
                    "cannot discharge `{}`'s precondition: its parameters are outside the fragment",
                    site.callee
                ));
            };
            if site.args.len() != callee_params.len() {
                return RankStatus::Pending(format!(
                    "call to `{}` does not match its arity for precondition checking",
                    site.callee
                ));
            }
            let callee_reqs = match elab_clauses(checker, callee, &callee_params, &callee.requires)
            {
                Ok(r) => r,
                Err(reason) => return RankStatus::Pending(reason),
            };
            let args = match elab_args(checker, d, &params, &site.args, &callee_params) {
                Ok(a) => a,
                Err(reason) => return RankStatus::Pending(reason),
            };
            for req in &callee_reqs {
                let inst = check::subst(req, &args);
                obligations.push(RankObligation {
                    kind: RankKind::CallPrecondition(site.callee.clone()),
                    ob: implication(&params, &requires, &path, inst),
                });
            }
        }
    }

    // Every generated obligation is re-verified well-sorted (reusing the same
    // independent checker contracts use); a failure is a compiler bug, not a source
    // error, and is surfaced as a precise pending reason rather than a panic.
    for ro in &obligations {
        if let Err(e) = wf::check(&ro.ob) {
            return RankStatus::Pending(format!(
                "internal: generated an ill-sorted ranking obligation ({}): {e:?}",
                ro.kind.label()
            ));
        }
    }
    RankStatus::Obligations {
        edges: edge,
        obligations,
    }
}

/// Reject a body that could hide a recursive call from the direct-call model: a
/// lambda, an indirect (non-named) call, or a call to a higher-order parameter.
/// This keeps the direct-call edge count a sound over-approximation of "no
/// recursion", so a function with zero recursive edges really is non-recursive.
fn first_order_body(d: &Decl) -> Result<(), String> {
    let params: BTreeSet<&str> = d.params.iter().map(|p| p.name.as_str()).collect();
    walk_first_order(&d.body, &params)
}

fn walk_first_order(e: &S<Expr>, params: &BTreeSet<&str>) -> Result<(), String> {
    match &e.node {
        Expr::Lam(..) => {
            return Err("the body contains a lambda; hidden recursion is not supported".to_string())
        }
        Expr::Call(f, _) => match &f.node {
            Expr::Var(name) if params.contains(name.as_str()) => {
                return Err(
                    "the body calls a higher-order parameter; hidden recursion is not supported"
                        .to_string(),
                )
            }
            Expr::Var(_) => {}
            _ => {
                return Err(
                    "the body has an indirect call; hidden recursion is not supported".to_string(),
                )
            }
        },
        _ => {}
    }
    let mut result = Ok(());
    e.node.each_child(&mut |c| {
        if result.is_ok() {
            result = walk_first_order(c, params);
        }
    });
    result
}

/// `m >= 0`.
fn nonneg(m: LogicExpr) -> LogicExpr {
    LogicExpr::ge(m, LogicExpr::int(0))
}

/// Assemble `assumptions ++ path => goal` over the parameter sorts, with no
/// uninterpreted functions (the fragment inlines logical declarations).
fn implication(
    params: &[LogicSort],
    requires: &[LogicExpr],
    path: &[LogicExpr],
    goal: LogicExpr,
) -> Obligation {
    let mut assumptions = Vec::with_capacity(requires.len() + path.len());
    assumptions.extend(requires.iter().cloned());
    assumptions.extend(path.iter().cloned());
    Obligation {
        vars: params.to_vec(),
        funcs: Vec::new(),
        assumptions,
        goal,
    }
}

/// Elaborate a list of `Bool` clauses (a function's `requires`) over `d`'s params.
fn elab_clauses(
    checker: &Checker,
    d: &Decl,
    params: &[LogicSort],
    clauses: &[S<Expr>],
) -> Result<Vec<LogicExpr>, String> {
    let mut out = Vec::with_capacity(clauses.len());
    for c in clauses {
        let (logic, sort) = checker
            .elab_expr(d, params, c)
            .map_err(|_| "a precondition is outside the ranking fragment".to_string())?;
        if sort != LogicSort::Bool {
            return Err("a precondition is not a Bool".to_string());
        }
        out.push(logic);
    }
    Ok(out)
}

/// Elaborate the `(condition, negated)` path conditions of a recursive edge.
fn elab_path(
    checker: &Checker,
    d: &Decl,
    params: &[LogicSort],
    conds: &[(S<Expr>, bool)],
) -> Result<Vec<LogicExpr>, String> {
    let mut out = Vec::with_capacity(conds.len());
    for (cond, negated) in conds {
        let (logic, sort) = checker
            .elab_expr(d, params, cond)
            .map_err(|_| "a branch condition is outside the ranking fragment".to_string())?;
        if sort != LogicSort::Bool {
            return Err("a branch condition is not a Bool".to_string());
        }
        out.push(if *negated {
            LogicExpr::not(logic)
        } else {
            logic
        });
    }
    Ok(out)
}

/// Elaborate the arguments of a call, requiring each to match the expected sort at
/// its position (the callee's parameter sort) so the substitution stays well-sorted.
fn elab_args(
    checker: &Checker,
    d: &Decl,
    params: &[LogicSort],
    args: &[S<Expr>],
    expected: &[LogicSort],
) -> Result<Vec<LogicExpr>, String> {
    let mut out = Vec::with_capacity(args.len());
    for (arg, &want) in args.iter().zip(expected) {
        let (logic, sort) = checker
            .elab_expr(d, params, arg)
            .map_err(|_| "a call argument is outside the ranking fragment".to_string())?;
        if sort != want {
            return Err("a call argument has the wrong sort for its position".to_string());
        }
        out.push(logic);
    }
    Ok(out)
}

/// One call in a function body: the callee name, the `(condition, negated)` path
/// conditions guarding it, and its arguments. Both conditions and arguments are
/// cloned so the walk owns them, independent of the source tree's lifetime.
struct Site {
    callee: String,
    conds: Vec<(S<Expr>, bool)>,
    args: Vec<S<Expr>>,
}

/// Collect every directly-named call in `e` with its guarding path conditions.
/// `if` splits the path (the condition in the then-branch, its negation in the
/// else-branch). `match` arms are walked without a path condition: a constructor
/// discriminator is not in the linear-integer fragment, and dropping it only
/// weakens the antecedent, which keeps an unprovable obligation *pending* rather
/// than falsely discharged.
fn collect_sites(e: &S<Expr>, path: &mut Vec<(S<Expr>, bool)>, out: &mut Vec<Site>) {
    match &e.node {
        Expr::If(c, t, els) => {
            collect_sites(c, path, out);
            path.push(((**c).clone(), false));
            collect_sites(t, path, out);
            path.pop();
            path.push(((**c).clone(), true));
            collect_sites(els, path, out);
            path.pop();
        }
        Expr::Call(f, args) => {
            if let Expr::Var(callee) = &f.node {
                out.push(Site {
                    callee: callee.clone(),
                    conds: path.clone(),
                    args: args.clone(),
                });
            }
            for a in args {
                collect_sites(a, path, out);
            }
            collect_sites(f, path, out);
        }
        Expr::Match(scrut, arms) => {
            collect_sites(scrut, path, out);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    collect_sites(g, path, out);
                }
                collect_sites(&arm.body, path, out);
            }
        }
        Expr::Let(_, v, b) => {
            collect_sites(v, path, out);
            collect_sites(b, path, out);
        }
        _ => e.node.each_child(&mut |c| collect_sites(c, path, out)),
    }
}

/// The `dump smt` termination section: one canonical query artifact per ranking
/// obligation under a `-- name termination #i (role) --` banner, and a `pending`
/// line for a measure outside the fragment. Deterministic; no paths or timestamps.
/// Distinct from the partial-correctness obligations so the two certificate
/// families never blur.
pub(crate) fn render_smt(prog: &Program) -> String {
    let mut out = String::new();
    for f in generate(prog) {
        match &f.status {
            RankStatus::Pending(reason) => {
                out.push_str("-- ");
                out.push_str(&f.name);
                out.push_str(" termination: pending (");
                out.push_str(reason);
                out.push_str(") --\n\n");
            }
            RankStatus::Obligations { obligations, .. } => {
                for (i, ro) in obligations.iter().enumerate() {
                    out.push_str("-- ");
                    out.push_str(&f.name);
                    out.push_str(" termination #");
                    out.push_str(&i.to_string());
                    out.push_str(" (");
                    out.push_str(&ro.kind.label());
                    out.push_str(") --\n");
                    out.push_str(&SmtQuery::build(&ro.ob).render());
                    out.push('\n');
                }
            }
        }
    }
    out
}
