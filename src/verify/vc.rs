//! Verification-condition generation: from a contracted
//! function's checked contract and its symbolically elaborated body, produce the
//! standalone SMT obligations whose `unsat` discharges each postcondition.
//!
//! The body is elaborated into one logical term over the parameter binders (an
//! `if` becomes an `ite`, so branch conditions ride inside the term rather than
//! splitting into separate path obligations). For each `ensures` clause the goal
//! is that clause with the result binder replaced by the body term, assumed under
//! the `requires` clauses. A function whose body leaves the scalar fragment is
//! reported *pending*, never rejected, because its contract is still valid Prism.
//!
//! Generation reads the resolved surface program before optimization, so the
//! obligation bytes are invariant across optimizer configuration, backend, and
//! effect-lowering tier. No solver is consulted here; discharge is a later step.

use crate::error::TypeError;
use crate::syntax::ast::Program;
use crate::verify::check::{subst_var, Checker};
use crate::verify::logic::{Obligation, VarId};
use crate::verify::query::SmtQuery;
use crate::verify::wf;

/// The verification conditions of one contracted function.
pub(crate) struct FunctionVCs {
    pub(crate) name: String,
    /// The contract digest: the verification identity a certificate is subject to,
    /// and what moves (invalidating the dependency cone) when the contract changes.
    pub(crate) subject: String,
    pub(crate) status: VcStatus,
}

pub(crate) enum VcStatus {
    /// One obligation per `ensures` clause, in source order.
    Obligations(Vec<Obligation>),
    /// The contract is well-formed but the body is outside the supported
    /// fragment, so no obligation can be generated yet.
    Pending(String),
}

/// Generate the postcondition obligations for every contracted function in the
/// resolved program.
///
/// # Errors
/// A malformed logical declaration or contract (the same source errors the check
/// path raises); an unsupported *body* is reported as [`VcStatus::Pending`], not
/// an error.
pub(crate) fn generate(prog: &Program) -> Result<Vec<FunctionVCs>, TypeError> {
    let checker = Checker::build(prog)?;
    let mut out = Vec::new();
    for d in &prog.fns {
        if d.requires.is_empty() && d.ensures.is_empty() {
            continue;
        }
        let contract = checker.checked_contract(d)?;
        let subject = crate::verify::normalize::contract_digest(&contract);
        if contract.ensures.is_empty() {
            // A requires-only contract has no standalone goal; its precondition
            // constrains callers, discharged modularly in a later wave.
            continue;
        }
        let body = match checker.elab_body(d, &contract.params, contract.result) {
            Ok(body) => body,
            Err(reason) => {
                out.push(FunctionVCs {
                    name: d.name.clone(),
                    subject,
                    status: VcStatus::Pending(reason.to_string()),
                });
                continue;
            }
        };
        let result_binder = VarId(u32::try_from(contract.params.len()).unwrap_or(u32::MAX));
        let mut obligations = Vec::new();
        for post in &contract.ensures {
            let goal = subst_var(post, result_binder, &body);
            let ob = Obligation {
                vars: contract.params.clone(),
                funcs: Vec::new(),
                assumptions: contract.requires.clone(),
                goal,
            };
            wf::check(&ob).map_err(|e| TypeError::InternalInvariant {
                msg: format!("generated an ill-sorted VC for `{}`: {e:?}", d.name),
            })?;
            obligations.push(ob);
        }
        out.push(FunctionVCs {
            name: d.name.clone(),
            subject,
            status: VcStatus::Obligations(obligations),
        });
    }
    Ok(out)
}

/// The `dump smt` rendering: one canonical query artifact per obligation, each
/// under a `-- name #i --` banner, and a `pending` line for ineligible bodies.
/// Deterministic; no paths, spans, or timestamps.
///
/// # Errors
/// Propagates a malformed-contract source error from [`generate`].
pub(crate) fn render(prog: &Program) -> Result<String, TypeError> {
    let mut out = String::new();
    for f in &generate(prog)? {
        match &f.status {
            VcStatus::Pending(reason) => {
                out.push_str("-- ");
                out.push_str(&f.name);
                out.push_str(": pending (");
                out.push_str(reason);
                out.push_str(") --\n\n");
            }
            VcStatus::Obligations(obs) => {
                for (i, ob) in obs.iter().enumerate() {
                    out.push_str("-- ");
                    out.push_str(&f.name);
                    out.push_str(" #");
                    out.push_str(&i.to_string());
                    out.push_str(" --\n");
                    out.push_str(&SmtQuery::build(ob).render());
                    out.push('\n');
                }
            }
        }
    }
    Ok(out)
}
