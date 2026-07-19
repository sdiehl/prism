//! `prism verify` orchestration: generate each
//! function's obligations, discharge them through one or more pinned external
//! solvers, record content-addressed receipts and certificates, and aggregate an
//! honest per-function verdict. A function is verified only when every one of its
//! obligations returns `unsat`; a single counterexample refutes it, a split
//! between two solvers fails closed, and an undecided or missing solver leaves it
//! unproven, never silently accepted.
//!
//! Two certificate families are kept distinct: partial correctness (the `requires`/
//! `ensures` contract obligations) and termination (the `decreases` ranking
//! obligations). They only combine into total correctness for a function whose
//! contract and ranking both close.
//!
//! Evidence is content-addressed. When a store is present, every receipt is
//! recorded, a passing `unsat` receipt is bound as reusable evidence keyed by the
//! exact query and solver identity, and a fully discharged function mints a
//! [`SmtCertificate`] whose closure the store can later re-check. A solver flag or
//! version change moves receipt (and certificate) identity; the query identity
//! never moves.

use std::collections::BTreeSet;
use std::io;
use std::time::Duration;

use crate::error::TypeError;
use crate::store::disk::Store;
use crate::syntax::ast::Program;
use crate::verify::certificate::{CertObligation, CertTrust, Completeness, SmtCertificate};
use crate::verify::logic::Obligation;
use crate::verify::query::SmtQuery;
use crate::verify::ranking::{self, RankObligation, RankStatus};
use crate::verify::result::{ResultStatus, SmtResult};
use crate::verify::solver::{self, PinnedSolver};
use crate::verify::store as verify_store;
use crate::verify::vc::{self, VcStatus};

/// How the verifier consults solvers.
pub(crate) struct VerifyOptions {
    /// Solver executables in pinned order. Without `require_agreement`, only the
    /// first is consulted; with it, every one must agree.
    pub(crate) solvers: Vec<String>,
    /// Every selected solver must report `unsat`; any split fails closed.
    pub(crate) require_agreement: bool,
    /// The per-discharge wall-clock budget, or the adapter default when `None`.
    pub(crate) timeout: Option<Duration>,
}

impl VerifyOptions {
    /// The single-solver, no-store default the plain `prism verify FILE` and the
    /// existing tests use.
    pub(crate) fn single(exe: &str) -> Self {
        Self {
            solvers: vec![exe.to_string()],
            require_agreement: false,
            timeout: None,
        }
    }
}

/// The partial-correctness verdict for one contracted function.
pub(crate) enum Verdict {
    /// Every obligation returned `unsat` (solver-oracle). Carries the count.
    Verified(usize),
    /// An obligation has a counterexample. Carries its index.
    Counterexample(usize),
    /// Two solvers split on an obligation (one `unsat`, one `sat`); fails closed.
    Disagreement(usize),
    /// An obligation was undecided (`unknown`, timeout, crash, or malformed output).
    Unknown(usize),
    /// The body is outside the supported fragment; nothing to discharge.
    Pending(String),
    /// A selected solver executable was not found.
    NoSolver,
}

impl Verdict {
    /// Whether this verdict clears the honest exit gate. Only a full `unsat` proof
    /// does. Pending proved nothing, so it is deliberately not clear: a CI gate
    /// keyed on exit 0 must never pass a contract that was never discharged.
    const fn is_clear(&self) -> bool {
        matches!(self, Self::Verified(_))
    }
}

/// The termination verdict for one `total fn` with a `decreases` measure.
pub(crate) enum TermVerdict {
    /// Every ranking obligation returned `unsat` (solver-oracle). Carries the count.
    Verified(usize),
    /// A ranking obligation has a counterexample: a *failed ranking argument*, not
    /// a proof of divergence. Totality stays pending. Carries the obligation index
    /// and its role.
    FailedRanking { obligation: usize, kind: String },
    /// Two solvers split on a ranking obligation; totality stays pending.
    Disagreement(usize),
    /// A ranking obligation was undecided; totality stays pending.
    Unknown(usize),
    /// The measure is outside the ranking fragment; nothing to discharge.
    Pending(String),
    /// A selected solver executable was not found.
    NoSolver,
}

impl TermVerdict {
    /// Whether this termination verdict clears the honest exit gate. Only a fully
    /// discharged ranking measure does; a pending measure proved no termination.
    const fn is_clear(&self) -> bool {
        matches!(self, Self::Verified(_))
    }
}

/// One contracted function's verdict and, when the store minted one, its
/// certificate digest.
struct FunctionReport {
    name: String,
    verdict: Verdict,
    certificate: Option<String>,
}

pub(crate) struct VerifyReport {
    solvers: Vec<String>,
    require_agreement: bool,
    functions: Vec<FunctionReport>,
    terminations: Vec<(String, TermVerdict)>,
}

/// Discharge every contracted function's obligations and every ranking measure's
/// obligations through the single solver `solver_exe`, without a store.
///
/// # Errors
/// A malformed logical declaration or contract (a source error).
pub(crate) fn run(prog: &Program, solver_exe: &str) -> Result<VerifyReport, TypeError> {
    run_with(prog, &VerifyOptions::single(solver_exe), None)
}

/// Discharge every obligation under `opts`, recording content-addressed evidence in
/// `store` when one is provided.
///
/// # Errors
/// A malformed logical declaration or contract (a source error).
pub(crate) fn run_with(
    prog: &Program,
    opts: &VerifyOptions,
    store: Option<&Store>,
) -> Result<VerifyReport, TypeError> {
    let pinned = pin_solvers(opts);
    let mut functions = Vec::new();
    for f in vc::generate(prog)? {
        let (verdict, certificate) = match f.status {
            VcStatus::Pending(reason) => (Verdict::Pending(reason), None),
            VcStatus::Obligations(obs) => {
                discharge_function(pinned.as_deref(), store, &f.subject, &obs)
            }
        };
        functions.push(FunctionReport {
            name: f.name,
            verdict,
            certificate,
        });
    }
    let mut terminations = Vec::new();
    for f in ranking::generate(prog) {
        let verdict = match f.status {
            RankStatus::Pending(reason) => TermVerdict::Pending(reason),
            RankStatus::Obligations { obligations, .. } => {
                discharge_ranking(pinned.as_deref(), store, &obligations)
            }
        };
        terminations.push((f.name, verdict));
    }
    Ok(VerifyReport {
        solvers: opts.solvers.clone(),
        require_agreement: opts.require_agreement,
        functions,
        terminations,
    })
}

/// Pin the solvers to consult, or `None` when a required one is unavailable.
/// Without agreement only the first is consulted; with it every one must be
/// present, since agreement cannot be reached with a missing solver.
fn pin_solvers(opts: &VerifyOptions) -> Option<Vec<PinnedSolver>> {
    if opts.require_agreement {
        let mut pins = Vec::new();
        for exe in &opts.solvers {
            pins.push(solver::pin(exe, opts.timeout)?);
        }
        Some(pins)
    } else {
        let first = opts.solvers.first()?;
        Some(vec![solver::pin(first, opts.timeout)?])
    }
}

/// The obligation-level verdict from the consulted solvers' receipts.
enum ObVerdict {
    /// Every consulted solver returned `unsat`.
    Proved,
    /// Some solver returned `sat` and none returned `unsat`.
    Counterexample,
    /// Solvers split: at least one `unsat` and at least one `sat`. Fails closed.
    Disagreement,
    /// No `sat`, not all `unsat`: an undecided, timeout, crash, or malformed answer.
    Undecided,
}

/// One discharged obligation: its query digest, the aggregate verdict, and the
/// per-solver receipts (recorded in the store when present).
struct ObResult {
    query_digest: String,
    verdict: ObVerdict,
    receipts: Vec<SmtResult>,
}

/// Discharge a contracted function's obligations and, when every one is proved and
/// a store is present, mint and store its certificate.
fn discharge_function(
    solvers: Option<&[PinnedSolver]>,
    store: Option<&Store>,
    subject: &str,
    obligations: &[Obligation],
) -> (Verdict, Option<String>) {
    let Some(solvers) = solvers else {
        return (Verdict::NoSolver, None);
    };
    let mut results = Vec::new();
    for ob in obligations {
        results.push(discharge_obligation(solvers, store, ob));
    }
    for (i, r) in results.iter().enumerate() {
        match r.verdict {
            ObVerdict::Proved => {}
            ObVerdict::Counterexample => return (Verdict::Counterexample(i), None),
            ObVerdict::Disagreement => return (Verdict::Disagreement(i), None),
            ObVerdict::Undecided => return (Verdict::Unknown(i), None),
        }
    }
    let certificate = store.and_then(|s| mint_certificate(s, subject, &results).ok());
    (Verdict::Verified(obligations.len()), certificate)
}

/// Termination is proved only if every ranking obligation is proved; a `sat` is a
/// failed ranking argument (totality pending), never a proof of divergence.
fn discharge_ranking(
    solvers: Option<&[PinnedSolver]>,
    store: Option<&Store>,
    obligations: &[RankObligation],
) -> TermVerdict {
    let Some(solvers) = solvers else {
        return TermVerdict::NoSolver;
    };
    for (i, ro) in obligations.iter().enumerate() {
        let result = discharge_obligation(solvers, store, &ro.ob);
        match result.verdict {
            ObVerdict::Proved => {}
            ObVerdict::Counterexample => {
                return TermVerdict::FailedRanking {
                    obligation: i,
                    kind: ro.kind.label(),
                }
            }
            ObVerdict::Disagreement => return TermVerdict::Disagreement(i),
            ObVerdict::Undecided => return TermVerdict::Unknown(i),
        }
    }
    TermVerdict::Verified(obligations.len())
}

/// Discharge one obligation across every consulted solver, reusing a recorded
/// `unsat` where one exists and recording each fresh receipt.
fn discharge_obligation(
    solvers: &[PinnedSolver],
    store: Option<&Store>,
    ob: &Obligation,
) -> ObResult {
    let query = SmtQuery::build(ob);
    let mut receipts = Vec::new();
    for s in solvers {
        receipts.push(obtain_receipt(store, s, &query));
    }
    ObResult {
        verdict: classify(&receipts),
        query_digest: query.digest,
        receipts,
    }
}

/// A receipt for one query from one solver: a recorded reusable `unsat` when
/// available, otherwise a fresh discharge, recorded on the way out.
fn obtain_receipt(store: Option<&Store>, s: &PinnedSolver, query: &SmtQuery) -> SmtResult {
    let id = s.id();
    if let Some(store) = store {
        if let Ok(Some(reused)) = verify_store::reusable_unsat(store, &query.digest, &id) {
            return reused;
        }
    }
    let discharge = s.discharge(&query.smtlib);
    let result = SmtResult::oracle(query.digest.clone(), discharge.status, id, discharge.model);
    if let Some(store) = store {
        let _ = verify_store::put_result(store, &result);
    }
    result
}

/// The aggregate verdict of one obligation's per-solver receipts.
fn classify(receipts: &[SmtResult]) -> ObVerdict {
    if receipts.iter().all(|r| r.status == ResultStatus::Unsat) {
        return ObVerdict::Proved;
    }
    let any_sat = receipts.iter().any(|r| r.status == ResultStatus::Sat);
    let any_unsat = receipts.iter().any(|r| r.status == ResultStatus::Unsat);
    if any_sat {
        if any_unsat {
            return ObVerdict::Disagreement;
        }
        return ObVerdict::Counterexample;
    }
    ObVerdict::Undecided
}

/// Mint and store a complete solver-oracle certificate for a fully discharged
/// function: one obligation per postcondition, each carrying the `unsat` receipt
/// digest(s) that discharged it, no dependencies and no trusted assumptions.
fn mint_certificate(store: &Store, subject: &str, results: &[ObResult]) -> io::Result<String> {
    let obligations = results
        .iter()
        .map(|o| CertObligation {
            query_digest: o.query_digest.clone(),
            receipts: o
                .receipts
                .iter()
                .filter(|r| r.is_reusable_evidence())
                .map(SmtResult::digest)
                .collect(),
        })
        .collect();
    let cert = SmtCertificate {
        subject: subject.to_string(),
        obligations,
        dependencies: Vec::new(),
        assumptions: Vec::new(),
        completeness: Completeness::Complete,
        trust: CertTrust::SolverOracle,
    };
    verify_store::put_certificate(store, &cert)
}

impl VerifyReport {
    /// Whether the exit gate is clear: every contract and every ranking measure was
    /// discharged (`unsat`-proved). Pending is unproven and does not clear, so a CI
    /// check keyed on exit 0 never passes a contract that proved nothing; the
    /// pending items are still named in [`Self::render`] for the human reader.
    pub(crate) fn all_clear(&self) -> bool {
        self.functions.iter().all(|f| f.verdict.is_clear())
            && self.terminations.iter().all(|(_, v)| v.is_clear())
    }

    /// The digests of every certificate this run minted and stored (present only
    /// when a store was supplied and a function fully discharged).
    pub(crate) fn certificate_digests(&self) -> Vec<String> {
        self.functions
            .iter()
            .filter_map(|f| f.certificate.clone())
            .collect()
    }

    /// A one-line failure summary for the command's exit path. Counts every item
    /// that did not clear the gate, so a pending (unproven) item is reported as not
    /// verified, matching the honest exit code.
    pub(crate) fn summary(&self) -> String {
        let contracts = self
            .functions
            .iter()
            .filter(|f| !f.verdict.is_clear())
            .count();
        let terminations = self
            .terminations
            .iter()
            .filter(|(_, v)| !v.is_clear())
            .count();
        format!("{contracts} contract(s) and {terminations} termination(s) not verified")
    }

    /// The label naming the trusted solver(s) for the honest header and the
    /// missing-solver line.
    fn solver_label(&self) -> String {
        self.solvers.join(", ")
    }

    /// The human report. Names each function's verdict; the header is explicit that
    /// an `unsat` is a solver-oracle receipt, not an independent proof. Partial
    /// correctness and termination are separate sections, with a derived
    /// total-correctness note for the functions whose contract and ranking both
    /// close.
    pub(crate) fn render(&self) -> String {
        let agreement = if self.require_agreement {
            " (agreement required)"
        } else {
            ""
        };
        let mut out = format!(
            "prism verify: solver-oracle receipts (trusting `{}`){agreement}\n",
            self.solver_label()
        );
        if self.functions.is_empty() && self.terminations.is_empty() {
            out.push_str("  no contracts or termination measures to verify\n");
            return out;
        }
        for f in &self.functions {
            let line = self.verdict_line(&f.verdict, f.certificate.as_deref());
            push_row(&mut out, &f.name, &line);
        }
        if !self.terminations.is_empty() {
            out.push_str("termination:\n");
            for (name, verdict) in &self.terminations {
                let line = self.term_line(verdict);
                push_row(&mut out, name, &line);
            }
        }
        let derived = self.total_correctness();
        if !derived.is_empty() {
            out.push_str("total correctness (derived, partial correctness + termination):\n");
            for name in derived {
                out.push_str("  ");
                out.push_str(&name);
                out.push('\n');
            }
        }
        out
    }

    fn verdict_line(&self, verdict: &Verdict, certificate: Option<&str>) -> String {
        match verdict {
            Verdict::Verified(n) => {
                let noun = if *n == 1 { "obligation" } else { "obligations" };
                let mut line = format!("verified ({n} {noun})");
                if let Some(digest) = certificate {
                    line.push_str(" [certificate ");
                    line.push_str(short(digest));
                    line.push(']');
                }
                line
            }
            Verdict::Counterexample(i) => format!("counterexample on obligation #{i}"),
            Verdict::Disagreement(i) => {
                format!("solver disagreement on obligation #{i} (fails closed)")
            }
            Verdict::Unknown(i) => format!("undecided on obligation #{i}"),
            Verdict::Pending(reason) => format!("pending: {reason}"),
            Verdict::NoSolver => format!("solver `{}` not found", self.solver_label()),
        }
    }

    fn term_line(&self, verdict: &TermVerdict) -> String {
        match verdict {
            TermVerdict::Verified(1) => "verified (1 ranking obligation)".to_string(),
            TermVerdict::Verified(n) => format!("verified ({n} ranking obligations)"),
            TermVerdict::FailedRanking { obligation, kind } => {
                format!("pending: failed ranking argument on obligation #{obligation} ({kind})")
            }
            TermVerdict::Disagreement(i) => {
                format!("pending: solver disagreement on obligation #{i} (fails closed)")
            }
            TermVerdict::Unknown(i) => format!("pending: undecided on obligation #{i}"),
            TermVerdict::Pending(reason) => format!("pending: {reason}"),
            TermVerdict::NoSolver => format!("solver `{}` not found", self.solver_label()),
        }
    }

    /// Functions whose contract and ranking both closed: total correctness is
    /// derived only when both certificate families verify, never inferred from one.
    fn total_correctness(&self) -> Vec<String> {
        let verified_contracts: BTreeSet<&str> = self
            .functions
            .iter()
            .filter(|f| matches!(f.verdict, Verdict::Verified(_)))
            .map(|f| f.name.as_str())
            .collect();
        self.terminations
            .iter()
            .filter(|(n, v)| {
                matches!(v, TermVerdict::Verified(_)) && verified_contracts.contains(n.as_str())
            })
            .map(|(n, _)| n.clone())
            .collect()
    }
}

fn push_row(out: &mut String, name: &str, line: &str) {
    out.push_str("  ");
    out.push_str(name);
    out.push_str(": ");
    out.push_str(line);
    out.push('\n');
}

/// A short digest prefix for the certificate note.
fn short(digest: &str) -> &str {
    &digest[..digest.len().min(12)]
}

#[cfg(test)]
mod tests {
    use super::{classify, FunctionReport, ObVerdict, TermVerdict, Verdict, VerifyReport};
    use crate::verify::result::{ResultStatus, SmtResult, SolverId, Trust};

    /// A single-contract report carrying `verdict`, for the exit-gate tests.
    fn report_with(verdict: Verdict) -> VerifyReport {
        VerifyReport {
            solvers: vec!["z3".to_string()],
            require_agreement: false,
            functions: vec![FunctionReport {
                name: "f".to_string(),
                verdict,
                certificate: None,
            }],
            terminations: vec![],
        }
    }

    // A contract that proved nothing (Pending) must not clear the exit gate: a CI
    // check keyed on exit 0 would otherwise pass unverified code. The pending item
    // is still named in the human-readable report.
    #[test]
    fn pending_contract_does_not_clear_the_exit_gate() {
        let pending = report_with(Verdict::Pending(
            "body outside the scalar fragment".to_string(),
        ));
        assert!(!pending.all_clear(), "a pending contract is not all-clear");
        assert!(
            pending.render().contains("f: pending"),
            "pending items are still listed:\n{}",
            pending.render()
        );
        assert!(
            pending.summary().contains("1 contract"),
            "the summary counts pending as unverified: {}",
            pending.summary()
        );
    }

    // A fully discharged contract clears the gate (exit 0).
    #[test]
    fn verified_contract_clears_the_exit_gate() {
        assert!(
            report_with(Verdict::Verified(1)).all_clear(),
            "a verified contract is all-clear"
        );
    }

    // A pending termination measure is unproven and does not clear the gate either.
    #[test]
    fn pending_termination_does_not_clear_the_exit_gate() {
        let report = VerifyReport {
            solvers: vec!["z3".to_string()],
            require_agreement: false,
            functions: vec![],
            terminations: vec![(
                "g".to_string(),
                TermVerdict::Pending("measure outside the ranking fragment".to_string()),
            )],
        };
        assert!(
            !report.all_clear(),
            "a pending termination is not all-clear"
        );
    }

    fn receipt(status: ResultStatus) -> SmtResult {
        SmtResult {
            query_digest: "aa".to_string(),
            status,
            trust: Trust::SolverOracle,
            solver: SolverId {
                family: "z3".to_string(),
                version: "v".to_string(),
                flags: vec![],
            },
            model: vec![],
        }
    }

    #[test]
    fn agreement_classification() {
        use ResultStatus::{Sat, Timeout, Unknown, Unsat};
        // A single solver, or several in agreement, on `unsat`: proved.
        assert!(matches!(classify(&[receipt(Unsat)]), ObVerdict::Proved));
        assert!(matches!(
            classify(&[receipt(Unsat), receipt(Unsat)]),
            ObVerdict::Proved
        ));
        // A `sat` with no `unsat`: a counterexample.
        assert!(matches!(
            classify(&[receipt(Sat)]),
            ObVerdict::Counterexample
        ));
        // A split between two solvers fails closed as a disagreement.
        assert!(matches!(
            classify(&[receipt(Unsat), receipt(Sat)]),
            ObVerdict::Disagreement
        ));
        // Anything undecided (unknown, timeout, ...) with no `sat` and not all
        // `unsat` is undecided, never a pass.
        assert!(matches!(
            classify(&[receipt(Unknown)]),
            ObVerdict::Undecided
        ));
        assert!(matches!(
            classify(&[receipt(Unsat), receipt(Unknown)]),
            ObVerdict::Undecided
        ));
        assert!(matches!(
            classify(&[receipt(Timeout)]),
            ObVerdict::Undecided
        ));
    }
}
