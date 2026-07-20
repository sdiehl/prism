//! Totality checking: the acyclic trivial checker and the direct
//! structural-recursion checker.
//!
//! It consumes the resolved surface program. A claim it cannot establish is
//! reported *pending* with a precise reason, never "non-total": a restriction
//! means the checker cannot prove the claim, not that the function diverges. It is
//! a verify-time analysis: it never gates ordinary compilation, and the `total`
//! claim is erased before Core regardless of the outcome.
//!
//! `Trivial`: an acyclic function whose body stays in a total fragment and
//! every directly called function is itself certified total (a constructor and a
//! total scalar primitive count; a plain uncertified helper does not, one false
//! leaf must not certify a whole call graph). `Structural`: a single
//! self-recursive function where every recursive call consumes a strict
//! constructor subterm of one matched parameter. Mutual recursion, higher-order
//! calls, effects, mutation, division, and holes stay pending.

use std::collections::{BTreeMap, BTreeSet};

use crate::syntax::ast::{BinOp, Expr, Pattern, Program, Total, S};
use crate::util::scc::tarjan_scc;
use crate::verify::ranking::{self, RankStatus};

/// The totality verdict for one claimed function.
pub(crate) enum Status {
    /// Checked total: acyclic, total fragment, certified callees.
    Trivial,
    /// Checked total by structural recursion on the named parameter.
    Structural(String),
    /// Trusted source assumption (`assume total fn`).
    Assumed,
    /// A `decreases` measure produced well-formed ranking obligations. Solver-free,
    /// so this dump does not yet claim the measure proves anything: it reports how
    /// many obligations over how many recursive edges await discharge by an SMT
    /// solver (`prism verify`). Kept distinct from the checked and trusted verdicts.
    Ranking { edges: usize, obligations: usize },
    /// Well-formed but unproven, with a precise reason.
    Pending(String),
}

pub(crate) struct FnTotality {
    pub(crate) name: String,
    pub(crate) status: Status,
}

impl Status {
    /// The honest one-line badge for `dump totality` and `:info`. Every
    /// successful-looking status stays distinct; nothing collapses to "verified".
    pub(crate) fn badge(&self) -> String {
        match self {
            Self::Trivial => "checked (acyclic)".to_string(),
            Self::Structural(param) => format!("checked (structural on {param})"),
            Self::Assumed => "trusted (source assumption)".to_string(),
            Self::Ranking { edges, obligations } => format!(
                "ranking: {obligations} obligation(s) over {edges} recursive edge(s); \
                 discharge with prism verify"
            ),
            Self::Pending(reason) => format!("pending: {reason}"),
        }
    }
}

/// The `dump totality` rendering: one line per claimed function, honest badge.
pub(crate) fn render(prog: &Program) -> String {
    let results = check(prog);
    if results.is_empty() {
        return "no totality claims\n".to_string();
    }
    let mut out = String::new();
    for f in &results {
        out.push_str("  ");
        out.push_str(&f.name);
        out.push_str(": ");
        out.push_str(&f.status.badge());
        out.push('\n');
    }
    out
}

/// Check every `total`/`assume total` function in `prog`, in callee-first order.
pub(crate) fn check(prog: &Program) -> Vec<FnTotality> {
    let ctx = Ctx::new(prog);
    let sccs = tarjan_scc(&ctx.adj);

    // Ranking analyses for every `total fn` carrying a `decreases` measure, by name.
    // Solver-free here: a well-formed measure yields obligations awaiting discharge,
    // never a proof, so a measured function never joins the `certified` set below.
    let rankings: BTreeMap<String, RankStatus> = ranking::generate(prog)
        .into_iter()
        .map(|f| (f.name, f.status))
        .collect();

    // Certified-total function indices, filled callee-first so a caller sees its
    // callees' verdicts. A constructor is total by construction and lives outside
    // this set (handled in the body walk).
    let mut certified: BTreeSet<usize> = BTreeSet::new();
    let mut verdicts: BTreeMap<usize, Status> = BTreeMap::new();

    for scc in &sccs {
        let mutual = scc.len() > 1;
        for &i in scc {
            let d = &prog.fns[i];
            let claim = d.total;
            if claim == Total::No {
                continue;
            }
            if claim == Total::Assume {
                certified.insert(i);
                verdicts.insert(i, Status::Assumed);
                continue;
            }
            let self_rec = ctx.adj[i].contains(&i);
            let status = if mutual {
                // Mutual recursion needs one SCC-wide measure; a per-member ranking
                // would be unsound, so it stays pending even with a `decreases`.
                Status::Pending("mutual recursion is not supported yet".into())
            } else if d.decreases.is_some() {
                ranking_status(&rankings, &d.name)
            } else if self_rec {
                ctx.structural(prog, i, &certified)
            } else {
                ctx.trivial(prog, i, &certified)
            };
            if matches!(status, Status::Trivial | Status::Structural(_)) {
                certified.insert(i);
            }
            verdicts.insert(i, status);
        }
    }

    // Report in source order for a stable, readable dump.
    prog.fns
        .iter()
        .enumerate()
        .filter_map(|(i, d)| {
            verdicts.remove(&i).map(|status| FnTotality {
                name: d.name.clone(),
                status,
            })
        })
        .collect()
}

/// Map a function's ranking analysis onto its (solver-free) totality badge.
fn ranking_status(rankings: &BTreeMap<String, RankStatus>, name: &str) -> Status {
    match rankings.get(name) {
        Some(RankStatus::Obligations { edges, obligations }) => Status::Ranking {
            edges: *edges,
            obligations: obligations.len(),
        },
        Some(RankStatus::Pending(reason)) => Status::Pending(reason.clone()),
        // Every `total fn` with a `decreases` measure is analyzed, so a miss can
        // only be an internal desync; report it honestly rather than certifying.
        None => Status::Pending("the ranking measure was not analyzed".into()),
    }
}

struct Ctx<'a> {
    ctors: BTreeSet<&'a str>,
    effect_ops: BTreeSet<&'a str>,
    fn_index: BTreeMap<&'a str, usize>,
    // Call graph over top-level functions, successors in increasing index order.
    adj: Vec<Vec<usize>>,
}

impl<'a> Ctx<'a> {
    fn new(prog: &'a Program) -> Self {
        let ctors = prog
            .types
            .iter()
            .flat_map(|t| t.ctors.iter().map(|c| c.name.as_str()))
            .collect();
        let effect_ops = prog
            .effects
            .iter()
            .flat_map(|e| e.ops.iter().map(|o| o.name.as_str()))
            .collect();
        let fn_index: BTreeMap<&str, usize> = prog
            .fns
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.as_str(), i))
            .collect();
        let mut adj = vec![Vec::new(); prog.fns.len()];
        for (i, d) in prog.fns.iter().enumerate() {
            let mut names = BTreeSet::new();
            collect_fn_calls(&d.body, &fn_index, &mut names);
            adj[i] = names
                .iter()
                .filter_map(|n| fn_index.get(n.as_str()).copied())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
        }
        Self {
            ctors,
            effect_ops,
            fn_index,
            adj,
        }
    }

    /// Acyclic function, total-fragment body, every called function certified.
    fn trivial(&self, prog: &Program, i: usize, certified: &BTreeSet<usize>) -> Status {
        let d = &prog.fns[i];
        let mut callees = BTreeSet::new();
        if let Err(reason) = self.body_ok(&d.body, &mut callees) {
            return Status::Pending(reason);
        }
        for callee in &callees {
            let idx = self.fn_index[callee.as_str()];
            if !certified.contains(&idx) {
                return Status::Pending(format!("calls `{callee}`, which is not certified total"));
            }
        }
        Status::Trivial
    }

    /// Single self-recursive function; every recursive call must pass a strict
    /// subterm of one matched parameter in that parameter's position.
    fn structural(&self, prog: &Program, i: usize, certified: &BTreeSet<usize>) -> Status {
        let d = &prog.fns[i];
        // Non-recursive callees must still be certified total (the recursive call
        // to self is allowed within the SCC).
        let mut callees = BTreeSet::new();
        if let Err(reason) = self.body_ok(&d.body, &mut callees) {
            return Status::Pending(reason);
        }
        for callee in &callees {
            if callee == &d.name {
                continue;
            }
            let idx = self.fn_index[callee.as_str()];
            if !certified.contains(&idx) {
                return Status::Pending(format!("calls `{callee}`, which is not certified total"));
            }
        }
        // Try each parameter position as the structural argument.
        for (p, param) in d.params.iter().enumerate() {
            let mut ok = true;
            let mut saw_recursive = false;
            let subterms = BTreeSet::new();
            check_descent(
                &d.body,
                &d.name,
                p,
                &param.name,
                &subterms,
                &mut ok,
                &mut saw_recursive,
            );
            if ok && saw_recursive {
                return Status::Structural(param.name.clone());
            }
        }
        Status::Pending(
            "a recursive call does not consume a strict subterm of any matched parameter".into(),
        )
    }

    /// Walk a body for the total fragment, collecting the top-level functions it
    /// calls. Returns the first unsupported construct as a pending reason.
    fn body_ok(&self, e: &S<Expr>, callees: &mut BTreeSet<String>) -> Result<(), String> {
        match &e.node {
            Expr::Int(_)
            | Expr::Bool(_)
            | Expr::Unit
            | Expr::Var(_)
            | Expr::Float(_)
            | Expr::Char(_)
            | Expr::Str(_) => Ok(()),
            Expr::Bin(op, l, r) => {
                total_binop(*op)?;
                self.body_ok(l, callees)?;
                self.body_ok(r, callees)
            }
            Expr::If(c, t, e2) => {
                self.body_ok(c, callees)?;
                self.body_ok(t, callees)?;
                self.body_ok(e2, callees)
            }
            Expr::Let(_, v, b) => {
                self.body_ok(v, callees)?;
                self.body_ok(b, callees)
            }
            Expr::Match(scrut, arms) => {
                self.body_ok(scrut, callees)?;
                for arm in arms {
                    self.body_ok(&arm.body, callees)?;
                }
                Ok(())
            }
            Expr::Tuple(xs) | Expr::List(xs) | Expr::UnboxedTuple(xs) => {
                for x in xs {
                    self.body_ok(x, callees)?;
                }
                Ok(())
            }
            Expr::RecordCreate(_, fs) | Expr::UnboxedRecord(fs) => {
                for (_, x) in fs {
                    self.body_ok(x, callees)?;
                }
                Ok(())
            }
            Expr::Neg(x)
            | Expr::FieldAccess(x, _)
            | Expr::UnboxedField(x, _)
            | Expr::Inst(x, _)
            | Expr::Ann(x, _) => self.body_ok(x, callees),
            Expr::Call(f, args) => {
                let Expr::Var(name) = &f.node else {
                    return Err("performs a higher-order or indirect call".into());
                };
                if self.effect_ops.contains(name.as_str()) {
                    return Err(format!("performs the effect operation `{name}`"));
                }
                if self.fn_index.contains_key(name.as_str()) {
                    callees.insert(name.clone());
                } else if !self.ctors.contains(name.as_str()) {
                    return Err(format!("calls `{name}`, which has no known totality"));
                }
                for a in args {
                    self.body_ok(a, callees)?;
                }
                Ok(())
            }
            Expr::Lam(..) => Err("contains a lambda".into()),
            Expr::Handle(..) => Err("installs an effect handler".into()),
            Expr::Mask(..) => Err("masks an effect".into()),
            Expr::Hole(_) => Err("contains a typed hole".into()),
            Expr::Index(..) | Expr::IndexSet(..) => Err("performs a partial index".into()),
            Expr::Pipe(..) => Err("uses a pipeline (unsupported in the first fragment)".into()),
            Expr::RecordUpdate(..) | Expr::RecordUpdatePath(..) => {
                Err("performs a functional update (unsupported in the first fragment)".into())
            }
            Expr::Sugar(_) | Expr::Marker(_) => Err("uses mutable state or unlowered sugar".into()),
        }
    }
}

/// Collect the names of top-level functions called anywhere in `e` (constructors
/// and effect ops are not functions and are skipped). Used to build the call
/// graph; eligibility is a separate, stricter walk.
fn collect_fn_calls(e: &S<Expr>, fns: &BTreeMap<&str, usize>, out: &mut BTreeSet<String>) {
    if let Expr::Var(name) = &e.node {
        if fns.contains_key(name.as_str()) {
            out.insert(name.clone());
        }
    }
    e.node.each_child(&mut |c| collect_fn_calls(c, fns, out));
}

/// The arithmetic/logic operators that always terminate without a fault. Division
/// and remainder are partial (fault on a zero divisor) and exponentiation is left
/// for review, so they stay pending in the first fragment.
fn total_binop(op: BinOp) -> Result<(), String> {
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Eq
        | BinOp::Ne
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::And
        | BinOp::Or => Ok(()),
        BinOp::Div | BinOp::Rem => {
            Err("uses `/` or `%`, a partial primitive (needs a definedness proof)".into())
        }
        BinOp::Pow => Err("uses `^`, whose totality is not yet established".into()),
    }
}

/// Structural-descent check for parameter `p` (name `param`) of self-recursive
/// `name`. `subterms` are binders known to be strict subterms of `param` in the
/// current scope. Clears `ok` if any recursive call fails to pass a subterm in
/// position `p`; sets `saw_recursive` if a recursive call was seen at all.
fn check_descent(
    e: &S<Expr>,
    name: &str,
    p: usize,
    param: &str,
    subterms: &BTreeSet<String>,
    ok: &mut bool,
    saw_recursive: &mut bool,
) {
    match &e.node {
        Expr::Call(f, args) => {
            if let Expr::Var(callee) = &f.node {
                if callee == name {
                    *saw_recursive = true;
                    match args.get(p).map(|a| &a.node) {
                        Some(Expr::Var(arg)) if subterms.contains(arg) => {}
                        _ => *ok = false,
                    }
                }
            }
            for a in args {
                check_descent(a, name, p, param, subterms, ok, saw_recursive);
            }
            check_descent(f, name, p, param, subterms, ok, saw_recursive);
        }
        Expr::Let(binder, value, body) => {
            // The bound value is evaluated in the enclosing scope.
            check_descent(value, name, p, param, subterms, ok, saw_recursive);
            // The binder shadows any same-named strict subterm inside the body, and
            // the let-bound value is not itself tracked as a strict subterm, so drop
            // the name before descending. Without this, `let m = param in name(m)`
            // recurs on the whole parameter yet would pass as if `m` were a subterm.
            let mut inner = subterms.clone();
            inner.remove(binder);
            check_descent(body, name, p, param, &inner, ok, saw_recursive);
        }
        Expr::Match(scrut, arms) => {
            check_descent(scrut, name, p, param, subterms, ok, saw_recursive);
            // Matching the parameter (or a known subterm of it) binds the matched
            // constructor's fields as strict subterms within each arm.
            let on_param =
                matches!(&scrut.node, Expr::Var(v) if v == param || subterms.contains(v));
            for arm in arms {
                // A pattern binder shadows any same-named outer strict subterm, so
                // drop every name the pattern rebinds first. Only then, and only when
                // matching on the tracked parameter, are the constructor fields
                // re-added as fresh strict subterms. A binder that shadows a subterm
                // without descending under a constructor (a bare `Var` pattern, or a
                // field of an unrelated scrutinee) is thereby no longer trusted.
                let mut inner = subterms.clone();
                remove_pattern_binders(&arm.pat, &mut inner);
                if on_param {
                    add_pattern_subterms(&arm.pat, &mut inner);
                }
                check_descent(&arm.body, name, p, param, &inner, ok, saw_recursive);
            }
        }
        _ => e
            .node
            .each_child(&mut |c| check_descent(c, name, p, param, subterms, ok, saw_recursive)),
    }
}

/// Add the binders introduced *inside* a constructor/tuple/record pattern as
/// strict subterms. A bare `Var` pattern binds the whole scrutinee, not a strict
/// subterm, so it is deliberately not added.
fn add_pattern_subterms(pat: &S<Pattern>, out: &mut BTreeSet<String>) {
    match &pat.node {
        Pattern::Ctor(_, fields) | Pattern::Tuple(fields) => {
            for f in fields {
                add_binders(f, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, f) in fields {
                add_binders(f, out);
            }
        }
        _ => {}
    }
}

/// Remove every name a pattern binds from the strict-subterm set, at any depth.
/// A rebind shadows the outer name, so a same-named subterm must stop being
/// trusted for the arm's scope before the constructor fields (if any) are re-added.
fn remove_pattern_binders(pat: &S<Pattern>, out: &mut BTreeSet<String>) {
    match &pat.node {
        Pattern::Var(v) => {
            out.remove(v);
        }
        Pattern::Ctor(_, fields) | Pattern::Tuple(fields) => {
            for f in fields {
                remove_pattern_binders(f, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, f) in fields {
                remove_pattern_binders(f, out);
            }
        }
        _ => {}
    }
}

/// Every `Var` binder anywhere within `pat` (already known to sit under a
/// constructor), so nested destructuring still yields strict subterms.
fn add_binders(pat: &S<Pattern>, out: &mut BTreeSet<String>) {
    match &pat.node {
        Pattern::Var(v) => {
            out.insert(v.clone());
        }
        Pattern::Ctor(_, fields) | Pattern::Tuple(fields) => {
            for f in fields {
                add_binders(f, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for (_, f) in fields {
                add_binders(f, out);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::dump;

    // A recursive call certifies structural only when it consumes a strict subterm
    // of a matched parameter. A binder that reuses a tracked subterm's name but
    // rebinds it to the whole parameter must not be trusted as a subterm: the
    // recursion does not shrink and the function does not terminate.
    #[test]
    fn shadowed_match_binder_is_not_structural() {
        // `S(m)` binds `m` as a strict subterm of `n`; the inner match rebinds `m`
        // to `n` itself (the field of `S(n)`), so `loops(m)` recurs on the whole
        // parameter.
        let src = "\
type Nat = Z | S(Nat)

total fn loops(n: Nat): Int =
  match n of
    Z => 0
    S(m) =>
      match S(n) of
        Z => 0
        S(m) => loops(m)
";
        let out = dump("totality", src).expect("dump totality");
        assert!(
            out.contains("loops: pending:"),
            "a shadowed subterm must not certify structural:\n{out}"
        );
        assert!(
            !out.contains("loops: checked"),
            "non-terminating recursion must never be checked total:\n{out}"
        );
    }

    // The same hazard through a `let` binder: `let m = n` shadows the subterm `m`
    // and rebinds it to the whole parameter.
    #[test]
    fn shadowed_let_binder_is_not_structural() {
        let src = "\
type Nat = Z | S(Nat)

total fn loops(n: Nat): Int =
  match n of
    Z => 0
    S(m) =>
      let m = n
      loops(m)
";
        let out = dump("totality", src).expect("dump totality");
        assert!(
            out.contains("loops: pending:"),
            "a shadowing let must not certify structural:\n{out}"
        );
        assert!(
            !out.contains("loops: checked"),
            "non-terminating recursion must never be checked total:\n{out}"
        );
    }

    // A genuine structural recursion (no shadowing) still certifies total, so the
    // shadowing guard did not over-restrict the checker.
    #[test]
    fn genuine_structural_recursion_still_certifies() {
        let src = "\
type Nat = Z | S(Nat)

total fn depth(n: Nat): Int =
  match n of
    Z => 0
    S(m) => 1 + depth(m)
";
        let out = dump("totality", src).expect("dump totality");
        assert!(
            out.contains("depth: checked (structural on n)"),
            "structural recursion must still certify:\n{out}"
        );
    }
}
