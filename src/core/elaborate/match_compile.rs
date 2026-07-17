use std::slice;

use super::{
    pat_vars, rebind, small_int, spanned, Arm, BTreeMap, BigInt, Builtin, Comp, CoreOp, CorePat,
    CorePhase, CtorInfo, Elab, Error, Locals, NodeId, Pattern, Span, Spanned, Sym, Value, S,
};

// Convert a shallow surface pattern (the residual after match compilation, whose
// ctor/tuple fields are always plain binders) into a core pattern. Literal and
// record patterns are compiled into tests upstream and never reach a `Case` arm.
fn core_pat(p: &Pattern) -> CorePat {
    match p {
        Pattern::Var(x) => CorePat::Var(Sym::from(x)),
        Pattern::Ctor(n, subs) => {
            CorePat::Ctor(Sym::from(n), subs.iter().map(field_binder).collect())
        }
        Pattern::Tuple(subs) => CorePat::Tuple(subs.iter().map(field_binder).collect()),
        _ => CorePat::Wild,
    }
}

// A ctor/tuple field position: `Some` names it, `None` ignores it.
fn field_binder(p: &S<Pattern>) -> Option<Sym> {
    match &p.node {
        Pattern::Var(x) => Some(Sym::from(x)),
        _ => None,
    }
}

// Field binders that all bind (none ignored).
fn binders(fvs: &[String]) -> Vec<Option<Sym>> {
    fvs.iter().map(|n| Some(Sym::from(n))).collect()
}

impl Elab<'_> {
    pub(super) fn compile_match(
        &mut self,
        scrut: Value,
        arms: Vec<(Pattern, Comp)>,
    ) -> Result<Comp, Error> {
        if arms.is_empty() {
            return Err(Error::InternalInvariant(
                "compile_match: empty match survived exhaustiveness".into(),
            ));
        }
        if !arms.iter().any(|(p, _)| pattern_needs_compile(p)) {
            return Ok(Comp::Case(
                scrut,
                arms.into_iter().map(|(p, b)| (core_pat(&p), b)).collect(),
            ));
        }
        let (v, wrap): (String, _) = match &scrut {
            Value::Var(x) => (x.to_string(), None),
            other => (self.fresh(), Some(other.clone())),
        };
        let col_arms = arms
            .into_iter()
            .map(|(p, b)| (vec![spanned(p)], b))
            .collect();
        let body = self.compile_sub_arms(slice::from_ref(&v), col_arms, None)?;
        Ok(match wrap {
            Some(s) => Comp::Bind(Box::new(Comp::Return(s)), v.into(), Box::new(body)),
            None => body,
        })
    }

    pub(super) fn flat_pat(&self, p: &S<Pattern>) -> Pattern {
        match &p.node {
            Pattern::Record(n, fs, sp) => desugar_record_pat(self.ctors, n, fs, *sp),
            other => other.clone(),
        }
    }

    // Fresh names for a guarded arm's pattern vars: the else path re-matches
    // the scrutinee against the remaining arms, so the user's names must stay
    // scoped to the guard and body or they would shadow the rest's bindings.
    pub(super) fn freshen(&mut self, p: &Pattern, map: &mut Vec<(String, String)>) -> Pattern {
        let subs = |me: &mut Self, ps: &[S<Pattern>], map: &mut Vec<(String, String)>| {
            ps.iter()
                .map(|s| spanned(me.freshen(&s.node, map)))
                .collect()
        };
        match p {
            Pattern::Var(x) => {
                let f = self.fresh();
                map.push((x.clone(), f.clone()));
                Pattern::Var(f)
            }
            Pattern::Ctor(n, ps) => Pattern::Ctor(n.clone(), subs(self, ps, map)),
            Pattern::Tuple(ps) => Pattern::Tuple(subs(self, ps, map)),
            other => other.clone(),
        }
    }

    // A guarded arm compiles to `if cond then body else rest`, where rest
    // re-matches the scrutinee against the remaining arms; a wildcard catchall
    // routes values the guarded pattern rejects to the same rest. Coverage has
    // proven the unguarded arms exhaustive, so the defensive wildcard on a
    // nested rest is dead code that only keeps the decision tree total.
    pub(super) fn elab_arms(
        &mut self,
        vs: &str,
        arms: &[Arm<CorePhase>],
        locals: &Locals,
        nested: bool,
    ) -> Result<Comp, Error> {
        let unreachable = || Comp::Error(Value::Str("ICE: guarded match fell through".into()));
        let cut = arms
            .iter()
            .position(|a| a.guard.is_some())
            .unwrap_or(arms.len());
        let mut cases = Vec::new();
        for arm in &arms[..cut] {
            let mut l2 = locals.clone();
            pat_vars(&arm.pat, &mut l2);
            cases.push((self.flat_pat(&arm.pat), self.elab(&arm.body, &l2)?));
        }
        let mut join: Option<(Sym, Comp)> = None;
        if let Some(arm) = arms.get(cut) {
            let rest = self.elab_arms(vs, &arms[cut + 1..], locals, true)?;
            let mut l2 = locals.clone();
            pat_vars(&arm.pat, &mut l2);
            let Some(g) = arm.guard.as_ref() else {
                return Err(Error::InternalInvariant("cut marks a guarded arm".into()));
            };
            let cg = self.elab(g, &l2)?;
            let cb = self.elab(&arm.body, &l2)?;
            let flat = self.flat_pat(&arm.pat);
            let mut map = Vec::new();
            let pat = self.freshen(&flat, &mut map);
            let gv = self.fresh();
            // The fallthrough `rest` lands in two positions: the guard's `else`
            // and the wildcard arm that routes pattern-rejects. When the guarded
            // arm's own pattern is refutable it splits into a matching branch
            // (whose guard-`else` holds `rest`) and leaves a surviving wildcard
            // default (also `rest`), so N such arms clone the fallthrough into 2^N
            // copies. Bind it once as a nullary join point (a thunk over a
            // zero-parameter lambda closing over the ambient scope) and reach it
            // by forcing and applying that closure to no arguments from each
            // position, turning the copies into O(1) references. The nullary
            // lambda matters for the native backend: codegen realizes every thunk
            // as a closure invoked through `prismap_n`, so an arity-0 lambda
            // applied to zero arguments is a shape it already lowers, whereas a
            // thunk directly wrapping a general computation is not. Beta on the
            // empty argument list makes this observably identical to running
            // `rest` inline, so the interpreter and effect lowering are
            // unaffected. An irrefutable pattern instead folds the guarded arm and
            // the wildcard into one trivial group that match compilation collapses
            // to a single `rest`, so there we emit it inline exactly as before and
            // nothing churns.
            let dup = !is_trivial_pat(&pat);
            let force_join = |j: Sym| Comp::App(Box::new(Comp::Force(Value::Var(j))), Vec::new());
            let (else_br, wild_br) = if dup {
                let j: Sym = self.fresh().into();
                join = Some((j, rest));
                (force_join(j), force_join(j))
            } else {
                (rest.clone(), rest)
            };
            let test = Comp::If(
                Value::Var(gv.clone().into()),
                Box::new(rebind(&map, cb)),
                Box::new(else_br),
            );
            cases.push((
                pat,
                Comp::Bind(Box::new(rebind(&map, cg)), gv.into(), Box::new(test)),
            ));
            cases.push((Pattern::Wild, wild_br));
        } else if nested && !matches!(cases.last(), Some((Pattern::Wild | Pattern::Var(_), _))) {
            // A nested rest runs only because an outer guard failed, never
            // because its scrutinee escaped coverage. Its unguarded arms are
            // exhaustive, so this filler wildcard is dead; it exists only to keep
            // the decision tree total.
            cases.push((Pattern::Wild, unreachable()));
        }
        if cases.is_empty() {
            return Ok(unreachable());
        }
        let tree = self.compile_match(Value::Var(vs.into()), cases)?;
        Ok(match join {
            Some((j, rest)) => Comp::Bind(
                Box::new(Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                    Vec::new(),
                    Box::new(rest),
                ))))),
                j,
                Box::new(tree),
            ),
            None => tree,
        })
    }

    pub(super) fn fresh_fields(&mut self, n: usize) -> Vec<String> {
        (0..n).map(|_| self.fresh()).collect()
    }

    pub(super) fn compile_sub_arms(
        &mut self,
        field_vars: &[String],
        arms: Vec<(Vec<S<Pattern>>, Comp)>,
        default: Option<Comp>,
    ) -> Result<Comp, Error> {
        if arms.is_empty() {
            return default.ok_or_else(|| {
                Error::InternalInvariant(
                    "compile_sub_arms: empty arm matrix survived exhaustiveness".into(),
                )
            });
        }

        let all_trivial = arms.iter().all(|(subs, _)| {
            subs.iter()
                .all(|p| matches!(p.node, Pattern::Wild | Pattern::Var(_)))
        });

        if all_trivial {
            let (subs, body) = arms.into_iter().next().ok_or_else(|| {
                Error::InternalInvariant("empty arm group survived the is_empty guard".into())
            })?;
            return Ok(bind_fields(field_vars, &subs, body));
        }

        let col = (0..field_vars.len())
            .find(|&c| {
                arms.iter().any(|(subs, _)| {
                    subs.get(c)
                        .is_some_and(|p| !matches!(p.node, Pattern::Wild | Pattern::Var(_)))
                })
            })
            .ok_or_else(|| {
                Error::InternalInvariant("all_trivial guard guarantees a non-trivial column".into())
            })?;

        let col_scrut = Value::Var(field_vars[col].clone().into());
        let mut part = self.partition_arms(arms.clone(), col)?;

        // Wildcard/variable rows (column retained, so a `Var` still binds the
        // scrutinee) form the Case's `Wild` arm and the scalar chain's final
        // `else`: the rows that apply once no listed constructor/literal matched.
        let wild = std::mem::take(&mut part.wild);
        let col_default = if wild.is_empty() {
            default.clone()
        } else {
            Some(self.compile_sub_arms(field_vars, wild, default.clone())?)
        };

        // A wildcard also matches every listed head, so `specialize` (in the emit
        // helpers) folds these rows into each branch IN SOURCE ORDER; that is what
        // keeps first-match semantics when a wildcard arm precedes a constructor or
        // literal arm. Scalar (bool/int/float/char) columns test the value
        // directly; ctor/tuple columns destructure through a Case. The two never
        // mix in one column because coverage groups same-typed patterns together.
        if part.has_bool || !part.lits.is_empty() {
            self.emit_scalar_column(
                &part,
                &arms,
                field_vars,
                col,
                &col_scrut,
                default.as_ref(),
                col_default,
            )
        } else {
            self.emit_case_column(
                &part,
                &arms,
                field_vars,
                col,
                col_scrut,
                default,
                col_default,
            )
        }
    }

    // Bucket the active column's arms by head-pattern kind, rewriting each row's
    // column for the chosen branch (expand for ctor/tuple, drop for scalars).
    pub(super) fn partition_arms(
        &self,
        arms: Vec<ArmRow>,
        col: usize,
    ) -> Result<ArmPartition, Error> {
        let mut part = ArmPartition::default();
        for (subs, body) in arms {
            let mut node = subs[col].node.clone();
            if let Pattern::Record(n, fs, sp) = node {
                node = desugar_record_pat(self.ctors, &n, &fs, sp);
            }
            match node {
                Pattern::Ctor(name, sub_subs) => part
                    .ctors
                    .entry(name)
                    .or_default()
                    .push((expand_col(&subs, col, &sub_subs), body)),
                Pattern::Tuple(sub_subs) => {
                    part.tuple_arity = sub_subs.len();
                    part.tuple.push((expand_col(&subs, col, &sub_subs), body));
                }
                Pattern::Int(lit) => {
                    push_lit(
                        &mut part.lits,
                        Lit::Int(lit.value),
                        drop_col(&subs, col),
                        body,
                    );
                }
                Pattern::Float(f) => {
                    push_lit(&mut part.lits, Lit::Float(f), drop_col(&subs, col), body);
                }
                Pattern::Char(c) => push_lit(
                    &mut part.lits,
                    Lit::Int(BigInt::from(u32::from(c))),
                    drop_col(&subs, col),
                    body,
                ),
                Pattern::Bool(b) => {
                    part.has_bool = true;
                    part.bools[usize::from(b)].push((drop_col(&subs, col), body));
                }
                Pattern::Wild | Pattern::Var(_) => part.wild.push((subs, body)),
                Pattern::Record(..) => {
                    return Err(Error::InternalInvariant(
                        "desugar_record_pat returned a record pattern".into(),
                    ))
                }
            }
        }
        Ok(part)
    }

    // Build one branch's sub-matrix in source order. A row whose column head is a
    // wildcard or variable matches every value, so it belongs in EVERY branch: it
    // is always included, its column expanded with `wild_fill` fresh wildcards
    // (0 drops the column, as a scalar branch tests the value directly), and if it
    // named a variable that variable is bound to the scrutinee. A row with a
    // concrete head is included only when `head_match` accepts it, using the
    // sub-patterns it returns for the expansion.
    fn specialize(
        &self,
        arms: &[ArmRow],
        col: usize,
        col_scrut: &Value,
        wild_fill: usize,
        mut head_match: impl FnMut(&Pattern) -> Option<Vec<S<Pattern>>>,
    ) -> Vec<ArmRow> {
        let mut out = Vec::new();
        for (subs, body) in arms {
            match self.flat_pat(&subs[col]) {
                Pattern::Wild => {
                    out.push((
                        expand_col(subs, col, &vec![wild_pat(); wild_fill]),
                        body.clone(),
                    ));
                }
                Pattern::Var(x) => out.push((
                    expand_col(subs, col, &vec![wild_pat(); wild_fill]),
                    bind_col_var(body.clone(), &x, col_scrut),
                )),
                other => {
                    if let Some(ss) = head_match(&other) {
                        out.push((expand_col(subs, col, &ss), body.clone()));
                    }
                }
            }
        }
        out
    }

    // A bool column becomes one If. An int/float/char column becomes a chain of
    // equality tests, built innermost-first so the source order is preserved. Each
    // value's sub-matrix is `specialize`d from the full ordered rows so preceding
    // wildcard arms are tried in their real position.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_scalar_column(
        &mut self,
        part: &ArmPartition,
        arms: &[ArmRow],
        field_vars: &[String],
        col: usize,
        col_scrut: &Value,
        default: Option<&Comp>,
        col_default: Option<Comp>,
    ) -> Result<Comp, Error> {
        let mut rest_vars = field_vars.to_vec();
        rest_vars.remove(col);
        let ice = || {
            Error::InternalInvariant("scalar column without default survived exhaustiveness".into())
        };
        if part.has_bool {
            let side = |me: &mut Self, want: bool| -> Result<Comp, Error> {
                let group = me.specialize(arms, col, col_scrut, 0, |p| match p {
                    Pattern::Bool(b) if *b == want => Some(Vec::new()),
                    _ => None,
                });
                if group.is_empty() {
                    col_default.clone().ok_or_else(ice)
                } else {
                    me.compile_sub_arms(&rest_vars, group, default.cloned())
                }
            };
            let t = side(self, true)?;
            let f = side(self, false)?;
            return Ok(Comp::If(col_scrut.clone(), Box::new(t), Box::new(f)));
        }
        let mut acc = col_default.ok_or_else(ice)?;
        for (lit, _) in part.lits.iter().rev() {
            let group = self.specialize(arms, col, col_scrut, 0, |p| {
                if lit_matches(p, lit) {
                    Some(Vec::new())
                } else {
                    None
                }
            });
            let body = self.compile_sub_arms(&rest_vars, group, default.cloned())?;
            let t = self.fresh();
            let (eq, pre) = match lit {
                Lit::Float(f) => (
                    Comp::Prim(CoreOp::Eqf, col_scrut.clone(), Value::Float(*f)),
                    None,
                ),
                Lit::Int(n) => small_int(n).map_or_else(
                    || {
                        let tmp = self.fresh();
                        let parse =
                            Comp::StrBuiltin(Builtin::BigLit, vec![Value::Str(n.to_string())]);
                        (
                            Comp::Prim(
                                CoreOp::Eq,
                                col_scrut.clone(),
                                Value::Var(tmp.clone().into()),
                            ),
                            Some((tmp, parse)),
                        )
                    },
                    |v| {
                        (
                            Comp::Prim(CoreOp::Eq, col_scrut.clone(), Value::Int(v)),
                            None,
                        )
                    },
                ),
            };
            acc = Comp::Bind(
                Box::new(eq),
                t.clone().into(),
                Box::new(Comp::If(
                    Value::Var(t.into()),
                    Box::new(body),
                    Box::new(acc),
                )),
            );
            if let Some((tmp, parse)) = pre {
                acc = Comp::Bind(Box::new(parse), tmp.into(), Box::new(acc));
            }
        }
        Ok(acc)
    }

    // Emit a Case: one arm per ctor, then a tuple arm or wildcard default. Each
    // ctor/tuple arm's sub-matrix is `specialize`d from the full ordered rows, so
    // a wildcard arm preceding a constructor arm still wins first-match; the Wild
    // arm carries the wildcard-only default for any unlisted constructor.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_case_column(
        &mut self,
        part: &ArmPartition,
        arms: &[ArmRow],
        field_vars: &[String],
        col: usize,
        col_scrut: Value,
        default: Option<Comp>,
        col_default: Option<Comp>,
    ) -> Result<Comp, Error> {
        let mut sub_case_arms: Vec<(CorePat, Comp)> = Vec::new();
        for sub_ctor in part.ctors.keys() {
            let n_sub = self.ctors.get(sub_ctor).map_or(0, |info| info.args.len());
            let sub_fvs = self.fresh_fields(n_sub);
            let new_field_vars = splice_vars(field_vars, col, &sub_fvs);
            let group = self.specialize(arms, col, &col_scrut, n_sub, |p| match p {
                Pattern::Ctor(name, ss) if name == sub_ctor => Some(ss.clone()),
                _ => None,
            });
            let sub_body = self.compile_sub_arms(&new_field_vars, group, default.clone())?;
            sub_case_arms.push((
                CorePat::Ctor(Sym::from(sub_ctor), binders(&sub_fvs)),
                sub_body,
            ));
        }

        if part.tuple.is_empty() {
            if let Some(def) = col_default {
                sub_case_arms.push((CorePat::Wild, def));
            }
        } else {
            let arity = part.tuple_arity;
            let sub_fvs = self.fresh_fields(arity);
            let new_field_vars = splice_vars(field_vars, col, &sub_fvs);
            let group = self.specialize(arms, col, &col_scrut, arity, |p| match p {
                Pattern::Tuple(ss) => Some(ss.clone()),
                _ => None,
            });
            let sub_body = self.compile_sub_arms(&new_field_vars, group, default)?;
            sub_case_arms.push((CorePat::Tuple(binders(&sub_fvs)), sub_body));
        }

        Ok(Comp::Case(col_scrut, sub_case_arms))
    }
}

pub(super) fn desugar_record_pat(
    ctors: &BTreeMap<String, CtorInfo>,
    ctor_name: &str,
    fields: &[(String, S<Pattern>)],
    spread: bool,
) -> Pattern {
    let Some(info) = ctors.get(ctor_name) else {
        return Pattern::Wild;
    };
    let n = info.args.len();
    let mut subs: Vec<S<Pattern>> = (0..n)
        .map(|_| Spanned {
            id: NodeId::DUMMY,
            synth: false,
            node: Pattern::Wild,
            span: Span::new(0, 0),
        })
        .collect();
    for (fname, fpat) in fields {
        if let Some(fi) = info.fields.iter().position(|f| f.as_str() == fname) {
            subs[fi] = fpat.clone();
        }
    }
    let _ = spread;
    Pattern::Ctor(ctor_name.to_string(), subs)
}

// An irrefutable column head: it matches every value and binds nothing that
// forces a test. A match whose every arm head is trivial collapses to its first
// arm downstream (the wildcard fallthrough arm is dropped), so a guarded arm
// under such a column has a single-use fallthrough and needs no join point.
const fn is_trivial_pat(p: &Pattern) -> bool {
    matches!(p, Pattern::Wild | Pattern::Var(_))
}

pub(super) fn pattern_needs_compile(p: &Pattern) -> bool {
    match p {
        Pattern::Ctor(_, subs) | Pattern::Tuple(subs) => subs
            .iter()
            .any(|s| !matches!(s.node, Pattern::Wild | Pattern::Var(_))),
        Pattern::Int(_) | Pattern::Float(_) | Pattern::Char(_) | Pattern::Bool(_) => true,
        _ => false,
    }
}

// A fresh wildcard sub-pattern, used to fill a destructured column for a
// wildcard/variable row specialized into a constructor/tuple branch.
const fn wild_pat() -> S<Pattern> {
    spanned(Pattern::Wild)
}

// When a `Var(x)` row is specialized into a column that is destructured (ctor,
// tuple) or dropped (scalar), `x` no longer binds through the column, so bind it
// to the whole matched value here.
fn bind_col_var(body: Comp, x: &str, col_scrut: &Value) -> Comp {
    Comp::Bind(
        Box::new(Comp::Return(col_scrut.clone())),
        Sym::from(x),
        Box::new(body),
    )
}

// Whether a concrete scalar pattern is the literal `key` (grouped exactly as
// `partition_arms` groups them: char folds into its codepoint as an Int).
fn lit_matches(p: &Pattern, key: &Lit) -> bool {
    match (p, key) {
        (Pattern::Int(l), Lit::Int(n)) => &l.value == n,
        (Pattern::Char(c), Lit::Int(n)) => &BigInt::from(u32::from(*c)) == n,
        (Pattern::Float(f), Lit::Float(g)) => f.to_bits() == g.to_bits(),
        _ => false,
    }
}

fn expand_col(subs: &[S<Pattern>], col: usize, sub_subs: &[S<Pattern>]) -> Vec<S<Pattern>> {
    let mut out = subs.to_vec();
    out.remove(col);
    for (i, ss) in sub_subs.iter().enumerate() {
        out.insert(col + i, ss.clone());
    }
    out
}

fn drop_col(subs: &[S<Pattern>], col: usize) -> Vec<S<Pattern>> {
    let mut out = subs.to_vec();
    out.remove(col);
    out
}

fn splice_vars(vars: &[String], col: usize, fvs: &[String]) -> Vec<String> {
    let mut out = vars.to_vec();
    out.remove(col);
    for (i, v) in fvs.iter().enumerate() {
        out.insert(col + i, v.clone());
    }
    out
}

enum Lit {
    Int(BigInt),
    Float(f64),
}

// One row of the pattern matrix: the remaining sub-patterns and the arm body.
type ArmRow = (Vec<S<Pattern>>, Comp);

// The active column's arms bucketed by head-pattern kind. Each row has already
// had the active column rewritten: ctor/tuple rows expand it into the field
// columns, literal/bool rows drop it, wildcard rows keep it for the fallback.
#[derive(Default)]
pub(super) struct ArmPartition {
    ctors: BTreeMap<String, Vec<ArmRow>>,
    tuple: Vec<ArmRow>,
    tuple_arity: usize,
    lits: Vec<(Lit, Vec<ArmRow>)>,
    bools: [Vec<ArmRow>; 2],
    has_bool: bool,
    wild: Vec<ArmRow>,
}

#[allow(clippy::type_complexity)]
fn push_lit(
    groups: &mut Vec<(Lit, Vec<(Vec<S<Pattern>>, Comp)>)>,
    lit: Lit,
    subs: Vec<S<Pattern>>,
    body: Comp,
) {
    let same = |a: &Lit| match (a, &lit) {
        (Lit::Int(x), Lit::Int(y)) => x == y,
        (Lit::Float(x), Lit::Float(y)) => x.to_bits() == y.to_bits(),
        _ => false,
    };
    match groups.iter_mut().find(|(k, _)| same(k)) {
        Some((_, g)) => g.push((subs, body)),
        None => groups.push((lit, vec![(subs, body)])),
    }
}

fn bind_fields(field_vars: &[String], pats: &[S<Pattern>], body: Comp) -> Comp {
    let mut result = body;
    for (fv, pat) in field_vars.iter().zip(pats.iter()).rev() {
        if let Pattern::Var(x) = &pat.node {
            result = Comp::Bind(
                Box::new(Comp::Return(Value::Var(fv.clone().into()))),
                x.clone().into(),
                Box::new(result),
            );
        }
    }
    result
}
