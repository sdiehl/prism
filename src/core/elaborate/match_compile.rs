use std::slice;

use super::{
    pat_vars, rebind, small_int, spanned, Arm, BTreeMap, BigInt, Builtin, Comp, CoreOp, CorePat,
    CorePhase, CtorInfo, Elab, Error, Locals, Pattern, Span, Spanned, Sym, Value, S,
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
            return Err(Error::Ice(
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
        if let Some(arm) = arms.get(cut) {
            let rest = self.elab_arms(vs, &arms[cut + 1..], locals, true)?;
            let mut l2 = locals.clone();
            pat_vars(&arm.pat, &mut l2);
            let Some(g) = arm.guard.as_ref() else {
                return Err(Error::Ice("cut marks a guarded arm".into()));
            };
            let cg = self.elab(g, &l2)?;
            let cb = self.elab(&arm.body, &l2)?;
            let flat = self.flat_pat(&arm.pat);
            let mut map = Vec::new();
            let pat = self.freshen(&flat, &mut map);
            let gv = self.fresh();
            let test = Comp::If(
                Value::Var(gv.clone().into()),
                Box::new(rebind(&map, cb)),
                Box::new(rest.clone()),
            );
            cases.push((
                pat,
                Comp::Bind(Box::new(rebind(&map, cg)), gv.into(), Box::new(test)),
            ));
            cases.push((Pattern::Wild, rest));
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
        self.compile_match(Value::Var(vs.into()), cases)
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
                Error::Ice("compile_sub_arms: empty arm matrix survived exhaustiveness".into())
            });
        }

        let all_trivial = arms.iter().all(|(subs, _)| {
            subs.iter()
                .all(|p| matches!(p.node, Pattern::Wild | Pattern::Var(_)))
        });

        if all_trivial {
            let (subs, body) = arms
                .into_iter()
                .next()
                .ok_or_else(|| Error::Ice("empty arm group survived the is_empty guard".into()))?;
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
                Error::Ice("all_trivial guard guarantees a non-trivial column".into())
            })?;

        let col_scrut = Value::Var(field_vars[col].clone().into());
        let mut part = self.partition_arms(arms, col)?;

        let wild = std::mem::take(&mut part.wild);
        let col_default = if wild.is_empty() {
            default
        } else {
            Some(self.compile_sub_arms(field_vars, wild, default)?)
        };

        // Scalar (bool/int/float/char) columns test the value directly. Ctor and
        // tuple columns destructure through a Case. The two never mix in one
        // column because coverage groups same-typed patterns together.
        if part.has_bool || !part.lits.is_empty() {
            self.emit_scalar_column(&part, field_vars, col, &col_scrut, col_default.as_ref())
        } else {
            self.emit_case_column(&part, field_vars, col, col_scrut, col_default)
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
                    return Err(Error::Ice(
                        "desugar_record_pat returned a record pattern".into(),
                    ))
                }
            }
        }
        Ok(part)
    }

    // A bool column becomes one If. An int/float/char column becomes a chain of
    // equality tests, built innermost-first so the source order is preserved.
    pub(super) fn emit_scalar_column(
        &mut self,
        part: &ArmPartition,
        field_vars: &[String],
        col: usize,
        col_scrut: &Value,
        col_default: Option<&Comp>,
    ) -> Result<Comp, Error> {
        let mut rest_vars = field_vars.to_vec();
        rest_vars.remove(col);
        let ice = || Error::Ice("scalar column without default survived exhaustiveness".into());
        if part.has_bool {
            let [f_arms, t_arms] = &part.bools;
            let mut side = |group: &[ArmRow]| -> Result<Comp, Error> {
                if group.is_empty() {
                    col_default.cloned().ok_or_else(ice)
                } else {
                    self.compile_sub_arms(&rest_vars, group.to_vec(), col_default.cloned())
                }
            };
            let t = side(t_arms)?;
            let f = side(f_arms)?;
            return Ok(Comp::If(col_scrut.clone(), Box::new(t), Box::new(f)));
        }
        let mut acc = col_default.cloned().ok_or_else(ice)?;
        for (lit, group) in part.lits.iter().rev() {
            let body = self.compile_sub_arms(&rest_vars, group.clone(), col_default.cloned())?;
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

    // Emit a Case: one arm per ctor, then a tuple arm or wildcard default.
    pub(super) fn emit_case_column(
        &mut self,
        part: &ArmPartition,
        field_vars: &[String],
        col: usize,
        col_scrut: Value,
        col_default: Option<Comp>,
    ) -> Result<Comp, Error> {
        let mut sub_case_arms: Vec<(CorePat, Comp)> = Vec::new();
        for (sub_ctor, sub_group) in &part.ctors {
            let n_sub = self.ctors.get(sub_ctor).map_or(0, |info| info.args.len());
            let sub_fvs = self.fresh_fields(n_sub);
            let new_field_vars = splice_vars(field_vars, col, &sub_fvs);
            let sub_body =
                self.compile_sub_arms(&new_field_vars, sub_group.clone(), col_default.clone())?;
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
            let sub_fvs = self.fresh_fields(part.tuple_arity);
            let new_field_vars = splice_vars(field_vars, col, &sub_fvs);
            let sub_body =
                self.compile_sub_arms(&new_field_vars, part.tuple.clone(), col_default)?;
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
            id: crate::syntax::ast::NodeId::DUMMY,
            synth: false,
            node: Pattern::Wild,
            span: Span::new(0, 0),
        })
        .collect();
    for (fname, fpat) in fields {
        if let Some(fi) = info.fields.iter().position(|f| f == fname) {
            subs[fi] = fpat.clone();
        }
    }
    let _ = spread;
    Pattern::Ctor(ctor_name.to_string(), subs)
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
