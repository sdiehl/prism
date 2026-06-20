use std::fmt;

use marginalia::Span;

use super::Tc;
use crate::error::TypeError;
use crate::syntax::ast::{Arm, BigInt, Core, Pattern, S};

#[derive(Clone, PartialEq)]
enum Head {
    Ctor(String, usize),
    Tuple(usize),
    Bool(bool),
    Int(BigInt),
    Float(u64),
}

impl Head {
    const fn arity(&self) -> usize {
        match self {
            Self::Ctor(_, n) | Self::Tuple(n) => *n,
            _ => 0,
        }
    }
}

#[derive(Clone)]
enum Pat {
    Any,
    Con(Head, Vec<Self>),
}

type Row = Vec<Pat>;

#[derive(Clone)]
enum Witness {
    Any,
    Lit(String),
    Ctor(String, Vec<Self>),
    Tuple(Vec<Self>),
}

impl Witness {
    fn of(h: &Head) -> Self {
        match h {
            Head::Ctor(name, n) => Self::Ctor(name.clone(), vec![Self::Any; *n]),
            Head::Tuple(n) => Self::Tuple(vec![Self::Any; *n]),
            Head::Bool(b) => Self::Lit(b.to_string()),
            Head::Int(v) => Self::Lit(v.to_string()),
            Head::Float(bits) => Self::Lit(f64::from_bits(*bits).to_string()),
        }
    }

    fn rebuild(h: &Head, args: Vec<Self>) -> Self {
        match h {
            Head::Ctor(name, _) => Self::Ctor(name.clone(), args),
            Head::Tuple(_) => Self::Tuple(args),
            _ => Self::of(h),
        }
    }
}

fn write_args(f: &mut fmt::Formatter<'_>, args: &[Witness]) -> fmt::Result {
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{a}")?;
    }
    Ok(())
}

impl fmt::Display for Witness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Any => write!(f, "_"),
            Self::Lit(s) => write!(f, "{s}"),
            Self::Ctor(name, args) if args.is_empty() => write!(f, "{name}"),
            Self::Ctor(name, args) => {
                write!(f, "{name}(")?;
                write_args(f, args)?;
                write!(f, ")")
            }
            Self::Tuple(args) => {
                write!(f, "(")?;
                write_args(f, args)?;
                write!(f, ")")
            }
        }
    }
}

fn specialize(m: &[Row], h: &Head) -> Vec<Row> {
    m.iter()
        .filter_map(|row| match &row[0] {
            Pat::Con(g, args) if g == h => Some(args.iter().chain(&row[1..]).cloned().collect()),
            Pat::Con(..) => None,
            Pat::Any => {
                let mut out = vec![Pat::Any; h.arity()];
                out.extend_from_slice(&row[1..]);
                Some(out)
            }
        })
        .collect()
}

fn defaults(m: &[Row]) -> Vec<Row> {
    m.iter()
        .filter(|row| matches!(row[0], Pat::Any))
        .map(|row| row[1..].to_vec())
        .collect()
}

fn heads(m: &[Row]) -> Vec<Head> {
    let mut out: Vec<Head> = Vec::new();
    for row in m {
        if let Pat::Con(h, _) = &row[0] {
            if !out.contains(h) {
                out.push(h.clone());
            }
        }
    }
    out
}

fn fresh_lit(present: &[Head]) -> Witness {
    let ints: Vec<BigInt> = present
        .iter()
        .filter_map(|h| match h {
            Head::Int(v) => Some(v.clone()),
            _ => None,
        })
        .collect();
    if present.is_empty() || ints.len() != present.len() {
        return Witness::Any;
    }
    // Pigeonhole guarantees one of len+1 candidates is absent; if that somehow
    // fails, degrade to a wildcard rather than crash the checker.
    (0..=ints.len() as u64)
        .map(BigInt::from)
        .find(|n| !ints.contains(n))
        .map_or(Witness::Any, |n| Witness::Lit(n.to_string()))
}

impl Tc<'_> {
    fn lower_pat(&self, p: &Pattern) -> Pat {
        let subs = |ps: &[S<Pattern>]| -> Vec<Pat> {
            ps.iter().map(|s| self.lower_pat(&s.node)).collect()
        };
        match p {
            Pattern::Wild | Pattern::Var(_) => Pat::Any,
            Pattern::Int(lit) => Pat::Con(Head::Int(lit.value.clone()), vec![]),
            Pattern::Char(c) => Pat::Con(Head::Int(BigInt::from(u32::from(*c))), vec![]),
            Pattern::Float(v) => Pat::Con(Head::Float(v.to_bits()), vec![]),
            Pattern::Bool(b) => Pat::Con(Head::Bool(*b), vec![]),
            Pattern::Tuple(ps) => Pat::Con(Head::Tuple(ps.len()), subs(ps)),
            Pattern::Ctor(name, ps) => Pat::Con(Head::Ctor(name.clone(), ps.len()), subs(ps)),
            Pattern::Record(name, fps, _) => self.ctors.get(name).map_or(Pat::Any, |info| {
                let args = info
                    .fields
                    .iter()
                    .map(|fname| {
                        fps.iter()
                            .find(|(n, _)| *fname == n)
                            .map_or(Pat::Any, |(_, s)| self.lower_pat(&s.node))
                    })
                    .collect();
                Pat::Con(Head::Ctor(name.clone(), info.fields.len()), args)
            }),
        }
    }

    fn siblings(&self, h: &Head) -> Option<Vec<Head>> {
        match h {
            Head::Tuple(n) => Some(vec![Head::Tuple(*n)]),
            Head::Bool(_) => Some(vec![Head::Bool(false), Head::Bool(true)]),
            Head::Ctor(name, _) => {
                let tname = &self.ctors.get(name)?.type_name;
                let mut cs: Vec<(usize, Head)> = self
                    .ctors
                    .iter()
                    .filter(|(_, i)| &i.type_name == tname)
                    .map(|(k, i)| (i.tag, Head::Ctor(k.clone(), i.args.len())))
                    .collect();
                cs.sort_by_key(|(tag, _)| *tag);
                Some(cs.into_iter().map(|(_, h)| h).collect())
            }
            Head::Int(_) | Head::Float(_) => None,
        }
    }

    fn useful(&self, m: &[Row], row: &[Pat]) -> bool {
        let Some((head, rest)) = row.split_first() else {
            return m.is_empty();
        };
        match head {
            Pat::Con(h, args) => {
                let r2: Row = args.iter().chain(rest).cloned().collect();
                self.useful(&specialize(m, h), &r2)
            }
            Pat::Any => {
                let present = heads(m);
                let complete = present
                    .first()
                    .and_then(|h| self.siblings(h))
                    .is_some_and(|all| all.iter().all(|h| present.contains(h)));
                if complete {
                    present.iter().any(|h| {
                        let mut r2 = vec![Pat::Any; h.arity()];
                        r2.extend_from_slice(rest);
                        self.useful(&specialize(m, h), &r2)
                    })
                } else {
                    self.useful(&defaults(m), rest)
                }
            }
        }
    }

    fn witness(&self, m: &[Row], width: usize) -> Option<Vec<Witness>> {
        if width == 0 {
            return m.is_empty().then(Vec::new);
        }
        let present = heads(m);
        let Some(all) = present.first().and_then(|h| self.siblings(h)) else {
            let mut out = vec![fresh_lit(&present)];
            out.extend(self.witness(&defaults(m), width - 1)?);
            return Some(out);
        };
        if let Some(missing) = all.iter().find(|h| !present.contains(h)) {
            let mut out = vec![Witness::of(missing)];
            out.extend(self.witness(&defaults(m), width - 1)?);
            return Some(out);
        }
        for h in &present {
            let n = h.arity();
            if let Some(mut w) = self.witness(&specialize(m, h), n + width - 1) {
                let tail = w.split_off(n);
                let mut out = vec![Witness::rebuild(h, w)];
                out.extend(tail);
                return Some(out);
            }
        }
        None
    }

    // A guarded arm may fail at runtime, so its row never enters the matrix: it
    // contributes nothing to exhaustiveness and shadows no later arm. An arm is
    // unreachable only when earlier unguarded rows already cover it.
    pub(super) fn check_coverage(&self, arms: &[Arm<Core>], span: Span) -> Result<(), TypeError> {
        let mut matrix: Vec<Row> = Vec::new();
        for arm in arms {
            let row = vec![self.lower_pat(&arm.pat.node)];
            if !self.useful(&matrix, &row) {
                return Err(TypeError::Other {
                    span: arm.pat.span,
                    msg: "unreachable match arm".into(),
                });
            }
            if arm.guard.is_none() {
                matrix.push(row);
            }
        }
        if let Some(w) = self.witness(&matrix, 1) {
            return Err(TypeError::Other {
                span,
                msg: format!("non-exhaustive match: missing {}", w[0]),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{defaults, fresh_lit, specialize, Head, Pat};
    use crate::syntax::ast::BigInt;

    fn int(n: i64) -> Head {
        Head::Int(BigInt::from(n))
    }

    // `specialize` on a head keeps matching-ctor rows (splicing their fields to
    // the front), drops other-ctor rows, and expands wildcards to the head's
    // arity in wildcards.
    #[test]
    fn specialize_matches_expands_and_drops() {
        let m = vec![
            vec![
                Pat::Con(Head::Ctor("Cons".into(), 2), vec![Pat::Any, Pat::Any]),
                Pat::Con(Head::Bool(true), vec![]),
            ],
            vec![Pat::Con(Head::Ctor("Nil".into(), 0), vec![]), Pat::Any],
            vec![Pat::Any, Pat::Any],
        ];
        let out = specialize(&m, &Head::Ctor("Cons".into(), 2));
        assert_eq!(out.len(), 2, "the Nil row is dropped");
        // matching row: 2 ctor fields spliced ahead of the 1 trailing column.
        assert_eq!(out[0].len(), 3);
        assert!(matches!(out[0][2], Pat::Con(Head::Bool(true), _)));
        // wildcard row: expands to arity-2 wildcards + the trailing column.
        assert_eq!(out[1].len(), 3);
        assert!(out[1].iter().all(|p| matches!(p, Pat::Any)));
    }

    // `defaults` keeps only wildcard-headed rows and drops the first column.
    #[test]
    fn defaults_keeps_wildcard_rows() {
        let m = vec![
            vec![Pat::Con(Head::Bool(true), vec![]), Pat::Any],
            vec![Pat::Any, Pat::Con(Head::Bool(false), vec![])],
        ];
        let out = defaults(&m);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].len(), 1);
        assert!(matches!(out[0][0], Pat::Con(Head::Bool(false), _)));
    }

    // `fresh_lit` returns the smallest non-negative integer absent from an
    // all-integer column (its pigeonhole search is total), and `_` otherwise.
    #[test]
    fn fresh_lit_finds_missing_integer() {
        assert_eq!(fresh_lit(&[]).to_string(), "_");
        assert_eq!(fresh_lit(&[int(0), int(1), int(2)]).to_string(), "3");
        assert_eq!(fresh_lit(&[int(0), int(2)]).to_string(), "1");
        // a non-integer head present means no finite enumeration: fall to `_`.
        assert_eq!(fresh_lit(&[int(0), Head::Bool(true)]).to_string(), "_");
    }
}
