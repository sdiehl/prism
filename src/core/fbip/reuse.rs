use crate::kw;
use crate::names::reuse_token;
use crate::sym::Sym;

use super::super::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};

#[must_use]
pub fn reuse(core: &Core) -> Core {
    Core {
        fns: core
            .fns
            .iter()
            .map(|f| CoreFn {
                name: f.name,
                params: f.params.clone(),
                dict_arity: f.dict_arity,
                body: reuse_comp(&f.body),
            })
            .collect(),
    }
}

fn reuse_comp(c: &Comp) -> Comp {
    match c {
        Comp::Bind(m, x, n) => Comp::Bind(Box::new(reuse_comp(m)), *x, Box::new(reuse_comp(n))),
        Comp::If(v, t, e) => Comp::If(v.clone(), Box::new(reuse_comp(t)), Box::new(reuse_comp(e))),
        Comp::Lam(ps, b) => Comp::Lam(ps.clone(), Box::new(reuse_comp(b))),
        Comp::Case(scrut, arms) => Comp::Case(
            scrut.clone(),
            arms.iter()
                .map(|(p, body)| (p.clone(), reuse_arm(scrut, p, &reuse_comp(body))))
                .collect(),
        ),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Comp::Handle {
            body: Box::new(reuse_comp(body)),
            return_var: *return_var,
            return_body: return_body.as_deref().map(|rb| Box::new(reuse_comp(rb))),
            ops: ops.rebuild(|op| HandleOp {
                body: reuse_comp(&op.body),
                ..op.clone()
            }),
        },
        other => other.clone(),
    }
}

fn reuse_arm(scrut: &Value, p: &CorePat, body: &Comp) -> Comp {
    let Value::Var(s) = scrut else {
        return body.clone();
    };
    let arity = match p {
        // The wired nullable frees no cell when matched (its native form is
        // the null word or the element itself), so it can never seed a token.
        CorePat::Ctor(name, _) if kw::is_or_null_ctor(name.as_str()) => return body.clone(),
        CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => fields.len(),
        _ => return body.clone(),
    };
    let tok: Sym = reuse_token(s.as_str()).into();
    // Reuse is a pure optimization, so a scrutinee `try_reuse` cannot place into a
    // scoped `WithReuse` is left as the safe no-reuse body. When it does succeed,
    // the result is balanced by construction: `WithReuse` frees the cell at one
    // point and `consume_alloc` spends the token on every control path (it returns
    // `None`, declining the whole rewrite, if any path fails to allocate), so no
    // post-hoc balance check is needed.
    try_reuse(body, *s, tok, arity).unwrap_or_else(|| body.clone())
}

// Pair the `drop s` (the cell freed when the scrutinee is consumed) with a later
// constructor allocation. The drop may sit on the bind chain or, when the
// scrutinee survives down some arms, inside a branch; either way the freed cell
// becomes a token that the rest of THAT path must spend exactly once. Find the
// drop, then hand the continuation to `consume_alloc`, which fails (aborting the
// whole rewrite) unless every path from the drop allocates a fitting cell. Arms
// where the drop never appears are left untouched.
fn try_reuse(c: &Comp, s: Sym, tok: Sym, cap: usize) -> Option<Comp> {
    match c {
        Comp::Bind(m, x, n) => {
            if let Comp::Drop(Value::Var(d)) = m.as_ref() {
                if *d == s {
                    let n2 = consume_alloc(n, tok, cap)?;
                    return Some(Comp::WithReuse {
                        token: tok,
                        freed: Value::Var(s),
                        body: Box::new(n2),
                    });
                }
            }
            if let Some(m2) = try_reuse(m, s, tok, cap) {
                return Some(Comp::Bind(Box::new(m2), *x, n.clone()));
            }
            Some(Comp::Bind(
                m.clone(),
                *x,
                Box::new(try_reuse(n, s, tok, cap)?),
            ))
        }
        Comp::If(cond, t, e) => {
            let (t2, e2) = (try_reuse(t, s, tok, cap), try_reuse(e, s, tok, cap));
            // The drop must live in exactly one branch (the scrutinee cannot be
            // both freed and passed through on the same conditional).
            match (t2, e2) {
                (Some(t2), None) => Some(Comp::If(cond.clone(), Box::new(t2), e.clone())),
                (None, Some(e2)) => Some(Comp::If(cond.clone(), t.clone(), Box::new(e2))),
                _ => None,
            }
        }
        Comp::Case(scrut, arms) => {
            let mut hit = false;
            let arms = arms
                .iter()
                .map(|(p, b)| {
                    try_reuse(b, s, tok, cap).map_or_else(
                        || (p.clone(), b.clone()),
                        |b2| {
                            hit = true;
                            (p.clone(), b2)
                        },
                    )
                })
                .collect();
            hit.then(|| Comp::Case(scrut.clone(), arms))
        }
        // A nested pattern's inner arm reuses first, wrapping its body in a
        // `WithReuse` that the outer scrutinee's `drop` now sits inside. Keep
        // searching through it, then rewrap with the inner token untouched.
        Comp::WithReuse { token, freed, body } => {
            let body2 = try_reuse(body, s, tok, cap)?;
            Some(Comp::WithReuse {
                token: *token,
                freed: freed.clone(),
                body: Box::new(body2),
            })
        }
        _ => None,
    }
}

// Reuse credit (FP^2): a freed token feeds the first constructor allocation that
// follows the drop on every control path, not just the literal tail. Walk the
// bind chain forward and rewrite the first `return Ctor` (whose arity fits the
// freed cell, so prism_reuse_alloc never writes past the old shell) into an
// in-place `Reuse`; the token is then spent and the continuation left alone. At a
// branch every arm must spend the credit exactly once, so both sides must
// succeed. Any path reaching a non-allocating tail returns None, aborting the
// whole rewrite and falling back to the safe body.
fn consume_alloc(c: &Comp, tok: Sym, cap: usize) -> Option<Comp> {
    match c {
        Comp::Bind(m, x, n) => {
            // The bound computation `m` may itself tail-produce the allocation
            // (CBPV nests `return Ctor to x; ...` as a bind chain under one `m`),
            // so try to spend the credit there first; only if no path of `m`
            // allocates does the credit flow on into the continuation `n`.
            if let Some(m2) = consume_alloc(m, tok, cap) {
                return Some(Comp::Bind(Box::new(m2), *x, n.clone()));
            }
            Some(Comp::Bind(
                m.clone(),
                *x,
                Box::new(consume_alloc(n, tok, cap)?),
            ))
        }
        Comp::Return(v @ (Value::Ctor(..) | Value::Tuple(..)))
            if ctor_arity(v) <= cap && !is_or_null_alloc(v) =>
        {
            Some(Comp::Reuse(tok, v.clone()))
        }
        Comp::If(cond, t, e) => Some(Comp::If(
            cond.clone(),
            Box::new(consume_alloc(t, tok, cap)?),
            Box::new(consume_alloc(e, tok, cap)?),
        )),
        Comp::Case(scrut, arms) => {
            let arms = arms
                .iter()
                .map(|(p, b)| Some((p.clone(), consume_alloc(b, tok, cap)?)))
                .collect::<Option<Vec<_>>>()?;
            Some(Comp::Case(scrut.clone(), arms))
        }
        // The fitting allocation may live past an inner reuse's `WithReuse` (a
        // deeper-nested pattern); walk into it so the credit can reach the tail.
        Comp::WithReuse { token, freed, body } => {
            let body2 = consume_alloc(body, tok, cap)?;
            Some(Comp::WithReuse {
                token: *token,
                freed: freed.clone(),
                body: Box::new(body2),
            })
        }
        _ => None,
    }
}

const fn ctor_arity(v: &Value) -> usize {
    match v {
        Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.len(),
        _ => 0,
    }
}

// The wired nullable allocates no cell, so it can never spend a reuse credit.
fn is_or_null_alloc(v: &Value) -> bool {
    matches!(v, Value::Ctor(name, ..) if kw::is_or_null_ctor(name.as_str()))
}
