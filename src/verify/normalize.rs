//! Alpha-normalization and the structural digest.
//!
//! Two obligations that differ only by the numbering of their declared variables
//! and functions, or by an unused declaration, normalize to the same canonical
//! obligation and therefore to the same bytes and the same digest. Any change to
//! an operator, a literal, a sort, or the term structure moves the digest. The
//! digest is over a tag-based structural encoding, so it is independent of the
//! SMT-LIB surface spelling and of the Core content hash.

use crate::verify::logic::{Contract, FuncId, LogicExpr, LogicSort, Obligation, VarId};

/// Domain separator for the contract digest, so a contract and an obligation with
/// coincidentally identical tag streams can never share an identity.
const CONTRACT_DIGEST_DOMAIN: &[u8] = b"prism-logic-contract-v1";

/// Domain separator for the logical-declaration digest.
const LOGIC_DEF_DIGEST_DOMAIN: &[u8] = b"prism-logic-def-v1";

/// Canonicalize an obligation: renumber the variables and functions actually
/// referenced, by first occurrence over `assumptions ++ goal`, dropping any
/// declaration nothing mentions.
pub(crate) fn normalize(ob: &Obligation) -> Obligation {
    let mut vmap: Vec<Option<u32>> = vec![None; ob.vars.len()];
    let mut fmap: Vec<Option<u32>> = vec![None; ob.funcs.len()];
    let mut vorder: Vec<VarId> = Vec::new();
    let mut forder: Vec<FuncId> = Vec::new();
    for a in &ob.assumptions {
        collect(a, &mut vmap, &mut fmap, &mut vorder, &mut forder);
    }
    collect(&ob.goal, &mut vmap, &mut fmap, &mut vorder, &mut forder);

    Obligation {
        vars: vorder.iter().map(|v| ob.vars[v.0 as usize]).collect(),
        funcs: forder
            .iter()
            .map(|f| ob.funcs[f.0 as usize].clone())
            .collect(),
        assumptions: ob
            .assumptions
            .iter()
            .map(|a| rename(a, &vmap, &fmap))
            .collect(),
        goal: rename(&ob.goal, &vmap, &fmap),
    }
}

/// Assign a fresh dense index to each variable and function the first time it is
/// seen, recording the discovery order.
fn collect(
    e: &LogicExpr,
    vmap: &mut [Option<u32>],
    fmap: &mut [Option<u32>],
    vorder: &mut Vec<VarId>,
    forder: &mut Vec<FuncId>,
) {
    match e {
        LogicExpr::Var(v) => {
            if vmap[v.0 as usize].is_none() {
                vmap[v.0 as usize] = Some(len32(vorder.len()));
                vorder.push(*v);
            }
        }
        LogicExpr::App(f, args) => {
            if fmap[f.0 as usize].is_none() {
                fmap[f.0 as usize] = Some(len32(forder.len()));
                forder.push(*f);
            }
            for a in args {
                collect(a, vmap, fmap, vorder, forder);
            }
        }
        LogicExpr::Builtin(_, args) => {
            for a in args {
                collect(a, vmap, fmap, vorder, forder);
            }
        }
        LogicExpr::Bool(_) | LogicExpr::Int(_) => {}
    }
}

fn rename(e: &LogicExpr, vmap: &[Option<u32>], fmap: &[Option<u32>]) -> LogicExpr {
    match e {
        LogicExpr::Var(v) => LogicExpr::Var(VarId(vmap[v.0 as usize].expect("var was collected"))),
        LogicExpr::App(f, args) => LogicExpr::App(
            FuncId(fmap[f.0 as usize].expect("func was collected")),
            args.iter().map(|a| rename(a, vmap, fmap)).collect(),
        ),
        LogicExpr::Builtin(b, args) => {
            LogicExpr::Builtin(*b, args.iter().map(|a| rename(a, vmap, fmap)).collect())
        }
        LogicExpr::Bool(_) | LogicExpr::Int(_) => e.clone(),
    }
}

/// The structural identity of an obligation: a blake3 over a tag-based encoding of
/// its canonical (normalized) form.
pub(crate) fn structural_digest(ob: &Obligation) -> String {
    let norm = normalize(ob);
    let mut buf = Vec::new();
    encode_obligation(&norm, &mut buf);
    blake3::hash(buf.as_slice()).to_hex().to_string()
}

/// The structural identity of a contract: a blake3 over a domain-separated,
/// tag-based encoding. The parameter and result binders are positional and
/// already canonical, so no alpha-normalization is needed; changing a parameter
/// sort, the result sort, or any clause moves the digest.
pub(crate) fn contract_digest(c: &Contract) -> String {
    let mut buf = Vec::from(CONTRACT_DIGEST_DOMAIN);
    put_u32(&mut buf, len32(c.params.len()));
    for s in &c.params {
        put_u16(&mut buf, s.tag());
    }
    put_u32(&mut buf, len32(c.requires.len()));
    for r in &c.requires {
        encode_expr(r, &mut buf);
    }
    put_u16(&mut buf, c.result.tag());
    put_u32(&mut buf, len32(c.ensures.len()));
    for e in &c.ensures {
        encode_expr(e, &mut buf);
    }
    blake3::hash(buf.as_slice()).to_hex().to_string()
}

/// The structural identity of a checked logical declaration: a domain-separated
/// blake3 over its parameter sorts, result sort, and inlined body. Changing a
/// parameter sort, the result sort, or the body moves the digest.
pub(crate) fn logic_def_digest(
    params: &[LogicSort],
    result: LogicSort,
    body: &LogicExpr,
) -> String {
    let mut buf = Vec::from(LOGIC_DEF_DIGEST_DOMAIN);
    put_u32(&mut buf, len32(params.len()));
    for s in params {
        put_u16(&mut buf, s.tag());
    }
    put_u16(&mut buf, result.tag());
    encode_expr(body, &mut buf);
    blake3::hash(buf.as_slice()).to_hex().to_string()
}

fn encode_obligation(ob: &Obligation, buf: &mut Vec<u8>) {
    put_u32(buf, len32(ob.vars.len()));
    for s in &ob.vars {
        put_u16(buf, s.tag());
    }
    put_u32(buf, len32(ob.funcs.len()));
    for d in &ob.funcs {
        put_u32(buf, len32(d.params.len()));
        for p in &d.params {
            put_u16(buf, p.tag());
        }
        put_u16(buf, d.result.tag());
    }
    put_u32(buf, len32(ob.assumptions.len()));
    for a in &ob.assumptions {
        encode_expr(a, buf);
    }
    encode_expr(&ob.goal, buf);
}

fn encode_expr(e: &LogicExpr, buf: &mut Vec<u8>) {
    match e {
        LogicExpr::Var(v) => {
            buf.push(1);
            put_u32(buf, v.0);
        }
        LogicExpr::Bool(b) => {
            buf.push(2);
            buf.push(u8::from(*b));
        }
        LogicExpr::Int(n) => {
            buf.push(3);
            let bytes = n.to_signed_bytes_le();
            put_u32(buf, len32(bytes.len()));
            buf.extend_from_slice(&bytes);
        }
        LogicExpr::Builtin(b, args) => {
            buf.push(4);
            put_u16(buf, b.tag());
            put_u32(buf, len32(args.len()));
            for a in args {
                encode_expr(a, buf);
            }
        }
        LogicExpr::App(f, args) => {
            buf.push(5);
            put_u32(buf, f.0);
            put_u32(buf, len32(args.len()));
            for a in args {
                encode_expr(a, buf);
            }
        }
    }
}

fn put_u16(buf: &mut Vec<u8>, n: u16) {
    buf.extend_from_slice(&n.to_be_bytes());
}

fn put_u32(buf: &mut Vec<u8>, n: u32) {
    buf.extend_from_slice(&n.to_be_bytes());
}

/// Encode a collection length as the `u32` the digest format uses. Lengths this
/// large do not occur in a real obligation; a pathological overflow saturates
/// rather than wraps, so the digest stays a total function of the input.
fn len32(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}
