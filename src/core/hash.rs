//! Content-addressed hashing of elaborated Core.
//!
//! Each top-level definition is hashed over its Core after two normalizations,
//! so the hash names *behavior*, not spelling or position:
//!
//!   - alpha-normalization: every binder (function params, lets, lambda params,
//!     match binders, handler binders, reuse tokens, AND compiler temporaries
//!     `t@N`) is rendered as a de Bruijn index, so local names and the global
//!     temp counter drop out.
//!   - Merkle dependency substitution: a reference to another top-level symbol
//!     is replaced by that symbol's hash, so a definition's hash transitively
//!     commits to everything it calls.
//!
//! A recursive group is the one place members cannot be hashed independently.
//! The strongly-connected component is hashed as a unit, members referring to
//! each other by intra-component index, then each member's hash is derived from
//! the component hash and its index. Self-recursion is the size-one case of the
//! same rule, so it needs no special path.
//!
//! Metadata that an importer's elaboration reads but Core does not carry (the
//! generalized type and principal effect row) is folded in via `meta`; omitting
//! an elaboration input is a silent-collision bug, so the caller supplies it.
//!
//! Leaves (builtins, ctor/effect-op names) are committed by stable identifier:
//! renaming a constructor or an effect operation *is* a behavioral change at
//! this granularity, so their names are part of the hash by design.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use super::cbpv::{self, Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::fv;
use crate::sym::Sym;

/// Map from a definition's canonical symbol to its content hash (hex).
pub type Hashes = BTreeMap<Sym, String>;

/// Scheme tag: every hash commits to it, so a change to this encoding cannot
/// silently reuse an old hash computed under a different scheme.
const SCHEME: &str = "prism-core-hash-v1";

/// Hash every definition in `core`. `meta[sym]` is a canonical rendering of the
/// out-of-Core elaboration inputs for `sym` (type, principal row); an absent
/// entry folds in nothing.
#[must_use]
pub fn hash_program(core: &Core, meta: &BTreeMap<Sym, String>) -> Hashes {
    let fnmap: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();
    let mut hashes = Hashes::new();
    // Callee-before-caller, so every external dependency is already hashed when
    // a component is encoded.
    for comp_members in sccs(core, &fnmap) {
        let members: BTreeSet<Sym> = comp_members.iter().copied().collect();
        hash_component(&comp_members, &members, &fnmap, meta, &mut hashes);
    }
    hashes
}

/// Hash one SCC and write each member's derived hash into `hashes`.
fn hash_component(
    members: &[Sym],
    member_set: &BTreeSet<Sym>,
    fnmap: &BTreeMap<Sym, &CoreFn>,
    meta: &BTreeMap<Sym, String>,
    hashes: &mut Hashes,
) {
    // Ordering pass: encode each member with intra-component references left as
    // a neutral placeholder, then sort. This gives a name-independent canonical
    // order for the cycle. The structural encoding decides; the name is only a
    // tiebreak for two members that are structurally identical (rare).
    let mut order: Vec<(String, Sym)> = members
        .iter()
        .map(|m| (encode(fnmap[m], member_set, None, hashes), *m))
        .collect();
    order.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.as_str().cmp(b.1.as_str())));

    let idx: BTreeMap<Sym, usize> = order
        .iter()
        .enumerate()
        .map(|(i, (_, m))| (*m, i))
        .collect();

    // Real pass: encode with intra-component indices, fold each member's meta,
    // and hash the concatenation as the component identity.
    let mut blob = String::from(SCHEME);
    for (_, m) in &order {
        let _ = write!(blob, "|meta:{}|", meta.get(m).map_or("", String::as_str));
        blob.push_str(&encode(fnmap[m], member_set, Some(&idx), hashes));
    }
    let component = hex(&blob);

    for (i, (_, m)) in order.iter().enumerate() {
        hashes.insert(*m, hex(&format!("{component}:{i}")));
    }
}

fn hex(s: &str) -> String {
    blake3::hash(s.as_bytes()).to_hex().to_string()
}

/// Canonically encode one definition's body (params as the outermost binders).
/// `member_set` is the current SCC; `idx` maps its members to component indices
/// (`None` during the ordering pass, where intra-SCC refs are placeholders).
fn encode(
    f: &CoreFn,
    member_set: &BTreeSet<Sym>,
    idx: Option<&BTreeMap<Sym, usize>>,
    hashes: &Hashes,
) -> String {
    let mut e = Enc {
        member_set,
        idx,
        hashes,
        env: f.params.clone(),
        out: String::new(),
    };
    let _ = write!(e.out, "fn{}", f.params.len());
    e.comp(&f.body);
    e.out
}

struct Enc<'a> {
    member_set: &'a BTreeSet<Sym>,
    idx: Option<&'a BTreeMap<Sym, usize>>,
    hashes: &'a Hashes,
    env: Vec<Sym>,
    out: String,
}

impl Enc<'_> {
    /// Length-prefixed token, so no name or string can be confused with its
    /// neighbours in the encoding.
    fn tok(&mut self, s: &str) {
        let _ = write!(self.out, "{}:{s}", s.len());
    }

    /// Resolve a symbol reference: an enclosing binder (de Bruijn index), an
    /// intra-component member (index/placeholder), an already-hashed external
    /// dependency (its hash), or a stray leaf (its name).
    fn refer(&mut self, s: Sym) {
        self.out.push('%');
        if let Some(pos) = self.env.iter().rposition(|b| *b == s) {
            let _ = write!(self.out, "b{}", self.env.len() - 1 - pos);
        } else if self.member_set.contains(&s) {
            match self.idx {
                Some(m) => {
                    let _ = write!(self.out, "r{}", m[&s]);
                }
                None => self.out.push_str("r?"),
            }
        } else if let Some(h) = self.hashes.get(&s) {
            let _ = write!(self.out, "h{h}");
        } else {
            self.out.push('g');
            self.tok(s.as_str());
        }
    }

    fn vals(&mut self, vs: &[Value]) {
        self.out.push('[');
        for v in vs {
            self.val(v);
        }
        self.out.push(']');
    }

    fn val(&mut self, v: &Value) {
        match v {
            Value::Var(x) => {
                self.out.push('v');
                self.refer(*x);
            }
            Value::Int(n) => {
                let _ = write!(self.out, "i{n}");
            }
            Value::I64(n) => {
                let _ = write!(self.out, "j{n}");
            }
            Value::U64(n) => {
                let _ = write!(self.out, "u{n}");
            }
            // Bit pattern, so NaN payloads and -0.0 are committed exactly.
            Value::Float(f) => {
                let _ = write!(self.out, "f{}", f.to_bits());
            }
            Value::Bool(b) => {
                let _ = write!(self.out, "o{}", u8::from(*b));
            }
            Value::Unit => self.out.push('1'),
            Value::Str(s) => {
                self.out.push('s');
                self.tok(s);
            }
            Value::Thunk(c) => {
                self.out.push('t');
                self.comp(c);
            }
            Value::Ctor(n, tag, args) => {
                self.out.push('c');
                self.tok(n.as_str());
                let _ = write!(self.out, "/{tag}");
                self.vals(args);
            }
            Value::Tuple(args) => {
                self.out.push('p');
                self.vals(args);
            }
        }
    }

    // Encode a pattern's shape and return its binders in left-to-right order so
    // the caller can push them onto the de Bruijn environment.
    fn pat(&mut self, p: &CorePat) -> Vec<Sym> {
        let fields = |out: &mut String, fs: &[Option<Sym>], bs: &mut Vec<Sym>| {
            out.push('[');
            for f in fs {
                match f {
                    Some(x) => {
                        out.push('v');
                        bs.push(*x);
                    }
                    None => out.push('_'),
                }
            }
            out.push(']');
        };
        let mut bs = Vec::new();
        match p {
            CorePat::Wild => self.out.push_str("_w"),
            CorePat::Var(x) => {
                self.out.push_str("_v");
                bs.push(*x);
            }
            CorePat::Ctor(n, fs) => {
                self.out.push_str("_c");
                self.tok(n.as_str());
                fields(&mut self.out, fs, &mut bs);
            }
            CorePat::Tuple(fs) => {
                self.out.push_str("_t");
                fields(&mut self.out, fs, &mut bs);
            }
        }
        bs
    }

    // Run `body` with `binders` pushed, then pop them.
    fn scoped(&mut self, binders: &[Sym], body: impl FnOnce(&mut Self)) {
        self.env.extend_from_slice(binders);
        body(self);
        self.env.truncate(self.env.len() - binders.len());
    }

    fn comp(&mut self, c: &Comp) {
        // The variant name uniquely tags the node, so distinct trees that share
        // a child shape cannot collide.
        let _ = write!(self.out, "<{}>", c.kind());
        match c {
            Comp::Return(v)
            | Comp::Force(v)
            | Comp::Print(v)
            | Comp::PrintF(v)
            | Comp::PrintS(v)
            | Comp::Error(v)
            | Comp::Srand(v)
            | Comp::Dup(v)
            | Comp::Drop(v)
            | Comp::RefNew(v)
            | Comp::RefGet(v) => self.val(v),
            Comp::FloatBuiltin(op, v) => {
                self.tok(&format!("{op:?}"));
                self.val(v);
            }
            Comp::Bind(m, x, n) => {
                self.comp(m);
                self.scoped(&[*x], |e| e.comp(n));
            }
            Comp::Lam(xs, b) => {
                let _ = write!(self.out, "{}", xs.len());
                self.scoped(xs, |e| e.comp(b));
            }
            Comp::App(f, args) => {
                self.comp(f);
                self.vals(args);
            }
            Comp::If(v, t, e) => {
                self.val(v);
                self.comp(t);
                self.comp(e);
            }
            Comp::Prim(op, a, b) => {
                self.tok(&format!("{op:?}"));
                self.val(a);
                self.val(b);
            }
            // The call head is a dependency reference, so substitution applies.
            Comp::Call(name, args) => {
                self.refer(*name);
                self.vals(args);
            }
            // Effect operation: a leaf, committed by name.
            Comp::Do(op, args) => {
                self.tok(op.as_str());
                self.vals(args);
            }
            Comp::Case(v, arms) => {
                self.val(v);
                self.out.push('{');
                for (p, body) in arms {
                    let bs = self.pat(p);
                    self.scoped(&bs, |e| e.comp(body));
                }
                self.out.push('}');
            }
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                self.comp(body);
                match (return_var, return_body) {
                    (Some(rv), Some(rb)) => {
                        self.out.push('R');
                        self.scoped(&[*rv], |e| e.comp(rb));
                    }
                    _ => self.out.push('N'),
                }
                // Handler clauses form a set, so encode in name order.
                let mut ops: Vec<&HandleOp> = ops.iter().collect();
                ops.sort_by(|a, b| a.name.as_str().cmp(b.name.as_str()));
                self.out.push('{');
                for op in ops {
                    self.tok(op.name.as_str());
                    let mut binders = op.params.clone();
                    binders.push(op.resume);
                    self.scoped(&binders, |e| e.comp(&op.body));
                }
                self.out.push('}');
            }
            // Masked effect labels are a set, not binders.
            Comp::Mask(ops, b) => {
                let mut names: Vec<&str> = ops.iter().map(|s| s.as_str()).collect();
                names.sort_unstable();
                for n in names {
                    self.tok(n);
                }
                self.comp(b);
            }
            Comp::StrBuiltin(b, args) => {
                self.tok(&format!("{b:?}"));
                self.vals(args);
            }
            Comp::WithReuse { token, freed, body } => {
                self.val(freed);
                self.scoped(&[*token], |e| e.comp(body));
            }
            Comp::Reuse(tok, v) => {
                self.refer(*tok);
                self.val(v);
            }
            Comp::RefSet(a, b) => {
                self.val(a);
                self.val(b);
            }
            Comp::PrintNl | Comp::ReadInt | Comp::ReadLine | Comp::Rand => {}
        }
    }
}

/// Strongly-connected components of the dependency graph over `core.fns`, in
/// callee-before-caller order. A dependency is any top-level symbol the body
/// calls or captures first-class (call head or free variable).
fn sccs(core: &Core, fnmap: &BTreeMap<Sym, &CoreFn>) -> Vec<Vec<Sym>> {
    let order: Vec<Sym> = core.fns.iter().map(|f| f.name).collect();
    let pos: BTreeMap<Sym, usize> = order.iter().enumerate().map(|(i, s)| (*s, i)).collect();
    let adj: Vec<Vec<usize>> = core
        .fns
        .iter()
        .map(|f| {
            let mut deps = BTreeSet::new();
            let mut calls = Vec::new();
            cbpv::calls_in(&f.body, &mut calls);
            for c in calls {
                if let Some(&j) = pos.get(&c) {
                    deps.insert(j);
                }
            }
            for v in fv::comp(&f.body) {
                if fnmap.contains_key(&v) {
                    deps.insert(pos[&v]);
                }
            }
            deps.into_iter().collect()
        })
        .collect();

    // Shared iterative Tarjan: components come out callee-first (the order the
    // Merkle hashing needs, a cycle's dependencies hashed before it). hash.rs
    // canonicalizes the members within a component separately, so their order
    // here is not load-bearing.
    crate::scc::tarjan_scc(&adj)
        .into_iter()
        .map(|comp| comp.into_iter().map(|i| order[i]).collect())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{hash_program, Sym};
    use crate::core::{Comp, Core, CoreFn, Value};
    use std::collections::BTreeMap;

    fn sym(s: &str) -> Sym {
        Sym::new(s)
    }

    // `fn f(x) = let <binder> = x; <binder>`, identical behavior whatever the
    // binder is spelled.
    fn let_id(binder: &str) -> Core {
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Var(sym("x")))),
            sym(binder),
            Box::new(Comp::Return(Value::Var(sym(binder)))),
        );
        Core {
            fns: vec![CoreFn {
                name: sym("f"),
                params: vec![sym("x")],
                body,
            }],
        }
    }

    #[test]
    fn alpha_equivalent_bodies_hash_equally() {
        let m = BTreeMap::new();
        assert_eq!(
            hash_program(&let_id("y"), &m)[&sym("f")],
            hash_program(&let_id("z"), &m)[&sym("f")],
        );
    }

    // Same Core, different out-of-Core metadata must not collide: omitting an
    // elaboration input from the hash is the silent-miscompile hole.
    #[test]
    fn metadata_is_folded_in() {
        let core = let_id("y");
        let m1 = BTreeMap::from([(sym("f"), "Int -> Int".to_string())]);
        let m2 = BTreeMap::from([(sym("f"), "a -> a".to_string())]);
        assert_ne!(
            hash_program(&core, &m1)[&sym("f")],
            hash_program(&core, &m2)[&sym("f")],
        );
    }

    #[test]
    fn hashing_is_deterministic() {
        let (core, m) = (let_id("y"), BTreeMap::new());
        assert_eq!(hash_program(&core, &m), hash_program(&core, &m));
    }
}
