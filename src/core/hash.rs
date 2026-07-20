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

use serde::{Deserialize, Serialize};

use super::cbpv::{self, Comp, Core, CoreFn, CorePat, HandleOp, Value};
use super::fv;
use crate::sym::Sym;

/// A content hash: a hex digest produced by the hasher.
///
/// A newtype over the hex string so a content hash cannot be confused with an
/// arbitrary string as it travels through the identity, store, and lineage code.
/// It renders and serializes exactly as its inner hex (via
/// `Display`/`Deref`/`as_str`), so the wire bytes, on-disk objects, and folded
/// roots are byte-identical to the bare string they replaced.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Digest(String);

impl Digest {
    /// The digest's hex text. The single spelling used at every serialization
    /// boundary (disk objects, wire codec, hash inputs), so byte identity holds.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Consume the digest, yielding its owned hex string.
    #[must_use]
    pub fn into_string(self) -> String {
        self.0
    }
}

impl std::ops::Deref for Digest {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Digest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl AsRef<str> for Digest {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl From<String> for Digest {
    fn from(s: String) -> Self {
        Self(s)
    }
}

impl From<&str> for Digest {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<Digest> for String {
    fn from(d: Digest) -> Self {
        d.0
    }
}

/// Map from a definition's canonical symbol to its content hash.
pub type Hashes = BTreeMap<Sym, Digest>;

/// Scheme tag: every hash commits to it, so a change to this encoding cannot
/// silently reuse an old hash computed under a different scheme.
pub const SCHEME: &str = "prism-core-hash-v1";

/// Width, in hex characters, of the abbreviated hash prefix shown in the
/// human-facing `core-hash`/`shape`/`stdlib-hash` dumps. Full hashes are longer;
/// display truncates to this many leading nibbles.
pub const HASH_PREFIX_HEX: usize = 16;

/// Fold a `name -> content-hash` map into a single namespace root, a
/// branch-hash-style fold over the sorted entries.
///
/// The root commits to the SCHEME and to each length-prefixed name, so it moves
/// under a rename or any content change but not under reordering (the map is
/// sorted). Part A feeds it the per-definition behavior hashes; Part B merges in
/// the datatype/effect shape digests, so the stdlib root covers the whole
/// documented surface through one fold.
#[must_use]
pub fn root(entries: &BTreeMap<String, Digest>) -> Digest {
    let mut blob = String::from(SCHEME);
    for (name, hash) in entries {
        let _ = write!(blob, "|{}:{name}={hash}", name.len());
    }
    hex(&blob)
}

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

/// A per-definition *shallow* hash: the definition's own content (its Core
/// structure and its out-of-Core metadata) with every dependency referred to by
/// name rather than by substituted hash.
///
/// This is the complement of [`hash_program`]'s deep, Merkle-substituted hash.
/// Under the deep hash, editing one definition moves the hash of every
/// transitive dependent (that is the point: the hash commits to behavior). The
/// shallow hash isolates a definition's *own* change from ripples through it, so
/// a behavior diff can separate the handful of definitions a developer edited
/// from the downstream cone those edits affect. It is not an identity (it does
/// not compose across a rename of a callee) and is never stored; it exists only
/// to attribute a deep-hash move to its source.
#[must_use]
pub fn shallow_hashes(core: &Core, meta: &BTreeMap<Sym, String>) -> Hashes {
    let empty_set = BTreeSet::new();
    let empty_hashes = Hashes::new();
    core.fns
        .iter()
        .map(|f| {
            // Empty member set and dep map, so every free symbol resolves through
            // the encoder's stray-leaf arm and is committed by name.
            let body = encode(f, &empty_set, None, &empty_hashes);
            let m = meta.get(&f.name).map_or("", String::as_str);
            let blob = format!("{SCHEME}|meta{}:{m}{body}", m.len());
            (f.name, hex(&blob))
        })
        .collect()
}

/// The strongly-connected components of `core`'s dependency graph, callee-first.
///
/// Each component is the recursive group that must be hashed (and stored) as a
/// unit. A singleton is the common case; a cycle (mutual recursion) is a group
/// of two or more whose members' hashes fold in each other.
#[must_use]
pub fn scc_groups(core: &Core) -> Vec<Vec<Sym>> {
    let fnmap: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();
    sccs(core, &fnmap)
}

/// Hash one isolated recursive group, given the content hashes of every external
/// dependency it references, and return each member's per-definition hash.
///
/// This is the single-component core of [`hash_program`] (which is this run over
/// each SCC in dependency order, threading one growing hash map). The store calls
/// it to reproduce a stored definition's hash from its group and its dependency
/// hashes alone, with no access to the rest of the program: seeding `deps` as the
/// initial hash map makes every external reference resolve to its substituted
/// hash exactly as it did in the whole-program pass, so a group serialized and
/// read back hashes to the same value it had in context.
#[must_use]
pub fn hash_group(group: &[CoreFn], deps: &Hashes, meta: &BTreeMap<Sym, String>) -> Hashes {
    let members: Vec<Sym> = group.iter().map(|f| f.name).collect();
    let member_set: BTreeSet<Sym> = members.iter().copied().collect();
    let fnmap: BTreeMap<Sym, &CoreFn> = group.iter().map(|f| (f.name, f)).collect();
    let mut hashes = deps.clone();
    hash_component(&members, &member_set, &fnmap, meta, &mut hashes);
    members
        .iter()
        .filter_map(|m| hashes.get(m).map(|h| (*m, h.clone())))
        .collect()
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
        // Length-prefix the free-form meta (same `{len}:{payload}` discipline as
        // every other field) so its bytes cannot forge a `|meta:` member boundary
        // and collide two distinct components.
        let m_str = meta.get(m).map_or("", String::as_str);
        let _ = write!(blob, "|meta{}:{m_str}", m_str.len());
        blob.push_str(&encode(fnmap[m], member_set, Some(&idx), hashes));
    }
    let component = hex(&blob);

    for (i, (_, m)) in order.iter().enumerate() {
        hashes.insert(*m, hex(&format!("{component}:{i}")));
    }
}

pub(crate) fn hex(s: &str) -> Digest {
    Digest(blake3::hash(s.as_bytes()).to_hex().to_string())
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
        var_ids: BTreeMap::new(),
    };
    let _ = write!(e.out, "fn{}d{}", f.params.len(), f.dict_arity);
    e.comp(&f.body);
    e.out
}

struct Enc<'a> {
    member_set: &'a BTreeSet<Sym>,
    idx: Option<&'a BTreeMap<Sym, usize>>,
    hashes: &'a Hashes,
    env: Vec<Sym>,
    out: String,
    // Canonical, per-definition renumbering of the compiler-generated `var`
    // operations. A `var x` desugars to State ops named `get@x@n`/`set@x@n`,
    // where `x` is the user's chosen name and `n` a *global* State index assigned
    // in definition order. Neither is behavior: renaming the `var` or reordering
    // top-level definitions must not move the hash (a stated content-addressing
    // guarantee). This maps each distinct State index to an id assigned by first
    // occurrence in the structural walk, so the get/set pair of one variable
    // share an id and the numbering is reorder- and rename-invariant.
    var_ids: BTreeMap<String, u32>,
}

impl Enc<'_> {
    /// Length-prefixed token, so no name or string can be confused with its
    /// neighbours in the encoding.
    fn tok(&mut self, s: &str) {
        let _ = write!(self.out, "{}:{s}", s.len());
    }

    /// Encode an effect-operation name, canonicalizing the compiler-generated
    /// `var` operations so a `var` rename or a definition reorder does not move
    /// the hash. A user-declared effect op is committed verbatim (renaming it is
    /// a behavioral change, by design); only the `get@x@n`/`set@x@n` forms minted
    /// by `var` desugaring are renumbered.
    fn op_tok(&mut self, name: &str) {
        let canon = self.op_name_canon(name);
        self.tok(&canon);
    }

    // The canonical spelling of an effect-op name: `get@x@n`/`set@x@n` become
    // `get@#k`/`set@#k`, dropping the user variable name and mapping the global
    // State index `n` to a per-definition id `k` assigned by first occurrence.
    // Because the id keys on the shared State index, the get and set of one `var`
    // resolve to the same `k` whichever the walk reaches first. Any non-`var`
    // name is returned unchanged.
    fn op_name_canon(&mut self, name: &str) -> String {
        let Some((verb, idx)) = crate::names::parse_var_get(name)
            .map(|(_, n)| ("get", n))
            .or_else(|| crate::names::parse_var_set(name).map(|(_, n)| ("set", n)))
        else {
            return name.to_string();
        };
        let next = u32::try_from(self.var_ids.len()).unwrap_or(u32::MAX);
        let id = *self.var_ids.entry(idx.to_string()).or_insert(next);
        format!("{verb}@#{id}")
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
            // Unboxed products get their own tags (`P`, `R`), appended without a
            // scheme bump: no boxed program constructs these nodes, so existing
            // content hashes are untouched.
            Value::UnboxedTuple(args) => {
                self.out.push('P');
                self.vals(args);
            }
            Value::UnboxedRecord(fields) => {
                self.out.push('R');
                self.out.push('{');
                for (n, v) in fields {
                    self.tok(n.as_str());
                    self.val(v);
                }
                self.out.push('}');
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
            | Comp::Error(v)
            | Comp::Dup(v)
            | Comp::Drop(v)
            | Comp::RefNew(v)
            | Comp::RefGet(v) => self.val(v),
            // The `<{kind}>` prefix above already distinguishes the op, so hashing
            // the operands in order reproduces the old per-variant byte sequence
            // exactly (one value for the output/seed ops, none for the inputs).
            Comp::Io(_, args) => {
                for v in args {
                    self.val(v);
                }
            }
            Comp::FloatBuiltin(op, v) => {
                self.tok(op.hash_tag());
                self.val(v);
            }
            Comp::Neg(lane, v) => {
                self.tok(lane.hash_tag());
                self.val(v);
            }
            Comp::UnboxedProject(v, field) => {
                self.val(v);
                self.tok(field.as_str());
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
                self.tok(op.hash_tag());
                self.val(a);
                self.val(b);
            }
            // The call head is a dependency reference, so substitution applies.
            Comp::Call(name, args) => {
                self.refer(*name);
                self.vals(args);
            }
            // Effect operation: a leaf, committed by name (generated `var` ops
            // canonicalized so a rename or reorder does not move the hash).
            Comp::Do(op, args) => {
                self.op_tok(op.as_str());
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
                // Handler clauses form a set, so encode in name order. The sort
                // key is the *canonical* op name, so a generated `var` handler
                // orders and renumbers with its matching `do`: two revisions that
                // differ only by a `var` rename or a definition reorder emit the
                // clauses in the same order. The body was walked first, so every
                // `var` op's id is already fixed by program order.
                let mut ops: Vec<(String, &HandleOp)> = ops
                    .iter()
                    .map(|op| (self.op_name_canon(op.name.as_str()), op))
                    .collect();
                ops.sort_by(|a, b| a.0.cmp(&b.0));
                self.out.push('{');
                for (canon, op) in ops {
                    self.tok(&canon);
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
                self.tok(b.hash_tag());
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
            Comp::RefSet(a, b) | Comp::InitAt(a, b) => {
                self.val(a);
                self.val(b);
            }
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
    // here is not part of the hash contract.
    crate::util::scc::tarjan_scc(&adj)
        .into_iter()
        .map(|comp| comp.into_iter().map(|i| order[i]).collect())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{hash_program, Digest, Sym};
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
                dict_arity: 0,
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

    // `fn f() = do get@<var>@<idx>()`, a `var` read. The `var` name and the global
    // State index carried in the generated op name are not behavior, so a rename
    // (`n` -> `cur`) or a reorder (a different index) must not move the hash.
    fn var_read(var: &str, idx: u32) -> Core {
        let op = crate::names::var_get(var, idx);
        Core {
            fns: vec![CoreFn {
                name: sym("f"),
                params: vec![],
                dict_arity: 0,
                body: Comp::Do(sym(&op), vec![]),
            }],
        }
    }

    #[test]
    fn generated_var_ops_are_rename_and_reorder_invariant() {
        let m = BTreeMap::new();
        // A `var` rename (n -> cur) and a State-index shift (0 -> 7, as a reorder
        // would produce) both leave the behavior hash fixed.
        assert_eq!(
            hash_program(&var_read("n", 0), &m)[&sym("f")],
            hash_program(&var_read("cur", 7), &m)[&sym("f")],
        );
        // A genuinely different (user-declared) effect op is still committed by
        // name, so it does not collide with a `var` op.
        let real = Core {
            fns: vec![CoreFn {
                name: sym("f"),
                params: vec![],
                dict_arity: 0,
                body: Comp::Do(sym("ask"), vec![]),
            }],
        };
        assert_ne!(
            hash_program(&var_read("n", 0), &m)[&sym("f")],
            hash_program(&real, &m)[&sym("f")],
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
    fn dictionary_arity_is_folded_in() {
        let mk = |dict_arity| Core {
            fns: vec![CoreFn {
                name: sym("f"),
                params: vec![sym("a"), sym("b")],
                dict_arity,
                body: Comp::Return(Value::Var(sym("b"))),
            }],
        };
        let m = BTreeMap::new();
        assert_ne!(
            hash_program(&mk(0), &m)[&sym("f")],
            hash_program(&mk(1), &m)[&sym("f")],
        );
    }

    // A caller hashed with `hash_group`, seeded with its callee's whole-program
    // hash, matches the caller's hash in the whole-program pass. This is the store
    // invariant: a definition's hash is reproducible from its group plus its
    // dependency hashes, with no access to the rest of the program.
    #[test]
    fn hash_group_matches_whole_program() {
        // `g` calls `f`; two separate size-one SCCs, `f` a dependency of `g`.
        let f = CoreFn {
            name: sym("f"),
            params: vec![sym("x")],
            dict_arity: 0,
            body: Comp::Return(Value::Var(sym("x"))),
        };
        let g = CoreFn {
            name: sym("g"),
            params: vec![sym("y")],
            dict_arity: 0,
            body: Comp::Call(sym("f"), vec![Value::Var(sym("y"))]),
        };
        let core = Core {
            fns: vec![f, g.clone()],
        };
        let meta = BTreeMap::new();
        let whole = hash_program(&core, &meta);
        // `g`'s group is `{g}`; its only external dependency is `f`.
        let deps = BTreeMap::from([(sym("f"), whole[&sym("f")].clone())]);
        let group = super::hash_group(&[g], &deps, &meta);
        assert_eq!(group[&sym("g")], whole[&sym("g")]);
    }

    #[test]
    fn hashing_is_deterministic() {
        let (core, m) = (let_id("y"), BTreeMap::new());
        assert_eq!(hash_program(&core, &m), hash_program(&core, &m));
    }

    #[test]
    fn root_is_deterministic_and_order_independent() {
        let mut a = BTreeMap::new();
        a.insert("map".to_string(), Digest::from("aaa"));
        a.insert("filter".to_string(), Digest::from("bbb"));
        // A different insertion order yields the same sorted map, so the same root.
        let mut b = BTreeMap::new();
        b.insert("filter".to_string(), Digest::from("bbb"));
        b.insert("map".to_string(), Digest::from("aaa"));
        assert_eq!(super::root(&a), super::root(&b));
    }

    #[test]
    fn root_moves_under_rename_or_content_change() {
        let base = BTreeMap::from([("map".to_string(), Digest::from("aaa"))]);
        // Renaming the binding (same content hash, new name) changes the root:
        // the namespace commits to the public name.
        let renamed = BTreeMap::from([("fmap".to_string(), Digest::from("aaa"))]);
        // Changing the behavior hash under the same name changes it too.
        let rebodied = BTreeMap::from([("map".to_string(), Digest::from("zzz"))]);
        assert_ne!(super::root(&base), super::root(&renamed));
        assert_ne!(super::root(&base), super::root(&rebodied));
    }
}
