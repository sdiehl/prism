//! The `def`-kind wire codec: the reversible bytes between one elaborated
//! anonymous definition and the compact frame the store persists.
//!
//! # The envelope
//!
//! A stored definition is the one wire envelope, read left to right, each header
//! part checked before the next is touched (the same discipline as
//! `lib/std/Wire.pr`, self-contained here because this codec serializes the
//! compiler's own Core, not Prism-level values):
//!
//! ```text
//!   +------------+------+------------------+--------------+
//!   | scheme tag | kind | contract digest  |     body     |
//!   +------------+------+------------------+--------------+
//!
//!   scheme tag       length-prefixed string, "prism-core-hash-v1"; a foreign
//!                    scheme is rejected before anything else
//!   kind             uvarint, the def kind (WireKind::Def)
//!   contract digest  length-prefixed hex, the definition's content hash, so a
//!                    reader knows the identity before decoding the body
//!   body             the node table below
//! ```
//!
//! # The body: a hash-consed node table over one recursive group
//!
//! ```text
//!   member_count K: uvarint  members of the recursive group (1 for most defs)
//!   target        : uvarint  which member this object is keyed by (< K)
//!   dep_count D   : uvarint  distinct external dependency hashes referenced
//!   deps[D]       : string   those content hashes, in first-reference order
//!   node_count N  : uvarint  size of the shared node table (all members)
//!   nodes[N]      : node     topologically ordered: every child index < its own
//!                            index, so decode is a single forward pass
//!   members[K]:
//!     param_count : uvarint  outermost binders (the member's parameters)
//!     dict_arity  : uvarint  leading params that are dictionaries
//!     meta        : string   the elaboration metadata the content hash commits to
//!     root        : uvarint  the node index of this member's root computation
//! ```
//!
//! Each node is serialized once and referenced by index; a subexpression that
//! occurs more than once is one entry, referenced from each occurrence (the
//! hash-consing). Two nodes are the same entry exactly when they are equal under
//! the content hash's rules: a variable is a de Bruijn index (outward distance to
//! its binder), a call to another definition is that definition's content hash
//! (indexed through `deps`), a self-call is an intra-group reference, and a leaf
//! (a constructor, an effect operation, a builtin) is its stable name. So the
//! serialized graph and [`crate::core::hash_group`] agree by construction: a
//! decoded definition re-hashes to the same content hash it had in context, which
//! [`Decoded::rehash`] checks.
//!
//! # Totality
//!
//! [`decode_def`] never panics on hostile bytes. Every varint is byte-capped,
//! every length is bounded, the scheme and kind are checked before the body,
//! child indices are range-checked against the already-parsed prefix, graph
//! reconstruction runs against an expansion budget (so a shared-DAG bomb cannot
//! blow up), and trailing bytes are rejected.

use std::collections::{BTreeMap, HashMap};

use crate::core::builtins::{Builtin, FloatOp};
use crate::core::{hash_group, Comp, CoreFn, CoreOp, CorePat, HandleOp, Hashes, IoOp, Value};
use crate::driver::WireKind;
use crate::sym::Sym;

use super::CodecError;

// Byte discipline shared with `lib/std/Wire.pr`, restated for the compiler's
// store: a varint is capped so a hostile all-continuation run cannot read
// forever, and a length prefix is bounded so a hostile count cannot force
// unbounded work.
const VARINT_MAX_BYTES: usize = 10;
const VARINT_CONT: u8 = 0x80;
const VARINT_LOW: u64 = 0x7f;
const WIRE_LEN_MAX: u64 = 1 << 20;

// The node table and the reconstructed graph are both bounded: a table larger
// than this, or a reconstruction that expands past this many nodes (a shared-DAG
// blow-up), is rejected rather than allowed to exhaust memory.
const MAX_NODES: u64 = 1 << 20;
const MAX_EXPANSION: usize = 1 << 22;

/// Everything the anonymous encoding of one stored object draws on. The store
/// layer builds this from the pipeline it already runs; the codec never performs
/// IO or touches the pipeline.
///
/// An object is one recursive group (a strongly-connected component of the
/// dependency graph), the unit the content hash folds as a whole: a singleton for
/// the common case, a cycle for mutual recursion. Every member's hash commits to
/// every other member's body, so the whole group travels in each member's object
/// and `target` names which member this object is keyed by.
#[derive(Debug)]
pub struct AnonEntry<'a> {
    /// The group's members. A self-call, or a call to a sibling, serializes as an
    /// intra-group reference; a call outside the group serializes as a hash.
    pub group: &'a [&'a CoreFn],
    /// Which member this object is keyed by (its hash is the contract).
    pub target: usize,
    /// The target member's content hash: the store key and the frame's contract.
    pub hash: &'a str,
    /// Content hashes keyed by canonical symbol, so a reference to a definition
    /// outside the group serializes as that definition's hash exactly as the
    /// content hash substitutes it. The whole program's hash map is fine to pass;
    /// group members resolve to intra-group references before it is consulted, and
    /// only genuinely external, referenced entries are stored.
    pub deps: &'a Hashes,
    /// Each member's out-of-Core elaboration inputs the content hash commits to
    /// (type, principal row, fip/fbip, borrow mask), rendered to one string each
    /// by the hasher and keyed by member symbol. Opaque to the codec; round-tripped
    /// verbatim.
    pub meta: &'a BTreeMap<Sym, String>,
}

/// One stored object read back: the reconstructed recursive group plus enough
/// context to reproduce the target member's content hash without the rest of the
/// program.
///
/// The reconstructed group is anonymous, so binders and every member's symbol are
/// fresh; the content hash is name-independent, so this does not change the hash.
/// [`Decoded::rehash`] recomputes it.
#[derive(Debug, Clone)]
pub struct Decoded {
    /// The content hash the frame carried (the store key of the target member).
    pub contract: String,
    /// The reconstructed group members. Symbols and binders are fresh.
    pub group: Vec<CoreFn>,
    /// Which member this object is keyed by, an index into `group`.
    pub target: usize,
    /// The external dependency content hashes, in the frame's order.
    pub dep_hashes: Vec<String>,
    /// The dependency hashes keyed by the fresh symbol the reconstructed bodies
    /// call them through, ready to seed [`crate::core::hash_group`].
    pub deps: Hashes,
    /// Each member's elaboration metadata string, keyed by its fresh symbol.
    pub meta: BTreeMap<Sym, String>,
    /// The size of the serialized node table: distinct hash-consed nodes, so a
    /// shared subexpression counts once however many times it occurs, across every
    /// member of the group.
    pub node_count: usize,
}

impl Decoded {
    /// The member this object is keyed by.
    #[must_use]
    pub fn target_func(&self) -> &CoreFn {
        &self.group[self.target]
    }

    /// Recompute the target member's content hash from the reconstructed group and
    /// its dependency hashes. Equal to the hash it had in its original
    /// whole-program context: the store's central invariant.
    #[must_use]
    pub fn rehash(&self) -> Option<String> {
        hash_group(&self.group, &self.deps, &self.meta)
            .get(&self.group[self.target].name)
            .cloned()
    }
}

// The node-table tag: one discriminant for every Core value and computation
// shape. Encoded as a uvarint; the array below is the single source of truth for
// the numbering, so encode (`as u8`) and decode (index into the array) cannot
// drift.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Tag {
    VVar,
    VInt,
    VI64,
    VU64,
    VFloat,
    VBool,
    VUnit,
    VStr,
    VThunk,
    VCtor,
    VTuple,
    CReturn,
    CBind,
    CForce,
    CLam,
    CApp,
    CIf,
    CPrim,
    CCall,
    CIo,
    CError,
    CCase,
    CFloat,
    CDo,
    CHandle,
    CMask,
    CStr,
    CDup,
    CDrop,
    CWithReuse,
    CReuse,
    CRefNew,
    CRefGet,
    CRefSet,
}

const TAGS: &[Tag] = &[
    Tag::VVar,
    Tag::VInt,
    Tag::VI64,
    Tag::VU64,
    Tag::VFloat,
    Tag::VBool,
    Tag::VUnit,
    Tag::VStr,
    Tag::VThunk,
    Tag::VCtor,
    Tag::VTuple,
    Tag::CReturn,
    Tag::CBind,
    Tag::CForce,
    Tag::CLam,
    Tag::CApp,
    Tag::CIf,
    Tag::CPrim,
    Tag::CCall,
    Tag::CIo,
    Tag::CError,
    Tag::CCase,
    Tag::CFloat,
    Tag::CDo,
    Tag::CHandle,
    Tag::CMask,
    Tag::CStr,
    Tag::CDup,
    Tag::CDrop,
    Tag::CWithReuse,
    Tag::CReuse,
    Tag::CRefNew,
    Tag::CRefGet,
    Tag::CRefSet,
];

impl Tag {
    fn from_u64(n: u64) -> Result<Self, CodecError> {
        usize::try_from(n)
            .ok()
            .and_then(|i| TAGS.get(i).copied())
            .ok_or(CodecError::Malformed)
    }
}

// How a symbol reference resolves, mirroring the content hash's `refer`: an
// enclosing binder (de Bruijn distance), the sole group member (a self-call), an
// external dependency (an index into the dep table), or a leaf name.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum RefTag {
    Bound,
    Member,
    Dep,
    Global,
}

const REF_TAGS: &[RefTag] = &[RefTag::Bound, RefTag::Member, RefTag::Dep, RefTag::Global];

impl RefTag {
    fn from_u64(n: u64) -> Result<Self, CodecError> {
        usize::try_from(n)
            .ok()
            .and_then(|i| REF_TAGS.get(i).copied())
            .ok_or(CodecError::Malformed)
    }
}

// The pattern shapes a `Case` arm can test (literals and records compile away
// upstream), encoded inline in the arm rather than as their own table nodes.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum PatTag {
    Wild,
    Var,
    Ctor,
    Tuple,
}

const PAT_TAGS: &[PatTag] = &[PatTag::Wild, PatTag::Var, PatTag::Ctor, PatTag::Tuple];

impl PatTag {
    fn from_u64(n: u64) -> Result<Self, CodecError> {
        usize::try_from(n)
            .ok()
            .and_then(|i| PAT_TAGS.get(i).copied())
            .ok_or(CodecError::Malformed)
    }
}

// The leaf-operator families, each an ordered table that is the single source of
// truth for its wire numbering. A new enum variant must be appended here; encode
// panics on a variant it cannot find (a codec bug on trusted input), decode
// rejects an index it does not know.
const CORE_OPS: &[CoreOp] = &[
    CoreOp::Add,
    CoreOp::Sub,
    CoreOp::Mul,
    CoreOp::Div,
    CoreOp::Rem,
    CoreOp::Eq,
    CoreOp::Ne,
    CoreOp::Lt,
    CoreOp::Le,
    CoreOp::Gt,
    CoreOp::Ge,
    CoreOp::Addf,
    CoreOp::Subf,
    CoreOp::Mulf,
    CoreOp::Divf,
    CoreOp::Eqf,
    CoreOp::Nef,
    CoreOp::Ltf,
    CoreOp::Lef,
    CoreOp::Gtf,
    CoreOp::Gef,
];

const IO_OPS: &[IoOp] = &[
    IoOp::Print,
    IoOp::PrintF,
    IoOp::PrintS,
    IoOp::PrintNl,
    IoOp::ReadInt,
    IoOp::ReadLine,
    IoOp::Rand,
    IoOp::Srand,
];

const FLOAT_OPS: &[FloatOp] = &[
    FloatOp::ToFloat,
    FloatOp::Truncate,
    FloatOp::FloorToInt,
    FloatOp::CeilToInt,
    FloatOp::AbsFloat,
    FloatOp::Sqrt,
    FloatOp::Sin,
    FloatOp::Cos,
    FloatOp::Exp,
    FloatOp::Ln,
];

const BUILTINS: &[Builtin] = &[
    Builtin::Concat,
    Builtin::StrLen,
    Builtin::StrEq,
    Builtin::StrCmp,
    Builtin::Substring,
    Builtin::CharAt,
    Builtin::ShowChar,
    Builtin::Blake3,
    Builtin::ParseInt,
    Builtin::BigLit,
    Builtin::ParseFloat,
    Builtin::PowFloat,
    Builtin::ShowFloatPrec,
    Builtin::Getenv,
    Builtin::ReadFile,
    Builtin::WriteFile,
    Builtin::FileExists,
    Builtin::AppendFile,
    Builtin::RemoveFile,
    Builtin::Exit,
    Builtin::System,
    Builtin::Eprint,
    Builtin::ArgsCount,
    Builtin::Arg,
    Builtin::ShowInt,
    Builtin::ShowI64,
    Builtin::ShowU64,
    Builtin::ShowBool,
    Builtin::ShowFloat,
    Builtin::ToI64,
    Builtin::ToU64,
    Builtin::IntOfI64,
    Builtin::IntOfU64,
    Builtin::I64Add,
    Builtin::I64Sub,
    Builtin::I64Mul,
    Builtin::I64Div,
    Builtin::U64Div,
    Builtin::I64Rem,
    Builtin::U64Rem,
    Builtin::I64Cmp,
    Builtin::U64Cmp,
    Builtin::U64Add,
    Builtin::U64Sub,
    Builtin::U64Mul,
    Builtin::ByteAt,
    Builtin::ByteLen,
    Builtin::StringOfBytes,
    Builtin::ArrayPop,
    Builtin::I64And,
    Builtin::I64Or,
    Builtin::I64Xor,
    Builtin::I64Shl,
    Builtin::I64Shr,
    Builtin::U64And,
    Builtin::U64Or,
    Builtin::U64Xor,
    Builtin::U64Shl,
    Builtin::U64Shr,
    Builtin::ArrayNew,
    Builtin::ArrayEmpty,
    Builtin::ArrayLen,
    Builtin::ArrayGet,
    Builtin::ArraySet,
    Builtin::ArrayPush,
    Builtin::StringOfArray,
    Builtin::SortPrim,
    Builtin::TaqSnoc,
    Builtin::TaqConcat,
    Builtin::TaqUncons,
];

fn op_wire<T: PartialEq + Copy>(table: &[T], op: T) -> u64 {
    table
        .iter()
        .position(|x| *x == op)
        .map(|i| i as u64)
        .expect("operator missing from codec table (append it)")
}

fn op_from_wire<T: Copy>(table: &[T], n: u64) -> Result<T, CodecError> {
    usize::try_from(n)
        .ok()
        .and_then(|i| table.get(i))
        .copied()
        .ok_or(CodecError::Malformed)
}

// ------------------------------- encoding ----------------------------------

pub(super) fn put_uvarint(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let lo = (n & VARINT_LOW) as u8;
        n >>= 7;
        if n == 0 {
            out.push(lo);
            return;
        }
        out.push(lo | VARINT_CONT);
    }
}

// Zigzag maps a signed integer to an unsigned one so small negatives stay small
// under LEB128. The casts reinterpret the bit pattern by design, not a lossy
// conversion.
#[allow(clippy::cast_sign_loss)]
const fn zigzag(x: i64) -> u64 {
    ((x << 1) ^ (x >> 63)) as u64
}

#[allow(clippy::cast_possible_wrap)]
const fn unzigzag(z: u64) -> i64 {
    ((z >> 1) as i64) ^ -((z & 1) as i64)
}

fn put_svarint(out: &mut Vec<u8>, x: i64) {
    put_uvarint(out, zigzag(x));
}

pub(super) fn put_str(out: &mut Vec<u8>, s: &str) {
    put_uvarint(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

fn put_tag(out: &mut Vec<u8>, t: Tag) {
    put_uvarint(out, t as u64);
}

fn put_indices(out: &mut Vec<u8>, idxs: &[u32]) {
    put_uvarint(out, idxs.len() as u64);
    for i in idxs {
        put_uvarint(out, u64::from(*i));
    }
}

struct Encoder<'a> {
    members: HashMap<Sym, u64>,
    deps: &'a Hashes,
    dep_order: Vec<String>,
    dep_index: HashMap<String, usize>,
    env: Vec<Sym>,
    table: Vec<Vec<u8>>,
    intern: HashMap<Vec<u8>, u32>,
}

impl<'a> Encoder<'a> {
    fn new(members: HashMap<Sym, u64>, deps: &'a Hashes) -> Self {
        Self {
            members,
            deps,
            dep_order: Vec::new(),
            dep_index: HashMap::new(),
            env: Vec::new(),
            table: Vec::new(),
            intern: HashMap::new(),
        }
    }

    // Intern a node's finished local bytes and return its table index. Identical
    // bytes share one entry; children were interned first, so a child's index is
    // always smaller than its parent's (the topological order decode relies on).
    fn push(&mut self, bytes: Vec<u8>) -> u32 {
        if let Some(i) = self.intern.get(&bytes) {
            return *i;
        }
        // A node table never approaches 2^32 entries; the decode side caps it at
        // MAX_NODES, far below.
        #[allow(clippy::cast_possible_truncation)]
        let i = self.table.len() as u32;
        self.intern.insert(bytes.clone(), i);
        self.table.push(bytes);
        i
    }

    fn dep_slot(&mut self, hash: &str) -> u64 {
        if let Some(i) = self.dep_index.get(hash) {
            return *i as u64;
        }
        let i = self.dep_order.len();
        self.dep_index.insert(hash.to_string(), i);
        self.dep_order.push(hash.to_string());
        i as u64
    }

    // A symbol reference, resolved in the same order the content hash resolves
    // it: enclosing binder, the group member, an external dependency, else a leaf
    // name.
    fn refer(&mut self, out: &mut Vec<u8>, s: Sym) {
        if let Some(pos) = self.env.iter().rposition(|b| *b == s) {
            put_uvarint(out, RefTag::Bound as u64);
            put_uvarint(out, (self.env.len() - 1 - pos) as u64);
        } else if let Some(idx) = self.members.get(&s) {
            put_uvarint(out, RefTag::Member as u64);
            put_uvarint(out, *idx);
        } else if let Some(h) = self.deps.get(&s) {
            let slot = self.dep_slot(h);
            put_uvarint(out, RefTag::Dep as u64);
            put_uvarint(out, slot);
        } else {
            put_uvarint(out, RefTag::Global as u64);
            put_str(out, s.as_str());
        }
    }

    fn scoped<R>(&mut self, binders: &[Sym], body: impl FnOnce(&mut Self) -> R) -> R {
        self.env.extend_from_slice(binders);
        let r = body(self);
        self.env.truncate(self.env.len() - binders.len());
        r
    }

    fn value(&mut self, v: &Value) -> u32 {
        let mut out = Vec::new();
        match v {
            Value::Var(x) => {
                put_tag(&mut out, Tag::VVar);
                self.refer(&mut out, *x);
            }
            Value::Int(n) => {
                put_tag(&mut out, Tag::VInt);
                put_svarint(&mut out, *n);
            }
            Value::I64(n) => {
                put_tag(&mut out, Tag::VI64);
                put_svarint(&mut out, *n);
            }
            Value::U64(n) => {
                put_tag(&mut out, Tag::VU64);
                put_uvarint(&mut out, *n);
            }
            Value::Float(f) => {
                put_tag(&mut out, Tag::VFloat);
                out.extend_from_slice(&f.to_bits().to_le_bytes());
            }
            Value::Bool(b) => {
                put_tag(&mut out, Tag::VBool);
                out.push(u8::from(*b));
            }
            Value::Unit => put_tag(&mut out, Tag::VUnit),
            Value::Str(s) => {
                put_tag(&mut out, Tag::VStr);
                put_str(&mut out, s);
            }
            Value::Thunk(c) => {
                let ci = self.comp(c);
                put_tag(&mut out, Tag::VThunk);
                put_uvarint(&mut out, u64::from(ci));
            }
            Value::Ctor(n, t, args) => {
                let idxs = self.values(args);
                put_tag(&mut out, Tag::VCtor);
                put_str(&mut out, n.as_str());
                put_uvarint(&mut out, *t as u64);
                put_indices(&mut out, &idxs);
            }
            Value::Tuple(args) => {
                let idxs = self.values(args);
                put_tag(&mut out, Tag::VTuple);
                put_indices(&mut out, &idxs);
            }
        }
        self.push(out)
    }

    fn values(&mut self, vs: &[Value]) -> Vec<u32> {
        vs.iter().map(|v| self.value(v)).collect()
    }

    fn write_pat(out: &mut Vec<u8>, p: &CorePat) {
        let fields = |out: &mut Vec<u8>, fs: &[Option<Sym>]| {
            put_uvarint(out, fs.len() as u64);
            for f in fs {
                out.push(u8::from(f.is_some()));
            }
        };
        match p {
            CorePat::Wild => put_uvarint(out, PatTag::Wild as u64),
            CorePat::Var(_) => put_uvarint(out, PatTag::Var as u64),
            CorePat::Ctor(n, fs) => {
                put_uvarint(out, PatTag::Ctor as u64);
                put_str(out, n.as_str());
                fields(out, fs);
            }
            CorePat::Tuple(fs) => {
                put_uvarint(out, PatTag::Tuple as u64);
                fields(out, fs);
            }
        }
    }

    // The binders a pattern introduces, left to right, matching the order the
    // content hash pushes them.
    fn pat_binders(p: &CorePat) -> Vec<Sym> {
        match p {
            CorePat::Wild => Vec::new(),
            CorePat::Var(x) => vec![*x],
            CorePat::Ctor(_, fs) | CorePat::Tuple(fs) => fs.iter().flatten().copied().collect(),
        }
    }

    fn comp(&mut self, c: &Comp) -> u32 {
        let mut out = Vec::new();
        match c {
            Comp::Return(v) => self.unary(&mut out, Tag::CReturn, v),
            Comp::Force(v) => self.unary(&mut out, Tag::CForce, v),
            Comp::Error(v) => self.unary(&mut out, Tag::CError, v),
            Comp::Dup(v) => self.unary(&mut out, Tag::CDup, v),
            Comp::Drop(v) => self.unary(&mut out, Tag::CDrop, v),
            Comp::RefNew(v) => self.unary(&mut out, Tag::CRefNew, v),
            Comp::RefGet(v) => self.unary(&mut out, Tag::CRefGet, v),
            Comp::RefSet(a, b) => {
                let (ai, bi) = (self.value(a), self.value(b));
                put_tag(&mut out, Tag::CRefSet);
                put_uvarint(&mut out, u64::from(ai));
                put_uvarint(&mut out, u64::from(bi));
            }
            Comp::Bind(m, x, n) => {
                let mi = self.comp(m);
                let ni = self.scoped(&[*x], |e| e.comp(n));
                put_tag(&mut out, Tag::CBind);
                put_uvarint(&mut out, u64::from(mi));
                put_uvarint(&mut out, u64::from(ni));
            }
            Comp::Lam(xs, b) => {
                let bi = self.scoped(xs, |e| e.comp(b));
                put_tag(&mut out, Tag::CLam);
                put_uvarint(&mut out, xs.len() as u64);
                put_uvarint(&mut out, u64::from(bi));
            }
            Comp::App(f, args) => {
                let fi = self.comp(f);
                let idxs = self.values(args);
                put_tag(&mut out, Tag::CApp);
                put_uvarint(&mut out, u64::from(fi));
                put_indices(&mut out, &idxs);
            }
            Comp::If(v, t, e) => {
                let vi = self.value(v);
                let (ti, ei) = (self.comp(t), self.comp(e));
                put_tag(&mut out, Tag::CIf);
                put_uvarint(&mut out, u64::from(vi));
                put_uvarint(&mut out, u64::from(ti));
                put_uvarint(&mut out, u64::from(ei));
            }
            Comp::Prim(op, a, b) => {
                let (ai, bi) = (self.value(a), self.value(b));
                put_tag(&mut out, Tag::CPrim);
                put_uvarint(&mut out, op_wire(CORE_OPS, *op));
                put_uvarint(&mut out, u64::from(ai));
                put_uvarint(&mut out, u64::from(bi));
            }
            Comp::Call(name, args) => {
                let idxs = self.values(args);
                put_tag(&mut out, Tag::CCall);
                self.refer(&mut out, *name);
                put_indices(&mut out, &idxs);
            }
            Comp::Io(op, args) => {
                let idxs = self.values(args);
                put_tag(&mut out, Tag::CIo);
                put_uvarint(&mut out, op_wire(IO_OPS, *op));
                put_indices(&mut out, &idxs);
            }
            Comp::FloatBuiltin(op, v) => {
                let vi = self.value(v);
                put_tag(&mut out, Tag::CFloat);
                put_uvarint(&mut out, op_wire(FLOAT_OPS, *op));
                put_uvarint(&mut out, u64::from(vi));
            }
            Comp::Do(op, args) => {
                let idxs = self.values(args);
                put_tag(&mut out, Tag::CDo);
                put_str(&mut out, op.as_str());
                put_indices(&mut out, &idxs);
            }
            Comp::StrBuiltin(b, args) => {
                let idxs = self.values(args);
                put_tag(&mut out, Tag::CStr);
                put_uvarint(&mut out, op_wire(BUILTINS, *b));
                put_indices(&mut out, &idxs);
            }
            Comp::Case(v, arms) => {
                let vi = self.value(v);
                let arm_idxs: Vec<(&CorePat, u32)> = arms
                    .iter()
                    .map(|(p, body)| {
                        let binders = Self::pat_binders(p);
                        let bi = self.scoped(&binders, |e| e.comp(body));
                        (p, bi)
                    })
                    .collect();
                put_tag(&mut out, Tag::CCase);
                put_uvarint(&mut out, u64::from(vi));
                put_uvarint(&mut out, arm_idxs.len() as u64);
                for (p, bi) in arm_idxs {
                    Self::write_pat(&mut out, p);
                    put_uvarint(&mut out, u64::from(bi));
                }
            }
            Comp::Handle {
                body,
                return_var,
                return_body,
                ops,
            } => {
                let bi = self.comp(body);
                let rbi = return_body.as_ref().map(|rb| {
                    let binders: Vec<Sym> = return_var.iter().copied().collect();
                    self.scoped(&binders, |e| e.comp(rb))
                });
                let op_idxs: Vec<(&HandleOp, u32)> = ops
                    .iter()
                    .map(|op| {
                        let mut binders = op.params.clone();
                        binders.push(op.resume);
                        let oi = self.scoped(&binders, |e| e.comp(&op.body));
                        (op, oi)
                    })
                    .collect();
                put_tag(&mut out, Tag::CHandle);
                put_uvarint(&mut out, u64::from(bi));
                out.push(u8::from(return_var.is_some()));
                match rbi {
                    Some(i) => {
                        out.push(1);
                        put_uvarint(&mut out, u64::from(i));
                    }
                    None => out.push(0),
                }
                put_uvarint(&mut out, op_idxs.len() as u64);
                for (op, oi) in op_idxs {
                    put_str(&mut out, op.name.as_str());
                    put_uvarint(&mut out, op.params.len() as u64);
                    put_uvarint(&mut out, u64::from(oi));
                }
            }
            Comp::Mask(ops, b) => {
                let bi = self.comp(b);
                put_tag(&mut out, Tag::CMask);
                put_uvarint(&mut out, ops.len() as u64);
                for o in ops {
                    put_str(&mut out, o.as_str());
                }
                put_uvarint(&mut out, u64::from(bi));
            }
            Comp::WithReuse { token, freed, body } => {
                let fi = self.value(freed);
                let bi = self.scoped(&[*token], |e| e.comp(body));
                put_tag(&mut out, Tag::CWithReuse);
                put_uvarint(&mut out, u64::from(fi));
                put_uvarint(&mut out, u64::from(bi));
            }
            Comp::Reuse(token, v) => {
                let vi = self.value(v);
                put_tag(&mut out, Tag::CReuse);
                self.refer(&mut out, *token);
                put_uvarint(&mut out, u64::from(vi));
            }
        }
        self.push(out)
    }

    fn unary(&mut self, out: &mut Vec<u8>, t: Tag, v: &Value) {
        let vi = self.value(v);
        put_tag(out, t);
        put_uvarint(out, u64::from(vi));
    }
}

/// Encode one definition's anonymous payload as a `def`-kind frame.
///
/// Deterministic in `entry`: the same group (up to the fresh binder names the
/// hash ignores) encodes to byte-identical output, so an unchanged hash re-commits
/// the same bytes. Panics only on a codec bug (a Core operator absent from the
/// tables above), never on well-formed input.
#[must_use]
pub fn encode_def(entry: &AnonEntry<'_>) -> Vec<u8> {
    let member_index: HashMap<Sym, u64> = entry
        .group
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name, i as u64))
        .collect();
    let mut enc = Encoder::new(member_index, entry.deps);

    // Intern every member's body into the one shared node table (so a subexpression
    // shared across members is stored once), collecting each member's own header.
    let roots: Vec<(usize, usize, &str, u32)> = entry
        .group
        .iter()
        .map(|f| {
            let params = f.params.clone();
            let root = enc.scoped(&params, |e| e.comp(&f.body));
            let meta = entry.meta.get(&f.name).map_or("", String::as_str);
            (f.params.len(), f.dict_arity, meta, root)
        })
        .collect();

    let mut out = Vec::new();
    put_str(&mut out, crate::core::HASH_SCHEME);
    put_uvarint(&mut out, u64::from(WireKind::Def.varint()));
    put_str(&mut out, entry.hash);

    put_uvarint(&mut out, entry.group.len() as u64);
    put_uvarint(&mut out, entry.target as u64);
    put_uvarint(&mut out, enc.dep_order.len() as u64);
    for h in &enc.dep_order {
        put_str(&mut out, h);
    }
    put_uvarint(&mut out, enc.table.len() as u64);
    for node in &enc.table {
        out.extend_from_slice(node);
    }
    for (param_count, dict_arity, meta, root) in roots {
        put_uvarint(&mut out, param_count as u64);
        put_uvarint(&mut out, dict_arity as u64);
        put_str(&mut out, meta);
        put_uvarint(&mut out, u64::from(root));
    }
    out
}

// ------------------------------- decoding ----------------------------------

pub(super) struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub(super) const fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    // Whether every byte has been consumed, the trailing-byte check a total
    // decoder performs before it trusts a frame.
    pub(super) const fn at_end(&self) -> bool {
        self.pos == self.buf.len()
    }

    fn byte(&mut self) -> Result<u8, CodecError> {
        let b = *self.buf.get(self.pos).ok_or(CodecError::Truncated)?;
        self.pos += 1;
        Ok(b)
    }

    pub(super) fn uvarint(&mut self) -> Result<u64, CodecError> {
        let mut acc: u64 = 0;
        let mut shift = 0;
        for _ in 0..VARINT_MAX_BYTES {
            let b = self.byte()?;
            acc |= (u64::from(b) & VARINT_LOW) << shift;
            if b & VARINT_CONT == 0 {
                return Ok(acc);
            }
            shift += 7;
        }
        Err(CodecError::Truncated)
    }

    fn svarint(&mut self) -> Result<i64, CodecError> {
        Ok(unzigzag(self.uvarint()?))
    }

    fn bounded_len(&mut self) -> Result<usize, CodecError> {
        let n = self.uvarint()?;
        if n > WIRE_LEN_MAX {
            return Err(CodecError::TooLarge);
        }
        usize::try_from(n).map_err(|_| CodecError::TooLarge)
    }

    pub(super) fn string(&mut self) -> Result<String, CodecError> {
        let n = self.bounded_len()?;
        let end = self.pos.checked_add(n).ok_or(CodecError::Truncated)?;
        let slice = self.buf.get(self.pos..end).ok_or(CodecError::Truncated)?;
        let s = std::str::from_utf8(slice).map_err(|_| CodecError::Utf8)?;
        self.pos = end;
        Ok(s.to_string())
    }

    fn float(&mut self) -> Result<f64, CodecError> {
        let end = self.pos.checked_add(8).ok_or(CodecError::Truncated)?;
        let slice = self.buf.get(self.pos..end).ok_or(CodecError::Truncated)?;
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(slice);
        self.pos = end;
        Ok(f64::from_bits(u64::from_le_bytes(bytes)))
    }

    fn bool(&mut self) -> Result<bool, CodecError> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(CodecError::Malformed),
        }
    }

    // A node reference: an index into the table strictly below the node being
    // parsed, so the graph is acyclic and decode is a forward pass.
    fn node_ref(&mut self, below: u32) -> Result<u32, CodecError> {
        let i = self.uvarint()?;
        let i = u32::try_from(i).map_err(|_| CodecError::BadReference)?;
        if i >= below {
            return Err(CodecError::BadReference);
        }
        Ok(i)
    }

    fn node_refs(&mut self, below: u32) -> Result<Vec<u32>, CodecError> {
        let n = self.bounded_len()?;
        (0..n).map(|_| self.node_ref(below)).collect()
    }

    fn reference(&mut self, member_count: usize, dep_count: usize) -> Result<Ref, CodecError> {
        match RefTag::from_u64(self.uvarint()?)? {
            RefTag::Bound => Ok(Ref::Bound(self.uvarint()?)),
            RefTag::Member => {
                let i = usize::try_from(self.uvarint()?).map_err(|_| CodecError::BadReference)?;
                if i >= member_count {
                    return Err(CodecError::BadReference);
                }
                Ok(Ref::Member(i))
            }
            RefTag::Dep => {
                let i = usize::try_from(self.uvarint()?).map_err(|_| CodecError::BadReference)?;
                if i >= dep_count {
                    return Err(CodecError::BadReference);
                }
                Ok(Ref::Dep(i))
            }
            RefTag::Global => Ok(Ref::Global(self.string()?)),
        }
    }
}

#[derive(Clone)]
enum Ref {
    Bound(u64),
    Member(usize),
    Dep(usize),
    Global(String),
}

#[derive(Clone)]
struct RawPat {
    tag: PatTag,
    name: String,
    fields: Vec<bool>,
}

// A node parsed into structure, its children still indices into the table. The
// forward pass builds the whole table, then reconstruction walks it from the
// root, materializing binders.
#[derive(Clone)]
enum Node {
    Var(Ref),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Thunk(u32),
    Ctor(String, u64, Vec<u32>),
    Tuple(Vec<u32>),
    Return(u32),
    Bind(u32, u32),
    Force(u32),
    Lam(u64, u32),
    App(u32, Vec<u32>),
    If(u32, u32, u32),
    Prim(CoreOp, u32, u32),
    Call(Ref, Vec<u32>),
    Io(IoOp, Vec<u32>),
    Error(u32),
    Case(u32, Vec<(RawPat, u32)>),
    FloatOp(FloatOp, u32),
    Do(String, Vec<u32>),
    Handle {
        body: u32,
        ret_var: bool,
        ret_body: Option<u32>,
        ops: Vec<(String, u64, u32)>,
    },
    Mask(Vec<String>, u32),
    StrOp(Builtin, Vec<u32>),
    Dup(u32),
    Drop(u32),
    WithReuse(u32, u32),
    Reuse(Ref, u32),
    RefNew(u32),
    RefGet(u32),
    RefSet(u32, u32),
}

fn parse_pat_fields(r: &mut Reader<'_>) -> Result<Vec<bool>, CodecError> {
    let n = r.bounded_len()?;
    (0..n).map(|_| r.bool()).collect()
}

fn parse_pat(r: &mut Reader<'_>) -> Result<RawPat, CodecError> {
    let tag = PatTag::from_u64(r.uvarint()?)?;
    let (name, fields) = match tag {
        PatTag::Wild | PatTag::Var => (String::new(), Vec::new()),
        PatTag::Ctor => {
            let name = r.string()?;
            (name, parse_pat_fields(r)?)
        }
        PatTag::Tuple => (String::new(), parse_pat_fields(r)?),
    };
    Ok(RawPat { tag, name, fields })
}

fn parse_node(
    r: &mut Reader<'_>,
    index: u32,
    member_count: usize,
    dep_count: usize,
) -> Result<Node, CodecError> {
    let node = match Tag::from_u64(r.uvarint()?)? {
        Tag::VVar => Node::Var(r.reference(member_count, dep_count)?),
        Tag::VInt => Node::Int(r.svarint()?),
        Tag::VI64 => Node::I64(r.svarint()?),
        Tag::VU64 => Node::U64(r.uvarint()?),
        Tag::VFloat => Node::Float(r.float()?),
        Tag::VBool => Node::Bool(r.bool()?),
        Tag::VUnit => Node::Unit,
        Tag::VStr => Node::Str(r.string()?),
        Tag::VThunk => Node::Thunk(r.node_ref(index)?),
        Tag::VCtor => {
            let name = r.string()?;
            let t = r.uvarint()?;
            Node::Ctor(name, t, r.node_refs(index)?)
        }
        Tag::VTuple => Node::Tuple(r.node_refs(index)?),
        Tag::CReturn => Node::Return(r.node_ref(index)?),
        Tag::CBind => Node::Bind(r.node_ref(index)?, r.node_ref(index)?),
        Tag::CForce => Node::Force(r.node_ref(index)?),
        Tag::CLam => Node::Lam(r.uvarint()?, r.node_ref(index)?),
        Tag::CApp => Node::App(r.node_ref(index)?, r.node_refs(index)?),
        Tag::CIf => Node::If(r.node_ref(index)?, r.node_ref(index)?, r.node_ref(index)?),
        Tag::CPrim => {
            let op = op_from_wire(CORE_OPS, r.uvarint()?)?;
            Node::Prim(op, r.node_ref(index)?, r.node_ref(index)?)
        }
        Tag::CCall => {
            let head = r.reference(member_count, dep_count)?;
            Node::Call(head, r.node_refs(index)?)
        }
        Tag::CIo => {
            let op = op_from_wire(IO_OPS, r.uvarint()?)?;
            Node::Io(op, r.node_refs(index)?)
        }
        Tag::CError => Node::Error(r.node_ref(index)?),
        Tag::CCase => {
            let scrut = r.node_ref(index)?;
            let n_arms = r.bounded_len()?;
            let arms = (0..n_arms)
                .map(|_| Ok((parse_pat(r)?, r.node_ref(index)?)))
                .collect::<Result<Vec<_>, CodecError>>()?;
            Node::Case(scrut, arms)
        }
        Tag::CFloat => {
            let op = op_from_wire(FLOAT_OPS, r.uvarint()?)?;
            Node::FloatOp(op, r.node_ref(index)?)
        }
        Tag::CDo => {
            let op = r.string()?;
            Node::Do(op, r.node_refs(index)?)
        }
        Tag::CHandle => {
            let body = r.node_ref(index)?;
            let ret_var = r.bool()?;
            let ret_body = if r.bool()? {
                Some(r.node_ref(index)?)
            } else {
                None
            };
            let n_ops = r.bounded_len()?;
            let ops = (0..n_ops)
                .map(|_| Ok((r.string()?, r.uvarint()?, r.node_ref(index)?)))
                .collect::<Result<Vec<_>, CodecError>>()?;
            Node::Handle {
                body,
                ret_var,
                ret_body,
                ops,
            }
        }
        Tag::CMask => {
            let n = r.bounded_len()?;
            let names = (0..n).map(|_| r.string()).collect::<Result<Vec<_>, _>>()?;
            Node::Mask(names, r.node_ref(index)?)
        }
        Tag::CStr => {
            let b = op_from_wire(BUILTINS, r.uvarint()?)?;
            Node::StrOp(b, r.node_refs(index)?)
        }
        Tag::CDup => Node::Dup(r.node_ref(index)?),
        Tag::CDrop => Node::Drop(r.node_ref(index)?),
        Tag::CWithReuse => Node::WithReuse(r.node_ref(index)?, r.node_ref(index)?),
        Tag::CReuse => {
            let token = r.reference(member_count, dep_count)?;
            Node::Reuse(token, r.node_ref(index)?)
        }
        Tag::CRefNew => Node::RefNew(r.node_ref(index)?),
        Tag::CRefGet => Node::RefGet(r.node_ref(index)?),
        Tag::CRefSet => Node::RefSet(r.node_ref(index)?, r.node_ref(index)?),
    };
    Ok(node)
}

// Reconstruction state: the parsed table, the fresh symbols the dependencies and
// the sole member are called through, and the expansion budget that bounds a
// shared-DAG blow-up.
struct Builder<'a> {
    nodes: &'a [Node],
    dep_syms: &'a [Sym],
    member_syms: &'a [Sym],
    budget: usize,
}

impl Builder<'_> {
    fn spend(&mut self) -> Result<(), CodecError> {
        self.budget = self.budget.checked_sub(1).ok_or(CodecError::DepthLimit)?;
        Ok(())
    }

    fn node(&self, i: u32) -> Result<&Node, CodecError> {
        self.nodes.get(i as usize).ok_or(CodecError::BadReference)
    }

    fn resolve(&self, r: &Ref, binders: &[Sym]) -> Result<Sym, CodecError> {
        match r {
            Ref::Bound(k) => {
                let k = usize::try_from(*k).map_err(|_| CodecError::BadReference)?;
                let pos = binders
                    .len()
                    .checked_sub(1)
                    .and_then(|last| last.checked_sub(k))
                    .ok_or(CodecError::BadReference)?;
                Ok(binders[pos])
            }
            Ref::Member(i) => self
                .member_syms
                .get(*i)
                .copied()
                .ok_or(CodecError::BadReference),
            Ref::Dep(i) => self
                .dep_syms
                .get(*i)
                .copied()
                .ok_or(CodecError::BadReference),
            Ref::Global(name) => Ok(Sym::new(name)),
        }
    }

    fn value(&mut self, i: u32, binders: &mut Vec<Sym>) -> Result<Value, CodecError> {
        self.spend()?;
        let v = match self.node(i)?.clone() {
            Node::Var(r) => Value::Var(self.resolve(&r, binders)?),
            Node::Int(n) => Value::Int(n),
            Node::I64(n) => Value::I64(n),
            Node::U64(n) => Value::U64(n),
            Node::Float(f) => Value::Float(f),
            Node::Bool(b) => Value::Bool(b),
            Node::Unit => Value::Unit,
            Node::Str(s) => Value::Str(s),
            Node::Thunk(c) => Value::Thunk(Box::new(self.comp(c, binders)?)),
            Node::Ctor(n, t, args) => Value::Ctor(
                Sym::new(&n),
                usize::try_from(t).map_err(|_| CodecError::Malformed)?,
                self.values(&args, binders)?,
            ),
            Node::Tuple(args) => Value::Tuple(self.values(&args, binders)?),
            _ => return Err(CodecError::Malformed),
        };
        Ok(v)
    }

    fn values(&mut self, idxs: &[u32], binders: &mut Vec<Sym>) -> Result<Vec<Value>, CodecError> {
        idxs.iter().map(|i| self.value(*i, binders)).collect()
    }

    // Run `body` with `n` fresh binders pushed, returning both its result and the
    // fresh symbols so the caller can place them (as lambda params, a let binder,
    // handler params, ...).
    fn scoped<R>(
        &mut self,
        binders: &mut Vec<Sym>,
        n: usize,
        body: impl FnOnce(&mut Self, &mut Vec<Sym>) -> Result<R, CodecError>,
    ) -> Result<(R, Vec<Sym>), CodecError> {
        let fresh: Vec<Sym> = (0..n).map(|_| Sym::fresh()).collect();
        binders.extend_from_slice(&fresh);
        let r = body(self, binders);
        binders.truncate(binders.len() - n);
        Ok((r?, fresh))
    }

    fn build_pat(p: &RawPat) -> (CorePat, Vec<Sym>) {
        match p.tag {
            PatTag::Wild => (CorePat::Wild, Vec::new()),
            PatTag::Var => {
                let x = Sym::fresh();
                (CorePat::Var(x), vec![x])
            }
            PatTag::Ctor | PatTag::Tuple => {
                let mut binders = Vec::new();
                let opts: Vec<Option<Sym>> = p
                    .fields
                    .iter()
                    .map(|&is_binder| {
                        is_binder.then(|| {
                            let x = Sym::fresh();
                            binders.push(x);
                            x
                        })
                    })
                    .collect();
                let pat = if p.tag == PatTag::Ctor {
                    CorePat::Ctor(Sym::new(&p.name), opts)
                } else {
                    CorePat::Tuple(opts)
                };
                (pat, binders)
            }
        }
    }

    fn comp(&mut self, i: u32, binders: &mut Vec<Sym>) -> Result<Comp, CodecError> {
        self.spend()?;
        let c = match self.node(i)?.clone() {
            Node::Return(v) => Comp::Return(self.value(v, binders)?),
            Node::Force(v) => Comp::Force(self.value(v, binders)?),
            Node::Error(v) => Comp::Error(self.value(v, binders)?),
            Node::Dup(v) => Comp::Dup(self.value(v, binders)?),
            Node::Drop(v) => Comp::Drop(self.value(v, binders)?),
            Node::RefNew(v) => Comp::RefNew(self.value(v, binders)?),
            Node::RefGet(v) => Comp::RefGet(self.value(v, binders)?),
            Node::RefSet(a, b) => Comp::RefSet(self.value(a, binders)?, self.value(b, binders)?),
            Node::Bind(m, n) => {
                let mc = self.comp(m, binders)?;
                let (nc, fresh) = self.scoped(binders, 1, |s, b| s.comp(n, b))?;
                Comp::Bind(Box::new(mc), fresh[0], Box::new(nc))
            }
            Node::Lam(nparams, body) => {
                let nparams = usize::try_from(nparams).map_err(|_| CodecError::Malformed)?;
                let (bc, fresh) = self.scoped(binders, nparams, |s, b| s.comp(body, b))?;
                Comp::Lam(fresh, Box::new(bc))
            }
            Node::App(f, args) => Comp::App(
                Box::new(self.comp(f, binders)?),
                self.values(&args, binders)?,
            ),
            Node::If(v, t, e) => Comp::If(
                self.value(v, binders)?,
                Box::new(self.comp(t, binders)?),
                Box::new(self.comp(e, binders)?),
            ),
            Node::Prim(op, a, b) => {
                Comp::Prim(op, self.value(a, binders)?, self.value(b, binders)?)
            }
            Node::Call(head, args) => {
                Comp::Call(self.resolve(&head, binders)?, self.values(&args, binders)?)
            }
            Node::Io(op, args) => Comp::Io(op, self.values(&args, binders)?),
            Node::FloatOp(op, v) => Comp::FloatBuiltin(op, self.value(v, binders)?),
            Node::Do(op, args) => Comp::Do(Sym::new(&op), self.values(&args, binders)?),
            Node::StrOp(b, args) => Comp::StrBuiltin(b, self.values(&args, binders)?),
            Node::Case(scrut, arms) => {
                let sv = self.value(scrut, binders)?;
                let arms = arms
                    .iter()
                    .map(|(rp, body)| {
                        let (pat, pbinders) = Self::build_pat(rp);
                        binders.extend_from_slice(&pbinders);
                        let body = self.comp(*body, binders);
                        binders.truncate(binders.len() - pbinders.len());
                        Ok((pat, body?))
                    })
                    .collect::<Result<Vec<_>, CodecError>>()?;
                Comp::Case(sv, arms)
            }
            Node::Handle {
                body,
                ret_var,
                ret_body,
                ops,
            } => {
                let bc = self.comp(body, binders)?;
                let n_ret = usize::from(ret_var);
                let (rb, ret_fresh) = self.scoped(binders, n_ret, |s, b| match ret_body {
                    Some(idx) => Ok(Some(s.comp(idx, b)?)),
                    None => Ok(None),
                })?;
                let handle_ops = ops
                    .iter()
                    .map(|(name, nparams, obody)| {
                        let nparams =
                            usize::try_from(*nparams).map_err(|_| CodecError::Malformed)?;
                        let (oc, fresh) =
                            self.scoped(binders, nparams + 1, |s, b| s.comp(*obody, b))?;
                        let (params, resume) = fresh.split_at(nparams);
                        Ok(HandleOp {
                            name: Sym::new(name),
                            params: params.to_vec(),
                            resume: resume[0],
                            body: oc,
                        })
                    })
                    .collect::<Result<Vec<_>, CodecError>>()?;
                Comp::Handle {
                    body: Box::new(bc),
                    return_var: ret_fresh.first().copied(),
                    return_body: rb.map(Box::new),
                    ops: handle_ops,
                }
            }
            Node::Mask(names, b) => Comp::Mask(
                names.iter().map(|n| Sym::new(n)).collect(),
                Box::new(self.comp(b, binders)?),
            ),
            Node::WithReuse(freed, body) => {
                let fv = self.value(freed, binders)?;
                let (bc, fresh) = self.scoped(binders, 1, |s, b| s.comp(body, b))?;
                Comp::WithReuse {
                    token: fresh[0],
                    freed: fv,
                    body: Box::new(bc),
                }
            }
            Node::Reuse(token, v) => {
                Comp::Reuse(self.resolve(&token, binders)?, self.value(v, binders)?)
            }
            _ => return Err(CodecError::Malformed),
        };
        Ok(c)
    }
}

// One member's header in a decoded frame: its parameter count, dictionary arity,
// metadata string, and the node index of its body root.
struct Header {
    param_count: usize,
    dict_arity: usize,
    meta: String,
    root: u32,
}

/// Decode a `def`-kind frame back to one reconstructed definition.
///
/// Total: any malformed, truncated, or hostile input returns a [`CodecError`]
/// rather than panicking. The scheme and kind are checked before the body, every
/// length and varint is bounded, references are range-checked, reconstruction is
/// budgeted, and trailing bytes are rejected.
///
/// # Errors
/// Returns a [`CodecError`] describing the first inconsistency found.
pub fn decode_def(bytes: &[u8]) -> Result<Decoded, CodecError> {
    let mut r = Reader::new(bytes);
    if r.string()? != crate::core::HASH_SCHEME {
        return Err(CodecError::Scheme);
    }
    if r.uvarint()? != u64::from(WireKind::Def.varint()) {
        return Err(CodecError::Kind);
    }
    let contract = r.string()?;

    let member_count = r.bounded_len()?;
    if member_count == 0 {
        return Err(CodecError::Malformed);
    }
    let target = r.bounded_len()?;
    if target >= member_count {
        return Err(CodecError::BadReference);
    }

    let dep_count = r.bounded_len()?;
    let dep_hashes = (0..dep_count)
        .map(|_| r.string())
        .collect::<Result<Vec<_>, _>>()?;

    let node_count = r.uvarint()?;
    if node_count > MAX_NODES {
        return Err(CodecError::TooLarge);
    }
    let node_count = usize::try_from(node_count).map_err(|_| CodecError::TooLarge)?;
    let mut nodes = Vec::with_capacity(node_count.min(1024));
    for i in 0..node_count {
        nodes.push(parse_node(
            &mut r,
            u32::try_from(i).map_err(|_| CodecError::TooLarge)?,
            member_count,
            dep_count,
        )?);
    }

    let mut headers = Vec::with_capacity(member_count);
    for _ in 0..member_count {
        let param_count = r.bounded_len()?;
        let dict_arity = r.bounded_len()?;
        // dict_arity is not part of the hash, but a valid entry never claims more
        // dictionary params than it has parameters.
        if dict_arity > param_count {
            return Err(CodecError::Malformed);
        }
        let meta = r.string()?;
        let root = r.uvarint()?;
        let root = u32::try_from(root).map_err(|_| CodecError::BadReference)?;
        if root as usize >= nodes.len() {
            return Err(CodecError::BadReference);
        }
        headers.push(Header {
            param_count,
            dict_arity,
            meta,
            root,
        });
    }

    if r.pos != bytes.len() {
        return Err(CodecError::TrailingBytes);
    }

    let member_syms: Vec<Sym> = (0..member_count).map(|_| Sym::fresh()).collect();
    let dep_syms: Vec<Sym> = (0..dep_count).map(|_| Sym::fresh()).collect();

    // One expansion budget for the whole object, so a shared-DAG blow-up is bounded
    // across all members together.
    let mut builder = Builder {
        nodes: &nodes,
        dep_syms: &dep_syms,
        member_syms: &member_syms,
        budget: MAX_EXPANSION,
    };

    let mut group = Vec::with_capacity(member_count);
    let mut meta = BTreeMap::new();
    for (m, h) in headers.into_iter().enumerate() {
        let params: Vec<Sym> = (0..h.param_count).map(|_| Sym::fresh()).collect();
        let mut binders = params.clone();
        let body = builder.comp(h.root, &mut binders)?;
        group.push(CoreFn {
            name: member_syms[m],
            params,
            dict_arity: h.dict_arity,
            body,
        });
        meta.insert(member_syms[m], h.meta);
    }

    let deps: Hashes = dep_syms
        .iter()
        .copied()
        .zip(dep_hashes.iter().cloned())
        .collect();

    Ok(Decoded {
        contract,
        group,
        target,
        dep_hashes,
        deps,
        meta,
        node_count: nodes.len(),
    })
}
