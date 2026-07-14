//! The `kont`-kind wire codec: the reversible bytes between one live interpreter
//! continuation and the compact frame a suspended program persists.
//!
//! Where [`crate::store::codec`] serializes the compiler's own anonymous Core (a
//! `def`), this codec serializes the interpreter's *runtime* representation (the
//! `kont`): the frame stack, the lowered node graph the frames evaluate, and the
//! runtime values (closures, thunks, captured continuations, data, buffers) the
//! environments hold. The two are distinct wires over distinct domains, but an
//! operator (a `CoreOp`, `Builtin`, `FloatOp`, `IoOp`, `NegLane`) means the same
//! thing in both, so its wire number is drawn from the one canonical home in
//! `store::codec` rather than re-typed here.
//!
//! # The envelope
//!
//! Read left to right, each header part checked before the next is touched (the
//! `lib/std/Wire.pr` discipline, self-contained here as in `store::codec`):
//!
//! ```text
//!   +------------+------+------------------+--------------+
//!   | scheme tag | kind |  bundle digest   |     body     |
//!   +------------+------+------------------+--------------+
//!
//!   scheme tag     length-prefixed "prism-core-hash-v1"; a foreign scheme is
//!                  rejected before anything else
//!   kind           uvarint, WireKind::Kont
//!   bundle digest  length-prefixed: the code-identity hash of the program this
//!                  continuation runs in. A resumer checks it before the body, so a
//!                  continuation cannot resume against code it was not captured in.
//!   body           the machine snapshot below
//! ```
//!
//! # The body: a machine snapshot over one hash-consed node table
//!
//! The frame stack, the pending state (an `Eval(cmp, env)` or a `Ret(value)`), and
//! the scalar machine registers (`rng`, current `fn_name`, observation count, exit
//! code, halted flag, and the replay trace recorded so far). Every recursive
//! object (a node, a value, an atom, a frame, an environment, a handler record) is
//! interned once into a shared node table and referenced by index; a child index
//! is always strictly below its parent's, so the graph is acyclic by construction
//! and decode is a single forward pass. A subterm shared across many frames (an
//! environment, most of all) is stored once.
//!
//! Unlike the `def` wire, a binder here keeps its interned name: the interpreter
//! resolves variables by symbol through the environment map, not by de Bruijn
//! distance, so the name matters. Environment and handler-op orderings are
//! canonicalized by name (symbol ids are process-local), which keeps the wire
//! byte-idempotent under a decode/encode round-trip.
//!
//! Code references resolve reference-or-inline: a call to a top-level definition
//! rides as the callee's *name*, resolved at resume against the resumer's function
//! table (whose identity the matching bundle digest guarantees), so same-bundle
//! wire cost is state only; an inline lambda or thunk body is inlined.
//!
//! # Totality
//!
//! [`decode_kont`](crate::eval::kont::decode_kont) never panics on hostile bytes: every varint is byte-capped,
//! every length is bounded, the scheme, kind and bundle are checked before the
//! body, child indices are range-checked against the already-parsed prefix,
//! reconstruction runs against an expansion budget, and trailing bytes are
//! rejected. [`encode_kont`](crate::eval::kont::encode_kont) is fallible: a value that cannot cross the suspend
//! boundary (a graph nested past the suspendable depth, the fingerprint of an
//! unserializable capture or a cycle) is refused by name rather than encoded.

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use num_bigint::BigInt;

// The byte substrate (varints, bounded blobs/strings, table numbering, the
// hostile-input reader, and the node-table bounds) is shared with the `def` codec;
// only the `kont` schema below is local.
use crate::binary::{
    from_wire, put_indices, put_str, put_svarint, put_uvarint, to_wire, Reader, MAX_EXPANSION,
    MAX_NODES,
};
use crate::core::{CoreOp, CorePat};
use crate::driver::WireKind;
use crate::provenance::Observation;
// The op-family tables are numbered once in the `def` codec; the `kont` wire draws
// the same numbering so an operator means one thing on both wires.
use crate::store::codec::{BUILTINS, CORE_OPS, FLOAT_OPS, NEG_LANES};
use crate::store::CodecError;
use crate::sym::Sym;
use crate::types::ty::Type;

use super::{Atom, Cmp, Env, Frame, HandleInfo, Node, Obs, Rv};

// The deepest value graph a single suspend may serialize, and the deepest a
// decode will reconstruct. Realistic continuation state (a physics vector, a
// small record, a counter, a modest queue) nests far below this. The bound is
// what keeps both the recursive encoder and the recursive decoder inside the
// native stack on hostile input: a value deeper than this is refused by name at
// suspend time, and a hostile envelope claiming a deeper chain is rejected
// (`DepthLimit`) rather than allowed to overflow the stack. It is deliberately
// conservative: the smallest thread stack we run on is ~2 MiB and an unoptimized
// recursive frame here runs a few KiB, so this leaves a wide margin. The frame
// *stack* is encoded iteratively, so this bounds nested runtime data (a cons-list,
// a tree) and the source-bounded computation depth, not the count of pending
// frames. Carrying mobile state deeper than a source program can build is the
// typed-envelope codec's job, not this dynamic one.
const MAX_SUSPEND_DEPTH: usize = 256;

/// A live interpreter continuation made portable: the whole suspended machine as
/// a value. Encoded by [`encode_kont`], reconstructed by [`decode_kont`], and
/// resumed by the driver in `crate::eval`.
#[derive(Clone, Debug)]
pub struct Kont {
    /// The code-identity digest of the program this continuation runs in. A
    /// resumer refuses a continuation whose bundle does not match its own code.
    pub bundle: String,
    /// The pending continuation: the frame stack, bottom to top.
    pub stack: Vec<Frame>,
    /// What the machine was about to do when it suspended.
    pub state: KontState,
    /// The `rand`/`srand` generator state, so a resumed run's randomness continues
    /// the original stream.
    pub rng: u64,
    /// The function name the machine was evaluating in (for post-resume
    /// diagnostics), as a symbol.
    pub fn_name: Sym,
    /// How many capability observations the run had performed before it suspended.
    pub observed: usize,
    /// The exit code, if the program had already called `exit`.
    pub exit: Option<i32>,
    /// The replay trace recorded up to the suspend point, so a resumed run
    /// reproduces the prefix's world reads and stays deterministic across the cut.
    pub trace: Vec<Obs>,
    /// Complete ordered observations emitted before the suspend point.
    pub observations: Vec<Observation>,
}

/// The machine's pending state at a suspend point: mid-evaluation of a computation
/// under an environment, or about to return a value into the top frame.
#[derive(Clone, Debug)]
pub enum KontState {
    Eval(Cmp, Env),
    Ret(Rv),
}

/// Why a live continuation could not be written to the `kont` wire. The suspend
/// boundary is explicit: what cannot cross says so by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SuspendError {
    /// A value reachable from the continuation nests past `MAX_SUSPEND_DEPTH`
    /// (the fingerprint of an unserializable capture or a cycle); the string names
    /// where the encoder gave up.
    NonSerializable(String),
}

impl std::fmt::Display for SuspendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonSerializable(what) => {
                write!(
                    f,
                    "cannot suspend: {what} cannot cross the suspend boundary"
                )
            }
        }
    }
}

impl std::error::Error for SuspendError {}

/// Whether the suspend codec has a wire encoding for every value of this ground
/// type.
///
/// This is the type-level projection of the value shapes [`encode_kont`]
/// serializes (the `value` match above, one arm per `Tag::V*` variant). Scalars,
/// `Char`, `Str`, tuples, and algebraic data with encodable fields all round-trip,
/// so a capture of such a type can cross a move. A function type answers `false`, not
/// because the codec lacks a `VClosure` tag but because a closure's portability
/// turns on its own captured environment, which a static per-closure pass does
/// not inspect; an abstract or unresolved type is likewise undecidable here.
/// A `false` therefore means "cannot prove portable", never "provably not".
#[must_use]
pub fn portable_value_type(ty: &Type) -> bool {
    match ty {
        Type::Unit
        | Type::Int
        | Type::I64
        | Type::U64
        | Type::Bool
        | Type::Float
        | Type::Char
        | Type::Str => true,
        Type::Tuple(fields) => fields.iter().all(portable_value_type),
        Type::Con(_, args) => args.iter().all(portable_value_type),
        _ => false,
    }
}

// One discriminant for every runtime shape the table can hold, across all six
// domains (value, node, atom, frame, environment, handler record). Encoded as a
// uvarint; the array below is the single source of truth for the numbering, so
// encode (`as u8`) and decode (index into the array) cannot drift. A reference is
// an untyped index; the builder validates the referent's tag against the domain
// it is used in, so a cross-domain reference in a hostile frame is rejected rather
// than misread.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Tag {
    // Values (`Rv`).
    VInt,
    VI64,
    VU64,
    VFloat,
    VBool,
    VUnit,
    VStr,
    VBig,
    VClosure,
    VThunk,
    VData,
    VTuple,
    VArray,
    VBuf,
    VResume,
    // Computations (`Node`).
    NReturn,
    NBind,
    NForce,
    NLam,
    NApp,
    NIf,
    NPrim,
    NCall,
    NPrint,
    NPrintNl,
    NReadInt,
    NReadLine,
    NRand,
    NSrand,
    NError,
    NCase,
    NFloat,
    NNeg,
    NDo,
    NHandle,
    NMask,
    NStr,
    // Atoms (`Atom`).
    AVar,
    AInt,
    AI64,
    AU64,
    AFloat,
    ABool,
    AUnit,
    AStr,
    AThunk,
    ACtor,
    ATuple,
    // Frames (`Frame`).
    FBind,
    FArgs,
    FRestore,
    FHandle,
    FMask,
    // Environment and handler record.
    EnvMap,
    HInfo,
}

const TAGS: &[Tag] = &[
    Tag::VInt,
    Tag::VI64,
    Tag::VU64,
    Tag::VFloat,
    Tag::VBool,
    Tag::VUnit,
    Tag::VStr,
    Tag::VBig,
    Tag::VClosure,
    Tag::VThunk,
    Tag::VData,
    Tag::VTuple,
    Tag::VArray,
    Tag::VBuf,
    Tag::VResume,
    Tag::NReturn,
    Tag::NBind,
    Tag::NForce,
    Tag::NLam,
    Tag::NApp,
    Tag::NIf,
    Tag::NPrim,
    Tag::NCall,
    Tag::NPrint,
    Tag::NPrintNl,
    Tag::NReadInt,
    Tag::NReadLine,
    Tag::NRand,
    Tag::NSrand,
    Tag::NError,
    Tag::NCase,
    Tag::NFloat,
    Tag::NNeg,
    Tag::NDo,
    Tag::NHandle,
    Tag::NMask,
    Tag::NStr,
    Tag::AVar,
    Tag::AInt,
    Tag::AI64,
    Tag::AU64,
    Tag::AFloat,
    Tag::ABool,
    Tag::AUnit,
    Tag::AStr,
    Tag::AThunk,
    Tag::ACtor,
    Tag::ATuple,
    Tag::FBind,
    Tag::FArgs,
    Tag::FRestore,
    Tag::FHandle,
    Tag::FMask,
    Tag::EnvMap,
    Tag::HInfo,
];

impl Tag {
    fn from_u64(n: u64) -> Result<Self, CodecError> {
        from_wire(TAGS, n)
    }
}

// The pattern shapes a `Case` arm can test, encoded inline in the arm (as in
// `store::codec`) but keeping the binder names, since the interpreter binds them
// into the environment by symbol.
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
        from_wire(PAT_TAGS, n)
    }
}

// Tags for the observation trace frames (mirrors `Obs`).
const OBS_INT: u64 = 0;
const OBS_STR: u64 = 1;
const OBS_BOOL: u64 = 2;
const OBS_OUT: u64 = 3;

// ------------------------------- encoding ----------------------------------

fn put_sym(out: &mut Vec<u8>, s: Sym) {
    put_str(out, s.as_str());
}

fn put_tag(out: &mut Vec<u8>, t: Tag) {
    put_uvarint(out, t as u64);
}

struct Encoder {
    table: Vec<Vec<u8>>,
    intern: HashMap<Vec<u8>, u32>,
    depth: usize,
}

impl Encoder {
    fn new() -> Self {
        Self {
            table: Vec::new(),
            intern: HashMap::new(),
            depth: 0,
        }
    }

    // Intern a node's finished bytes and return its table index. Identical bytes
    // share one entry; children were interned first, so a child index is always
    // smaller than its parent's, the topological order decode relies on.
    fn push(&mut self, bytes: Vec<u8>) -> u32 {
        if let Some(i) = self.intern.get(&bytes) {
            return *i;
        }
        #[allow(clippy::cast_possible_truncation)]
        let i = self.table.len() as u32;
        self.intern.insert(bytes.clone(), i);
        self.table.push(bytes);
        i
    }

    // Enter one level of value nesting, refusing (rather than overflowing the
    // stack) a graph past the suspendable depth. Every recursive encode step that
    // descends into runtime data guards through here.
    fn enter(&mut self, what: &str) -> Result<(), SuspendError> {
        self.depth += 1;
        if self.depth > MAX_SUSPEND_DEPTH {
            return Err(SuspendError::NonSerializable(format!(
                "a {what} nested past the suspendable depth ({MAX_SUSPEND_DEPTH})"
            )));
        }
        Ok(())
    }

    const fn leave(&mut self) {
        self.depth -= 1;
    }

    fn value(&mut self, v: &Rv) -> Result<u32, SuspendError> {
        self.enter("value")?;
        let mut out = Vec::new();
        match v {
            Rv::Int(n) => {
                put_tag(&mut out, Tag::VInt);
                put_svarint(&mut out, *n);
            }
            Rv::I64(n) => {
                put_tag(&mut out, Tag::VI64);
                put_svarint(&mut out, *n);
            }
            Rv::U64(n) => {
                put_tag(&mut out, Tag::VU64);
                put_uvarint(&mut out, *n);
            }
            Rv::Float(f) => {
                put_tag(&mut out, Tag::VFloat);
                out.extend_from_slice(&f.to_bits().to_le_bytes());
            }
            Rv::Bool(b) => {
                put_tag(&mut out, Tag::VBool);
                out.push(u8::from(*b));
            }
            Rv::Unit => put_tag(&mut out, Tag::VUnit),
            Rv::Str(s) => {
                put_tag(&mut out, Tag::VStr);
                put_str(&mut out, s);
            }
            Rv::Big(n) => {
                put_tag(&mut out, Tag::VBig);
                let bytes = n.to_signed_bytes_le();
                put_uvarint(&mut out, bytes.len() as u64);
                out.extend_from_slice(&bytes);
            }
            Rv::Closure(ps, body, env) => {
                let bi = self.comp(body)?;
                let ei = self.env(env)?;
                put_tag(&mut out, Tag::VClosure);
                put_uvarint(&mut out, ps.len() as u64);
                for p in ps.iter() {
                    put_sym(&mut out, *p);
                }
                put_uvarint(&mut out, u64::from(bi));
                put_uvarint(&mut out, u64::from(ei));
            }
            Rv::Thunk(body, env) => {
                let bi = self.comp(body)?;
                let ei = self.env(env)?;
                put_tag(&mut out, Tag::VThunk);
                put_uvarint(&mut out, u64::from(bi));
                put_uvarint(&mut out, u64::from(ei));
            }
            Rv::Data(name, fs) => {
                let idxs = self.values(fs)?;
                put_tag(&mut out, Tag::VData);
                put_sym(&mut out, *name);
                put_indices(&mut out, &idxs);
            }
            Rv::Tuple(fs) => {
                let idxs = self.values(fs)?;
                put_tag(&mut out, Tag::VTuple);
                put_indices(&mut out, &idxs);
            }
            Rv::Array(fs) => {
                let idxs = self.values(fs)?;
                put_tag(&mut out, Tag::VArray);
                put_indices(&mut out, &idxs);
            }
            Rv::Buf(bytes) => {
                put_tag(&mut out, Tag::VBuf);
                put_uvarint(&mut out, bytes.len() as u64);
                out.extend_from_slice(bytes);
            }
            // Typed buffers are storage primitives and cannot cross a
            // serialized continuation boundary.
            Rv::TBuf(_) => {
                return Err(SuspendError::NonSerializable("typed buffer".into()));
            }
            Rv::Resume(frames) => {
                let idxs = self.frames(frames)?;
                put_tag(&mut out, Tag::VResume);
                put_indices(&mut out, &idxs);
            }
        }
        self.leave();
        Ok(self.push(out))
    }

    fn values(&mut self, vs: &[Rv]) -> Result<Vec<u32>, SuspendError> {
        vs.iter().map(|v| self.value(v)).collect()
    }

    fn env(&mut self, env: &Env) -> Result<u32, SuspendError> {
        self.enter("environment")?;
        // Canonical order by name: symbol ids are process-local, so ordering by id
        // (the `BTreeMap`'s own order) would not survive a decode/encode round-trip.
        let mut entries: Vec<(&Sym, &Rv)> = env.iter().collect();
        entries.sort_by_key(|(k, _)| k.as_str());
        let mut kvs = Vec::with_capacity(entries.len());
        for (k, v) in entries {
            let vi = self.value(v)?;
            kvs.push((*k, vi));
        }
        let mut out = Vec::new();
        put_tag(&mut out, Tag::EnvMap);
        put_uvarint(&mut out, kvs.len() as u64);
        for (k, vi) in kvs {
            put_sym(&mut out, k);
            put_uvarint(&mut out, u64::from(vi));
        }
        self.leave();
        Ok(self.push(out))
    }

    fn atom(&mut self, a: &Atom) -> Result<u32, SuspendError> {
        self.enter("atom")?;
        let mut out = Vec::new();
        match a {
            Atom::Var(x) => {
                put_tag(&mut out, Tag::AVar);
                put_sym(&mut out, *x);
            }
            Atom::Int(n) => {
                put_tag(&mut out, Tag::AInt);
                put_svarint(&mut out, *n);
            }
            Atom::I64(n) => {
                put_tag(&mut out, Tag::AI64);
                put_svarint(&mut out, *n);
            }
            Atom::U64(n) => {
                put_tag(&mut out, Tag::AU64);
                put_uvarint(&mut out, *n);
            }
            Atom::Float(f) => {
                put_tag(&mut out, Tag::AFloat);
                out.extend_from_slice(&f.to_bits().to_le_bytes());
            }
            Atom::Bool(b) => {
                put_tag(&mut out, Tag::ABool);
                out.push(u8::from(*b));
            }
            Atom::Unit => put_tag(&mut out, Tag::AUnit),
            Atom::Str(s) => {
                put_tag(&mut out, Tag::AStr);
                put_str(&mut out, s);
            }
            Atom::Thunk(c) => {
                let ci = self.comp(c)?;
                put_tag(&mut out, Tag::AThunk);
                put_uvarint(&mut out, u64::from(ci));
            }
            Atom::Ctor(name, args) => {
                let idxs = self.atoms(args)?;
                put_tag(&mut out, Tag::ACtor);
                put_sym(&mut out, *name);
                put_indices(&mut out, &idxs);
            }
            Atom::Tuple(args) => {
                let idxs = self.atoms(args)?;
                put_tag(&mut out, Tag::ATuple);
                put_indices(&mut out, &idxs);
            }
        }
        self.leave();
        Ok(self.push(out))
    }

    fn atoms(&mut self, args: &[Atom]) -> Result<Vec<u32>, SuspendError> {
        args.iter().map(|a| self.atom(a)).collect()
    }

    fn comp(&mut self, c: &Cmp) -> Result<u32, SuspendError> {
        self.enter("computation")?;
        let mut out = Vec::new();
        match &**c {
            Node::Return(a) => self.unary_atom(&mut out, Tag::NReturn, a)?,
            Node::Force(a) => self.unary_atom(&mut out, Tag::NForce, a)?,
            Node::Error(a) => self.unary_atom(&mut out, Tag::NError, a)?,
            Node::Print(a) => self.unary_atom(&mut out, Tag::NPrint, a)?,
            Node::Srand(a) => self.unary_atom(&mut out, Tag::NSrand, a)?,
            Node::PrintNl => put_tag(&mut out, Tag::NPrintNl),
            Node::ReadInt => put_tag(&mut out, Tag::NReadInt),
            Node::ReadLine => put_tag(&mut out, Tag::NReadLine),
            Node::Rand => put_tag(&mut out, Tag::NRand),
            Node::Bind(m, x, n) => {
                let mi = self.comp(m)?;
                let ni = self.comp(n)?;
                put_tag(&mut out, Tag::NBind);
                put_uvarint(&mut out, u64::from(mi));
                put_sym(&mut out, *x);
                put_uvarint(&mut out, u64::from(ni));
            }
            Node::Lam(ps, body) => {
                let bi = self.comp(body)?;
                put_tag(&mut out, Tag::NLam);
                put_uvarint(&mut out, ps.len() as u64);
                for p in ps.iter() {
                    put_sym(&mut out, *p);
                }
                put_uvarint(&mut out, u64::from(bi));
            }
            Node::App(m, args) => {
                let mi = self.comp(m)?;
                let idxs = self.atoms(args)?;
                put_tag(&mut out, Tag::NApp);
                put_uvarint(&mut out, u64::from(mi));
                put_indices(&mut out, &idxs);
            }
            Node::If(a, t, e) => {
                let ai = self.atom(a)?;
                let ti = self.comp(t)?;
                let ei = self.comp(e)?;
                put_tag(&mut out, Tag::NIf);
                put_uvarint(&mut out, u64::from(ai));
                put_uvarint(&mut out, u64::from(ti));
                put_uvarint(&mut out, u64::from(ei));
            }
            Node::Prim(op, a, b) => {
                let ai = self.atom(a)?;
                let bi = self.atom(b)?;
                put_tag(&mut out, Tag::NPrim);
                put_uvarint(&mut out, to_wire(CORE_OPS, *op));
                put_uvarint(&mut out, u64::from(ai));
                put_uvarint(&mut out, u64::from(bi));
            }
            Node::Call(name, args) => {
                let idxs = self.atoms(args)?;
                put_tag(&mut out, Tag::NCall);
                put_sym(&mut out, *name);
                put_indices(&mut out, &idxs);
            }
            Node::Case(a, arms) => {
                let ai = self.atom(a)?;
                let arm_idxs: Vec<(&CorePat, u32)> = arms
                    .iter()
                    .map(|(p, body)| Ok((p, self.comp(body)?)))
                    .collect::<Result<_, SuspendError>>()?;
                put_tag(&mut out, Tag::NCase);
                put_uvarint(&mut out, u64::from(ai));
                put_uvarint(&mut out, arm_idxs.len() as u64);
                for (p, bi) in arm_idxs {
                    write_pat(&mut out, p);
                    put_uvarint(&mut out, u64::from(bi));
                }
            }
            Node::FloatBuiltin(op, a) => {
                let ai = self.atom(a)?;
                put_tag(&mut out, Tag::NFloat);
                put_uvarint(&mut out, to_wire(FLOAT_OPS, *op));
                put_uvarint(&mut out, u64::from(ai));
            }
            Node::Neg(lane, a) => {
                let ai = self.atom(a)?;
                put_tag(&mut out, Tag::NNeg);
                put_uvarint(&mut out, to_wire(NEG_LANES, *lane));
                put_uvarint(&mut out, u64::from(ai));
            }
            Node::Do(op, args) => {
                let idxs = self.atoms(args)?;
                put_tag(&mut out, Tag::NDo);
                put_sym(&mut out, *op);
                put_indices(&mut out, &idxs);
            }
            Node::StrBuiltin(b, args) => {
                let idxs = self.atoms(args)?;
                put_tag(&mut out, Tag::NStr);
                put_uvarint(&mut out, to_wire(BUILTINS, *b));
                put_indices(&mut out, &idxs);
            }
            Node::Handle(hi) => {
                let hidx = self.handle(hi)?;
                put_tag(&mut out, Tag::NHandle);
                put_uvarint(&mut out, u64::from(hidx));
            }
            Node::Mask(ops, body) => {
                let bi = self.comp(body)?;
                put_tag(&mut out, Tag::NMask);
                put_uvarint(&mut out, ops.len() as u64);
                for o in ops.iter() {
                    put_sym(&mut out, *o);
                }
                put_uvarint(&mut out, u64::from(bi));
            }
        }
        self.leave();
        Ok(self.push(out))
    }

    fn unary_atom(&mut self, out: &mut Vec<u8>, t: Tag, a: &Atom) -> Result<(), SuspendError> {
        let ai = self.atom(a)?;
        put_tag(out, t);
        put_uvarint(out, u64::from(ai));
        Ok(())
    }

    // A handler record: the ops in canonical name order (symbol ids are
    // process-local), the body, and the optional return clause.
    fn handle(&mut self, hi: &HandleInfo) -> Result<u32, SuspendError> {
        self.enter("handler")?;
        let bi = self.comp(&hi.body)?;
        let rbi = match &hi.return_body {
            Some(rb) => Some(self.comp(rb)?),
            None => None,
        };
        let mut ops: Vec<_> = hi.ops.iter().collect();
        ops.sort_by_key(|(k, _)| k.as_str());
        let op_idxs = ops
            .into_iter()
            .map(|(name, (params, resume, body))| Ok((*name, params, *resume, self.comp(body)?)))
            .collect::<Result<Vec<_>, SuspendError>>()?;
        let mut out = Vec::new();
        put_tag(&mut out, Tag::HInfo);
        put_uvarint(&mut out, u64::from(bi));
        match hi.return_var {
            Some(rv) => {
                out.push(1);
                put_sym(&mut out, rv);
            }
            None => out.push(0),
        }
        match rbi {
            Some(i) => {
                out.push(1);
                put_uvarint(&mut out, u64::from(i));
            }
            None => out.push(0),
        }
        put_uvarint(&mut out, op_idxs.len() as u64);
        for (name, params, resume, bidx) in op_idxs {
            put_sym(&mut out, name);
            put_uvarint(&mut out, params.len() as u64);
            for p in params {
                put_sym(&mut out, *p);
            }
            put_sym(&mut out, resume);
            put_uvarint(&mut out, u64::from(bidx));
        }
        self.leave();
        Ok(self.push(out))
    }

    fn frame(&mut self, f: &Frame) -> Result<u32, SuspendError> {
        self.enter("frame")?;
        let mut out = Vec::new();
        match f {
            Frame::Bind(x, n, env) => {
                let ni = self.comp(n)?;
                let ei = self.env(env)?;
                put_tag(&mut out, Tag::FBind);
                put_sym(&mut out, *x);
                put_uvarint(&mut out, u64::from(ni));
                put_uvarint(&mut out, u64::from(ei));
            }
            Frame::Args(args, env) => {
                let idxs = self.atoms(args)?;
                let ei = self.env(env)?;
                put_tag(&mut out, Tag::FArgs);
                put_indices(&mut out, &idxs);
                put_uvarint(&mut out, u64::from(ei));
            }
            Frame::Restore(name) => {
                put_tag(&mut out, Tag::FRestore);
                put_sym(&mut out, *name);
            }
            Frame::Handle(hi, env) => {
                let hidx = self.handle(hi)?;
                let ei = self.env(env)?;
                put_tag(&mut out, Tag::FHandle);
                put_uvarint(&mut out, u64::from(hidx));
                put_uvarint(&mut out, u64::from(ei));
            }
            Frame::Mask(ops) => {
                put_tag(&mut out, Tag::FMask);
                put_uvarint(&mut out, ops.len() as u64);
                for o in ops.iter() {
                    put_sym(&mut out, *o);
                }
            }
        }
        self.leave();
        Ok(self.push(out))
    }

    fn frames(&mut self, fs: &[Frame]) -> Result<Vec<u32>, SuspendError> {
        fs.iter().map(|f| self.frame(f)).collect()
    }
}

fn write_pat(out: &mut Vec<u8>, p: &CorePat) {
    let fields = |out: &mut Vec<u8>, fs: &[Option<Sym>]| {
        put_uvarint(out, fs.len() as u64);
        for f in fs {
            match f {
                Some(s) => {
                    out.push(1);
                    put_sym(out, *s);
                }
                None => out.push(0),
            }
        }
    };
    match p {
        CorePat::Wild => put_uvarint(out, PatTag::Wild as u64),
        CorePat::Var(x) => {
            put_uvarint(out, PatTag::Var as u64);
            put_sym(out, *x);
        }
        CorePat::Ctor(n, fs) => {
            put_uvarint(out, PatTag::Ctor as u64);
            put_sym(out, n.as_str().into());
            fields(out, fs);
        }
        CorePat::Tuple(fs) => {
            put_uvarint(out, PatTag::Tuple as u64);
            fields(out, fs);
        }
    }
}

fn put_obs(out: &mut Vec<u8>, o: &Obs) {
    match o {
        Obs::Int(n) => {
            put_uvarint(out, OBS_INT);
            put_svarint(out, *n);
        }
        Obs::Str(s) => {
            put_uvarint(out, OBS_STR);
            put_str(out, s);
        }
        Obs::Bool(b) => {
            put_uvarint(out, OBS_BOOL);
            out.push(u8::from(*b));
        }
        Obs::Out => put_uvarint(out, OBS_OUT),
    }
}

/// Encode a live continuation as a `kont`-kind frame.
///
/// # Errors
/// Returns [`SuspendError`] when a reachable value cannot cross the suspend
/// boundary (a graph nested past the suspendable depth, the fingerprint of an
/// unserializable capture or a cycle), naming where the encoder gave up.
pub fn encode_kont(k: &Kont) -> Result<Vec<u8>, SuspendError> {
    let mut enc = Encoder::new();
    let stack_idxs = enc.frames(&k.stack)?;
    let state = match &k.state {
        KontState::Eval(c, env) => {
            let ci = enc.comp(c)?;
            let ei = enc.env(env)?;
            (0u8, ci, ei)
        }
        KontState::Ret(v) => {
            let vi = enc.value(v)?;
            (1u8, vi, 0)
        }
    };

    let mut out = Vec::new();
    put_str(&mut out, crate::core::HASH_SCHEME);
    put_uvarint(&mut out, u64::from(WireKind::Kont.varint()));
    put_str(&mut out, &k.bundle);

    put_uvarint(&mut out, k.rng);
    put_sym(&mut out, k.fn_name);
    put_uvarint(&mut out, k.observed as u64);
    match k.exit {
        Some(code) => {
            out.push(1);
            put_svarint(&mut out, i64::from(code));
        }
        None => out.push(0),
    }
    put_uvarint(&mut out, k.trace.len() as u64);
    for o in &k.trace {
        put_obs(&mut out, o);
    }
    put_uvarint(&mut out, k.observations.len() as u64);
    for observation in &k.observations {
        let json = serde_json::to_string(observation).map_err(|error| {
            SuspendError::NonSerializable(format!("observation trace: {error}"))
        })?;
        put_str(&mut out, &json);
    }

    put_uvarint(&mut out, enc.table.len() as u64);
    for node in &enc.table {
        out.extend_from_slice(node);
    }

    put_indices(&mut out, &stack_idxs);
    out.push(state.0);
    put_uvarint(&mut out, u64::from(state.1));
    put_uvarint(&mut out, u64::from(state.2));
    Ok(out)
}

// ------------------------------- decoding ----------------------------------

#[derive(Clone)]
struct RawPat {
    tag: PatTag,
    name: String,
    fields: Vec<Option<String>>,
}

#[derive(Clone)]
struct RawHandleOp {
    name: String,
    params: Vec<String>,
    resume: String,
    body: u32,
}

// A node parsed into structure, its children still indices into the table. The
// forward pass builds the whole table, then reconstruction walks it from the
// roots, materializing each into its runtime domain.
#[derive(Clone)]
enum Raw {
    VInt(i64),
    VI64(i64),
    VU64(u64),
    VFloat(f64),
    VBool(bool),
    VUnit,
    VStr(String),
    VBig(Vec<u8>),
    VClosure(Vec<String>, u32, u32),
    VThunk(u32, u32),
    VData(String, Vec<u32>),
    VTuple(Vec<u32>),
    VArray(Vec<u32>),
    VBuf(Vec<u8>),
    VResume(Vec<u32>),
    NReturn(u32),
    NForce(u32),
    NError(u32),
    NPrint(u32),
    NSrand(u32),
    NPrintNl,
    NReadInt,
    NReadLine,
    NRand,
    NBind(u32, String, u32),
    NLam(Vec<String>, u32),
    NApp(u32, Vec<u32>),
    NIf(u32, u32, u32),
    NPrim(CoreOp, u32, u32),
    NCall(String, Vec<u32>),
    NCase(u32, Vec<(RawPat, u32)>),
    NFloat(crate::core::builtins::FloatOp, u32),
    NNeg(crate::core::NegLane, u32),
    NDo(String, Vec<u32>),
    NStr(crate::core::builtins::Builtin, Vec<u32>),
    NHandle(u32),
    NMask(Vec<String>, u32),
    AVar(String),
    AInt(i64),
    AI64(i64),
    AU64(u64),
    AFloat(f64),
    ABool(bool),
    AUnit,
    AStr(String),
    AThunk(u32),
    ACtor(String, Vec<u32>),
    ATuple(Vec<u32>),
    FBind(String, u32, u32),
    FArgs(Vec<u32>, u32),
    FRestore(String),
    FHandle(u32, u32),
    FMask(Vec<String>),
    EnvMap(Vec<(String, u32)>),
    HInfo {
        body: u32,
        ret_var: Option<String>,
        ret_body: Option<u32>,
        ops: Vec<RawHandleOp>,
    },
}

fn parse_pat(r: &mut Reader<'_>) -> Result<RawPat, CodecError> {
    let tag = PatTag::from_u64(r.uvarint()?)?;
    let read_fields = |r: &mut Reader<'_>| -> Result<Vec<Option<String>>, CodecError> {
        let n = r.bounded_len()?;
        (0..n)
            .map(|_| {
                if r.bool()? {
                    Ok(Some(r.string()?))
                } else {
                    Ok(None)
                }
            })
            .collect()
    };
    let (name, fields) = match tag {
        PatTag::Wild => (String::new(), Vec::new()),
        PatTag::Var => (r.string()?, Vec::new()),
        PatTag::Ctor => {
            let name = r.string()?;
            (name, read_fields(r)?)
        }
        PatTag::Tuple => (String::new(), read_fields(r)?),
    };
    Ok(RawPat { tag, name, fields })
}

fn parse_node(r: &mut Reader<'_>, index: u32) -> Result<Raw, CodecError> {
    let strs = |r: &mut Reader<'_>| -> Result<Vec<String>, CodecError> {
        let n = r.bounded_len()?;
        (0..n).map(|_| r.string()).collect()
    };
    Ok(match Tag::from_u64(r.uvarint()?)? {
        Tag::VInt => Raw::VInt(r.svarint()?),
        Tag::VI64 => Raw::VI64(r.svarint()?),
        Tag::VU64 => Raw::VU64(r.uvarint()?),
        Tag::VFloat => Raw::VFloat(r.float()?),
        Tag::VBool => Raw::VBool(r.bool()?),
        Tag::VUnit => Raw::VUnit,
        Tag::VStr => Raw::VStr(r.string()?),
        Tag::VBig => Raw::VBig(r.blob()?.to_vec()),
        Tag::VClosure => {
            let n = r.bounded_len()?;
            let ps = (0..n).map(|_| r.string()).collect::<Result<_, _>>()?;
            Raw::VClosure(ps, r.node_ref(index)?, r.node_ref(index)?)
        }
        Tag::VThunk => Raw::VThunk(r.node_ref(index)?, r.node_ref(index)?),
        Tag::VData => {
            let name = r.string()?;
            Raw::VData(name, r.node_refs(index)?)
        }
        Tag::VTuple => Raw::VTuple(r.node_refs(index)?),
        Tag::VArray => Raw::VArray(r.node_refs(index)?),
        Tag::VBuf => Raw::VBuf(r.blob()?.to_vec()),
        Tag::VResume => Raw::VResume(r.node_refs(index)?),
        Tag::NReturn => Raw::NReturn(r.node_ref(index)?),
        Tag::NForce => Raw::NForce(r.node_ref(index)?),
        Tag::NError => Raw::NError(r.node_ref(index)?),
        Tag::NPrint => Raw::NPrint(r.node_ref(index)?),
        Tag::NSrand => Raw::NSrand(r.node_ref(index)?),
        Tag::NPrintNl => Raw::NPrintNl,
        Tag::NReadInt => Raw::NReadInt,
        Tag::NReadLine => Raw::NReadLine,
        Tag::NRand => Raw::NRand,
        Tag::NBind => {
            let m = r.node_ref(index)?;
            let x = r.string()?;
            Raw::NBind(m, x, r.node_ref(index)?)
        }
        Tag::NLam => {
            let n = r.bounded_len()?;
            let ps = (0..n).map(|_| r.string()).collect::<Result<_, _>>()?;
            Raw::NLam(ps, r.node_ref(index)?)
        }
        Tag::NApp => {
            let m = r.node_ref(index)?;
            Raw::NApp(m, r.node_refs(index)?)
        }
        Tag::NIf => Raw::NIf(r.node_ref(index)?, r.node_ref(index)?, r.node_ref(index)?),
        Tag::NPrim => {
            let op = from_wire(CORE_OPS, r.uvarint()?)?;
            Raw::NPrim(op, r.node_ref(index)?, r.node_ref(index)?)
        }
        Tag::NCall => {
            let name = r.string()?;
            Raw::NCall(name, r.node_refs(index)?)
        }
        Tag::NCase => {
            let scrut = r.node_ref(index)?;
            let n = r.bounded_len()?;
            let arms = (0..n)
                .map(|_| Ok((parse_pat(r)?, r.node_ref(index)?)))
                .collect::<Result<Vec<_>, CodecError>>()?;
            Raw::NCase(scrut, arms)
        }
        Tag::NFloat => {
            let op = from_wire(FLOAT_OPS, r.uvarint()?)?;
            Raw::NFloat(op, r.node_ref(index)?)
        }
        Tag::NNeg => {
            let lane = from_wire(NEG_LANES, r.uvarint()?)?;
            Raw::NNeg(lane, r.node_ref(index)?)
        }
        Tag::NDo => {
            let op = r.string()?;
            Raw::NDo(op, r.node_refs(index)?)
        }
        Tag::NStr => {
            let b = from_wire(BUILTINS, r.uvarint()?)?;
            Raw::NStr(b, r.node_refs(index)?)
        }
        Tag::NHandle => Raw::NHandle(r.node_ref(index)?),
        Tag::NMask => {
            let ops = strs(r)?;
            Raw::NMask(ops, r.node_ref(index)?)
        }
        Tag::AVar => Raw::AVar(r.string()?),
        Tag::AInt => Raw::AInt(r.svarint()?),
        Tag::AI64 => Raw::AI64(r.svarint()?),
        Tag::AU64 => Raw::AU64(r.uvarint()?),
        Tag::AFloat => Raw::AFloat(r.float()?),
        Tag::ABool => Raw::ABool(r.bool()?),
        Tag::AUnit => Raw::AUnit,
        Tag::AStr => Raw::AStr(r.string()?),
        Tag::AThunk => Raw::AThunk(r.node_ref(index)?),
        Tag::ACtor => {
            let name = r.string()?;
            Raw::ACtor(name, r.node_refs(index)?)
        }
        Tag::ATuple => Raw::ATuple(r.node_refs(index)?),
        Tag::FBind => {
            let x = r.string()?;
            Raw::FBind(x, r.node_ref(index)?, r.node_ref(index)?)
        }
        Tag::FArgs => {
            let args = r.node_refs(index)?;
            Raw::FArgs(args, r.node_ref(index)?)
        }
        Tag::FRestore => Raw::FRestore(r.string()?),
        Tag::FHandle => Raw::FHandle(r.node_ref(index)?, r.node_ref(index)?),
        Tag::FMask => Raw::FMask(strs(r)?),
        Tag::EnvMap => {
            let n = r.bounded_len()?;
            let kvs = (0..n)
                .map(|_| Ok((r.string()?, r.node_ref(index)?)))
                .collect::<Result<Vec<_>, CodecError>>()?;
            Raw::EnvMap(kvs)
        }
        Tag::HInfo => {
            let body = r.node_ref(index)?;
            let ret_var = if r.bool()? { Some(r.string()?) } else { None };
            let ret_body = if r.bool()? {
                Some(r.node_ref(index)?)
            } else {
                None
            };
            let n = r.bounded_len()?;
            let ops = (0..n)
                .map(|_| {
                    let name = r.string()?;
                    let np = r.bounded_len()?;
                    let params = (0..np).map(|_| r.string()).collect::<Result<_, _>>()?;
                    let resume = r.string()?;
                    let body = r.node_ref(index)?;
                    Ok(RawHandleOp {
                        name,
                        params,
                        resume,
                        body,
                    })
                })
                .collect::<Result<Vec<_>, CodecError>>()?;
            Raw::HInfo {
                body,
                ret_var,
                ret_body,
                ops,
            }
        }
    })
}

// Reconstruction: the parsed table plus the expansion budget bounding a shared-DAG
// blow-up. Each `*_at` method interprets a table entry in one runtime domain,
// rejecting a cross-domain reference (a hostile frame that points a value slot at,
// say, a handler record) as malformed.
struct Builder<'a> {
    nodes: &'a [Raw],
    budget: usize,
    depth: usize,
}

impl Builder<'_> {
    fn spend(&mut self) -> Result<(), CodecError> {
        self.budget = self.budget.checked_sub(1).ok_or(CodecError::DepthLimit)?;
        Ok(())
    }

    // Enter one level of reconstruction, rejecting a chain deeper than the native
    // stack can bear. Every recursive `*_at` calls this at entry and drops `depth`
    // back before its `Ok(..)`; an error path unwinds the whole decode, so a
    // skipped decrement there is harmless. `budget` bounds total nodes (a wide DAG),
    // this bounds the recursion depth (a deep chain); a hostile envelope needs both.
    fn descend(&mut self) -> Result<(), CodecError> {
        self.spend()?;
        self.depth += 1;
        if self.depth > MAX_SUSPEND_DEPTH {
            return Err(CodecError::DepthLimit);
        }
        Ok(())
    }

    fn at(&self, i: u32) -> Result<&Raw, CodecError> {
        self.nodes.get(i as usize).ok_or(CodecError::BadReference)
    }

    fn value_at(&mut self, i: u32) -> Result<Rv, CodecError> {
        self.descend()?;
        let out = match self.at(i)?.clone() {
            Raw::VInt(n) => Rv::Int(n),
            Raw::VI64(n) => Rv::I64(n),
            Raw::VU64(n) => Rv::U64(n),
            Raw::VFloat(f) => Rv::Float(f),
            Raw::VBool(b) => Rv::Bool(b),
            Raw::VUnit => Rv::Unit,
            Raw::VStr(s) => Rv::Str(s),
            Raw::VBig(bytes) => Rv::Big(BigInt::from_signed_bytes_le(&bytes)),
            Raw::VClosure(ps, body, env) => {
                let ps: Rc<[Sym]> = ps.iter().map(|s| Sym::new(s)).collect();
                Rv::Closure(ps, self.comp_at(body)?, self.env_at(env)?)
            }
            Raw::VThunk(body, env) => Rv::Thunk(self.comp_at(body)?, self.env_at(env)?),
            Raw::VData(name, args) => Rv::Data(Sym::new(&name), self.values_at(&args)?.into()),
            Raw::VTuple(args) => Rv::Tuple(self.values_at(&args)?.into()),
            Raw::VArray(args) => Rv::Array(self.values_at(&args)?.into()),
            Raw::VBuf(bytes) => Rv::Buf(Rc::new(bytes)),
            Raw::VResume(frames) => Rv::Resume(self.frames_at(&frames)?.into()),
            _ => return Err(CodecError::Malformed),
        };
        self.depth -= 1;
        Ok(out)
    }

    fn values_at(&mut self, idxs: &[u32]) -> Result<Vec<Rv>, CodecError> {
        idxs.iter().map(|i| self.value_at(*i)).collect()
    }

    fn env_at(&mut self, i: u32) -> Result<Env, CodecError> {
        self.descend()?;
        let Raw::EnvMap(kvs) = self.at(i)?.clone() else {
            return Err(CodecError::Malformed);
        };
        let mut map = BTreeMap::new();
        for (k, vi) in kvs {
            map.insert(Sym::new(&k), self.value_at(vi)?);
        }
        self.depth -= 1;
        Ok(Rc::new(map))
    }

    fn atom_at(&mut self, i: u32) -> Result<Atom, CodecError> {
        self.descend()?;
        let out = match self.at(i)?.clone() {
            Raw::AVar(x) => Atom::Var(Sym::new(&x)),
            Raw::AInt(n) => Atom::Int(n),
            Raw::AI64(n) => Atom::I64(n),
            Raw::AU64(n) => Atom::U64(n),
            Raw::AFloat(f) => Atom::Float(f),
            Raw::ABool(b) => Atom::Bool(b),
            Raw::AUnit => Atom::Unit,
            Raw::AStr(s) => Atom::Str(s),
            Raw::AThunk(c) => Atom::Thunk(self.comp_at(c)?),
            Raw::ACtor(name, args) => Atom::Ctor(Sym::new(&name), self.atoms_at(&args)?),
            Raw::ATuple(args) => Atom::Tuple(self.atoms_at(&args)?),
            _ => return Err(CodecError::Malformed),
        };
        self.depth -= 1;
        Ok(out)
    }

    fn atoms_at(&mut self, idxs: &[u32]) -> Result<Vec<Atom>, CodecError> {
        idxs.iter().map(|i| self.atom_at(*i)).collect()
    }

    fn build_pat(p: &RawPat) -> CorePat {
        match p.tag {
            PatTag::Wild => CorePat::Wild,
            PatTag::Var => CorePat::Var(Sym::new(&p.name)),
            PatTag::Ctor => CorePat::Ctor(
                Sym::new(&p.name),
                p.fields
                    .iter()
                    .map(|f| f.as_deref().map(Sym::new))
                    .collect(),
            ),
            PatTag::Tuple => CorePat::Tuple(
                p.fields
                    .iter()
                    .map(|f| f.as_deref().map(Sym::new))
                    .collect(),
            ),
        }
    }

    fn comp_at(&mut self, i: u32) -> Result<Cmp, CodecError> {
        self.descend()?;
        let node = match self.at(i)?.clone() {
            Raw::NReturn(a) => Node::Return(self.atom_at(a)?),
            Raw::NForce(a) => Node::Force(self.atom_at(a)?),
            Raw::NError(a) => Node::Error(self.atom_at(a)?),
            Raw::NPrint(a) => Node::Print(self.atom_at(a)?),
            Raw::NSrand(a) => Node::Srand(self.atom_at(a)?),
            Raw::NPrintNl => Node::PrintNl,
            Raw::NReadInt => Node::ReadInt,
            Raw::NReadLine => Node::ReadLine,
            Raw::NRand => Node::Rand,
            Raw::NBind(m, x, n) => Node::Bind(self.comp_at(m)?, Sym::new(&x), self.comp_at(n)?),
            Raw::NLam(ps, body) => {
                let ps: Rc<[Sym]> = ps.iter().map(|s| Sym::new(s)).collect();
                Node::Lam(ps, self.comp_at(body)?)
            }
            Raw::NApp(m, args) => {
                let m = self.comp_at(m)?;
                Node::App(m, self.atoms_at(&args)?.into())
            }
            Raw::NIf(a, t, e) => Node::If(self.atom_at(a)?, self.comp_at(t)?, self.comp_at(e)?),
            Raw::NPrim(op, a, b) => Node::Prim(op, self.atom_at(a)?, self.atom_at(b)?),
            Raw::NCall(name, args) => Node::Call(Sym::new(&name), self.atoms_at(&args)?),
            Raw::NCase(scrut, arms) => {
                let scrut = self.atom_at(scrut)?;
                let arms = arms
                    .iter()
                    .map(|(rp, body)| Ok((Self::build_pat(rp), self.comp_at(*body)?)))
                    .collect::<Result<Vec<_>, CodecError>>()?;
                Node::Case(scrut, arms)
            }
            Raw::NFloat(op, a) => Node::FloatBuiltin(op, self.atom_at(a)?),
            Raw::NNeg(lane, a) => Node::Neg(lane, self.atom_at(a)?),
            Raw::NDo(op, args) => Node::Do(Sym::new(&op), self.atoms_at(&args)?),
            Raw::NStr(b, args) => Node::StrBuiltin(b, self.atoms_at(&args)?),
            Raw::NHandle(h) => Node::Handle(Rc::new(self.handle_at(h)?)),
            Raw::NMask(ops, body) => Node::Mask(
                ops.iter().map(|s| Sym::new(s)).collect(),
                self.comp_at(body)?,
            ),
            _ => return Err(CodecError::Malformed),
        };
        self.depth -= 1;
        Ok(Rc::new(node))
    }

    fn handle_at(&mut self, i: u32) -> Result<HandleInfo, CodecError> {
        self.descend()?;
        let Raw::HInfo {
            body,
            ret_var,
            ret_body,
            ops,
        } = self.at(i)?.clone()
        else {
            return Err(CodecError::Malformed);
        };
        let body = self.comp_at(body)?;
        let return_body = match ret_body {
            Some(rb) => Some(self.comp_at(rb)?),
            None => None,
        };
        let mut op_map = BTreeMap::new();
        for op in ops {
            let params: Vec<Sym> = op.params.iter().map(|s| Sym::new(s)).collect();
            let resume = Sym::new(&op.resume);
            let obody = self.comp_at(op.body)?;
            op_map.insert(Sym::new(&op.name), (params, resume, obody));
        }
        self.depth -= 1;
        Ok(HandleInfo {
            body,
            ops: op_map,
            return_var: ret_var.as_deref().map(Sym::new),
            return_body,
        })
    }

    fn frame_at(&mut self, i: u32) -> Result<Frame, CodecError> {
        self.descend()?;
        let out = match self.at(i)?.clone() {
            Raw::FBind(x, n, env) => Frame::Bind(Sym::new(&x), self.comp_at(n)?, self.env_at(env)?),
            Raw::FArgs(args, env) => Frame::Args(self.atoms_at(&args)?.into(), self.env_at(env)?),
            Raw::FRestore(name) => Frame::Restore(Sym::new(&name)),
            Raw::FHandle(h, env) => Frame::Handle(Rc::new(self.handle_at(h)?), self.env_at(env)?),
            Raw::FMask(ops) => Frame::Mask(ops.iter().map(|s| Sym::new(s)).collect()),
            _ => return Err(CodecError::Malformed),
        };
        self.depth -= 1;
        Ok(out)
    }

    fn frames_at(&mut self, idxs: &[u32]) -> Result<Vec<Frame>, CodecError> {
        idxs.iter().map(|i| self.frame_at(*i)).collect()
    }
}

fn read_obs(r: &mut Reader<'_>) -> Result<Obs, CodecError> {
    Ok(match r.uvarint()? {
        OBS_INT => Obs::Int(r.svarint()?),
        OBS_STR => Obs::Str(r.string()?),
        OBS_BOOL => Obs::Bool(r.bool()?),
        OBS_OUT => Obs::Out,
        _ => return Err(CodecError::Malformed),
    })
}

/// Decode a `kont`-kind frame back to a live continuation.
///
/// Total: any malformed, truncated, or hostile input returns a [`CodecError`]
/// rather than panicking. The scheme, kind and bundle are checked before the body,
/// every length and varint is bounded, references are range-checked, reconstruction
/// is budgeted, and trailing bytes are rejected.
///
/// # Errors
/// Returns a [`CodecError`] describing the first inconsistency found.
pub fn decode_kont(bytes: &[u8]) -> Result<Kont, CodecError> {
    let mut r = Reader::new(bytes);
    if r.string()? != crate::core::HASH_SCHEME {
        return Err(CodecError::Scheme);
    }
    if r.uvarint()? != u64::from(WireKind::Kont.varint()) {
        return Err(CodecError::Kind);
    }
    let bundle = r.string()?;

    let rng = r.uvarint()?;
    let fn_name = Sym::new(&r.string()?);
    let observed = r.bounded_len()?;
    let exit = if r.bool()? {
        Some(i32::try_from(r.svarint()?).map_err(|_| CodecError::Malformed)?)
    } else {
        None
    };
    let trace_len = r.bounded_len()?;
    let trace = (0..trace_len)
        .map(|_| read_obs(&mut r))
        .collect::<Result<Vec<_>, _>>()?;
    let observation_len = r.bounded_len()?;
    let observations = (0..observation_len)
        .map(|_| {
            let json = r.string()?;
            serde_json::from_str(&json).map_err(|_| CodecError::Malformed)
        })
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
        )?);
    }

    let stack_len = r.bounded_len()?;
    let stack_idxs = (0..stack_len)
        .map(|_| {
            let i = u32::try_from(r.uvarint()?).map_err(|_| CodecError::BadReference)?;
            if i as usize >= nodes.len() {
                return Err(CodecError::BadReference);
            }
            Ok(i)
        })
        .collect::<Result<Vec<_>, CodecError>>()?;

    let state_tag = r.byte()?;
    let a = r.uvarint()?;
    let b = r.uvarint()?;
    let ai = u32::try_from(a).map_err(|_| CodecError::BadReference)?;
    let bi = u32::try_from(b).map_err(|_| CodecError::BadReference)?;
    if state_tag > 1 || ai as usize >= nodes.len() {
        return Err(CodecError::Malformed);
    }
    if state_tag == 0 && bi as usize >= nodes.len() {
        return Err(CodecError::BadReference);
    }

    if !r.at_end() {
        return Err(CodecError::TrailingBytes);
    }

    let mut builder = Builder {
        nodes: &nodes,
        budget: MAX_EXPANSION,
        depth: 0,
    };
    let stack = builder.frames_at(&stack_idxs)?;
    let state = match state_tag {
        0 => KontState::Eval(builder.comp_at(ai)?, builder.env_at(bi)?),
        _ => KontState::Ret(builder.value_at(ai)?),
    };

    Ok(Kont {
        bundle,
        stack,
        state,
        rng,
        fn_name,
        observed,
        exit,
        trace,
        observations,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::rc::Rc;

    use num_bigint::BigInt;

    use super::super::{Atom, Cmp, Env, Frame, HandleInfo, Node, Obs, Rv};
    use super::{decode_kont, encode_kont, Kont, KontState, SuspendError};
    use crate::core::builtins::{Builtin, FloatOp};
    use crate::core::{CoreOp, CorePat, NegLane};
    use crate::store::CodecError;
    use crate::sym::Sym;

    fn cmp(n: Node) -> Cmp {
        Rc::new(n)
    }

    fn env(pairs: Vec<(&str, Rv)>) -> Env {
        Rc::new(pairs.into_iter().map(|(k, v)| (Sym::new(k), v)).collect())
    }

    // A continuation exercising every value, node, atom, frame, pattern and
    // handler shape the codec must round-trip, so the idempotence and totality
    // checks below cover the whole table, not just the common cases.
    fn kitchen_sink() -> Kont {
        let inner_body = cmp(Node::Prim(
            CoreOp::Add,
            Atom::Var(Sym::new("x")),
            Atom::Int(2),
        ));
        let handler = HandleInfo {
            body: cmp(Node::Do(Sym::new("ask"), vec![Atom::Unit])),
            ops: BTreeMap::from([
                (
                    Sym::new("ask"),
                    (
                        vec![Sym::new("p")],
                        Sym::new("k"),
                        cmp(Node::App(
                            cmp(Node::Force(Atom::Var(Sym::new("k")))),
                            Rc::from([Atom::Int(7)]),
                        )),
                    ),
                ),
                (
                    Sym::new("tell"),
                    (
                        vec![Sym::new("a"), Sym::new("b")],
                        Sym::new("k2"),
                        cmp(Node::Return(Atom::Unit)),
                    ),
                ),
            ]),
            return_var: Some(Sym::new("r")),
            return_body: Some(cmp(Node::Return(Atom::Var(Sym::new("r"))))),
        };
        let big_body = cmp(Node::Bind(
            cmp(Node::Return(Atom::Int(1))),
            Sym::new("x"),
            cmp(Node::Case(
                Atom::Var(Sym::new("x")),
                vec![
                    (CorePat::Wild, cmp(Node::Return(Atom::Unit))),
                    (
                        CorePat::Var(Sym::new("y")),
                        cmp(Node::Return(Atom::Var(Sym::new("y")))),
                    ),
                    (
                        CorePat::Ctor(Sym::new("Cons"), vec![Some(Sym::new("h")), None]),
                        cmp(Node::If(
                            Atom::Bool(true),
                            cmp(Node::FloatBuiltin(FloatOp::Sqrt, Atom::Float(2.0))),
                            cmp(Node::Neg(NegLane::Float, Atom::Float(1.5))),
                        )),
                    ),
                    (
                        CorePat::Tuple(vec![Some(Sym::new("a")), Some(Sym::new("b"))]),
                        cmp(Node::StrBuiltin(
                            Builtin::Concat,
                            vec![Atom::Str("h".into()), Atom::Str("i".into())],
                        )),
                    ),
                ],
            )),
        ));
        let lam = Rv::Closure(
            Rc::from([Sym::new("x")]),
            inner_body,
            env(vec![("captured", Rv::Int(99))]),
        );
        let list = Rv::Data(
            Sym::new("Cons"),
            vec![
                Rv::Int(1),
                Rv::Data(
                    Sym::new("Cons"),
                    vec![
                        Rv::Str("two".into()),
                        Rv::Data(Sym::new("Nil"), vec![].into()),
                    ]
                    .into(),
                ),
            ]
            .into(),
        );
        let resume = Rv::Resume(Rc::from([
            Frame::Restore(Sym::new("caller")),
            Frame::Mask(Rc::from([Sym::new("ask")])),
        ]));
        let base_env = env(vec![
            ("i64", Rv::I64(-5)),
            ("u64", Rv::U64(42)),
            ("f", Rv::Float(-0.0)),
            ("b", Rv::Bool(true)),
            ("unit", Rv::Unit),
            ("big", Rv::Big(BigInt::from(1) << 200)),
            ("buf", Rv::Buf(Rc::new(vec![0u8, 255, 7, 128]))),
            ("tup", Rv::Tuple(vec![Rv::Int(1), Rv::Unit].into())),
            ("arr", Rv::Array(vec![Rv::Int(3), Rv::Int(4)].into())),
            ("thunk", Rv::Thunk(cmp(Node::PrintNl), env(vec![]))),
            ("lam", lam),
            ("list", list),
            ("resume", resume),
        ]);
        let stack = vec![
            Frame::Restore(Sym::new("main")),
            Frame::Bind(
                Sym::new("z"),
                cmp(Node::Return(Atom::Var(Sym::new("z")))),
                base_env.clone(),
            ),
            Frame::Args(
                Rc::from([Atom::Int(1), Atom::Var(Sym::new("i64"))]),
                base_env.clone(),
            ),
            Frame::Handle(Rc::new(handler), base_env.clone()),
            Frame::Mask(Rc::from([Sym::new("tell")])),
        ];
        Kont {
            bundle: "deadbeefcafef00d".into(),
            stack,
            state: KontState::Eval(big_body, base_env),
            rng: 0x9E37_79B9_7F4A_7C15,
            fn_name: Sym::new("main"),
            observed: 3,
            exit: None,
            trace: vec![
                Obs::Int(10),
                Obs::Str("hi".into()),
                Obs::Bool(false),
                Obs::Out,
            ],
            observations: vec![crate::provenance::Observation::Stdout(b"hi".to_vec())],
        }
    }

    #[test]
    fn roundtrip_is_byte_idempotent() {
        let k = kitchen_sink();
        let bytes = encode_kont(&k).expect("kitchen sink encodes");
        let decoded = decode_kont(&bytes).expect("decodes");
        let bytes2 = encode_kont(&decoded).expect("re-encodes");
        assert_eq!(bytes, bytes2, "encode(decode(encode(k))) is byte-identical");
        // Scalars survive verbatim.
        assert_eq!(decoded.bundle, k.bundle);
        assert_eq!(decoded.rng, k.rng);
        assert_eq!(decoded.fn_name.as_str(), "main");
        assert_eq!(decoded.observed, k.observed);
        assert_eq!(decoded.exit, k.exit);
        assert_eq!(decoded.trace, k.trace);
        assert_eq!(decoded.observations, k.observations);
        assert_eq!(decoded.stack.len(), k.stack.len());
    }

    #[test]
    fn ret_state_roundtrips() {
        let k = Kont {
            state: KontState::Ret(Rv::Data(
                Sym::new("Ok"),
                vec![Rv::Int(1), Rv::Str("done".into())].into(),
            )),
            ..kitchen_sink()
        };
        let bytes = encode_kont(&k).unwrap();
        let bytes2 = encode_kont(&decode_kont(&bytes).unwrap()).unwrap();
        assert_eq!(bytes, bytes2);
    }

    #[test]
    fn empty_and_short_inputs_never_panic() {
        for n in 0..64 {
            let _ = decode_kont(&vec![0u8; n]);
        }
    }

    #[test]
    fn wrong_scheme_and_kind_rejected() {
        // A def-kind frame's scheme is fine but the kind is wrong.
        let mut buf = Vec::new();
        super::put_str(&mut buf, crate::core::HASH_SCHEME);
        super::put_uvarint(&mut buf, u64::from(crate::driver::WireKind::Def.varint()));
        assert_eq!(decode_kont(&buf).unwrap_err(), CodecError::Kind);

        let mut foreign = Vec::new();
        super::put_str(&mut foreign, "not-prism");
        assert_eq!(decode_kont(&foreign).unwrap_err(), CodecError::Scheme);
    }

    #[test]
    fn truncation_at_every_prefix_is_total() {
        let bytes = encode_kont(&kitchen_sink()).unwrap();
        for cut in 0..bytes.len() {
            // Must return Err (or, for a coincidentally-complete prefix, Ok), never
            // panic. A truncated frame can never be the full frame, so it either
            // errors or is a strict prefix the reader rejects.
            let _ = decode_kont(&bytes[..cut]);
        }
    }

    #[test]
    fn trailing_bytes_rejected() {
        let mut bytes = encode_kont(&kitchen_sink()).unwrap();
        bytes.push(0);
        assert_eq!(decode_kont(&bytes).unwrap_err(), CodecError::TrailingBytes);
    }

    #[test]
    fn corrupting_any_byte_never_panics() {
        let base = encode_kont(&kitchen_sink()).unwrap();
        for i in 0..base.len() {
            for delta in [1u8, 0x7f, 0x80, 0xff] {
                let mut b = base.clone();
                b[i] = b[i].wrapping_add(delta);
                // Totality: a single-byte perturbation is decoded or rejected, never
                // a panic.
                let _ = decode_kont(&b);
            }
        }
    }

    #[test]
    fn oversized_node_count_rejected() {
        // Hand-build a header with a monstrous node count.
        let mut buf = Vec::new();
        super::put_str(&mut buf, crate::core::HASH_SCHEME);
        super::put_uvarint(&mut buf, u64::from(crate::driver::WireKind::Kont.varint()));
        super::put_str(&mut buf, "bundle");
        super::put_uvarint(&mut buf, 0); // rng
        super::put_str(&mut buf, "main"); // fn_name
        super::put_uvarint(&mut buf, 0); // observed
        buf.push(0); // exit: none
        super::put_uvarint(&mut buf, 0); // trace len
        super::put_uvarint(&mut buf, 0); // observation len
        super::put_uvarint(&mut buf, u64::MAX); // node_count
        assert_eq!(decode_kont(&buf).unwrap_err(), CodecError::TooLarge);
    }

    #[test]
    fn deeply_nested_value_is_refused_by_name() {
        // A value nested past the suspendable depth is refused, not encoded.
        let mut v = Rv::Data(Sym::new("Nil"), vec![].into());
        for _ in 0..(super::MAX_SUSPEND_DEPTH + 64) {
            v = Rv::Data(Sym::new("Cons"), vec![Rv::Int(0), v].into());
        }
        let k = Kont {
            state: KontState::Ret(v),
            ..kitchen_sink()
        };
        match encode_kont(&k) {
            Err(SuspendError::NonSerializable(msg)) => {
                assert!(msg.contains("value"), "refusal names the value: {msg}");
            }
            other => panic!("expected a refusal, got {other:?}"),
        }
    }

    #[test]
    fn a_moderately_deep_list_still_roundtrips() {
        let mut v = Rv::Data(Sym::new("Nil"), vec![].into());
        for i in 0..128 {
            v = Rv::Data(Sym::new("Cons"), vec![Rv::Int(i), v].into());
        }
        let k = Kont {
            state: KontState::Ret(v),
            ..kitchen_sink()
        };
        let bytes = encode_kont(&k).unwrap();
        let bytes2 = encode_kont(&decode_kont(&bytes).unwrap()).unwrap();
        assert_eq!(bytes, bytes2);
    }
}
