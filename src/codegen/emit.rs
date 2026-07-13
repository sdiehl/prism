//! Backend-neutral lowering walker. All semantic decisions (tagging, closure
//! layout, case dispatch, RC, tail calls) live here. An `Isa` impl supplies
//! only the instructions of its target (LLVM via inkwell or MLIR's llvm
//! dialect as text). The two targets differ structurally in one place: LLVM
//! merges control flow with phi nodes, MLIR with block arguments, abstracted
//! as `jump_merge`/`open_merge`.

use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "mlir")]
use std::fmt::Write;
use std::mem::size_of;
use std::slice;

use serde::{Deserialize, Serialize};

const CLOSURE_TAG_SCHEME: &[u8] = b"prism-closure-tag-v1";
const CLOSURE_TAG_MASK: u64 = i64::MAX.cast_unsigned();

use super::abi::{ctor_tag, idx64, BIG_TAG, HDR_BYTES, STR_TAG, TAG_OFF, WORD_BYTES};
use super::dispatch::partial_app_body;
use super::isa::{Buf, Cmp, FloatBinOp, FloatIntrinsic, IntOp, Isa};
use super::rt;
#[cfg(feature = "mlir")]
use crate::core::builtins::BUILTINS;
use crate::core::builtins::{builtin, AbiArg, AbiResult, Builtin, BuiltinKind, FloatOp};
use crate::core::effect_lower::{is_free_monad_driver, EOP};
use crate::core::tailrec::{reassoc, trmc_mode, trmc_shape, TrmcMode, TrmcShape};
use crate::core::{fv, reachable_fns, Comp, Core, CoreFn, CoreOp, CorePat, IoOp, NegLane, Value};
use crate::names::{closure_cap, generated_param};
use crate::sym::Sym;
use crate::types::CtorInfo;

// Variable identity stays `Sym` end-to-end; the value is the SSA register name
// (`%t3`, `%a0`, ...), the legitimate output-edge text.
type Regs = BTreeMap<Sym, String>;

fn closure_tag(owner: Sym, ordinal: usize) -> usize {
    let mut hasher = blake3::Hasher::new();
    hasher.update(CLOSURE_TAG_SCHEME);
    hasher.update(owner.as_str().as_bytes());
    hasher.update(&ordinal.to_le_bytes());
    let mut bytes = [0; size_of::<u64>()];
    bytes.copy_from_slice(&hasher.finalize().as_bytes()[..size_of::<u64>()]);
    let mut tag = u64::from_le_bytes(bytes) & CLOSURE_TAG_MASK;
    while tag == BIG_TAG.cast_unsigned() || tag == STR_TAG.cast_unsigned() {
        tag = (tag + 1) & CLOSURE_TAG_MASK;
    }
    usize::try_from(tag).expect("closure tags fit the native target word")
}

#[derive(Clone)]
pub(super) enum LamBody {
    // An ordinary closure.
    Core(Comp),
    // A curry adapter for under-application. Once saturated with its remaining
    // params it forwards all captured-plus-remaining values to `target` (an
    // index into `lams`), which has the full arity.
    Curry { target: usize },
}

#[derive(Clone)]
pub(super) struct LamInfo {
    pub(super) tag: usize,
    pub(super) owner: Sym,
    pub(super) params: Vec<Sym>,
    pub(super) free_vars: Vec<Sym>,
    pub(super) body: LamBody,
}

// TRMC (tail recursion modulo constructor / addition). A function whose
// recursive call feeds exactly one constructor field in tail position, like
// `Cons(y, map(f, rest))`, is split into `prism_N` (a thin wrapper) and
// `prism_N.trmc(args.., hole)`: each step allocates the constructor with a zero
// placeholder in the recursive field, stores the cell into the incoming hole,
// and musttail-recurses on the placeholder's address. Base cases store their
// result into the hole. The wrapper passes a stack slot as the first hole and
// returns its final contents, so the chain runs in constant stack. Ownership is
// unchanged: fields stored at allocation are owned by the new cell as on the
// non-TRMC path, and each hole is written once before anyone reads it. `1 + f(x)`
// tails get the same treatment with an integer accumulator instead of a hole
// (Int `+` is associative and commutative, including bignum promotion).
//
// The decision of WHICH shape a tail realizes (`trmc_mode`/`trmc_shape`) lives
// in `core::tailrec`, shared with the `fip` bounded-stack check so the static
// promise and this emitted code can never classify a tail differently. Only the
// code emission below is backend-specific.
#[derive(Clone)]
struct TrmcCtx {
    name: Sym,
    sym: String,
    arity: usize,
    mode: TrmcMode,
    extra: String,
}

pub(super) struct Cg<'a, I> {
    pub(super) isa: &'a I,
    b: Buf,
    cur_arity: usize,
    ctors: &'a BTreeMap<String, CtorInfo>,
    fn_arities: BTreeMap<String, usize>,
    pub(super) lams: Vec<LamInfo>,
    // Curry adapters memoized by (target lam, supplied arg count), so dispatch
    // planning and emission agree on adapter tags.
    pub(super) adapters: BTreeMap<(usize, usize), usize>,
    strs: Vec<String>,
    used_rt: BTreeMap<String, usize>,
    // Owned-libm transcendentals actually called (the `prism_m_*` symbols). These
    // take and return `f64` rather than the `i64` of `used_rt`, so they carry a
    // distinct declaration (see `declare_f`).
    used_fcall: BTreeSet<String>,
    // Arities at which `prism_apply_n` is actually called. A 0-arg `App` (and any
    // arity with no matching lambda) still needs the function emitted, or it is
    // an undefined symbol at link time.
    pub(super) used_apply: BTreeSet<usize>,
    current_owner: Option<Sym>,
    owner_ordinals: BTreeMap<Sym, usize>,
    used_closure_tags: BTreeSet<usize>,
    trmc: Option<TrmcCtx>,
}

impl<'a, I: Isa> Cg<'a, I> {
    fn new(
        isa: &'a I,
        ctors: &'a BTreeMap<String, CtorInfo>,
        fn_arities: BTreeMap<String, usize>,
    ) -> Self {
        Self {
            isa,
            b: Buf::default(),
            cur_arity: 0,
            ctors,
            fn_arities,
            lams: Vec::new(),
            adapters: BTreeMap::new(),
            strs: Vec::new(),
            used_rt: BTreeMap::new(),
            used_fcall: BTreeSet::new(),
            used_apply: BTreeSet::new(),
            current_owner: None,
            owner_ordinals: BTreeMap::new(),
            used_closure_tags: BTreeSet::new(),
            trmc: None,
        }
    }

    pub(super) fn mint_closure_tag(&mut self, owner: Sym) -> Result<usize, String> {
        let ordinal = self.owner_ordinals.entry(owner).or_default();
        let tag = closure_tag(owner, *ordinal);
        *ordinal += 1;
        if self.used_closure_tags.insert(tag) {
            Ok(tag)
        } else {
            Err(format!("ICE: closure tag collision for `{owner}`"))
        }
    }

    fn dst(&mut self, emit: impl FnOnce(&I, &mut Buf, &str)) -> String {
        let t = self.b.tmp();
        emit(self.isa, &mut self.b, &t);
        t
    }

    fn values(&mut self, regs: &Regs, vs: &[Value]) -> Result<Vec<String>, String> {
        vs.iter().map(|v| self.value(regs, v)).collect()
    }

    fn sym(name: &str) -> String {
        super::native_symbol(name)
    }

    fn fn_arity(&self, name: &str) -> Result<usize, String> {
        self.fn_arities
            .get(name)
            .copied()
            .ok_or_else(|| format!("ICE: unknown function `{name}` in arity table"))
    }

    fn fill_obj(&mut self, ptr: &str, tag: i64, fields: &[String]) -> String {
        assert!(
            tag < BIG_TAG.min(STR_TAG),
            "ICE: ctor tag collides with reserved heap tags"
        );
        self.fill_tagged_obj(ptr, tag, fields)
    }

    fn fill_tagged_obj(&mut self, ptr: &str, tag: i64, fields: &[String]) -> String {
        let tag_ptr = self.dst(|i, b, d| i.gep(b, d, ptr, TAG_OFF));
        let tv = self.isa.const_int(&mut self.b, tag);
        self.isa.store(&mut self.b, &tv, &tag_ptr);
        for (i, fv) in fields.iter().enumerate() {
            let off = HDR_BYTES + idx64(i) * WORD_BYTES;
            let fp = self.dst(|i, b, d| i.gep(b, d, ptr, off));
            self.isa.store(&mut self.b, fv, &fp);
        }
        self.dst(|i, b, d| i.ptrtoint(b, d, ptr))
    }

    fn alloc_obj(&mut self, tag: i64, fields: &[String]) -> String {
        let n = self.isa.const_int(&mut self.b, idx64(fields.len()));
        let ptr = self.dst(|i, b, d| i.call_ptr(b, d, rt::ALLOC, slice::from_ref(&n)));
        self.fill_obj(&ptr, tag, fields)
    }

    fn alloc_closure_obj(&mut self, tag: i64, fields: &[String]) -> String {
        let n = self.isa.const_int(&mut self.b, idx64(fields.len()));
        let ptr = self.dst(|i, b, d| i.call_ptr(b, d, rt::ALLOC, slice::from_ref(&n)));
        self.fill_tagged_obj(&ptr, tag, fields)
    }

    fn reuse_obj(&mut self, token: &str, tag: i64, fields: &[String]) -> String {
        let n = self.isa.const_int(&mut self.b, idx64(fields.len()));
        let args = [token.to_string(), n];
        let ptr = self.dst(|i, b, d| i.call_ptr(b, d, rt::REUSE_ALLOC, &args));
        self.fill_obj(&ptr, tag, fields)
    }

    fn alloc_closure(
        &mut self,
        regs: &Regs,
        params: &[Sym],
        body: &Comp,
    ) -> Result<String, String> {
        // `Sym` orders by intern id, so sort captures by name to keep the closure
        // cell layout (and `_fv` numbering) byte-stable across runs.
        let mut free_vars: Vec<Sym> = fv::comp_without(body, params).into_iter().collect();
        free_vars.sort_by_cached_key(|s| s.as_str());

        let owner = self
            .current_owner
            .ok_or_else(|| "ICE: closure without a top-level owner".to_string())?;
        let tag = self.mint_closure_tag(owner)?;
        self.lams.push(LamInfo {
            tag,
            owner,
            params: params.to_vec(),
            free_vars: free_vars.clone(),
            body: LamBody::Core(body.clone()),
        });

        let fvs: Vec<String> = free_vars
            .iter()
            .map(|fv| {
                regs.get(fv)
                    .cloned()
                    .ok_or_else(|| format!("unbound free var {fv}"))
            })
            .collect::<Result<_, _>>()?;
        Ok(self.alloc_closure_obj(idx64(tag), &fvs))
    }

    fn untag(&mut self, v: &str) -> String {
        let one = self.isa.const_int(&mut self.b, 1);
        self.dst(|i, b, d| i.bin(b, d, IntOp::Ashr, v, &one))
    }

    fn retag(&mut self, v: &str) -> String {
        let one = self.isa.const_int(&mut self.b, 1);
        let s = self.dst(|i, b, d| i.bin(b, d, IntOp::Shl, v, &one));
        self.dst(|i, b, d| i.bin(b, d, IntOp::Or, &s, &one))
    }

    fn rc_dec(&mut self, v: &str) {
        self.isa
            .call_void(&mut self.b, rt::RC_DEC, &[v.to_string()]);
    }

    fn unbox(&mut self, p: &str) -> String {
        self.dst(|i, b, d| i.call(b, d, rt::UNBOX, &[p.to_string()]))
    }

    fn box_i64(&mut self, payload: &str) -> String {
        self.dst(|i, b, d| i.call(b, d, rt::BOX, &[payload.to_string()]))
    }

    // Canonicalize a raw i64 into an `Int` word (tagged immediate, or a bignum
    // cell when it overflows the 63-bit tag). Used by the saturating float->int
    // conversions, whose i64::MIN/MAX results do not fit the immediate range.
    fn int_of_long(&mut self, raw: &str) -> String {
        self.used_rt.insert(rt::INT_OF_LONG.into(), 1);
        self.dst(|i, b, d| i.call(b, d, rt::INT_OF_LONG, &[raw.to_string()]))
    }

    fn f_in(&mut self, v: &str) -> String {
        let bits = self.unbox(v);
        self.dst(|i, b, d| i.cast_i2f(b, d, &bits))
    }

    fn f_out(&mut self, fv: &str) -> String {
        let bits = self.dst(|i, b, d| i.cast_f2i(b, d, fv));
        self.box_i64(&bits)
    }

    // Every Prism value is a single i64. Pointer tagging keeps the low bit as a
    // discriminant: `1` marks an immediate (small int, bool, unit packed inline),
    // `0` marks a heap cell whose i64 is its aligned address (cells are at least
    // 2-aligned, so a real pointer never sets the low bit). An immediate int `n`
    // is stored as `(n << 1) | 1`, recovered by an arithmetic `>> 1`. This is what
    // makes dup/drop no-ops on immediates: the runtime's inc/dec skip any value
    // with the low bit set or equal to 0 (unit), so emitting refcount ops on a
    // non-cell is always harmless.
    fn value(&mut self, regs: &Regs, v: &Value) -> Result<String, String> {
        match v {
            Value::Var(x) => regs
                .get(x)
                .cloned()
                .ok_or_else(|| format!("codegen: unbound {x}")),
            Value::Int(n) => Ok(self.isa.const_int(&mut self.b, n.wrapping_shl(1) | 1)),
            Value::I64(n) => {
                let c = self.isa.const_int(&mut self.b, *n);
                Ok(self.box_i64(&c))
            }
            Value::U64(n) => {
                let c = self.isa.const_int(&mut self.b, n.cast_signed());
                Ok(self.box_i64(&c))
            }
            Value::Bool(b) => Ok(self.isa.const_int(&mut self.b, (i64::from(*b) << 1) | 1)),
            Value::Unit => Ok(self.isa.const_int(&mut self.b, 0)),
            Value::Float(f) => {
                let ft = self.isa.const_float(&mut self.b, *f);
                Ok(self.f_out(&ft))
            }
            Value::Str(s) => {
                let idx = self.strs.len();
                let nbytes = s.len();
                self.strs.push(s.clone());
                Ok(self.dst(|i, b, d| i.str_lit(b, d, idx, nbytes)))
            }
            Value::Thunk(inner) => match inner.as_ref() {
                Comp::Lam(params, body) => self.alloc_closure(regs, params, body),
                _ => Err("unsupported thunk form (non-lam)".into()),
            },
            // A locally-constructed-and-projected unboxed product is scalarized
            // away by the optimizer (case-of-known-product), so it never reaches
            // codegen: that is the zero-cell win. One that escapes across a
            // non-inlined boundary survives to here; until true cross-boundary
            // flattening (product-in-registers), it is boxed exactly like a tuple,
            // which keeps observable behavior identical (only the layout, not the
            // semantics, differs). `UnboxedRecord` never reaches codegen: a record
            // lowers positionally to `UnboxedTuple` at elaboration.
            Value::Tuple(fields) | Value::UnboxedTuple(fields) => {
                let fvs = self.values(regs, fields)?;
                Ok(self.alloc_obj(0, &fvs))
            }
            Value::Ctor(name, tag, fields) => {
                let fvs = self.values(regs, fields)?;
                let obj = self.alloc_obj(idx64(*tag), &fvs);
                // Count the EOp cell each `do op` builds (stderr-only under
                // PRISM_EFFOP_STATS, so stdout is untouched).
                if name.as_str() == EOP {
                    self.isa.call_void(&mut self.b, rt::EFFOP_ALLOC, &[]);
                }
                Ok(obj)
            }
            Value::UnboxedRecord(_) => {
                Err("unboxed record value reached codegen; records lower positionally".into())
            }
        }
    }

    fn lower(&mut self, regs: &Regs, c: &Comp) -> Result<String, String> {
        match c {
            Comp::Return(v) | Comp::Force(v) => self.value(regs, v),
            Comp::Bind(m, x, n) => {
                let r = self.lower(regs, m)?;
                let mut r2 = regs.clone();
                r2.insert(*x, r);
                self.lower(&r2, n)
            }
            Comp::Prim(op, a, b) => {
                let a = self.value(regs, a)?;
                let b = self.value(regs, b)?;
                let r = self.prim(*op, &a, &b);
                self.rc_dec(&a);
                self.rc_dec(&b);
                Ok(r)
            }
            Comp::Call(name, args) => {
                let arity = self.fn_arity(name.as_str())?;
                let mut avs = Vec::new();
                for a in args {
                    avs.push(self.value(regs, a)?);
                }
                if avs.len() >= arity {
                    let f = Self::sym(name.as_str());
                    Ok(self.dst(|i, b, d| i.call(b, d, &f, &avs)))
                } else {
                    let (cap_names, rem_names, body) =
                        partial_app_body(name.as_str(), avs.len(), arity);
                    let mut temp_regs = regs.clone();
                    for (cn, av) in cap_names.iter().zip(&avs) {
                        temp_regs.insert(*cn, av.clone());
                    }
                    self.alloc_closure(&temp_regs, &rem_names, &body)
                }
            }
            Comp::Io(op, args) => match op {
                IoOp::Print => {
                    let r = self.value(regs, &args[0])?;
                    self.isa
                        .call_void(&mut self.b, rt::PRINT_INT, slice::from_ref(&r));
                    self.rc_dec(&r);
                    Ok(self.isa.const_int(&mut self.b, 0))
                }
                IoOp::PrintF => {
                    let r = self.value(regs, &args[0])?;
                    // Pass the raw double bits; the runtime formats them with the same
                    // shortest-round-trip layout as `show_float` (not C `%g`).
                    let bits = self.unbox(&r);
                    self.isa
                        .call_void(&mut self.b, rt::PRINT_FLOAT, slice::from_ref(&bits));
                    self.rc_dec(&r);
                    Ok(self.isa.const_int(&mut self.b, 0))
                }
                IoOp::PrintS => {
                    let r = self.value(regs, &args[0])?;
                    let cp = self.dst(|i, b, d| i.inttoptr(b, d, &r));
                    let bp = self.dst(|i, b, d| i.gep(b, d, &cp, HDR_BYTES));
                    self.isa.printf_str(&mut self.b, &bp);
                    self.rc_dec(&r);
                    Ok(self.isa.const_int(&mut self.b, 0))
                }
                IoOp::PrintNl => {
                    self.isa.call_void(&mut self.b, rt::PRINT_NL, &[]);
                    Ok(self.isa.const_int(&mut self.b, 0))
                }
                IoOp::ReadInt => {
                    // The runtime returns an already-encoded Int (a tagged
                    // immediate, or a bignum cell when the value exceeds the
                    // 63-bit immediate range), so no retag here: shifting a
                    // full-width i64 would silently drop bit 62.
                    Ok(self.dst(|i, b, d| i.call(b, d, rt::READ_INT, &[])))
                }
                IoOp::ReadLine => Ok(self.dst(|i, b, d| i.call(b, d, rt::READ_LINE, &[]))),
                IoOp::Rand => {
                    let t = self.dst(|i, b, d| i.call(b, d, rt::RAND, &[]));
                    Ok(self.retag(&t))
                }
                IoOp::Srand => {
                    let r = self.value(regs, &args[0])?;
                    let ut = self.untag(&r);
                    self.isa
                        .call_void(&mut self.b, rt::SRAND, slice::from_ref(&ut));
                    Ok(self.isa.const_int(&mut self.b, 0))
                }
            },
            // `error(v)` is the Exn fault, not a clean exit: an internal string
            // message routes through `prism_fatal`, an `error(n)` int payload
            // through `prism_error_int`. Both report to stderr and terminate with
            // status 1 (the interpreter's fault behavior); the int is not a
            // process exit code (that is the separate `exit` builtin).
            Comp::Error(v) => {
                let r = self.value(regs, v)?;
                if matches!(v, Value::Str(_)) {
                    self.isa.call_void(&mut self.b, rt::FATAL, &[r]);
                } else {
                    let code = self.untag(&r);
                    self.isa.call_void(&mut self.b, rt::ERROR_INT, &[code]);
                }
                Ok(self.isa.const_int(&mut self.b, 0))
            }
            Comp::If(v, t, e) => self.lower_if(regs, v, t, e, false),
            Comp::Lam(..) => Err("bare Lam in lower; should be inside Thunk".into()),
            Comp::App(f_comp, args) => {
                let clos = self.lower(regs, f_comp)?;
                let mut avs = vec![clos.clone()];
                for a in args {
                    avs.push(self.value(regs, a)?);
                }
                self.used_apply.insert(args.len());
                let f = format!("prism_apply_{}", args.len());
                let t = self.dst(|i, b, d| i.call(b, d, &f, &avs));
                self.rc_dec(&clos);
                Ok(t)
            }
            Comp::Case(val, arms) => self.lower_case(regs, val, arms, false),
            Comp::FloatBuiltin(op, v) => {
                let a = self.value(regs, v)?;
                let out = match op {
                    // int -> float.
                    FloatOp::ToFloat => {
                        let ua = self.untag(&a);
                        let rf = self.dst(|i, b, d| i.sitofp(b, d, &ua));
                        self.f_out(&rf)
                    }
                    // float -> int, saturating (NaN -> 0). `fptosi_sat` matches the
                    // interpreter's `f as i64`, pinning identical out-of-range
                    // behavior on both backends (plain `fptosi` is UB there). The
                    // saturated i64 can be i64::MIN/MAX, which overflow the 63-bit
                    // tag, so canonicalize through `prism_int_of_long` (promotes to
                    // a bignum when needed) rather than an inline retag.
                    FloatOp::Truncate => {
                        let fa = self.f_in(&a);
                        let r = self.dst(|i, b, d| i.fptosi_sat(b, d, &fa));
                        self.int_of_long(&r)
                    }
                    FloatOp::FloorToInt | FloatOp::CeilToInt => {
                        let intr = if matches!(op, FloatOp::FloorToInt) {
                            FloatIntrinsic::Floor
                        } else {
                            FloatIntrinsic::Ceil
                        };
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_intrinsic(b, d, intr, &fa));
                        let r = self.dst(|i, b, d| i.fptosi_sat(b, d, &ff));
                        self.int_of_long(&r)
                    }
                    // Exact float -> float: a hardware intrinsic, identical on
                    // every IEEE-754 platform.
                    FloatOp::AbsFloat
                    | FloatOp::Sqrt
                    | FloatOp::Floor
                    | FloatOp::Ceil
                    | FloatOp::Round
                    | FloatOp::Trunc => {
                        let intr = match op {
                            FloatOp::AbsFloat => FloatIntrinsic::Fabs,
                            FloatOp::Sqrt => FloatIntrinsic::Sqrt,
                            FloatOp::Floor => FloatIntrinsic::Floor,
                            FloatOp::Ceil => FloatIntrinsic::Ceil,
                            FloatOp::Round => FloatIntrinsic::Round,
                            _ => FloatIntrinsic::Trunc,
                        };
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_intrinsic(b, d, intr, &fa));
                        self.f_out(&ff)
                    }
                    // Transcendental: a call into the owned vendored libm, the same
                    // `prism_m_*` symbol the interpreter FFIs, so the two agree bit
                    // for bit. `runtime_sym` returns `Some` for exactly this class.
                    _ => {
                        let sym = op
                            .runtime_sym()
                            .expect("ICE: non-transcendental FloatOp reached the runtime-call arm");
                        self.used_fcall.insert(sym.to_string());
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_call1(b, d, sym, &fa));
                        self.f_out(&ff)
                    }
                };
                self.rc_dec(&a);
                Ok(out)
            }
            // Genuine unary negation. The float lane is a real `fneg` (sign-bit
            // flip, preserves signed zero, matches the interpreter's `-f` bit for
            // bit). The integer lanes reuse the existing subtract-from-zero
            // lowering: this is a machine-level detail only. The Core node stays a
            // `Neg`, so the content hash and the `Num` negate method never see a `0 - x`.
            Comp::Neg(NegLane::Float, v) => {
                let a = self.value(regs, v)?;
                let fa = self.f_in(&a);
                let rf = self.dst(|i, b, d| i.fneg(b, d, &fa));
                let out = self.f_out(&rf);
                self.rc_dec(&a);
                Ok(out)
            }
            Comp::Neg(NegLane::Int, v) => {
                self.lower(regs, &Comp::Prim(CoreOp::Sub, Value::Int(0), v.clone()))
            }
            Comp::Neg(NegLane::I64, v) => self.lower(
                regs,
                &Comp::StrBuiltin(Builtin::I64Sub, vec![Value::I64(0), v.clone()]),
            ),
            Comp::UnboxedProject(_, _) => Err(
                "codegen: unboxed record projection is not implemented for the native ABI".into(),
            ),
            Comp::Do(op, _) => Err(format!(
                "effect `{op}` reached codegen unlowered: it is performed outside any lexical \
                 `handle`, which the local free-monad lowering cannot translate. Perform it \
                 inside a `handle` in the same function."
            )),
            Comp::Handle { .. } => Err(
                "`handle` reached codegen unlowered: effect lowering must run before emission \
                 (see core::lower_effects)"
                    .into(),
            ),
            Comp::Mask(..) => Err(
                "`mask` reached codegen unlowered: effect lowering must run before emission \
                 (see core::lower_effects)"
                    .into(),
            ),
            Comp::StrBuiltin(b, args) => {
                if b.native_deferred() {
                    return Err(format!(
                        "{}: the content-addressed store bridge is interpreter-only; \
                         the native runtime has no C symbol for it yet",
                        b.name()
                    ));
                }
                let sym = b.sym();
                if !matches!(builtin(b.name()), Some((_, BuiltinKind::Str))) {
                    self.used_rt.insert(sym.clone(), args.len());
                }
                let abi = b.abi();
                let mut avs = Vec::new();
                let mut owned = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let v = self.value(regs, a)?;
                    avs.push(match abi.arg(i) {
                        AbiArg::Immediate => self.untag(&v),
                        AbiArg::BoxedFloat => self.unbox(&v),
                        AbiArg::Raw => v.clone(),
                    });
                    owned.push(v);
                }
                let t = self.dst(|i, b, d| i.call(b, d, &sym, &avs));
                let out = match abi.result() {
                    AbiResult::Raw => t,
                    AbiResult::RetagImmediate => self.retag(&t),
                };
                for v in owned {
                    self.rc_dec(&v);
                }
                Ok(out)
            }
            Comp::Dup(v) => {
                let r = self.value(regs, v)?;
                self.isa.call_void(&mut self.b, rt::RC_INC, &[r]);
                Ok(self.isa.fresh_zero(&mut self.b))
            }
            Comp::Drop(v) => {
                let r = self.value(regs, v)?;
                self.isa.call_void(&mut self.b, rt::RC_DEC, &[r]);
                Ok(self.isa.fresh_zero(&mut self.b))
            }
            Comp::WithReuse { token, freed, body } => {
                let r = self.value(regs, freed)?;
                let t = self.dst(|i, b, d| i.call(b, d, rt::REUSE_TOKEN, slice::from_ref(&r)));
                let mut r2 = regs.clone();
                r2.insert(*token, t);
                self.lower(&r2, body)
            }
            Comp::Reuse(tok, ctor) => {
                let t = self.value(regs, &Value::Var(*tok))?;
                let (tag, fields) = match ctor {
                    Value::Ctor(_, tg, fs) => (idx64(*tg), fs),
                    Value::Tuple(fs) => (0, fs),
                    _ => return Err("reuse: non-constructor value".into()),
                };
                let fvs = self.values(regs, fields)?;
                Ok(self.reuse_obj(&t, tag, &fvs))
            }
            // Mutable-cell ops for an erased `var`. The cell flows as an ordinary
            // owned value; `value` returns the dup'd reference the rc pass gave
            // this use, which read/write consume (rc_dec the cell after). The
            // stored/initial value moves into the cell, so it is not dropped here.
            Comp::RefNew(v) => {
                let r = self.value(regs, v)?;
                Ok(self.dst(|i, b, d| i.call(b, d, rt::REF_NEW, slice::from_ref(&r))))
            }
            Comp::RefGet(c) => {
                let cv = self.value(regs, c)?;
                let r = self.dst(|i, b, d| i.call(b, d, rt::REF_GET, slice::from_ref(&cv)));
                self.rc_dec(&cv);
                Ok(r)
            }
            Comp::RefSet(c, v) => {
                let cv = self.value(regs, c)?;
                let rv = self.value(regs, v)?;
                self.isa
                    .call_void(&mut self.b, rt::REF_SET, &[cv.clone(), rv]);
                self.rc_dec(&cv);
                Ok(self.isa.fresh_zero(&mut self.b))
            }
        }
    }

    fn lower_tail(&mut self, regs: &Regs, c: &Comp) -> Result<(), String> {
        match c {
            Comp::Bind(m, x, n) => {
                if let Comp::Call(g, args) = m.as_ref() {
                    if let Some(t) = self.trmc.as_ref() {
                        if *g == t.name && args.len() == t.arity {
                            if let Some(shape) = trmc_shape(n, x.as_str()) {
                                let t = t.clone();
                                return self.trmc_step(regs, args, &shape, &t);
                            }
                        }
                    }
                }
                let r = self.lower(regs, m)?;
                let mut r2 = regs.clone();
                r2.insert(*x, r);
                self.lower_tail(&r2, n)
            }
            Comp::If(v, t, e) => self.lower_if(regs, v, t, e, true).map(|_| ()),
            Comp::Case(val, arms) => self.lower_case(regs, val, arms, true).map(|_| ()),
            // Free the cell into a token, bind it, then lower the body in tail
            // position so a `Reuse`-shaped TRMC tail inside it still loops. Same
            // instruction sequence the threaded `bind (reuse_token ..)` emitted.
            Comp::WithReuse { token, freed, body } => {
                let r = self.value(regs, freed)?;
                let t = self.dst(|i, b, d| i.call(b, d, rt::REUSE_TOKEN, slice::from_ref(&r)));
                let mut r2 = regs.clone();
                r2.insert(*token, t);
                self.lower_tail(&r2, body)
            }
            Comp::Call(name, args) => {
                if let Some(t) = self.trmc.clone() {
                    if *name == t.name && args.len() == t.arity {
                        let mut avs = self.values(regs, args)?;
                        avs.push(t.extra.clone());
                        let r = self.dst(|i, b, d| i.musttail_call(b, d, &t.sym, &avs));
                        self.isa.ret(&mut self.b, &r);
                    } else {
                        let r = self.lower(regs, c)?;
                        self.trmc_finish(&r, &t);
                    }
                    return Ok(());
                }
                let arity = self.fn_arity(name.as_str())?;
                if args.len() == arity && arity == self.cur_arity {
                    let avs: Vec<String> = args
                        .iter()
                        .map(|a| self.value(regs, a))
                        .collect::<Result<_, _>>()?;
                    let f = Self::sym(name.as_str());
                    let t = self.dst(|i, b, d| i.musttail_call(b, d, &f, &avs));
                    self.isa.ret(&mut self.b, &t);
                } else {
                    let r = self.lower(regs, c)?;
                    self.isa.ret(&mut self.b, &r);
                }
                Ok(())
            }
            _ => {
                let r = self.lower(regs, c)?;
                match self.trmc.clone() {
                    Some(t) => self.trmc_finish(&r, &t),
                    None => self.isa.ret(&mut self.b, &r),
                }
                Ok(())
            }
        }
    }

    fn trmc_finish(&mut self, r: &str, t: &TrmcCtx) {
        match t.mode {
            TrmcMode::Hole => {
                let p = self.dst(|i, b, d| i.inttoptr(b, d, &t.extra));
                self.isa.store(&mut self.b, r, &p);
                self.isa.ret(&mut self.b, r);
            }
            TrmcMode::Acc => {
                let s = self.prim(CoreOp::Add, r, &t.extra);
                self.rc_dec(r);
                self.rc_dec(&t.extra);
                self.isa.ret(&mut self.b, &s);
            }
        }
    }

    fn trmc_step(
        &mut self,
        regs: &Regs,
        args: &[Value],
        shape: &TrmcShape<'_>,
        t: &TrmcCtx,
    ) -> Result<(), String> {
        let mut avs = self.values(regs, args)?;
        match shape {
            TrmcShape::Acc(other) => {
                let c = self.value(regs, other)?;
                let acc2 = self.prim(CoreOp::Add, &t.extra, &c);
                self.rc_dec(&t.extra);
                self.rc_dec(&c);
                avs.push(acc2);
            }
            TrmcShape::Ctor {
                token,
                tag,
                fields,
                hole,
            } => {
                let mut fvs = Vec::new();
                for (i, fval) in fields.iter().enumerate() {
                    fvs.push(if i == *hole {
                        self.isa.const_int(&mut self.b, 0)
                    } else {
                        self.value(regs, fval)?
                    });
                }
                let n = self.isa.const_int(&mut self.b, idx64(fields.len()));
                let ptr = match token {
                    Some(tok) => {
                        let tr = regs
                            .get(tok)
                            .cloned()
                            .ok_or_else(|| format!("codegen: unbound {tok}"))?;
                        let cargs = [tr, n];
                        self.dst(|i, b, d| i.call_ptr(b, d, rt::REUSE_ALLOC, &cargs))
                    }
                    None => self.dst(|i, b, d| i.call_ptr(b, d, rt::ALLOC, slice::from_ref(&n))),
                };
                let cell = self.fill_obj(&ptr, *tag, &fvs);
                let off = HDR_BYTES + idx64(*hole) * WORD_BYTES;
                let hp = self.dst(|i, b, d| i.gep(b, d, &ptr, off));
                let hole_int = self.dst(|i, b, d| i.ptrtoint(b, d, &hp));
                let parent = self.dst(|i, b, d| i.inttoptr(b, d, &t.extra));
                self.isa.store(&mut self.b, &cell, &parent);
                avs.push(hole_int);
            }
        }
        let r = self.dst(|i, b, d| i.musttail_call(b, d, &t.sym, &avs));
        self.isa.ret(&mut self.b, &r);
        Ok(())
    }

    fn lower_if(
        &mut self,
        regs: &Regs,
        v: &Value,
        t: &Comp,
        e: &Comp,
        tail: bool,
    ) -> Result<String, String> {
        let vc = self.value(regs, v)?;
        let one = self.isa.const_int(&mut self.b, 1);
        let c = self.dst(|i, b, d| i.icmp(b, d, Cmp::Ne, &vc, &one));
        let lt = self.b.label();
        let le = self.b.label();
        if tail {
            self.isa.cond_br(&mut self.b, &c, &lt, &le);
            self.isa.open_block(&mut self.b, &lt);
            self.lower_tail(regs, t)?;
            self.isa.open_block(&mut self.b, &le);
            self.lower_tail(regs, e)?;
            return Ok(String::new());
        }
        let lm = self.b.label();
        self.isa.cond_br(&mut self.b, &c, &lt, &le);
        self.isa.open_block(&mut self.b, &lt);
        let rt = self.lower(regs, t)?;
        let pt = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &lm, &rt);
        self.isa.open_block(&mut self.b, &le);
        let re = self.lower(regs, e)?;
        let pe = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &lm, &re);
        let r = self.b.tmp();
        self.isa
            .open_merge(&mut self.b, &lm, &r, &[(rt, pt), (re, pe)]);
        Ok(r)
    }

    fn lower_case(
        &mut self,
        regs: &Regs,
        val: &Value,
        arms: &[(CorePat, Comp)],
        tail: bool,
    ) -> Result<String, String> {
        let ptr_int = self.value(regs, val)?;
        let ptr = self.dst(|i, b, d| i.inttoptr(b, d, &ptr_int));

        let needs_tag = arms.iter().any(|(p, _)| matches!(p, CorePat::Ctor(..)));
        let tag = if needs_tag {
            let tag_ptr = self.dst(|i, b, d| i.gep(b, d, &ptr, TAG_OFF));
            Some(self.dst(|i, b, d| i.load(b, d, &tag_ptr)))
        } else {
            None
        };

        let merge_lbl = self.b.label();
        let default_lbl = self.b.label();
        let arm_lbls: Vec<String> = arms.iter().map(|_| self.b.label()).collect();

        let wild_idx = arms
            .iter()
            .position(|(p, _)| matches!(p, CorePat::Wild | CorePat::Var(_)));

        if let Some(t) = &tag {
            let mut cases: Vec<(i64, String)> = Vec::new();
            for (i, (pat, _)) in arms.iter().enumerate() {
                if let CorePat::Ctor(name, _) = pat {
                    if let Some(tag) = ctor_tag(self.ctors, name.as_str()) {
                        cases.push((idx64(tag), arm_lbls[i].clone()));
                    }
                }
            }
            self.isa.switch(&mut self.b, t, &default_lbl, &cases);
        } else {
            // No tag dispatch: every arm is tuple/var/wild and irrefutable, so
            // first-match order means the first arm wins.
            self.isa.jump(&mut self.b, &arm_lbls[0]);
        }

        self.isa.open_block(&mut self.b, &default_lbl);
        if let Some(idx) = wild_idx {
            self.isa.jump(&mut self.b, &arm_lbls[idx]);
        } else {
            // Exhaustiveness proves this dead for well-typed code; a compiler bug
            // that slips an uncovered tag here aborts with a diagnostic (matching
            // the interpreter's clean error) rather than executing raw-UB
            // `unreachable`, mirroring the apply-arity trap.
            self.isa.call_void(&mut self.b, rt::MATCH_ERROR, &[]);
            self.isa.unreachable(&mut self.b);
        }

        let mut phis: Vec<(String, String)> = vec![];
        for (arm_idx, (pat, body)) in arms.iter().enumerate() {
            self.isa.open_block(&mut self.b, &arm_lbls[arm_idx]);
            let mut arm_regs = regs.clone();
            match pat {
                CorePat::Ctor(_, fields) | CorePat::Tuple(fields) => {
                    for (fi, sub) in fields.iter().enumerate() {
                        if let Some(vname) = sub {
                            let off = HDR_BYTES + idx64(fi) * WORD_BYTES;
                            let fp = self.dst(|i, b, d| i.gep(b, d, &ptr, off));
                            let fv = self.dst(|i, b, d| i.load(b, d, &fp));
                            arm_regs.insert(*vname, fv);
                        }
                    }
                }
                CorePat::Var(vname) => {
                    arm_regs.insert(*vname, ptr_int.clone());
                }
                CorePat::Wild => {}
            }
            if tail {
                self.lower_tail(&arm_regs, body)?;
            } else {
                let r = self.lower(&arm_regs, body)?;
                let cur = self.b.cur.clone();
                self.isa.jump_merge(&mut self.b, &merge_lbl, &r);
                phis.push((r, cur));
            }
        }

        if tail {
            return Ok(String::new());
        }
        let result = self.b.tmp();
        self.isa.open_merge(&mut self.b, &merge_lbl, &result, &phis);
        Ok(result)
    }

    // Exhaustive over `CoreOp`: adding a primitive is a compile error here rather
    // than a silently mis-lowered op. The int add/sub and comparison lanes share
    // the immediate fast-path scaffold (`both_imm` then `fast`/`slow`/`merge`).
    fn prim(&mut self, op: CoreOp, a: &str, b: &str) -> String {
        match op {
            CoreOp::Addf | CoreOp::Subf | CoreOp::Mulf | CoreOp::Divf => {
                let fa = self.f_in(a);
                let fb = self.f_in(b);
                let instr = match op {
                    CoreOp::Addf => FloatBinOp::Fadd,
                    CoreOp::Subf => FloatBinOp::Fsub,
                    CoreOp::Mulf => FloatBinOp::Fmul,
                    _ => FloatBinOp::Fdiv,
                };
                let rf = self.dst(|i, bf, d| i.fbin(bf, d, instr, &fa, &fb));
                self.f_out(&rf)
            }
            CoreOp::Eqf | CoreOp::Nef | CoreOp::Ltf | CoreOp::Lef | CoreOp::Gtf | CoreOp::Gef => {
                let fa = self.f_in(a);
                let fb = self.f_in(b);
                let pred = match op {
                    CoreOp::Eqf => Cmp::Eq,
                    CoreOp::Nef => Cmp::Ne,
                    CoreOp::Ltf => Cmp::Lt,
                    CoreOp::Lef => Cmp::Le,
                    CoreOp::Gtf => Cmp::Gt,
                    _ => Cmp::Ge,
                };
                let c = self.dst(|i, bf, d| i.fcmp(bf, d, pred, &fa, &fb));
                let z = self.dst(|i, bf, d| i.zext(bf, d, &c));
                self.retag(&z)
            }
            CoreOp::Mul | CoreOp::Div | CoreOp::Rem => {
                let sym = match op {
                    CoreOp::Mul => rt::INT_MUL,
                    CoreOp::Div => rt::INT_DIV,
                    _ => rt::INT_REM,
                };
                self.used_rt.insert(sym.into(), 2);
                let args = [a.to_string(), b.to_string()];
                self.dst(|i, bf, d| i.call(bf, d, sym, &args))
            }
            CoreOp::Add | CoreOp::Sub => self.prim_addsub(op, a, b),
            CoreOp::Eq | CoreOp::Ne | CoreOp::Lt | CoreOp::Le | CoreOp::Gt | CoreOp::Ge => {
                self.prim_icmp(op, a, b)
            }
        }
    }

    fn prim_addsub(&mut self, op: CoreOp, a: &str, b: &str) -> String {
        let cond = self.both_imm(a, b);
        let fast = self.b.label();
        let slow = self.b.label();
        let merge = self.b.label();
        let (instr, sym) = if op == CoreOp::Add {
            (IntOp::Add, rt::INT_ADD)
        } else {
            (IntOp::Sub, rt::INT_SUB)
        };
        self.used_rt.insert(sym.into(), 2);
        let fastok = self.b.label();
        self.isa.cond_br(&mut self.b, &cond, &fast, &slow);
        self.isa.open_block(&mut self.b, &fast);
        let ua = self.untag(a);
        let ub = self.untag(b);
        let r = self.dst(|i, bf, d| i.bin(bf, d, instr, &ua, &ub));
        let one = self.isa.const_int(&mut self.b, 1);
        let s = self.dst(|i, bf, d| i.bin(bf, d, IntOp::Shl, &r, &one));
        let back = self.dst(|i, bf, d| i.bin(bf, d, IntOp::Ashr, &s, &one));
        let fit = self.dst(|i, bf, d| i.icmp(bf, d, Cmp::Eq, &back, &r));
        self.isa.cond_br(&mut self.b, &fit, &fastok, &slow);
        self.isa.open_block(&mut self.b, &fastok);
        let rf = self.dst(|i, bf, d| i.bin(bf, d, IntOp::Or, &s, &one));
        let pf = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &merge, &rf);
        self.isa.open_block(&mut self.b, &slow);
        let args = [a.to_string(), b.to_string()];
        let rs = self.dst(|i, bf, d| i.call(bf, d, sym, &args));
        let ps = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &merge, &rs);
        let out = self.b.tmp();
        self.isa
            .open_merge(&mut self.b, &merge, &out, &[(rf, pf), (rs, ps)]);
        out
    }

    fn prim_icmp(&mut self, op: CoreOp, a: &str, b: &str) -> String {
        let cond = self.both_imm(a, b);
        let fast = self.b.label();
        let slow = self.b.label();
        let merge = self.b.label();
        let pred = match op {
            CoreOp::Eq => Cmp::Eq,
            CoreOp::Ne => Cmp::Ne,
            CoreOp::Lt => Cmp::Lt,
            CoreOp::Le => Cmp::Le,
            CoreOp::Gt => Cmp::Gt,
            _ => Cmp::Ge,
        };
        // Tagging is order-preserving, so immediates compare as tagged words.
        self.used_rt.insert(rt::INT_CMP.into(), 2);
        self.isa.cond_br(&mut self.b, &cond, &fast, &slow);
        self.isa.open_block(&mut self.b, &fast);
        let c1 = self.dst(|i, bf, d| i.icmp(bf, d, pred, a, b));
        let z1 = self.dst(|i, bf, d| i.zext(bf, d, &c1));
        let rf = self.retag(&z1);
        let pf = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &merge, &rf);
        self.isa.open_block(&mut self.b, &slow);
        let args = [a.to_string(), b.to_string()];
        let c = self.dst(|i, bf, d| i.call(bf, d, rt::INT_CMP, &args));
        let zero = self.isa.const_int(&mut self.b, 0);
        let c2 = self.dst(|i, bf, d| i.icmp(bf, d, pred, &c, &zero));
        let z2 = self.dst(|i, bf, d| i.zext(bf, d, &c2));
        let rs = self.retag(&z2);
        let ps = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &merge, &rs);
        let out = self.b.tmp();
        self.isa
            .open_merge(&mut self.b, &merge, &out, &[(rf, pf), (rs, ps)]);
        out
    }

    fn both_imm(&mut self, a: &str, b: &str) -> String {
        let t = self.dst(|i, bf, d| i.bin(bf, d, IntOp::And, a, b));
        let one = self.isa.const_int(&mut self.b, 1);
        let bit = self.dst(|i, bf, d| i.bin(bf, d, IntOp::And, &t, &one));
        self.dst(|i, bf, d| i.icmp(bf, d, Cmp::Eq, &bit, &one))
    }

    // Bind each function parameter to its `%a{i}` SSA register and return the
    // ordered list of register names for the function header.
    fn bind_a_params(regs: &mut Regs, params: &[Sym]) -> Vec<String> {
        params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let r = format!("%a{i}");
                regs.insert(*p, r.clone());
                r
            })
            .collect()
    }

    fn function(&mut self, f: &CoreFn) -> Result<String, String> {
        self.current_owner = Some(f.name);
        let body = reassoc(&f.body);
        if let Some(mode) = trmc_mode(f.name.as_str(), f.params.len(), &body) {
            return self.trmc_function(f, &body, mode);
        }
        self.b.reset();
        let mut regs = Regs::new();
        let params = Self::bind_a_params(&mut regs, &f.params);
        self.cur_arity = f.params.len();
        let header = self.isa.fn_define(&Self::sym(f.name.as_str()), &params);
        self.isa.open_entry(&mut self.b);
        // Count one driver work-step per entry to a free-monad driver (stderr-only
        // under PRISM_DRIVE_STATS, so stdout is untouched). This is the counter
        // whose asymptotics track the trampoline's actual work.
        if is_free_monad_driver(f.name.as_str()) {
            self.isa.call_void(&mut self.b, rt::DRIVE_STEP, &[]);
        }
        self.lower_tail(&regs, &body)?;
        Ok(format!("{header}{}{}", self.b.body, self.isa.fn_close()))
    }

    // `.` cannot occur in a source identifier, so the helper symbol is
    // unforgeable. Both LLVM and MLIR accept it unquoted.
    fn trmc_function(&mut self, f: &CoreFn, body: &Comp, mode: TrmcMode) -> Result<String, String> {
        let sym = format!("{}.trmc", Self::sym(f.name.as_str()));
        self.b.reset();
        let mut regs = Regs::new();
        let mut params = Self::bind_a_params(&mut regs, &f.params);
        let extra = format!("%a{}", f.params.len());
        params.push(extra.clone());
        self.cur_arity = params.len();
        self.trmc = Some(TrmcCtx {
            name: f.name,
            sym: sym.clone(),
            arity: f.params.len(),
            mode,
            extra,
        });
        let header = self.isa.fn_define(&sym, &params);
        self.isa.open_entry(&mut self.b);
        let lowered = self.lower_tail(&regs, body);
        self.trmc = None;
        lowered?;
        let helper = format!("{header}{}{}", self.b.body, self.isa.fn_close());

        self.b.reset();
        let params: Vec<String> = (0..f.params.len()).map(|i| format!("%a{i}")).collect();
        let header = self.isa.fn_define(&Self::sym(f.name.as_str()), &params);
        self.isa.open_entry(&mut self.b);
        let mut args = params;
        match mode {
            TrmcMode::Hole => {
                let slot = self.dst(Isa::alloca_word);
                let si = self.dst(|i, b, d| i.ptrtoint(b, d, &slot));
                args.push(si);
                let _ = self.dst(|i, b, d| i.call(b, d, &sym, &args));
                let r = self.dst(|i, b, d| i.load(b, d, &slot));
                self.isa.ret(&mut self.b, &r);
            }
            TrmcMode::Acc => {
                args.push(self.isa.const_int(&mut self.b, 1));
                let r = self.dst(|i, b, d| i.call(b, d, &sym, &args));
                self.isa.ret(&mut self.b, &r);
            }
        }
        Ok(format!(
            "{helper}\n{header}{}{}",
            self.b.body,
            self.isa.fn_close()
        ))
    }

    fn lam_fn(&mut self, idx: usize) -> Result<String, String> {
        self.current_owner = Some(self.lams[idx].owner);
        let tag = self.lams[idx].tag;
        let params = self.lams[idx].params.clone();
        let free_vars = self.lams[idx].free_vars.clone();
        let body = self.lams[idx].body.clone();

        self.b.reset();
        let mut regs = Regs::new();
        let mut all_params = Vec::new();
        for (i, fv) in free_vars.iter().enumerate() {
            let r = format!("%_fv{i}");
            regs.insert(*fv, r.clone());
            all_params.push(r);
        }
        for (i, p) in params.iter().enumerate() {
            let r = format!("%{}", crate::names::generated_param(i));
            regs.insert(*p, r.clone());
            all_params.push(r);
        }

        self.cur_arity = all_params.len();
        let header = self.isa.fn_define(&format!("prism_lam_{tag}"), &all_params);
        self.isa.open_entry(&mut self.b);
        match body {
            LamBody::Core(c) => self.lower_tail(&regs, &c)?,
            LamBody::Curry { target } => {
                // Captured fields (target fvs ++ already-supplied args) are owned
                // by this adapter's closure, which its caller drops after the
                // call, so dup each before forwarding into the consuming target
                // call. The remaining params arrived owned and forward as-is.
                let captured = free_vars.len();
                for r in all_params.iter().take(captured) {
                    self.isa
                        .call_void(&mut self.b, rt::RC_INC, slice::from_ref(r));
                }
                let target_tag = self.lams[target].tag;
                let r = self.dst(|i, b, d| {
                    i.call(b, d, &format!("prism_lam_{target_tag}"), &all_params);
                });
                self.isa.ret(&mut self.b, &r);
            }
        }
        Ok(format!("{header}{}{}", self.b.body, self.isa.fn_close()))
    }
}

pub(super) enum SelectedEmissionError {
    Codegen(String),
}

impl From<String> for SelectedEmissionError {
    fn from(error: String) -> Self {
        Self::Codegen(error)
    }
}

/// Lowers fully prepared Core through an external instruction backend.
///
/// The shared walker owns evaluation order, representation, reference counting,
/// and tail-call lowering. The [`Isa`] implementation only spells instructions.
///
/// # Errors
/// Returns a diagnostic when the lowered Core violates a code-generation
/// invariant or the backend cannot emit a required construct.
pub fn emit_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<String, String> {
    emit_with_isa_selection(isa, core, ctors, None, true).map_err(|error| match error {
        SelectedEmissionError::Codegen(error) => error,
    })
}

/// Lower a selected set of top-level definitions while retaining the complete
/// program arity table for cross-SCC calls. This boundary is intentionally
/// limited to definitions that do not mint closures or indirect-call
/// dispatchers; those require the whole-program closure-tag plan.
///
/// # Errors
/// Returns a diagnostic when selection is empty, a selected definition is not
/// independently emit-able, or ordinary code generation fails.
pub(super) fn emit_selected_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    selected: &BTreeSet<Sym>,
) -> Result<String, SelectedEmissionError> {
    if selected.is_empty() {
        return Err(SelectedEmissionError::Codegen(
            "ICE: empty backend SCC selection".to_string(),
        ));
    }
    emit_with_isa_selection(isa, core, ctors, Some(selected), false)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ClosureSummary {
    lams: Vec<ClosureShape>,
    used_apply: BTreeSet<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ClosureShape {
    tag: usize,
    owner: String,
    params: usize,
    free_vars: usize,
}

impl ClosureSummary {
    pub(crate) fn validate(&self) -> bool {
        let mut tags = BTreeSet::new();
        let mut owner_counts = BTreeMap::<&str, usize>::new();
        for lambda in &self.lams {
            if !tags.insert(lambda.tag) {
                return false;
            }
            *owner_counts.entry(&lambda.owner).or_default() += 1;
        }
        owner_counts.into_iter().all(|(owner, count)| {
            let owner = Sym::new(owner);
            (0..count).all(|ordinal| tags.contains(&closure_tag(owner, ordinal)))
        })
    }
}

#[derive(Clone)]
pub(super) struct ClosurePlan {
    lams: Vec<LamInfo>,
    adapters: BTreeMap<(usize, usize), usize>,
    used_apply: BTreeSet<usize>,
    ordinary_lams: usize,
}

impl ClosurePlan {
    pub(super) fn fingerprint(&self) -> String {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"prism-closure-plan-v2");
        for lambda in &self.lams {
            hasher.update(&lambda.tag.to_le_bytes());
            hasher.update(lambda.owner.as_str().as_bytes());
            hasher.update(&lambda.params.len().to_le_bytes());
            hasher.update(&lambda.free_vars.len().to_le_bytes());
            match &lambda.body {
                LamBody::Core(_) => {
                    hasher.update(b"core");
                }
                LamBody::Curry { target } => {
                    hasher.update(b"curry");
                    hasher.update(&self.lams[*target].tag.to_le_bytes());
                }
            }
        }
        for arity in &self.used_apply {
            hasher.update(&arity.to_le_bytes());
        }
        hasher.finalize().to_hex().to_string()
    }

    pub(super) fn dispatch_arities(&self) -> BTreeSet<usize> {
        let mut arities = self
            .lams
            .iter()
            .map(|lambda| lambda.params.len())
            .collect::<BTreeSet<_>>();
        arities.extend(self.used_apply.iter().copied());
        arities
    }

    pub(super) const fn has_adapters(&self) -> bool {
        self.ordinary_lams < self.lams.len()
    }
}

pub(super) fn closure_summary_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    selected: &BTreeSet<Sym>,
) -> Result<ClosureSummary, String> {
    let live = reachable_fns(core);
    let fn_arities = core
        .fns
        .iter()
        .map(|function| (function.name.to_string(), function.params.len()))
        .collect();
    let mut cg = Cg::new(isa, ctors, fn_arities);
    for function in &core.fns {
        if live.contains(&function.name) && selected.contains(&function.name) {
            let _ = cg.function(function)?;
        }
    }
    let mut index = 0;
    while index < cg.lams.len() {
        let _ = cg.lam_fn(index)?;
        index += 1;
    }
    let summary = ClosureSummary {
        lams: cg
            .lams
            .into_iter()
            .map(|lambda| ClosureShape {
                tag: lambda.tag,
                owner: lambda.owner.to_string(),
                params: lambda.params.len(),
                free_vars: lambda.free_vars.len(),
            })
            .collect(),
        used_apply: cg.used_apply,
    };
    if summary.validate() {
        Ok(summary)
    } else {
        Err("ICE: invalid SCC closure summary".to_string())
    }
}

pub(super) fn plan_closures_from_summaries_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    summaries: &[ClosureSummary],
) -> Result<ClosurePlan, String> {
    if !summaries.iter().all(ClosureSummary::validate) {
        return Err("ICE: invalid SCC closure summary".to_string());
    }
    let fn_arities = core
        .fns
        .iter()
        .map(|function| (function.name.to_string(), function.params.len()))
        .collect();
    let mut cg = Cg::new(isa, ctors, fn_arities);
    for summary in summaries {
        cg.used_apply.extend(summary.used_apply.iter().copied());
        for lambda in &summary.lams {
            let owner = Sym::new(&lambda.owner);
            let params = (0..lambda.params)
                .map(|index| Sym::new(&generated_param(index)))
                .collect();
            let free_vars = (0..lambda.free_vars)
                .map(|index| Sym::new(&closure_cap(index)))
                .collect();
            cg.lams.push(LamInfo {
                tag: lambda.tag,
                owner,
                params,
                free_vars,
                body: LamBody::Core(Comp::Return(Value::Unit)),
            });
            *cg.owner_ordinals.entry(owner).or_default() += 1;
            if !cg.used_closure_tags.insert(lambda.tag) {
                return Err("ICE: closure tag collision across SCC summaries".to_string());
            }
        }
    }
    cg.lams.sort_by_key(|lambda| lambda.tag);
    let ordinary_lams = cg.lams.len();
    loop {
        let before = (cg.lams.len(), cg.used_apply.len());
        for arity in cg.apply_arities() {
            cg.plan_dispatch(arity);
        }
        if (cg.lams.len(), cg.used_apply.len()) == before {
            break;
        }
    }
    Ok(ClosurePlan {
        lams: cg.lams,
        adapters: cg.adapters,
        used_apply: cg.used_apply,
        ordinary_lams,
    })
}

pub(super) fn plan_closures_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<ClosurePlan, String> {
    let selected = core
        .fns
        .iter()
        .map(|function| function.name)
        .collect::<BTreeSet<_>>();
    let summary = closure_summary_with_isa(isa, core, ctors, &selected)?;
    plan_closures_from_summaries_with_isa(isa, core, ctors, &[summary])
}

fn cg_from_closure_plan<'a, I: Isa>(
    isa: &'a I,
    core: &Core,
    ctors: &'a BTreeMap<String, CtorInfo>,
    plan: &ClosurePlan,
) -> Cg<'a, I> {
    let fn_arities = core
        .fns
        .iter()
        .map(|function| (function.name.to_string(), function.params.len()))
        .collect();
    let mut cg = Cg::new(isa, ctors, fn_arities);
    cg.lams.clone_from(&plan.lams);
    cg.adapters.clone_from(&plan.adapters);
    cg.used_apply.clone_from(&plan.used_apply);
    cg.used_closure_tags = cg.lams.iter().map(|lambda| lambda.tag).collect();
    cg
}

pub(super) fn emit_closure_adapters_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    plan: &ClosurePlan,
) -> Result<String, String> {
    let mut cg = cg_from_closure_plan(isa, core, ctors, plan);
    let mut bodies = String::new();
    for index in plan.ordinary_lams..cg.lams.len() {
        bodies.push_str(&cg.lam_fn(index)?);
        bodies.push('\n');
    }
    Ok(finish_module(isa, &cg, &bodies, ""))
}

pub(super) fn emit_closure_dispatch_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    plan: &ClosurePlan,
    arity: usize,
) -> String {
    let mut cg = cg_from_closure_plan(isa, core, ctors, plan);
    let dispatch = cg.apply_dispatch(arity);
    finish_module(isa, &cg, "", &dispatch)
}

pub(super) fn emit_selected_plan_with_isa<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    selected: &BTreeSet<Sym>,
) -> Result<String, String> {
    if selected.is_empty() {
        return Err("ICE: empty backend global-plan selection".to_string());
    }
    emit_with_isa_selection(isa, core, ctors, Some(selected), true).map_err(|error| match error {
        SelectedEmissionError::Codegen(error) => error,
    })
}

fn emit_with_isa_selection<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    selected: Option<&BTreeSet<Sym>>,
    owns_closure_plan: bool,
) -> Result<String, SelectedEmissionError> {
    let live = reachable_fns(core);
    let fn_arities: BTreeMap<String, usize> = core
        .fns
        .iter()
        .map(|f| (f.name.to_string(), f.params.len()))
        .collect();
    let mut fn_bodies = String::new();
    let mut cg = Cg::new(isa, ctors, fn_arities);

    for f in &core.fns {
        if live.contains(&f.name) && selected.is_none_or(|members| members.contains(&f.name)) {
            fn_bodies.push_str(&cg.function(f)?);
            fn_bodies.push('\n');
        }
    }

    // Emit every ordinary closure body first. Lowering a body can discover
    // nested closures (`alloc_closure`), so re-check the length until it drains;
    // only then are all `Core` lambdas (and every `App` arity in `used_apply`)
    // known.
    let mut lam_idx = 0;
    while lam_idx < cg.lams.len() {
        fn_bodies.push_str(&cg.lam_fn(lam_idx)?);
        fn_bodies.push('\n');
        lam_idx += 1;
    }

    if !owns_closure_plan {
        return Ok(finish_module(isa, &cg, &fn_bodies, ""));
    }

    // Stable closure tags, rather than traversal position, define the global
    // dispatcher order. This makes folding independently discovered SCC
    // summaries byte-identical to whole-program planning.
    cg.lams.sort_by_key(|lambda| lambda.tag);

    // Plan every curry adapter and follow-on apply arity to a fixpoint. This runs
    // against the complete closure set, and adapter (`Curry`) bodies mint no
    // further closures, so the adapters emitted just below are the last lambdas
    // added. Each round strictly shrinks adapter arity (n == 0 mints nothing), so
    // the fixpoint terminates.
    loop {
        let before = (cg.lams.len(), cg.used_apply.len());
        for n in cg.apply_arities() {
            cg.plan_dispatch(n);
        }
        if (cg.lams.len(), cg.used_apply.len()) == before {
            break;
        }
    }

    // Emit the curry-adapter bodies planned above (the lambdas appended since the
    // closure loop drained).
    while lam_idx < cg.lams.len() {
        fn_bodies.push_str(&cg.lam_fn(lam_idx)?);
        fn_bodies.push('\n');
        lam_idx += 1;
    }

    // Every lambda arity needs a dispatcher, as does every arity an `App` calls,
    // even with no matching lambda (a 0-arg apply on a dead path still has to
    // resolve as a symbol).
    let mut dispatch = String::new();
    for n in cg.apply_arities() {
        dispatch.push_str(&cg.apply_dispatch(n));
        dispatch.push('\n');
    }

    Ok(finish_module(isa, &cg, &fn_bodies, &dispatch))
}

fn finish_module<I: Isa>(isa: &I, cg: &Cg<'_, I>, fn_bodies: &str, dispatch: &str) -> String {
    let mut out = String::new();
    let mut seen = BTreeSet::new();
    isa.prelude(&mut out, &mut seen);
    // Runtime declares beyond the static prelude are per-use, so modules that
    // never leave the immediate fast path stay byte-stable. `declare` dedups
    // against the prelude, since some runtime symbols appear in both.
    for (sym, arity) in &cg.used_rt {
        isa.declare(&mut out, &mut seen, sym, *arity);
    }
    // The owned-libm transcendentals, declared with their `f64 -> f64` signature.
    for sym in &cg.used_fcall {
        isa.declare_f(&mut out, &mut seen, sym);
    }
    for (i, s) in cg.strs.iter().enumerate() {
        isa.str_global(&mut out, i, s);
    }
    out.push('\n');
    out.push_str(fn_bodies);
    out.push_str(dispatch);
    out
}

/// Escape a string for an MLIR string literal: printable ASCII verbatim,
/// backslash, quote and non-printables as two-digit hex escapes.
#[cfg(feature = "mlir")]
pub(super) fn escape_str(s: &str) -> String {
    let mut escaped = String::new();
    for b in s.bytes() {
        match b {
            b'\\' => escaped.push_str("\\5C"),
            b'"' => escaped.push_str("\\22"),
            crate::ASCII_PRINTABLE_LO..=crate::ASCII_PRINTABLE_HI => escaped.push(b as char),
            _ => write!(escaped, "\\{b:02X}").unwrap(),
        }
    }
    escaped
}

/// Runtime declares for the string builtins, in table order: each is a
/// `(symbol, arity)` pair taking and returning `i64`.
#[cfg(feature = "mlir")]
pub(super) fn str_builtin_decls() -> impl Iterator<Item = (String, usize)> {
    BUILTINS
        .iter()
        .filter(|(_, _, kind)| *kind == BuiltinKind::Str)
        .map(|(name, arity, _)| {
            let sym = Builtin::from_name(name)
                .expect("ICE: str builtin name not in Builtin")
                .sym();
            (sym, *arity)
        })
}

#[cfg(test)]
mod tests {
    use crate::core::builtins::{Builtin, BuiltinKind, BUILTINS};

    fn c_def(name: &str) -> i64 {
        let prefix = format!("#define {name} ");
        let line = super::rt::RUNTIME_FILES
            .iter()
            .flat_map(|(_, body, _)| body.lines())
            .find(|l| l.starts_with(&prefix))
            .unwrap_or_else(|| panic!("{name} not defined in any runtime/ module"));
        let val = line[prefix.len()..].trim_end().trim_end_matches('L');
        val.strip_prefix("0x").map_or_else(
            || val.parse().unwrap(),
            |hex| i64::from_str_radix(hex, 16).unwrap(),
        )
    }

    #[test]
    fn layout_matches_runtime() {
        assert_eq!(c_def("PRISM_STR_TAG"), super::STR_TAG);
        assert_eq!(c_def("PRISM_BIG_TAG"), super::BIG_TAG);
        assert_eq!(c_def("PRISM_TAG_W") * super::WORD_BYTES, super::TAG_OFF);
        assert_eq!(
            c_def("PRISM_HDR_WORDS") * super::WORD_BYTES,
            super::HDR_BYTES
        );
        assert_eq!(c_def("PRISM_RC_W"), 0);
        assert_eq!(
            c_def("PRISM_ARITY_W") * super::WORD_BYTES + super::WORD_BYTES,
            super::HDR_BYTES
        );
    }

    // `Builtin::abi` is exhaustive (no wildcard), so the compiler already forces
    // every variant to declare its convention and rejects a symbol that no
    // `Builtin` produces. This checks the remaining well-formedness invariant the
    // type system cannot: every tagged arg index stays within the builtin's
    // arity and no arg is both immediate and float, so re-arity-ing a builtin
    // trips here rather than mis-tagging a call at runtime.
    #[test]
    fn builtin_abi_within_arity() {
        for &(name, arity, kind) in BUILTINS {
            if kind != BuiltinKind::Str {
                continue;
            }
            let b =
                Builtin::from_name(name).expect("str builtin in BUILTINS has no Builtin variant");
            assert!(
                b.abi().args_within(arity),
                "{name} tags an argument beyond arity {arity}"
            );
        }
    }
}
