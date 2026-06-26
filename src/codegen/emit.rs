//! Backend-neutral lowering walker. All semantic decisions (tagging, closure
//! layout, case dispatch, RC, tail calls) live here. An `Isa` impl supplies
//! only the instructions of its target (LLVM via inkwell or MLIR's llvm
//! dialect as text). The two targets differ structurally in one place: LLVM
//! merges control flow with phi nodes, MLIR with block arguments, abstracted
//! as `jump_merge`/`open_merge`.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "mlir")]
use std::fmt::Write;
use std::slice;

use crate::core::builtins::{builtin, BuiltinKind, FloatOp};
use crate::core::effect_lower::EOP;
use crate::core::tailrec::{reassoc, trmc_mode, trmc_shape, TrmcMode, TrmcShape};
use crate::core::{fv, reachable_fns, Comp, Core, CoreFn, CoreOp, CorePat, Value};
use crate::names::{closure_cap, closure_rem};
use crate::sym::Sym;
use crate::types::CtorInfo;

// Variable identity stays `Sym` end-to-end; the value is the SSA register name
// (`%t3`, `%a0`, ...), the legitimate output-edge text.
type Regs = BTreeMap<Sym, String>;

// Must match the heap cell layout in runtime/prism_rt.c:
// {refcount@0, tag@8, arity@16, fields@24}, cross-checked against the
// runtime's PRISM_*_W macros by the `layout_matches_runtime` test.
const TAG_OFF: i64 = 8;
const HDR_BYTES: i64 = 24;
const WORD_BYTES: i64 = 8;

// Reserved heap tags, cross-checked against runtime/prism_rt.c by the
// `layout_matches_runtime` test. Ctor and lambda tags must stay below both.
const STR_TAG: i64 = 0x5354_5200;
const BIG_TAG: i64 = 0x4249_4700;
const _: () = assert!(
    size_of::<usize>() == 8 && size_of::<u64>() == 8,
    "prism tagging scheme assumes LP64"
);

pub(super) fn idx64(n: usize) -> i64 {
    // `n` is a heap tag, field index, arity, or byte length of an in-memory
    // program. Exceeding `i64::MAX` would require an >8-exabyte input on an LP64
    // host (unreachable in practice), and this is called from many
    // value-returning sites that cannot thread a `Result`. Saturate rather than
    // panic; the result stays a valid `i64`.
    i64::try_from(n).unwrap_or(i64::MAX)
}

#[derive(Clone)]
enum LamBody {
    // An ordinary closure.
    Core(Comp),
    // A curry adapter for under-application. Once saturated with its remaining
    // params it forwards all captured-plus-remaining values to `target` (an
    // index into `lams`), which has the full arity.
    Curry { target: usize },
}

#[derive(Clone)]
struct LamInfo {
    tag: usize,
    params: Vec<Sym>,
    free_vars: Vec<Sym>,
    body: LamBody,
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

#[derive(Default)]
pub(super) struct Buf {
    tmp: usize,
    blk: usize,
    pub(super) cur: String,
    pub(super) body: String,
}

impl Buf {
    pub(super) fn tmp(&mut self) -> String {
        let r = format!("%t{}", self.tmp);
        self.tmp += 1;
        r
    }

    fn label(&mut self) -> String {
        let l = format!("b{}", self.blk);
        self.blk += 1;
        l
    }

    #[cfg(feature = "mlir")]
    pub(super) fn line(&mut self, s: &str) {
        writeln!(self.body, "  {s}").unwrap();
    }

    #[cfg(feature = "mlir")]
    pub(super) fn open(&mut self, text: &str, label: &str) {
        writeln!(self.body, "{text}").unwrap();
        self.cur = label.to_string();
    }

    fn reset(&mut self) {
        self.tmp = 0;
        self.blk = 0;
        self.body.clear();
    }
}

// The integer machine ops a backend renders. An enum (not a string) so each
// backend's match is exhaustive and an unknown op is unrepresentable, never a
// codegen panic.
#[derive(Clone, Copy)]
pub(super) enum IntOp {
    Add,
    Sub,
    And,
    Or,
    Shl,
    Ashr,
}

impl IntOp {
    // Only the textual MLIR backend renders the mnemonic; the LLVM backend
    // matches the variant directly into an inkwell builder call.
    #[cfg(feature = "mlir")]
    pub(super) const fn mnemonic(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::And => "and",
            Self::Or => "or",
            Self::Shl => "shl",
            Self::Ashr => "ashr",
        }
    }
}

pub(super) trait Isa {
    fn const_int(&self, b: &mut Buf, n: i64) -> String;
    fn const_float(&self, b: &mut Buf, f: f64) -> String;
    fn fresh_zero(&self, b: &mut Buf) -> String;
    fn str_lit(&self, b: &mut Buf, dst: &str, idx: usize, len: usize);
    fn bin(&self, b: &mut Buf, dst: &str, op: IntOp, x: &str, y: &str);
    fn fbin(&self, b: &mut Buf, dst: &str, op: &str, x: &str, y: &str);
    fn icmp(&self, b: &mut Buf, dst: &str, pred: &str, x: &str, y: &str);
    fn fcmp(&self, b: &mut Buf, dst: &str, pred: &str, x: &str, y: &str);
    fn zext(&self, b: &mut Buf, dst: &str, c: &str);
    fn sitofp(&self, b: &mut Buf, dst: &str, v: &str);
    fn fptosi(&self, b: &mut Buf, dst: &str, v: &str);
    fn cast_i2f(&self, b: &mut Buf, dst: &str, v: &str);
    fn cast_f2i(&self, b: &mut Buf, dst: &str, v: &str);
    fn f_intrinsic(&self, b: &mut Buf, dst: &str, name: &str, a: &str);
    fn inttoptr(&self, b: &mut Buf, dst: &str, v: &str);
    fn ptrtoint(&self, b: &mut Buf, dst: &str, p: &str);
    fn alloca_word(&self, b: &mut Buf, dst: &str);
    fn gep(&self, b: &mut Buf, dst: &str, p: &str, off: i64);
    fn load(&self, b: &mut Buf, dst: &str, p: &str);
    fn store(&self, b: &mut Buf, v: &str, p: &str);
    fn call(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]);
    fn call_ptr(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]);
    fn call_void(&self, b: &mut Buf, f: &str, args: &[String]);
    fn musttail_call(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]);
    fn printf_float(&self, b: &mut Buf, v: &str);
    fn printf_str(&self, b: &mut Buf, p: &str);
    fn exit_with(&self, b: &mut Buf, v: &str);
    fn jump(&self, b: &mut Buf, l: &str);
    fn cond_br(&self, b: &mut Buf, c: &str, lt: &str, lf: &str);
    fn switch(&self, b: &mut Buf, v: &str, default: &str, cases: &[(i64, String)]);
    fn unreachable(&self, b: &mut Buf);
    fn ret(&self, b: &mut Buf, v: &str);
    fn open_entry(&self, b: &mut Buf);
    fn open_block(&self, b: &mut Buf, l: &str);
    fn jump_merge(&self, b: &mut Buf, l: &str, v: &str);
    fn open_merge(&self, b: &mut Buf, l: &str, dst: &str, preds: &[(String, String)]);
    fn fn_define(&self, name: &str, params: &[String]) -> String;
    fn fn_close(&self) -> String;
    fn prelude(&self, out: &mut String);
    fn declare(&self, out: &mut String, sym: &str, arity: usize);
    fn str_global(&self, out: &mut String, idx: usize, s: &str);
}

struct Cg<'a, I> {
    isa: &'a I,
    b: Buf,
    cur_arity: usize,
    ctors: &'a BTreeMap<String, CtorInfo>,
    fn_arities: BTreeMap<String, usize>,
    lams: Vec<LamInfo>,
    // Curry adapters memoized by (target lam, supplied arg count), so dispatch
    // planning and emission agree on adapter tags.
    adapters: BTreeMap<(usize, usize), usize>,
    strs: Vec<String>,
    used_rt: BTreeMap<String, usize>,
    // Arities at which `prism_apply_n` is actually called. A 0-arg `App` (and any
    // arity with no matching lambda) still needs the function emitted, or it is
    // an undefined symbol at link time.
    used_apply: BTreeSet<usize>,
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
            used_apply: BTreeSet::new(),
            trmc: None,
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

    // Hygienic core names carry `@`, which LLVM rejects in symbols. `.` is
    // unforgeable in source identifiers and valid unquoted in LLVM and MLIR.
    fn sym(name: &str) -> String {
        format!("prism_{}", name.replace('@', "."))
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
        let ptr = self.dst(|i, b, d| i.call_ptr(b, d, "prism_alloc", slice::from_ref(&n)));
        self.fill_obj(&ptr, tag, fields)
    }

    fn reuse_obj(&mut self, token: &str, tag: i64, fields: &[String]) -> String {
        let n = self.isa.const_int(&mut self.b, idx64(fields.len()));
        let args = [token.to_string(), n];
        let ptr = self.dst(|i, b, d| i.call_ptr(b, d, "prism_reuse_alloc", &args));
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
        free_vars.sort_by_key(|s| s.as_str());

        let tag = self.lams.len();
        self.lams.push(LamInfo {
            tag,
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
        Ok(self.alloc_obj(idx64(tag), &fvs))
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
            .call_void(&mut self.b, "prism_rc_dec", &[v.to_string()]);
    }

    fn unbox(&mut self, p: &str) -> String {
        self.dst(|i, b, d| i.call(b, d, "prism_unbox", &[p.to_string()]))
    }

    fn box_i64(&mut self, payload: &str) -> String {
        self.dst(|i, b, d| i.call(b, d, "prism_box", &[payload.to_string()]))
    }

    fn f_in(&mut self, v: &str) -> String {
        let bits = self.unbox(v);
        self.dst(|i, b, d| i.cast_i2f(b, d, &bits))
    }

    fn f_out(&mut self, fv: &str) -> String {
        let bits = self.dst(|i, b, d| i.cast_f2i(b, d, fv));
        self.box_i64(&bits)
    }

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
            Value::Tuple(fields) => {
                let fvs = self.values(regs, fields)?;
                Ok(self.alloc_obj(0, &fvs))
            }
            Value::Ctor(name, tag, fields) => {
                let fvs = self.values(regs, fields)?;
                let obj = self.alloc_obj(idx64(*tag), &fvs);
                // Count the EOp cell each `do op` builds (stderr-only under
                // PRISM_EFFOP_STATS, so stdout is untouched).
                if *name == EOP {
                    self.isa.call_void(&mut self.b, "prism_effop_alloc", &[]);
                }
                Ok(obj)
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
            Comp::Print(v) => {
                let r = self.value(regs, v)?;
                self.isa
                    .call_void(&mut self.b, "prism_print_int", slice::from_ref(&r));
                self.rc_dec(&r);
                Ok(self.isa.const_int(&mut self.b, 0))
            }
            Comp::PrintF(v) => {
                let r = self.value(regs, v)?;
                let fd = self.f_in(&r);
                self.isa.printf_float(&mut self.b, &fd);
                self.rc_dec(&r);
                Ok(self.isa.const_int(&mut self.b, 0))
            }
            Comp::PrintS(v) => {
                let r = self.value(regs, v)?;
                let cp = self.dst(|i, b, d| i.inttoptr(b, d, &r));
                let bp = self.dst(|i, b, d| i.gep(b, d, &cp, HDR_BYTES));
                self.isa.printf_str(&mut self.b, &bp);
                self.rc_dec(&r);
                Ok(self.isa.const_int(&mut self.b, 0))
            }
            Comp::Error(v) => {
                let r = self.value(regs, v)?;
                if matches!(v, Value::Str(_)) {
                    self.isa.call_void(&mut self.b, "prism_fatal", &[r]);
                } else {
                    let code = self.untag(&r);
                    self.isa.exit_with(&mut self.b, &code);
                }
                Ok(self.isa.const_int(&mut self.b, 0))
            }
            Comp::If(v, t, e) => self.lower_if(regs, v, t, e, false),
            Comp::PrintNl => {
                self.isa.call_void(&mut self.b, "prism_print_nl", &[]);
                Ok(self.isa.const_int(&mut self.b, 0))
            }
            Comp::ReadInt => {
                let t = self.dst(|i, b, d| i.call(b, d, "prism_read_int", &[]));
                Ok(self.retag(&t))
            }
            Comp::ReadLine => Ok(self.dst(|i, b, d| i.call(b, d, "prism_read_line", &[]))),
            Comp::Rand => {
                let t = self.dst(|i, b, d| i.call(b, d, "prism_rand", &[]));
                Ok(self.retag(&t))
            }
            Comp::Srand(v) => {
                let r = self.value(regs, v)?;
                let ut = self.untag(&r);
                self.isa
                    .call_void(&mut self.b, "prism_srand", slice::from_ref(&ut));
                Ok(self.isa.const_int(&mut self.b, 0))
            }
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
                    FloatOp::ToFloat => {
                        let ua = self.untag(&a);
                        let rf = self.dst(|i, b, d| i.sitofp(b, d, &ua));
                        self.f_out(&rf)
                    }
                    FloatOp::Truncate => {
                        let fa = self.f_in(&a);
                        let r = self.dst(|i, b, d| i.fptosi(b, d, &fa));
                        self.retag(&r)
                    }
                    FloatOp::FloorToInt => {
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_intrinsic(b, d, "floor", &fa));
                        let r = self.dst(|i, b, d| i.fptosi(b, d, &ff));
                        self.retag(&r)
                    }
                    FloatOp::CeilToInt => {
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_intrinsic(b, d, "ceil", &fa));
                        let r = self.dst(|i, b, d| i.fptosi(b, d, &ff));
                        self.retag(&r)
                    }
                    FloatOp::AbsFloat => {
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_intrinsic(b, d, "fabs", &fa));
                        self.f_out(&ff)
                    }
                    FloatOp::Sqrt | FloatOp::Sin | FloatOp::Cos | FloatOp::Exp | FloatOp::Ln => {
                        let intr = match op {
                            FloatOp::Sqrt => "sqrt",
                            FloatOp::Sin => "sin",
                            FloatOp::Cos => "cos",
                            FloatOp::Exp => "exp",
                            _ => "log",
                        };
                        let fa = self.f_in(&a);
                        let ff = self.dst(|i, b, d| i.f_intrinsic(b, d, intr, &fa));
                        self.f_out(&ff)
                    }
                };
                self.rc_dec(&a);
                Ok(out)
            }
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
                let sym = b.sym();
                if !matches!(builtin(b.name()), Some((_, BuiltinKind::Str))) {
                    self.used_rt.insert(sym.clone(), args.len());
                }
                let (imm_args, float_args, imm_res) = b.abi();
                let mut avs = Vec::new();
                let mut owned = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let v = self.value(regs, a)?;
                    avs.push(if imm_args.contains(&i) {
                        self.untag(&v)
                    } else if float_args.contains(&i) {
                        self.unbox(&v)
                    } else {
                        v.clone()
                    });
                    owned.push(v);
                }
                let t = self.dst(|i, b, d| i.call(b, d, &sym, &avs));
                let out = if imm_res { self.retag(&t) } else { t };
                for v in owned {
                    self.rc_dec(&v);
                }
                Ok(out)
            }
            Comp::Dup(v) => {
                let r = self.value(regs, v)?;
                self.isa.call_void(&mut self.b, "prism_rc_inc", &[r]);
                Ok(self.isa.fresh_zero(&mut self.b))
            }
            Comp::Drop(v) => {
                let r = self.value(regs, v)?;
                self.isa.call_void(&mut self.b, "prism_rc_dec", &[r]);
                Ok(self.isa.fresh_zero(&mut self.b))
            }
            Comp::WithReuse { token, freed, body } => {
                let r = self.value(regs, freed)?;
                let t = self.dst(|i, b, d| i.call(b, d, "prism_reuse_token", slice::from_ref(&r)));
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
                Ok(self.dst(|i, b, d| i.call(b, d, "prism_ref_new", slice::from_ref(&r))))
            }
            Comp::RefGet(c) => {
                let cv = self.value(regs, c)?;
                let r = self.dst(|i, b, d| i.call(b, d, "prism_ref_get", slice::from_ref(&cv)));
                self.rc_dec(&cv);
                Ok(r)
            }
            Comp::RefSet(c, v) => {
                let cv = self.value(regs, c)?;
                let rv = self.value(regs, v)?;
                self.isa
                    .call_void(&mut self.b, "prism_ref_set", &[cv.clone(), rv]);
                self.rc_dec(&cv);
                Ok(self.isa.fresh_zero(&mut self.b))
            }
        }
    }

    fn lower_tail(&mut self, regs: &Regs, c: &Comp) -> Result<(), String> {
        match c {
            Comp::Bind(m, x, n) => {
                if let (Some(t), Comp::Call(g, args)) = (self.trmc.clone(), m.as_ref()) {
                    if *g == t.name && args.len() == t.arity {
                        if let Some(shape) = trmc_shape(n, x.as_str()) {
                            return self.trmc_step(regs, args, &shape, &t);
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
                let t = self.dst(|i, b, d| i.call(b, d, "prism_reuse_token", slice::from_ref(&r)));
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
                        self.dst(|i, b, d| i.call_ptr(b, d, "prism_reuse_alloc", &cargs))
                    }
                    None => {
                        self.dst(|i, b, d| i.call_ptr(b, d, "prism_alloc", slice::from_ref(&n)))
                    }
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
        let c = self.dst(|i, b, d| i.icmp(b, d, "ne", &vc, &one));
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
                    if let Some(info) = self.ctors.get(name.as_str()) {
                        cases.push((idx64(info.tag), arm_lbls[i].clone()));
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

    fn prim(&mut self, op: CoreOp, a: &str, b: &str) -> String {
        match op {
            CoreOp::Addf | CoreOp::Subf | CoreOp::Mulf | CoreOp::Divf => {
                let fa = self.f_in(a);
                let fb = self.f_in(b);
                let instr = match op {
                    CoreOp::Addf => "fadd",
                    CoreOp::Subf => "fsub",
                    CoreOp::Mulf => "fmul",
                    _ => "fdiv",
                };
                let rf = self.dst(|i, bf, d| i.fbin(bf, d, instr, &fa, &fb));
                return self.f_out(&rf);
            }
            CoreOp::Eqf | CoreOp::Nef | CoreOp::Ltf | CoreOp::Lef | CoreOp::Gtf | CoreOp::Gef => {
                let fa = self.f_in(a);
                let fb = self.f_in(b);
                let pred = match op {
                    CoreOp::Eqf => "oeq",
                    CoreOp::Nef => "une",
                    CoreOp::Ltf => "olt",
                    CoreOp::Lef => "ole",
                    CoreOp::Gtf => "ogt",
                    _ => "oge",
                };
                let c = self.dst(|i, bf, d| i.fcmp(bf, d, pred, &fa, &fb));
                let z = self.dst(|i, bf, d| i.zext(bf, d, &c));
                return self.retag(&z);
            }
            CoreOp::Mul | CoreOp::Div | CoreOp::Rem => {
                let sym = match op {
                    CoreOp::Mul => "prism_rt_int_mul",
                    CoreOp::Div => "prism_rt_int_div",
                    _ => "prism_rt_int_rem",
                };
                self.used_rt.insert(sym.into(), 2);
                let args = [a.to_string(), b.to_string()];
                return self.dst(|i, bf, d| i.call(bf, d, sym, &args));
            }
            _ => {}
        }
        let cond = self.both_imm(a, b);
        let fast = self.b.label();
        let slow = self.b.label();
        let merge = self.b.label();
        if matches!(op, CoreOp::Add | CoreOp::Sub) {
            let (instr, sym) = if op == CoreOp::Add {
                (IntOp::Add, "prism_rt_int_add")
            } else {
                (IntOp::Sub, "prism_rt_int_sub")
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
            let fit = self.dst(|i, bf, d| i.icmp(bf, d, "eq", &back, &r));
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
            return out;
        }
        let pred = match op {
            CoreOp::Eq => "eq",
            CoreOp::Ne => "ne",
            CoreOp::Lt => "slt",
            CoreOp::Le => "sle",
            CoreOp::Gt => "sgt",
            _ => "sge",
        };
        // Tagging is order-preserving, so immediates compare as tagged words.
        self.used_rt.insert("prism_rt_int_cmp".into(), 2);
        self.isa.cond_br(&mut self.b, &cond, &fast, &slow);
        self.isa.open_block(&mut self.b, &fast);
        let c1 = self.dst(|i, bf, d| i.icmp(bf, d, pred, a, b));
        let z1 = self.dst(|i, bf, d| i.zext(bf, d, &c1));
        let rf = self.retag(&z1);
        let pf = self.b.cur.clone();
        self.isa.jump_merge(&mut self.b, &merge, &rf);
        self.isa.open_block(&mut self.b, &slow);
        let args = [a.to_string(), b.to_string()];
        let c = self.dst(|i, bf, d| i.call(bf, d, "prism_rt_int_cmp", &args));
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
        self.dst(|i, bf, d| i.icmp(bf, d, "eq", &bit, &one))
    }

    fn function(&mut self, f: &CoreFn) -> Result<String, String> {
        let body = reassoc(&f.body);
        if let Some(mode) = trmc_mode(f.name.as_str(), f.params.len(), &body) {
            return self.trmc_function(f, &body, mode);
        }
        self.b.reset();
        let mut regs = Regs::new();
        let params: Vec<String> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let r = format!("%a{i}");
                regs.insert(*p, r.clone());
                r
            })
            .collect();
        self.cur_arity = f.params.len();
        let header = self.isa.fn_define(&Self::sym(f.name.as_str()), &params);
        self.isa.open_entry(&mut self.b);
        // Count one driver work-step per entry to a free-monad driver (stderr-only
        // under PRISM_DRIVE_STATS, so stdout is untouched). This is the counter
        // whose asymptotics track the trampoline's actual work.
        if crate::core::effect_lower::is_free_monad_driver(f.name.as_str()) {
            self.isa.call_void(&mut self.b, "prism_drive_step", &[]);
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
        let mut params: Vec<String> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let r = format!("%a{i}");
                regs.insert(*p, r.clone());
                r
            })
            .collect();
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
            let r = format!("%_p{i}");
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
                        .call_void(&mut self.b, "prism_rc_inc", slice::from_ref(r));
                }
                let r =
                    self.dst(|i, b, d| i.call(b, d, &format!("prism_lam_{target}"), &all_params));
                self.isa.ret(&mut self.b, &r);
            }
        }
        Ok(format!("{header}{}{}", self.b.body, self.isa.fn_close()))
    }
}

impl<I: Isa> Cg<'_, I> {
    // Tag of the curry adapter that under-applies `target` (arity m, with
    // `target_fvs` captured free vars) to `n` arguments: a lambda of arity m-n
    // capturing target_fvs+n values. Allocated on first request and memoized so
    // planning and emission resolve the same tag.
    fn curry_adapter(&mut self, target: usize, target_fvs: usize, n: usize) -> usize {
        if let Some(&tag) = self.adapters.get(&(target, n)) {
            return tag;
        }
        let tag = self.lams.len();
        let m = self.lams[target].params.len();
        let free_vars = (0..target_fvs + n)
            .map(|i| Sym::new(&closure_cap(i)))
            .collect();
        let params = (0..m - n).map(|i| Sym::new(&closure_rem(i))).collect();
        self.lams.push(LamInfo {
            tag,
            params,
            free_vars,
            body: LamBody::Curry { target },
        });
        self.adapters.insert((target, n), tag);
        tag
    }

    // Register (without emitting) the curry adapters and follow-on apply arities
    // a `prism_apply_n` dispatcher will reference. Stateful backends realize each
    // function on first emission, so this must reach a fixpoint before any lambda
    // body is emitted. Applying zero arguments is the identity on the closure
    // (see `apply_dispatch`), so n == 0 needs no adapter; skipping it also keeps
    // the fixpoint finite, since an n == 0 under-application would mint a
    // same-arity adapter that regenerates forever. Every other adapter has arity
    // m - n < m, so the chain of adapters-of-adapters strictly shrinks.
    fn plan_dispatch(&mut self, n: usize) {
        if n == 0 {
            return;
        }
        for tag in 0..self.lams.len() {
            let m = self.lams[tag].params.len();
            let fvs = self.lams[tag].free_vars.len();
            match m.cmp(&n) {
                Ordering::Greater => {
                    self.curry_adapter(tag, fvs, n);
                }
                Ordering::Less => {
                    self.used_apply.insert(n - m);
                }
                Ordering::Equal => {}
            }
        }
    }

    // One `prism_apply_n` dispatcher, total over every lambda tag, dispatching
    // per the lambda's parameter count m against the n supplied args: exact
    // (m == n, call it), under (m > n, build a curry adapter closure of arity
    // m-n), or over (m < n, call with the first m then apply the remaining n-m to
    // the result). All adapters and follow-on apply arities must already be
    // planned (see `plan_dispatch`), so this never grows `lams` and references
    // only emitted functions. Applying zero arguments only ever lands on an
    // arity-0 thunk, so for n == 0 the sole reachable case is m == 0;
    // positive-arity tags route to `_dead` like any non-applicable value.
    fn apply_dispatch(&mut self, n: usize) -> String {
        let lams: Vec<LamInfo> = self
            .lams
            .iter()
            .filter(|l| n > 0 || l.params.is_empty())
            .cloned()
            .collect();
        let mut params = vec!["%_clos".to_string()];
        params.extend((0..n).map(|i| format!("%_a{i}")));
        let header = self.isa.fn_define(&format!("prism_apply_{n}"), &params);

        let mut b = Buf::default();
        self.isa.open_entry(&mut b);

        self.isa.inttoptr(&mut b, "%_cp", "%_clos");
        self.isa.gep(&mut b, "%_tp", "%_cp", TAG_OFF);
        self.isa.load(&mut b, "%_tag", "%_tp");

        if lams.is_empty() {
            self.isa.call_void(&mut b, "prism_apply_error", &[]);
            self.isa.unreachable(&mut b);
            return format!("{header}{}{}", b.body, self.isa.fn_close());
        }

        let cases: Vec<(i64, String)> = lams
            .iter()
            .map(|l| (idx64(l.tag), format!("_lam{}", l.tag)))
            .collect();
        self.isa.switch(&mut b, "%_tag", "_dead", &cases);
        self.isa.open_block(&mut b, "_dead");
        self.isa.call_void(&mut b, "prism_apply_error", &[]);
        self.isa.unreachable(&mut b);

        let mut preds: Vec<(String, String)> = Vec::new();
        for lam in &lams {
            let tag = lam.tag;
            let m = lam.params.len();
            let fvs = lam.free_vars.len();
            self.isa.open_block(&mut b, &format!("_lam{tag}"));

            let mut captured: Vec<String> = Vec::new();
            for i in 0..fvs {
                let fp = format!("%_fp{tag}_{i}");
                let fv = format!("%_fv{tag}_{i}");
                let off = HDR_BYTES + idx64(i) * WORD_BYTES;
                self.isa.gep(&mut b, &fp, "%_cp", off);
                self.isa.load(&mut b, &fv, &fp);
                captured.push(fv);
            }
            let args: Vec<String> = (0..n).map(|i| format!("%_a{i}")).collect();
            let r = format!("%_r{tag}");

            match m.cmp(&n) {
                Ordering::Equal => {
                    let mut call_args = captured;
                    call_args.extend(args);
                    self.isa
                        .call(&mut b, &r, &format!("prism_lam_{tag}"), &call_args);
                }
                Ordering::Greater => {
                    // Under-application: capture (fvs ++ args) into an adapter
                    // closure expecting the remaining m-n. The fvs are still owned
                    // by `%_clos` (the caller drops it after this apply), so dup
                    // them; the args were handed to us and move in.
                    let adapter = self.curry_adapter(tag, fvs, n);
                    let mut fields = captured;
                    for fv in &fields {
                        self.isa
                            .call_void(&mut b, "prism_rc_inc", slice::from_ref(fv));
                    }
                    fields.extend(args);
                    let nf = self.isa.const_int(&mut b, idx64(fields.len()));
                    let cp = format!("%_ac{tag}");
                    self.isa
                        .call_ptr(&mut b, &cp, "prism_alloc", slice::from_ref(&nf));
                    let tp = format!("%_atp{tag}");
                    self.isa.gep(&mut b, &tp, &cp, TAG_OFF);
                    let tv = self.isa.const_int(&mut b, idx64(adapter));
                    self.isa.store(&mut b, &tv, &tp);
                    for (i, fld) in fields.iter().enumerate() {
                        let off = HDR_BYTES + idx64(i) * WORD_BYTES;
                        let fp = format!("%_afp{tag}_{i}");
                        self.isa.gep(&mut b, &fp, &cp, off);
                        self.isa.store(&mut b, fld, &fp);
                    }
                    self.isa.ptrtoint(&mut b, &r, &cp);
                }
                Ordering::Less => {
                    // Over-application: call with the first m args for the next
                    // closure, then apply the remaining n-m to it.
                    let mut call_args = captured;
                    call_args.extend(args.iter().take(m).cloned());
                    let inter = format!("%_i{tag}");
                    self.isa
                        .call(&mut b, &inter, &format!("prism_lam_{tag}"), &call_args);
                    let mut more = vec![inter.clone()];
                    more.extend(args.iter().skip(m).cloned());
                    self.isa
                        .call(&mut b, &r, &format!("prism_apply_{}", n - m), &more);
                    self.isa.call_void(&mut b, "prism_rc_dec", &[inter]);
                }
            }
            self.isa.jump_merge(&mut b, "_merge", &r);
            preds.push((r, format!("_lam{tag}")));
        }
        self.isa.open_merge(&mut b, "_merge", "%_result", &preds);
        self.isa.ret(&mut b, "%_result");
        format!("{header}{}{}", b.body, self.isa.fn_close())
    }
}

pub(super) fn emit_with<I: Isa>(
    isa: &I,
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<String, String> {
    let live = reachable_fns(core);
    let fn_arities: BTreeMap<String, usize> = core
        .fns
        .iter()
        .map(|f| (f.name.to_string(), f.params.len()))
        .collect();
    let mut fn_bodies = String::new();
    let mut cg = Cg::new(isa, ctors, fn_arities);

    for f in &core.fns {
        if live.contains(&f.name) {
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

    // Plan every curry adapter and follow-on apply arity to a fixpoint. This runs
    // against the complete closure set, and adapter (`Curry`) bodies mint no
    // further closures, so the adapters emitted just below are the last lambdas
    // added. Each round strictly shrinks adapter arity (n == 0 mints nothing), so
    // the fixpoint terminates.
    loop {
        let before = (cg.lams.len(), cg.used_apply.len());
        let arities: Vec<usize> = {
            let mut a: BTreeSet<usize> = cg.lams.iter().map(|l| l.params.len()).collect();
            a.extend(cg.used_apply.iter().copied());
            a.into_iter().collect()
        };
        for n in arities {
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
    let arities: BTreeSet<usize> = {
        let mut a: BTreeSet<usize> = cg.lams.iter().map(|l| l.params.len()).collect();
        a.extend(cg.used_apply.iter().copied());
        a
    };
    let mut dispatch = String::new();
    for n in arities {
        dispatch.push_str(&cg.apply_dispatch(n));
        dispatch.push('\n');
    }

    let mut out = String::new();
    isa.prelude(&mut out);
    // Runtime declares beyond the static prelude are per-use, so modules that
    // never leave the immediate fast path stay byte-stable.
    for (sym, arity) in &cg.used_rt {
        isa.declare(&mut out, sym, *arity);
    }
    for (i, s) in cg.strs.iter().enumerate() {
        isa.str_global(&mut out, i, s);
    }
    out.push('\n');
    out.push_str(&fn_bodies);
    out.push_str(&dispatch);
    Ok(out)
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
            0x20..=0x7E => escaped.push(b as char),
            _ => write!(escaped, "\\{b:02X}").unwrap(),
        }
    }
    escaped
}

fn partial_app_body(name: &str, n_given: usize, arity: usize) -> (Vec<Sym>, Vec<Sym>, Comp) {
    let cap_names: Vec<Sym> = (0..n_given).map(|i| Sym::new(&closure_cap(i))).collect();
    let rem_names: Vec<Sym> = (0..arity - n_given)
        .map(|i| Sym::new(&closure_rem(i)))
        .collect();
    let call_args = cap_names
        .iter()
        .chain(rem_names.iter())
        .map(|n| Value::Var(*n))
        .collect();
    let mut body = Comp::Call(name.into(), call_args);
    for cn in &cap_names {
        body = Comp::Bind(
            Box::new(Comp::Dup(Value::Var(*cn))),
            "_".into(),
            Box::new(body),
        );
    }
    (cap_names, rem_names, body)
}

/// Runtime declares for the string builtins, in table order: each is a
/// `(symbol, arity)` pair taking and returning `i64`.
#[cfg(feature = "mlir")]
pub(super) fn str_builtin_decls() -> impl Iterator<Item = (String, usize)> {
    crate::core::builtins::BUILTINS
        .iter()
        .filter(|(_, _, kind)| *kind == BuiltinKind::Str)
        .map(|(name, arity, _)| {
            let sym = crate::core::builtins::Builtin::from_name(name)
                .expect("ICE: str builtin name not in Builtin")
                .sym();
            (sym, *arity)
        })
}

#[cfg(test)]
mod tests {
    fn c_def(name: &str) -> i64 {
        let rt = include_str!("../../runtime/prism_rt.c");
        let prefix = format!("#define {name} ");
        let line = rt
            .lines()
            .find(|l| l.starts_with(&prefix))
            .unwrap_or_else(|| panic!("{name} not defined in prism_rt.c"));
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
    // `Builtin` produces. This pins the remaining well-formedness invariant the
    // type system cannot: every tagged arg index stays within the builtin's
    // arity and no arg is both immediate and float, so re-arity-ing a builtin
    // trips here rather than mis-tagging a call at runtime.
    #[test]
    fn builtin_abi_within_arity() {
        use crate::core::builtins::{Builtin, BuiltinKind, BUILTINS};

        for &(name, arity, kind) in BUILTINS {
            if kind != BuiltinKind::Str {
                continue;
            }
            let b =
                Builtin::from_name(name).expect("str builtin in BUILTINS has no Builtin variant");
            let (imm, float, _) = b.abi();
            for i in imm {
                assert!(
                    !float.contains(i),
                    "{name} arg {i} is both immediate and float"
                );
            }
            for i in imm.iter().chain(float) {
                assert!(*i < arity, "{name} tags arg {i} but arity is {arity}");
            }
        }
    }
}
