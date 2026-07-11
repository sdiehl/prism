//! The backend machine interface.
//!
//! This module defines the shared SSA buffer (`Buf`), the machine-op enums
//! (`IntOp`, `Cmp`, `FloatBinOp`, `FloatIntrinsic`), and the `Isa` trait each
//! target implements. The backend-neutral lowering walker writes into a `Buf`
//! through an `Isa` and never names a concrete target instruction.

use std::collections::BTreeSet;
use std::fmt::Write;

/// Shared SSA text buffer passed to an [`Isa`] implementation.
#[derive(Debug, Default)]
pub struct Buf {
    tmp: usize,
    blk: usize,
    /// Label of the block currently being emitted.
    pub cur: String,
    /// Function body accumulated by textual backends.
    pub body: String,
}

impl Buf {
    /// Returns a fresh SSA temporary name.
    pub fn tmp(&mut self) -> String {
        let r = format!("%t{}", self.tmp);
        self.tmp += 1;
        r
    }

    /// Returns a fresh block label.
    pub fn label(&mut self) -> String {
        let l = format!("b{}", self.blk);
        self.blk += 1;
        l
    }

    /// Appends one indented instruction line to the textual body.
    pub fn line(&mut self, s: &str) {
        writeln!(self.body, "  {s}").unwrap();
    }

    /// Opens a textual block and records its label as current.
    pub fn open(&mut self, text: &str, label: &str) {
        writeln!(self.body, "{text}").unwrap();
        self.cur = label.to_string();
    }

    pub(super) fn reset(&mut self) {
        self.tmp = 0;
        self.blk = 0;
        self.body.clear();
    }
}

// The integer machine ops a backend renders. An enum (not a string) so each
// backend's match is exhaustive and an unknown op is unrepresentable, never a
// codegen panic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntOp {
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

// The six-way ordered comparison, backend- and lane-agnostic: the int-vs-float
// predicate spelling (signed `slt` vs ordered `olt`) is a rendering concern the
// backend resolves, so int and float comparisons share one enum and one
// exhaustive match at each call site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Cmp {
    // MLIR spells the predicate as a quoted string; LLVM matches the variant
    // into an inkwell `IntPredicate`/`FloatPredicate` directly.
    #[cfg(feature = "mlir")]
    pub(super) const fn icmp_pred(self) -> &'static str {
        match self {
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Lt => "slt",
            Self::Le => "sle",
            Self::Gt => "sgt",
            Self::Ge => "sge",
        }
    }

    #[cfg(feature = "mlir")]
    pub(super) const fn fcmp_pred(self) -> &'static str {
        match self {
            Self::Eq => "oeq",
            Self::Ne => "une",
            Self::Lt => "olt",
            Self::Le => "ole",
            Self::Gt => "ogt",
            Self::Ge => "oge",
        }
    }
}

// The float binary machine ops a backend renders, same shape as `IntOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatBinOp {
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
}

impl FloatBinOp {
    #[cfg(feature = "mlir")]
    pub(super) const fn mnemonic(self) -> &'static str {
        match self {
            Self::Fadd => "fadd",
            Self::Fsub => "fsub",
            Self::Fmul => "fmul",
            Self::Fdiv => "fdiv",
        }
    }
}

// The unary float intrinsics a backend renders. The base name is shared by both
// backends (LLVM forms `llvm.{name}.f64`, MLIR forms `llvm.intr.{name}`), so it
// is not gated on the MLIR feature. Only the exact, correctly-rounded ops live
// here (floor/ceil/round/trunc/sqrt/fabs): every IEEE-754 platform computes them
// identically, so they need no owned implementation. Transcendentals do not
// appear -- platform intrinsics would call the divergent system libm, so they
// route through the owned `prism_m_*` runtime calls instead (see the
// `Comp::FloatBuiltin` lowering and `FloatOp::runtime_sym`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatIntrinsic {
    Floor,
    Ceil,
    Round,
    Trunc,
    Sqrt,
    Fabs,
}

impl FloatIntrinsic {
    /// Runtime intrinsic base name shared by native backends.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Floor => "floor",
            Self::Ceil => "ceil",
            // LLVM `llvm.round.f64` and MLIR `llvm.intr.round` are round-half-away
            // -from-zero, matching Rust `f64::round` in the interpreter.
            Self::Round => "round",
            Self::Trunc => "trunc",
            Self::Sqrt => "sqrt",
            Self::Fabs => "fabs",
        }
    }
}

/// Instruction-spelling interface for the shared Core lowering walker.
///
/// External experimental backends implement this trait and pass the instance to
/// [`super::emit_with_isa`]. Semantic lowering remains in Prism; implementations
/// only render the target's primitive instructions and control-flow operations.
pub trait Isa {
    fn const_int(&self, b: &mut Buf, n: i64) -> String;
    fn const_float(&self, b: &mut Buf, f: f64) -> String;
    fn fresh_zero(&self, b: &mut Buf) -> String;
    fn str_lit(&self, b: &mut Buf, dst: &str, idx: usize, len: usize);
    fn bin(&self, b: &mut Buf, dst: &str, op: IntOp, x: &str, y: &str);
    fn fbin(&self, b: &mut Buf, dst: &str, op: FloatBinOp, x: &str, y: &str);
    fn icmp(&self, b: &mut Buf, dst: &str, pred: Cmp, x: &str, y: &str);
    fn fcmp(&self, b: &mut Buf, dst: &str, pred: Cmp, x: &str, y: &str);
    fn zext(&self, b: &mut Buf, dst: &str, c: &str);
    fn sitofp(&self, b: &mut Buf, dst: &str, v: &str);
    // Saturating float -> signed i64 (clamps to i64::MIN/MAX, NaN -> 0). The
    // pinned float-to-int semantics, matching the interpreter's `f as i64`; plain
    // `fptosi` is undefined out of range and would diverge the backends.
    fn fptosi_sat(&self, b: &mut Buf, dst: &str, v: &str);
    fn cast_i2f(&self, b: &mut Buf, dst: &str, v: &str);
    fn cast_f2i(&self, b: &mut Buf, dst: &str, v: &str);
    fn f_intrinsic(&self, b: &mut Buf, dst: &str, op: FloatIntrinsic, a: &str);
    // A call into the owned vendored libm: `sym` is an `f64 -> f64` symbol
    // (`prism_m_*`), taking and returning a native double. The MLIR backend needs
    // the symbol declared once (`declare_f`); the LLVM backend declares on use.
    fn f_call1(&self, b: &mut Buf, dst: &str, sym: &str, a: &str);
    // Emit a module-level declaration for an `f64 -> f64` runtime symbol. A no-op
    // where the backend declares functions on first use (LLVM/inkwell).
    fn declare_f(&self, out: &mut String, seen: &mut BTreeSet<String>, sym: &str);
    fn fneg(&self, b: &mut Buf, dst: &str, x: &str);
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
    fn printf_str(&self, b: &mut Buf, p: &str);
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
    fn prelude(&self, out: &mut String, seen: &mut BTreeSet<String>);
    // Declares `sym` once: a backend that emits text (MLIR) must not re-declare a
    // symbol the prelude or an earlier use already wrote, or the module fails to
    // verify. `seen` tracks what has been declared.
    fn declare(&self, out: &mut String, seen: &mut BTreeSet<String>, sym: &str, arity: usize);
    fn str_global(&self, out: &mut String, idx: usize, s: &str);
}
