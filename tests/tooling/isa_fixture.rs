// The out-of-tree backend fixture: an `Isa` implementation written purely
// against the public API, the compile-time pin of the supported backend
// contract. If a change to `Isa`, `emit_with_isa`, or the checked lowered-input
// path breaks external backend authors, it breaks here first, as a reviewed
// signature change rather than a silent one.
//
// The renderer is deliberately trivial (a line of pseudo-assembly per
// instruction); semantic lowering lives in the shared emitter, and this file
// exercises only the seam: implement the trait, admit a program through
// `LoweredCore::validate_structural` (the lint-grade checked constructor), and
// emit.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use prism::codegen::{emit_with_isa, Buf, Cmp, FloatBinOp, FloatIntrinsic, IntOp, Isa};
use prism::core::{Comp, Core, CoreFn, LoweredCore, Value};
use prism::Sym;

struct PseudoAsm;

// One pseudo-instruction line; every destination is minted by the caller-side
// counter the emitter threads through `Buf`, so a fixed spelling suffices here.
fn op(b: &mut Buf, text: &str) {
    b.body.push_str(text);
    b.body.push('\n');
}

impl Isa for PseudoAsm {
    fn const_int(&self, _b: &mut Buf, n: i64) -> String {
        format!("#{n}")
    }
    fn const_float(&self, _b: &mut Buf, f: f64) -> String {
        format!("#{f}")
    }
    fn fresh_zero(&self, _b: &mut Buf) -> String {
        "#0".to_string()
    }
    fn str_lit(&self, b: &mut Buf, dst: &str, idx: usize, len: usize) {
        op(b, &format!("{dst} = str {idx} {len}"));
    }
    fn bin(&self, b: &mut Buf, dst: &str, op_: IntOp, x: &str, y: &str) {
        op(b, &format!("{dst} = {op_:?} {x} {y}"));
    }
    fn fbin(&self, b: &mut Buf, dst: &str, op_: FloatBinOp, x: &str, y: &str) {
        op(b, &format!("{dst} = {op_:?} {x} {y}"));
    }
    fn icmp(&self, b: &mut Buf, dst: &str, pred: Cmp, x: &str, y: &str) {
        op(b, &format!("{dst} = icmp {pred:?} {x} {y}"));
    }
    fn fcmp(&self, b: &mut Buf, dst: &str, pred: Cmp, x: &str, y: &str) {
        op(b, &format!("{dst} = fcmp {pred:?} {x} {y}"));
    }
    fn zext(&self, b: &mut Buf, dst: &str, c: &str) {
        op(b, &format!("{dst} = zext {c}"));
    }
    fn sitofp(&self, b: &mut Buf, dst: &str, v: &str) {
        op(b, &format!("{dst} = sitofp {v}"));
    }
    fn fptosi_sat(&self, b: &mut Buf, dst: &str, v: &str) {
        op(b, &format!("{dst} = fptosi_sat {v}"));
    }
    fn cast_i2f(&self, b: &mut Buf, dst: &str, v: &str) {
        op(b, &format!("{dst} = i2f {v}"));
    }
    fn cast_f2i(&self, b: &mut Buf, dst: &str, v: &str) {
        op(b, &format!("{dst} = f2i {v}"));
    }
    fn f_intrinsic(&self, b: &mut Buf, dst: &str, op_: FloatIntrinsic, a: &str) {
        op(b, &format!("{dst} = {op_:?} {a}"));
    }
    fn f_call1(&self, b: &mut Buf, dst: &str, sym: &str, a: &str) {
        op(b, &format!("{dst} = call {sym} {a}"));
    }
    fn declare_f(&self, _out: &mut String, _seen: &mut BTreeSet<String>, _sym: &str) {}
    fn fneg(&self, b: &mut Buf, dst: &str, x: &str) {
        op(b, &format!("{dst} = fneg {x}"));
    }
    fn inttoptr(&self, b: &mut Buf, dst: &str, v: &str) {
        op(b, &format!("{dst} = inttoptr {v}"));
    }
    fn ptrtoint(&self, b: &mut Buf, dst: &str, p: &str) {
        op(b, &format!("{dst} = ptrtoint {p}"));
    }
    fn alloca_word(&self, b: &mut Buf, dst: &str) {
        op(b, &format!("{dst} = alloca"));
    }
    fn gep(&self, b: &mut Buf, dst: &str, p: &str, off: i64) {
        op(b, &format!("{dst} = gep {p} {off}"));
    }
    fn load(&self, b: &mut Buf, dst: &str, p: &str) {
        op(b, &format!("{dst} = load {p}"));
    }
    fn store(&self, b: &mut Buf, v: &str, p: &str) {
        op(b, &format!("store {v} {p}"));
    }
    fn call(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        op(b, &format!("{dst} = call {f} {}", args.join(" ")));
    }
    fn call_ptr(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        op(b, &format!("{dst} = call_ptr {f} {}", args.join(" ")));
    }
    fn call_void(&self, b: &mut Buf, f: &str, args: &[String]) {
        op(b, &format!("call {f} {}", args.join(" ")));
    }
    fn musttail_call(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        op(b, &format!("{dst} = musttail {f} {}", args.join(" ")));
    }
    fn printf_str(&self, b: &mut Buf, p: &str) {
        op(b, &format!("printf {p}"));
    }
    fn jump(&self, b: &mut Buf, l: &str) {
        op(b, &format!("jump {l}"));
    }
    fn cond_br(&self, b: &mut Buf, c: &str, lt: &str, lf: &str) {
        op(b, &format!("br {c} {lt} {lf}"));
    }
    fn switch(&self, b: &mut Buf, v: &str, default: &str, cases: &[(i64, String)]) {
        op(b, &format!("switch {v} {default} {cases:?}"));
    }
    fn unreachable(&self, b: &mut Buf) {
        op(b, "unreachable");
    }
    fn ret(&self, b: &mut Buf, v: &str) {
        op(b, &format!("ret {v}"));
    }
    fn open_entry(&self, b: &mut Buf) {
        op(b, "entry:");
    }
    fn open_block(&self, b: &mut Buf, l: &str) {
        op(b, &format!("{l}:"));
    }
    fn jump_merge(&self, b: &mut Buf, l: &str, v: &str) {
        op(b, &format!("jump {l} ({v})"));
    }
    fn open_merge(&self, b: &mut Buf, l: &str, dst: &str, preds: &[(String, String)]) {
        op(b, &format!("{l}({dst} from {preds:?}):"));
    }
    fn fn_define(&self, name: &str, params: &[String]) -> String {
        format!("fn {name}({})\n", params.join(", "))
    }
    fn fn_close(&self) -> String {
        "end\n".to_string()
    }
    fn prelude(&self, _out: &mut String, _seen: &mut BTreeSet<String>) {}
    fn declare(&self, _out: &mut String, _seen: &mut BTreeSet<String>, _sym: &str, _arity: usize) {}
    fn str_global(&self, out: &mut String, idx: usize, s: &str) {
        let _ = writeln!(out, "str{idx} = {s:?}");
    }
}

fn main_returning(n: i64) -> Core {
    Core {
        fns: vec![CoreFn {
            name: Sym::new("main"),
            params: vec![],
            body: Comp::Return(Value::Int(n)),
            dict_arity: 0,
        }],
    }
}

// The full external path: validate a hand-built lowered program through the
// public checked constructor and emit it with an out-of-tree backend.
#[test]
fn external_backend_compiles_through_the_public_contract() {
    let lowered =
        LoweredCore::validate_structural(main_returning(42)).expect("structurally valid program");
    let text = emit_with_isa(&PseudoAsm, &lowered, &std::collections::BTreeMap::new())
        .expect("the shared emitter drives the external Isa");
    assert!(text.contains("fn"), "emitted module names its function");
}

// The checked constructor is a real gate: a structural violation (an unbound
// variable) is refused, so a forged stage claim cannot reach a backend.
#[test]
fn validate_structural_refuses_a_malformed_program() {
    let bad = Core {
        fns: vec![CoreFn {
            name: Sym::new("main"),
            params: vec![],
            body: Comp::Return(Value::Var(Sym::new("nowhere"))),
            dict_arity: 0,
        }],
    };
    let errs = LoweredCore::validate_structural(bad).expect_err("unbound variable is refused");
    assert!(errs.iter().any(|e| e.contains("unbound")));
}
