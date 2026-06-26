use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use super::emit::{emit_with, escape_str, idx64, str_builtin_decls, Buf, IntOp, Isa};
use crate::core::Core;
use crate::types::CtorInfo;

/// Textual MLIR `llvm` dialect syntax, translated to LLVM IR by
/// `mlir-translate --mlir-to-llvmir` with no pass pipeline. Constants are
/// `llvm.mlir.constant` ops. Merges are blocks with one block argument.
struct MlirText;

impl Isa for MlirText {
    fn const_int(&self, b: &mut Buf, n: i64) -> String {
        let t = b.tmp();
        b.line(&format!("{t} = llvm.mlir.constant({n} : i64) : i64"));
        t
    }

    fn const_float(&self, b: &mut Buf, f: f64) -> String {
        let t = b.tmp();
        b.line(&format!("{t} = llvm.mlir.constant({f:.17e} : f64) : f64"));
        t
    }

    fn fresh_zero(&self, b: &mut Buf) -> String {
        self.const_int(b, 0)
    }

    fn str_lit(&self, b: &mut Buf, dst: &str, idx: usize, len: usize) {
        let p = b.tmp();
        b.line(&format!("{p} = llvm.mlir.addressof @str{idx} : !llvm.ptr"));
        let n = self.const_int(b, idx64(len));
        b.line(&format!(
            "{dst} = llvm.call @prism_str_lit({p}, {n}) : (!llvm.ptr, i64) -> i64"
        ));
    }

    fn bin(&self, b: &mut Buf, dst: &str, op: IntOp, x: &str, y: &str) {
        b.line(&format!("{dst} = llvm.{} {x}, {y} : i64", op.mnemonic()));
    }

    fn fbin(&self, b: &mut Buf, dst: &str, op: &str, x: &str, y: &str) {
        b.line(&format!("{dst} = llvm.{op} {x}, {y} : f64"));
    }

    fn icmp(&self, b: &mut Buf, dst: &str, pred: &str, x: &str, y: &str) {
        b.line(&format!("{dst} = llvm.icmp \"{pred}\" {x}, {y} : i64"));
    }

    fn fcmp(&self, b: &mut Buf, dst: &str, pred: &str, x: &str, y: &str) {
        b.line(&format!("{dst} = llvm.fcmp \"{pred}\" {x}, {y} : f64"));
    }

    fn zext(&self, b: &mut Buf, dst: &str, c: &str) {
        b.line(&format!("{dst} = llvm.zext {c} : i1 to i64"));
    }

    fn sitofp(&self, b: &mut Buf, dst: &str, v: &str) {
        b.line(&format!("{dst} = llvm.sitofp {v} : i64 to f64"));
    }

    fn fptosi(&self, b: &mut Buf, dst: &str, v: &str) {
        b.line(&format!("{dst} = llvm.fptosi {v} : f64 to i64"));
    }

    fn cast_i2f(&self, b: &mut Buf, dst: &str, v: &str) {
        b.line(&format!("{dst} = llvm.bitcast {v} : i64 to f64"));
    }

    fn cast_f2i(&self, b: &mut Buf, dst: &str, v: &str) {
        b.line(&format!("{dst} = llvm.bitcast {v} : f64 to i64"));
    }

    fn f_intrinsic(&self, b: &mut Buf, dst: &str, name: &str, a: &str) {
        b.line(&format!("{dst} = llvm.intr.{name}({a}) : (f64) -> f64"));
    }

    fn inttoptr(&self, b: &mut Buf, dst: &str, v: &str) {
        b.line(&format!("{dst} = llvm.inttoptr {v} : i64 to !llvm.ptr"));
    }

    fn ptrtoint(&self, b: &mut Buf, dst: &str, p: &str) {
        b.line(&format!("{dst} = llvm.ptrtoint {p} : !llvm.ptr to i64"));
    }

    fn alloca_word(&self, b: &mut Buf, dst: &str) {
        let n = self.const_int(b, 1);
        b.line(&format!(
            "{dst} = llvm.alloca {n} x i64 : (i64) -> !llvm.ptr"
        ));
    }

    fn gep(&self, b: &mut Buf, dst: &str, p: &str, off: i64) {
        b.line(&format!(
            "{dst} = llvm.getelementptr {p}[{off}] : (!llvm.ptr) -> !llvm.ptr, i8"
        ));
    }

    fn load(&self, b: &mut Buf, dst: &str, p: &str) {
        b.line(&format!("{dst} = llvm.load {p} : !llvm.ptr -> i64"));
    }

    fn store(&self, b: &mut Buf, v: &str, p: &str) {
        b.line(&format!("llvm.store {v}, {p} : i64, !llvm.ptr"));
    }

    fn call(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        b.line(&format!(
            "{dst} = llvm.call @{f}({}) : ({}) -> i64",
            args.join(", "),
            i64s(args.len())
        ));
    }

    fn call_ptr(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        b.line(&format!(
            "{dst} = llvm.call @{f}({}) : ({}) -> !llvm.ptr",
            args.join(", "),
            i64s(args.len())
        ));
    }

    fn call_void(&self, b: &mut Buf, f: &str, args: &[String]) {
        b.line(&format!(
            "llvm.call @{f}({}) : ({}) -> ()",
            args.join(", "),
            i64s(args.len())
        ));
    }

    fn musttail_call(&self, b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        b.line(&format!(
            "{dst} = llvm.call musttail @{f}({}) : ({}) -> i64",
            args.join(", "),
            i64s(args.len())
        ));
    }

    fn printf_float(&self, b: &mut Buf, v: &str) {
        Self::printf(b, "fmt_g", v, "f64");
    }

    fn printf_str(&self, b: &mut Buf, p: &str) {
        Self::printf(b, "fmt_s", p, "!llvm.ptr");
    }

    fn exit_with(&self, b: &mut Buf, v: &str) {
        let c = b.tmp();
        b.line(&format!("{c} = llvm.trunc {v} : i64 to i32"));
        b.line(&format!("llvm.call @exit({c}) : (i32) -> ()"));
    }

    fn jump(&self, b: &mut Buf, l: &str) {
        b.line(&format!("llvm.br ^{l}"));
    }

    fn cond_br(&self, b: &mut Buf, c: &str, lt: &str, lf: &str) {
        b.line(&format!("llvm.cond_br {c}, ^{lt}, ^{lf}"));
    }

    fn switch(&self, b: &mut Buf, v: &str, default: &str, cases: &[(i64, String)]) {
        let parts: Vec<String> = cases.iter().map(|(n, l)| format!("{n}: ^{l}")).collect();
        b.line(&format!(
            "llvm.switch {v} : i64, ^{default} [{}]",
            parts.join(", ")
        ));
    }

    fn unreachable(&self, b: &mut Buf) {
        b.line("llvm.unreachable");
    }

    fn ret(&self, b: &mut Buf, v: &str) {
        b.line(&format!("llvm.return {v} : i64"));
    }

    fn open_entry(&self, b: &mut Buf) {
        // The entry block is implicit in the llvm.func signature.
        b.cur = "entry".into();
    }

    fn open_block(&self, b: &mut Buf, l: &str) {
        b.open(&format!("^{l}:"), l);
    }

    fn jump_merge(&self, b: &mut Buf, l: &str, v: &str) {
        b.line(&format!("llvm.br ^{l}({v} : i64)"));
    }

    fn open_merge(&self, b: &mut Buf, l: &str, dst: &str, _preds: &[(String, String)]) {
        b.open(&format!("^{l}({dst}: i64):"), l);
    }

    fn fn_define(&self, name: &str, params: &[String]) -> String {
        let ps: Vec<String> = params.iter().map(|p| format!("{p}: i64")).collect();
        format!("llvm.func @{name}({}) -> i64 {{\n", ps.join(", "))
    }

    fn fn_close(&self) -> String {
        "}\n".into()
    }

    fn prelude(&self, out: &mut String, seen: &mut BTreeSet<String>) {
        // The fixed runtime declarations. Some (the `taq` ops, `exit`) also reach
        // the per-use declares below, so each is registered in `seen` to keep the
        // textual module from declaring a symbol twice (which fails to verify).
        const FIXED: &[&str] = &[
            "llvm.func @printf(!llvm.ptr, ...) -> i32",
            "llvm.func @exit(i32)",
            "llvm.func @prism_alloc(i64) -> !llvm.ptr",
            "llvm.func @prism_div_zero()",
            "llvm.func @prism_apply_error()",
            "llvm.func @prism_fatal(i64)",
            "llvm.func @prism_rc_inc(i64)",
            "llvm.func @prism_rc_dec(i64)",
            "llvm.func @prism_reuse_token(i64) -> i64",
            "llvm.func @prism_reuse_alloc(i64, i64) -> !llvm.ptr",
            "llvm.func @prism_ref_new(i64) -> i64",
            "llvm.func @prism_ref_get(i64) -> i64",
            "llvm.func @prism_ref_set(i64, i64)",
            "llvm.func @prism_effop_alloc()",
            "llvm.func @prism_drive_step()",
            "llvm.func @prism_taq_snoc(i64, i64) -> i64",
            "llvm.func @prism_taq_concat(i64, i64) -> i64",
            "llvm.func @prism_taq_uncons(i64) -> i64",
            "llvm.func @prism_frame_bind(i64, i64, i64) -> i64",
            "llvm.func @prism_frame_handle(i64, i64, i64) -> i64",
            "llvm.func @prism_frame_mask(i64, i64) -> i64",
            "llvm.func @prism_kont_splice(i64, i64) -> i64",
            "llvm.func @prism_box(i64) -> i64",
            "llvm.func @prism_unbox(i64) -> i64",
            "llvm.func @prism_print_int(i64)",
            "llvm.func @prism_print_nl()",
            "llvm.func @prism_read_int() -> i64",
            "llvm.func @prism_read_line() -> i64",
            "llvm.func @prism_rand() -> i64",
            "llvm.func @prism_srand(i64)",
            "llvm.func @prism_str_lit(!llvm.ptr, i64) -> i64",
        ];
        for line in FIXED {
            let name = line
                .split('@')
                .nth(1)
                .and_then(|s| s.split('(').next())
                .unwrap_or("")
                .trim();
            if seen.insert(name.to_string()) {
                out.push_str(line);
                out.push('\n');
            }
        }
        for (sym, arity) in str_builtin_decls() {
            self.declare(out, seen, &sym, arity);
        }
        Self::fmt_global(out, "fmt_g", "%g");
        Self::fmt_global(out, "fmt_s", "%s");
    }

    fn declare(&self, out: &mut String, seen: &mut BTreeSet<String>, sym: &str, arity: usize) {
        if seen.insert(sym.to_string()) {
            writeln!(out, "llvm.func @{sym}({}) -> i64", i64s(arity)).unwrap();
        }
    }

    fn str_global(&self, out: &mut String, idx: usize, s: &str) {
        Self::fmt_global(out, &format!("str{idx}"), s);
    }
}

impl MlirText {
    fn printf(b: &mut Buf, fmt: &str, arg: &str, ty: &str) {
        let p = b.tmp();
        b.line(&format!("{p} = llvm.mlir.addressof @{fmt} : !llvm.ptr"));
        let r = b.tmp();
        b.line(&format!(
            "{r} = llvm.call @printf({p}, {arg}) vararg(!llvm.func<i32 (ptr, ...)>) : (!llvm.ptr, {ty}) -> i32"
        ));
    }

    fn fmt_global(out: &mut String, name: &str, s: &str) {
        writeln!(
            out,
            "llvm.mlir.global internal constant @{name}(\"{}\\00\") : !llvm.array<{} x i8>",
            escape_str(s),
            s.len() + 1
        )
        .unwrap();
    }
}

fn i64s(n: usize) -> String {
    vec!["i64"; n].join(", ")
}

/// # Errors
/// Fails when a construct reaches codegen unlowered or unsupported, or when the
/// structural self-check rejects the emitted module.
pub fn emit(core: &Core, ctors: &BTreeMap<String, CtorInfo>) -> Result<String, String> {
    let text = emit_with(&MlirText, core, ctors)?;
    verify(&text)?;
    Ok(text)
}

/// Structural self-check, the text-backend analogue of the LLVM backend's
/// `m.verify()`. The real verifier runs downstream in `mlir-translate` (only
/// when the toolchain is installed); this catches gross emission bugs (an
/// unbalanced function body, a call to an undeclared symbol) with no external
/// dependency, so a malformed module is a structured error rather than a
/// confusing translator failure or a silent miscompile.
///
/// On rejection the offending module is kept at a stable temp path for
/// inspection, mirroring `emit_bitcode` on the LLVM side.
///
/// # Errors
/// Fails on an empty module, an unbalanced brace/paren nesting, a malformed
/// line, or a reference to a symbol that is never defined.
fn verify(text: &str) -> Result<(), String> {
    check(text).map_err(|e| {
        let kept = std::env::temp_dir().join("prism_failed.mlir");
        let _ = std::fs::write(&kept, text);
        format!(
            "MLIR self-check rejected module, kept at {}:\n{e}",
            kept.display()
        )
    })
}

fn check(text: &str) -> Result<(), String> {
    if text.trim().is_empty() {
        return Err("empty module".into());
    }

    // `@name` definitions: `llvm.func @f`, `llvm.mlir.global ... @g`. Both
    // forms put the symbol immediately after an `@` token at a fixed position,
    // so a single scan over `@`-prefixed words on definition lines suffices.
    let mut defined: BTreeSet<&str> = BTreeSet::new();
    for line in text.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("llvm.func @") {
            defined.insert(symbol(rest));
        } else if let Some(rest) = t.strip_prefix("llvm.mlir.global") {
            if let Some(at) = rest.find('@') {
                defined.insert(symbol(&rest[at + 1..]));
            }
        }
    }

    // Brace and paren nesting must net to zero and never dip below zero, and
    // every referenced `@symbol` must be defined. Both scans ignore characters
    // inside `"..."` string literals, where delimiters and `@`-bearing hygienic
    // names (e.g. an `unhandled effect get@i@0` message) appear verbatim and are
    // not MLIR tokens.
    let (mut braces, mut parens) = (0i64, 0i64);
    for (n, line) in text.lines().enumerate() {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        let mut in_str = false;
        let mut escaped = false;
        for (i, ch) in t.char_indices() {
            if in_str {
                if escaped {
                    escaped = false;
                } else if ch == '\\' {
                    escaped = true;
                } else if ch == '"' {
                    in_str = false;
                }
                continue;
            }
            match ch {
                '"' => in_str = true,
                '{' => braces += 1,
                '}' => braces -= 1,
                '(' => parens += 1,
                ')' => parens -= 1,
                '@' => {
                    // Skip the definition site itself; a defined name resolves.
                    let name = symbol(&t[i + 1..]);
                    if name.is_empty() {
                        return Err(format!("malformed symbol reference at line {}: {t}", n + 1));
                    }
                    if !defined.contains(name) {
                        return Err(format!(
                            "reference to undefined symbol @{name} at line {}: {t}",
                            n + 1
                        ));
                    }
                }
                _ => {}
            }
            if braces < 0 || parens < 0 {
                return Err(format!("unbalanced delimiter at line {}: {t}", n + 1));
            }
        }
    }
    if braces != 0 || parens != 0 {
        return Err(format!(
            "unbalanced module: brace depth {braces}, paren depth {parens}"
        ));
    }
    Ok(())
}

// The symbol name following an `@`: leading run of identifier characters
// (MLIR symbols here are alphanumeric plus `_` and `.`).
fn symbol(rest: &str) -> &str {
    let end = rest
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
        .unwrap_or(rest.len());
    &rest[..end]
}
