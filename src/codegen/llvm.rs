use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::path::Path;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};
use inkwell::types::FunctionType;
use inkwell::values::{
    BasicMetadataValueEnum, BasicValueEnum, CallSiteValue, FloatValue, FunctionValue, GlobalValue,
    IntValue, LLVMTailCallKind, PointerValue,
};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel};

use super::emit::{emit_with, idx64, Buf, IntOp, Isa};
use crate::core::Core;
use crate::types::CtorInfo;

/// Inkwell interpreter of the string `Isa`: SSA names map to live values,
/// labels to basic blocks, so the walker stays backend-neutral. Functions,
/// runtime declares, and globals materialize lazily on first reference.
struct Inkwell<'ctx> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    vals: RefCell<HashMap<String, BasicValueEnum<'ctx>>>,
    // Integer constants are uniqued by their value, kept apart from the
    // name-keyed `vals` map so a value-named constant cannot pollute the SSA
    // name space. LLVM constants are module-global, so this outlives the
    // per-function `vals` clear.
    consts: RefCell<HashMap<i64, BasicValueEnum<'ctx>>>,
    blocks: RefCell<HashMap<String, BasicBlock<'ctx>>>,
    func: Cell<Option<FunctionValue<'ctx>>>,
    // First codegen-internal failure (a builder error or an unbound SSA name).
    // Emission continues with a poison value so one bug surfaces as a single
    // structured error at the `emit` boundary instead of aborting the process.
    err: RefCell<Option<String>>,
}

fn nm(s: &str) -> &str {
    s.trim_start_matches('%')
}

fn ipred(p: &str) -> IntPredicate {
    match p {
        "eq" => IntPredicate::EQ,
        "ne" => IntPredicate::NE,
        "slt" => IntPredicate::SLT,
        "sle" => IntPredicate::SLE,
        "sgt" => IntPredicate::SGT,
        _ => IntPredicate::SGE,
    }
}

fn fpred(p: &str) -> FloatPredicate {
    match p {
        "oeq" => FloatPredicate::OEQ,
        "une" => FloatPredicate::UNE,
        "olt" => FloatPredicate::OLT,
        "ole" => FloatPredicate::OLE,
        "ogt" => FloatPredicate::OGT,
        _ => FloatPredicate::OGE,
    }
}

impl<'ctx> Inkwell<'ctx> {
    fn new(ctx: &'ctx Context) -> Self {
        let module = ctx.create_module("prism");
        if Target::initialize_native(&InitializationConfig::default()).is_ok() {
            let triple = TargetMachine::get_default_triple();
            module.set_triple(&triple);
            if let Some(tm) = Target::from_triple(&triple).ok().and_then(|t| {
                t.create_target_machine(
                    &triple,
                    "generic",
                    "",
                    OptimizationLevel::Default,
                    RelocMode::Default,
                    CodeModel::Default,
                )
            }) {
                module.set_data_layout(&tm.get_target_data().get_data_layout());
            }
        }
        Self {
            ctx,
            module,
            builder: ctx.create_builder(),
            vals: RefCell::default(),
            consts: RefCell::default(),
            blocks: RefCell::default(),
            func: Cell::new(None),
            err: RefCell::default(),
        }
    }

    // Record the first codegen-internal failure; later ones are dropped so the
    // surfaced message names the original cause.
    fn ice(&self, msg: &str) {
        let mut slot = self.err.borrow_mut();
        if slot.is_none() {
            *slot = Some(format!("ICE: {msg}"));
        }
    }

    // Poison values returned for a failed builder op so emission stays total.
    // The recorded `err` makes the result unusable, so the poison only has to
    // type-check.
    fn pint(&self, what: &str, e: &BuilderError) -> IntValue<'ctx> {
        self.ice(&format!("{what}: {e}"));
        self.i64t().const_zero()
    }

    fn pflt(&self, what: &str, e: &BuilderError) -> FloatValue<'ctx> {
        self.ice(&format!("{what}: {e}"));
        self.ctx.f64_type().const_zero()
    }

    fn pptr(&self, what: &str, e: &BuilderError) -> PointerValue<'ctx> {
        self.ice(&format!("{what}: {e}"));
        self.ptr_t().const_null()
    }

    fn pval(&self, what: &str, e: &BuilderError) -> BasicValueEnum<'ctx> {
        self.ice(&format!("{what}: {e}"));
        self.i64t().const_zero().into()
    }

    // A statement-position builder op (branch, store, ret): record a failure and
    // drop the instruction value, which the caller never uses.
    fn act<T>(&self, what: &str, r: Result<T, BuilderError>) {
        if let Err(e) = r {
            self.ice(&format!("{what}: {e}"));
        }
    }

    // The current function, set by `fn_define` before any block is opened. If
    // unset (a structural invariant the walker upholds), record an ICE and host
    // the orphan block in a private placeholder so emission stays total instead
    // of panicking.
    fn cur_fn(&self) -> FunctionValue<'ctx> {
        self.func.get().unwrap_or_else(|| {
            self.ice("block emitted outside any function");
            self.module
                .get_function(".orphan")
                .unwrap_or_else(|| self.module.add_function(".orphan", self.i64_fn(0), None))
        })
    }

    fn i64t(&self) -> inkwell::types::IntType<'ctx> {
        self.ctx.i64_type()
    }

    fn ptr_t(&self) -> inkwell::types::PointerType<'ctx> {
        self.ctx.ptr_type(AddressSpace::default())
    }

    fn i64_fn(&self, arity: usize) -> FunctionType<'ctx> {
        self.i64t().fn_type(&vec![self.i64t().into(); arity], false)
    }

    fn get(&self, n: &str) -> BasicValueEnum<'ctx> {
        if let Some(v) = n.strip_prefix("$c").and_then(|d| d.parse::<i64>().ok()) {
            if let Some(c) = self.consts.borrow().get(&v).copied() {
                return c;
            }
        }
        self.vals.borrow().get(n).copied().unwrap_or_else(|| {
            self.ice(&format!("unbound ssa {n}"));
            self.i64t().const_zero().into()
        })
    }

    fn int(&self, n: &str) -> IntValue<'ctx> {
        self.get(n).into_int_value()
    }

    fn flt(&self, n: &str) -> FloatValue<'ctx> {
        self.get(n).into_float_value()
    }

    fn pv(&self, n: &str) -> PointerValue<'ctx> {
        self.get(n).into_pointer_value()
    }

    fn set(&self, n: &str, v: BasicValueEnum<'ctx>) {
        self.vals.borrow_mut().insert(n.to_string(), v);
    }

    fn block(&self, l: &str) -> BasicBlock<'ctx> {
        if let Some(bb) = self.blocks.borrow().get(l) {
            return *bb;
        }
        let f = self.cur_fn();
        let bb = self.ctx.append_basic_block(f, l);
        self.blocks.borrow_mut().insert(l.to_string(), bb);
        bb
    }

    fn decl(&self, name: &str, ty: FunctionType<'ctx>) -> FunctionValue<'ctx> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, ty, None))
    }

    fn call_direct(
        &self,
        f: FunctionValue<'ctx>,
        args: &[BasicMetadataValueEnum<'ctx>],
        name: &str,
    ) -> Option<CallSiteValue<'ctx>> {
        // The walker positions the builder at a block before any call, so a
        // failure here breaks a structural invariant; record an ICE and return
        // `None` rather than panicking, keeping emission total.
        self.builder
            .build_call(f, args, name)
            .map_err(|e| self.ice(&format!("call: {e}")))
            .ok()
    }

    // Extract the call's basic result. A missing call (builder failure) or a
    // void result (a value-returning builtin mis-declared) is recorded and
    // poisoned with i64 zero rather than panicking, like the other fallbacks.
    fn cs_basic(&self, cs: Option<CallSiteValue<'ctx>>) -> BasicValueEnum<'ctx> {
        cs.and_then(|cs| cs.try_as_basic_value().basic())
            .unwrap_or_else(|| {
                self.ice("call returned void where a value was expected");
                self.i64t().const_zero().into()
            })
    }

    fn call_named(&self, fname: &str, ty: FunctionType<'ctx>, args: &[String], dst: &str) {
        let f = self.decl(fname, ty);
        let margs: Vec<BasicMetadataValueEnum<'ctx>> =
            args.iter().map(|a| self.get(a).into()).collect();
        let cs = self.call_direct(f, &margs, nm(dst));
        if !dst.is_empty() {
            self.set(dst, self.cs_basic(cs));
        }
    }

    fn str_gl(&self, idx: usize, size: usize) -> GlobalValue<'ctx> {
        let name = format!(".str{idx}");
        self.module.get_global(&name).unwrap_or_else(|| {
            let len = u32::try_from(size).unwrap_or_else(|_| {
                self.ice("string literal exceeds u32 length");
                u32::MAX
            });
            let ty = self.ctx.i8_type().array_type(len);
            self.module.add_global(ty, None, &name)
        })
    }

    fn cstr_global(&self, name: &str, bytes: &[u8]) -> GlobalValue<'ctx> {
        self.module.get_global(name).unwrap_or_else(|| {
            let init = self.ctx.const_string(bytes, true);
            let g = self.module.add_global(init.get_type(), None, name);
            g.set_initializer(&init);
            g.set_constant(true);
            g.set_linkage(Linkage::Private);
            g
        })
    }

    fn printf(&self, fmt_name: &str, fmt: &[u8], arg: BasicMetadataValueEnum<'ctx>) {
        let pf = self.decl(
            "printf",
            self.ctx.i32_type().fn_type(&[self.ptr_t().into()], true),
        );
        let g = self.cstr_global(fmt_name, fmt);
        self.call_direct(pf, &[g.as_pointer_value().into(), arg], "");
    }
}

impl Isa for Inkwell<'_> {
    fn const_int(&self, _b: &mut Buf, n: i64) -> String {
        self.consts
            .borrow_mut()
            .entry(n)
            .or_insert_with(|| self.i64t().const_int(n.cast_unsigned(), false).into());
        format!("$c{n}")
    }

    fn const_float(&self, b: &mut Buf, f: f64) -> String {
        let t = b.tmp();
        self.set(&t, self.ctx.f64_type().const_float(f).into());
        t
    }

    fn fresh_zero(&self, b: &mut Buf) -> String {
        let t = b.tmp();
        self.set(&t, self.i64t().const_zero().into());
        t
    }

    fn str_lit(&self, _b: &mut Buf, dst: &str, idx: usize, len: usize) {
        let g = self.str_gl(idx, len + 1);
        let f = self.decl(
            "prism_str_lit",
            self.i64t()
                .fn_type(&[self.ptr_t().into(), self.i64t().into()], false),
        );
        let n = self.i64t().const_int(idx64(len).cast_unsigned(), false);
        let cs = self.call_direct(f, &[g.as_pointer_value().into(), n.into()], nm(dst));
        self.set(dst, self.cs_basic(cs));
    }

    fn bin(&self, _b: &mut Buf, dst: &str, op: IntOp, x: &str, y: &str) {
        let (x, y) = (self.int(x), self.int(y));
        let bld = &self.builder;
        let r = match op {
            IntOp::Add => bld.build_int_add(x, y, nm(dst)),
            IntOp::Sub => bld.build_int_sub(x, y, nm(dst)),
            IntOp::And => bld.build_and(x, y, nm(dst)),
            IntOp::Or => bld.build_or(x, y, nm(dst)),
            IntOp::Shl => bld.build_left_shift(x, y, nm(dst)),
            IntOp::Ashr => bld.build_right_shift(x, y, true, nm(dst)),
        };
        self.set(dst, r.unwrap_or_else(|e| self.pint("bin", &e)).into());
    }

    fn fbin(&self, _b: &mut Buf, dst: &str, op: &str, x: &str, y: &str) {
        let (x, y) = (self.flt(x), self.flt(y));
        let bld = &self.builder;
        let r = match op {
            "fadd" => bld.build_float_add(x, y, nm(dst)),
            "fsub" => bld.build_float_sub(x, y, nm(dst)),
            "fmul" => bld.build_float_mul(x, y, nm(dst)),
            _ => bld.build_float_div(x, y, nm(dst)),
        };
        self.set(dst, r.unwrap_or_else(|e| self.pflt("fbin", &e)).into());
    }

    fn icmp(&self, _b: &mut Buf, dst: &str, pred: &str, x: &str, y: &str) {
        let r = self
            .builder
            .build_int_compare(ipred(pred), self.int(x), self.int(y), nm(dst))
            .unwrap_or_else(|e| self.pint("icmp", &e));
        self.set(dst, r.into());
    }

    fn fcmp(&self, _b: &mut Buf, dst: &str, pred: &str, x: &str, y: &str) {
        let r = self
            .builder
            .build_float_compare(fpred(pred), self.flt(x), self.flt(y), nm(dst))
            .unwrap_or_else(|e| self.pint("fcmp", &e));
        self.set(dst, r.into());
    }

    fn zext(&self, _b: &mut Buf, dst: &str, c: &str) {
        let r = self
            .builder
            .build_int_z_extend(self.int(c), self.i64t(), nm(dst))
            .unwrap_or_else(|e| self.pint("zext", &e));
        self.set(dst, r.into());
    }

    fn sitofp(&self, _b: &mut Buf, dst: &str, v: &str) {
        let r = self
            .builder
            .build_signed_int_to_float(self.int(v), self.ctx.f64_type(), nm(dst))
            .unwrap_or_else(|e| self.pflt("sitofp", &e));
        self.set(dst, r.into());
    }

    fn fptosi(&self, _b: &mut Buf, dst: &str, v: &str) {
        let r = self
            .builder
            .build_float_to_signed_int(self.flt(v), self.i64t(), nm(dst))
            .unwrap_or_else(|e| self.pint("fptosi", &e));
        self.set(dst, r.into());
    }

    fn cast_i2f(&self, _b: &mut Buf, dst: &str, v: &str) {
        let r = self
            .builder
            .build_bit_cast(self.int(v), self.ctx.f64_type(), nm(dst))
            .unwrap_or_else(|e| self.pval("bitcast", &e));
        self.set(dst, r);
    }

    fn cast_f2i(&self, _b: &mut Buf, dst: &str, v: &str) {
        let r = self
            .builder
            .build_bit_cast(self.flt(v), self.i64t(), nm(dst))
            .unwrap_or_else(|e| self.pval("bitcast", &e));
        self.set(dst, r);
    }

    fn f_intrinsic(&self, _b: &mut Buf, dst: &str, name: &str, a: &str) {
        let f64t = self.ctx.f64_type();
        let f = self.decl(
            &format!("llvm.{name}.f64"),
            f64t.fn_type(&[f64t.into()], false),
        );
        let cs = self.call_direct(f, &[self.flt(a).into()], nm(dst));
        self.set(dst, self.cs_basic(cs));
    }

    fn inttoptr(&self, _b: &mut Buf, dst: &str, v: &str) {
        let r = self
            .builder
            .build_int_to_ptr(self.int(v), self.ptr_t(), nm(dst))
            .unwrap_or_else(|e| self.pptr("inttoptr", &e));
        self.set(dst, r.into());
    }

    fn ptrtoint(&self, _b: &mut Buf, dst: &str, p: &str) {
        let r = self
            .builder
            .build_ptr_to_int(self.pv(p), self.i64t(), nm(dst))
            .unwrap_or_else(|e| self.pint("ptrtoint", &e));
        self.set(dst, r.into());
    }

    fn alloca_word(&self, _b: &mut Buf, dst: &str) {
        let r = self
            .builder
            .build_alloca(self.i64t(), nm(dst))
            .unwrap_or_else(|e| self.pptr("alloca", &e));
        self.set(dst, r.into());
    }

    // Byte offsets as ptrtoint/add/inttoptr: the safe builder surface has no
    // gep, and instcombine folds this back to `gep i8` under -O2.
    fn gep(&self, _b: &mut Buf, dst: &str, p: &str, off: i64) {
        let base = self
            .builder
            .build_ptr_to_int(self.pv(p), self.i64t(), "")
            .unwrap_or_else(|e| self.pint("gep", &e));
        let o = self.i64t().const_int(off.cast_unsigned(), false);
        let sum = self
            .builder
            .build_int_add(base, o, "")
            .unwrap_or_else(|e| self.pint("gep", &e));
        let r = self
            .builder
            .build_int_to_ptr(sum, self.ptr_t(), nm(dst))
            .unwrap_or_else(|e| self.pptr("gep", &e));
        self.set(dst, r.into());
    }

    fn load(&self, _b: &mut Buf, dst: &str, p: &str) {
        let r = self
            .builder
            .build_load(self.i64t(), self.pv(p), nm(dst))
            .unwrap_or_else(|e| self.pval("load", &e));
        self.set(dst, r);
    }

    fn store(&self, _b: &mut Buf, v: &str, p: &str) {
        self.act("store", self.builder.build_store(self.pv(p), self.int(v)));
    }

    fn call(&self, _b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        self.call_named(f, self.i64_fn(args.len()), args, dst);
    }

    fn call_ptr(&self, _b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        let ty = self
            .ptr_t()
            .fn_type(&vec![self.i64t().into(); args.len()], false);
        self.call_named(f, ty, args, dst);
    }

    fn call_void(&self, _b: &mut Buf, f: &str, args: &[String]) {
        let ty = self
            .ctx
            .void_type()
            .fn_type(&vec![self.i64t().into(); args.len()], false);
        self.call_named(f, ty, args, "");
    }

    // `musttail` is a hard guarantee, not a hint: LLVM either emits a tail call
    // or fails compilation, so a TRMC/handler loop can never silently degrade to
    // a stack-growing call. The structural preconditions (matching signature, the
    // call in tail position followed by `ret`) are enforced by `Module::verify`,
    // which `emit_bitcode` runs before lowering; a violation is a loud verifier
    // error with the offending IR kept on disk, never a runtime overflow.
    fn musttail_call(&self, _b: &mut Buf, dst: &str, f: &str, args: &[String]) {
        let f = self.decl(f, self.i64_fn(args.len()));
        let margs: Vec<BasicMetadataValueEnum<'_>> =
            args.iter().map(|a| self.get(a).into()).collect();
        let cs = self.call_direct(f, &margs, nm(dst));
        if let Some(cs) = cs {
            cs.set_tail_call_kind(LLVMTailCallKind::LLVMTailCallKindMustTail);
        }
        self.set(dst, self.cs_basic(cs));
    }

    fn printf_float(&self, _b: &mut Buf, v: &str) {
        self.printf(".fmtf", b"%g", self.flt(v).into());
    }

    fn printf_str(&self, _b: &mut Buf, p: &str) {
        self.printf(".fmts", b"%s", self.pv(p).into());
    }

    fn exit_with(&self, _b: &mut Buf, v: &str) {
        let i32t = self.ctx.i32_type();
        let c = self
            .builder
            .build_int_truncate(self.int(v), i32t, "")
            .unwrap_or_else(|e| self.pint("trunc", &e));
        let ex = self.decl("exit", self.ctx.void_type().fn_type(&[i32t.into()], false));
        self.call_direct(ex, &[c.into()], "");
    }

    fn jump(&self, _b: &mut Buf, l: &str) {
        self.act("br", self.builder.build_unconditional_branch(self.block(l)));
    }

    fn cond_br(&self, _b: &mut Buf, c: &str, lt: &str, lf: &str) {
        self.act(
            "condbr",
            self.builder
                .build_conditional_branch(self.int(c), self.block(lt), self.block(lf)),
        );
    }

    fn switch(&self, _b: &mut Buf, v: &str, default: &str, cases: &[(i64, String)]) {
        let cs: Vec<(IntValue<'_>, BasicBlock<'_>)> = cases
            .iter()
            .map(|(n, l)| {
                (
                    self.i64t().const_int(n.cast_unsigned(), false),
                    self.block(l),
                )
            })
            .collect();
        self.act(
            "switch",
            self.builder
                .build_switch(self.int(v), self.block(default), &cs),
        );
    }

    fn unreachable(&self, _b: &mut Buf) {
        self.act("unreachable", self.builder.build_unreachable());
    }

    fn ret(&self, _b: &mut Buf, v: &str) {
        self.act("ret", self.builder.build_return(Some(&self.int(v))));
    }

    fn open_entry(&self, b: &mut Buf) {
        let f = self.cur_fn();
        let bb = self.ctx.append_basic_block(f, "entry");
        self.blocks.borrow_mut().insert("entry".into(), bb);
        self.builder.position_at_end(bb);
        b.cur = "entry".into();
    }

    fn open_block(&self, b: &mut Buf, l: &str) {
        self.builder.position_at_end(self.block(l));
        b.cur = l.to_string();
    }

    fn jump_merge(&self, b: &mut Buf, l: &str, _v: &str) {
        self.jump(b, l);
    }

    fn open_merge(&self, b: &mut Buf, l: &str, dst: &str, preds: &[(String, String)]) {
        self.open_block(b, l);
        match self.builder.build_phi(self.i64t(), nm(dst)) {
            Ok(phi) => {
                for (v, lbl) in preds {
                    phi.add_incoming(&[(&self.get(v), self.block(lbl))]);
                }
                self.set(dst, phi.as_basic_value());
            }
            Err(e) => {
                self.ice(&format!("phi: {e}"));
                self.set(dst, self.i64t().const_zero().into());
            }
        }
    }

    fn fn_define(&self, name: &str, params: &[String]) -> String {
        let f = self.decl(name, self.i64_fn(params.len()));
        self.func.set(Some(f));
        self.vals.borrow_mut().clear();
        self.blocks.borrow_mut().clear();
        for (i, p) in params.iter().enumerate() {
            let idx = u32::try_from(i).unwrap_or(u32::MAX);
            if let Some(arg) = f.get_nth_param(idx) {
                arg.set_name(nm(p));
                self.set(p, arg);
            } else {
                self.ice(&format!("function `{name}` parameter {i} out of range"));
            }
        }
        String::new()
    }

    fn fn_close(&self) -> String {
        String::new()
    }

    // Declarations and globals are created at first use, so the up-front
    // prelude of the textual backends has nothing left to do.
    fn prelude(&self, _out: &mut String, _seen: &mut std::collections::BTreeSet<String>) {}

    fn declare(
        &self,
        _out: &mut String,
        _seen: &mut std::collections::BTreeSet<String>,
        sym: &str,
        arity: usize,
    ) {
        // inkwell dedups via get-or-add, so the `seen` set is unused here.
        self.decl(sym, self.i64_fn(arity));
    }

    fn str_global(&self, _out: &mut String, idx: usize, s: &str) {
        let g = self.str_gl(idx, s.len() + 1);
        g.set_initializer(&self.ctx.const_string(s.as_bytes(), true));
        g.set_constant(true);
        g.set_linkage(Linkage::Private);
    }
}

fn with_module<T>(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    f: impl FnOnce(&Module<'_>) -> Result<T, String>,
) -> Result<T, String> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx);
    emit_with(&isa, core, ctors)?;
    // Surface the first codegen-internal failure captured during emission as a
    // structured error instead of a panic at the original site.
    if let Some(e) = isa.err.borrow_mut().take() {
        return Err(e);
    }
    f(&isa.module)
}

/// # Errors
/// Fails when a construct reaches codegen unlowered or unsupported.
pub fn emit(core: &Core, ctors: &BTreeMap<String, CtorInfo>) -> Result<String, String> {
    with_module(core, ctors, |m| Ok(m.print_to_string().to_string()))
}

/// Verify the module and write LLVM bitcode to `bc`. On verifier failure the
/// textual IR is kept at a stable temp path for inspection.
///
/// # Errors
/// Fails on codegen failure, a verifier rejection, or an unwritable path.
pub fn emit_bitcode(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    bc: &Path,
) -> Result<(), String> {
    with_module(core, ctors, |m| {
        if let Err(e) = m.verify() {
            let kept = std::env::temp_dir().join("prism_failed.ll");
            let _ = std::fs::write(&kept, m.print_to_string().to_string());
            return Err(format!(
                "LLVM verifier rejected module, kept at {}:\n{}",
                kept.display(),
                e
            ));
        }
        if m.write_bitcode_to_path(bc) {
            Ok(())
        } else {
            Err(format!("cannot write bitcode to {}", bc.display()))
        }
    })
}
