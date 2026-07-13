use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::path::Path;

use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};
use inkwell::types::FunctionType;
use inkwell::values::{
    AnyValue, BasicMetadataValueEnum, BasicValueEnum, CallSiteValue, FloatValue, FunctionValue,
    GlobalValue, IntValue, LLVMTailCallKind, PointerValue, StructValue,
};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel};

use super::abi::idx64;
use super::emit::{
    closure_summary_with_isa, emit_closure_adapters_with_isa, emit_closure_dispatch_with_isa,
    emit_selected_plan_with_isa, emit_selected_with_isa, emit_with_isa,
    plan_closures_from_summaries_with_isa, plan_closures_with_isa, ClosurePlan, ClosureSummary,
    SelectedEmissionError,
};
use super::isa::{Buf, Cmp, FloatBinOp, FloatIntrinsic, IntOp, Isa};
use super::native_kont;
use super::rt;
use crate::core::{Core, LoweredCore};
use crate::sym::Sym;
use crate::types::CtorInfo;

const LLVM_USED_GLOBAL: &str = "llvm.used";
const LLVM_METADATA_SECTION: &str = "llvm.metadata";

#[derive(Clone)]
struct NativeKontFunction {
    symbol: String,
    params: Vec<String>,
}

/// Inkwell interpreter of the string `Isa`: SSA names map to live values,
/// labels to basic blocks, so the walker stays backend-neutral. Functions,
/// runtime declares, and globals materialize lazily on first reference.
struct Inkwell<'ctx> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    vals: RefCell<HashMap<String, BasicValueEnum<'ctx>>>,
    blocks: RefCell<HashMap<String, BasicBlock<'ctx>>>,
    func: Cell<Option<FunctionValue<'ctx>>>,
    native_kont_enabled: bool,
    native_kont_func: RefCell<Option<NativeKontFunction>>,
    pending_musttail: Cell<bool>,
    // First codegen-internal failure (a builder error or an unbound SSA name).
    // Emission continues with a poison value so one bug surfaces as a single
    // structured error at the `emit` boundary instead of aborting the process.
    err: RefCell<Option<String>>,
}

fn nm(s: &str) -> &str {
    s.trim_start_matches('%')
}

impl<'ctx> Inkwell<'ctx> {
    fn new(ctx: &'ctx Context, native_kont_enabled: bool) -> Self {
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
            blocks: RefCell::default(),
            func: Cell::new(None),
            native_kont_enabled,
            native_kont_func: RefCell::default(),
            pending_musttail: Cell::new(false),
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

    // Every function in a Prism module is non-unwinding: the language has no
    // exceptions and this backend emits no invokes/landingpads, so nothing
    // (generated bodies, C runtime, libc/intrinsic decls) can unwind. Marking it
    // lets `-O2` drop unwind tables and treat every call as non-throwing, which
    // enables freer code motion and smaller objects.
    fn set_nounwind(&self, f: FunctionValue<'ctx>) {
        let kind = Attribute::get_named_enum_kind_id("nounwind");
        f.add_attribute(
            AttributeLoc::Function,
            self.ctx.create_enum_attribute(kind, 0),
        );
    }

    fn decl(&self, name: &str, ty: FunctionType<'ctx>) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function(name) {
            return f;
        }
        let f = self.module.add_function(name, ty, None);
        self.set_nounwind(f);
        f
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

    fn call_void_typed(
        &self,
        fname: &str,
        ty: FunctionType<'ctx>,
        args: &[BasicMetadataValueEnum<'ctx>],
    ) {
        let f = self.decl(fname, ty);
        let _ = self.call_direct(f, args, "");
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

    fn native_kont_symbol_ptr(&self, symbol: &str) -> PointerValue<'ctx> {
        let global_name = format!(".kont.shadow.{symbol}");
        self.cstr_global(&global_name, symbol.as_bytes())
            .as_pointer_value()
    }

    fn native_kont_enter_current(&self) {
        if !self.native_kont_enabled {
            return;
        }
        let Some(frame) = self.native_kont_func.borrow().clone() else {
            return;
        };
        self.native_kont_enter_symbol(&frame.symbol, frame.params.len());
        for (index, param) in frame.params.iter().enumerate() {
            self.native_kont_arg_value(index, self.int(param));
        }
    }

    fn native_kont_enter_symbol(&self, symbol: &str, arity: usize) {
        let args = [
            self.native_kont_symbol_ptr(symbol).into(),
            self.i64t()
                .const_int(u64::try_from(arity).unwrap_or(u64::MAX), false)
                .into(),
        ];
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.ptr_t().into(), self.i64t().into()], false);
        self.call_void_typed(rt::NATIVE_KONT_ENTER, ty, &args);
    }

    fn native_kont_tailcall_symbol(&self, symbol: &str, arity: usize) {
        if !self.native_kont_enabled {
            return;
        }
        let args = [
            self.native_kont_symbol_ptr(symbol).into(),
            self.i64t()
                .const_int(u64::try_from(arity).unwrap_or(u64::MAX), false)
                .into(),
        ];
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.ptr_t().into(), self.i64t().into()], false);
        self.call_void_typed(rt::NATIVE_KONT_TAILCALL, ty, &args);
    }

    fn native_kont_arg_value(&self, index: usize, value: IntValue<'ctx>) {
        if !self.native_kont_enabled {
            return;
        }
        let args = [
            self.i64t()
                .const_int(u64::try_from(index).unwrap_or(u64::MAX), false)
                .into(),
            value.into(),
        ];
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.i64t().into(), self.i64t().into()], false);
        self.call_void_typed(rt::NATIVE_KONT_ARG, ty, &args);
    }

    fn native_kont_leave_current(&self) {
        if !self.native_kont_enabled {
            return;
        }
        let ty = self.ctx.void_type().fn_type(&[], false);
        self.call_void_typed(rt::NATIVE_KONT_LEAVE, ty, &[]);
    }

    fn retain_globals(&self, globals: &[GlobalValue<'ctx>]) {
        if globals.is_empty() {
            return;
        }
        let pointers: Vec<PointerValue<'ctx>> =
            globals.iter().map(|g| g.as_pointer_value()).collect();
        let used = self.module.get_global(LLVM_USED_GLOBAL).unwrap_or_else(|| {
            self.module.add_global(
                self.ptr_t()
                    .array_type(u32::try_from(pointers.len()).unwrap_or(u32::MAX)),
                None,
                LLVM_USED_GLOBAL,
            )
        });
        used.set_initializer(&self.ptr_t().const_array(&pointers));
        used.set_linkage(Linkage::Appending);
        used.set_section(Some(LLVM_METADATA_SECTION));
    }

    fn native_kont_ptrs_global(&self, table: &str) -> Vec<GlobalValue<'ctx>> {
        let entry_t = self.ctx.struct_type(
            &[
                self.ptr_t().into(),
                self.ptr_t().into(),
                self.ptr_t().into(),
                self.ptr_t().into(),
            ],
            false,
        );
        let mut entries: Vec<StructValue<'ctx>> = Vec::new();
        for (i, row) in native_kont::rows(table).enumerate() {
            let Some(f) = self.module.get_function(row.symbol) else {
                continue;
            };
            let symbol = self.cstr_global(&format!(".kont_symbol{i}"), row.symbol.as_bytes());
            let hash = self.cstr_global(&format!(".kont_hash{i}"), row.def_hash.as_bytes());
            let core_name = self.cstr_global(&format!(".kont_name{i}"), row.core_name.as_bytes());
            entries.push(self.ctx.const_struct(
                &[
                    f.as_global_value().as_pointer_value().into(),
                    symbol.as_pointer_value().into(),
                    hash.as_pointer_value().into(),
                    core_name.as_pointer_value().into(),
                ],
                false,
            ));
        }
        if entries.is_empty() {
            return Vec::new();
        }

        let init = entry_t.const_array(&entries);
        let ptrs = self
            .module
            .get_global(native_kont::PTRS_GLOBAL)
            .unwrap_or_else(|| {
                self.module
                    .add_global(init.get_type(), None, native_kont::PTRS_GLOBAL)
            });
        ptrs.set_initializer(&init);
        ptrs.set_constant(true);
        ptrs.set_linkage(Linkage::External);
        ptrs.set_section(Some(native_kont::TABLE_SECTION));
        ptrs.set_alignment(8);

        let len_init = self
            .i64t()
            .const_int(u64::try_from(entries.len()).unwrap_or(u64::MAX), false);
        let len = self
            .module
            .get_global(native_kont::PTRS_LEN_GLOBAL)
            .unwrap_or_else(|| {
                self.module
                    .add_global(self.i64t(), None, native_kont::PTRS_LEN_GLOBAL)
            });
        len.set_initializer(&len_init);
        len.set_constant(true);
        len.set_linkage(Linkage::External);
        len.set_section(Some(native_kont::TABLE_SECTION));
        len.set_alignment(8);
        vec![ptrs, len]
    }

    fn native_kont_table_global(&self, core: &Core, table: &str) {
        let init = self.ctx.const_string(table.as_bytes(), true);
        let global = self
            .module
            .get_global(native_kont::TABLE_GLOBAL)
            .unwrap_or_else(|| {
                self.module
                    .add_global(init.get_type(), None, native_kont::TABLE_GLOBAL)
            });
        global.set_initializer(&init);
        global.set_constant(true);
        global.set_linkage(Linkage::External);
        global.set_section(Some(native_kont::TABLE_SECTION));
        global.set_alignment(1);
        let state_map = native_kont::state_map(core, table);
        let state_init = self.ctx.const_string(state_map.as_bytes(), true);
        let state_global = self
            .module
            .get_global(native_kont::STATE_MAP_GLOBAL)
            .unwrap_or_else(|| {
                self.module
                    .add_global(state_init.get_type(), None, native_kont::STATE_MAP_GLOBAL)
            });
        state_global.set_initializer(&state_init);
        state_global.set_constant(true);
        state_global.set_linkage(Linkage::External);
        state_global.set_section(Some(native_kont::TABLE_SECTION));
        state_global.set_alignment(1);
        let mut retained = vec![global, state_global];
        retained.extend(self.native_kont_ptrs_global(table));
        self.retain_globals(&retained);
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
    fn const_int(&self, b: &mut Buf, n: i64) -> String {
        let t = b.tmp();
        self.set(&t, self.i64t().const_int(n.cast_unsigned(), false).into());
        t
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
            rt::STR_LIT,
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

    fn fbin(&self, _b: &mut Buf, dst: &str, op: FloatBinOp, x: &str, y: &str) {
        let (x, y) = (self.flt(x), self.flt(y));
        let bld = &self.builder;
        let r = match op {
            FloatBinOp::Fadd => bld.build_float_add(x, y, nm(dst)),
            FloatBinOp::Fsub => bld.build_float_sub(x, y, nm(dst)),
            FloatBinOp::Fmul => bld.build_float_mul(x, y, nm(dst)),
            FloatBinOp::Fdiv => bld.build_float_div(x, y, nm(dst)),
        };
        self.set(dst, r.unwrap_or_else(|e| self.pflt("fbin", &e)).into());
    }

    fn icmp(&self, _b: &mut Buf, dst: &str, pred: Cmp, x: &str, y: &str) {
        let p = match pred {
            Cmp::Eq => IntPredicate::EQ,
            Cmp::Ne => IntPredicate::NE,
            Cmp::Lt => IntPredicate::SLT,
            Cmp::Le => IntPredicate::SLE,
            Cmp::Gt => IntPredicate::SGT,
            Cmp::Ge => IntPredicate::SGE,
        };
        let r = self
            .builder
            .build_int_compare(p, self.int(x), self.int(y), nm(dst))
            .unwrap_or_else(|e| self.pint("icmp", &e));
        self.set(dst, r.into());
    }

    fn fcmp(&self, _b: &mut Buf, dst: &str, pred: Cmp, x: &str, y: &str) {
        let p = match pred {
            Cmp::Eq => FloatPredicate::OEQ,
            Cmp::Ne => FloatPredicate::UNE,
            Cmp::Lt => FloatPredicate::OLT,
            Cmp::Le => FloatPredicate::OLE,
            Cmp::Gt => FloatPredicate::OGT,
            Cmp::Ge => FloatPredicate::OGE,
        };
        let r = self
            .builder
            .build_float_compare(p, self.flt(x), self.flt(y), nm(dst))
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

    fn fptosi_sat(&self, _b: &mut Buf, dst: &str, v: &str) {
        // `llvm.fptosi.sat` is the saturating conversion (clamp to i64::MIN/MAX,
        // NaN -> 0), matching Rust's `f as i64` in the interpreter. inkwell has no
        // direct builder for it, so declare and call the intrinsic.
        let i64t = self.i64t();
        let f64t = self.ctx.f64_type();
        let f = self.decl(
            "llvm.fptosi.sat.i64.f64",
            i64t.fn_type(&[f64t.into()], false),
        );
        let cs = self.call_direct(f, &[self.flt(v).into()], nm(dst));
        self.set(dst, self.cs_basic(cs));
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

    fn f_intrinsic(&self, _b: &mut Buf, dst: &str, op: FloatIntrinsic, a: &str) {
        let f64t = self.ctx.f64_type();
        let f = self.decl(
            &format!("llvm.{}.f64", op.name()),
            f64t.fn_type(&[f64t.into()], false),
        );
        let cs = self.call_direct(f, &[self.flt(a).into()], nm(dst));
        self.set(dst, self.cs_basic(cs));
    }

    fn f_call1(&self, _b: &mut Buf, dst: &str, sym: &str, a: &str) {
        let f64t = self.ctx.f64_type();
        let f = self.decl(sym, f64t.fn_type(&[f64t.into()], false));
        let cs = self.call_direct(f, &[self.flt(a).into()], nm(dst));
        self.set(dst, self.cs_basic(cs));
    }

    // inkwell declares functions on first use (in `f_call1`), so no module-level
    // pre-declaration is needed for the LLVM backend.
    fn declare_f(
        &self,
        _out: &mut String,
        _seen: &mut std::collections::BTreeSet<String>,
        _sym: &str,
    ) {
    }

    fn fneg(&self, _b: &mut Buf, dst: &str, x: &str) {
        let r = self
            .builder
            .build_float_neg(self.flt(x), nm(dst))
            .unwrap_or_else(|e| self.pflt("fneg", &e));
        self.set(dst, r.into());
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

    // A real `getelementptr inbounds i8, ptr p, i64 off`, indexing an `i8` element
    // type so the byte offset is literal. This preserves pointer provenance and the
    // `inbounds` guarantee, which the prior `ptrtoint`/`add`/`inttoptr` form
    // discarded (leaving alias analysis to a `-O2` instcombine fold-back).
    //
    // This is one of the crate's audited `unsafe` sites (see `[lints.rust]` in
    // Cargo.toml). inkwell marks every indexed-gep builder `unsafe` because it
    // cannot check the indices stay in bounds of the pointee, and there is no safe
    // equivalent for a dynamic byte offset (`build_struct_gep` needs a static field
    // index, which the variable-arity cell fields and string payload do not have).
    #[allow(unsafe_code)]
    fn gep(&self, _b: &mut Buf, dst: &str, p: &str, off: i64) {
        let o = self.i64t().const_int(off.cast_unsigned(), false);
        // SAFETY: `off` is always a header/field/payload byte offset produced by
        // the emitter for a cell it just allocated with enough words (TAG_OFF, or
        // HDR_BYTES + field*WORD_BYTES, all within the cell's `prism_alloc` size),
        // so the resulting pointer is in bounds. `i8` element type makes `off` a
        // literal byte count; `p` is a live cell pointer.
        let r = unsafe {
            self.builder
                .build_in_bounds_gep(self.ctx.i8_type(), self.pv(p), &[o], nm(dst))
        }
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
        self.native_kont_tailcall_symbol(f, args.len());
        for (index, arg) in args.iter().enumerate() {
            self.native_kont_arg_value(index, self.int(arg));
        }
        let f = self.decl(f, self.i64_fn(args.len()));
        let margs: Vec<BasicMetadataValueEnum<'_>> =
            args.iter().map(|a| self.get(a).into()).collect();
        let cs = self.call_direct(f, &margs, nm(dst));
        if let Some(cs) = cs {
            cs.set_tail_call_kind(LLVMTailCallKind::LLVMTailCallKindMustTail);
        }
        self.pending_musttail.set(true);
        self.set(dst, self.cs_basic(cs));
    }

    fn printf_str(&self, _b: &mut Buf, p: &str) {
        self.printf(".fmts", b"%s", self.pv(p).into());
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
        if self.pending_musttail.replace(false) {
            self.act("ret", self.builder.build_return(Some(&self.int(v))));
            return;
        }
        self.native_kont_leave_current();
        self.act("ret", self.builder.build_return(Some(&self.int(v))));
    }

    fn open_entry(&self, b: &mut Buf) {
        let f = self.cur_fn();
        let bb = self.ctx.append_basic_block(f, "entry");
        self.blocks.borrow_mut().insert("entry".into(), bb);
        self.builder.position_at_end(bb);
        b.cur = "entry".into();
        self.native_kont_enter_current();
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
        if self.native_kont_enabled {
            self.native_kont_func.replace(Some(NativeKontFunction {
                symbol: name.to_string(),
                params: params.to_vec(),
            }));
        } else {
            self.native_kont_func.replace(None);
        }
        self.pending_musttail.set(false);
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

fn normalize_numbered_symbols(text: &str, prefix: &str) -> String {
    let mut aliases = BTreeMap::<String, usize>::new();
    let mut output = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(offset) = rest.find(prefix) {
        output.push_str(&rest[..offset]);
        output.push_str(prefix);
        rest = &rest[offset + prefix.len()..];
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            continue;
        }
        let original = rest[..digits].to_string();
        let next = aliases.len();
        let alias = *aliases.entry(original).or_insert(next);
        output.push_str(&alias.to_string());
        rest = &rest[digits..];
    }
    output.push_str(rest);
    output
}

fn normalize_function(text: &str) -> String {
    let strings = normalize_numbered_symbols(text, "@.str");
    normalize_numbered_symbols(&strings, "#")
}

fn defined_functions(module: &Module<'_>) -> BTreeMap<String, String> {
    module
        .get_functions()
        .filter(|function| function.count_basic_blocks() > 0)
        .map(|function| {
            (
                function.get_name().to_string_lossy().into_owned(),
                normalize_function(&function.print_to_string().to_string()),
            )
        })
        .collect()
}

pub(crate) fn whole_function_map(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<BTreeMap<String, String>, String> {
    with_module(core, ctors, None, false, |module| {
        Ok(defined_functions(module))
    })
}

pub(crate) fn scc_function_map(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
) -> Result<BTreeMap<String, String>, String> {
    let mut functions = BTreeMap::new();
    for members in crate::core::scc_groups(core) {
        let selected = members.into_iter().collect::<BTreeSet<_>>();
        let ctx = Context::create();
        let isa = Inkwell::new(&ctx, false);
        emit_selected_with_isa(&isa, core, ctors, &selected).map_err(|error| match error {
            SelectedEmissionError::Codegen(error) => error,
        })?;
        if let Some(error) = isa.err.borrow_mut().take() {
            return Err(error);
        }
        functions.extend(defined_functions(&isa.module));
    }

    let plan_ctx = Context::create();
    let plan_isa = Inkwell::new(&plan_ctx, false);
    let plan = plan_closures_with_isa(&plan_isa, core, ctors)?;
    if let Some(error) = plan_isa.err.borrow_mut().take() {
        return Err(error);
    }
    if plan.has_adapters() {
        let ctx = Context::create();
        let isa = Inkwell::new(&ctx, false);
        emit_closure_adapters_with_isa(&isa, core, ctors, &plan)?;
        functions.extend(defined_functions(&isa.module));
    }
    for arity in plan.dispatch_arities() {
        let ctx = Context::create();
        let isa = Inkwell::new(&ctx, false);
        let _ = emit_closure_dispatch_with_isa(&isa, core, ctors, &plan, arity);
        functions.extend(defined_functions(&isa.module));
    }
    Ok(functions)
}

fn with_module<T>(
    core: &Core,
    ctors: &BTreeMap<String, CtorInfo>,
    native_kont_table: Option<&str>,
    native_kont_frames: bool,
    f: impl FnOnce(&Module<'_>) -> Result<T, String>,
) -> Result<T, String> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx, native_kont_frames);
    emit_with_isa(&isa, core, ctors)?;
    if let Some(table) = native_kont_table {
        isa.native_kont_table_global(core, table);
    }
    // Surface the first codegen-internal failure captured during emission as a
    // structured error instead of a panic at the original site.
    if let Some(e) = isa.err.borrow_mut().take() {
        return Err(e);
    }
    f(&isa.module)
}

/// # Errors
/// Fails when a construct reaches codegen unlowered or unsupported.
pub fn emit(core: &LoweredCore, ctors: &BTreeMap<String, CtorInfo>) -> Result<String, String> {
    with_module(core, ctors, None, false, |m| {
        Ok(m.print_to_string().to_string())
    })
}

/// # Errors
/// Fails when a construct reaches codegen unlowered or unsupported.
pub fn emit_with_native_kont_table(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    native_kont_table: &str,
    native_kont_frames: bool,
) -> Result<String, String> {
    with_module(
        core,
        ctors,
        Some(native_kont_table),
        native_kont_frames,
        |m| Ok(m.print_to_string().to_string()),
    )
}

/// Verify the module and write LLVM bitcode to `bc`. On verifier failure the
/// textual IR is kept at a stable temp path for inspection.
///
/// # Errors
/// Fails on codegen failure, a verifier rejection, or an unwritable path.
pub fn emit_bitcode(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    bc: &Path,
) -> Result<(), String> {
    emit_bitcode_with_native_kont_table(core, ctors, "", false, bc)
}

/// Write the globally coupled native continuation metadata as its own module.
///
/// # Errors
/// Fails LLVM verification or when the bitcode path cannot be written.
pub fn emit_native_kont_plan_bitcode(
    core: &LoweredCore,
    native_kont_table: &str,
    bc: &Path,
) -> Result<(), String> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx, false);
    isa.native_kont_table_global(core, native_kont_table);
    if let Err(error) = isa.module.verify() {
        return Err(format!("LLVM verifier rejected native kont plan: {error}"));
    }
    if isa.module.write_bitcode_to_path(bc) {
        Ok(())
    } else {
        Err(format!("cannot write bitcode to {}", bc.display()))
    }
}

/// One independently linkable part of the closure dispatch plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClosurePlanShard {
    /// Curry-adapter function bodies shared by arity dispatchers.
    Adapters,
    /// The dispatcher for one applied argument count.
    Dispatch(usize),
}

/// A fully discovered closure plan shared by every independently cacheable
/// adapter and dispatch shard in one build. Keeping this opaque prevents shard
/// emission from rediscovering the whole program.
pub(crate) struct PlannedClosures {
    plan: ClosurePlan,
}

impl PlannedClosures {
    /// Return the exact independently cacheable closure-plan shards.
    #[must_use]
    pub(crate) fn shards(&self) -> Vec<(ClosurePlanShard, String)> {
        let base = self.plan.fingerprint();
        let mut shards = Vec::new();
        if self.plan.has_adapters() {
            shards.push((ClosurePlanShard::Adapters, format!("{base}:adapters")));
        }
        shards.extend(self.plan.dispatch_arities().into_iter().map(|arity| {
            (
                ClosurePlanShard::Dispatch(arity),
                format!("{base}:dispatch:{arity}"),
            )
        }));
        shards
    }
}

/// Discover the closure metadata contributed by one selected backend SCC.
///
/// # Errors
/// Fails when selected closure discovery encounters invalid Core.
pub(crate) fn scc_closure_summary(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    selected: &BTreeSet<Sym>,
) -> Result<ClosureSummary, String> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx, false);
    let summary = closure_summary_with_isa(&isa, core, ctors, selected)?;
    if let Some(error) = isa.err.borrow_mut().take() {
        return Err(error);
    }
    Ok(summary)
}

/// Fold independently discovered SCC closure summaries into one canonical
/// adapter and dispatch plan.
///
/// # Errors
/// Fails when a summary is malformed, tags collide, or planning fails.
pub(crate) fn plan_closures_from_summaries(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    summaries: &[ClosureSummary],
) -> Result<PlannedClosures, String> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx, false);
    let plan = plan_closures_from_summaries_with_isa(&isa, core, ctors, summaries)?;
    if let Some(error) = isa.err.borrow_mut().take() {
        return Err(error);
    }
    Ok(PlannedClosures { plan })
}

/// Emit one shared closure-plan shard from an already discovered plan.
///
/// # Errors
/// Fails during code generation, LLVM verification, or writing the bitcode.
pub(crate) fn emit_closure_plan_shard_bitcode(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    plan: &PlannedClosures,
    shard: ClosurePlanShard,
    bc: &Path,
) -> Result<(), String> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx, false);
    match shard {
        ClosurePlanShard::Adapters => {
            emit_closure_adapters_with_isa(&isa, core, ctors, &plan.plan)?;
        }
        ClosurePlanShard::Dispatch(arity) => {
            let _ = emit_closure_dispatch_with_isa(&isa, core, ctors, &plan.plan, arity);
        }
    }
    if let Some(error) = isa.err.borrow_mut().take() {
        return Err(error);
    }
    if let Err(error) = isa.module.verify() {
        return Err(format!(
            "LLVM verifier rejected closure plan shard: {error}"
        ));
    }
    if isa.module.write_bitcode_to_path(bc) {
        Ok(())
    } else {
        Err(format!("cannot write bitcode to {}", bc.display()))
    }
}

/// A selected backend SCC either needs the shared closure plan or failed normal
/// code generation.
#[derive(Debug)]
pub enum SccBitcodeError {
    /// Ordinary code generation failed.
    Codegen(String),
}

impl fmt::Display for SccBitcodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Codegen(error) => formatter.write_str(error),
        }
    }
}

impl std::error::Error for SccBitcodeError {}

/// Verify and write one independently emit-able backend SCC as LLVM bitcode.
///
/// The complete Core remains available for cross-SCC arity declarations, while
/// only `selected` definitions receive bodies.
///
/// # Errors
/// Fails when the SCC needs the global closure plan, violates a code-generation
/// invariant, fails LLVM verification, or cannot be written.
pub fn emit_selected_bitcode(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    selected: &BTreeSet<Sym>,
    native_kont_table: &str,
    owns_closure_plan: bool,
    bc: &Path,
) -> Result<(), SccBitcodeError> {
    let ctx = Context::create();
    let isa = Inkwell::new(&ctx, false);
    if owns_closure_plan {
        emit_selected_plan_with_isa(&isa, core, ctors, selected)
            .map_err(SccBitcodeError::Codegen)?;
    } else {
        emit_selected_with_isa(&isa, core, ctors, selected).map_err(|error| match error {
            SelectedEmissionError::Codegen(error) => SccBitcodeError::Codegen(error),
        })?;
    }
    if !native_kont_table.is_empty() {
        isa.native_kont_table_global(core, native_kont_table);
    }
    if let Some(error) = isa.err.borrow_mut().take() {
        return Err(SccBitcodeError::Codegen(error));
    }
    if let Err(error) = isa.module.verify() {
        let kept = std::env::temp_dir().join("prism_failed_scc.ll");
        let _ = std::fs::write(&kept, isa.module.print_to_string().to_string());
        return Err(SccBitcodeError::Codegen(format!(
            "LLVM verifier rejected backend SCC, kept at {}:\n{}",
            kept.display(),
            error
        )));
    }
    if isa.module.write_bitcode_to_path(bc) {
        Ok(())
    } else {
        Err(SccBitcodeError::Codegen(format!(
            "cannot write bitcode to {}",
            bc.display()
        )))
    }
}

/// Verify the module with a native kont metadata table and write LLVM bitcode to
/// `bc`.
///
/// # Errors
/// Fails on codegen failure, a verifier rejection, or an unwritable path.
pub fn emit_bitcode_with_native_kont_table(
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    native_kont_table: &str,
    native_kont_frames: bool,
    bc: &Path,
) -> Result<(), String> {
    let table = (!native_kont_table.is_empty()).then_some(native_kont_table);
    with_module(core, ctors, table, native_kont_frames, |m| {
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
