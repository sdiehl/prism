use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;
#[cfg(feature = "native")]
use std::process::Command;
#[cfg(feature = "native")]
use std::{env, fs};

#[cfg(feature = "mlir")]
use crate::codegen::emit_mlir;
#[cfg(feature = "native")]
use crate::codegen::{emit_llvm, emit_llvm_bc};
#[cfg(feature = "native")]
use crate::core::effect_lower::residual_effects;
use crate::core::fbip::{borrow_sigs, Sigs};
use crate::core::{
    balanced, check_fip, check_fip_linear, elaborate, fip_annots, insert_rc, lower_effects,
    pp_core, pp_core_pretty, reuse, Core,
};
use crate::error::Error;
use crate::eval::{run, Run, Rv};
use crate::lex::lex;
#[cfg(feature = "native")]
use crate::names::ENTRY_POINT;
use crate::parse::{parse, ParseResult};
use crate::resolve::resolve_modules;
use crate::sym::Sym;
use crate::syntax::ast::{Core as CorePhase, Program, Span};
use crate::syntax::desugar::desugar;
use crate::types::{check as typecheck, Checked, CtorInfo};

pub const PRELUDE: &str = include_str!("../../lib/prelude.pr");

/// The source file extension. Modules `import Foo` resolve to `Foo.pr`.
pub const SOURCE_EXT: &str = "pr";
#[cfg(feature = "native")]
const RUNTIME: &str = include_str!("../../runtime/prism_rt.c");

#[must_use]
pub fn with_prelude(src: &str) -> String {
    format!("{PRELUDE}\n{src}")
}

/// Prepend a caller-supplied prelude instead of the built-in one.
///
/// A project that sets `[package] prelude` opts into its own always-on
/// definitions; the built-in prelude is not added on top, so the project's
/// prelude is the whole base.
#[must_use]
pub fn with_custom_prelude(prelude: &str, src: &str) -> String {
    format!("{prelude}\n{src}")
}

/// # Examples
/// ```
/// let src = prism::with_prelude("fn double(x : Int) : Int = x * 2");
/// let checked = prism::check(&src).unwrap();
/// let double = checked.decls.iter().find(|d| d.name == "double").unwrap();
/// assert_eq!(double.ty.show(), "(Int) -> Int");
/// ```
///
/// # Errors
/// Fails on lex, parse, or type errors.
pub fn check(src: &str) -> Result<Checked, Error> {
    check_at(src, Path::new("."))
}

/// Like [`check`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on lex, parse, module, or type errors.
pub fn check_at(src: &str, base: &Path) -> Result<Checked, Error> {
    let ParseResult { program, .. } = parse(src)?;
    let program = resolve_modules(program, base)?;
    let lints = lint_surface(src, &program);
    let program = desugar(program)?;
    let mut checked = typecheck(&program)?;
    checked.warnings.extend(lints);
    emit_warnings(src, &checked);
    Ok(checked)
}

// Unused-binding and shadowed-name lints over the resolved surface program,
// scoped to the user's own source (the prepended prelude is excluded by offset).
fn lint_surface(src: &str, prog: &Program) -> Vec<crate::tc::Warning> {
    let user_start = crate::error::SourceMap::new(src).prelude_len();
    crate::resolve::lint_bindings(prog, user_start)
}

// Surface non-fatal checker diagnostics (orphan/overlapping instances, unused or
// shadowed bindings) on stderr, with a source caret when the warning points into
// this source. Errors abort earlier, so this only runs once a program type checks.
fn emit_warnings(src: &str, checked: &Checked) {
    for w in &checked.warnings {
        eprint!(
            "{}",
            crate::error::render_warning(src, "<source>", &w.span, &w.msg, true)
        );
    }
}

fn frontend(src: &str, base: &Path) -> Result<(Program<CorePhase>, Checked, Core), Error> {
    let ParseResult { program, .. } = parse(src)?;
    let program = resolve_modules(program, base)?;
    let lints = lint_surface(src, &program);
    let program = desugar(program)?;
    let mut checked = typecheck(&program)?;
    checked.warnings.extend(lints);
    emit_warnings(src, &checked);
    let core = elaborate(&program, &checked)?;
    fip_check(&program, &checked, &core)?;
    reconcile_effects(&checked, &core)?;
    Ok((program, checked, core))
}

// Cross-check the two effect engines as a real assertion (not a debug_assert):
// the op-keyed call-graph fixpoint used by effect lowering (`latent_ops`)
// against the type checker's effect-name-keyed inferred row (`Checked::effects`).
// The agreed direction is containment: every effect a function can still perform
// must appear in its inferred row. A violation means the checker under-reported
// an effect a later pass will still try to lower, an internal-consistency bug
// surfaced here rather than as a miscompile. Synthesized ops that are not
// type-level effects are skipped rather than flagged.
fn reconcile_effects(checked: &Checked, core: &Core) -> Result<(), Error> {
    use std::collections::BTreeSet;

    let latent = crate::core::effect_lower::latent_ops(core);
    let empty = BTreeSet::new();
    for f in &core.fns {
        let Some(ops) = latent.get(&f.name) else {
            continue;
        };
        let inferred = checked.effects.get(f.name.as_str()).unwrap_or(&empty);
        let extra: Vec<&str> = ops
            .iter()
            .filter_map(|op| checked.eff_ops.get(op.as_str()))
            .map(|info| info.effect_name)
            .filter(|e| !inferred.contains(e))
            .collect::<BTreeSet<_>>()
            .iter()
            .map(|s| s.as_str())
            .collect();
        if !extra.is_empty() {
            let row: Vec<&str> = inferred.iter().map(|s| s.as_str()).collect();
            return Err(Error::Ice(format!(
                "effect reconciliation: `{}` can still perform {extra:?} after lowering, \
                 but its inferred row is {row:?}",
                f.name
            )));
        }
    }
    Ok(())
}

// Check the FP^2 discipline of every `fip`/`fbip`-annotated function. Linearity
// is a property of the SOURCE term, so it is checked on the raw elaborated core
// (`check_fip_linear`), using the typechecker's param/field types to exempt
// scalars (a `dup` on an immediate is a runtime no-op). Zero-allocation, the
// callee closure, and bounded stack are properties of the COMPILED term, so they
// are checked on the reuse-lowered core (`check_fip`). Runs on every
// check/build/interpret (shared `frontend`); pure annotated functions are
// unaffected by effect lowering, so this un-effect-lowered core matches
// `dump fbip`.
fn fip_check(program: &Program<CorePhase>, checked: &Checked, core: &Core) -> Result<(), Error> {
    let annots = fip_annots(program);
    if annots.is_empty() {
        return Ok(());
    }
    let to_err = |msg: String| {
        // Point the diagnostic at the offending annotated function: its name
        // appears backtick-quoted in the message, so the first annotated decl
        // whose name occurs there owns the span.
        let span = program
            .fns
            .iter()
            .filter(|d| annots.contains_key(&Sym::from(&d.name)))
            .find(|d| msg.contains(&format!("`{}`", d.name)))
            .map_or_else(marginalia::Span::default, |d| d.span);
        Error::Type(crate::error::TypeError::Other { span, msg })
    };
    let sigs = borrow_sigs(program);
    let users: std::collections::BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
    check_fip_linear(core, &annots, &checked.decls, &checked.ctors).map_err(to_err)?;
    check_fip(&reuse(&insert_rc(core, &sigs)), &annots, &sigs, &users).map_err(to_err)
}

/// # Examples
/// ```
/// let src = prism::with_prelude("fn main() = print(1 + 2)");
/// let run = prism::interpret(&src).unwrap();
/// assert_eq!(run.out[0].show(), "3");
/// ```
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret(src: &str) -> Result<Run, Error> {
    interpret_at(src, Path::new("."))
}

/// Like [`interpret`], resolving any module imports relative to `base`.
///
/// Captures all `print` output into the returned [`Run`]'s `term` (the
/// differential oracle and wasm path); nothing reaches real stdio.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_at(src: &str, base: &Path) -> Result<Run, Error> {
    let core = prepared_core(src, base)?;
    run(&core).map_err(Error::Runtime)
}

/// Like [`interpret_at`], but streams `print` to `out_sink` and reads `input`.
///
/// The native CLI passes real stdout/stdin so program output is live and
/// `read_*` reaches the terminal; `term` still carries the exact transcript and
/// `Run::exit` carries any `exit(code)`.
///
/// # Errors
/// Fails on front-end errors or a runtime fault.
pub fn interpret_io_at(
    src: &str,
    base: &Path,
    out_sink: &mut dyn std::io::Write,
    input: &mut dyn std::io::BufRead,
) -> Result<Run, Error> {
    let core = prepared_core(src, base)?;
    crate::eval::run_io(&core, out_sink, input).map_err(Error::Runtime)
}

// Shared front-end and rc-balance ICE check for the interpreter entries. The
// interpreter runs the un-lowered core, but the balance check over the
// effect-lowered core still runs so a bad lowering is caught here too.
fn prepared_core(src: &str, base: &Path) -> Result<Core, Error> {
    let (program, checked, core) = frontend(src, base)?;
    let sigs = borrow_sigs(&program);
    let (lowered, _, warning) = lower_effects(&core, &checked.ctors)?;
    emit_lower_warning(src, warning.as_deref());
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs)
        .map_err(|e| Error::Codegen(format!("ICE: rc imbalance: {e}")))?;
    Ok(core)
}

fn lowered_core(
    src: &str,
    base: &Path,
) -> Result<(Checked, Core, BTreeMap<String, CtorInfo>, Sigs), Error> {
    let (program, checked, core) = frontend(src, base)?;
    let sigs = borrow_sigs(&program);
    let (lowered, ctors, warning) = lower_effects(&core, &checked.ctors)?;
    emit_lower_warning(src, warning.as_deref());
    Ok((checked, lowered, ctors, sigs))
}

// Surface the effect-lowering fallback warning through the standard renderer,
// the same one `emit_warnings` uses for checker diagnostics. The diagnostic
// comes from the Core phase, which carries no source spans, so it renders as a
// plain `warning: ...` line (an empty span makes `render_warning` skip the caret).
fn emit_lower_warning(src: &str, warning: Option<&str>) {
    if let Some(msg) = warning {
        eprint!(
            "{}",
            crate::error::render_warning(src, "<source>", &Span::empty(0), msg, true)
        );
    }
}

/// The effect-lowering strategy this snippet's program takes.
///
/// A performance classification of how its effects compile (`pure`, `evidence`,
/// `state-fusion`, `local-partial`, `whole-program-free-monad`,
/// `selective-free-monad`). A perf snapshot pins this per corpus program so a
/// silent regression onto the slow free-monad path surfaces as a reviewable diff.
/// `full` carries the prelude.
///
/// # Errors
/// Fails on front-end errors.
pub fn effect_strategy_full(full: &str, base: &Path) -> Result<&'static str, Error> {
    let (_, checked, core) = frontend(full, base)?;
    Ok(crate::core::effect_strategy(&core, &checked.ctors)?)
}

/// The effect-lowering fallback warnings this snippet's program raises.
///
/// Empty when it stays on a fused path. Each names the functions that lost
/// fusion and why, so a test can lock the diagnostic a slow-path program
/// produces. `full` carries the prelude.
///
/// # Errors
/// Fails on front-end errors.
pub fn effect_warnings_full(full: &str, base: &Path) -> Result<Vec<String>, Error> {
    let (_, checked, core) = frontend(full, base)?;
    let (_, _, warning) = lower_effects(&core, &checked.ctors)?;
    Ok(warning.into_iter().collect())
}

/// The CBPV core IR of the snippet's own functions (prelude elided),
/// pretty-printed.
///
/// Effects are lowered to explicit `handle`/`do`, reference-counting
/// `dup`/`drop` inserted, and FBIP `reuse_token`/`reuse` in-place updates
/// applied: the lowest-level representation available without the LLVM
/// back-end. `src` is the bare snippet; the prelude is prepended internally.
///
/// # Errors
/// Fails on front-end errors.
pub fn core_ir(src: &str) -> Result<String, Error> {
    core_ir_full(&with_prelude(src), Path::new("."))
}

/// Like [`core_ir`], but `full` already carries the prelude (as the REPL's
/// composed buffer does). Imports resolve relative to `base`.
///
/// Reference counting and FBIP reuse are applied, but effects are left as
/// readable `do`/`handle` nodes rather than lowered into the runtime's monadic
/// representation, mirroring `dump fbip`.
///
/// # Errors
/// Fails on front-end errors.
pub fn core_ir_full(full: &str, base: &Path) -> Result<String, Error> {
    let prelude = prelude_fn_names()?;
    let (program, _, core) = frontend(full, base)?;
    let sigs = borrow_sigs(&program);
    let optimized = reuse(&insert_rc(&core, &sigs));
    let own = Core {
        fns: optimized
            .fns
            .into_iter()
            .filter(|f| !prelude.contains(&f.name))
            .collect(),
    };
    Ok(pp_core_pretty(&own))
}

/// Off-platform builtins (file IO, env, process) the snippet would invoke.
///
/// Found by scanning the elaborated core rather than token adjacency: a builtin
/// reached through a let-binding or passed as a value (`let f = read_file`) is
/// eta-expanded to a `StrBuiltin` node and so is still caught. `full` already
/// carries the prelude. Returns the offending names in first-seen order, empty
/// when the snippet stays on platform.
///
/// # Errors
/// Fails on front-end errors (lex, parse, module, type, fip).
pub fn off_platform_builtins(full: &str, base: &Path) -> Result<Vec<&'static str>, Error> {
    use crate::core::{Comp, Value};

    fn scan_val(v: &Value, out: &mut Vec<&'static str>) {
        match v {
            Value::Thunk(c) => scan_comp(c, out),
            Value::Ctor(_, _, fs) | Value::Tuple(fs) => fs.iter().for_each(|f| scan_val(f, out)),
            _ => {}
        }
    }

    fn scan_comp(c: &Comp, out: &mut Vec<&'static str>) {
        if let Comp::StrBuiltin(b, _) = c {
            if b.off_platform() && !out.contains(&b.name()) {
                out.push(b.name());
            }
        }
        match c {
            Comp::Return(v)
            | Comp::Force(v)
            | Comp::Print(v)
            | Comp::PrintF(v)
            | Comp::PrintS(v)
            | Comp::Error(v)
            | Comp::Srand(v)
            | Comp::FloatBuiltin(_, v)
            | Comp::Dup(v)
            | Comp::Drop(v)
            | Comp::Reuse(_, v)
            | Comp::RefNew(v)
            | Comp::RefGet(v) => scan_val(v, out),
            Comp::RefSet(c, v) => {
                scan_val(c, out);
                scan_val(v, out);
            }
            Comp::WithReuse { freed, body, .. } => {
                scan_val(freed, out);
                scan_comp(body, out);
            }
            Comp::Prim(_, a, b) => {
                scan_val(a, out);
                scan_val(b, out);
            }
            Comp::Bind(m, _, n) => {
                scan_comp(m, out);
                scan_comp(n, out);
            }
            Comp::App(f, args) => {
                scan_comp(f, out);
                for a in args {
                    scan_val(a, out);
                }
            }
            Comp::If(v, t, e) => {
                scan_val(v, out);
                scan_comp(t, out);
                scan_comp(e, out);
            }
            Comp::Call(_, args) | Comp::Do(_, args) | Comp::StrBuiltin(_, args) => {
                for a in args {
                    scan_val(a, out);
                }
            }
            Comp::Lam(_, b) | Comp::Mask(_, b) => scan_comp(b, out),
            Comp::Case(v, arms) => {
                scan_val(v, out);
                for (_, body) in arms {
                    scan_comp(body, out);
                }
            }
            Comp::Handle {
                body,
                return_body,
                ops,
                ..
            } => {
                scan_comp(body, out);
                if let Some(rb) = return_body {
                    scan_comp(rb, out);
                }
                for op in ops {
                    scan_comp(&op.body, out);
                }
            }
            Comp::ReadInt | Comp::ReadLine | Comp::PrintNl | Comp::Rand => {}
        }
    }

    let (_, _, core) = frontend(full, base)?;
    let reachable = crate::core::reachable_fns(&core);
    let mut out = Vec::new();
    for f in core.fns.iter().filter(|f| reachable.contains(&f.name)) {
        scan_comp(&f.body, &mut out);
    }
    Ok(out)
}

// Core function names contributed by the prelude alone, used to elide it from a
// snippet's IR dump.
fn prelude_fn_names() -> Result<std::collections::HashSet<Sym>, Error> {
    let (_, _, core) = frontend(PRELUDE, Path::new("."))?;
    Ok(core.fns.into_iter().map(|f| f.name).collect())
}

#[cfg(feature = "native")]
fn compiled(src: &str, base: &Path) -> Result<(Checked, Core, BTreeMap<String, CtorInfo>), Error> {
    let (checked, lowered, ctors, sigs) = lowered_core(src, base)?;
    residual_effects(&lowered).map_err(Error::Ice)?;
    Ok((checked, reuse(&insert_rc(&lowered, &sigs)), ctors))
}

/// # Errors
/// Fails on front-end errors, codegen failure, or when linking with cc fails.
#[cfg(feature = "native")]
pub fn build(src: &str, out: &Path) -> Result<(), Error> {
    build_at(src, Path::new("."), out)
}

/// Like [`build`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when linking with cc fails.
#[cfg(feature = "native")]
pub fn build_at(src: &str, base: &Path, out: &Path) -> Result<(), Error> {
    let (checked, core, ctors) = compiled(src, base)?;
    if !checked.decls.iter().any(|d| d.name == ENTRY_POINT) {
        return Err(Error::Codegen("no main function to build".into()));
    }
    let bc = out.with_extension("bc");
    emit_llvm_bc(&core, &ctors, &bc).map_err(Error::Codegen)?;
    cc_link(&bc, out)
}

// Save the offending IR at a stable path so a clang parse error points at
// something inspectable. The happy path stays a single clang invocation.
#[cfg(feature = "native")]
fn ir_failure(tool: &str, ir: &Path, stderr: &[u8]) -> Error {
    let ext = ir.extension().and_then(|e| e.to_str()).unwrap_or("ll");
    let kept = env::temp_dir().join(format!("prism_failed.{ext}"));
    let _ = fs::copy(ir, &kept);
    let text = String::from_utf8_lossy(stderr);
    let head: Vec<&str> = text.lines().take(8).collect();
    Error::Codegen(format!(
        "{tool} rejected generated IR, kept at {}:\n{}",
        kept.display(),
        head.join("\n")
    ))
}

#[cfg(feature = "native")]
fn cc_link(ir: &Path, out: &Path) -> Result<(), Error> {
    let cc = env::var("PRISM_CC").unwrap_or_else(|_| "clang".into());
    let rt = out.with_extension("prism_rt.c");
    fs::write(&rt, RUNTIME)?;
    // Extra cc flags, whitespace-split. CI sets this to -fsanitize=undefined so
    // the corpus runs under UBSan and any new runtime UB aborts the program.
    let extra = env::var("PRISM_CC_FLAGS").unwrap_or_default();
    let res = Command::new(&cc)
        .args(["-O2", "-flto=thin", "-Wno-override-module"])
        .args(extra.split_whitespace())
        .arg(ir)
        .arg(&rt)
        .arg("-lm")
        .arg("-o")
        .arg(out)
        .output()
        .map_err(|e| Error::Codegen(format!("running {cc}: {e} (is clang installed?)")));
    let _ = fs::remove_file(&rt);
    let cc_out = res?;
    if cc_out.status.success() {
        if !cc_out.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&cc_out.stderr));
        }
        Ok(())
    } else {
        Err(ir_failure(&cc, ir, &cc_out.stderr))
    }
}

/// # Errors
/// Fails on front-end errors or codegen failure.
#[cfg(feature = "native")]
pub fn emit_ir(src: &str) -> Result<String, Error> {
    let (_, core, ctors) = compiled(src, Path::new("."))?;
    emit_llvm(&core, &ctors).map_err(Error::Codegen)
}

/// # Errors
/// Fails on front-end errors or an unbalanced rc insertion.
pub fn rc_balanced(src: &str) -> Result<(), Error> {
    let (_, lowered, _, sigs) = lowered_core(src, Path::new("."))?;
    balanced(&reuse(&insert_rc(&lowered, &sigs)), &sigs).map_err(Error::Codegen)
}

/// # Errors
/// Fails on front-end errors, codegen failure, or when the MLIR toolchain fails.
#[cfg(feature = "mlir")]
pub fn build_mlir(src: &str, out: &Path) -> Result<(), Error> {
    build_mlir_at(src, Path::new("."), out)
}

/// Like [`build_mlir`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors, codegen failure, or when the MLIR toolchain fails.
#[cfg(feature = "mlir")]
pub fn build_mlir_at(src: &str, base: &Path, out: &Path) -> Result<(), Error> {
    let (checked, core, ctors) = compiled(src, base)?;
    if !checked.decls.iter().any(|d| d.name == ENTRY_POINT) {
        return Err(Error::Codegen("no main function to build".into()));
    }
    let mlir_text = emit_mlir(&core, &ctors).map_err(Error::Codegen)?;
    let mlir_file = out.with_extension("mlir");
    fs::write(&mlir_file, &mlir_text)?;

    let ll_file = out.with_extension("ll");
    let translate_out = Command::new("mlir-translate")
        .arg("--mlir-to-llvmir")
        .arg(&mlir_file)
        .output()
        .map_err(|e| {
            Error::Codegen(format!(
                "mlir-translate: {e} (is mlir-translate installed?)"
            ))
        })?;
    if !translate_out.status.success() {
        return Err(ir_failure(
            "mlir-translate",
            &mlir_file,
            &translate_out.stderr,
        ));
    }
    fs::write(&ll_file, &translate_out.stdout)?;

    let res = cc_link(&ll_file, out);
    let _ = fs::remove_file(&mlir_file);
    res
}

fn types_section(checked: &Checked) -> String {
    let mut s = String::new();
    for d in &checked.decls {
        writeln!(s, "{} : {}", d.name, d.ty.show()).unwrap();
    }
    s
}

#[must_use]
pub fn report(src: &str) -> String {
    report_at(src, Path::new("."))
}

#[must_use]
pub fn report_at(src: &str, base: &Path) -> String {
    // Render a phase failure with the same span-aware ariadne report the CLI
    // shows for `run`/`build`/`check`, so `report` does not degrade to a bare
    // message.
    let render = |e: Error| e.render_plain(src, "<source>");
    let mut out = String::new();
    let tokens = match lex(src) {
        Ok((t, _)) => t,
        Err(e) => return render(e.into()),
    };
    let toks: Vec<String> = tokens.iter().map(|(_, t, _)| format!("{t:?}")).collect();
    section(&mut out, "tokens", &toks.join(" "));

    let ParseResult { program, .. } = match parse(src) {
        Ok(r) => r,
        Err(e) => {
            section(&mut out, "parse", &render(e.into()));
            return out;
        }
    };
    section(&mut out, "ast", &format!("{program:#?}"));

    let program = match resolve_modules(program, base) {
        Ok(p) => p,
        Err(e) => {
            section(&mut out, "resolve", &render(e));
            return out;
        }
    };

    let program = match desugar(program) {
        Ok(p) => p,
        Err(e) => {
            section(&mut out, "types", &render(e.into()));
            return out;
        }
    };
    let checked = match typecheck(&program) {
        Ok(c) => c,
        Err(e) => {
            section(&mut out, "types", &render(e.into()));
            return out;
        }
    };
    section(&mut out, "types", types_section(&checked).trim_end());

    let core = match elaborate(&program, &checked) {
        Ok(c) => c,
        Err(e) => {
            section(&mut out, "core (cbpv)", &render(e));
            return out;
        }
    };
    section(&mut out, "core (cbpv)", pp_core(&core).trim_end());

    if let Err(e) = fip_check(&program, &checked, &core) {
        section(&mut out, "fip", &render(e));
        return out;
    }

    let sigs = borrow_sigs(&program);
    section(
        &mut out,
        "fbip (rc)",
        pp_core(&reuse(&insert_rc(&core, &sigs))).trim_end(),
    );

    #[cfg(feature = "native")]
    match lower_effects(&core, &checked.ctors) {
        Ok((lowered, ctors, _)) => match emit_llvm(&reuse(&insert_rc(&lowered, &sigs)), &ctors) {
            Ok(ir) => section(&mut out, "llvm", strip_target(&ir).trim_end()),
            Err(e) => section(&mut out, "llvm", &format!("(skipped: {e})")),
        },
        Err(e) => section(&mut out, "llvm", &format!("(skipped: {e})")),
    }

    match run(&core) {
        Ok(r) => {
            let outs: Vec<String> = r.out.iter().map(Rv::show).collect();
            section(
                &mut out,
                "run",
                &format!("output: [{}]\nresult: {}", outs.join(", "), r.value.show()),
            );
        }
        Err(e) => section(&mut out, "run", &format!("error: {e}")),
    }
    out
}

/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump(phase: &str, src: &str) -> Result<String, Error> {
    dump_at(phase, src, Path::new("."))
}

/// Like [`dump`], resolving any module imports relative to `base`.
///
/// # Errors
/// Fails on front-end errors or an unknown phase name.
pub fn dump_at(phase: &str, src: &str, base: &Path) -> Result<String, Error> {
    match phase {
        "tokens" => {
            let (t, _) = lex(src)?;
            Ok(t.iter()
                .map(|(_, t, _)| format!("{t:?}"))
                .collect::<Vec<_>>()
                .join(" "))
        }
        "ast" => Ok(format!("{:#?}", parse(src)?.program)),
        "types" => Ok(types_section(&check_at(src, base)?)),
        "core" => {
            let (_, _, core) = frontend(src, base)?;
            Ok(pp_core_pretty(&core))
        }
        "core-json" => {
            let (_, _, core) = frontend(src, base)?;
            Ok(crate::core::core_to_json(&core))
        }
        "fbip" => {
            let (program, _, core) = frontend(src, base)?;
            let sigs = borrow_sigs(&program);
            Ok(pp_core_pretty(&reuse(&insert_rc(&core, &sigs))))
        }
        "lowered" => {
            let (_, lowered, _, _) = lowered_core(src, base)?;
            Ok(pp_core_pretty(&lowered))
        }
        #[cfg(feature = "native")]
        "llvm" => {
            let (_, core, ctors) = compiled(src, base)?;
            emit_llvm(&core, &ctors).map_err(Error::Codegen)
        }
        #[cfg(feature = "mlir")]
        "mlir" => {
            let (_, core, ctors) = compiled(src, base)?;
            emit_mlir(&core, &ctors).map_err(Error::Codegen)
        }
        other => Err(Error::Codegen(format!("unknown phase {other}"))),
    }
}

// The module's target triple and data layout are host-derived, so they differ
// between machines. They are irrelevant to the snapshotted pipeline (clang
// re-derives them at link time), so drop them from the dump.
#[cfg(feature = "native")]
fn strip_target(ir: &str) -> String {
    ir.lines()
        .filter(|l| !l.starts_with("target datalayout") && !l.starts_with("target triple"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn section(out: &mut String, title: &str, body: &str) {
    writeln!(out, "== {title} ==").unwrap();
    writeln!(out, "{body}").unwrap();
    out.push('\n');
}
