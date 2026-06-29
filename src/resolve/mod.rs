//! Name resolution: canonicalizes references to globally unique symbols.
//!
//! A program with no imports is a single module (the user's source plus the
//! implicit prelude); resolution is then the identity on names and only
//! validates the export table. With imports, [`resolve_modules`] loads the
//! referenced files and assigns every top-level name in each imported module a
//! canonical symbol (`Data.Map.insert` for exports, `Data.Map@helper` for
//! privates), rewrites every reference in each module against its own import
//! scope, and merges everything into one flat [`Program`] keyed by those
//! globally unique symbols. Two modules may export the same short name and
//! coexist, since references reach the disjoint canonical symbols.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use marginalia::Span;

use crate::error::{Error, TypeError};
use crate::syntax::ast::{
    Constraint, Decl, EffLabel, Expr, HandlerArm, ImportDecl, Pattern, Program, Qualifier, Row,
    Sugar, SugarArm, Surface, Ty, S,
};

mod lints;
mod load;
pub use lints::lint_bindings;
pub use load::{load, Module, Root};

/// The search path for a single-file or test program: the given source root,
/// then the embedded standard library.
#[must_use]
pub fn default_roots(base: &Path) -> Vec<Root> {
    vec![
        Root::Dir(base.to_path_buf()),
        Root::Embedded(crate::stdlib::STDLIB),
    ]
}

/// The search path for a project.
///
/// The project source root, each path dependency's source root (in declared
/// order), then the embedded standard library. A dependency's modules resolve
/// under its own root; the project shadows a name it redefines.
#[must_use]
pub fn project_roots(src_dir: &Path, dep_dirs: &[PathBuf]) -> Vec<Root> {
    let mut roots = vec![Root::Dir(src_dir.to_path_buf())];
    roots.extend(dep_dirs.iter().map(|d| Root::Dir(d.clone())));
    roots.push(Root::Embedded(crate::stdlib::STDLIB));
    roots
}

/// Width of each module's span band. Module `i` shifts its spans by
/// `(i + 1) << SPAN_BAND_SHIFT`, so no single file exceeding 1 TiB and no run of
/// fewer than 2^23 modules can collide, while staying clear of the synthesized
/// span region at `usize::MAX / 2`. On 32-bit targets (wasm32) `usize` is too
/// narrow for a 40-bit band, so the shift drops to 24 (16 MiB per file, up to
/// ~128 modules before nearing `usize::MAX / 2`).
#[cfg(target_pointer_width = "64")]
const SPAN_BAND_SHIFT: u32 = 40;
#[cfg(not(target_pointer_width = "64"))]
const SPAN_BAND_SHIFT: u32 = 24;

/// Bare names a selective import binds in unqualified scope, each mapped to the
/// canonical symbol it resolves to.
type Unqualified = BTreeMap<String, String>;

/// A qualifier (alias, else last path component) mapped to the loaded modules it
/// names; an entry has more than one index only when imports share a qualifier.
type Quals = BTreeMap<String, Vec<usize>>;

/// A module's exported names mapped to the canonical symbol each resolves to.
/// For an own definition that is `Module.name`; for a `pub import` re-export it
/// is the original definition's canonical symbol.
type Exports = BTreeMap<String, String>;

/// Every name a program binds at the top level: the universe a `pub` export or
/// an importer may refer to (type and constructor names, effects, errors,
/// aliases, classes, pattern synonyms, functions).
#[must_use]
pub fn binders(p: &Program) -> BTreeSet<String> {
    let mut s = BTreeSet::new();
    for d in &p.types {
        s.insert(d.name.clone());
        s.extend(d.ctors.iter().map(|c| c.name.clone()));
    }
    s.extend(p.effects.iter().map(|e| e.name.clone()));
    s.extend(p.errors.iter().map(|e| e.name.clone()));
    s.extend(p.aliases.iter().map(|a| a.name.clone()));
    s.extend(p.synonyms.iter().map(|s| s.name.clone()));
    s.extend(p.classes.iter().map(|c| c.name.clone()));
    s.extend(p.patterns.iter().map(|p| p.name.clone()));
    s.extend(p.fns.iter().map(|f| f.name.clone()));
    s
}

/// The names a module makes visible to importers: every `pub` item, plus the
/// constructors of every transparent `pub` data type. An `opaque` type exports
/// its name only; its constructors stay module-private, so their absence from
/// this set hides them from importers.
fn exports_of(p: &Program) -> BTreeSet<String> {
    let mut e = p.exports.clone();
    for d in &p.types {
        if p.exports.contains(&d.name) && !p.opaques.contains(&d.name) {
            e.extend(d.ctors.iter().map(|c| c.name.clone()));
        }
    }
    e
}

/// Resolve a parsed program to canonical form.
///
/// For an import-free program this checks that every exported name is actually
/// defined and returns the program unchanged.
///
/// # Errors
/// Fails when a name is exported (`pub`) without a matching definition.
pub fn resolve(program: Program) -> Result<Program, TypeError> {
    let bound = binders(&program);
    if let Some(name) = program.exports.iter().find(|n| !bound.contains(*n)) {
        return Err(TypeError::Scope {
            span: Span::empty(0),
            msg: format!("cannot export `{name}`: no such definition"),
        });
    }
    Ok(program)
}

/// A loaded module's identity and the canonical symbol each exported name
/// resolves to (its own definitions plus any `pub import` re-exports).
struct ModInfo {
    path: String,
    exports: Exports,
}

/// Resolve a program that may import other modules, loading them under `base`.
///
/// Import-free programs take the single-module [`resolve`] fast path unchanged.
///
/// # Errors
/// Fails on a missing or unparseable module, a cross-module name clash, an
/// undefined export, or an unresolved/ambiguous qualified reference.
pub fn resolve_modules(root: Program, base: &Path) -> Result<Program, Error> {
    resolve_modules_in(root, &default_roots(base))
}

/// Like [`resolve_modules`], but against an explicit module search path.
///
/// The roots are the project root, its dependencies, and the stdlib. The
/// single-`base` form is the common case; this form threads dependency roots for
/// a project build.
///
/// # Errors
/// Fails on a missing or unparseable module, a cross-module name clash, an
/// undefined export, or an unresolved/ambiguous qualified reference.
pub fn resolve_modules_in(root: Program, roots: &[Root]) -> Result<Program, Error> {
    if root.imports.is_empty() {
        return Ok(resolve(root)?);
    }

    let mut modules = load(&root, roots)?;
    let mut mods: Vec<ModInfo> = modules
        .iter()
        .map(|m| {
            let path = m.path.join(".");
            let exports = exports_of(&m.prog)
                .into_iter()
                .map(|n| {
                    let canon = format!("{path}.{n}");
                    (n, canon)
                })
                .collect();
            ModInfo { path, exports }
        })
        .collect();
    let by_path: BTreeMap<String, usize> = mods
        .iter()
        .enumerate()
        .map(|(i, m)| (m.path.clone(), i))
        .collect();
    add_reexports(&mut mods, &modules, &by_path)?;

    // The root is the empty-path module: its own names (and the prelude prepended
    // to it) stay bare, so `main` and the prelude keep their global symbols.
    let root_own = canon_of(&root, None);
    let (root_unqual, root_quals) = build_scope(&root.imports, &by_path, &mods)?;
    let mut root = root;
    Rw::new("", &root_own, &root_unqual, &root_quals, &mods, 0).program(&mut root)?;

    for (i, m) in modules.iter_mut().enumerate() {
        let path = m.path.join(".");
        let own = canon_of(&m.prog, Some(&path));
        let (unqual, quals) = build_scope(&m.prog.imports, &by_path, &mods)?;
        // Each module lands in its own span band; see `Rw::span_delta`.
        let delta = (i + 1) << SPAN_BAND_SHIFT;
        Rw::new(&path, &own, &unqual, &quals, &mods, delta).program(&mut m.prog)?;
    }

    Ok(merge(root, modules))
}

/// The bare names a program's imports open into unqualified scope.
///
/// Each maps to its canonical symbol, with the program's own definitions removed
/// (a local definition shadows an import of the same name). The REPL applies this
/// to interactively typed expressions so a bare `map` resolves through the
/// prelude's glob imports exactly as it does inside a file body.
///
/// # Errors
/// Fails on a missing or unparseable imported module.
pub fn import_bindings(
    program: &Program,
    roots: &[Root],
) -> Result<BTreeMap<String, String>, Error> {
    if program.imports.is_empty() {
        return Ok(BTreeMap::new());
    }
    let modules = load(program, roots)?;
    let mut mods: Vec<ModInfo> = modules
        .iter()
        .map(|m| {
            let path = m.path.join(".");
            let exports = exports_of(&m.prog)
                .into_iter()
                .map(|n| {
                    let canon = format!("{path}.{n}");
                    (n, canon)
                })
                .collect();
            ModInfo { path, exports }
        })
        .collect();
    let by_path: BTreeMap<String, usize> = mods
        .iter()
        .enumerate()
        .map(|(i, m)| (m.path.clone(), i))
        .collect();
    add_reexports(&mut mods, &modules, &by_path)?;
    let (mut unqual, _) = build_scope(&program.imports, &by_path, &mods)?;
    for own in binders(program) {
        unqual.remove(&own);
    }
    Ok(unqual)
}

/// Rewrite an expression's bare references to canonical symbols.
///
/// Bare names are resolved against `imports` (from [`import_bindings`]); lambda
/// and `match` binders shadow imports, and unknown names stay bare for later
/// phases. The REPL uses this to resolve an interactively typed expression
/// against the prelude's import scope, which the program-level resolver only
/// reaches for file bodies.
///
/// # Errors
/// Surfaces the same scope errors the program resolver would for a malformed
/// reference.
pub fn resolve_expr(expr: &mut S<Expr>, imports: &BTreeMap<String, String>) -> Result<(), Error> {
    if imports.is_empty() {
        return Ok(());
    }
    let own = BTreeMap::new();
    let quals = BTreeMap::new();
    let mods: &[ModInfo] = &[];
    let mut rw = Rw::new("", &own, imports, &quals, mods, 0);
    rw.expr(expr);
    rw.err.take().map_or(Ok(()), |e| Err(Error::Type(e)))
}

/// Map every top-level name a module binds to its canonical form. An exported
/// name becomes `Data.Map.insert` (dotted, the symbol an importer reaches); a
/// private name becomes `Data.Map@helper` (the `@` is unforgeable in source and
/// codegen rewrites it to a dot). The root module (`path == None`) is the
/// empty-path module: its names stay bare.
fn canon_of(p: &Program, path: Option<&str>) -> BTreeMap<String, String> {
    let exports = exports_of(p);
    binders(p)
        .into_iter()
        .map(|n| {
            let canon = match path {
                None => n.clone(),
                Some(path) if exports.contains(&n) => format!("{path}.{n}"),
                Some(path) => crate::names::private(path, &n),
            };
            (n, canon)
        })
        .collect()
}

/// Build a module's import scope: the unqualified bindings a selective import
/// brings into bare scope (each mapped to its canonical symbol), and the
/// qualifier table mapping a qualifier (alias, else last path component) to the
/// modules it names. A selective import also registers its qualifier, so
/// `import M (a)` admits both bare `a` and `M.a`.
fn build_scope(
    imports: &[ImportDecl],
    by_path: &BTreeMap<String, usize>,
    mods: &[ModInfo],
) -> Result<(Unqualified, Quals), Error> {
    let mut unqualified: Unqualified = BTreeMap::new();
    let mut quals: Quals = BTreeMap::new();
    for imp in imports {
        let path = imp.path.join(".");
        let idx = *by_path
            .get(path.as_str())
            .ok_or_else(|| Error::Resolve(format!("cannot resolve import of module `{path}`")))?;
        // A glob import (`import M (..)`) opens every exported name into
        // unqualified scope; a selective import opens just the listed names.
        let opened: Vec<(String, String)> = if imp.glob {
            mods[idx]
                .exports
                .iter()
                .map(|(n, c)| (n.clone(), c.clone()))
                .collect()
        } else if let Some(names) = &imp.names {
            let mut v = Vec::with_capacity(names.len());
            for n in names {
                let Some(canon) = mods[idx].exports.get(n) else {
                    return Err(Error::Resolve(format!(
                        "module `{path}` does not export `{n}`"
                    )));
                };
                v.push((n.clone(), canon.clone()));
            }
            v
        } else {
            Vec::new()
        };
        for (n, canon) in opened {
            if let Some(prev) = unqualified.insert(n.clone(), canon.clone()) {
                if prev != canon {
                    return Err(Error::Resolve(format!(
                        "`{n}` is ambiguous: brought unqualified by `{prev}` and `{canon}`"
                    )));
                }
            }
        }
        // The full module path is always a valid qualifier (`Geo.Util.one`); the
        // short name (alias, else last component) is the convenient one
        // (`Util.one`). Register both, skipping the short when it equals the path.
        let short = imp
            .alias
            .clone()
            .unwrap_or_else(|| imp.path.last().cloned().unwrap_or_default());
        // Register the same module under a qualifier at most once: a module the
        // prelude already opened and the user imports again names one module, not
        // two, so it must not read as ambiguous. Distinct modules sharing a short
        // name still each get an entry, which is the genuine ambiguity.
        push_unique(quals.entry(path.clone()).or_default(), idx);
        if short != path {
            push_unique(quals.entry(short).or_default(), idx);
        }
    }
    Ok((unqualified, quals))
}

fn push_unique(v: &mut Vec<usize>, idx: usize) {
    if !v.contains(&idx) {
        v.push(idx);
    }
}

/// Propagate `pub import` re-exports: a module that `pub import`s names from
/// another adds them to its own export table, each pointing at the original
/// definition's canonical symbol. Iterated to a fixpoint so a chain of
/// re-exports (A re-exports from B, which re-exports from C) fully resolves. An
/// own definition shadows a re-export of the same name. A `pub import` with no
/// name list re-exports everything the source currently exports.
fn add_reexports(
    mods: &mut [ModInfo],
    modules: &[Module],
    by_path: &BTreeMap<String, usize>,
) -> Result<(), Error> {
    loop {
        let snapshot: Vec<Exports> = mods.iter().map(|m| m.exports.clone()).collect();
        let mut changed = false;
        for (ti, m) in modules.iter().enumerate() {
            for imp in m.prog.imports.iter().filter(|i| i.reexport) {
                let path = imp.path.join(".");
                let si = *by_path.get(path.as_str()).ok_or_else(|| {
                    Error::Resolve(format!("cannot resolve import of module `{path}`"))
                })?;
                let src = &snapshot[si];
                let names: Vec<String> = imp
                    .names
                    .as_ref()
                    .map_or_else(|| src.keys().cloned().collect(), Clone::clone);
                for n in names {
                    if let Some(canon) = src.get(&n) {
                        if let Entry::Vacant(e) = mods[ti].exports.entry(n) {
                            e.insert(canon.clone());
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    Ok(())
}

/// Concatenate the rewritten modules into the root, producing one flat program.
fn merge(mut root: Program, modules: Vec<Module>) -> Program {
    for m in modules {
        let p = m.prog;
        root.types.extend(p.types);
        root.effects.extend(p.effects);
        root.errors.extend(p.errors);
        root.aliases.extend(p.aliases);
        root.synonyms.extend(p.synonyms);
        root.classes.extend(p.classes);
        root.instances.extend(p.instances);
        root.canonicals.extend(p.canonicals);
        root.patterns.extend(p.patterns);
        root.fns.extend(p.fns);
        root.opaques.extend(p.opaques);
    }
    root.imports.clear();
    root
}

/// A scope-aware rewriter for one module. References to the module's own
/// top-level names (and a selective import's unqualified names) become their
/// canonical form; a qualified reference resolves to the imported module's
/// canonical symbol; local bindings (params, let/var, match vars, ...) are never
/// rewritten. A bare name in no scope is left unchanged, so builtins, effect-op
/// names, and prelude names flow through untouched.
struct Rw<'a> {
    module: &'a str,
    own: &'a BTreeMap<String, String>,
    unqualified: &'a BTreeMap<String, String>,
    quals: &'a BTreeMap<String, Vec<usize>>,
    mods: &'a [ModInfo],
    // Per-module span offset. Each module is parsed with byte offsets from 0, so
    // two modules' nodes can share a span; the type checker's span-keyed maps
    // (`span_types`, `dicts`, `fixed`, ...) would then collide and the elaborator
    // would read one module's type for another's expression. Shifting every node
    // into a disjoint high band keyed by module index makes spans globally
    // unique. The root module keeps delta 0 (real source offsets).
    span_delta: usize,
    locals: Vec<String>,
    err: Option<TypeError>,
}

impl<'a> Rw<'a> {
    const fn new(
        module: &'a str,
        own: &'a BTreeMap<String, String>,
        unqualified: &'a BTreeMap<String, String>,
        quals: &'a BTreeMap<String, Vec<usize>>,
        mods: &'a [ModInfo],
        span_delta: usize,
    ) -> Self {
        Self {
            module,
            own,
            unqualified,
            quals,
            mods,
            span_delta,
            locals: Vec::new(),
            err: None,
        }
    }

    // Shift a node's span into this module's disjoint band.
    const fn shift(&self, s: &mut Span) {
        if self.span_delta != 0 {
            s.start += self.span_delta;
            s.end += self.span_delta;
        }
    }

    fn program(mut self, p: &mut Program) -> Result<(), Error> {
        for d in &mut p.types {
            d.name = self.canon(&d.name);
            for c in &mut d.ctors {
                c.name = self.canon(&c.name);
                for a in &mut c.args {
                    self.ty(a);
                }
                if let Some(fields) = &mut c.fields {
                    for (_, t) in fields {
                        self.ty(t);
                    }
                }
            }
        }
        for e in &mut p.effects {
            e.name = self.canon(&e.name);
            for op in &mut e.ops {
                for t in &mut op.params {
                    self.ty(t);
                }
                self.ty(&mut op.ret);
            }
        }
        for er in &mut p.errors {
            er.name = self.canon(&er.name);
            for t in &mut er.params {
                self.ty(t);
            }
        }
        for a in &mut p.aliases {
            a.name = self.canon(&a.name);
            for l in &mut a.labels {
                self.efflabel(l);
            }
        }
        for s in &mut p.synonyms {
            s.name = self.canon(&s.name);
            self.ty(&mut s.ty);
        }
        for c in &mut p.classes {
            c.name = self.canon(&c.name);
            for (_, t) in &mut c.methods {
                self.ty(t);
            }
        }
        for inst in &mut p.instances {
            inst.module = self.module.to_string();
            inst.class = self.value(&inst.class, inst.span);
            self.ty(&mut inst.head);
            for con in &mut inst.context {
                self.constraint(con);
            }
            for m in &mut inst.methods {
                self.decl(m, false);
            }
        }
        for c in &mut p.canonicals {
            // Mirror instance canonicalization: class and head become global
            // symbols so the designation keys on the same `(class, head)` the
            // instance store does. `name` is a global instance reference, left
            // bare exactly like the names in `inst_keys`.
            c.class = self.value(&c.class, c.span);
            self.ty(&mut c.head);
        }
        for pat in &mut p.patterns {
            pat.name = self.canon(&pat.name);
            pat.for_ty = self.value(&pat.for_ty, pat.span);
            let base = self.locals.len();
            self.locals.extend(pat.params.iter().cloned());
            self.expr(&mut pat.view);
            if let Some(make) = &mut pat.make {
                self.expr(make);
            }
            self.locals.truncate(base);
        }
        for f in &mut p.fns {
            self.decl(f, true);
        }
        self.err.take().map_or(Ok(()), |e| Err(Error::Type(e)))
    }

    fn decl(&mut self, d: &mut Decl, canon_name: bool) {
        if canon_name {
            d.name = self.canon(&d.name);
        }
        let base = self.locals.len();
        // Defaults are capture-free: resolved before the function's own
        // parameters enter scope, so they see only the enclosing bindings.
        for p in &mut d.params {
            if let Some(t) = &mut p.ty {
                self.ty(t);
            }
            if let Some(def) = &mut p.default {
                self.expr(def);
            }
        }
        for p in &mut d.params {
            self.locals.push(p.name.clone());
        }
        if let Some(t) = &mut d.ret {
            self.ty(t);
        }
        if let Some(effs) = &mut d.eff {
            for l in effs {
                self.efflabel(l);
            }
        }
        for c in &mut d.constraints {
            self.constraint(c);
        }
        self.expr(&mut d.body);
        self.locals.truncate(base);
    }

    fn constraint(&mut self, c: &mut Constraint) {
        c.class = self.value(&c.class, c.span);
        self.ty(&mut c.ty);
    }

    fn efflabel(&mut self, l: &mut EffLabel) {
        l.name = self.value(&l.name, Span::empty(0));
        for a in &mut l.args {
            self.ty(a);
        }
    }

    fn ty(&mut self, t: &mut Ty) {
        match t {
            Ty::Con(name, args) => {
                *name = self.value(name, Span::empty(0));
                for a in args {
                    self.ty(a);
                }
            }
            Ty::Fun(params, row, ret) => {
                for p in params {
                    self.ty(p);
                }
                if let Row::Cons(labels, _) = row {
                    for l in labels {
                        self.efflabel(l);
                    }
                }
                self.ty(ret);
            }
            Ty::Forall(_, inner) => self.ty(inner),
            Ty::Tuple(items) => {
                for i in items {
                    self.ty(i);
                }
            }
            _ => {}
        }
    }

    fn expr(&mut self, e: &mut S<Expr>) {
        self.shift(&mut e.span);
        let span = e.span;
        match &mut e.node {
            Expr::Var(n) => *n = self.value(n, span),
            Expr::Bin(_, a, b) | Expr::Pipe(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Expr::If(c, t, f) => {
                self.expr(c);
                self.expr(t);
                self.expr(f);
            }
            Expr::Let(x, v, body) => {
                self.expr(v);
                let base = self.locals.len();
                self.locals.push(x.clone());
                self.expr(body);
                self.locals.truncate(base);
            }
            Expr::Lam(params, body) => {
                let base = self.locals.len();
                for p in params {
                    if let Some(t) = &mut p.ty {
                        self.ty(t);
                    }
                    self.locals.push(p.name.clone());
                }
                self.expr(body);
                self.locals.truncate(base);
            }
            Expr::Call(f, args) => {
                self.expr(f);
                for a in args {
                    self.expr(a);
                }
            }
            Expr::Match(s, arms) => {
                self.expr(s);
                for arm in arms {
                    let base = self.locals.len();
                    self.pat(&mut arm.pat);
                    if let Some(g) = &mut arm.guard {
                        self.expr(g);
                    }
                    self.expr(&mut arm.body);
                    self.locals.truncate(base);
                }
            }
            Expr::List(xs) | Expr::Tuple(xs) => {
                for x in xs {
                    self.expr(x);
                }
            }
            Expr::FieldAccess(x, _) => self.expr(x),
            Expr::RecordCreate(name, fields) => {
                *name = self.value(name, span);
                for (_, v) in fields {
                    self.expr(v);
                }
            }
            Expr::RecordUpdate(x, _, fields) => {
                self.expr(x);
                for (_, v) in fields {
                    self.expr(v);
                }
            }
            Expr::RecordUpdatePath(x, paths) => {
                self.expr(x);
                for (steps, op) in paths {
                    for s in steps.iter_mut() {
                        if let Some(e) = s.sub_expr_mut() {
                            self.expr(e);
                        }
                    }
                    self.expr(op.expr_mut());
                }
            }
            Expr::Handle(body, arms) => {
                self.expr(body);
                for arm in arms {
                    self.handler_arm(arm);
                }
            }
            Expr::Mask(label, body) => {
                *label = self.value(label, span);
                self.expr(body);
            }
            Expr::Inst(x, tys) => {
                self.expr(x);
                for t in tys {
                    *t = self.value(t, span);
                }
            }
            Expr::Index(recv, key) => {
                self.expr(recv);
                self.expr(key);
            }
            Expr::IndexSet(recv, key, val) => {
                self.expr(recv);
                self.expr(key);
                self.expr(val);
            }
            Expr::Ann(x, t) => {
                self.expr(x);
                self.ty(t);
            }
            Expr::Sugar(s) => self.sugar(s, span),
            // A parse-time marker carries no name to resolve; its operands (the
            // wrapped `e?` expr, interpolation holes) ride in the enclosing
            // `Call` and are resolved there.
            Expr::Marker(_)
            | Expr::Int(_)
            | Expr::Float(_)
            | Expr::Char(_)
            | Expr::Bool(_)
            | Expr::Unit
            | Expr::Str(_) => {}
        }
    }

    fn sugar(&mut self, s: &mut Sugar<Surface>, span: Span) {
        match s {
            Sugar::Default(a, b) | Sugar::Transact(a, b) | Sugar::Compose(_, a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Sugar::VarDecl(x, v, body) => {
                self.expr(v);
                let base = self.locals.len();
                self.locals.push(x.clone());
                self.expr(body);
                self.locals.truncate(base);
            }
            Sugar::OptChain(x, _) => self.expr(x),
            Sugar::ReadPath(b, steps) => {
                self.expr(b);
                for s in steps.iter_mut() {
                    if let Some(e) = s.sub_expr_mut() {
                        self.expr(e);
                    }
                }
            }
            Sugar::NamedHandle(name, body, arms) => {
                let base = self.locals.len();
                self.locals.push(name.clone());
                self.expr(body);
                self.locals.truncate(base);
                for arm in arms {
                    self.handler_arm(arm);
                }
            }
            Sugar::Assign(_, v) => self.expr(v),
            Sugar::IndexAssign(recv, key, v) => {
                self.expr(recv);
                self.expr(key);
                self.expr(v);
            }
            Sugar::Throw(name, args) => {
                *name = self.value(name, span);
                for a in args {
                    self.expr(a);
                }
            }
            Sugar::TryCatch(body, arms) => {
                self.expr(body);
                for arm in arms {
                    arm.name = self.value(&arm.name, arm.span);
                    let base = self.locals.len();
                    self.locals.extend(arm.binders.iter().cloned());
                    self.expr(&mut arm.body);
                    self.locals.truncate(base);
                }
            }
            Sugar::For(x, iter, quals, body) => {
                self.expr(iter);
                let base = self.locals.len();
                self.locals.push(x.clone());
                self.quals(quals);
                self.expr(body);
                self.locals.truncate(base);
            }
            Sugar::Comp(head, x, source, quals) => {
                self.expr(source);
                let base = self.locals.len();
                self.locals.push(x.clone());
                self.quals(quals);
                self.expr(head);
                self.locals.truncate(base);
            }
            Sugar::Range(pre, hi) => {
                for e in pre {
                    self.expr(e);
                }
                self.expr(hi);
            }
            Sugar::While(cond, body) => {
                if let Some(c) = cond {
                    self.expr(c);
                }
                self.expr(body);
            }
            Sugar::Break | Sugar::Continue => {}
            Sugar::Return(e) => self.expr(e),
        }
    }

    fn quals(&mut self, quals: &mut [Qualifier]) {
        for q in quals {
            match q {
                Qualifier::Guard(g) => self.expr(g),
                Qualifier::Bind(y, e) => {
                    self.expr(e);
                    self.locals.push(y.clone());
                }
            }
        }
    }

    // Effect-op names live in the effect namespace (not the top-level binder
    // set), so they are left bare; only the bound locals are tracked.
    fn handler_arm(&mut self, arm: &mut HandlerArm) {
        let base = self.locals.len();
        match arm {
            HandlerArm::Return(x, body) | HandlerArm::Sugar(SugarArm::Val(x, body)) => {
                self.locals.push(x.clone());
                self.expr(body);
            }
            HandlerArm::Op(_, params, k, body) => {
                self.locals.extend(params.iter().cloned());
                self.locals.push(k.clone());
                self.expr(body);
            }
            HandlerArm::Sugar(
                SugarArm::Fun(_, params, body) | SugarArm::Final(_, params, body),
            ) => {
                self.locals.extend(params.iter().cloned());
                self.expr(body);
            }
        }
        self.locals.truncate(base);
    }

    fn pat(&mut self, p: &mut S<Pattern>) {
        self.shift(&mut p.span);
        match &mut p.node {
            Pattern::Var(n) => self.locals.push(n.clone()),
            Pattern::Ctor(name, args) => {
                *name = self.value(name, p.span);
                for a in args {
                    self.pat(a);
                }
            }
            Pattern::Record(name, fields, _) => {
                *name = self.value(name, p.span);
                for (_, sp) in fields {
                    self.pat(sp);
                }
            }
            Pattern::Tuple(items) => {
                for it in items {
                    self.pat(it);
                }
            }
            _ => {}
        }
    }

    /// Canonicalize a top-level definition name to its module-qualified form.
    fn canon(&self, name: &str) -> String {
        self.own
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    /// Resolve a referenced name: locals untouched; `Q.n` resolved through the
    /// qualifier table; the module's own names and any unqualified imports
    /// rewritten to canonical form; everything else (builtins, effect ops,
    /// prelude) left bare for later phases.
    fn value(&mut self, name: &str, span: Span) -> String {
        if self.locals.iter().any(|l| l == name) {
            return name.to_string();
        }
        // Split on the LAST dot, so a multi-segment qualifier (`Geo.Util.one`)
        // resolves as (`Geo.Util`, `one`) and a single one (`Map.insert`) as
        // (`Map`, `insert`).
        if let Some((q, n)) = name.rsplit_once('.') {
            return self.qualified(q, n, name, span);
        }
        if let Some(canon) = self.own.get(name).or_else(|| self.unqualified.get(name)) {
            return canon.clone();
        }
        name.to_string()
    }

    fn qualified(&mut self, q: &str, n: &str, full: &str, span: Span) -> String {
        let Some(idxs) = self.quals.get(q) else {
            self.record(
                span,
                format!("`{full}`: no imported module qualified `{q}`"),
            );
            return full.to_string();
        };
        let hits: Vec<&ModInfo> = idxs
            .iter()
            .filter(|&&i| self.mods[i].exports.contains_key(n))
            .map(|&i| &self.mods[i])
            .collect();
        match hits.as_slice() {
            [] => {
                self.record(span, format!("module `{q}` does not export `{n}`"));
                full.to_string()
            }
            [m] => m
                .exports
                .get(n)
                .cloned()
                .unwrap_or_else(|| full.to_string()),
            many => {
                let paths: Vec<&str> = many.iter().map(|m| m.path.as_str()).collect();
                self.record(
                    span,
                    format!("`{full}` is ambiguous: exported by {}", paths.join(", ")),
                );
                full.to_string()
            }
        }
    }

    fn record(&mut self, span: Span, msg: String) {
        if self.err.is_none() {
            self.err = Some(TypeError::Scope { span, msg });
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::parse;

    #[test]
    fn pub_marks_exports_and_resolves() {
        let src = "pub fn f() = 1\npub type Color = Red | Green\nfn main() = print(f())\n";
        let prog = super::resolve(parse(src).unwrap().program).unwrap();
        assert!(prog.exports.contains("f"));
        assert!(prog.exports.contains("Color"));
        assert!(!prog.exports.contains("main"));
    }
}
