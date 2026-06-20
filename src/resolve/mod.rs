//! Name resolution: canonicalizes references to globally unique symbols.
//!
//! A program with no imports is a single module (the user's source plus the
//! implicit prelude); resolution is then the identity on names and only
//! validates the export table. With imports, [`resolve_modules`] loads the
//! referenced files, renames each imported module's private names to a
//! collision-proof canonical form, resolves qualified references, and merges
//! everything into one flat [`Program`] for the rest of the pipeline.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use marginalia::Span;

use crate::error::{Error, TypeError};
use crate::syntax::ast::{
    Constraint, Decl, EffLabel, Expr, HandlerArm, ImportDecl, Pattern, Program, Qualifier, Row,
    Sugar, SugarArm, Surface, Ty, S,
};

mod load;
pub use load::{load, Module};

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
/// constructors of every `pub` data type (exported transparently). An `opaque`
/// type exports its name only; its constructors stay module-private, so the
/// existing private-namespacing machinery hides them from importers.
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

/// A loaded module's identity and the bare names it exports.
struct ModExports {
    path: String,
    exports: BTreeSet<String>,
}

/// Resolve a program that may import other modules, loading them under `base`.
///
/// Import-free programs take the single-module [`resolve`] fast path unchanged.
///
/// # Errors
/// Fails on a missing or unparseable module, a cross-module name clash, an
/// undefined export, or an unresolved/ambiguous qualified reference.
pub fn resolve_modules(root: Program, base: &Path) -> Result<Program, Error> {
    if root.imports.is_empty() {
        return Ok(resolve(root)?);
    }

    let mut modules = load(&root, base)?;
    let mods: Vec<ModExports> = modules
        .iter()
        .map(|m| ModExports {
            path: m.path.join("."),
            exports: exports_of(&m.prog),
        })
        .collect();
    let by_path: BTreeMap<&str, usize> = mods
        .iter()
        .enumerate()
        .map(|(i, m)| (m.path.as_str(), i))
        .collect();

    eager_unique(&root, &mods)?;

    let no_privates = BTreeMap::new();
    let root_quals = build_quals(&root.imports, &by_path, &mods)?;
    let mut root = root;
    Rw::new(&no_privates, &root_quals, &mods).program(&mut root)?;

    for m in &mut modules {
        let path = m.path.join(".");
        let privates = module_privates(&m.prog, &path);
        let quals = build_quals(&m.prog.imports, &by_path, &mods)?;
        Rw::new(&privates, &quals, &mods).program(&mut m.prog)?;
    }

    Ok(merge(root, modules))
}

/// Exported names must be globally unique: no two modules may export the same
/// bare name, and none may shadow a name the root (prelude included) binds.
/// Private names are namespaced separately, so they never participate.
fn eager_unique(root: &Program, mods: &[ModExports]) -> Result<(), Error> {
    let root_binders = binders(root);
    let mut owner: BTreeMap<&str, &str> = BTreeMap::new();
    for b in &root_binders {
        owner.insert(b, "(this program)");
    }
    for m in mods {
        for n in &m.exports {
            if let Some(prev) = owner.insert(n, &m.path) {
                return Err(Error::Resolve(format!(
                    "name `{n}` exported by module `{}` clashes with `{prev}`",
                    m.path
                )));
            }
        }
    }
    Ok(())
}

/// A module's private top-level names mapped to collision-proof canonical names
/// (`Data.Map@helper`); the `@` is unforgeable in source and codegen rewrites it
/// back to a dot for a valid symbol.
fn module_privates(p: &Program, path: &str) -> BTreeMap<String, String> {
    let exports = exports_of(p);
    binders(p)
        .into_iter()
        .filter(|n| !exports.contains(n))
        .map(|n| {
            let canon = format!("{path}@{n}");
            (n, canon)
        })
        .collect()
}

/// Map each import's qualifier (its alias, else the last path component) to the
/// modules it names, validating selective import lists against their exports.
fn build_quals(
    imports: &[ImportDecl],
    by_path: &BTreeMap<&str, usize>,
    mods: &[ModExports],
) -> Result<BTreeMap<String, Vec<usize>>, Error> {
    let mut quals: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for imp in imports {
        let path = imp.path.join(".");
        let idx = *by_path
            .get(path.as_str())
            .ok_or_else(|| Error::Resolve(format!("cannot resolve import of module `{path}`")))?;
        if let Some(names) = &imp.names {
            for n in names {
                if !mods[idx].exports.contains(n) {
                    return Err(Error::Resolve(format!(
                        "module `{path}` does not export `{n}`"
                    )));
                }
            }
        }
        let qual = imp
            .alias
            .clone()
            .unwrap_or_else(|| imp.path.last().cloned().unwrap_or_default());
        quals.entry(qual).or_default().push(idx);
    }
    Ok(quals)
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
        root.patterns.extend(p.patterns);
        root.fns.extend(p.fns);
        root.opaques.extend(p.opaques);
    }
    root.imports.clear();
    root
}

/// A scope-aware rewriter for one module. References to the module's own private
/// top-level names become their canonical form; qualified references resolve to
/// the bare exported name; local bindings (params, let/var, match vars, ...) are
/// never rewritten.
struct Rw<'a> {
    privates: &'a BTreeMap<String, String>,
    quals: &'a BTreeMap<String, Vec<usize>>,
    mods: &'a [ModExports],
    locals: Vec<String>,
    err: Option<TypeError>,
}

impl<'a> Rw<'a> {
    const fn new(
        privates: &'a BTreeMap<String, String>,
        quals: &'a BTreeMap<String, Vec<usize>>,
        mods: &'a [ModExports],
    ) -> Self {
        Self {
            privates,
            quals,
            mods,
            locals: Vec::new(),
            err: None,
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
            inst.class = self.value(&inst.class, inst.span);
            self.ty(&mut inst.head);
            for con in &mut inst.context {
                self.constraint(con);
            }
            for m in &mut inst.methods {
                self.decl(m, false);
            }
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
                for (_, v) in paths {
                    self.expr(v);
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
            Sugar::Default(a, b) | Sugar::Transact(a, b) => {
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

    /// Canonicalize a top-level definition name (private -> namespaced).
    fn canon(&self, name: &str) -> String {
        self.privates
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    /// Resolve a referenced name: locals untouched, `Q.n` resolved through the
    /// qualifier table, own privates rewritten, everything else left bare.
    fn value(&mut self, name: &str, span: Span) -> String {
        if self.locals.iter().any(|l| l == name) {
            return name.to_string();
        }
        if let Some((q, n)) = name.split_once('.') {
            return self.qualified(q, n, name, span);
        }
        self.privates
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    fn qualified(&mut self, q: &str, n: &str, full: &str, span: Span) -> String {
        let Some(idxs) = self.quals.get(q) else {
            self.record(
                span,
                format!("`{full}`: no imported module qualified `{q}`"),
            );
            return full.to_string();
        };
        let hits: Vec<&str> = idxs
            .iter()
            .filter(|&&i| self.mods[i].exports.contains(n))
            .map(|&i| self.mods[i].path.as_str())
            .collect();
        match hits.as_slice() {
            [] => {
                self.record(span, format!("module `{q}` does not export `{n}`"));
                full.to_string()
            }
            [_] => n.to_string(),
            many => {
                self.record(
                    span,
                    format!("`{full}` is ambiguous: exported by {}", many.join(", ")),
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
