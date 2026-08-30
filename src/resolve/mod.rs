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
use std::mem;
use std::path::{Path, PathBuf};

use marginalia::Span;

use crate::error::{suggest, Error, TypeError};
use crate::stdlib::STDLIB;
use crate::syntax::ast::{
    Constraint, Decl, EffLabel, Expr, HandlerArm, ImportDecl, MigrationDir, MigrationRoute,
    Pattern, PreludeCapture, Program, Qualifier, Row, Sugar, SugarArm, Surface, Ty, S,
};
use crate::syntax::desugar::routes_to_current;
use crate::{kw, names};

mod identity;
mod lints;
mod load;
use identity::{CanonicalName, ModuleName};

pub use lints::{lint_bindings, lint_prelude_captures, prelude_capture};
pub use load::{
    load, serving_root, Module, Root, SourceBundleArtifactKind, SourceBundleIdentity,
    SourceBundleKind, SourceBundleOrigin,
};

/// The search path for a single-file or test program: the given source root,
/// then the embedded standard library.
#[must_use]
pub fn default_roots(base: &Path) -> Vec<Root> {
    vec![Root::Dir(base.to_path_buf()), Root::Embedded(STDLIB)]
}

/// The search path for a project.
///
/// The project source root, each path dependency's source root (in declared
/// order), then the embedded standard library. A dependency's modules resolve
/// under its own root; the project shadows a name it redefines.
#[must_use]
pub fn project_roots(src_dir: &Path, dep_dirs: &[PathBuf]) -> Vec<Root> {
    project_roots_with_std(src_dir, dep_dirs, Root::Embedded(STDLIB))
}

/// The search path for a project with an explicit standard-library source root.
///
/// Lock-aware package builds use this to replace the compiler's embedded stdlib
/// with a store-served source bundle when `prism.lock` pins a different Std root.
#[must_use]
pub fn project_roots_with_std(src_dir: &Path, dep_dirs: &[PathBuf], std_root: Root) -> Vec<Root> {
    project_roots_with_packages_and_std(src_dir, dep_dirs, Vec::new(), std_root)
}

/// The search path for a project with store-served package roots.
///
/// Package roots sit after path dependencies and before Std: a project shadows a
/// dependency, a path dependency shadows a store package, and all user packages
/// shadow the standard library just like ordinary source roots do.
#[must_use]
pub fn project_roots_with_packages_and_std(
    src_dir: &Path,
    dep_dirs: &[PathBuf],
    package_roots: Vec<Root>,
    std_root: Root,
) -> Vec<Root> {
    let mut roots = vec![Root::Dir(src_dir.to_path_buf())];
    roots.extend(dep_dirs.iter().map(|d| Root::Dir(d.clone())));
    roots.extend(package_roots);
    roots.push(std_root);
    roots
}

/// The dotted paths of every module `root` transitively imports, in load order.
///
/// A pure enumeration with no side effects: the CLI uses it to report which
/// files enter a build, without duplicating the loader's search logic.
///
/// # Errors
/// Fails when an imported module resolves in no root or does not parse.
pub fn imported_paths(root: &Program, roots: &[Root]) -> Result<Vec<String>, Error> {
    Ok(load(root, roots)?
        .into_iter()
        .map(|m| m.path.join("."))
        .collect())
}

/// A module's own top-level names, each mapped to the canonical symbol its
/// definition takes.
type Own = BTreeMap<String, CanonicalName>;

/// Bare names an import list opens, each mapped to every canonical symbol
/// offered for it.
///
/// More than one candidate arises when distinct modules open the same short name
/// into the same tier. That makes a *use* of the name ambiguous, never the import
/// itself: a module is free to export a name another module in scope also
/// exports, as long as nothing refers to it bare. Deciding this at the import
/// instead would mean every importable module has to avoid every short name any
/// module a program might also import already uses, which is what manual
/// prefixing of a module's whole surface buys back.
type Candidates = BTreeMap<String, Vec<CanonicalName>>;

/// A qualifier (alias, else last path component) mapped to the loaded modules it
/// names; an entry has more than one index only when imports share a qualifier.
type Quals = BTreeMap<String, Vec<usize>>;

/// One tier of import scope: what an import list opens into unqualified scope,
/// and the qualifiers it registers.
#[derive(Default)]
struct Scope {
    opened: Candidates,
    quals: Quals,
}

/// Everything one module's references resolve against, in precedence order.
///
/// `own`/`scope` are the region's own definitions and imports. `prelude_own`/
/// `prelude_scope` are a prepended prelude's, and are empty for every module
/// that is not a root program. A declaration below `prelude_end` is the
/// prelude's and resolves against the prelude halves alone; the user's file is
/// not in the prelude's scope, which is what stops a user definition from
/// capturing a prelude one.
///
/// `moved_prelude` holds only those prelude names a user definition displaced,
/// and is consulted last, after imports. A library module cannot import the
/// prelude's classes and types, so its references to them fall through as bare
/// names and would otherwise miss the displaced definition entirely; the table
/// is empty whenever nothing was displaced, so an unshadowed program resolves
/// byte-identically.
struct ScopeSet<'a> {
    own: &'a Own,
    scope: &'a Scope,
    prelude_own: &'a Own,
    prelude_scope: &'a Scope,
    prelude_end: usize,
    moved_prelude: &'a Own,
}

/// A module's exported names mapped to the canonical symbol each resolves to.
/// For an own definition that is `Module.name`; for a `pub import` re-export it
/// is the original definition's canonical symbol.
type Exports = BTreeMap<String, CanonicalName>;

/// Visit every top-level binder with the span of the declaration that introduces
/// it. A constructor takes its data declaration's span, since it is introduced by
/// that declaration and shares its region.
fn each_binder(p: &Program, mut f: impl FnMut(Span, &str)) {
    for d in &p.types {
        f(d.span, &d.name);
        for c in &d.ctors {
            f(d.span, &c.name);
        }
    }
    // An operation takes its effect declaration's span, for the same reason a
    // constructor takes its data declaration's: the parent declaration is what
    // introduces it and the two share a region. Leaving operations out of this
    // walk is what kept them out of every module namespace, so an operation name
    // was global across the whole standard library no matter what was imported.
    for e in &p.effects {
        f(e.span, &e.name);
        for op in &e.ops {
            f(e.span, &op.name);
        }
    }
    for e in &p.errors {
        f(e.span, &e.name);
    }
    for a in &p.aliases {
        f(a.span, &a.name);
    }
    for s in &p.synonyms {
        f(s.span, &s.name);
    }
    for c in &p.classes {
        f(c.span, &c.name);
    }
    for pat in &p.patterns {
        f(pat.span, &pat.name);
    }
    for d in &p.fns {
        f(d.span, &d.name);
    }
}

/// Every name a program binds at the top level: the universe a `pub` export or
/// an importer may refer to (type and constructor names, effects, errors,
/// aliases, classes, pattern synonyms, functions).
#[must_use]
pub fn binders(p: &Program) -> BTreeSet<String> {
    let mut s = BTreeSet::new();
    each_binder(p, |_, n| {
        s.insert(n.to_string());
    });
    s
}

/// The top-level names a prepended prelude defines, and the ones the user's own
/// file defines, split at [`Program::prelude_end`]. With no prelude prefix the
/// first set is empty and every name belongs to the user.
fn binders_by_region(p: &Program) -> (BTreeSet<String>, BTreeSet<String>) {
    let (mut prelude, mut user) = (BTreeSet::new(), BTreeSet::new());
    let end = p.prelude_end;
    each_binder(p, |span, n| {
        let side = if span.start < end {
            &mut prelude
        } else {
            &mut user
        };
        side.insert(n.to_string());
    });
    (prelude, user)
}

/// The names a module makes visible to importers: every `pub` item, plus the
/// constructors of every transparent `pub` data type and the operations of every
/// `pub` effect. An `opaque` type exports its name only; its constructors stay
/// module-private, so their absence from this set hides them from importers.
///
/// An effect's operations ride on the effect's own visibility: performing or
/// handling one is the only way to use the effect at all, so a `pub effect`
/// whose operations stayed private would export a name no importer could do
/// anything with.
fn exports_of(p: &Program) -> BTreeSet<String> {
    let mut e = p.exports.clone();
    for d in &p.types {
        if p.exports.contains(&d.name) && !p.opaques.contains(&d.name) {
            e.extend(d.ctors.iter().map(|c| c.name.clone()));
        }
    }
    e.extend(operations_of(p));
    e
}

/// The operation names a module's `pub` effects make visible to importers.
///
/// Kept apart from the rest of [`exports_of`] because an operation is the one
/// exported name with no qualified spelling: a handler clause names the
/// operation bare, so `M.op` is not something an importer can write there. The
/// set is what lets a bare clause name reach an imported operation.
fn operations_of(p: &Program) -> BTreeSet<String> {
    p.effects
        .iter()
        .filter(|eff| p.exports.contains(&eff.name))
        .flat_map(|eff| eff.ops.iter().map(|op| op.name.clone()))
        .collect()
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
        return Err(TypeError::ScopeFailure {
            span: Span::empty(0),
            msg: format!("cannot export `{name}`: no such definition"),
        });
    }
    Ok(program)
}

/// A loaded module's identity and the canonical symbol each exported name
/// resolves to (its own definitions plus any `pub import` re-exports).
struct ModInfo {
    path: ModuleName,
    exports: Exports,
    /// The subset of `exports` that names effect operations. See
    /// [`operations_of`].
    operations: BTreeSet<String>,
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
    if is_single_region(&root) {
        return Ok(resolve(root)?);
    }
    let modules = load(&root, roots)?;
    resolve_loaded_modules(root, modules)
}

/// Whether resolution is the identity on `root`'s names: no imports to rewrite
/// against, and one source region, so no prelude definition can be shadowed.
/// A prepended prelude makes the program two regions even with no imports, since
/// a user definition of a prelude name must shadow it rather than replace it.
const fn is_single_region(root: &Program) -> bool {
    root.imports.is_empty() && root.prelude_end == 0
}

/// Resolve a root against an already parsed and loaded module closure.
///
/// # Errors
/// Fails on a cross-module name clash, undefined export, or an unresolved or
/// ambiguous qualified reference.
pub(crate) fn resolve_loaded_modules(
    root: Program,
    modules: Vec<Module>,
) -> Result<Program, Error> {
    let (root, modules) = resolve_loaded_module_units(root, modules)?;
    Ok(merge(root, modules))
}

/// Resolve every module while retaining module boundaries and dependency bodies.
///
/// # Errors
/// Fails on a cross-module name clash, undefined export, or an unresolved or
/// ambiguous qualified reference.
pub(crate) fn resolve_loaded_module_units(
    root: Program,
    modules: Vec<Module>,
) -> Result<(Program, Vec<Module>), Error> {
    let (root, modules, _) = resolve_loaded_module_units_seeing(root, modules)?;
    Ok((root, modules))
}

/// [`resolve_loaded_module_units`], additionally returning every reference the
/// renamer resolved.
///
/// # Errors
/// Fails on a cross-module name clash, undefined export, or an unresolved or
/// ambiguous qualified reference.
pub(crate) fn resolve_loaded_module_units_seeing(
    root: Program,
    mut modules: Vec<Module>,
) -> Result<(Program, Vec<Module>, Vec<Occurrence>), Error> {
    if is_single_region(&root) {
        return Ok((resolve(root)?, modules, Vec::new()));
    }
    let (mods, by_path) = module_infos(&modules)?;

    // The root is the empty-path module: its own names stay bare, so `main` and
    // every unshadowed prelude definition keep their global symbols. The prelude
    // prepended to it is a region of its own, with its own definitions and its
    // own imports, so the two cannot capture each other.
    let (root_prelude_own, root_own) = root_owns(&root);
    let moved_prelude = moved_prelude(&root_prelude_own);
    let (prelude_imports, user_imports): (Vec<ImportDecl>, Vec<ImportDecl>) = root
        .imports
        .iter()
        .cloned()
        .partition(|i| i.span.start < root.prelude_end);
    let root_prelude_scope = build_scope(&prelude_imports, &by_path, &mods)?;
    let root_scope = build_scope(&user_imports, &by_path, &mods)?;
    let root_scopes = ScopeSet {
        own: &root_own,
        scope: &root_scope,
        prelude_own: &root_prelude_own,
        prelude_scope: &root_prelude_scope,
        prelude_end: root.prelude_end,
        moved_prelude: &moved_prelude,
    };
    let mut root = root;
    root.prelude_captures = prelude_captures(&root, &root_prelude_scope);
    let mut seen = Rw::new("", &root_scopes, &mods).program(&mut root)?;

    // An imported module carries no prelude of its own, so its prelude halves
    // stay empty and every one of its declarations resolves in the user region.
    let (no_own, no_scope) = (Own::new(), Scope::default());
    for m in &mut modules {
        let path = m.path.join(".");
        let own = own_of(&m.prog, &path, binders(&m.prog));
        let scope = build_scope(&m.prog.imports, &by_path, &mods)?;
        let scopes = ScopeSet {
            own: &own,
            scope: &scope,
            prelude_own: &no_own,
            prelude_scope: &no_scope,
            prelude_end: 0,
            moved_prelude: &moved_prelude,
        };
        seen.extend(Rw::new(&path, &scopes, &mods).program(&mut m.prog)?);
    }

    Ok((root, modules, seen))
}

/// Resolve a program and report every reference the renamer resolved, alongside
/// the resolved program.
///
/// The goto-definition and find-references relation, taken from the resolver
/// rather than reconstructed by a second walk. See [`Occurrence`].
///
/// # Errors
/// Fails on a missing or unparseable module, a cross-module name clash, an
/// undefined export, or an unresolved/ambiguous qualified reference.
pub fn resolve_modules_seeing(
    root: Program,
    roots: &[Root],
) -> Result<(Program, Vec<Occurrence>), Error> {
    if root.imports.is_empty() {
        return Ok((resolve(root)?, Vec::new()));
    }
    let modules = load(&root, roots)?;
    let (root, modules, seen) = resolve_loaded_module_units_seeing(root, modules)?;
    Ok((merge(root, modules), seen))
}

/// The bare names a program's imports open into unqualified scope.
///
/// Each maps to its canonical symbol, with the program's own definitions removed
/// (a local definition shadows an import of the same name). The REPL applies this
/// to interactively typed expressions so a bare `map` resolves through the
/// prelude's glob imports exactly as it does inside a file body. A name two
/// modules offer is dropped rather than picked between: no bare reference to it
/// resolves, which is the same answer the file-body resolver gives.
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
    let (mods, by_path) = module_infos(&modules)?;
    let mut scope = build_scope(&program.imports, &by_path, &mods)?;
    for own in binders(program) {
        scope.opened.remove(&own);
    }
    Ok(scope
        .opened
        .into_iter()
        .filter_map(|(name, candidates)| match candidates.as_slice() {
            [only] => Some((name, only.as_str().to_string())),
            _ => None,
        })
        .collect())
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
    let (no_own, no_scope) = (Own::new(), Scope::default());
    let scope = Scope {
        opened: imports
            .iter()
            .map(|(name, canonical)| (name.clone(), vec![CanonicalName::new(canonical.clone())]))
            .collect(),
        quals: Quals::new(),
    };
    let scopes = ScopeSet {
        own: &no_own,
        scope: &scope,
        prelude_own: &no_own,
        prelude_scope: &no_scope,
        prelude_end: 0,
        moved_prelude: &no_own,
    };
    let mods: &[ModInfo] = &[];
    let mut rw = Rw::new("", &scopes, mods);
    rw.expr(expr);
    rw.err.take().map_or(Ok(()), |e| Err(Error::Type(e)))
}

/// Map each of `names` to its canonical form under `path`. An exported name
/// becomes `Data.Map.insert` (dotted, the symbol an importer reaches); a private
/// name becomes `Data.Map@helper` (the `@` is unforgeable in source and native
/// codegen encodes it distinctly from `.`).
fn own_of(p: &Program, path: &str, names: BTreeSet<String>) -> Own {
    let exports = exports_of(p);
    names
        .into_iter()
        .map(|n| {
            let canon = if exports.contains(&n) {
                names::exported(path, &n)
            } else {
                names::private(path, &n)
            };
            (n, CanonicalName::new(canon))
        })
        .collect()
}

/// The root module's two definition tiers, the prelude's first.
///
/// The root is the empty-path module, so its names stay bare. A prelude
/// definition keeps its bare name too, unless the user's own file defines that
/// name as well: then the prelude's moves to the module-private
/// `@prelude@name`, so the user's definition can take the bare name without
/// capturing the prelude's own references to it. Materializing the private
/// symbol only where a collision makes it observable is what leaves every
/// program that shadows nothing byte-identical, symbols and content hash alike.
///
/// A prelude class is the one exception and never moves. Operator elaboration
/// and `deriving` name those classes directly, so moving one would leave `==`
/// resolving to a class the program no longer spells, and a user constructor
/// that merely happens to share the name would break arithmetic it never
/// mentions. A user definition of a prelude class name therefore collides with
/// it rather than shadowing it.
fn root_owns(p: &Program) -> (Own, Own) {
    let (prelude, user) = binders_by_region(p);
    let prelude_classes: BTreeSet<&str> = p
        .classes
        .iter()
        .filter(|c| c.span.start < p.prelude_end)
        .map(|c| c.name.as_str())
        .collect();
    let own_user = user
        .iter()
        .map(|n| (n.clone(), CanonicalName::new(n.clone())))
        .collect();
    let own_prelude = prelude
        .into_iter()
        .map(|n| {
            let canon = if user.contains(&n) && !prelude_classes.contains(n.as_str()) {
                names::prelude_private(&n)
            } else {
                n.clone()
            };
            (n, CanonicalName::new(canon))
        })
        .collect();
    (own_prelude, own_user)
}

/// The user's own top-level definitions that took a name the prelude had already
/// opened into unqualified scope, keyed by that name.
///
/// The prelude glob-imports a set of standard modules, so a bare `count` in a
/// file means `Data.List.count` until the file defines its own `count`; from then
/// on every unqualified use in the file means the local one, including uses the
/// author wrote before adding the definition. Nothing is ill-formed about that,
/// and the resolver keeps resolving it the same way, so this is a report of the
/// silent change of meaning, computed at the only point that can see it.
///
/// A name two prelude imports both offer is skipped: a bare reference to it was
/// already ambiguous and resolved to neither, so the user's definition displaced
/// nothing.
fn prelude_captures(root: &Program, prelude_scope: &Scope) -> BTreeMap<String, PreludeCapture> {
    let mut out = BTreeMap::new();
    let end = root.prelude_end;
    each_binder(root, |span, name| {
        if span.start < end {
            return;
        }
        if let Some([only]) = prelude_scope.opened.get(name).map(Vec::as_slice) {
            out.insert(
                name.to_string(),
                PreludeCapture {
                    opened: only.as_str().to_string(),
                    span,
                },
            );
        }
    });
    out
}

/// The prelude definitions a user definition displaced, keyed by their bare
/// name. Empty when the user's file shadows nothing, which is every program
/// that does not reuse a prelude name.
fn moved_prelude(prelude_own: &Own) -> Own {
    prelude_own
        .iter()
        .filter(|(name, canon)| canon.as_str() != name.as_str())
        .map(|(name, canon)| (name.clone(), canon.clone()))
        .collect()
}

/// Build a module's import scope: the unqualified bindings its imports bring
/// into bare scope (each mapped to every canonical symbol offered for it), and
/// the qualifier table mapping a qualifier (alias, else last path component) to
/// the modules it names. A selective import also registers its qualifier, so
/// `import M (a)` admits both bare `a` and `M.a`.
///
/// Two modules opening the same short name is recorded, not rejected: the
/// ambiguity belongs to a bare reference that has to choose between them, and
/// [`Rw::pick`] reports it there.
// An import whose module path names no loaded module, offering the loaded paths
// the spelling is closest to.
fn unresolved_import(path: &str, by_path: &BTreeMap<String, usize>) -> Error {
    let hint = suggest::suggestion(path, by_path.keys().map(String::as_str))
        .map_or_else(String::new, |s| format!("; {s}"));
    Error::ResolveModule(format!("cannot resolve import of module `{path}`{hint}"))
}

fn build_scope(
    imports: &[ImportDecl],
    by_path: &BTreeMap<String, usize>,
    mods: &[ModInfo],
) -> Result<Scope, Error> {
    let mut scope = Scope::default();
    for imp in imports {
        let path = imp.path.join(".");
        let idx = *by_path
            .get(path.as_str())
            .ok_or_else(|| unresolved_import(&path, by_path))?;
        // A glob import (`import M (..)`) opens every exported name into
        // unqualified scope; a selective import opens just the listed names.
        let opened: Vec<(String, CanonicalName)> = if imp.glob {
            mods[idx]
                .exports
                .iter()
                .map(|(n, c)| (n.clone(), c.clone()))
                .collect()
        } else if let Some(names) = &imp.names {
            let mut v = Vec::with_capacity(names.len());
            for n in names {
                let Some(canon) = mods[idx].exports.get(n) else {
                    let hint = suggest::suggestion(n, mods[idx].exports.keys().map(String::as_str))
                        .map_or_else(String::new, |s| format!("; {s}"));
                    return Err(Error::ResolveModule(format!(
                        "module `{path}` does not export `{n}`{hint}"
                    )));
                };
                v.push((n.clone(), canon.clone()));
            }
            v
        } else {
            Vec::new()
        };
        for (n, canon) in opened {
            let candidates = scope.opened.entry(n).or_default();
            if !candidates.contains(&canon) {
                candidates.push(canon);
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
        push_unique(scope.quals.entry(path.clone()).or_default(), idx);
        if short != path {
            push_unique(scope.quals.entry(short).or_default(), idx);
        }
    }
    Ok(scope)
}

fn push_unique(v: &mut Vec<usize>, idx: usize) {
    if !v.contains(&idx) {
        v.push(idx);
    }
}

// Build the per-module export tables (each bare name -> its canonical symbol),
// the path -> index map, and propagate re-exports to a fixpoint. Shared by
// `resolve_modules_in` and `import_bindings`.
fn module_infos(modules: &[Module]) -> Result<(Vec<ModInfo>, BTreeMap<String, usize>), Error> {
    let mut mods: Vec<ModInfo> = modules
        .iter()
        .map(|m| {
            let path = m.path.join(".");
            let exports = exports_of(&m.prog)
                .into_iter()
                .map(|n| {
                    let canon = format!("{path}.{n}");
                    (n, CanonicalName::new(canon))
                })
                .collect();
            ModInfo {
                path: ModuleName::new(path),
                exports,
                operations: operations_of(&m.prog),
            }
        })
        .collect();
    let by_path: BTreeMap<String, usize> = mods
        .iter()
        .enumerate()
        .map(|(i, m)| (m.path.as_str().to_string(), i))
        .collect();
    add_reexports(&mut mods, modules, &by_path)?;
    Ok((mods, by_path))
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
        let ops_snapshot: Vec<BTreeSet<String>> =
            mods.iter().map(|m| m.operations.clone()).collect();
        let mut changed = false;
        for (ti, m) in modules.iter().enumerate() {
            for imp in m.prog.imports.iter().filter(|i| i.reexport) {
                let path = imp.path.join(".");
                let si = *by_path
                    .get(path.as_str())
                    .ok_or_else(|| unresolved_import(&path, by_path))?;
                let src = &snapshot[si];
                let names: Vec<String> = imp
                    .names
                    .as_ref()
                    .map_or_else(|| src.keys().cloned().collect(), Clone::clone);
                for n in names {
                    if let Some(canon) = src.get(&n) {
                        // An operation stays an operation across a re-export, so
                        // a clause in the re-exporting module's importer still
                        // reaches it by its bare name.
                        if ops_snapshot[si].contains(&n) {
                            changed |= mods[ti].operations.insert(n.clone());
                        }
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
        root.stable.extend(p.stable);
        root.canonicals.extend(p.canonicals);
        root.patterns.extend(p.patterns);
        root.fns.extend(p.fns);
        root.opaques.extend(p.opaques);
        // Carry each module's deprecation suggestions so a use of an imported
        // deprecated definition warns. Keyed by surface name; a use-site warning
        // fires only for the user's own source (the lint span filter).
        root.deprecated.extend(p.deprecated);
    }
    root.imports.clear();
    root
}

/// One resolved reference: where a name was written, and what it means.
///
/// Collected by the renamer itself rather than by a second walk over the AST,
/// because the renamer is where the decision is *made*. It already carries the
/// scope stack that separates a local binding from a top-level name, and it
/// already knows which module's coordinates a span is in. A parallel walker would
/// have to reimplement that scoping and could then disagree with the resolver
/// about what a name means; this cannot disagree, because it is the same walk.
///
/// This is the goto-definition and find-references relation: read forward it
/// answers "what is this name", read backward "where is this used".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Occurrence {
    /// The dotted module whose source `span` indexes into (empty for the root).
    pub module: String,
    /// The canonical name of the declaration this reference sits inside.
    pub owner: String,
    /// That declaration's own byte range, in the same coordinates as `span`.
    ///
    /// Carried so a consumer can place a reference *within* its declaration
    /// (`span.start - owner_span.start`) without knowing which coordinates these
    /// are. That matters because the root module's are the compiled source's,
    /// which begins with the prelude, while a tool holding one module's file has
    /// nothing to subtract; the difference between the two spans is the same
    /// either way.
    pub owner_span: Span,
    /// The reference's byte range in that module's own source.
    pub span: Span,
    /// The canonical name it resolves to. A builtin, an effect operation, or a
    /// prelude name that no later phase renames stays bare, so a consumer matches
    /// this against the definitions it knows and treats an unmatched target as a
    /// reference leaving its own view.
    pub target: String,
}

/// A scope-aware rewriter for one module. References to the module's own
/// top-level names (and a selective import's unqualified names) become their
/// canonical form; a qualified reference resolves to the imported module's
/// canonical symbol; local bindings (params, let/var, match vars, ...) are never
/// rewritten. A bare name in no scope is left unchanged, so builtins, effect-op
/// names, and prelude names flow through untouched.
struct Rw<'a> {
    module: &'a str,
    s: &'a ScopeSet<'a>,
    mods: &'a [ModInfo],
    // Whether the declaration being rewritten sits in the prepended prelude's
    // region. Set from the declaration's own span before each top-level item, so
    // the prelude's bodies resolve in the prelude's scope and the user's in the
    // user's. Always false for a module with no prelude prefix.
    in_prelude: bool,
    locals: Vec<String>,
    /// Every reference resolved so far, in walk order. See [`Occurrence`].
    occurrences: Vec<Occurrence>,
    /// The declaration being rewritten (canonical name and span), recorded as the
    /// owner of each reference found inside it. Every site that walks an
    /// expression sets this first, so a reference always names the declaration a
    /// reader would navigate to.
    owner: (String, Span),
    // Each locally declared `stable` family mapped to the predecessor rungs whose
    // route to the current rung the migration table promises. A family-qualified
    // `T.Vk.upgrade`/`.downgrade` resolves only for a promised rung; an omitted
    // route is not offered. Built once per module from its `stable` blocks.
    family_routes: BTreeMap<String, BTreeSet<String>>,
    err: Option<TypeError>,
}

impl<'a> Rw<'a> {
    const fn new(module: &'a str, s: &'a ScopeSet<'a>, mods: &'a [ModInfo]) -> Self {
        Self {
            module,
            s,
            mods,
            in_prelude: false,
            locals: Vec::new(),
            occurrences: Vec::new(),
            owner: (String::new(), Span::empty(0)),
            family_routes: BTreeMap::new(),
            err: None,
        }
    }

    // Enter the region the declaration at `span` belongs to.
    const fn at(&mut self, span: Span) {
        self.in_prelude = span.start < self.s.prelude_end;
    }

    // Rewrite `p` in place, returning every reference resolved along the way.
    fn program(mut self, p: &mut Program) -> Result<Vec<Occurrence>, Error> {
        // Record the promised family routes before rewriting any reference, so a
        // `T.Vk.upgrade` use resolves against the declared migration table.
        self.family_routes = p
            .stable
            .iter()
            .map(|sd| (sd.name.clone(), routes_to_current(sd)))
            .collect();
        for d in &mut p.types {
            self.at(d.span);
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
            self.at(e.span);
            e.name = self.canon(&e.name);
            for op in &mut e.ops {
                op.name = self.canon(&op.name);
                for t in &mut op.params {
                    self.ty(t);
                }
                self.ty(&mut op.ret);
            }
        }
        for er in &mut p.errors {
            self.at(er.span);
            er.name = self.canon(&er.name);
            for t in &mut er.params {
                self.ty(t);
            }
        }
        for a in &mut p.aliases {
            self.at(a.span);
            a.name = self.canon(&a.name);
            for l in &mut a.labels {
                self.efflabel(l);
            }
        }
        for s in &mut p.synonyms {
            self.at(s.span);
            s.name = self.canon(&s.name);
            self.ty(&mut s.ty);
        }
        for c in &mut p.classes {
            self.at(c.span);
            c.name = self.canon(&c.name);
            // A superclass names another class, so it resolves like any other
            // reference. Leaving it bare breaks a class whose superclass moved
            // to its module-private symbol because the user shadowed the name.
            for s in &mut c.supers {
                *s = self.value(s, c.span);
            }
            for (_, t) in &mut c.methods {
                self.ty(t);
            }
        }
        for inst in &mut p.instances {
            self.at(inst.span);
            inst.module = self.module.to_string();
            // An instance is global, so its own bare name is its canonical one;
            // it owns the references in every method body it declares.
            self.owner = (inst.name.clone(), inst.span);
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
            self.at(c.span);
            c.class = self.value(&c.class, c.span);
            self.ty(&mut c.head);
        }
        for pat in &mut p.patterns {
            self.at(pat.span);
            pat.name = self.canon(&pat.name);
            // The extractor owns the references in its view and make clauses.
            self.owner = (pat.name.clone(), pat.span);
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
            self.at(f.span);
            self.decl(f, true);
        }
        // Resolve names inside `stable` blocks (field types, additive defaults,
        // and converter bodies) before desugar expands them into ordinary
        // types/fns. A converter's `{ ..vN, .. }` body binds its source rung as a
        // local, so push that before resolving the body.
        for sd in &mut p.stable {
            self.at(sd.span);
            // The family owns the references in its field defaults and converter
            // bodies. They desugar into their own declarations later; before that
            // the block is the declaration a reader would navigate to.
            self.owner = (sd.name.clone(), sd.span);
            for rung in &mut sd.rungs {
                for field in &mut rung.fields {
                    self.ty(&mut field.ty);
                    if let Some(def) = &mut field.default {
                        self.expr(def);
                    }
                }
            }
            for cv in &mut sd.converters {
                let base = self.locals.len();
                self.locals.push(names::stable_param(&cv.from));
                self.expr(&mut cv.base);
                for (_, e) in &mut cv.overrides {
                    self.expr(e);
                }
                self.locals.truncate(base);
            }
            // A `version(...)` override is an ordinary function (a named function
            // or an inline lambda); resolve each supplied direction like any body.
            for mig in &mut sd.migrations {
                if let MigrationRoute::Version(v) = &mut mig.route {
                    for dir in [&mut v.upgrade, &mut v.downgrade] {
                        if let MigrationDir::Expr(e) = dir {
                            self.expr(e);
                        }
                    }
                }
            }
        }
        match self.err.take() {
            Some(e) => Err(Error::Type(e)),
            None => Ok(self.occurrences),
        }
    }

    fn decl(&mut self, d: &mut Decl, canon_name: bool) {
        if canon_name {
            d.name = self.canon(&d.name);
        }
        // A top-level declaration owns the references in its body. An instance
        // method (`canon_name` false) does not: its own name is the bare method
        // name, so it keeps the owner the instance walk installed, which is the
        // declaration a reader would navigate to.
        let outer = if canon_name {
            Some(mem::replace(&mut self.owner, (d.name.clone(), d.span)))
        } else {
            None
        };
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
        if let Some(outer) = outer {
            self.owner = outer;
        }
    }

    fn constraint(&mut self, c: &mut Constraint) {
        c.class = self.value(&c.class, c.span);
        self.ty(&mut c.ty);
    }

    fn efflabel(&mut self, l: &mut EffLabel) {
        // The label carries the span of its own name, so this is one of the sites
        // whose position is exact enough to record as an occurrence.
        l.name = self.value_ref(&l.name, l.span);
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
            Ty::RowLit(Row::Cons(labels, _)) => {
                for l in labels {
                    self.efflabel(l);
                }
            }
            // Higher-kinded application `f(a, ..)`: the head is a bound type
            // variable (never a top-level name), but the arguments carry
            // references that still need canonicalizing.
            Ty::App(_, args) => {
                for a in args {
                    self.ty(a);
                }
            }
            _ => {}
        }
    }

    fn expr(&mut self, e: &mut S<Expr>) {
        let span = e.span;
        match &mut e.node {
            // The one site whose span is the identifier and nothing else.
            Expr::Var(n) => *n = self.value_ref(n, span),
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
            Expr::List(xs) | Expr::Tuple(xs) | Expr::UnboxedTuple(xs) => {
                for x in xs {
                    self.expr(x);
                }
            }
            Expr::FieldAccess(x, _) | Expr::UnboxedField(x, _) | Expr::Neg(x) => self.expr(x),
            Expr::UnboxedRecord(fields) => {
                for (_, v) in fields {
                    self.expr(v);
                }
            }
            Expr::RecordCreate(name, fields) => {
                *name = self.value(name, span);
                for (_, v) in fields {
                    self.expr(v);
                }
            }
            Expr::RecordUpdate(x, name, fields) => {
                self.expr(x);
                *name = self.value(name, span);
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
            Expr::Handle(body, arms, _) => {
                self.expr(body);
                for arm in arms {
                    self.handler_arm(arm, span);
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
            | Expr::Str(_)
            | Expr::Hole(_) => {}
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
                    self.handler_arm(arm, span);
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
            // Nothing to resolve. A quotation in particular is spliced into a
            // string literal against the unit's own unresolved text, before this
            // pass runs, so its target name is never canonicalized: what it
            // quotes is what its author wrote.
            Sugar::Break | Sugar::Continue | Sugar::Reflect(..) => {}
            Sugar::Return(e) | Sugar::Probe(_, e) => self.expr(e),
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

    /// An arm names the operation it handles, so that name resolves like any
    /// other reference: through the module's own definitions first, then its
    /// imports. Leaving it bare would let a handler for a local operation bind
    /// against an identically named one from an unimported module.
    fn handler_arm(&mut self, arm: &mut HandlerArm, span: Span) {
        let base = self.locals.len();
        match arm {
            HandlerArm::Return(x, body) | HandlerArm::Sugar(SugarArm::Val(x, body)) => {
                self.locals.push(x.clone());
                self.expr(body);
            }
            HandlerArm::Op(name, params, k, body) => {
                *name = self.handler_op(name, span);
                self.locals.extend(params.iter().cloned());
                self.locals.push(k.clone());
                self.expr(body);
            }
            HandlerArm::Sugar(
                SugarArm::Once(name, params, body) | SugarArm::Never(name, params, body),
            ) => {
                *name = self.handler_op(name, span);
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
            // Constructor names inside every alternative need qualifying. The
            // alternatives bind the same names, so the repeated `locals` pushes
            // are duplicates of one set, which the scope walk tolerates.
            Pattern::Or(alts) => {
                for alt in alts {
                    self.pat(alt);
                }
            }
            Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Float(_)
            | Pattern::Char(_)
            | Pattern::Bool(_) => {}
        }
    }

    /// Canonicalize a top-level definition name to its module-qualified form,
    /// against the definition tier of the region the declaration sits in.
    fn canon(&self, name: &str) -> String {
        let own = if self.in_prelude {
            self.s.prelude_own
        } else {
            self.s.own
        };
        own.get(name)
            .map_or_else(|| name.to_string(), |c| c.as_str().to_string())
    }

    /// The import tiers a reference in the current region searches, in
    /// precedence order. A prelude declaration sees only the prelude's imports;
    /// the user's region sees its own first, then the prelude's, so a name the
    /// file explicitly imported is never lost to one the prelude happened to
    /// open under the same short name.
    const fn scopes(&self) -> [Option<&'a Scope>; 2] {
        if self.in_prelude {
            [Some(self.s.prelude_scope), None]
        } else {
            [Some(self.s.scope), Some(self.s.prelude_scope)]
        }
    }

    /// The canonical symbol `scope` offers for `name`, reporting the ambiguity
    /// at the use site when it offers more than one.
    ///
    /// Ambiguity is a property of the reference, not of the imports: two modules
    /// in scope may export the same short name freely, and only a bare reference
    /// that would have to choose between them is an error. The first candidate
    /// is returned anyway so one reference yields one diagnostic rather than a
    /// cascade from downstream phases.
    fn pick(&mut self, scope: &Scope, name: &str, span: Span) -> Option<String> {
        match scope.opened.get(name)?.as_slice() {
            [] => None,
            [only] => Some(only.as_str().to_string()),
            many => {
                let owners: Vec<&str> = many.iter().map(|c| names::module_of(c.as_str())).collect();
                let first = many[0].as_str().to_string();
                self.record(
                    span,
                    format!(
                        "`{name}` is ambiguous: exported by {}; qualify the reference",
                        owners.join(" and ")
                    ),
                );
                Some(first)
            }
        }
    }

    /// Resolve a bare name through the tiers visible to the region being
    /// rewritten: the region's own definitions, then the prelude's, then the
    /// region's imports, then the prelude's. The first tier that binds the name
    /// wins outright; a lower tier never contributes a candidate to it.
    fn lookup(&mut self, name: &str, span: Span) -> Option<String> {
        if !self.in_prelude {
            if let Some(c) = self.s.own.get(name) {
                return Some(c.as_str().to_string());
            }
        }
        if let Some(c) = self.s.prelude_own.get(name) {
            return Some(c.as_str().to_string());
        }
        for scope in self.scopes() {
            let Some(scope) = scope else { continue };
            if let Some(hit) = self.pick(scope, name, span) {
                return Some(hit);
            }
        }
        // Last: a prelude name the user displaced. A library module reaches its
        // classes and types this way, having no import that could name them, and
        // imports still win so an explicit one is never lost to the prelude.
        self.s
            .moved_prelude
            .get(name)
            .map(|c| c.as_str().to_string())
    }

    /// Map a family-qualified route path (`T.Vk.upgrade` / `T.Vk.downgrade`) to
    /// the compiler-owned composed route function, or `None` when the path is not
    /// a promised family member. Requires `T` to be a locally declared `stable`
    /// family, `Vk` a rung whose route to the current rung the migration table
    /// promises, and the final segment the `upgrade`/`downgrade` member.
    fn stable_family_route(&self, name: &str) -> Option<String> {
        let (family, ver, member) = names::split_family_member(name)?;
        if !self.family_routes.get(family)?.contains(ver) {
            return None;
        }
        match member {
            kw::UPGRADE => Some(names::stable_route_upgrade(family, ver)),
            kw::DOWNGRADE => Some(names::stable_route_downgrade(family, ver)),
            _ => None,
        }
    }

    /// Resolve a referenced name: locals untouched; `Q.n` resolved through the
    /// qualifier table; the module's own names and any unqualified imports
    /// rewritten to canonical form; everything else (builtins, effect ops,
    /// prelude) left bare for later phases.
    fn value(&mut self, name: &str, span: Span) -> String {
        // A local shadows everything and refers to a binder, not a definition.
        if self.locals.iter().any(|l| l == name) {
            return name.to_string();
        }
        self.global(name, span)
    }

    /// The operation a handler clause names.
    ///
    /// A clause names its operation bare and the grammar admits nothing else, so
    /// the qualified route every other imported name has is closed here: under a
    /// plain `import M`, which opens no unqualified bindings, `M`'s operations
    /// would be spellable at a call site and unspellable at the clause that
    /// handles them. So when ordinary resolution finds nothing, the imported
    /// modules are searched for an operation of that name, which is the only
    /// reading such a clause can have. Two imports offering it is ambiguous and
    /// reported, never silently resolved to one of them.
    fn handler_op(&mut self, name: &str, span: Span) -> String {
        if self.locals.iter().any(|l| l == name) {
            return name.to_string();
        }
        if let Some(canon) = self.lookup(name, span) {
            return canon;
        }
        self.imported_operation(name, span)
            .unwrap_or_else(|| name.to_string())
    }

    /// An operation of that name exported by a module this region imports, taken
    /// tier by tier so the region's own imports answer before the prelude's.
    fn imported_operation(&mut self, name: &str, span: Span) -> Option<String> {
        let mods = self.mods;
        for scope in self.scopes() {
            let Some(scope) = scope else { continue };
            // A module is registered under both its full path and its short
            // qualifier, so the indices are collected through a set: one module
            // reached two ways is one candidate, not an ambiguity.
            let seen: BTreeSet<usize> = scope.quals.values().flatten().copied().collect();
            let hits: Vec<&ModInfo> = seen
                .into_iter()
                .map(|i| &mods[i])
                .filter(|m| m.operations.contains(name))
                .collect();
            match hits.as_slice() {
                [] => {}
                [m] => return Some(m.exports[name].as_str().to_string()),
                many => {
                    let owners: Vec<&str> = many.iter().map(|m| m.path.as_str()).collect();
                    let first = many[0].exports[name].as_str().to_string();
                    self.record(
                        span,
                        format!(
                            "operation `{name}` is ambiguous: declared by {}; import only the module whose operation this clause handles",
                            owners.join(" and ")
                        ),
                    );
                    return Some(first);
                }
            }
        }
        None
    }

    /// [`Self::value`] where `span` is the written identifier itself, recording
    /// the reference as an [`Occurrence`].
    ///
    /// Separate from `value`. Some resolution sites pass an enclosing node's span
    /// because the resolved name has no span of its own. Those spans suit a
    /// diagnostic, which underlines the construct, but are wrong
    /// for a link, which must cover the name and nothing else. Recording them would
    /// silently turn a whole declaration into one clickable region, so a site opts
    /// in here only when its span is exact: an expression variable, and an
    /// effect-row label, whose span the parser sets to the label's name and not to
    /// the argument list after it.
    fn value_ref(&mut self, name: &str, span: Span) -> String {
        if self.locals.iter().any(|l| l == name) {
            return name.to_string();
        }
        let resolved = self.global(name, span);
        self.see(span, &resolved);
        resolved
    }

    // The canonical name a non-local reference resolves to.
    fn global(&mut self, name: &str, span: Span) -> String {
        // A family-qualified `T.Vk.upgrade`/`.downgrade` reaches the generated
        // composed route, but only for a rung the migration table promises. The
        // family and rung come from the declared `stable` block, never sniffed
        // from the name, so this cannot capture an ordinary module-qualified call.
        if let Some(route) = self.stable_family_route(name) {
            return route;
        }
        // Split on the LAST dot, so a multi-segment qualifier (`Geo.Util.one`)
        // resolves as (`Geo.Util`, `one`) and a single one (`Map.insert`) as
        // (`Map`, `insert`).
        if let Some((q, n)) = name.rsplit_once('.') {
            return self.qualified(q, n, name, span);
        }
        self.lookup(name, span).unwrap_or_else(|| name.to_string())
    }

    // Record a resolved reference.
    //
    // Positionless references are dropped: `ty` and `efflabel` resolve through
    // the same entry point with a zero-width placeholder, because `Ty` carries no
    // spans of its own, and a reference a consumer cannot locate is not one it can
    // render. That is what confines this to term references for now; giving `Ty`
    // spans would extend it to types and effect rows with no change here.
    fn see(&mut self, span: Span, target: &str) {
        if span.is_empty() {
            return;
        }
        let (owner, owner_span) = &self.owner;
        self.occurrences.push(Occurrence {
            module: self.module.to_string(),
            owner: owner.clone(),
            owner_span: *owner_span,
            span,
            target: target.to_string(),
        });
    }

    /// Resolve `Q.n` through the qualifier tables visible to the current region,
    /// nearest tier first. A tier that names `Q` and exports `n` answers; a tier
    /// that names `Q` without exporting `n` falls through to the next, so a
    /// qualifier the prelude opened still serves a name the user's own import of
    /// the same qualifier does not carry.
    fn qualified(&mut self, q: &str, n: &str, full: &str, span: Span) -> String {
        let mods = self.mods;
        let mut qualifier_known = false;
        for scope in self.scopes() {
            let Some(idxs) = scope.and_then(|s| s.quals.get(q)) else {
                continue;
            };
            qualifier_known = true;
            let hits: Vec<&ModInfo> = idxs
                .iter()
                .filter(|&&i| mods[i].exports.contains_key(n))
                .map(|&i| &mods[i])
                .collect();
            match hits.as_slice() {
                [] => {}
                [m] => return m.exports[n].as_str().to_string(),
                many => {
                    let paths: Vec<&str> = many.iter().map(|m| m.path.as_str()).collect();
                    self.record(
                        span,
                        format!("`{full}` is ambiguous: exported by {}", paths.join(", ")),
                    );
                    return full.to_string();
                }
            }
        }
        let msg = if qualifier_known {
            format!("module `{q}` does not export `{n}`")
        } else {
            format!("`{full}`: no imported module qualified `{q}`")
        };
        self.record(span, msg);
        full.to_string()
    }

    fn record(&mut self, span: Span, msg: String) {
        if self.err.is_none() {
            self.err = Some(TypeError::ScopeFailure { span, msg });
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
