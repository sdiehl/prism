use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::io;
use std::path::PathBuf;
use std::process::Command;
use std::rc::Rc;
use std::time::Instant;

use anstyle::{AnsiColor, Color, Style};
use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::{CmdKind, Highlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::history::DefaultHistory;
use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{Context, Editor, Helper};

use crate::core::{builtin_arities, elaborate, elaborate_expr_defs, CoreFn};
use crate::driver::PRELUDE;
use crate::error::Error;
use crate::eval::{globals, Machine};
use crate::fmt::decl::fmt_class;
use crate::lex::Token as K;
use crate::lex::{lex_raw, Token};
use crate::parse::{incomplete, parse, parse_expr, ParseResult};
use crate::resolve::{binders, default_roots, import_bindings, resolve_expr, resolve_modules_in};
use crate::sym::Sym;
use crate::syntax::ast::{ClassDecl, Core, Expr, ImportDecl, Program, S};
use crate::syntax::desugar::{desugar, desugar_expr};
use crate::types::{
    check, check_allow_holes, infer_expr, infer_expr_dicts, infer_expr_dicts_allow_holes,
    show_effects, show_type_with_effects, Checked, CtorInfo, Type,
};

// Canonical commands. Any unambiguous prefix resolves to one (`:lo` -> :load,
// `:r` -> :reload), ghci style, so no separate aliases are needed.
const COMMANDS: &[&str] = &[
    ":browse", ":core", ":edit", ":help", ":info", ":kind", ":load", ":quit", ":reload", ":set",
    ":type",
];

// Syntax-highlight styles, one per token category, plus the dim style used for
// inline history hints. anstyle renders the ANSI escapes.
const KEYWORD: Style = fg(AnsiColor::Magenta);
const TYPE: Style = fg(AnsiColor::Cyan);
const NUM: Style = fg(AnsiColor::Yellow);
const STR: Style = fg(AnsiColor::Green);
const HINT: Style = fg(AnsiColor::BrightBlack);

const fn fg(c: AnsiColor) -> Style {
    Style::new().fg_color(Some(Color::Ansi(c)))
}

fn paint(s: Style, t: &str) -> String {
    format!("{}{t}{}", s.render(), s.render_reset())
}

// Target and allocator are resolved at compile time: PRISM_TARGET is the cargo
// target triple (set in build.rs); the allocator follows the mimalloc feature.
const fn allocator() -> &'static str {
    if cfg!(feature = "mimalloc") {
        "mimalloc"
    } else {
        "libc"
    }
}

fn banner(defs: usize) {
    let edge = TYPE.bold();
    let spectrum = [
        AnsiColor::Red,
        AnsiColor::Yellow,
        AnsiColor::Green,
        AnsiColor::Cyan,
        AnsiColor::Blue,
        AnsiColor::Magenta,
    ]
    .iter()
    .map(|&c| paint(fg(c), "="))
    .collect::<String>();
    let v = env!("CARGO_PKG_VERSION");
    let target = env!("PRISM_TARGET");
    println!(
        "     {}     {}",
        paint(edge, "/\\"),
        paint(Style::new().bold(), "prism interactive compiler")
    );
    println!(
        "    {}    {}",
        paint(edge, "/  \\"),
        paint(HINT, &format!("version {v}, {target}, {}", allocator()))
    );
    println!(
        "   {}   {}",
        paint(edge, "/    \\"),
        paint(HINT, &format!("prelude loaded ({defs} definitions)"))
    );
    println!(
        "  {}{}{}  {}",
        paint(edge, "/"),
        spectrum,
        paint(edge, "\\"),
        paint(HINT, "type :help for commands, :quit to quit")
    );
}

// Resolve a leading `:word` to its canonical command by unique prefix. Err
// carries the candidates: empty means unknown, many means ambiguous.
fn resolve(tok: &str) -> Result<&'static str, Vec<&'static str>> {
    let hits: Vec<&'static str> = COMMANDS
        .iter()
        .copied()
        .filter(|c| c.starts_with(tok))
        .collect();
    if let [one] = hits[..] {
        Ok(one)
    } else {
        Err(hits)
    }
}

struct Built {
    checked: Checked,
    globals: BTreeMap<Sym, CoreFn>,
    arity: BTreeMap<String, usize>,
    consts: BTreeMap<String, S<Expr<Core>>>,
    // Bare names the prelude's glob imports open into scope, mapped to their
    // canonical symbols, so a typed-in expression resolves `map` the same way a
    // file body does (the program resolver only reaches declared bodies).
    imports: BTreeMap<String, String>,
    // Resolved surface declarations retained for canonical `:info` rendering.
    // `Checked::classes` carries semantic facts, not the source declaration, so
    // it intentionally has no formatter-facing spelling for superclasses.
    classes: BTreeMap<String, ClassDecl>,
    // The same resolved/checker artifacts partitioned by the syntactic positions
    // the line editor completes. Rebuilt with the session, never maintained by
    // hand alongside it.
    completion: CompletionScope,
    // Every directly imported module spelling (full path and short alias) to its
    // canonical path. Used by module-aware completion and `:browse M`.
    modules: BTreeMap<String, String>,
}

#[derive(Clone, Default)]
struct CompletionScope {
    values: BTreeSet<String>,
    types: BTreeSet<String>,
    info: BTreeSet<String>,
    modules: BTreeSet<String>,
    importable_modules: BTreeSet<String>,
}

fn module_bindings(imports: &[ImportDecl]) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for import in imports {
        let path = import.path.join(".");
        out.insert(path.clone(), path.clone());
        let short = import
            .alias
            .clone()
            .or_else(|| import.path.last().cloned())
            .unwrap_or_default();
        if short == path || ambiguous.contains(&short) {
            continue;
        }
        match out.get(&short) {
            Some(previous) if previous != &path => {
                out.remove(&short);
                ambiguous.insert(short);
            }
            Some(_) => {}
            None => {
                out.insert(short, path.clone());
            }
        }
    }
    out
}

fn add_completion_name(
    scope: &mut CompletionScope,
    shown: &str,
    canonical: &str,
    values: &BTreeSet<String>,
    types: &BTreeSet<String>,
    classes: &BTreeSet<String>,
    effects: &BTreeSet<String>,
) {
    let is_value = values.contains(canonical);
    let is_type = types.contains(canonical);
    let is_info = is_value || is_type || classes.contains(canonical) || effects.contains(canonical);
    if is_value {
        scope.values.insert(shown.to_string());
    }
    if is_type {
        scope.types.insert(shown.to_string());
    }
    if is_info {
        scope.info.insert(shown.to_string());
    }
}

fn completion_scope(
    program: &Program<Core>,
    checked: &Checked,
    imports: &BTreeMap<String, String>,
    root_binders: &BTreeSet<String>,
    import_decls: &[ImportDecl],
) -> (CompletionScope, BTreeMap<String, String>) {
    let value_symbols: BTreeSet<String> = checked
        .env
        .keys()
        .map(ToString::to_string)
        .chain(checked.ctors.keys().cloned())
        .chain(checked.eff_ops.keys().cloned())
        .chain(checked.methods.keys().map(ToString::to_string))
        .collect();
    let mut type_symbols: BTreeSet<String> = checked.data.keys().cloned().collect();
    type_symbols.extend(Type::SCALARS.iter().map(Type::show));
    let class_symbols: BTreeSet<String> = checked.classes.keys().map(ToString::to_string).collect();
    let effect_symbols: BTreeSet<String> = program.effects.iter().map(|e| e.name.clone()).collect();
    let alias_symbols: BTreeSet<String> = program
        .aliases
        .iter()
        .map(|a| a.name.clone())
        .chain(program.synonyms.iter().map(|a| a.name.clone()))
        .collect();
    type_symbols.extend(alias_symbols.iter().cloned());

    let mut scope = CompletionScope::default();

    // Root declarations and compiler/prelude bindings already have their source
    // spelling. Imported private symbols carry `@` and are deliberately excluded:
    // they are present in the merged checker environment but never resolvable at
    // the REPL prompt.
    for canonical in value_symbols
        .iter()
        .chain(type_symbols.iter())
        .chain(class_symbols.iter())
        .chain(effect_symbols.iter())
    {
        if !canonical.contains(['.', '@']) || root_binders.contains(canonical) {
            add_completion_name(
                &mut scope,
                canonical,
                canonical,
                &value_symbols,
                &type_symbols,
                &class_symbols,
                &effect_symbols,
            );
        }
    }
    // Unqualified imports are the resolver's own exact live-scope map.
    for (shown, canonical) in imports {
        add_completion_name(
            &mut scope,
            shown,
            canonical,
            &value_symbols,
            &type_symbols,
            &class_symbols,
            &effect_symbols,
        );
    }

    let modules = module_bindings(import_decls);
    for (shown, path) in &modules {
        scope.modules.insert(shown.clone());
        // A directly imported module exposes its public canonical symbols under
        // the full path and its short alias. Private names use `@`, not this dot
        // prefix, so this scan cannot leak them into completion.
        let prefix = format!("{path}.");
        for canonical in value_symbols
            .iter()
            .chain(type_symbols.iter())
            .chain(class_symbols.iter())
            .chain(effect_symbols.iter())
            .filter(|name| name.starts_with(&prefix))
        {
            add_completion_name(
                &mut scope,
                canonical,
                canonical,
                &value_symbols,
                &type_symbols,
                &class_symbols,
                &effect_symbols,
            );
            if shown != path {
                let suffix = &canonical[prefix.len()..];
                add_completion_name(
                    &mut scope,
                    &format!("{shown}.{suffix}"),
                    canonical,
                    &value_symbols,
                    &type_symbols,
                    &class_symbols,
                    &effect_symbols,
                );
            }
        }
    }
    // The embedded module table is the resolver's lowest-priority root and is
    // always importable in the standalone REPL. Direct imports are included too,
    // covering a project module already discovered through a loaded session file.
    scope.importable_modules.extend(
        crate::stdlib::STDLIB
            .iter()
            .map(|(name, _)| (*name).to_string()),
    );
    scope.importable_modules.extend(modules.values().cloned());
    scope.info.extend(scope.values.iter().cloned());
    scope.info.extend(scope.types.iter().cloned());
    (scope, modules)
}

#[derive(Clone)]
enum Seg {
    File(String),
    Text(String),
}

// `:set` toggles. Types are shown by default (this is a typed REPL). Timing
// is opt-in.
#[derive(Clone, Copy)]
struct Flags {
    types: bool,
    timing: bool,
    holes: bool,
}

impl Default for Flags {
    fn default() -> Self {
        Self {
            types: true,
            timing: false,
            holes: false,
        }
    }
}

// Declarations accumulate as segments (files are re-read by :reload). `let`
// bindings live outside the program text and are spliced as a let chain
// around every later expression, so they re-evaluate per line.
struct Session {
    segs: Vec<Seg>,
    lets: Vec<(String, String)>,
    // The file `:reload` re-reads and `:edit` opens by default, set by the
    // last `:load` or `:edit`.
    active: Option<String>,
    flags: Flags,
    // Names present in the bare prelude, so `:browse` can show only what the
    // session added.
    base: BTreeSet<String>,
    // The last evaluated expression, self-contained (its own lets inlined), so
    // `it` refers back to it on the next line.
    it_src: Option<String>,
}

impl Session {
    fn probe(segs: Vec<Seg>, lets: Vec<(String, String)>) -> Self {
        Self {
            segs,
            lets,
            active: None,
            flags: Flags::default(),
            base: BTreeSet::new(),
            it_src: None,
        }
    }

    fn compose(&self) -> Result<String, Error> {
        let mut s = PRELUDE.to_string();
        for seg in &self.segs {
            s.push('\n');
            match seg {
                Seg::Text(t) => s.push_str(t),
                Seg::File(p) => s.push_str(&std::fs::read_to_string(p)?),
            }
        }
        Ok(s)
    }

    fn build(&self) -> Result<(String, Built), Error> {
        let src = self.compose()?;
        let ParseResult { program, .. } = parse(&src)?;
        let root_binders = binders(&program);
        let import_decls = program.imports.clone();
        // The prelude opens the `Data.*` stdlib modules with glob imports, so the
        // session must resolve modules against the stdlib roots before desugaring,
        // exactly as the batch driver's `frontend` does. Without this, names that
        // live in stdlib modules (e.g. `nth` behind `at_list`) are unbound.
        let roots = default_roots(std::path::Path::new("."));
        // The same import scope, captured for resolving interactively typed
        // expressions, which never pass through the program resolver below.
        let imports = import_bindings(&program, &roots)?;
        let program = resolve_modules_in(program, &roots)?;
        let program = desugar(program)?;
        let checked = if self.flags.holes {
            check_allow_holes(&program)?
        } else {
            check(&program)?
        };
        let (completion, modules) =
            completion_scope(&program, &checked, &imports, &root_binders, &import_decls);
        let classes = program
            .classes
            .iter()
            .map(|class| (class.name.clone(), class.clone()))
            .collect();
        let core = elaborate(&program, &checked)?;
        let mut arity: BTreeMap<String, usize> = checked
            .decls
            .iter()
            .map(|d| (d.name.clone(), d.params.len()))
            .collect();
        builtin_arities(&mut arity);
        let consts = program
            .fns
            .iter()
            .filter(|d| d.konst)
            .map(|d| (d.name.clone(), d.body.clone()))
            .collect();
        Ok((
            src,
            Built {
                globals: globals(&core),
                checked,
                arity,
                consts,
                imports,
                classes,
                completion,
                modules,
            },
        ))
    }

    // Splice the user's `let` bindings around `expr` so they re-evaluate per
    // line. `it` is bound outermost only when `expr` refers to it, so an
    // unrelated line is neither prefixed with stale text nor made to re-run the
    // previous expression's effects.
    fn chain(&self, expr: &str) -> String {
        let mut s = String::new();
        if let Some(it) = self.it_src.as_ref().filter(|_| mentions_it(expr)) {
            let _ = write!(s, "let it = ({it}) in ");
        }
        s.push_str(&self.chain_lets(expr));
        s
    }

    // Re-splice every prior `let` as an enclosing binding rather than keeping
    // evaluated globals: each line is type-checked and run as one fresh
    // expression, so an earlier binding exists for this line only if its source
    // is textually present.
    fn chain_lets(&self, expr: &str) -> String {
        let mut s = String::new();
        for (n, rhs) in &self.lets {
            let _ = write!(s, "let {n} = ({rhs}) in ");
        }
        s.push_str(expr);
        s
    }

    fn eval_chained(&self, built: &Built, expr: &str) -> Result<(String, String, String), Error> {
        let text = self.chain(expr);
        let mut surface = parse_expr(&text)?;
        resolve_expr(&mut surface, &built.imports)?;
        let e = desugar_expr(&surface)?;
        let (ty, eff, dicts) = if self.flags.holes {
            let (ty, eff, dicts, _) = infer_expr_dicts_allow_holes(&built.checked, &e)?;
            (ty, eff, dicts)
        } else {
            infer_expr_dicts(&built.checked, &e)?
        };
        let (comp, synthesized) = elaborate_expr_defs(
            &built.checked,
            &e,
            &built.arity,
            Some(&dicts),
            &built.consts,
        )?;
        // Elaboration synthesizes structural `show` helpers on demand. A
        // whole-program compile folds them into its Core, so `built.globals`
        // (the prelude session) lacks any this expression alone needed; add
        // them here or a call to one faults as an unknown function.
        let mut globals = built.globals.clone();
        for f in synthesized {
            globals.insert(f.name, f);
        }
        // The REPL streams `print` to the terminal and reads from real stdin,
        // but `exit(n)` only ends the evaluation: the shell keeps running.
        let stdout = io::stdout();
        let stdin = io::stdin();
        let mut out = stdout.lock();
        let mut input = stdin.lock();
        let v = {
            let mut m = Machine::new(&globals, &mut out, &mut input);
            m.eval(&comp).map_err(Error::RuntimeEvaluation)?
        };
        drop(out);
        drop(input);
        Ok((v.repr(), ty.show(), show_effects(&eff)))
    }
}

// Render an evaluated result per the session flags: value alone, or with its
// type and effects.
fn show_eval(flags: Flags, (val, ty, eff): &(String, String, String), elapsed: Instant) {
    if flags.types {
        println!("{val} : {ty} ! {eff}");
    } else {
        println!("{val}");
    }
    if flags.timing {
        println!("({} ms)", elapsed.elapsed().as_secs_f64() * 1000.0);
    }
}

type Scopes = Rc<RefCell<CompletionScope>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompletionKind {
    Values,
    Types,
    Info,
    Modules,
    ImportableModules,
    Files,
}

fn completion_kind(line: &str, pos: usize) -> CompletionKind {
    let before = &line[..pos];
    if let Some(rest) = before.strip_prefix(':') {
        if let Some((word, _)) = rest.split_once(char::is_whitespace) {
            return match resolve(&format!(":{word}")) {
                Ok(":load" | ":edit") => CompletionKind::Files,
                Ok(":kind") => CompletionKind::Types,
                Ok(":browse") => CompletionKind::Modules,
                Ok(":info") => CompletionKind::Info,
                _ => CompletionKind::Values,
            };
        }
    }
    if before.trim_start().starts_with("import ") {
        CompletionKind::ImportableModules
    } else {
        CompletionKind::Values
    }
}

fn name_candidates(
    scope: &CompletionScope,
    kind: CompletionKind,
    line: &str,
    pos: usize,
) -> (usize, Vec<Pair>) {
    let names = match kind {
        CompletionKind::Values => &scope.values,
        CompletionKind::Types => &scope.types,
        CompletionKind::Info => &scope.info,
        CompletionKind::Modules => &scope.modules,
        CompletionKind::ImportableModules => &scope.importable_modules,
        CompletionKind::Files => return (pos, Vec::new()),
    };
    // Dots are part of a module-qualified name, so `Data.L` replaces as one
    // token rather than completing only the suffix after the final dot.
    let start = line[..pos]
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '.')
        .map_or(0, |i| i + 1);
    let word = &line[start..pos];
    if word.is_empty() {
        return (pos, Vec::new());
    }
    let cands = names
        .iter()
        .filter(|name| name.starts_with(word))
        .map(|name| Pair {
            display: name.clone(),
            replacement: name.clone(),
        })
        .collect();
    (start, cands)
}

struct PrismHelper {
    files: FilenameCompleter,
    scopes: Scopes,
    hints: HistoryHinter,
}

impl Completer for PrismHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        ctx: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        if line.starts_with(':') && !line[..pos].contains(' ') {
            let cands = COMMANDS
                .iter()
                .filter(|c| c.starts_with(&line[..pos]))
                .map(|c| Pair {
                    display: (*c).to_string(),
                    replacement: format!("{c} "),
                })
                .collect();
            return Ok((0, cands));
        }
        let kind = completion_kind(line, pos);
        if kind == CompletionKind::Files {
            return self.files.complete(line, pos, ctx);
        }
        Ok(name_candidates(&self.scopes.borrow(), kind, line, pos))
    }
}

impl Hinter for PrismHelper {
    type Hint = String;

    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        self.hints.hint(line, pos, ctx)
    }
}

impl Highlighter for PrismHelper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        highlight(line, pos)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Cow::Owned(format!("{}{hint}{}", HINT.render(), HINT.render_reset()))
    }

    fn highlight_char(&self, _line: &str, _pos: usize, kind: CmdKind) -> bool {
        kind != CmdKind::ForcedRefresh
    }
}

impl Validator for PrismHelper {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        Ok(if needs_more(ctx.input()) {
            ValidationResult::Incomplete
        } else {
            ValidationResult::Valid(None)
        })
    }
}

impl Helper for PrismHelper {}

// Whether the editor should keep reading more lines. A `:{ ... :}` block stays
// open until its closing line. Otherwise an expression that ends prematurely
// (open brace, unterminated string) is incomplete. Single-line commands and
// declarations submit immediately.
fn needs_more(src: &str) -> bool {
    let t = src.trim_start();
    if let Some(rest) = t.strip_prefix(":{") {
        return !rest.lines().any(|l| l.trim() == ":}");
    }
    if t.starts_with(':') {
        return false;
    }
    // A ghci-style binding `let x = e` / `x = e` (no `in`) is complete once its
    // RHS is. Otherwise `incomplete` would see a `let` missing its `in` and
    // slurp the next line into the binding.
    if let Some((_, rhs)) = try_let(t) {
        return incomplete(&rhs);
    }
    incomplete(src)
}

// Color category for a token. Everything else (operators, identifiers,
// punctuation) is left uncolored.
enum Cat {
    Keyword,
    Type,
    Num,
    Str,
    Plain,
}

const fn category(t: &Token) -> Cat {
    match t {
        K::Fn
        | K::Import
        | K::As
        | K::Type
        | K::Effect
        | K::KwError
        | K::Throw
        | K::Try
        | K::Catch
        | K::Alias
        | K::Class
        | K::Instance
        | K::Pattern
        | K::Deriving
        | K::Where
        | K::Handle
        | K::With
        | K::Handler
        | K::Mask
        | K::Val
        | K::Return
        | K::Let
        | K::Var
        | K::In
        | K::For
        | K::Do
        | K::If
        | K::Then
        | K::Else
        | K::Elif
        | K::Match
        | K::Of
        | K::Forall => Cat::Keyword,
        K::KwInt
        | K::KwBool
        | K::KwUnit
        | K::KwFloat
        | K::KwString
        | K::KwI64
        | K::KwU64
        | K::UIdent(_)
        | K::QualName(_) => Cat::Type,
        K::Int(_) | K::Float(_) | K::True | K::False => Cat::Num,
        K::StringLit(_) | K::InterpStart(_) | K::InterpMid(_) | K::InterpEnd(_) => Cat::Str,
        _ => Cat::Plain,
    }
}

const fn style(cat: &Cat) -> Style {
    match cat {
        Cat::Keyword => KEYWORD,
        Cat::Type => TYPE,
        Cat::Num => NUM,
        Cat::Str => STR,
        Cat::Plain => Style::new(),
    }
}

const fn bracket(t: &Token) -> Option<(bool, u8)> {
    match t {
        Token::LParen => Some((true, 0)),
        Token::RParen => Some((false, 0)),
        Token::LBrace => Some((true, 1)),
        Token::RBrace => Some((false, 1)),
        Token::LBracket => Some((true, 2)),
        Token::RBracket => Some((false, 2)),
        _ => None,
    }
}

// The pair of bracket offsets the cursor sits on, matched by nesting. Brackets
// inside string literals never reach here, since they live within one token.
fn matching(toks: &[(usize, Token, usize)], pos: usize) -> Option<(usize, usize)> {
    let at = toks
        .iter()
        .position(|(s, t, e)| bracket(t).is_some() && (*e == pos || *s == pos))?;
    let (s, t, _) = &toks[at];
    let (open, grp) = bracket(t)?;
    let mut depth = 0i32;
    if open {
        for (s2, t2, _) in &toks[at..] {
            if let Some((o2, g2)) = bracket(t2) {
                if g2 == grp {
                    depth += if o2 { 1 } else { -1 };
                    if depth == 0 {
                        return Some((*s, *s2));
                    }
                }
            }
        }
    } else {
        for (s2, t2, _) in toks[..=at].iter().rev() {
            if let Some((o2, g2)) = bracket(t2) {
                if g2 == grp {
                    depth += if o2 { 1 } else { -1 };
                    if depth == 0 {
                        return Some((*s2, *s));
                    }
                }
            }
        }
    }
    None
}

// Colorize the line by token category and embolden the bracket pair under the
// cursor. Falls back to the raw line while it does not lex (mid-edit).
fn highlight(line: &str, pos: usize) -> Cow<'_, str> {
    let Ok((toks, _)) = lex_raw(line) else {
        return Cow::Borrowed(line);
    };
    if toks.is_empty() {
        return Cow::Borrowed(line);
    }
    let pair = matching(&toks, pos);
    let mut out = String::with_capacity(line.len() + 16);
    let mut cur = 0;
    for (s, t, e) in &toks {
        if *s > cur {
            out.push_str(&line[cur..*s]);
        }
        let bold = pair.is_some_and(|(a, b)| *s == a || *s == b);
        let sty = style(&category(t));
        let sty = if bold { sty.bold() } else { sty };
        if sty == Style::new() {
            out.push_str(&line[*s..*e]);
        } else {
            let _ = write!(
                out,
                "{}{}{}",
                sty.render(),
                &line[*s..*e],
                sty.render_reset()
            );
        }
        cur = *e;
    }
    if cur < line.len() {
        out.push_str(&line[cur..]);
    }
    Cow::Owned(out)
}

fn refresh_scope(scopes: &Scopes, session: &Session, built: &Built) {
    let mut scope = built.completion.clone();
    for (name, _) in &session.lets {
        scope.values.insert(name.clone());
        scope.info.insert(name.clone());
    }
    *scopes.borrow_mut() = scope;
}

pub fn repl(show_banner: bool) {
    let mut session = Session::probe(Vec::new(), Vec::new());
    let mut built = match session.build() {
        Ok((_, b)) => b,
        Err(e) => {
            report(&e, PRELUDE, "<prelude>");
            return;
        }
    };
    // Everything in the bare prelude, so `:browse` can subtract it later. Read
    // from the exact same sources `browse` iterates (`checked.decls` and
    // `checked.ctors`, not `arity`, which only covers a subset) so the baseline
    // and the later diff never drift apart.
    session.base = built
        .checked
        .decls
        .iter()
        .map(|d| d.name.clone())
        .chain(built.checked.ctors.keys().cloned())
        .collect();
    if show_banner {
        banner(built.arity.len() + built.consts.len());
    } else {
        println!("prism {} | :help for commands", env!("CARGO_PKG_VERSION"));
    }
    let Ok(mut rl) = Editor::<PrismHelper, DefaultHistory>::new() else {
        eprintln!("could not start interactive shell");
        return;
    };
    let scopes: Scopes = Rc::new(RefCell::new(CompletionScope::default()));
    refresh_scope(&scopes, &session, &built);
    rl.set_helper(Some(PrismHelper {
        files: FilenameCompleter::new(),
        scopes: Rc::clone(&scopes),
        hints: HistoryHinter::new(),
    }));
    let hist = env::var_os("HOME").map(|h| PathBuf::from(h).join(".prism_history"));
    if let Some(p) = &hist {
        let _ = rl.load_history(p);
    }
    loop {
        match rl.readline("prism> ") {
            Ok(mut buf) => {
                // Gather continuation lines for `:{` blocks and unfinished
                // input. Interactively the validator has already done this (so
                // the guard is false); piped input falls through to here.
                while needs_more(buf.trim()) {
                    match rl.readline("  ...> ") {
                        Ok(more) => {
                            buf.push('\n');
                            buf.push_str(&more);
                        }
                        Err(_) => break,
                    }
                }
                let line = buf.trim();
                if line.is_empty() {
                    continue;
                }
                let _ = rl.add_history_entry(line);
                if !step(&mut session, &mut built, line) {
                    break;
                }
                refresh_scope(&scopes, &session, &built);
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("{e}");
                break;
            }
        }
    }
    if let Some(p) = &hist {
        let _ = rl.save_history(p);
    }
}

fn step(session: &mut Session, built: &mut Built, line: &str) -> bool {
    // A `:{` block is unwrapped below. Every other `:` token is a command.
    if !line.starts_with(":{") {
        if let Some(rest) = line.strip_prefix(':') {
            let (word, arg) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
            match resolve(&format!(":{word}")) {
                Ok(cmd) => return command(session, built, cmd, arg.trim()),
                Err(hits) if hits.is_empty() => {
                    eprintln!("unknown command `:{word}` (:help for the list)");
                }
                Err(hits) => eprintln!("ambiguous `:{word}`: {}", hits.join(", ")),
            }
            return true;
        }
    }
    // A `:{ ... :}` paste block: its body is one declaration chunk, or one
    // expression if it does not start with a declaration keyword.
    let line = unblock(line);
    if is_decl(&line) {
        let msg = decl_success_message(&line);
        let mut cand = session.segs.clone();
        upsert_decl(&mut cand, line.into_owned());
        commit_as(session, built, cand, "<repl>", &msg);
        return true;
    }
    if (line.starts_with("let ") || bare_bind(&line).is_some()) && parse_expr(&line).is_err() {
        if let Some((name, rhs)) = try_let(&line) {
            let mut cand = session.lets.clone();
            upsert(&mut cand, name.clone(), rhs);
            let mut probe = Session::probe(Vec::new(), cand);
            probe.it_src.clone_from(&session.it_src);
            match probe.eval_chained(built, &name) {
                Ok(parts) => {
                    session.lets = probe.lets;
                    show_eval(session.flags, &parts, Instant::now());
                }
                Err(e) => report(&e, &probe.chain(&name), "<repl>"),
            }
        } else {
            eprintln!("let needs a value: let x = e");
        }
        return true;
    }
    let started = Instant::now();
    match session.eval_chained(built, &line) {
        Ok(parts) => {
            show_eval(session.flags, &parts, started);
            // Remember the result as a self-contained `it`: `chain` folds in the
            // prior `it` only when this line referred to it, so unrelated lines
            // do not accrete text.
            session.it_src = Some(session.chain(&line));
        }
        Err(e) => report(&e, &session.chain(&line), "<repl>"),
    }
    true
}

fn is_decl(line: &str) -> bool {
    [
        "import ",
        "fn ",
        "type ",
        "effect ",
        "error ",
        "alias ",
        "class ",
        "instance ",
        "pattern ",
    ]
    .iter()
    .any(|k| line.starts_with(k))
}

// Strip a `:{ ... :}` wrapper, leaving the inner block. Otherwise the line is
// returned unchanged.
fn unblock(line: &str) -> Cow<'_, str> {
    line.strip_prefix(":{").map_or(Cow::Borrowed(line), |rest| {
        let inner: Vec<&str> = rest.lines().take_while(|l| l.trim() != ":}").collect();
        Cow::Owned(inner.join("\n").trim().to_string())
    })
}

// Whether `it` appears as an identifier, so `it`-chaining nests only when used.
fn mentions_it(line: &str) -> bool {
    lex_raw(line).is_ok_and(|(toks, _)| {
        toks.iter()
            .any(|(_, t, _)| matches!(t, Token::Ident(s) if s == "it"))
    })
}

// Replace a binding of the same name in place (ghci-style shadowing), else
// append, keeping the list bounded.
fn upsert(lets: &mut Vec<(String, String)>, name: String, rhs: String) {
    match lets.iter().position(|(n, _)| *n == name) {
        Some(i) => lets[i] = (name, rhs),
        None => lets.push((name, rhs)),
    }
}

// Replace a prior declaration of the same kind and name in place, so
// redefining `fn foo` supersedes the old one instead of duplicating it.
fn upsert_decl(segs: &mut Vec<Seg>, text: String) {
    let key = decl_key(&text);
    if let Some(k) = &key {
        if let Some(i) = segs
            .iter()
            .position(|s| matches!(s, Seg::Text(t) if decl_key(t).as_ref() == Some(k)))
        {
            segs[i] = Seg::Text(text);
            return;
        }
    }
    segs.push(Seg::Text(text));
}

// An `import`'s success message names the module, so the REPL confirms what
// was written rather than a bare "ok"; every other declaration keeps "ok".
fn decl_success_message(text: &str) -> String {
    match decl_key(text) {
        Some((kw, name)) if kw == "import" => format!("Imported {name} successfully"),
        _ => "ok".to_string(),
    }
}

// The (keyword, name) identifying a declaration. Instances have no simple name,
// so they always append.
fn decl_key(text: &str) -> Option<(String, String)> {
    let mut words = text.split_whitespace();
    let kw = words.next()?;
    if kw == "instance" {
        return None;
    }
    let name = words.next()?;
    let name = name.split(['(', ':', '=']).next()?;
    Some((kw.to_string(), name.to_string()))
}

// Dispatch a resolved `:command`. Returns whether the REPL keeps running.
fn command(session: &mut Session, built: &mut Built, cmd: &str, arg: &str) -> bool {
    match cmd {
        ":quit" => return false,
        ":help" => help(),
        ":type" => show_type(session, built, arg),
        ":load" => {
            if arg.is_empty() {
                eprintln!("usage: :load <file>");
            } else {
                load_file(session, built, arg);
            }
        }
        ":reload" => match session.active.clone() {
            Some(p) => {
                commit(session, built, session.segs.clone(), &p);
            }
            None => eprintln!("no active file; load one with :load <file>"),
        },
        ":edit" => edit(session, built, arg),
        ":browse" => browse(session, built, arg),
        ":core" => core(session),
        ":info" => info(session, built, arg),
        ":kind" => kind(built, arg),
        ":set" => {
            let holes_before = session.flags.holes;
            set(session, arg);
            if holes_before != session.flags.holes {
                match session.build() {
                    Ok((_, rebuilt)) => *built = rebuilt,
                    Err(e) => {
                        session.flags.holes = holes_before;
                        let src = session.compose().unwrap_or_default();
                        report(&e, &src, "<repl>");
                    }
                }
            }
        }
        _ => eprintln!("unknown command `{cmd}`; type :help for a list"),
    }
    true
}

fn help() {
    println!(":t <expr>      show the type and effects of an expression");
    println!(":kind <type>   show the kind of a type constructor");
    println!(":info <name>   describe a binding, type, or class");
    println!(":browse [M]    list session bindings, or the public names in module M");
    println!(":core          dump the lowered core IR of this session");
    println!(":load <file>   load declarations from a file");
    println!(":reload        re-read the active file from disk");
    println!(":edit [file]   open a file (or scratch) in $EDITOR, then load it");
    println!(":set [+-]tsh   toggle options (bare :set lists them)");
    println!(":quit          quit");
    println!("any unambiguous prefix works, ghci style (:r, :lo, :e)");
    println!(":{{ ... :}}       enter a multi-line block (also auto-detected)");
    println!("let x = e      bind a variable (re-evaluated per use); `it` is the last result");
    println!("<expr>         evaluate an expression");
    println!("import/fn/type/class/instance ... add a declaration to the session");
    println!("example        map(\\(x) -> x * x, [1..5])");
}

// Dump the lowered core IR (effects lowered, rc and reuse applied) of the
// session's own functions, prelude elided.
fn core(session: &Session) {
    match session
        .compose()
        .and_then(|s| crate::core_ir_full(&s, &PathBuf::from(".")))
    {
        Ok(ir) if ir.trim().is_empty() => println!("nothing defined yet"),
        Ok(ir) => print!("{ir}"),
        Err(e) => eprintln!("{e}"),
    }
}

// List what the session added on top of the prelude: declarations, then
// constructors, then `let` bindings.
fn browse(session: &Session, built: &Built, module: &str) {
    if !module.is_empty() {
        return browse_module(built, module);
    }
    let mut any = false;
    // Bare names only: a dotted/`@` canonical name is reachable qualified, not
    // in scope, so a module imported without `(..)` does not appear here even
    // though its declarations are checked and live in `built.checked`.
    for d in &built.checked.decls {
        if !d.name.contains(['.', '@']) && !session.base.contains(&d.name) {
            println!("{} : {}", d.name, d.ty.show());
            any = true;
        }
    }
    for (n, c) in &built.checked.ctors {
        if !n.contains(['.', '@']) && !session.base.contains(n) {
            println!("{n} : {}", ctor_type(c).show());
            any = true;
        }
    }
    // Names an explicit `import M (..)` or `import M (a, b)` opened unqualified
    // this session, resolved back to their checked types.
    for (name, canonical) in &built.imports {
        if session.base.contains(name) {
            continue;
        }
        if let Some(d) = built.checked.decls.iter().find(|d| &d.name == canonical) {
            println!("{name} : {}", d.ty.show());
            any = true;
        } else if let Some(c) = built.checked.ctors.get(canonical) {
            println!("{name} : {}", ctor_type(c).show());
            any = true;
        }
    }
    for (n, rhs) in &session.lets {
        println!("{n} = {rhs}");
        any = true;
    }
    if !any {
        println!("nothing defined yet");
    }
}

fn browse_module(built: &Built, module: &str) {
    let Some(path) = built.modules.get(module) else {
        eprintln!("'{module}' is not an open module");
        return;
    };
    let prefix = format!("{path}.");
    let mut rows = Vec::new();
    for decl in &built.checked.decls {
        if let Some(name) = decl.name.strip_prefix(&prefix) {
            rows.push((
                name.to_string(),
                format!(
                    "{name} : {}",
                    show_type_with_effects(&decl.ty, &decl.effects)
                ),
            ));
        }
    }
    for (canonical, ctor) in &built.checked.ctors {
        if let Some(name) = canonical.strip_prefix(&prefix) {
            rows.push((
                name.to_string(),
                format!("{name} : {}", ctor_type(ctor).show()),
            ));
        }
    }
    for canonical in built.checked.data.keys() {
        if let Some(name) = canonical.strip_prefix(&prefix) {
            rows.push((name.to_string(), format!("type {name}")));
        }
    }
    for canonical in built.classes.keys() {
        if let Some(name) = canonical.strip_prefix(&prefix) {
            rows.push((name.to_string(), format!("class {name}")));
        }
    }
    rows.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    rows.dedup_by(|a, b| a.1 == b.1);
    if rows.is_empty() {
        println!("module {path} exports no browsable names");
    } else {
        for (_, row) in rows {
            println!("{row}");
        }
    }
}

// The function type a constructor denotes: its argument types to the data type.
fn ctor_type(c: &CtorInfo) -> Type {
    let params = c.params.iter().map(|p| Type::Var(*p)).collect();
    let result = Type::Con(c.type_name, params);
    if c.args.is_empty() {
        result
    } else {
        Type::fun(c.args.clone(), result)
    }
}

fn info(session: &Session, built: &Built, name: &str) {
    let out = info_lines(session, built, name);
    if out.is_empty() {
        eprintln!("'{name}' is not in scope");
    } else {
        for line in out {
            println!("{line}");
        }
    }
}

fn info_lines(session: &Session, built: &Built, query: &str) -> Vec<String> {
    let ck = &built.checked;
    let mut out: Vec<String> = Vec::new();
    // Session lets shadow imports in expression resolution, so they must do the
    // same for `:info` rather than being canonicalized through an import first.
    if let Some((_, rhs)) = session.lets.iter().find(|(name, _)| name == query) {
        out.push(format!("{query} = {rhs}"));
        return out;
    }
    // A bare query (`map`) names a glob-imported binding stored under its
    // canonical symbol (`Data.List.map`); resolve it the way an expression would.
    let name = built.imports.get(query).map_or(query, String::as_str);
    if let Some(d) = ck.decls.iter().find(|d| d.name == name) {
        out.push(format!(
            "{name} : {}",
            show_type_with_effects(&d.ty, &d.effects)
        ));
    }
    if let Some(c) = ck.ctors.get(name) {
        let mut s = format!("constructor of {}: {}", c.type_name, ctor_type(c).show());
        if !c.fields.is_empty() {
            let _ = write!(
                s,
                "\n  fields: {}",
                c.fields
                    .iter()
                    .map(|f| f.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        out.push(s);
    }
    if let Some(d) = ck.data.get(name) {
        let head = if d.params.is_empty() {
            name.to_string()
        } else {
            format!("{name}({})", d.params.join(", "))
        };
        out.push(format!("type {head} = {}", d.ctors.join(" | ")));
    }
    if let Some(class) = built.classes.get(name) {
        out.push(fmt_class(class));
    }
    out
}

// The kind of a named type constructor, from its parameter count.
fn kind(built: &Built, name: &str) {
    let name = built.imports.get(name).map_or(name, String::as_str);
    let arity = if Type::SCALARS.iter().any(|t| t.show() == name) {
        Some(0)
    } else {
        built.checked.data.get(name).map(|d| d.params.len())
    };
    match arity {
        Some(n) => {
            let k = std::iter::repeat_n("*", n + 1)
                .collect::<Vec<_>>()
                .join(" -> ");
            println!("{name} : {k}");
        }
        None => eprintln!("'{name}' is not a known type"),
    }
}

// The settable toggles, one row each: letter, name, description, and the
// accessor into Flags. Single source so bare `:set` (the discovery listing) and
// `:set [+-]x` (the mutator) can never drift.
type Toggle = (
    char,
    &'static str,
    &'static str,
    fn(&mut Flags) -> &mut bool,
);
const TOGGLES: &[Toggle] = &[
    ('t', "types", "show inferred type and effect row", |f| {
        &mut f.types
    }),
    ('s', "timing", "show evaluation time", |f| &mut f.timing),
    ('h', "holes", "defer typed holes to runtime faults", |f| {
        &mut f.holes
    }),
];

// `:set +t -s` toggles options. Bare `:set` lists them with their state.
fn set(session: &mut Session, arg: &str) {
    if arg.is_empty() {
        println!("options (:set +x to enable, -x to disable):");
        for (ch, name, desc, get) in TOGGLES {
            let on = *get(&mut session.flags);
            println!("  +{ch}  {name:<7}{desc:<36}[{}]", on_off(on));
        }
        return;
    }
    for tok in arg.split_whitespace() {
        let mut chars = tok.chars();
        let (on, flag) = match chars.next() {
            Some('+') => (true, chars.as_str()),
            Some('-') => (false, chars.as_str()),
            _ => {
                eprintln!("usage: :set +t -s +h  (bare :set lists options)");
                continue;
            }
        };
        let row = TOGGLES.iter().find(|(ch, ..)| {
            let mut cs = flag.chars();
            cs.next() == Some(*ch) && cs.next().is_none()
        });
        match row {
            Some((.., get)) => *get(&mut session.flags) = on,
            None => eprintln!("unknown flag '{flag}' (bare :set lists options)"),
        }
    }
}

const fn on_off(b: bool) -> &'static str {
    if b {
        "on"
    } else {
        "off"
    }
}

fn show_type(session: &Session, built: &Built, rest: &str) {
    let text = session.chain(rest);
    let desugared = match parse_expr(&text) {
        Err(e) => return report(&e.into(), &text, "<repl>"),
        Ok(mut e) => match resolve_expr(&mut e, &built.imports) {
            Err(e) => return report(&e, &text, "<repl>"),
            Ok(()) => desugar_expr(&e),
        },
    };
    match desugared {
        Err(e) => report(&e.into(), &text, "<repl>"),
        Ok(e) => match infer_expr(&built.checked, &e) {
            Ok((ty, eff)) => println!("{rest} : {}", show_type_with_effects(&ty, &eff)),
            Err(e) => report(&e.into(), &text, "<repl>"),
        },
    }
}

// Open `arg`, the active file, or a stable scratch file in $EDITOR. On a clean
// exit, load it as the active file so its declarations enter the session.
fn edit(session: &mut Session, built: &mut Built, arg: &str) {
    let path = if !arg.is_empty() {
        arg.to_string()
    } else if let Some(a) = &session.active {
        a.clone()
    } else {
        env::temp_dir()
            .join("prism_scratch.pr")
            .to_string_lossy()
            .into_owned()
    };
    let editor = env::var("VISUAL")
        .or_else(|_| env::var("EDITOR"))
        .unwrap_or_else(|_| "vi".into());
    match Command::new(&editor).arg(&path).status() {
        Ok(s) if s.success() => load_file(session, built, &path),
        Ok(s) => eprintln!("{editor} exited with {s}"),
        Err(e) => eprintln!("could not launch {editor}: {e}"),
    }
}

// Upsert a file segment and, on a successful build, mark it active so `:reload`
// and a bare `:edit` target it. Used by both `:load` and `:edit`.
fn load_file(session: &mut Session, built: &mut Built, path: &str) {
    let mut cand = session.segs.clone();
    let seg = Seg::File(path.to_string());
    match cand
        .iter()
        .position(|s| matches!(s, Seg::File(p) if p == path))
    {
        Some(i) => cand[i] = seg,
        None => cand.push(seg),
    }
    if commit(session, built, cand, path) {
        session.active = Some(path.to_string());
    }
}

// Probe a candidate segment list, committing only on a successful build, so a
// bad :load or declaration never poisons the session. Returns whether it took.
fn commit(session: &mut Session, built: &mut Built, cand: Vec<Seg>, name: &str) -> bool {
    commit_as(session, built, cand, name, "ok")
}

// Same as `commit`, but with a caller-chosen success message: `import Teleport`
// reads better as "Imported Teleport successfully" than a bare "ok".
fn commit_as(
    session: &mut Session,
    built: &mut Built,
    cand: Vec<Seg>,
    name: &str,
    msg: &str,
) -> bool {
    let probe = Session::probe(cand, Vec::new());
    match probe.build() {
        Ok((_, b)) => {
            session.segs = probe.segs;
            *built = b;
            println!("{msg}");
            true
        }
        Err(Error::Io(e)) => {
            eprintln!("{name}: {e}");
            false
        }
        Err(e) => {
            let src = probe.compose().unwrap_or_default();
            report(&e, &src, name);
            false
        }
    }
}

fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next()
        .is_some_and(|c| c.is_ascii_lowercase() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

// `x = e` binds like ghci. `x == e` and non-ident left sides are expressions.
fn bare_bind(line: &str) -> Option<()> {
    let (lhs, rhs) = line.split_once('=')?;
    (is_ident(lhs.trim()) && !rhs.starts_with('=')).then_some(())
}

fn try_let(line: &str) -> Option<(String, String)> {
    let body = line.strip_prefix("let ").unwrap_or(line);
    let (lhs, rhs) = body.split_once('=')?;
    if rhs.starts_with('=') {
        return None;
    }
    let (name, ann) = match lhs.split_once(':') {
        Some((n, a)) => (n.trim(), Some(a.trim())),
        None => (lhs.trim(), None),
    };
    let rhs = rhs.trim();
    if !is_ident(name) || rhs.is_empty() {
        return None;
    }
    let rhs = ann.map_or_else(|| rhs.to_string(), |a| format!("({rhs} : {a})"));
    Some((name.to_string(), rhs))
}

fn report(e: &Error, src: &str, name: &str) {
    let rendered = e.render(src, name);
    if rendered.ends_with('\n') {
        eprint!("{rendered}");
    } else {
        eprintln!("{rendered}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh() -> (Session, Built) {
        let session = Session::probe(Vec::new(), Vec::new());
        let (_, built) = session
            .build()
            .expect("bare prelude must build in a fresh REPL");
        (session, built)
    }

    // A fresh REPL session must build the bare prelude on launch. The prelude
    // opens the `Data.*` stdlib modules with glob imports, so `build` has to
    // resolve modules against the stdlib roots; regressing that (e.g. dropping
    // the resolve step) leaves stdlib names like `nth` unbound and the REPL
    // dies before the first prompt.
    #[test]
    fn prelude_loads_on_launch() {
        let (_, built) = fresh();
        // A successful build already proves imports resolved: `at_list` (a prelude
        // function) calls `nth` from the `Data.List` stdlib module, so an
        // unresolved import would have failed above with an unbound-variable error.
        assert!(built.arity.contains_key("at_list"));
    }

    #[test]
    fn interactive_import_is_live_transactional_and_idempotent() {
        let (mut session, mut built) = fresh();
        assert!(!built.imports.contains_key("vempty"));

        assert!(step(&mut session, &mut built, "import Data.Vec (..)"));
        assert_eq!(
            built.imports.get("vempty").map(String::as_str),
            Some("Data.Vec.vempty")
        );
        assert_eq!(session.segs.len(), 1);
        let once = session.compose().unwrap();

        assert!(step(&mut session, &mut built, "import Data.Vec (..)"));
        assert_eq!(session.segs.len(), 1, "re-import replaces the same segment");
        assert_eq!(session.compose().unwrap(), once);

        let before_imports = built.imports.clone();
        assert!(step(&mut session, &mut built, "import Missing.Module (..)"));
        assert_eq!(
            session.compose().unwrap(),
            once,
            "failed import rolls back source state"
        );
        assert_eq!(
            built.imports, before_imports,
            "failed import rolls back resolver state"
        );
    }

    #[test]
    fn completion_routes_over_the_rebuilt_resolver_scope() {
        let (mut session, mut built) = fresh();
        step(&mut session, &mut built, "import Data.Vec (..)");

        assert!(built.completion.values.contains("vempty"));
        assert!(built.completion.types.contains("Vec"));
        assert!(built.completion.modules.contains("Data.Vec"));
        assert!(built.completion.modules.contains("Vec"));
        assert!(built.completion.importable_modules.contains("Json"));
        assert!(
            built
                .completion
                .values
                .iter()
                .all(|name| !name.contains('@')),
            "private resolver symbols must not complete"
        );

        let line = ":kind Ve";
        assert_eq!(completion_kind(line, line.len()), CompletionKind::Types);
        let (_, pairs) =
            name_candidates(&built.completion, CompletionKind::Types, line, line.len());
        assert!(pairs.iter().any(|pair| pair.replacement == "Vec"));

        let line = ":browse Data.V";
        assert_eq!(completion_kind(line, line.len()), CompletionKind::Modules);
        let (_, pairs) =
            name_candidates(&built.completion, CompletionKind::Modules, line, line.len());
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.replacement.as_str())
                .collect::<Vec<_>>(),
            vec!["Data.Vec"]
        );
    }

    #[test]
    fn info_class_uses_the_canonical_superclass_printer() {
        let mut session = Session::probe(
            vec![Seg::Text(
                "class Parent(a)\n\nclass Child(a) given Parent(a)".to_string(),
            )],
            Vec::new(),
        );
        let (_, built) = session.build().expect("class declarations type check");
        let lines = info_lines(&session, &built, "Child");
        assert_eq!(lines, vec!["class Child(a) given Parent(a)"]);

        session.lets.push(("map".into(), "41".into()));
        assert_eq!(
            info_lines(&session, &built, "map"),
            vec!["map = 41"],
            "a live let shadows the prelude import in :info"
        );
    }

    #[test]
    fn hole_toggle_changes_expression_evaluation_policy() {
        let (mut session, built) = fresh();
        let error = session
            .eval_chained(&built, "?todo")
            .expect_err("holes are rejected by default");
        let Error::Type(error) = error else {
            panic!("expected a type error, got {error}");
        };
        assert_eq!(error.code(), Some(crate::error::TYPED_HOLE.as_str()));

        session.flags.holes = true;
        let error = session
            .eval_chained(&built, "?todo")
            .expect_err("reaching a deferred hole faults");
        let Error::RuntimeEvaluation(fault) = error else {
            panic!("expected a runtime fault, got {error}");
        };
        assert_eq!(
            fault,
            crate::error::typed_hole_fault("todo", marginalia::Span::new(0, 5))
        );
    }

    // Elaborating a structural print/interpolation synthesizes a `_show_*`
    // helper on demand. A whole-program compile folds those into its Core; the
    // REPL evaluates one expression at a time against a pre-built environment,
    // so it must register the freshly synthesized helpers, or the call to one
    // faults at runtime as an unknown function (E7500). `println` and string
    // interpolation share the synthesis path: the print forms prove it runs,
    // the interpolated forms pin the exact rendered text.
    #[test]
    fn synthesized_show_helpers_reach_the_runtime_environment() {
        let (session, built) = fresh();
        for expr in ["println([1])", "println([1, 2, 3])", "println((1, [2]))"] {
            let (val, ty, _) = session
                .eval_chained(&built, expr)
                .unwrap_or_else(|e| panic!("`{expr}` must evaluate without a fault, got: {e}"));
            assert_eq!(val, "()", "`{expr}` returns unit");
            assert_eq!(ty, "Unit", "`{expr}` has unit type");
        }
        for (expr, rendered) in [
            ("\"{[1]}\"", "\"[1]\""),
            ("\"{[1, 2, 3]}\"", "\"[1, 2, 3]\""),
            ("\"{(1, [2])}\"", "\"(1, [2])\""),
        ] {
            let (val, ..) = session
                .eval_chained(&built, expr)
                .unwrap_or_else(|e| panic!("`{expr}` must evaluate without a fault, got: {e}"));
            assert_eq!(val, rendered, "`{expr}` renders its structural value");
        }
    }
}
