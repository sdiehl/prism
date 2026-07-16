//! Type-directed generator of small, well-typed Prism programs for the
//! differential-determinism gate.
//!
//! Every program it emits is total and well-typed by construction: arithmetic is
//! bignum-total (no overflow, no division), there is no recursion or loop, and
//! every subterm is generated against a target type under a typing context, so a
//! name is only referenced where it is in scope at the right type. The payoff is a
//! clean signal: a compile failure is a generator bug, and any observation-trace
//! divergence across tiers, backends, or optimizer levels is a compiler bug.
//!
//! Two program families are produced. The pure family exercises the typed core
//! (arithmetic, comparison, `if`, `let`). The effectful family wraps a generated
//! body in either a full handler or a `partial` handler forwarding its residual
//! row to an outer handler, so the residual-handler lowering is diffed the same
//! way. Arena handlers are a deliberate extension point once `with_arena` lands.

use std::fmt::Write as _;

/// A small deterministic LCG. Seeded generation keeps the corpus reproducible,
/// which the determinism gate requires; the constants are the well-known
/// Knuth/PCG multiplier and increment.
pub struct Rng(u64);

impl Rng {
    #[must_use]
    pub const fn seeded(seed: u64) -> Self {
        Self(seed)
    }

    const fn bits(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 16
    }

    // Uniform in `0..n` (n > 0).
    const fn below(&mut self, n: u64) -> u64 {
        self.bits() % n
    }

    // A uniform index into `0..n`, used for slice picks; the fallible conversion
    // keeps clippy's truncation lint quiet where a bare `as usize` would fire.
    fn index(&mut self, n: usize) -> usize {
        usize::try_from(self.below(n as u64)).unwrap()
    }

    // A literal small enough to read in a reproducer, signed so subtraction and
    // negative branches are covered.
    fn literal(&mut self) -> i64 {
        i64::try_from(self.below(21)).unwrap_or(0) - 10
    }

    const fn one_in(&mut self, n: u64) -> bool {
        self.below(n) == 0
    }
}

/// The two ground types the fragment ranges over.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ty {
    Int,
    Bool,
}

#[derive(Clone, Copy)]
enum BinOp {
    Add,
    Sub,
    Mul,
}

impl BinOp {
    const fn spelling(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
        }
    }
}

#[derive(Clone, Copy)]
enum CmpOp {
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,
}

impl CmpOp {
    const fn spelling(self) -> &'static str {
        match self {
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Le => "<=",
            Self::Ge => ">=",
            Self::Eq => "==",
            Self::Ne => "/=",
        }
    }
}

/// A generated expression of a statically known type. Rendering is fully
/// parenthesized, so the emitted text never depends on operator precedence.
enum Expr {
    Int(i64),
    Bool(bool),
    Var(String),
    Bin(BinOp, Box<Self>, Box<Self>),
    Cmp(CmpOp, Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    If(Box<Self>, Box<Self>, Box<Self>),
    Let(String, Box<Self>, Box<Self>),
}

impl Expr {
    fn render(&self) -> String {
        match self {
            Self::Int(n) => n.to_string(),
            Self::Bool(b) => b.to_string(),
            Self::Var(name) => name.clone(),
            Self::Bin(op, a, b) => format!("({} {} {})", a.render(), op.spelling(), b.render()),
            Self::Cmp(op, a, b) => format!("({} {} {})", a.render(), op.spelling(), b.render()),
            Self::And(a, b) => format!("({} && {})", a.render(), b.render()),
            Self::Or(a, b) => format!("({} || {})", a.render(), b.render()),
            Self::Not(a) => format!("(not ({}))", a.render()),
            Self::If(c, t, e) => {
                format!(
                    "(if {} then {} else {})",
                    c.render(),
                    t.render(),
                    e.render()
                )
            }
            Self::Let(name, value, body) => {
                format!("(let {name} = {} in {})", value.render(), body.render())
            }
        }
    }

    // The canonical minimal inhabitant of a type, the floor every shrink walks
    // toward.
    const fn leaf(ty: Ty) -> Self {
        match ty {
            Ty::Int => Self::Int(0),
            Ty::Bool => Self::Bool(true),
        }
    }
}

/// Names in scope with their types, plus a monotonic counter so every binder is
/// unique (Prism's top-level namespace is flat, and unique locals keep rendered
/// programs unambiguous).
#[derive(Clone)]
struct Ctx {
    vars: Vec<(String, Ty)>,
    next: u32,
}

impl Ctx {
    const fn new(next: u32) -> Self {
        Self {
            vars: Vec::new(),
            next,
        }
    }

    fn fresh(&mut self) -> String {
        let name = format!("x{}", self.next);
        self.next += 1;
        name
    }

    fn of_type(&self, ty: Ty) -> Vec<String> {
        self.vars
            .iter()
            .filter(|(_, t)| *t == ty)
            .map(|(n, _)| n.clone())
            .collect()
    }
}

// Generate an expression of `ty` under `ctx`. `fuel` bounds depth: at zero the
// result is a leaf, so generation always terminates and stays shallow enough to
// run under every tier.
fn gen_expr(rng: &mut Rng, ctx: &Ctx, ty: Ty, fuel: u32) -> Expr {
    let vars = ctx.of_type(ty);
    if fuel == 0 || rng.one_in(3) {
        return leaf_of(rng, ty, &vars);
    }
    match ty {
        Ty::Int => match rng.below(3) {
            0 => {
                let op = [BinOp::Add, BinOp::Sub, BinOp::Mul][rng.index(3)];
                Expr::Bin(
                    op,
                    Box::new(gen_expr(rng, ctx, Ty::Int, fuel - 1)),
                    Box::new(gen_expr(rng, ctx, Ty::Int, fuel - 1)),
                )
            }
            1 => Expr::If(
                Box::new(gen_expr(rng, ctx, Ty::Bool, fuel - 1)),
                Box::new(gen_expr(rng, ctx, Ty::Int, fuel - 1)),
                Box::new(gen_expr(rng, ctx, Ty::Int, fuel - 1)),
            ),
            _ => gen_let(rng, ctx, Ty::Int, fuel),
        },
        Ty::Bool => match rng.below(4) {
            0 => {
                let op = [
                    CmpOp::Lt,
                    CmpOp::Gt,
                    CmpOp::Le,
                    CmpOp::Ge,
                    CmpOp::Eq,
                    CmpOp::Ne,
                ][rng.index(6)];
                Expr::Cmp(
                    op,
                    Box::new(gen_expr(rng, ctx, Ty::Int, fuel - 1)),
                    Box::new(gen_expr(rng, ctx, Ty::Int, fuel - 1)),
                )
            }
            1 => Expr::And(
                Box::new(gen_expr(rng, ctx, Ty::Bool, fuel - 1)),
                Box::new(gen_expr(rng, ctx, Ty::Bool, fuel - 1)),
            ),
            2 => Expr::Or(
                Box::new(gen_expr(rng, ctx, Ty::Bool, fuel - 1)),
                Box::new(gen_expr(rng, ctx, Ty::Bool, fuel - 1)),
            ),
            _ => Expr::Not(Box::new(gen_expr(rng, ctx, Ty::Bool, fuel - 1))),
        },
    }
}

fn leaf_of(rng: &mut Rng, ty: Ty, vars: &[String]) -> Expr {
    // Prefer an in-scope variable when one exists: it keeps `let` bindings live
    // (fewer dead-binding programs) and diffs more variable-substitution paths.
    if !vars.is_empty() && !rng.one_in(3) {
        return Expr::Var(vars[rng.index(vars.len())].clone());
    }
    match ty {
        Ty::Int => Expr::Int(rng.literal()),
        Ty::Bool => Expr::Bool(rng.one_in(2)),
    }
}

fn gen_let(rng: &mut Rng, ctx: &Ctx, ty: Ty, fuel: u32) -> Expr {
    let bind_ty = if rng.one_in(2) { Ty::Int } else { Ty::Bool };
    let value = gen_expr(rng, ctx, bind_ty, fuel - 1);
    let mut inner = ctx.clone();
    let name = inner.fresh();
    inner.vars.push((name.clone(), bind_ty));
    let body = gen_expr(rng, &inner, ty, fuel - 1);
    Expr::Let(name, Box::new(value), Box::new(body))
}

// One handler arm's shape: a plain tail resume, or a non-tail resume whose result
// is observably combined after the continuation returns (the case that exposes
// resumption ordering across tiers).
#[derive(Clone)]
struct Arm {
    delta: i64,
    post: Option<i64>,
}

impl Arm {
    fn render(&self, op: &str) -> String {
        let delta = self.delta;
        self.post.map_or_else(
            || format!("    {op}(x) resume k => k((x + {delta}))"),
            |p| format!("    {op}(x) resume k => let r = k((x + {delta})) in (r + {p})"),
        )
    }
}

/// A generated effectful program: a body performing a fixed two-operation effect,
/// wrapped in a full handler or a `partial` handler that forwards its residual to
/// an outer full handler.
struct EffProgram {
    calls: Vec<bool>, // true = op `a`, false = op `b`
    partial: bool,
    inner: Arm, // the arm the partial handler discharges (op `a`)
    outer_a: Arm,
    outer_b: Arm,
    combine: Expr, // an Int expression over the call results v0..vN
    return_delta: i64,
}

/// The generator's output: either a pure typed-core program or an effectful one.
pub struct Program(Repr);

/// Semantic family exercised by a generated program. Differential gates use
/// this metadata to prove a deterministic seed did not accidentally collapse to
/// only one lowering path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramFamily {
    Pure,
    FullHandler,
    PartialHandler,
}

enum Repr {
    Pure(Expr),
    Eff(EffProgram),
}

impl Program {
    /// The semantic family this program exercises.
    #[must_use]
    pub const fn family(&self) -> ProgramFamily {
        match &self.0 {
            Repr::Pure(_) => ProgramFamily::Pure,
            Repr::Eff(eff) if eff.partial => ProgramFamily::PartialHandler,
            Repr::Eff(_) => ProgramFamily::FullHandler,
        }
    }

    /// The runnable `.pr` source. `main` prints an `Int`, so the observation trace
    /// is a single deterministic line plus the exit code.
    #[must_use]
    pub fn render(&self) -> String {
        match &self.0 {
            Repr::Pure(expr) => format!("fn main() = println({})\n", expr.render()),
            Repr::Eff(eff) => eff.render(),
        }
    }

    /// Source for final-value oracles. Unlike [`Self::render`], `main` returns the
    /// generated `Int` itself, so an evaluator that does not expose the output
    /// transcript still observes the program's result rather than a vacuous
    /// `Unit` from `println`.
    #[must_use]
    pub fn render_oracle(&self) -> String {
        match &self.0 {
            Repr::Pure(expr) => format!("fn main() = {}\n", expr.render()),
            Repr::Eff(eff) => eff.render_oracle(),
        }
    }

    /// Strictly simpler programs, for greedy shrinking toward a minimal reproducer.
    #[must_use]
    pub fn reductions(&self) -> Vec<Self> {
        match &self.0 {
            Repr::Pure(expr) => shrink_expr(expr)
                .into_iter()
                .map(|e| Self(Repr::Pure(e)))
                .collect(),
            Repr::Eff(eff) => eff.reductions().map(|e| Self(Repr::Eff(e))).collect(),
        }
    }
}

impl EffProgram {
    fn render(&self) -> String {
        self.render_with_main("println(run())")
    }

    fn render_oracle(&self) -> String {
        self.render_with_main("run()")
    }

    fn render_with_main(&self, main: &str) -> String {
        let mut src = String::from("effect Probe\n  a(Int) : Int\n  b(Int) : Int\n\n");
        src.push_str("fn work() : Int ! {Probe} =\n");
        for (i, &is_a) in self.calls.iter().enumerate() {
            let op = if is_a { "a" } else { "b" };
            let _ = writeln!(src, "  let v{i} = {op}({i})");
        }
        let _ = writeln!(src, "  {}\n", self.combine.render());

        let _ = writeln!(src, "fn run() : Int =");
        if self.partial {
            let _ = writeln!(src, "  handle (handle work() with partial {{");
            let _ = writeln!(src, "{},", self.inner.render("a"));
            let _ = writeln!(src, "    return r => r\n  }}) with {{");
        } else {
            let _ = writeln!(src, "  handle work() with {{");
        }
        let _ = writeln!(src, "{},", self.outer_a.render("a"));
        let _ = writeln!(src, "{},", self.outer_b.render("b"));
        let _ = writeln!(src, "    return r => (r + {})\n  }}\n", self.return_delta);
        let _ = writeln!(src, "fn main() = {main}");
        src
    }

    fn reductions(&self) -> impl Iterator<Item = Self> + '_ {
        let mut out = Vec::new();
        // Drop a call, but keep at least one of each op so both arms stay live.
        for i in 0..self.calls.len() {
            let mut calls = self.calls.clone();
            calls.remove(i);
            if calls.iter().any(|&a| a) && calls.iter().any(|&a| !a) {
                let mut r = self.clone_with(calls);
                r.combine = Expr::leaf(Ty::Int);
                out.push(r);
            }
        }
        // Simplify the combine expression.
        for e in shrink_expr(&self.combine) {
            let mut r = self.clone_self();
            r.combine = e;
            out.push(r);
        }
        // Zero each delta, drop the non-tail tails, and collapse partial to full.
        for r in self.arm_reductions() {
            out.push(r);
        }
        out.into_iter()
    }
}

// Same-typed, strictly-smaller variants of an expression. Every node offers a
// collapse to its type's canonical leaf, so shrinking always terminates at a
// minimal witness; structured nodes also offer their same-typed children and
// per-child shrinks.
fn shrink_expr(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let collapse = |ty: Ty| Expr::leaf(ty);
    match expr {
        Expr::Int(n) if *n != 0 => out.push(Expr::Int(0)),
        Expr::Bool(false) => out.push(Expr::Bool(true)),
        Expr::Int(_) | Expr::Bool(_) | Expr::Var(_) => {}
        Expr::Bin(op, a, b) => {
            out.push((**a).clone_expr());
            out.push((**b).clone_expr());
            for a2 in shrink_expr(a) {
                out.push(Expr::Bin(*op, Box::new(a2), Box::new((**b).clone_expr())));
            }
            for b2 in shrink_expr(b) {
                out.push(Expr::Bin(*op, Box::new((**a).clone_expr()), Box::new(b2)));
            }
        }
        Expr::Cmp(op, a, b) => {
            out.push(collapse(Ty::Bool));
            for a2 in shrink_expr(a) {
                out.push(Expr::Cmp(*op, Box::new(a2), Box::new((**b).clone_expr())));
            }
            for b2 in shrink_expr(b) {
                out.push(Expr::Cmp(*op, Box::new((**a).clone_expr()), Box::new(b2)));
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) => {
            out.push((**a).clone_expr());
            out.push((**b).clone_expr());
        }
        Expr::Not(a) => {
            out.push((**a).clone_expr());
        }
        Expr::If(c, t, e) => {
            out.push((**t).clone_expr());
            out.push((**e).clone_expr());
            let _ = c;
        }
        Expr::Let(name, value, body) => {
            // The body has the whole expression's type; keep it only when it does
            // not reference the bound name (else it would go out of scope).
            if !mentions(body, name) {
                out.push((**body).clone_expr());
            }
            for v2 in shrink_expr(value) {
                out.push(Expr::Let(
                    name.clone(),
                    Box::new(v2),
                    Box::new((**body).clone_expr()),
                ));
            }
        }
    }
    out
}

fn mentions(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Var(n) => n == name,
        Expr::Int(_) | Expr::Bool(_) => false,
        Expr::Not(a) => mentions(a, name),
        Expr::Bin(_, a, b) | Expr::Cmp(_, a, b) | Expr::And(a, b) | Expr::Or(a, b) => {
            mentions(a, name) || mentions(b, name)
        }
        Expr::If(c, t, e) => mentions(c, name) || mentions(t, name) || mentions(e, name),
        // A shadowing inner `let` of the same name would rebind, but the generator
        // never reuses a name, so any occurrence in `value`/`body` counts.
        Expr::Let(_, v, b) => mentions(v, name) || mentions(b, name),
    }
}

impl Expr {
    fn clone_expr(&self) -> Self {
        match self {
            Self::Int(n) => Self::Int(*n),
            Self::Bool(b) => Self::Bool(*b),
            Self::Var(n) => Self::Var(n.clone()),
            Self::Bin(op, a, b) => {
                Self::Bin(*op, Box::new(a.clone_expr()), Box::new(b.clone_expr()))
            }
            Self::Cmp(op, a, b) => {
                Self::Cmp(*op, Box::new(a.clone_expr()), Box::new(b.clone_expr()))
            }
            Self::And(a, b) => Self::And(Box::new(a.clone_expr()), Box::new(b.clone_expr())),
            Self::Or(a, b) => Self::Or(Box::new(a.clone_expr()), Box::new(b.clone_expr())),
            Self::Not(a) => Self::Not(Box::new(a.clone_expr())),
            Self::If(c, t, e) => Self::If(
                Box::new(c.clone_expr()),
                Box::new(t.clone_expr()),
                Box::new(e.clone_expr()),
            ),
            Self::Let(n, v, b) => Self::Let(
                n.clone(),
                Box::new(v.clone_expr()),
                Box::new(b.clone_expr()),
            ),
        }
    }
}

impl EffProgram {
    fn clone_self(&self) -> Self {
        self.clone_with(self.calls.clone())
    }

    fn clone_with(&self, calls: Vec<bool>) -> Self {
        Self {
            calls,
            partial: self.partial,
            inner: self.inner.clone(),
            outer_a: self.outer_a.clone(),
            outer_b: self.outer_b.clone(),
            combine: self.combine.clone_expr(),
            return_delta: self.return_delta,
        }
    }

    fn arm_reductions(&self) -> Vec<Self> {
        let mut out = Vec::new();
        if self.partial {
            let mut r = self.clone_self();
            r.partial = false;
            out.push(r);
        }
        if self.return_delta != 0 {
            let mut r = self.clone_self();
            r.return_delta = 0;
            out.push(r);
        }
        for select in 0..3 {
            let arm = [&self.inner, &self.outer_a, &self.outer_b][select];
            if arm.post.is_some() {
                let mut r = self.clone_self();
                [&mut r.inner, &mut r.outer_a, &mut r.outer_b][select].post = None;
                out.push(r);
            }
            if arm.delta != 0 {
                let mut r = self.clone_self();
                [&mut r.inner, &mut r.outer_a, &mut r.outer_b][select].delta = 0;
                out.push(r);
            }
        }
        out
    }
}

fn gen_arm(rng: &mut Rng) -> Arm {
    Arm {
        delta: rng.literal(),
        // A non-tail post is where resumption ordering becomes observable.
        post: if rng.one_in(2) {
            Some(rng.literal())
        } else {
            None
        },
    }
}

fn gen_effectful(rng: &mut Rng) -> EffProgram {
    let extra = rng.index(3);
    // At least one of each op so both handler arms and the residual forward fire.
    let mut calls = vec![true, false];
    for _ in 0..extra {
        calls.push(rng.one_in(2));
    }
    let mut ctx = Ctx::new(0);
    for i in 0..calls.len() {
        ctx.vars.push((format!("v{i}"), Ty::Int));
    }
    ctx.next = u32::try_from(calls.len()).unwrap();
    EffProgram {
        calls,
        partial: rng.one_in(2),
        inner: gen_arm(rng),
        outer_a: gen_arm(rng),
        outer_b: gen_arm(rng),
        combine: gen_expr(rng, &ctx, Ty::Int, 3),
        return_delta: rng.literal(),
    }
}

/// Generate `count` programs from `seed`: a mix of pure typed-core and effectful
/// (full/partial-handler) programs. Deterministic in the seed.
#[must_use]
pub fn generate(seed: u64, count: usize) -> Vec<Program> {
    let mut rng = Rng::seeded(seed);
    (0..count)
        .map(|_| {
            if rng.one_in(2) {
                Program(Repr::Pure(gen_expr(&mut rng, &Ctx::new(0), Ty::Int, 4)))
            } else {
                Program(Repr::Eff(gen_effectful(&mut rng)))
            }
        })
        .collect()
}

/// Greedily shrink `program` while `still_fails` keeps reporting a failure, then
/// return the minimal program and the last failure it produced. `still_fails`
/// returns `Some(reason)` for a failing program, `None` for a passing one.
pub fn shrink(
    mut program: Program,
    mut failure: String,
    still_fails: impl Fn(&Program) -> Option<String>,
) -> (Program, String) {
    loop {
        let mut smaller = None;
        for candidate in program.reductions() {
            if let Some(reason) = still_fails(&candidate) {
                smaller = Some((candidate, reason));
                break;
            }
        }
        match smaller {
            Some((candidate, reason)) => {
                program = candidate;
                failure = reason;
            }
            None => return (program, failure),
        }
    }
}
