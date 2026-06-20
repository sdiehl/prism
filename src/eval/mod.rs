use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::io::Write as _;
use std::rc::Rc;
use std::{env, fs, io, mem};

use num_bigint::{BigInt, Sign};

use crate::core::builtins::{Builtin, FloatOp};
use crate::core::{Comp, Core, CoreFn, CoreOp, CorePat, Value};
use crate::names::ENTRY_POINT;
use crate::sym::Sym;
use crate::types::{CONS, NIL};

#[derive(Clone, Debug)]
pub enum Rv {
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Big(BigInt),
    Closure(Rc<[Sym]>, Cmp, Env),
    Thunk(Cmp, Env),
    Data(Sym, Fields),
    Tuple(Fields),
    Resume(Rc<[Frame]>),
}

// Constructor payloads share structure via Rc, so cloning a value out of an env
// is O(1), not a deep copy. Drop drains children through a worklist rather than
// recursive drop glue, so freeing a deep structure cannot overflow the Rust
// stack (mirroring the C runtime's iterative prism_rc_dec).
#[derive(Clone, Debug)]
pub struct Fields(Rc<Vec<Rv>>);

impl std::ops::Deref for Fields {
    type Target = [Rv];
    fn deref(&self) -> &[Rv] {
        &self.0
    }
}

impl From<Vec<Rv>> for Fields {
    fn from(vs: Vec<Rv>) -> Self {
        Self(Rc::new(vs))
    }
}

impl Drop for Fields {
    fn drop(&mut self) {
        let Some(vs) = Rc::get_mut(&mut self.0) else {
            return;
        };
        let mut work = mem::take(vs);
        let mut i = 0;
        while i < work.len() {
            if let Rv::Data(_, fs) | Rv::Tuple(fs) = &mut work[i] {
                if let Some(inner) = Rc::get_mut(&mut fs.0) {
                    let mut inner = mem::take(inner);
                    work.append(&mut inner);
                }
            }
            i += 1;
        }
    }
}

type Env = Rc<BTreeMap<Sym, Rv>>;
pub type Cmp = Rc<Node>;

// Core lowered once into Rc-linked nodes so the machine can hold subterms in
// heap frames without deep-cloning them on every step.
#[derive(Debug)]
pub enum Node {
    Return(Atom),
    Bind(Cmp, Sym, Cmp),
    Force(Atom),
    Lam(Rc<[Sym]>, Cmp),
    App(Cmp, Rc<[Atom]>),
    If(Atom, Cmp, Cmp),
    Prim(CoreOp, Atom, Atom),
    Call(Sym, Vec<Atom>),
    Print(Atom),
    PrintNl,
    ReadInt,
    ReadLine,
    Rand,
    Srand(Atom),
    Error(Atom),
    Case(Atom, Vec<(CorePat, Cmp)>),
    FloatBuiltin(FloatOp, Atom),
    Do(Sym, Vec<Atom>),
    Handle(Rc<HandleInfo>),
    Mask(Rc<[Sym]>, Cmp),
    StrBuiltin(Builtin, Vec<Atom>),
}

#[derive(Debug)]
pub enum Atom {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(f64),
    Bool(bool),
    Unit,
    Str(String),
    Thunk(Cmp),
    Ctor(Sym, Vec<Self>),
    Tuple(Vec<Self>),
}

#[derive(Debug)]
pub struct HandleInfo {
    body: Cmp,
    ops: BTreeMap<Sym, (Vec<Sym>, Sym, Cmp)>,
    return_var: Option<Sym>,
    return_body: Option<Cmp>,
}

// Pending work lives on a heap stack of frames, so object-program recursion
// never grows the Rust call stack. A captured continuation is the slice of
// frames between a `do` and its handler (handler included: deep semantics);
// resuming pushes a clone of that slice back, which keeps resume multishot.
#[derive(Clone, Debug)]
pub enum Frame {
    Bind(Sym, Cmp, Env),
    Args(Rc<[Atom]>, Env),
    Restore(Sym),
    Handle(Rc<HandleInfo>, Env),
    Mask(Rc<[Sym]>),
}

enum State {
    Eval(Cmp, Env),
    Ret(Rv),
}

fn lower(c: &Comp) -> Cmp {
    let mut binds = Vec::new();
    let mut cur = c;
    while let Comp::Bind(m, x, n) = cur {
        binds.push((lower(m), *x));
        cur = n;
    }
    let mut acc = Rc::new(node(cur));
    for (m, x) in binds.into_iter().rev() {
        acc = Rc::new(Node::Bind(m, x, acc));
    }
    acc
}

fn node(c: &Comp) -> Node {
    match c {
        Comp::Return(v) => Node::Return(atom_of(v)),
        Comp::Bind(m, x, n) => Node::Bind(lower(m), *x, lower(n)),
        Comp::Force(v) => Node::Force(atom_of(v)),
        Comp::Lam(ps, b) => Node::Lam(Rc::from(ps.as_slice()), lower(b)),
        Comp::App(m, args) => Node::App(lower(m), args.iter().map(atom_of).collect()),
        Comp::If(v, t, e) => Node::If(atom_of(v), lower(t), lower(e)),
        Comp::Prim(op, a, b) => Node::Prim(*op, atom_of(a), atom_of(b)),
        Comp::Call(n, args) => Node::Call(*n, args.iter().map(atom_of).collect()),
        Comp::Print(v) | Comp::PrintF(v) | Comp::PrintS(v) => Node::Print(atom_of(v)),
        Comp::PrintNl => Node::PrintNl,
        Comp::ReadInt => Node::ReadInt,
        Comp::ReadLine => Node::ReadLine,
        Comp::Rand => Node::Rand,
        Comp::Srand(v) => Node::Srand(atom_of(v)),
        Comp::Error(v) => Node::Error(atom_of(v)),
        Comp::Case(v, arms) => Node::Case(
            atom_of(v),
            arms.iter().map(|(p, b)| (p.clone(), lower(b))).collect(),
        ),
        Comp::FloatBuiltin(n, v) => Node::FloatBuiltin(*n, atom_of(v)),
        Comp::Do(op, args) => Node::Do(*op, args.iter().map(atom_of).collect()),
        Comp::Handle {
            body,
            return_var,
            return_body,
            ops,
        } => Node::Handle(Rc::new(HandleInfo {
            body: lower(body),
            ops: ops
                .iter()
                .map(|op| (op.name, (op.params.clone(), op.resume, lower(&op.body))))
                .collect(),
            return_var: *return_var,
            return_body: return_body.as_deref().map(lower),
        })),
        Comp::Mask(ops, b) => Node::Mask(Rc::from(ops.as_slice()), lower(b)),
        Comp::StrBuiltin(n, args) => Node::StrBuiltin(*n, args.iter().map(atom_of).collect()),
        // The interpreter runs un-lowered core; Dup/Drop/ReuseToken/Reuse are
        // injected only by codegen-side RC lowering and must never reach here.
        // Masking them to a silent sink would hide the invariant breaking.
        Comp::Dup(_) | Comp::Drop(_) | Comp::ReuseToken(_) | Comp::Reuse(..) => {
            unreachable!("RC reuse node reached the interpreter; it runs un-lowered core")
        }
    }
}

fn atom_of(v: &Value) -> Atom {
    match v {
        Value::Var(x) => Atom::Var(*x),
        Value::Int(n) => Atom::Int(*n),
        Value::I64(n) => Atom::I64(*n),
        Value::U64(n) => Atom::U64(*n),
        Value::Float(f) => Atom::Float(*f),
        Value::Bool(b) => Atom::Bool(*b),
        Value::Unit => Atom::Unit,
        Value::Str(s) => Atom::Str(s.clone()),
        Value::Thunk(c) => Atom::Thunk(lower(c)),
        Value::Ctor(n, _, vs) => Atom::Ctor(*n, vs.iter().map(atom_of).collect()),
        Value::Tuple(vs) => Atom::Tuple(vs.iter().map(atom_of).collect()),
    }
}

impl Rv {
    /// Runtime shape tag. `print`/`show` dispatch on this, so the test corpus
    /// must exercise a direct `print` of each printable kind (see the
    /// `print_kind_coverage` oracle) or a backend mishandling of one shape can
    /// hide behind cases that only ever print strings.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Int(_) => "Int",
            Self::I64(_) => "I64",
            Self::U64(_) => "U64",
            Self::Float(_) => "Float",
            Self::Bool(_) => "Bool",
            Self::Unit => "Unit",
            Self::Str(_) => "Str",
            Self::Big(_) => "Big",
            Self::Closure(..) => "Closure",
            Self::Thunk(..) => "Thunk",
            Self::Data(..) => "Data",
            Self::Tuple(_) => "Tuple",
            Self::Resume(_) => "Resume",
        }
    }

    pub fn show(&self) -> String {
        match self {
            Self::Int(n) | Self::I64(n) => n.to_string(),
            Self::U64(n) => n.to_string(),
            Self::Float(f) => fmt_g(*f),
            Self::Bool(b) => b.to_string(),
            Self::Unit => "()".into(),
            Self::Str(s) => s.clone(),
            Self::Big(n) => n.to_string(),
            Self::Closure(..) | Self::Thunk(..) => "<function>".into(),
            Self::Resume(..) => "<continuation>".into(),
            Self::Data(name, fs) => match self.list_elems() {
                Some(es) => {
                    let es: Vec<_> = es.iter().map(|e| e.show()).collect();
                    format!("[{}]", es.join(", "))
                }
                None if fs.is_empty() => name.to_string(),
                None => {
                    let fs: Vec<_> = fs.iter().map(Self::show).collect();
                    format!("{name}({})", fs.join(", "))
                }
            },
            Self::Tuple(fs) => {
                let fs: Vec<_> = fs.iter().map(Self::show).collect();
                format!("({})", fs.join(", "))
            }
        }
    }

    // Like `show`, but renders a value as it would be written as a literal:
    // strings quoted and escaped, including strings nested in lists, tuples, and
    // constructors. Used for result display (the REPL), where a bare `foo` is
    // ambiguous with an identifier; `print` keeps using `show` for raw output so
    // the backends stay byte-identical.
    pub fn repr(&self) -> String {
        match self {
            Self::Str(s) => format!("{s:?}"),
            Self::Data(name, fs) => match self.list_elems() {
                Some(es) => {
                    let es: Vec<_> = es.iter().map(|e| e.repr()).collect();
                    format!("[{}]", es.join(", "))
                }
                None if fs.is_empty() => name.to_string(),
                None => {
                    let fs: Vec<_> = fs.iter().map(Self::repr).collect();
                    format!("{name}({})", fs.join(", "))
                }
            },
            Self::Tuple(fs) => {
                let fs: Vec<_> = fs.iter().map(Self::repr).collect();
                format!("({})", fs.join(", "))
            }
            _ => self.show(),
        }
    }

    fn list_elems(&self) -> Option<Vec<&Self>> {
        let mut es = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Self::Data(n, fs) if n == NIL && fs.is_empty() => return Some(es),
                Self::Data(n, fs) if n == CONS && fs.len() == 2 => {
                    es.push(&fs[0]);
                    cur = &fs[1];
                }
                _ => return None,
            }
        }
    }
}

// Output and input are host-supplied so the interpreter never touches real stdio
// itself: as the differential oracle and the wasm engine it must capture the
// transcript, while the native CLI streams to a real terminal. `out_sink`
// receives `print`/`println` bytes; `input` feeds `read_int`/`read_line`.
pub struct Machine<'a> {
    fns: BTreeMap<Sym, (Rc<[Sym]>, Cmp)>,
    pub out: Vec<Rv>,
    pub term: String,
    rng: u64,
    fn_name: Sym,
    out_sink: &'a mut dyn io::Write,
    input: &'a mut dyn io::BufRead,
    // Set by `exit(n)`: evaluation unwinds and the host maps it to a process
    // exit (CLI) or a returned status (REPL/wasm), never a `process::exit` here.
    exit: Option<i32>,
}

// The borrowed `dyn Write`/`dyn BufRead` handles are not `Debug`; show only the
// captured transcript state, which is what a dump wants anyway.
impl std::fmt::Debug for Machine<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Machine")
            .field("out", &self.out)
            .field("term", &self.term)
            .field("exit", &self.exit)
            .finish_non_exhaustive()
    }
}

#[derive(Debug)]
pub struct Run {
    pub value: Rv,
    pub out: Vec<Rv>,
    pub term: String,
    // `Some(code)` when the program called `exit(code)`; the host decides what
    // a process exit means in its context.
    pub exit: Option<i32>,
}

// SplitMix64 default seed, shared with the C runtime so the interpreter and
// native backends produce identical streams from an unseeded `rand`.
const DEFAULT_SEED: u64 = 0x9E37_79B9_7F4A_7C15;

const fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

impl<'a> Machine<'a> {
    #[must_use]
    pub fn new(
        globals: &BTreeMap<Sym, CoreFn>,
        out_sink: &'a mut dyn io::Write,
        input: &'a mut dyn io::BufRead,
    ) -> Self {
        Self {
            fns: globals
                .iter()
                .map(|(k, f)| (*k, (Rc::from(f.params.as_slice()), lower(&f.body))))
                .collect(),
            out: Vec::new(),
            term: String::new(),
            rng: DEFAULT_SEED,
            fn_name: ENTRY_POINT.into(),
            out_sink,
            input,
            exit: None,
        }
    }

    /// # Errors
    /// Fails with a runtime error message.
    pub fn eval(&mut self, c: &Comp) -> Result<Rv, String> {
        self.comp(&Env::default(), c)
    }

    /// # Errors
    /// Fails with a runtime error message.
    pub fn comp(&mut self, env: &Env, c: &Comp) -> Result<Rv, String> {
        self.exec(lower(c), env.clone())
    }

    fn exec(&mut self, root: Cmp, env: Env) -> Result<Rv, String> {
        let mut stack: Vec<Frame> = Vec::new();
        let mut state = State::Eval(root, env);
        loop {
            // `exit` short-circuits the whole program: stop unwinding and hand
            // the last value back so the host can act on `self.exit`.
            if self.exit.is_some() {
                if let State::Ret(v) = state {
                    return Ok(v);
                }
            }
            state = match state {
                State::Eval(c, env) => self.step(&mut stack, &c, env)?,
                State::Ret(v) => match stack.pop() {
                    None => return Ok(v),
                    Some(frame) => self.cont(&mut stack, frame, v)?,
                },
            };
        }
    }

    fn step(&mut self, stack: &mut Vec<Frame>, c: &Node, env: Env) -> Result<State, String> {
        Ok(match c {
            Node::Return(a) => State::Ret(atom(&env, a)?),
            Node::Bind(m, x, n) => {
                stack.push(Frame::Bind(*x, Rc::clone(n), env.clone()));
                State::Eval(Rc::clone(m), env)
            }
            Node::Force(a) => match atom(&env, a)? {
                Rv::Thunk(c, e) => State::Eval(c, e),
                other => State::Ret(other),
            },
            Node::Lam(ps, body) => State::Ret(Rv::Closure(Rc::clone(ps), Rc::clone(body), env)),
            Node::App(m, args) => {
                stack.push(Frame::Args(Rc::clone(args), env.clone()));
                State::Eval(Rc::clone(m), env)
            }
            Node::If(a, t, e) => match atom(&env, a)? {
                Rv::Bool(true) => State::Eval(Rc::clone(t), env),
                Rv::Bool(false) => State::Eval(Rc::clone(e), env),
                _ => return Err("if on non-boolean".into()),
            },
            Node::Prim(op, a, b) => State::Ret(prim(*op, &atom(&env, a)?, &atom(&env, b)?)?),
            Node::Call(name, args) => {
                let (params, body) = self
                    .fns
                    .get(name)
                    .ok_or_else(|| format!("unknown function {name}"))?;
                let avs = atoms(&env, args)?;
                if avs.len() < params.len() {
                    let mut cenv = BTreeMap::new();
                    for (p, a) in params.iter().zip(&avs) {
                        cenv.insert(*p, a.clone());
                    }
                    State::Ret(Rv::Closure(
                        Rc::from(&params[avs.len()..]),
                        Rc::clone(body),
                        Rc::new(cenv),
                    ))
                } else {
                    let mut e2 = BTreeMap::new();
                    for (p, a) in params.iter().zip(avs) {
                        e2.insert(*p, a);
                    }
                    let body = Rc::clone(body);
                    let prev = mem::replace(&mut self.fn_name, *name);
                    // A Restore already on top means we are in tail position:
                    // collapsing keeps tail calls O(1) space.
                    if !matches!(stack.last(), Some(Frame::Restore(_))) {
                        stack.push(Frame::Restore(prev));
                    }
                    State::Eval(body, Rc::new(e2))
                }
            }
            Node::Print(a) => {
                let rv = atom(&env, a)?;
                let s = rv.show();
                self.out.push(rv);
                write!(self.out_sink, "{s}").map_err(|e| format!("print: {e}"))?;
                self.out_sink.flush().ok();
                self.term.push_str(&s);
                State::Ret(Rv::Unit)
            }
            Node::PrintNl => {
                writeln!(self.out_sink).map_err(|e| format!("println: {e}"))?;
                self.out_sink.flush().ok();
                self.term.push('\n');
                State::Ret(Rv::Unit)
            }
            Node::Rand => State::Ret(Rv::Int((splitmix64(&mut self.rng) >> 2).cast_signed())),
            Node::Srand(a) => {
                self.rng = match atom(&env, a)? {
                    Rv::Int(n) => n.cast_unsigned(),
                    _ => return Err("srand: expected Int".into()),
                };
                State::Ret(Rv::Unit)
            }
            Node::ReadInt => {
                let mut line = String::new();
                self.input
                    .read_line(&mut line)
                    .map_err(|e| format!("read_int: {e}"))?;
                let n = line
                    .trim()
                    .parse::<i64>()
                    .map_err(|e| format!("read_int: {e}"))?;
                State::Ret(Rv::Int(n))
            }
            Node::ReadLine => {
                let mut line = String::new();
                self.input
                    .read_line(&mut line)
                    .map_err(|e| format!("read_line: {e}"))?;
                let s = line.strip_suffix('\n').unwrap_or(&line);
                State::Ret(Rv::Str(s.strip_suffix('\r').unwrap_or(s).into()))
            }
            Node::Error(a) => {
                return Err(match atom(&env, a)? {
                    Rv::Str(s) => s,
                    Rv::Int(n) => format!("error({n})"),
                    _ => "error(1)".into(),
                })
            }
            Node::Case(a, arms) => {
                let scrut = atom(&env, a)?;
                for (pat, body) in arms {
                    if let Some(binds) = match_pat(pat, &scrut) {
                        if binds.is_empty() {
                            return Ok(State::Eval(Rc::clone(body), env));
                        }
                        let mut env2 = env;
                        Rc::make_mut(&mut env2).extend(binds);
                        return Ok(State::Eval(Rc::clone(body), env2));
                    }
                }
                return Err(format!("no matching pattern in `{}`", self.fn_name));
            }
            Node::FloatBuiltin(name, a) => State::Ret(float_builtin(*name, atom(&env, a)?)?),
            Node::StrBuiltin(name, args) => {
                let vals = atoms(&env, args)?;
                // `exit(n)` is a host action, not a value: record the code and
                // let the exec loop unwind rather than killing the process here.
                #[allow(clippy::cast_possible_truncation)]
                if let (Builtin::Exit, [Rv::Int(n)]) = (*name, vals.as_slice()) {
                    self.exit = Some(*n as i32);
                    State::Ret(Rv::Unit)
                } else {
                    State::Ret(str_builtin(*name, &vals)?)
                }
            }
            Node::Do(op, args) => {
                let avs = atoms(&env, args)?;
                self.perform(stack, *op, avs)?
            }
            Node::Handle(hi) => {
                stack.push(Frame::Handle(Rc::clone(hi), env.clone()));
                State::Eval(Rc::clone(&hi.body), env)
            }
            Node::Mask(ops, body) => {
                stack.push(Frame::Mask(Rc::clone(ops)));
                State::Eval(Rc::clone(body), env)
            }
        })
    }

    fn cont(&mut self, stack: &mut Vec<Frame>, frame: Frame, v: Rv) -> Result<State, String> {
        Ok(match frame {
            Frame::Bind(x, n, mut env) => {
                Rc::make_mut(&mut env).insert(x, v);
                State::Eval(n, env)
            }
            Frame::Restore(name) => {
                self.fn_name = name;
                State::Ret(v)
            }
            Frame::Args(args, env) => {
                let avs = atoms(&env, &args)?;
                match v {
                    Rv::Closure(ps, body, mut cenv) => {
                        let e = Rc::make_mut(&mut cenv);
                        if avs.len() < ps.len() {
                            for (p, a) in ps.iter().zip(&avs) {
                                e.insert(*p, a.clone());
                            }
                            State::Ret(Rv::Closure(Rc::from(&ps[avs.len()..]), body, cenv))
                        } else {
                            for (p, a) in ps.iter().zip(avs) {
                                e.insert(*p, a);
                            }
                            State::Eval(body, cenv)
                        }
                    }
                    Rv::Resume(frames) => {
                        let arg = avs
                            .into_iter()
                            .next()
                            .ok_or_else(|| "resume requires an argument".to_string())?;
                        stack.extend(frames.iter().cloned());
                        State::Ret(arg)
                    }
                    _ => return Err(format!("applied a non-function in `{}`", self.fn_name)),
                }
            }
            Frame::Mask(_) => State::Ret(v),
            Frame::Handle(hi, env) => match (&hi.return_var, &hi.return_body) {
                (Some(rv), Some(rb)) => {
                    let mut env2 = env;
                    Rc::make_mut(&mut env2).insert(*rv, v);
                    State::Eval(Rc::clone(rb), env2)
                }
                _ => State::Ret(v),
            },
        })
    }

    fn perform(&mut self, stack: &mut Vec<Frame>, op: Sym, args: Vec<Rv>) -> Result<State, String> {
        let mut captured = Vec::new();
        // Each mask frame for this op's effect crossed on the way out makes
        // the walk skip one more matching handler (Koka-style mask).
        let mut skip = 0usize;
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Restore(name) => self.fn_name = name,
                // The recursive evaluator propagated performs past a pending
                // application without capturing it. Keep that behavior.
                Frame::Args(..) => {}
                Frame::Mask(ops) => {
                    if ops.contains(&op) {
                        skip += 1;
                    }
                    captured.push(Frame::Mask(ops));
                }
                Frame::Handle(hi, henv) if hi.ops.contains_key(&op) && skip > 0 => {
                    skip -= 1;
                    captured.push(Frame::Handle(hi, henv));
                }
                Frame::Handle(hi, henv) if hi.ops.contains_key(&op) => {
                    let (params, resume_var, body) = &hi.ops[&op];
                    let body = Rc::clone(body);
                    let mut env2 = henv.clone();
                    captured.push(Frame::Handle(Rc::clone(&hi), henv));
                    captured.reverse();
                    let e = Rc::make_mut(&mut env2);
                    for (p, a) in params.iter().zip(args) {
                        e.insert(*p, a);
                    }
                    e.insert(*resume_var, Rv::Resume(Rc::from(captured)));
                    return Ok(State::Eval(body, env2));
                }
                other => captured.push(other),
            }
        }
        Err(format!("unhandled effect `{op}`"))
    }
}

/// Mirrors `prism_big_of_str` in the C runtime: ASCII-trim, optional sign, then
/// a strict all-digit decimal parse. Anything else is None.
fn big_of_str(s: &str) -> Option<BigInt> {
    let t = s.trim_matches(|c: char| c.is_ascii_whitespace());
    let digits = t.strip_prefix(['+', '-']).unwrap_or(t);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    t.parse().ok()
}

/// Builds the `Result(Unit, String)` ADT value the file builtins return,
/// matching the `Ok`/`Err` cells the native runtime constructs.
fn file_result(r: std::io::Result<()>) -> Rv {
    match r {
        Ok(()) => Rv::Data("Ok".into(), vec![Rv::Unit].into()),
        Err(e) => Rv::Data("Err".into(), vec![Rv::Str(e.to_string())].into()),
    }
}

fn atom(env: &Env, a: &Atom) -> Result<Rv, String> {
    match a {
        Atom::Var(x) => env
            .get(x)
            .cloned()
            .ok_or_else(|| format!("unbound {x} at runtime")),
        Atom::Int(n) => Ok(Rv::Int(*n)),
        Atom::I64(n) => Ok(Rv::I64(*n)),
        Atom::U64(n) => Ok(Rv::U64(*n)),
        Atom::Float(f) => Ok(Rv::Float(*f)),
        Atom::Bool(b) => Ok(Rv::Bool(*b)),
        Atom::Unit => Ok(Rv::Unit),
        Atom::Str(s) => Ok(Rv::Str(s.clone())),
        Atom::Thunk(c) => Ok(Rv::Thunk(Rc::clone(c), env.clone())),
        Atom::Ctor(name, vs) => Ok(Rv::Data(*name, atoms(env, vs)?.into())),
        Atom::Tuple(vs) => Ok(Rv::Tuple(atoms(env, vs)?.into())),
    }
}

fn atoms(env: &Env, args: &[Atom]) -> Result<Vec<Rv>, String> {
    args.iter().map(|a| atom(env, a)).collect()
}

// Truncating/widening conversions are the language semantics of these builtins.
#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
fn float_builtin(op: FloatOp, rv: Rv) -> Result<Rv, String> {
    use FloatOp as F;
    match (op, rv) {
        (F::ToFloat, Rv::Int(n)) => Ok(Rv::Float(n as f64)),
        (F::Truncate, Rv::Float(f)) => Ok(Rv::Int(f as i64)),
        (F::FloorToInt, Rv::Float(f)) => Ok(Rv::Int(f.floor() as i64)),
        (F::CeilToInt, Rv::Float(f)) => Ok(Rv::Int(f.ceil() as i64)),
        (F::AbsFloat, Rv::Float(f)) => Ok(Rv::Float(f.abs())),
        (F::Sqrt, Rv::Float(f)) => Ok(Rv::Float(f.sqrt())),
        (F::Sin, Rv::Float(f)) => Ok(Rv::Float(f.sin())),
        (F::Cos, Rv::Float(f)) => Ok(Rv::Float(f.cos())),
        (F::Exp, Rv::Float(f)) => Ok(Rv::Float(f.exp())),
        (F::Ln, Rv::Float(f)) => Ok(Rv::Float(f.ln())),
        (o, _) => Err(format!("float builtin {}: wrong argument type", o.name())),
    }
}

fn str_builtin(b: Builtin, vals: &[Rv]) -> Result<Rv, String> {
    use Builtin as B;
    match (b, vals) {
        (B::Concat, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Str(format!("{a}{b}"))),
        (B::StrLen, [Rv::Str(s)]) => Ok(Rv::Int(i64::try_from(s.chars().count()).unwrap_or(0))),
        (B::StrEq, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Bool(a == b)),
        (B::StrCmp, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Int(match a.cmp(b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        })),
        (B::ShowInt, [Rv::Int(n)]) | (B::ShowI64, [Rv::I64(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ShowInt, [Rv::Big(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ShowBool, [Rv::Bool(b)]) => Ok(Rv::Str(b.to_string())),
        (B::ShowFloat, [Rv::Float(f)]) => Ok(Rv::Str(fmt_g(*f))),
        (B::ShowFloatPrec, [Rv::Float(f), Rv::Int(d)]) => {
            // The runtime writes `%.*f` into a 64-byte buffer, so it can only
            // return the first 63 (ASCII) chars; mirror that cap to stay byte
            // identical with the backend.
            let mut s = format!("{f:.*}", usize::try_from(*d).unwrap_or(0));
            s.truncate(63);
            Ok(Rv::Str(s))
        }
        (B::PowFloat, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(a.powf(*b))),
        (B::ParseFloat, [Rv::Str(s)]) => Ok(Rv::Float(s.trim().parse::<f64>().unwrap_or(0.0))),
        (B::Substring, [Rv::Str(s), Rv::Int(start), Rv::Int(len)]) => {
            let st = usize::try_from(*start).unwrap_or(0);
            let take = usize::try_from(*len).unwrap_or(0);
            Ok(Rv::Str(s.chars().skip(st).take(take).collect()))
        }
        (B::CharAt, [Rv::Str(s), Rv::Int(i)]) => {
            Ok(Rv::Int(usize::try_from(*i).map_or(-1, |idx| {
                s.chars().nth(idx).map_or(-1, |c| i64::from(c as u32))
            })))
        }
        (B::ShowChar, [Rv::Int(cp)]) => Ok(Rv::Str(
            u32::try_from(*cp)
                .ok()
                .and_then(char::from_u32)
                .map(|c| c.to_string())
                .unwrap_or_default(),
        )),
        (B::ParseInt, [Rv::Str(s)]) => Ok(big_of_str(s).map_or_else(
            || Rv::Data("None".into(), Vec::new().into()),
            |n| Rv::Data("Some".into(), vec![norm(n)].into()),
        )),
        // Elaborator-only: decimal text of a valid big literal to its `Integer`.
        (B::BigLit, [Rv::Str(s)]) => Ok(norm(s.parse().unwrap_or(BigInt::ZERO))),
        (B::Getenv, [Rv::Str(s)]) => Ok(Rv::Str(env::var(s).unwrap_or_default())),
        (B::ReadFile, [Rv::Str(p)]) => match fs::read_to_string(p) {
            Ok(s) => Ok(Rv::Str(s)),
            Err(e) => Err(format!("read_file: {e}: {p}")),
        },
        (B::WriteFile, [Rv::Str(p), Rv::Str(c)]) => Ok(file_result(fs::write(p, c))),
        (B::FileExists, [Rv::Str(p)]) => Ok(Rv::Bool(std::path::Path::new(p).exists())),
        (B::AppendFile, [Rv::Str(p), Rv::Str(c)]) => {
            let r = fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(p)
                .and_then(|mut f| f.write_all(c.as_bytes()));
            Ok(file_result(r))
        }
        (B::RemoveFile, [Rv::Str(p)]) => {
            let _ = fs::remove_file(p);
            Ok(Rv::Unit)
        }
        // `exit` is intercepted in `step` (it sets the machine's exit status
        // and unwinds), so it never reaches the value-returning builtin path.
        (B::Exit, _) => Err("exit: unexpected argument".into()),
        (B::ArgsCount, []) => Ok(Rv::Int(i64::try_from(env::args().count()).unwrap_or(0))),
        (B::Arg, [Rv::Int(i)]) => Ok(Rv::Str(
            usize::try_from(*i)
                .ok()
                .and_then(|k| env::args().nth(k))
                .unwrap_or_default(),
        )),
        (B::I64Add, [a, b]) => fixed2(a, b, u64::wrapping_add),
        (B::I64Sub, [a, b]) => fixed2(a, b, u64::wrapping_sub),
        (B::I64Mul, [a, b]) => fixed2(a, b, u64::wrapping_mul),
        (B::I64Div | B::I64Rem, [_, Rv::I64(0)]) | (B::U64Div | B::U64Rem, [_, Rv::U64(0)]) => {
            Err("division by zero".into())
        }
        (B::I64Div, [Rv::I64(x), Rv::I64(y)]) => Ok(Rv::I64(x.wrapping_div(*y))),
        (B::I64Rem, [Rv::I64(x), Rv::I64(y)]) => Ok(Rv::I64(x.wrapping_rem(*y))),
        (B::U64Div, [Rv::U64(x), Rv::U64(y)]) => Ok(Rv::U64(x / y)),
        (B::U64Rem, [Rv::U64(x), Rv::U64(y)]) => Ok(Rv::U64(x % y)),
        (B::I64Cmp, [Rv::I64(x), Rv::I64(y)]) => Ok(ord(x.cmp(y))),
        (B::U64Cmp, [Rv::U64(x), Rv::U64(y)]) => Ok(ord(x.cmp(y))),
        (B::ShowU64, [Rv::U64(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ToI64, [v]) => Ok(Rv::I64(low64(v)?.cast_signed())),
        (B::ToU64, [v]) => Ok(Rv::U64(low64(v)?)),
        (B::IntOfI64, [Rv::I64(n)]) => Ok(Rv::Int(*n)),
        (B::IntOfU64, [Rv::U64(n)]) => {
            Ok(i64::try_from(*n).map_or_else(|_| Rv::Big(BigInt::from(*n)), Rv::Int))
        }
        // The native kernel keys off `kind`. The interpreter compares the runtime
        // values directly, which gives the same stable order for every element
        // type the elaborator specializes.
        (B::SortPrim, [_kind, list]) => {
            let Some(elems) = list.list_elems() else {
                return Err("sort_prim: not a list".into());
            };
            let mut v: Vec<Rv> = elems.into_iter().cloned().collect();
            v.sort_by(rv_key_cmp);
            let mut acc = Rv::Data(NIL.into(), Vec::new().into());
            for e in v.into_iter().rev() {
                acc = Rv::Data(CONS.into(), vec![e, acc].into());
            }
            Ok(acc)
        }
        (op, _) => Err(format!("str builtin {}: wrong args", op.name())),
    }
}

// Total order on the primitive element types the sort kernel specializes,
// matching each canonical `Ord` instance: floats by IEEE total order (the same
// bit order the native radix uses), fixed-width ints by their signedness, and
// Integer (and Char-as-codepoint) by numeric value.
fn rv_key_cmp(a: &Rv, b: &Rv) -> Ordering {
    match (a, b) {
        (Rv::Float(x), Rv::Float(y)) => x.total_cmp(y),
        (Rv::I64(x), Rv::I64(y)) => x.cmp(y),
        (Rv::U64(x), Rv::U64(y)) => x.cmp(y),
        (Rv::Bool(x), Rv::Bool(y)) => x.cmp(y),
        _ => to_big(a)
            .zip(to_big(b))
            .map_or(Ordering::Equal, |(x, y)| x.cmp(&y)),
    }
}

// Render a float byte-for-byte like the native runtime's `printf("%g", d)` so
// the interpreter (the differential oracle) and the backend agree. C `%g` with
// the default 6 significant digits: branch fixed vs scientific on the rounded
// decimal exponent, strip trailing zeros, pad the exponent to two digits.
fn fmt_g(d: f64) -> String {
    const P: i32 = 6;
    if d.is_nan() {
        return "nan".to_string();
    }
    if d.is_infinite() {
        return if d < 0.0 { "-inf" } else { "inf" }.to_string();
    }
    // Rust's fixed-precision formatting is correctly rounded (round half to even)
    // like the printf family, so the exponent it produces is the one `%g` branches
    // on, including a carry that bumps the exponent (9.999996e5 -> 1e6).
    let sci = format!("{:.*e}", (P - 1) as usize, d);
    let (mantissa, exp) = sci.split_once('e').unwrap_or((sci.as_str(), "0"));
    let e: i32 = exp.parse().unwrap_or(0);
    if (-4..P).contains(&e) {
        let prec = usize::try_from(P - 1 - e).unwrap_or(0);
        strip_zeros(format!("{d:.prec$}"))
    } else {
        let m = strip_zeros(mantissa.to_string());
        let sign = if e < 0 { '-' } else { '+' };
        format!("{m}e{sign}{:02}", e.abs())
    }
}

fn strip_zeros(s: String) -> String {
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        s
    }
}

// IEEE 754 value equality is the intended semantics of Eqf/Nef (NaN never
// equal, +0.0 == -0.0), matching the backend's `fcmp oeq`/`une`. This is not
// bit equality.
#[allow(clippy::float_cmp)]
fn dispatch_float_op(op: CoreOp, x: f64, y: f64) -> Result<Rv, String> {
    Ok(match op {
        CoreOp::Addf => Rv::Float(x + y),
        CoreOp::Subf => Rv::Float(x - y),
        CoreOp::Mulf => Rv::Float(x * y),
        CoreOp::Divf => Rv::Float(x / y),
        CoreOp::Eqf => Rv::Bool(x == y),
        CoreOp::Nef => Rv::Bool(x != y),
        CoreOp::Ltf => Rv::Bool(x < y),
        CoreOp::Lef => Rv::Bool(x <= y),
        CoreOp::Gtf => Rv::Bool(x > y),
        CoreOp::Gef => Rv::Bool(x >= y),
        _ => return Err(format!("op {op:?} not defined for Float")),
    })
}

// i64 fast path: arithmetic that overflows i64 promotes to a normalized Big.
fn dispatch_int_op(op: CoreOp, x: i64, y: i64) -> Result<Rv, String> {
    if matches!(op, CoreOp::Div | CoreOp::Rem) && y == 0 {
        return Err("division by zero".into());
    }
    let wide = |r: Option<i64>, f: fn(BigInt, BigInt) -> BigInt| {
        r.map_or_else(|| norm(f(BigInt::from(x), BigInt::from(y))), Rv::Int)
    };
    Ok(match op {
        CoreOp::Add => wide(x.checked_add(y), |a, b| a + b),
        CoreOp::Sub => wide(x.checked_sub(y), |a, b| a - b),
        CoreOp::Mul => wide(x.checked_mul(y), |a, b| a * b),
        CoreOp::Div => wide(x.checked_div(y), |a, b| a / b),
        CoreOp::Rem => Rv::Int(x.wrapping_rem(y)),
        CoreOp::Eq => Rv::Bool(x == y),
        CoreOp::Ne => Rv::Bool(x != y),
        CoreOp::Lt => Rv::Bool(x < y),
        CoreOp::Le => Rv::Bool(x <= y),
        CoreOp::Gt => Rv::Bool(x > y),
        CoreOp::Ge => Rv::Bool(x >= y),
        _ => return Err(format!("op {op:?} not defined for Int")),
    })
}

fn dispatch_bigint_op(op: CoreOp, x: BigInt, y: BigInt) -> Result<Rv, String> {
    if matches!(op, CoreOp::Div | CoreOp::Rem) && y.sign() == Sign::NoSign {
        return Err("division by zero".into());
    }
    Ok(match op {
        CoreOp::Add => norm(x + y),
        CoreOp::Sub => norm(x - y),
        CoreOp::Mul => norm(x * y),
        CoreOp::Div => norm(x / y),
        CoreOp::Rem => norm(x % y),
        CoreOp::Eq => Rv::Bool(x == y),
        CoreOp::Ne => Rv::Bool(x != y),
        CoreOp::Lt => Rv::Bool(x < y),
        CoreOp::Le => Rv::Bool(x <= y),
        CoreOp::Gt => Rv::Bool(x > y),
        CoreOp::Ge => Rv::Bool(x >= y),
        _ => return Err(format!("op {op:?} not defined for Int")),
    })
}

fn prim(op: CoreOp, a: &Rv, b: &Rv) -> Result<Rv, String> {
    if let (Rv::Float(x), Rv::Float(y)) = (a, b) {
        return dispatch_float_op(op, *x, *y);
    }
    if let (Rv::Int(x), Rv::Int(y)) = (a, b) {
        return dispatch_int_op(op, *x, *y);
    }
    let (Some(x), Some(y)) = (to_big(a), to_big(b)) else {
        return Err("arithmetic on non-numeric value".into());
    };
    dispatch_bigint_op(op, x, y)
}

fn norm(n: BigInt) -> Rv {
    i64::try_from(&n).map_or_else(|_| Rv::Big(n), Rv::Int)
}

fn to_big(v: &Rv) -> Option<BigInt> {
    match v {
        Rv::Int(n) => Some(BigInt::from(*n)),
        Rv::Big(n) => Some(n.clone()),
        _ => None,
    }
}

fn low64(v: &Rv) -> Result<u64, String> {
    match v {
        Rv::Int(n) => Ok(n.cast_unsigned()),
        Rv::Big(n) => {
            let lo = n.iter_u64_digits().next().unwrap_or(0);
            Ok(if n.sign() == Sign::Minus {
                lo.wrapping_neg()
            } else {
                lo
            })
        }
        _ => Err("to_i64/to_u64: wrong args".into()),
    }
}

fn fixed2(a: &Rv, b: &Rv, f: fn(u64, u64) -> u64) -> Result<Rv, String> {
    match (a, b) {
        (Rv::I64(x), Rv::I64(y)) => Ok(Rv::I64(
            f(x.cast_unsigned(), y.cast_unsigned()).cast_signed(),
        )),
        (Rv::U64(x), Rv::U64(y)) => Ok(Rv::U64(f(*x, *y))),
        _ => Err("fixed-width op: wrong args".into()),
    }
}

const fn ord(o: Ordering) -> Rv {
    Rv::Int(match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    })
}

// Core patterns are shallow after match compilation: a ctor or tuple test whose
// fields are plain binders, or a catch-all that binds the whole scrutinee.
fn match_pat(p: &CorePat, v: &Rv) -> Option<Vec<(Sym, Rv)>> {
    match (p, v) {
        (CorePat::Wild, _) => Some(vec![]),
        (CorePat::Var(x), _) => Some(vec![(*x, v.clone())]),
        (CorePat::Ctor(name, fields), Rv::Data(dname, vals))
            if name == dname && fields.len() == vals.len() =>
        {
            Some(bind_fields(fields, vals))
        }
        (CorePat::Tuple(fields), Rv::Tuple(vals)) if fields.len() == vals.len() => {
            Some(bind_fields(fields, vals))
        }
        _ => None,
    }
}

// Bind each named field position to its value, ignoring wildcard positions.
fn bind_fields(fields: &[Option<Sym>], vals: &[Rv]) -> Vec<(Sym, Rv)> {
    fields
        .iter()
        .zip(vals.iter())
        .filter_map(|(b, val)| b.map(|s| (s, val.clone())))
        .collect()
}

#[must_use]
pub fn globals(core: &Core) -> BTreeMap<Sym, CoreFn> {
    core.fns.iter().map(|f| (f.name, f.clone())).collect()
}

/// Run `core` capturing all `print` output into the returned [`Run`]'s `term`
/// (the differential oracle and wasm path), reading input from an empty source.
/// Nothing reaches real stdio.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults.
pub fn run(core: &Core) -> Result<Run, String> {
    let mut sink: Vec<u8> = Vec::new();
    let mut input = io::Cursor::new(Vec::new());
    run_io(core, &mut sink, &mut input)
}

/// Run `core` with a host-supplied output sink and input source.
///
/// The native CLI passes real stdout/stdin here for live streaming; the oracle
/// passes in-memory buffers. `term` always carries the exact transcript
/// regardless of the sink.
///
/// # Errors
/// Fails when `main` is missing or evaluation faults.
pub fn run_io(
    core: &Core,
    out_sink: &mut dyn io::Write,
    input: &mut dyn io::BufRead,
) -> Result<Run, String> {
    let g = globals(core);
    let main = g.get(&Sym::new(ENTRY_POINT)).ok_or("no main function")?;
    let mut m = Machine::new(&g, out_sink, input);
    let value = m.comp(&Env::default(), &main.body)?;
    Ok(Run {
        value,
        out: m.out,
        term: m.term,
        exit: m.exit,
    })
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::{big_of_str, fmt_g, splitmix64, DEFAULT_SEED};

    // Reference column is the exact output of C `printf("%g", d)` (glibc/BSD).
    // The interpreter is the differential oracle, so its float rendering must
    // equal the backend's `%g` byte for byte.
    #[test]
    fn fmt_g_matches_c_printf() {
        let cases: &[(f64, &str)] = &[
            (0.0, "0"),
            (-0.0, "-0"),
            (1.0, "1"),
            (-1.0, "-1"),
            (1.0 / 3.0, "0.333333"),
            (-1.0 / 3.0, "-0.333333"),
            (0.1, "0.1"),
            (0.5, "0.5"),
            (1.5, "1.5"),
            (100_000_000.0, "1e+08"),
            (1_000_000.0, "1e+06"),
            (999_999.0, "999999"),
            (123_456.7, "123457"),
            (1_234_567.0, "1.23457e+06"),
            (9_999_999.0, "1e+07"),
            (0.000_000_1, "1e-07"),
            (0.0001, "0.0001"),
            (0.00001, "1e-05"),
            (1e12, "1e+12"),
            (1e-12, "1e-12"),
            (1.234_567_89, "1.23457"),
            (76.543_21, "76.5432"),
            (12_345.678, "12345.7"),
            (100.0, "100"),
            (0.000_123_456, "0.000123456"),
            (1e100, "1e+100"),
            (1e-100, "1e-100"),
            (123.456, "123.456"),
            (0.000_999_999_5, "0.001"),
            (9.999_996e5, "1e+06"),
        ];
        for &(d, want) in cases {
            assert_eq!(fmt_g(d), want, "fmt_g({d})");
        }
        assert_eq!(fmt_g(f64::NAN), "nan");
        assert_eq!(fmt_g(f64::INFINITY), "inf");
        assert_eq!(fmt_g(f64::NEG_INFINITY), "-inf");
    }

    fn runtime_src() -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime/prism_rt.c");
        std::fs::read_to_string(path).expect("read runtime/prism_rt.c")
    }

    // An unseeded `rand` must stream identical values on every backend, so the
    // interpreter's SplitMix64 and the C runtime's must be the same generator.
    // Like `layout_matches_runtime`: pin the interpreter's stream to a
    // hand-verified golden vector and assert the C source carries byte-identical
    // constants and structure, so drift in either implementation fails here
    // rather than only in the end-to-end corpus.
    #[test]
    fn splitmix64_matches_runtime() {
        assert_eq!(DEFAULT_SEED, 0x9E37_79B9_7F4A_7C15);
        let mut state = DEFAULT_SEED;
        let seq: Vec<u64> = (0..4).map(|_| splitmix64(&mut state)).collect();
        assert_eq!(
            seq,
            [
                0x6E78_9E6A_A1B9_65F4,
                0x06C4_5D18_8009_454F,
                0xF88B_B8A8_724C_81EC,
                0x1B39_896A_51A8_749B,
            ]
        );

        let rt = runtime_src();
        for needle in [
            "prism_rng = 0x9E3779B97F4A7C15UL",  // default seed
            "prism_rng += 0x9E3779B97F4A7C15UL", // increment
            "(z >> 30)) * 0xBF58476D1CE4E5B9UL", // mix 1
            "(z >> 27)) * 0x94D049BB133111EBUL", // mix 2
            "z ^= z >> 31",                      // final xor
            "(long)(z >> 2)",                    // rand() drops the low 2 bits
        ] {
            assert!(
                rt.contains(needle),
                "SplitMix64 drift: C runtime missing `{needle}`"
            );
        }
    }

    // Bignum decimal parsing must agree with the C runtime's `prism_big_of_str`
    // so a literal that overflows the immediate parses to the same value on every
    // backend. Pin the interpreter against golden values and assert the C source
    // still carries the same trim/sign/base-10 fold.
    #[test]
    fn big_of_str_matches_runtime() {
        use std::str::FromStr;

        let cases = [
            ("0", "0"),
            ("  42 ", "42"),
            (
                "-170141183460469231731687303715884105728",
                "-170141183460469231731687303715884105728",
            ),
            (
                "99999999999999999999999999999999",
                "99999999999999999999999999999999",
            ),
            ("+1000000000000000000000", "1000000000000000000000"),
        ];
        for (input, want) in cases {
            assert_eq!(
                big_of_str(input),
                Some(BigInt::from_str(want).unwrap()),
                "big_of_str({input:?})"
            );
        }
        assert_eq!(big_of_str("12x3"), None);
        assert_eq!(big_of_str(""), None);

        let rt = runtime_src();
        assert!(
            rt.contains("long prism_big_of_str(long s, int *ok)"),
            "C runtime missing prism_big_of_str"
        );
    }
}
