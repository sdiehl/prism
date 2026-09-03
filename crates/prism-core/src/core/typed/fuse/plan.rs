//! Join-plan construction, anti-unification, and residual emission.

use super::{
    as_var, binder_var, drive, free_comp_vars, names, next_fresh, normalize, peel, subst,
    union_effects, Arg, BTreeMap, CompSig, Consumer, CoreFnSig, Cx, Step, StreamExpr, Sym,
    TypedBinder, TypedComp, TypedCompKind, TypedCoreFn, TypedValue, TypedValueKind, FRESH_FUSE,
    SIZE_BUDGET, UNFOLD_BUDGET,
};

// --- join emission --------------------------------------------------------------

// One advancing stream position: the fresh variable abstracting it, its path
// into the pipeline tree, and its initial (seed) value.
pub(super) struct StreamParam {
    var: Sym,
    path: Vec<usize>,
    init: TypedValue,
}

// Anti-unify the seed pipeline against its one-step tail, allocate join
// parameters for the differing (advancing) positions and the changing
// accumulators, drive the pipeline symbolically, and residualize into one fresh
// top-level join function. Returns the redirected call, or `None` to not fuse.
pub(super) fn build_join(consumer: &Consumer, seed: &StreamExpr, cx: &mut Cx) -> Option<TypedComp> {
    // Abstract the scalar (non-closure) arguments to fresh variables, so the
    // producer's advance is driven symbolically (`x + 1`, not a folded
    // literal).
    let (sym_seed, init) = abstract_stream(seed, cx);
    let mut budget = UNFOLD_BUDGET;
    let step = drive(&sym_seed, consumer.ctors, cx, &mut budget)?;
    if step_size(&step) > SIZE_BUDGET {
        return None;
    }
    // The one-step tail (identical across every yielding/skipping leaf): the
    // knot.
    let tail = collect_tail(&step)?;
    // Classify each abstracted position: a differing one advances (a join
    // parameter), a coincident one is invariant (baked back to its seed value).
    let mut params: Vec<StreamParam> = Vec::new();
    let mut bakes: BTreeMap<Sym, TypedValue> = BTreeMap::new();
    classify(
        &sym_seed,
        &tail,
        &init,
        &mut Vec::new(),
        &mut params,
        &mut bakes,
    )?;
    let join = Sym::new(&names::fused_join(cx.joins));
    let stream_paths: Vec<Vec<usize>> = params.iter().map(|p| p.path.clone()).collect();
    let body0 = {
        let mut r = Res {
            consumer,
            join,
            stream_paths: &stream_paths,
            cx,
        };
        r.residual(&step)?
    };
    // Bake invariant abstracted positions to their seed values.
    let body = subst(&body0, &bakes, cx);
    // Join parameters: advancing stream positions first (deterministic
    // first-occurrence order), then the consumer's accumulators.
    let mut jparams: Vec<TypedBinder> = params
        .iter()
        .map(|p| TypedBinder::new(p.var, p.init.ty().clone()))
        .collect();
    jparams.extend(consumer.acc_params.iter().cloned());
    // Scope safety: the residual must close over nothing but the join
    // parameters. A leaked local (the most-specific-generalization scope trap)
    // aborts the seed.
    let jparam_names: Vec<Sym> = jparams.iter().map(TypedBinder::name).collect();
    if !join_is_closed(&body, &jparam_names) {
        return None;
    }
    let sig = CoreFnSig::new(
        Vec::new(),
        jparams.iter().map(|b| b.ty().clone()).collect(),
        consumer.call_sig.clone(),
    );
    cx.emitted
        .push(TypedCoreFn::new(join, jparams, body, sig, 0));
    cx.joins += 1;
    // The redirected initial call: seed values for the advancing positions,
    // then the accumulators' seed values.
    let mut initargs: Vec<TypedValue> = params.iter().map(|p| p.init.clone()).collect();
    initargs.extend(consumer.accs.iter().map(|a| a.seed.clone()));
    Some(TypedComp::new(
        consumer.call_sig.clone(),
        TypedCompKind::Call {
            callee: join,
            instantiation: Vec::new(),
            args: initargs,
        },
    ))
}

// Replace every scalar (non-thunk) value argument in the pipeline with a fresh
// variable, recording its seed value, in a fixed pre-order traversal (so
// parameter naming and order are byte-stable). Thunk arguments are left
// concrete so their applications inline during driving.
fn abstract_stream(s: &StreamExpr, cx: &mut Cx) -> (StreamExpr, BTreeMap<Sym, TypedValue>) {
    let mut init = BTreeMap::new();
    let out = abstract_go(s, &mut init, cx);
    (out, init)
}

fn abstract_go(s: &StreamExpr, init: &mut BTreeMap<Sym, TypedValue>, cx: &mut Cx) -> StreamExpr {
    let args = s
        .args
        .iter()
        .map(|a| match a {
            Arg::Val(v) if matches!(&peel(v).kind, TypedValueKind::Thunk(_)) => Arg::Val(v.clone()),
            Arg::Val(v) => {
                let f = next_fresh(&mut cx.fresh, FRESH_FUSE);
                init.insert(f, v.clone());
                Arg::Val(TypedValue::new(
                    v.ty().clone(),
                    TypedValueKind::Var {
                        name: f,
                        instantiation: Vec::new(),
                    },
                ))
            }
            Arg::Stream(inner) => Arg::Stream(Box::new(abstract_go(inner, init, cx))),
        })
        .collect();
    StreamExpr {
        comb: s.comb,
        instantiation: s.instantiation.clone(),
        args,
    }
}

// Walk the abstracted seed and its one-step tail in parallel, sorting each
// abstracted position into an advancing parameter or a baked invariant.
pub(super) fn classify(
    sym: &StreamExpr,
    tail: &StreamExpr,
    init: &BTreeMap<Sym, TypedValue>,
    path: &mut Vec<usize>,
    params: &mut Vec<StreamParam>,
    bakes: &mut BTreeMap<Sym, TypedValue>,
) -> Option<()> {
    if sym.comb != tail.comb || sym.args.len() != tail.args.len() {
        return None;
    }
    for (j, (sa, ta)) in sym.args.iter().zip(&tail.args).enumerate() {
        path.push(j);
        match (sa, ta) {
            (Arg::Val(sv), Arg::Val(tv)) => {
                if let Some(fv) = as_var(sv).filter(|fv| init.contains_key(fv)) {
                    // Invariant exactly when the tail threads the same variable
                    // through.
                    if as_var(tv) == Some(fv) {
                        bakes.insert(fv, init[&fv].clone());
                    } else {
                        params.push(StreamParam {
                            var: fv,
                            path: path.clone(),
                            init: init[&fv].clone(),
                        });
                    }
                } else if matches!(&peel(sv).kind, TypedValueKind::Thunk(_))
                    && matches!(&peel(tv).kind, TypedValueKind::Thunk(_))
                {
                    // A closure argument is threaded unchanged; alpha-renaming
                    // of its binder is irrelevant, so ignore it.
                } else if !value_eq(sv, tv) {
                    // A non-closure non-abstracted value must not change.
                    return None;
                }
            }
            (Arg::Stream(si), Arg::Stream(ti)) => classify(si, ti, init, path, params, bakes)?,
            _ => return None,
        }
        path.pop();
    }
    Some(())
}

// Collect the one-step tail shared by every yielding/skipping leaf; `None` if
// the leaves disagree (an unexpected non-uniform advance) or the pipeline never
// recurses.
fn collect_tail(step: &Step) -> Option<StreamExpr> {
    let mut tails = Vec::new();
    gather_tails(step, &mut tails);
    let first: StreamExpr = (*tails.first()?).clone();
    if tails.iter().all(|t| stream_eq(t, &first)) {
        Some(first)
    } else {
        None
    }
}

fn gather_tails<'a>(step: &'a Step, out: &mut Vec<&'a StreamExpr>) {
    match step {
        Step::Done => {}
        Step::Yield { next, .. } | Step::Skip { next } => out.push(next),
        Step::Branch { then, els, .. } => {
            gather_tails(then, out);
            gather_tails(els, out);
        }
        Step::Let { body, .. } => gather_tails(body, out),
    }
}

// The residualizer: turns a driven `Step` tree into the join function body,
// emitting the consumer's per-element action at each yield and a self-call at
// every leaf.
struct Res<'a> {
    consumer: &'a Consumer,
    join: Sym,
    stream_paths: &'a [Vec<usize>],
    cx: &'a mut Cx,
}

impl Res<'_> {
    fn residual(&mut self, step: &Step) -> Option<TypedComp> {
        match step {
            Step::Done => Some(subst(
                &self.consumer.done_body,
                &self.consumer.baked,
                self.cx,
            )),
            Step::Skip { next } => {
                let mut args = self.stream_rec_args(next)?;
                args.extend(self.consumer.acc_params.iter().map(binder_var));
                Some(self.join_call(args))
            }
            Step::Yield { head, next } => {
                let mut rec_args = self.stream_rec_args(next)?;
                rec_args.extend(self.consumer.accs.iter().map(|a| a.advance.clone()));
                let call = self.join_call(rec_args);
                let grafted = graft_return(&self.consumer.step_body, call)?;
                // Substitute the element and baked closures uniformly, then
                // inline the fold-function application the graft exposed.
                let mut sub = self.consumer.baked.clone();
                sub.insert(self.consumer.elem, head.clone());
                let done = subst(&grafted, &sub, self.cx);
                normalize(&done, self.cx)
            }
            Step::Branch { cond, then, els } => {
                let t = self.residual(then)?;
                let e = self.residual(els)?;
                let sig = CompSig::new(
                    t.sig().result().clone(),
                    union_effects(t.sig().effects(), e.sig().effects()),
                );
                Some(TypedComp::new(
                    sig,
                    TypedCompKind::If(cond.clone(), Box::new(t), Box::new(e)),
                ))
            }
            Step::Let { binder, comp, body } => {
                let b = self.residual(body)?;
                let sig = CompSig::new(
                    b.sig().result().clone(),
                    union_effects(comp.sig().effects(), b.sig().effects()),
                );
                Some(TypedComp::new(
                    sig,
                    TypedCompKind::Bind(comp.clone(), binder.clone(), Box::new(b)),
                ))
            }
        }
    }

    // The recursive join call, carrying the seed call-site sig (the join's
    // declared body signature, so the direct-call witness rule holds).
    fn join_call(&self, args: Vec<TypedValue>) -> TypedComp {
        TypedComp::new(
            self.consumer.call_sig.clone(),
            TypedCompKind::Call {
                callee: self.join,
                instantiation: Vec::new(),
                args,
            },
        )
    }

    // The advancing arguments for a recursive call: each stream parameter read
    // from the leaf's tail pipeline at its path.
    fn stream_rec_args(&self, next: &StreamExpr) -> Option<Vec<TypedValue>> {
        self.stream_paths
            .iter()
            .map(|p| read_at_path(next, p))
            .collect()
    }
}

// Replace the trailing `Return(Unit)` marker (the stripped self-call) with
// `repl`.
fn graft_return(body: &TypedComp, repl: TypedComp) -> Option<TypedComp> {
    match body.kind() {
        TypedCompKind::Return(value) if matches!(value.kind(), TypedValueKind::Unit) => Some(repl),
        TypedCompKind::Bind(first, binder, rest) => Some(TypedComp::new(
            body.sig().clone(),
            TypedCompKind::Bind(
                first.clone(),
                binder.clone(),
                Box::new(graft_return(rest, repl)?),
            ),
        )),
        _ => None,
    }
}

// Read the value at `path` (a sequence of argument indices descending through
// stream arguments, the last picking a value argument).
fn read_at_path(se: &StreamExpr, path: &[usize]) -> Option<TypedValue> {
    let (last, rest) = path.split_last()?;
    let mut cur = se;
    for &i in rest {
        match cur.args.get(i)? {
            Arg::Stream(inner) => cur = inner,
            Arg::Val(_) => return None,
        }
    }
    match cur.args.get(*last)? {
        Arg::Val(v) => Some(v.clone()),
        Arg::Stream(_) => None,
    }
}

fn step_size(step: &Step) -> usize {
    match step {
        Step::Done | Step::Yield { .. } | Step::Skip { .. } => 1,
        Step::Branch { then, els, .. } => 1 + step_size(then) + step_size(els),
        Step::Let { body, .. } => 1 + step_size(body),
    }
}

// Structural equality of two pipeline tails, ignoring closure (thunk)
// arguments: mappers/predicates/fold functions are threaded unchanged, so an
// alpha-rename of a baked closure's binder must not make two
// otherwise-identical tails disagree.
pub(super) fn stream_eq(a: &StreamExpr, b: &StreamExpr) -> bool {
    a.comb == b.comb
        && a.args.len() == b.args.len()
        && a.args.iter().zip(&b.args).all(|(x, y)| match (x, y) {
            (Arg::Stream(xi), Arg::Stream(yi)) => stream_eq(xi, yi),
            (Arg::Val(xv), Arg::Val(yv)) => {
                (matches!(&peel(xv).kind, TypedValueKind::Thunk(_))
                    && matches!(&peel(yv).kind, TypedValueKind::Thunk(_)))
                    || value_eq(xv, yv)
            }
            _ => false,
        })
}

// Value equality as the erased legacy pass computes it: floats by bit pattern
// (recursively through constructors and tuples), representation wrappers
// invisible, and everything else by erased structural equality.
fn value_eq(a: &TypedValue, b: &TypedValue) -> bool {
    match (&peel(a).kind, &peel(b).kind) {
        (TypedValueKind::Float(x), TypedValueKind::Float(y)) => x.to_bits() == y.to_bits(),
        (
            TypedValueKind::Ctor {
                name: xn,
                tag: xt,
                fields: xs,
                ..
            },
            TypedValueKind::Ctor {
                name: yn,
                tag: yt,
                fields: ys,
                ..
            },
        ) => {
            xn == yn
                && xt == yt
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| value_eq(x, y))
        }
        (TypedValueKind::Tuple(xs), TypedValueKind::Tuple(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| value_eq(x, y))
        }
        _ => a.clone().erase() == b.clone().erase(),
    }
}

// The scope-safety gate on an emitted join: its body may close over nothing but
// its own parameters (top-level names and literals are not free variables). A
// violation means the most-specific generalization proposed a hole under a
// binder introduced during driving, the classic scope trap.
pub(super) fn join_is_closed(body: &TypedComp, jparams: &[Sym]) -> bool {
    free_comp_vars(body).iter().all(|v| jparams.contains(v))
}
