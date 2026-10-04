//! Typed rewrite of off-tail resumptions into a threaded answer transformer.
//!
//! A clause that resumes off the tail (`op(x) resume k => let r = k(v) in
//! POST(r)`) is usually taken as the point where a continuation must become a
//! heap object: the resumption is needed as a value, so the handler cannot be
//! a fold. But the work left after the resumption has type `Ans -> Ans`, where
//! `Ans` is the one answer type every clause of a handler shares, and functions
//! of that type compose. So the continuation the clause needs is not the whole
//! rest of the program, only the pending post-work, and that composes into an
//! ordinary accumulator.
//!
//! The handler is rewritten to answer a function of that accumulator. Each
//! clause takes a `post`, a tail resumption passes it along unchanged, an
//! off-tail resumption passes `\r -> post(POST(r))`, and the return clause
//! applies whatever `post` it is handed to the value it answers. The handle
//! site seeds the identity and applies the result:
//!
//! ```text
//! handle BODY with { op(x, k) => C[k(v)], return r => R }      : Ans
//! ==>
//! handle BODY with {
//!   op(x, k) => thunk \post. p <- thunk \r. C[r] to y; post(y) ; k(v)(p)
//!   return r  => thunk \post. R to a; post(a)
//! } to g ; (force g)(\x. x)                                    : Ans
//! ```
//!
//! The replacement carries exactly the signature the handle node carried, so
//! nothing outside it changes. What it produces is the curried double
//! application `k(A)(B)` the state threader already recognizes as a fold, so
//! the whole rewritten handler lowers through parameter passing with no
//! reified continuation and one closure per off-tail operation, instead of one
//! monadic node per bind.
//!
//! The pending work may itself perform. Composition puts it under a later
//! application, but each clause's accumulator wraps the one the resumption
//! passes inward, so the applications unwind in the order the original nesting
//! ran them and the accumulator carries whatever row they share.
//!
//! Recognize-or-leave, like the sibling erasures: a clause that resumes more
//! than once, resumes under a thunk, mentions its resumption anywhere but the
//! two accepted positions, or leaves pending work performing a row the shared
//! accumulator cannot carry declines the whole handler, which the general
//! lowering then takes.
//!
//! Unlike the sibling erasures this one is not a fact about the program every
//! phase below shares. It buys one composed closure per off-tail resumption to
//! sell a fold, so it is worth its price exactly where the fold happens; a
//! program that goes on to reify a continuation anyway would pay for both. So
//! the caller runs it on the tree it hands the state rung, and leaves the tree
//! the rungs below read as written.

use std::collections::BTreeSet;

use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use crate::types::ty::EffRow;

use super::super::traverse::{free_comp_vars, free_value_vars, Rewrite};
use super::super::verify::row_included;
use super::super::{
    CompSig, CoreFnSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
    TypedHandleOp, TypedHandler, TypedValue, TypedValueKind,
};
use super::{as_var, binder_var, union_effects};

/// Rewrite handlers with an off-tail resumption to thread a composed answer
/// transformer, leaving every other handler untouched.
pub(crate) fn erase_nontail_resumes(fns: &[TypedCoreFn]) -> Vec<TypedCoreFn> {
    let mut pass = Threader {
        fresh: Fresh::new(),
    };
    fns.iter().map(|f| pass.function(f, &())).collect()
}

struct Threader {
    fresh: Fresh,
}

impl Rewrite for Threader {
    type Ctx = ();

    fn comp(&mut self, c: &TypedComp, (): &()) -> TypedComp {
        // Inner handlers first: each handle is rewritten against the answer
        // type it has once everything under it is settled.
        let descended = self.descend_comp(c, &());
        self.thread(&descended).unwrap_or(descended)
    }
}

/// The types one handle is rewritten against: its answer, its row, the
/// accumulator that carries the pending post-work, and the function-valued
/// answer the handler now produces.
struct Shape {
    answer: CoreType,
    row: EffRow,
    /// What the composed post-work performs. Empty for a handler whose pending
    /// work is pure, which is the common case and the one the state route reads
    /// best, so it is discovered rather than assumed.
    performs: EffRow,
    post: CoreType,
    arrow: CoreFnSig,
    carrier: CoreType,
}

impl Shape {
    /// The accumulator's own signature: a transformer of the answer performing
    /// whatever the pending work performs. Composition puts that work under a
    /// later application, but each clause's accumulator wraps the one the
    /// resumption passes inward, so the order the original nesting ran it in is
    /// the order the applications unwind in.
    fn transformer(answer: &CoreType, performs: &EffRow) -> CoreFnSig {
        CoreFnSig::new(
            Vec::new(),
            vec![answer.clone()],
            CompSig::new(answer.clone(), performs.clone()),
        )
    }

    fn of(sig: &CompSig, performs: &EffRow) -> Self {
        let answer = sig.result().clone();
        let row = sig.effects().clone();
        let performs = performs.clone();
        let post = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(Self::transformer(&answer, &performs))),
            EffRow::Empty,
        )));
        let arrow = CoreFnSig::new(
            Vec::new(),
            vec![post.clone()],
            CompSig::new(answer.clone(), row.clone()),
        );
        let carrier = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(arrow.clone())),
            EffRow::Empty,
        )));
        Self {
            answer,
            row,
            performs,
            post,
            arrow,
            carrier,
        }
    }

    /// The signature the rewritten handle node reports: it answers the
    /// accumulator arrow under the row the original handle already carried.
    fn outer(&self) -> CompSig {
        CompSig::new(self.carrier.clone(), self.row.clone())
    }

    /// `thunk \post. body`, the suspended clause answer.
    fn suspend(&self, acc: TypedBinder, body: TypedComp) -> TypedComp {
        let lam = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(self.arrow.clone())),
                EffRow::Empty,
            ),
            TypedCompKind::Lam(vec![acc], Box::new(body)),
        );
        ret(TypedValue::new(
            self.carrier.clone(),
            TypedValueKind::Thunk(Box::new(lam)),
        ))
    }
}

impl Threader {
    fn mint(&mut self, hint: &str) -> Sym {
        mint(&mut self.fresh, hint)
    }

    fn thread(&mut self, c: &TypedComp) -> Option<TypedComp> {
        let TypedCompKind::Handle {
            body,
            return_binder,
            return_body,
            ops,
        } = c.kind()
        else {
            return None;
        };
        // What the accumulator performs is a fact about the clauses, and the
        // clauses are typed against the accumulator, so the arms are rewritten
        // twice: once against the widest row the handler could legally carry,
        // to learn the row the pending work actually performs, and once against
        // exactly that row. The discovery pass mints into a scratch counter,
        // so a handler whose post-work is pure comes out of the second pass
        // byte for byte as it did before the first pass existed.
        let widest = Shape::of(c.sig(), c.sig().effects());
        let (_, performs, off_tail) = rewrite_arms(ops, &widest, &mut Fresh::new())?;
        // Every clause resumes on its tail: the handler already folds, and
        // threading an accumulator it never composes into would only cost a
        // closure per operation.
        if !off_tail {
            return None;
        }
        let shape = Shape::of(c.sig(), &performs);
        let outer = shape.outer();
        let (arms, _, _) = rewrite_arms(ops, &shape, &mut self.fresh)?;

        let (binder, answered) = if let (Some(binder), Some(body)) = (return_binder, return_body) {
            (binder.clone(), body.as_ref().clone())
        } else {
            let binder = TypedBinder::new(self.mint("ans"), body.sig().result().clone());
            let answered = ret(binder_var(&binder));
            (binder, answered)
        };
        let acc = TypedBinder::new(self.mint("post"), shape.post.clone());
        let delivered = deliver(&acc, answered, &shape, &mut self.fresh);
        let returns = shape.suspend(acc, delivered);

        let handler = TypedHandler::new(arms).ok()?;
        let handle = TypedComp::new(
            outer,
            TypedCompKind::Handle {
                body: body.clone(),
                return_binder: Some(binder),
                return_body: Some(Box::new(returns)),
                ops: handler,
            },
        );
        let thread = TypedBinder::new(self.mint("thread"), shape.carrier.clone());
        let seed = TypedBinder::new(self.mint("post"), shape.post.clone());
        let start = app(
            force(binder_var(&thread)),
            binder_var(&seed),
            CompSig::new(shape.answer.clone(), shape.row.clone()),
        );
        Some(bind(
            handle,
            thread,
            bind(identity(&shape, &mut self.fresh), seed, start),
        ))
    }
}

/// Rewrite every clause of one handler against one shape, reporting the arms,
/// the row the composed post-work performs, and whether any clause resumed off
/// its tail. `None` declines the whole handler.
fn rewrite_arms(
    ops: &TypedHandler,
    shape: &Shape,
    fresh: &mut Fresh,
) -> Option<(Vec<TypedHandleOp>, EffRow, bool)> {
    let outer = shape.outer();
    let mut arms = Vec::with_capacity(ops.arms().len());
    let mut performs = EffRow::Empty;
    let mut off_tail = false;
    for arm in ops.arms() {
        let resumption = retype_resume(arm.resume(), &outer)?;
        let acc = TypedBinder::new(mint(fresh, "post"), shape.post.clone());
        let mut site = Site {
            resumption: &resumption,
            acc: &acc,
            shape,
            fresh,
            performs: EffRow::Empty,
            off_tail: false,
        };
        let threaded = site.rewrite(&flatten(arm.body()), &resume_set(arm.resume().name()))?;
        performs = union_effects(&performs, &site.performs);
        off_tail |= site.off_tail;
        arms.push(TypedHandleOp::new(
            arm.name(),
            arm.instantiation().to_vec(),
            arm.params().to_vec(),
            resumption,
            shape.suspend(acc, threaded),
        ));
    }
    Some((arms, performs, off_tail))
}

fn mint(fresh: &mut Fresh, hint: &str) -> Sym {
    Sym::from(names::lowered(hint, fresh.bump()))
}

/// The names a clause body may use for its resumption: the clause binder plus
/// every let-bound alias of it in scope.
type Aliases = BTreeSet<Sym>;

fn resume_set(resume: Sym) -> Aliases {
    Aliases::from([resume])
}

/// One clause being rewritten under its own accumulator binder.
struct Site<'a> {
    resumption: &'a TypedBinder,
    acc: &'a TypedBinder,
    shape: &'a Shape,
    fresh: &'a mut Fresh,
    performs: EffRow,
    off_tail: bool,
}

impl Site<'_> {
    fn mint(&mut self, hint: &str) -> Sym {
        mint(self.fresh, hint)
    }

    // `(force k)(arg)`, answering the accumulator arrow the clause now returns.
    fn resume_call(&self, callee: &TypedComp, arg: TypedValue) -> Option<TypedComp> {
        let TypedCompKind::Force(v) = callee.kind() else {
            return None;
        };
        let alias = TypedValue::new(self.resumption.ty().clone(), v.kind.clone());
        Some(app(
            force(alias),
            arg,
            CompSig::new(self.shape.carrier.clone(), self.shape.row.clone()),
        ))
    }

    // `(force t)(post)`, running a resumption's answer against an accumulator.
    fn run(&self, thread: &TypedBinder, post: TypedValue) -> TypedComp {
        app(
            force(binder_var(thread)),
            post,
            CompSig::new(self.shape.answer.clone(), self.shape.row.clone()),
        )
    }

    // `k(v)(post)`: hand the resumption's own answer the accumulator it needs.
    fn resume_under(
        &mut self,
        callee: &TypedComp,
        arg: TypedValue,
        post: TypedValue,
    ) -> Option<TypedComp> {
        let call = self.resume_call(callee, arg)?;
        let thread = TypedBinder::new(self.mint("kont"), self.shape.carrier.clone());
        let run = self.run(&thread, post);
        Some(bind(call, thread, run))
    }

    fn rewrite(&mut self, c: &TypedComp, aliases: &Aliases) -> Option<TypedComp> {
        // Nothing left names the resumption: this branch answers directly, and
        // its answer is what the pending post-work is waiting for. A clause
        // that aborts instead of resuming is exactly this case.
        if free_comp_vars(c).is_disjoint(aliases) {
            return Some(deliver(self.acc, c.clone(), self.shape, self.fresh));
        }
        match c.kind() {
            TypedCompKind::App { callee, args, .. } if forces_resume(callee, aliases) => {
                let arg = resume_argument(args, aliases)?;
                let post = binder_var(self.acc);
                self.resume_under(callee, arg, post)
            }
            TypedCompKind::Bind(head, binder, rest) => {
                self.rewrite_bind(head, binder, rest, aliases)
            }
            TypedCompKind::If(condition, yes, no) => {
                let yes = self.rewrite(yes, aliases)?;
                let no = self.rewrite(no, aliases)?;
                Some(TypedComp::new(
                    CompSig::new(
                        self.shape.answer.clone(),
                        union_effects(yes.sig().effects(), no.sig().effects()),
                    ),
                    TypedCompKind::If(condition.clone(), Box::new(yes), Box::new(no)),
                ))
            }
            TypedCompKind::Case(scrutinee, arms) => {
                let mut rewritten = Vec::with_capacity(arms.len());
                let mut row = EffRow::Empty;
                for (pattern, body) in arms {
                    let body = self.rewrite(body, aliases)?;
                    row = union_effects(&row, body.sig().effects());
                    rewritten.push((pattern.clone(), body));
                }
                Some(TypedComp::new(
                    CompSig::new(self.shape.answer.clone(), row),
                    TypedCompKind::Case(scrutinee.clone(), rewritten),
                ))
            }
            _ => None,
        }
    }

    fn rewrite_bind(
        &mut self,
        head: &TypedComp,
        binder: &TypedBinder,
        rest: &TypedComp,
        aliases: &Aliases,
    ) -> Option<TypedComp> {
        // `t <- return k`: another name for the resumption, which the retyped
        // resumption must flow through too.
        if let TypedCompKind::Return(v) = head.kind() {
            if as_var(v).is_some_and(|name| aliases.contains(&name)) {
                let alias = TypedBinder::new(binder.name(), self.resumption.ty().clone());
                let source = TypedValue::new(self.resumption.ty().clone(), v.kind.clone());
                let mut extended = aliases.clone();
                extended.insert(binder.name());
                let tail = self.rewrite(rest, &extended)?;
                return Some(bind(ret(source), alias, tail));
            }
        }
        if let TypedCompKind::App { callee, args, .. } = head.kind() {
            if forces_resume(callee, aliases) {
                let arg = resume_argument(args, aliases)?;
                if !free_comp_vars(rest).is_disjoint(aliases) {
                    // A second resumption, or one captured for later.
                    return None;
                }
                // `r <- k(v) ; return r` is the tail resumption written through
                // a bind: composing an eta-expansion of the pending work would
                // cost a closure and buy nothing.
                if as_var_return(rest) == Some(binder.name()) {
                    let post = binder_var(self.acc);
                    return self.resume_under(callee, arg, post);
                }
                // The resumption's result feeds work that answers this scope:
                // that work is the pending post, composed onto the accumulator.
                if binder.ty() != &self.shape.answer {
                    return None;
                }
                self.off_tail = true;
                return self.compose(callee, arg, binder, rest);
            }
        }
        if !free_comp_vars(head).is_disjoint(aliases) {
            return None;
        }
        let tail = self.rewrite(rest, aliases)?;
        Some(bind(head.clone(), binder.clone(), tail))
    }

    // Compose the pending work onto the accumulator and resume under it:
    // `p <- return thunk \r. REST-then-post ; k(v)(p)`. The work may perform,
    // but only what the handle already lets escape: an accumulator carrying a
    // label the handle node does not report would change the type of the tree
    // around it, and this rewrite answers exactly the signature it replaced.
    fn compose(
        &mut self,
        callee: &TypedComp,
        arg: TypedValue,
        binder: &TypedBinder,
        rest: &TypedComp,
    ) -> Option<TypedComp> {
        if !row_included(rest.sig().effects(), &self.shape.row) {
            return None;
        }
        self.performs = union_effects(&self.performs, rest.sig().effects());
        let inner = deliver(self.acc, rest.clone(), self.shape, self.fresh);
        let lam = TypedComp::new(
            CompSig::new(
                CoreType::Function(Box::new(Shape::transformer(
                    &self.shape.answer,
                    &self.shape.performs,
                ))),
                EffRow::Empty,
            ),
            TypedCompKind::Lam(vec![binder.clone()], Box::new(inner)),
        );
        let composed = TypedBinder::new(self.mint("post"), self.shape.post.clone());
        let seed = ret(TypedValue::new(
            self.shape.post.clone(),
            TypedValueKind::Thunk(Box::new(lam)),
        ));
        let resumed = self.resume_under(callee, arg, binder_var(&composed))?;
        Some(bind(seed, composed, resumed))
    }
}

// Reassociate the bind spine so every sequenced step is a head. The desugar
// nests a step's own sub-steps to its left (`(a ; b) ; c`), which hides a
// resumption inside a head where the rewrite below expects to meet it in
// sequence. Binds are associative and Core binders are hygienic, so the
// rotation is a pure normalization; nothing under a suspension moves.
fn flatten(c: &TypedComp) -> TypedComp {
    match c.kind() {
        TypedCompKind::Bind(head, binder, rest) => {
            splice(flatten(head), binder.clone(), flatten(rest))
        }
        TypedCompKind::If(condition, yes, no) => TypedComp::new(
            c.sig().clone(),
            TypedCompKind::If(
                condition.clone(),
                Box::new(flatten(yes)),
                Box::new(flatten(no)),
            ),
        ),
        TypedCompKind::Case(scrutinee, arms) => TypedComp::new(
            c.sig().clone(),
            TypedCompKind::Case(
                scrutinee.clone(),
                arms.iter()
                    .map(|(pattern, body)| (pattern.clone(), flatten(body)))
                    .collect(),
            ),
        ),
        _ => c.clone(),
    }
}

// `head ; binder <- ; rest` with an already-flat head rotated out in front.
fn splice(head: TypedComp, binder: TypedBinder, rest: TypedComp) -> TypedComp {
    match head.kind() {
        TypedCompKind::Bind(inner, first, second) => {
            let spliced = splice(second.as_ref().clone(), binder, rest);
            bind(inner.as_ref().clone(), first.clone(), spliced)
        }
        _ => bind(head, binder, rest),
    }
}

// Whether this computation forces the resumption, seen through the let-bound
// aliases the desugar puts between a clause and its `k`.
fn forces_resume(callee: &TypedComp, aliases: &Aliases) -> bool {
    match callee.kind() {
        TypedCompKind::Force(v) => as_var(v).is_some_and(|name| aliases.contains(&name)),
        _ => false,
    }
}

// The one argument a resumption takes, refused when the resumption itself
// escapes into it.
fn resume_argument(args: &[TypedValue], aliases: &Aliases) -> Option<TypedValue> {
    let [arg] = args else {
        return None;
    };
    if free_value_vars(arg).is_disjoint(aliases) {
        Some(arg.clone())
    } else {
        None
    }
}

// `body ; y <- ; (force post)(y)`: hand what this branch answers to the
// accumulated post-work.
fn deliver(acc: &TypedBinder, body: TypedComp, shape: &Shape, fresh: &mut Fresh) -> TypedComp {
    let answered = TypedBinder::new(
        Sym::from(names::lowered("ans", fresh.bump())),
        body.sig().result().clone(),
    );
    let call = app(
        force(binder_var(acc)),
        binder_var(&answered),
        CompSig::new(shape.answer.clone(), shape.performs.clone()),
    );
    bind(body, answered, call)
}

// `return thunk \x. return x`, typed at the accumulator so the seed needs no
// widening at the application that consumes it.
fn identity(shape: &Shape, fresh: &mut Fresh) -> TypedComp {
    let x = TypedBinder::new(
        Sym::from(names::lowered("ans", fresh.bump())),
        shape.answer.clone(),
    );
    let lam = TypedComp::new(
        CompSig::new(
            CoreType::Function(Box::new(Shape::transformer(&shape.answer, &shape.performs))),
            EffRow::Empty,
        ),
        TypedCompKind::Lam(vec![x.clone()], Box::new(ret(binder_var(&x)))),
    );
    ret(TypedValue::new(
        shape.post.clone(),
        TypedValueKind::Thunk(Box::new(lam)),
    ))
}

// The resumption binder retyped to the handle's new answer. Its declared type
// is the one the verifier derives from the handle signature, so rebuilding it
// from the operation result it already carries keeps the two in step.
fn retype_resume(resume: &TypedBinder, outer: &CompSig) -> Option<TypedBinder> {
    let CoreType::Thunk(sig) = resume.ty() else {
        return None;
    };
    let CoreType::Function(fn_sig) = sig.result() else {
        return None;
    };
    let [result] = fn_sig.params() else {
        return None;
    };
    Some(TypedBinder::new(
        resume.name(),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![result.clone()],
                outer.clone(),
            ))),
            EffRow::Empty,
        ))),
    ))
}

// `return v` naming exactly one variable.
fn as_var_return(c: &TypedComp) -> Option<Sym> {
    match c.kind() {
        TypedCompKind::Return(v) => as_var(v),
        _ => None,
    }
}

fn ret(value: TypedValue) -> TypedComp {
    TypedComp::new(
        CompSig::new(value.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(value),
    )
}

fn force(value: TypedValue) -> TypedComp {
    let CoreType::Thunk(sig) = value.ty().clone() else {
        unreachable!("force of a non-thunk binder minted by this pass")
    };
    TypedComp::new(*sig, TypedCompKind::Force(value))
}

fn app(callee: TypedComp, arg: TypedValue, sig: CompSig) -> TypedComp {
    TypedComp::new(
        sig,
        TypedCompKind::App {
            callee: Box::new(callee),
            instantiation: Vec::new(),
            args: vec![arg],
        },
    )
}

fn bind(head: TypedComp, binder: TypedBinder, tail: TypedComp) -> TypedComp {
    let sig = CompSig::new(
        tail.sig().result().clone(),
        union_effects(head.sig().effects(), tail.sig().effects()),
    );
    TypedComp::new(
        sig,
        TypedCompKind::Bind(Box::new(head), binder, Box::new(tail)),
    )
}
