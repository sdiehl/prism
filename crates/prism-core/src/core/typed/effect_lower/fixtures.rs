//! Hand-built typed Core programs shared by the effect-lowering unit tests.
//!
//! One home for the programs whose shape several modules assert about, so a
//! plan test and a builder test that claim to be talking about the same program
//! are talking about the same program.

use prism_common::sym::Sym;
use prism_syntax::names::ENTRY_POINT;

use super::super::{
    CompSig, CoreFnSig, CoreType, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
    TypedHandleOp, TypedHandler, TypedValue, TypedValueKind,
};
use crate::types::ty::EffRow;
use crate::types::Type;

/// The effect the fixtures perform, and the one operation it declares.
pub const ASK: &str = "Ask";
pub const ASK_OP: &str = "Ask.ask";
/// A second effect, performed only where a handler clause is meant to be open.
pub const LEAK: &str = "Leak";
pub const LEAK_OP: &str = "Leak.leak";

/// The performer, the forwarder that forces what it is handed, and the
/// intermediate that calls the forwarder from direct code.
pub const BUMP: &str = "bump";
pub const RUN: &str = "run";
pub const HELPER: &str = "helper";
/// A declaration that performs nothing and forces what it is handed, so a
/// computation reaching it stays outside the region.
pub const SINK: &str = "sink";

#[must_use]
pub fn int() -> CoreType {
    CoreType::Source(Type::Int)
}

#[must_use]
pub fn asking() -> EffRow {
    EffRow::singleton(ASK)
}

pub fn named(name: &str, params: Vec<TypedBinder>, body: TypedComp) -> TypedCoreFn {
    let signature = CoreFnSig::new(
        Vec::new(),
        params.iter().map(TypedBinder::ty).cloned().collect(),
        body.sig().clone(),
    );
    TypedCoreFn::new(Sym::from(name), params, body, signature, 0)
}

#[must_use]
pub fn var(name: Sym, ty: CoreType) -> TypedValue {
    TypedValue::new(
        ty,
        TypedValueKind::Var {
            name,
            instantiation: Vec::new(),
        },
    )
}

#[must_use]
pub fn performed() -> TypedComp {
    TypedComp::new(
        CompSig::new(int(), asking()),
        TypedCompKind::Do {
            operation: Sym::from(ASK_OP),
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    )
}

#[must_use]
pub fn call(callee: &str, args: Vec<TypedValue>, effects: EffRow) -> TypedComp {
    TypedComp::new(
        CompSig::new(int(), effects),
        TypedCompKind::Call {
            callee: Sym::from(callee),
            instantiation: Vec::new(),
            args,
        },
    )
}

/// The suspended nullary function a thunk holds, with the source signature the
/// direct convention gives it.
fn nullary_lambda(body: TypedComp) -> TypedComp {
    TypedComp::new(
        CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                body.sig().clone(),
            ))),
            EffRow::Empty,
        ),
        TypedCompKind::Lam(Vec::new(), Box::new(body)),
    )
}

#[must_use]
pub fn nullary_thunk(body: TypedComp) -> TypedValue {
    let lambda = nullary_lambda(body);
    TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    )
}

/// The type of a suspended nullary computation that performs `effects`.
fn suspended_ty(effects: EffRow) -> CoreType {
    CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            Vec::new(),
            Vec::new(),
            CompSig::new(int(), effects),
        ))),
        EffRow::Empty,
    )))
}

/// The type of a suspended nullary computation that performs the operation.
#[must_use]
pub fn action_ty() -> CoreType {
    suspended_ty(asking())
}

/// Force what a declaration was handed and apply it: the body that performs
/// exactly what the computation reaching the slot performs, and nothing a
/// latent-op map can see.
fn forced_action(action: &TypedBinder, effects: EffRow) -> TypedComp {
    let signature = CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(int(), effects.clone()));
    let forced = TypedComp::new(
        CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
        TypedCompKind::Force(var(action.name(), action.ty().clone())),
    );
    TypedComp::new(
        CompSig::new(int(), effects),
        TypedCompKind::App {
            callee: Box::new(forced),
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    )
}

/// The continuation a handler clause resumes through: one argument, one
/// answer, and the signature of the function it suspends.
fn resume_binder() -> (TypedBinder, CoreFnSig) {
    let signature = CoreFnSig::new(Vec::new(), vec![int()], CompSig::new(int(), EffRow::Empty));
    let binder = TypedBinder::new(
        Sym::from("resume"),
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(signature.clone())),
            EffRow::Empty,
        ))),
    );
    (binder, signature)
}

/// Apply the continuation to one argument.
fn resumed(resume: &TypedBinder, signature: CoreFnSig, argument: TypedValue) -> TypedComp {
    let force = TypedComp::new(
        CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
        TypedCompKind::Force(var(resume.name(), resume.ty().clone())),
    );
    TypedComp::new(
        CompSig::new(int(), EffRow::Empty),
        TypedCompKind::App {
            callee: Box::new(force),
            instantiation: Vec::new(),
            args: vec![argument],
        },
    )
}

/// Perform the second operation before `rest`, which is what leaves a clause
/// open: the handler this clause belongs to does not discharge it.
fn leaking(rest: TypedComp) -> TypedComp {
    let leaked = TypedComp::new(
        CompSig::new(CoreType::Source(Type::Unit), EffRow::singleton(LEAK)),
        TypedCompKind::Do {
            operation: Sym::from(LEAK_OP),
            instantiation: Vec::new(),
            args: Vec::new(),
        },
    );
    TypedComp::new(
        CompSig::new(rest.sig().result().clone(), EffRow::singleton(LEAK)),
        TypedCompKind::Bind(
            Box::new(leaked),
            TypedBinder::new(Sym::from("ignored"), CoreType::Source(Type::Unit)),
            Box::new(rest),
        ),
    )
}

/// Wrap a computation in a tail-resumptive handler for `operation`, answering
/// with `result`. The handler is closed unless `open`, in which case its clause
/// performs a second operation the handler does not itself discharge.
fn handling(operation: &str, body: TypedComp, open: bool, result: EffRow) -> TypedComp {
    let parameter = TypedBinder::new(Sym::from("question"), int());
    let (resume, resume_signature) = resume_binder();
    let resumed = resumed(
        &resume,
        resume_signature,
        var(parameter.name(), parameter.ty().clone()),
    );
    let clause_body = if open { leaking(resumed) } else { resumed };
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        Sym::from(operation),
        Vec::new(),
        vec![parameter],
        resume,
        clause_body,
    )])
    .expect("one unique clause");
    TypedComp::new(
        CompSig::new(int(), result),
        TypedCompKind::Handle {
            body: Box::new(body),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    )
}

/// A handler for the operation the fixtures perform, which discharges what the
/// computation it wraps performs.
#[must_use]
pub fn handling_ask(body: TypedComp, leaking: bool) -> TypedComp {
    handling(ASK_OP, body, leaking, EffRow::Empty)
}

/// A handler for the *other* operation: an island a declaration installs
/// around its own body, discharging something the computation inside never
/// performs. What that computation performs leaves the island untouched.
fn handling_leak(body: TypedComp) -> TypedComp {
    let escaping = body.sig().effects().clone();
    handling(LEAK_OP, body, false, escaping)
}

/// The forwarder: it performs nothing of its own and only applies the
/// computation it is handed, which is what makes it invisible to a latent-op
/// map and visible only to the interprocedural thunk flow.
fn forwarder() -> TypedCoreFn {
    let action = TypedBinder::new(Sym::from("action"), action_ty());
    let applied = forced_action(&action, asking());
    named(RUN, vec![action], applied)
}

/// The forwarder with its force moved inside a handler of its own, for an
/// operation the computation it forces never performs. The declaration still
/// owns a slot the region drives, but every force of that slot sits under a
/// `handle` the declaration installs itself.
fn island_forwarder() -> TypedCoreFn {
    let action = TypedBinder::new(Sym::from("action"), action_ty());
    let applied = forced_action(&action, asking());
    named(RUN, vec![action], handling_leak(applied))
}

/// The thunk that performs, suspended around a call to the performer, handed to
/// the forwarder as a named-call argument so the flow analysis tracks it.
fn call_forwarder() -> TypedComp {
    let captured = nullary_thunk(call(BUMP, Vec::new(), asking()));
    call(RUN, vec![captured], asking())
}

/// `bump` performs the operation, `run` forces the computation it is handed,
/// and the entry point builds that computation and handles the operation around
/// the call.
///
/// The capture is trackable: the thunk travels as a named-call argument, never
/// buried in a constructor or handed to a dynamic callee.
#[must_use]
pub fn capturing_program() -> Vec<TypedCoreFn> {
    vec![
        named(BUMP, Vec::new(), performed()),
        forwarder(),
        named(
            ENTRY_POINT,
            Vec::new(),
            handling_ask(call_forwarder(), false),
        ),
    ]
}

/// [`capturing_program`] with the forwarder's force moved inside a handler of
/// its own, for an unrelated operation.
///
/// What the forced computation performs is absent from every row the
/// forwarder's own body discharges, so nothing about the forwarder's
/// declaration says which convention its slot is driven at: only the flow fact
/// does.
#[must_use]
pub fn island_program() -> Vec<TypedCoreFn> {
    vec![
        named(BUMP, Vec::new(), performed()),
        island_forwarder(),
        named(
            ENTRY_POINT,
            Vec::new(),
            handling_ask(call_forwarder(), false),
        ),
    ]
}

/// [`island_program`] with the handler moved to the *caller* and the force left
/// where it was.
///
/// The intermediate installs a handler for an unrelated operation and, inside
/// it, hands the computation that performs to the forwarder rather than forcing
/// it in place.
///
/// The op the forwarder's force performs still reaches this handler's driver,
/// and no map here says so: the forwarder performs nothing of its own, and the
/// force that performs it sits in the forwarder's body, not in this one.
#[must_use]
pub fn handed_off_program() -> Vec<TypedCoreFn> {
    vec![
        named(BUMP, Vec::new(), performed()),
        forwarder(),
        named(HELPER, Vec::new(), handling_leak(call_forwarder())),
        named(
            ENTRY_POINT,
            Vec::new(),
            handling_ask(call(HELPER, Vec::new(), asking()), false),
        ),
    ]
}

/// A handler whose clause answers with a transformer rather than resuming where
/// it stands.
///
/// It hands back a lambda for the code around the handle to apply, and that
/// lambda performs the operation this handler does not discharge.
///
/// The answer is a computation the confined region rewrites, carried out of the
/// driver in a value the source type describes as an ordinary function.
///
/// # Panics
/// Panics if the fixture's own clause table is rejected as duplicated, which
/// would mean the fixture is malformed.
#[must_use]
pub fn transformer_answer_program() -> Vec<TypedCoreFn> {
    let parameter = TypedBinder::new(Sym::from("question"), int());
    let (resume, _) = resume_binder();
    let left = TypedBinder::new(Sym::from("left"), int());
    let transformer = TypedComp::new(
        CompSig::new(int(), EffRow::singleton(LEAK)),
        TypedCompKind::Lam(
            vec![left.clone()],
            Box::new(leaking(TypedComp::new(
                CompSig::new(int(), EffRow::Empty),
                TypedCompKind::Return(var(left.name(), left.ty().clone())),
            ))),
        ),
    );
    let answer = TypedValue::new(
        CoreType::Thunk(Box::new(transformer.sig().clone())),
        TypedValueKind::Thunk(Box::new(transformer)),
    );
    let clause_body = TypedComp::new(
        CompSig::new(answer.ty().clone(), EffRow::Empty),
        TypedCompKind::Return(answer),
    );
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        Sym::from(ASK_OP),
        Vec::new(),
        vec![parameter],
        resume,
        clause_body.clone(),
    )])
    .expect("one unique clause");
    let handled = TypedComp::new(
        CompSig::new(clause_body.sig().result().clone(), EffRow::singleton(LEAK)),
        TypedCompKind::Handle {
            body: Box::new(call(BUMP, Vec::new(), asking())),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    );
    vec![
        named(BUMP, Vec::new(), performed()),
        named(HELPER, Vec::new(), handled),
    ]
}

/// A handler clause that hands the continuation to a declaration outside the
/// region, buried in a thunk: the shape a clause takes when something else
/// decides how often to resume.
///
/// Nothing in a latent map or a flow solution names what that thunk performs,
/// because a continuation performs whatever the computation it resumes
/// performs. The clause is open, which is what has the region reify the
/// continuation rather than leave it a source function.
///
/// # Panics
/// Panics if the fixture's own clause table is rejected as duplicated, which
/// would mean the fixture is malformed.
#[must_use]
pub fn resume_capturing_program() -> Vec<TypedCoreFn> {
    let parameter = TypedBinder::new(Sym::from("question"), int());
    let (resume, resume_signature) = resume_binder();
    let again = nullary_thunk(resumed(
        &resume,
        resume_signature,
        var(parameter.name(), parameter.ty().clone()),
    ));
    let clauses = TypedHandler::new(vec![TypedHandleOp::new(
        Sym::from(ASK_OP),
        Vec::new(),
        vec![parameter],
        resume,
        leaking(call(SINK, vec![again], EffRow::Empty)),
    )])
    .expect("one unique clause");
    let handled = TypedComp::new(
        CompSig::new(int(), EffRow::singleton(LEAK)),
        TypedCompKind::Handle {
            body: Box::new(call(BUMP, Vec::new(), asking())),
            return_binder: None,
            return_body: None,
            ops: clauses,
        },
    );
    let action = TypedBinder::new(Sym::from("action"), suspended_ty(EffRow::Empty));
    let sink_body = forced_action(&action, EffRow::Empty);
    vec![
        named(BUMP, Vec::new(), performed()),
        named(SINK, vec![action], sink_body),
        named(HELPER, Vec::new(), handled),
    ]
}

/// A member that binds what the operation answers and then hands a suspended
/// computation reading that binder to a declaration outside the region.
///
/// The suspension performs nothing, so the region leaves it at the direct
/// convention and copies it verbatim, while the binder it reads is one the
/// transform reified into a runtime word.
#[must_use]
pub fn word_capturing_program() -> Vec<TypedCoreFn> {
    let answer = TypedBinder::new(Sym::from("answer"), int());
    let read = TypedComp::new(
        CompSig::new(int(), EffRow::Empty),
        TypedCompKind::Return(var(answer.name(), int())),
    );
    let body = TypedComp::new(
        CompSig::new(int(), asking()),
        TypedCompKind::Bind(
            Box::new(performed()),
            answer,
            Box::new(call(SINK, vec![nullary_thunk(read)], EffRow::Empty)),
        ),
    );
    let action = TypedBinder::new(Sym::from("action"), suspended_ty(EffRow::Empty));
    vec![
        named(
            SINK,
            vec![action.clone()],
            forced_action(&action, EffRow::Empty),
        ),
        named(HELPER, Vec::new(), body),
        named(
            ENTRY_POINT,
            Vec::new(),
            handling_ask(call(HELPER, Vec::new(), asking()), false),
        ),
    ]
}

/// [`capturing_program`] with the call to the forwarder moved out of the
/// handler and into an intermediate declaration, which performs nothing itself
/// and captures the thunk.
///
/// The intermediate calls a member from direct code, so the region can only be
/// consistent if it reaches the intermediate too.
#[must_use]
pub fn forwarded_program() -> Vec<TypedCoreFn> {
    vec![
        named(BUMP, Vec::new(), performed()),
        forwarder(),
        named(HELPER, Vec::new(), call_forwarder()),
        named(
            ENTRY_POINT,
            Vec::new(),
            handling_ask(call(HELPER, Vec::new(), asking()), false),
        ),
    ]
}
