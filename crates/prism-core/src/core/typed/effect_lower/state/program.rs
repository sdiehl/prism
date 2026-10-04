//! Whole-program orchestration for state threading.

use prism_common::fresh::Fresh;

use super::super::super::verify::{row_included, union_rows};
use super::super::abi;
use super::super::latent;
use super::super::peel;
use super::reify;
use super::thread::thunk_row;
use super::thread::Threader;
use super::uniformity::producer_ops;
use super::{
    flow, name_ambient, names, plan_producer, residual_row, returned_ambient, threaded_thunk_type,
    widen_buried, widen_stored, BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreQuantifier, CoreType,
    DriftLog, EffRow, FoldPlan, Latent, Loc, Retyped, Sig, StateAnalysis, Sym, ThunkFlow,
    TypedBinder, TypedComp, TypedCoreFn, TypedValue, VerifyEnv,
};
use crate::core::typed::traverse::{Rewrite, Visit};
use crate::core::typed::{TypedCompKind, TypedValueKind};
use crate::types::ty::Label;
use prism_syntax::names::ENTRY_POINT;

/// A thunk type nothing threads evidence into, with every label the value
/// channel fuses removed from its row: an operation the type admits but no
/// caller performs has no handler left in the rewritten program, and the row
/// that named it would otherwise claim an effect that no longer exists there.
/// Labels the state channel fuses stay, as every uncarried position kept them
/// before the value channel existed.
/// The fused operations a declaration's returned thunk performs, read through
/// the locals its body binds: the same answer the body pass reaches for the
/// value it returns.
fn returned_ops(
    f: &TypedCoreFn,
    plan: &FoldPlan,
    latent: &Latent,
    flow: &ThunkFlow,
) -> BTreeSet<Sym> {
    flow::result_sig_in(f.body(), &flow::param_loc(f, flow), latent, flow)
        .iter()
        .map(|m| m.id)
        .filter(|id| plan.ops.contains(id))
        .collect()
}

/// Whether a carrying position takes evidence as a parameter of its own.
///
/// A carrier buried in data is widened where it sits, so the position holding
/// it takes none: the type the pattern recovers is what says which evidence its
/// force site hands it. A position spelled as a thunk of a function is not
/// buried but is the carrier itself, so that one is threaded.
fn threads_at_position(declared: &CoreType, plan: &FoldPlan) -> bool {
    !plan.widen
        || matches!(declared, CoreType::Thunk(inner)
            if matches!(inner.result(), CoreType::Function(_)))
}

/// A thunk position no fused operation reaches, at the row it keeps: every
/// fused effect is carried as evidence wherever it is performed, so a label
/// the declared row spells for one is answered by nothing and names nothing.
pub(super) fn stripped_type(declared: &CoreType, plan: &FoldPlan, env: &VerifyEnv) -> CoreType {
    let CoreType::Thunk(inner) = declared else {
        return declared.clone();
    };
    let CoreType::Function(fun) = inner.result() else {
        return declared.clone();
    };
    let row = residual_row(fun.body().effects(), &plan.ops, env);
    if row == *fun.body().effects() {
        return declared.clone();
    }
    CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            fun.quantifiers().to_vec(),
            fun.params().to_vec(),
            CompSig::new(fun.body().result().clone(), row),
        ))),
        inner.effects().clone(),
    )))
}

/// A threaded program together with the environment it was threaded under.
///
/// Every constructor field is read and built at its stored convention, so
/// the environment that declares those conventions is part of the candidate:
/// the verifier checks the functions against this declaration and nothing
/// downstream derives it again. Widening a field is not idempotent, a
/// widened carrier's row is polymorphic and refuses a second pass, so a
/// consumer that recomputed the environment from the plan would read a
/// different declaration than the one the functions were built against.
#[derive(Debug)]
pub struct Threaded {
    pub functions: Vec<TypedCoreFn>,
    pub env: VerifyEnv,
}

pub fn thread_program(
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    analysis: &StateAnalysis<'_>,
    drift: &DriftLog,
    fresh: &mut Fresh,
) -> Option<Threaded> {
    let StateAnalysis {
        ids, latent, flow, ..
    } = analysis;
    // Every constructor field is read and built at its stored convention.
    let widened_env = analysis.widened_env(plan);
    let env = &widened_env;
    // An operation's parameter is not a store position. A carrier handed
    // through one reads back in the clause at the row the clause was
    // elaborated at, while the store that keeps it and the perform sites that
    // hand it name their own, and widened carriers at different rows are
    // different types with no subtyping between them: the evidence they take
    // sits on both sides of their arrows. The shape is refused here by name
    // rather than at whichever site first reads the payload at the other row.
    for op in &plan.ops {
        let carrier = env.operation(*op).is_some_and(|sig| {
            sig.params().iter().any(|param| {
                widen_stored(param, plan, ids, env).is_ok_and(|widened| widened != *param)
            })
        });
        if carrier {
            return analysis.decline(format!("`{}`: a carrier payload", op.as_str()));
        }
    }
    // A value producer with an open declared row names its ambient before
    // anything reads its signature. A reified operation threads nothing, so
    // it does not decide whether its producer names an ambient, exactly as it
    // does not when the producer's signature is planned.
    let name_all = |credited: &Latent| -> Option<Vec<TypedCoreFn>> {
        fns.iter()
            .map(|f| {
                let threaded = &producer_ops(f, &plan.ops, credited) - &plan.reified;
                name_ambient(f, &threaded, plan, ids).or_else(|| {
                    analysis.decline(format!("`{}`: no ambient row", f.name().as_str()))
                })
            })
            .collect()
    };
    // The reified rewrite hands cells thunks to drivers that force them with
    // nothing in hand, so what such a thunk performs is credited to the
    // function that built it, and that function's ambient names it. Which
    // thunks become cells is the rewrite's own decision, and the rewrite does
    // not depend on how the rows it spells are named: a rehearsal over the
    // plainly named program says what every function is credited with, and
    // the program is then named and rewritten once more on that answer.
    let credited: Latent = if plan.reified.is_empty() {
        (*latent).clone()
    } else {
        let named = name_all(latent)?;
        let driven = driven_positions(&named, &plan.reified);
        let rehearsed =
            reified_program(&named, plan, analysis, &driven, latent, &mut fresh.clone())?;
        minted_analysis(&rehearsed, latent, flow).0
    };
    let named = name_all(&credited)?;
    let fns = &named[..];

    // An operation no parameter can carry is reified instead of threaded: its
    // performers answer with a cell and its handle sites drive the queue. The
    // operations that remain are threaded over that tree, so a performer of
    // both answers with a cell that carries the accumulator. The parameter
    // positions the island drives are decided once here, and the reified
    // rewrite and the threader both read that decision.
    let driven = driven_positions(fns, &plan.reified);
    let cells = cells_positions(fns, plan, flow, &driven);
    let answered = plan.reified.clone();
    let reified;
    let remaining;
    let minted;
    let (fns, plan, latent, flow) = if plan.reified.is_empty() {
        (fns, plan, *latent, *flow)
    } else {
        reified = reified_program(fns, plan, analysis, &driven, &credited, fresh)?;
        remaining = plan.threaded();
        minted = minted_analysis(&reified, latent, flow);
        (&reified[..], &remaining, &minted.0, &minted.1)
    };
    let folded = StateAnalysis::new(
        ids,
        latent,
        flow,
        env,
        analysis.entry.clone(),
        analysis.widen,
        analysis.reify,
    );

    // The canonical evidence name per fused operation. A forwarding handler
    // shadows one of these for its source; nothing else rebinds them.
    let mut evs: BTreeMap<Sym, Sym> = BTreeMap::new();
    for op in &plan.ops {
        evs.insert(*op, Sym::from(names::ev(ids.id(*op)?)));
    }

    let mut threader = Threader {
        plan,
        ids,
        env,
        declared: analysis.env,
        latent,
        flow,
        drift,
        retyped: Retyped::new(),
        evidence_types: BTreeMap::new(),
        signatures: BTreeMap::new(),
        cells,
        reified: answered,
        step: None,
        abort: None,
        row: EffRow::Empty,
        returning: false,
        scheme_row: None,
        why: None,
        fresh,
    };
    // Signature prepass: every call site rebuilds from its callee's
    // transformed signature, so those signatures exist before any body does.
    for f in fns {
        let sig = match threaded_signature(f, fns, plan, &folded, &threader.cells) {
            Ok(sig) => sig,
            Err(why) => return analysis.decline(format!("`{}`: {why}", f.name().as_str())),
        };
        threader.signatures.insert(f.name(), sig);
    }
    // The free-monad combinators reified cells call join the program after
    // threading and thread nothing themselves; a continuation handed to one
    // of them has its parameter as the receiver.
    for f in [abi::ebind_fn(), abi::qapply_fn()] {
        threader
            .signatures
            .entry(f.name())
            .or_insert_with(|| f.sig().clone());
    }

    let mut out = Vec::with_capacity(fns.len());
    for f in fns {
        threader.why = None;
        let Some(lowered) = thread_function(&mut threader, f, fns, plan, &folded, &evs) else {
            let why = threader
                .why
                .take()
                .unwrap_or_else(|| "a body dropped without a reason".to_string());
            return analysis.decline(format!("`{}`: {why}", f.name().as_str()));
        };
        // A function's threaded row is its declared row with the fused labels
        // subtracted, which assumes the fold reaches every site that performs
        // them. A site the fold cannot reach, a force of an arrow a data
        // declaration owns, leaves its label in the body and refutes that
        // assumption. The engine's contract is to lower or to decline, never to
        // hand back a body its own signature disagrees with, so the mismatch is
        // asked about here rather than left for the verifier to find.
        if !row_included(
            lowered.body().sig().effects(),
            lowered.sig().body().effects(),
        ) {
            let spell = |row: &EffRow| -> String {
                row.labels()
                    .iter()
                    .map(|label| label.name.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            return analysis.decline(format!(
                "`{}`: a body that keeps an operation the fold answers (body {}; signature {})",
                f.name().as_str(),
                spell(lowered.body().sig().effects()),
                spell(lowered.sig().body().effects())
            ));
        }
        out.push(lowered);
    }
    Some(Threaded {
        functions: out,
        env: widened_env,
    })
}

/// Lower a program whose operations are reified.
///
/// The island is the functions that perform one: they answer with cells. Every
/// other function keeps its shape, except that a handle over a reified
/// operation becomes a call to the driver that reads those cells.
fn reified_program(
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    analysis: &StateAnalysis<'_>,
    driven: &BTreeMap<Sym, BTreeSet<usize>>,
    credited: &Latent,
    fresh: &mut Fresh,
) -> Option<Vec<TypedCoreFn>> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
        ..
    } = analysis;
    // Every performer in the island answers over one row, so the cells, their
    // queues and the driver all agree on it: the labels the program's
    // operations leave behind, threaded and reified alike. A member's own row
    // variable is not part of it; a caller instantiates that away, and the
    // cells it answers with are what every instantiation shares.
    // A function answers cells when its declared row says an operation cell
    // may leave it: the row spells a reified effect, or is tailed by a
    // reifying quantifier, one some caller instantiates at such an effect.
    // Every reader of the function then reads a cell, whether it drives the
    // cell itself or answers cells in turn. The entry is read by the runtime,
    // which reads no cell: what its row spells is faulted by the handle
    // wrapped around its body, a driver.
    let reifying = reify::reifying_quantifiers(fns, &plan.reified, env);
    let effects = reify::reified_effects(&plan.reified, env);
    let entry = Sym::new(ENTRY_POINT);
    let members: BTreeSet<Sym> = fns
        .iter()
        .filter(|f| {
            let row = f.sig().body().effects();
            !producer_ops(f, &plan.reified, latent).is_empty()
                || (f.name() != entry
                    && row
                        .labels()
                        .into_iter()
                        .any(|label| effects.contains(&label.name)))
                || matches!(
                    row.tail(),
                    EffRow::Var(v) if reifying.get(&f.name()).is_some_and(|own| own.contains(v))
                )
        })
        .map(TypedCoreFn::name)
        .collect();
    let mut labels: BTreeSet<Label> = fns
        .iter()
        .filter(|f| members.contains(&f.name()))
        .flat_map(|f| {
            residual_row(f.sig().body().effects(), &plan.ops, env)
                .labels()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>()
        })
        .collect();
    // A thunk literal handed to a cells position is a member without a name:
    // its body is rebuilt as cells too, so what that body performs beyond
    // the fused operations is the island's as well.
    let mut handed = HandedThunks {
        carries: |callee, position| {
            flow.param
                .get(&callee)
                .and_then(|params| params.get(position))
                .is_some_and(|sig| sig.iter().any(|m| plan.reified.contains(&m.id)))
                || driven
                    .get(&callee)
                    .is_some_and(|positions| positions.contains(&position))
        },
        ops: &plan.ops,
        env,
        bound: BTreeMap::new(),
        labels: BTreeSet::new(),
    };
    for f in fns {
        handed.walk_function(f);
    }
    labels.extend(handed.labels);
    let row = EffRow::canonical(labels, EffRow::Empty);
    // A function the threader runs at a gained ambient performs its threaded
    // operations through evidence typed over that ambient, and so do the
    // cells it builds, since a cells thunk reads the evidence of the scope
    // that built it: its cells row is the island's labels over that ambient,
    // spelled with the name the threader will append, so the two passes
    // agree without a cast. One that threads nothing but installs a handler
    // the threader answers builds its cells at its own declared row, where
    // the evidence that handler makes is typed; any other keeps the island's
    // closed row, which a wider reader widens.
    let threaded: BTreeSet<Sym> = plan.ops.difference(&plan.reified).copied().collect();
    // A caller of an extended function answers at the extended row as well,
    // so its declared row grows by the island labels it does not spell, and
    // so on up to a caller whose row already spells them: what a driver
    // performs when it resumes a cell is performed by whoever ran it. The
    // entry keeps its row; the runtime reads it.
    let mut extending: BTreeSet<Sym> = fns
        .iter()
        .filter(|f| members.contains(&f.name()) || reify::hosts_driver(f, &plan.reified))
        .map(TypedCoreFn::name)
        .collect();
    loop {
        let grown: Vec<Sym> = fns
            .iter()
            .filter(|f| f.name() != entry && !extending.contains(&f.name()))
            .filter(|f| {
                let declared: BTreeSet<Sym> = f
                    .sig()
                    .body()
                    .effects()
                    .labels()
                    .into_iter()
                    .map(|label| label.name)
                    .collect();
                row.labels()
                    .into_iter()
                    .any(|label| !declared.contains(&label.name))
                    && reify::calls_any(f, &extending)
            })
            .map(TypedCoreFn::name)
            .collect();
        if grown.is_empty() {
            break;
        }
        extending.extend(grown);
    }
    let ambients: BTreeMap<Sym, EffRow> = fns
        .iter()
        .filter_map(|f| {
            let mut numbered: Vec<i64> = producer_ops(f, &threaded, credited)
                .iter()
                .filter_map(|op| ids.id(*op))
                .collect();
            (!numbered.is_empty()).then(|| {
                numbered.sort_unstable();
                let tail = EffRow::Var(Sym::from(names::evidence_row(&numbered)));
                (
                    f.name(),
                    EffRow::canonical(row.labels().into_iter().cloned(), tail),
                )
            })
        })
        .collect();
    // Members and hosts are read at their extended rows everywhere, the
    // types their callers hand arguments at included.
    let extended: Vec<TypedCoreFn> = fns
        .iter()
        .map(|f| {
            if extending.contains(&f.name()) {
                reify::extend_tail(f, &row, &plan.ops, env)
            } else {
                f.clone()
            }
        })
        .collect();
    let sigs: BTreeMap<Sym, CoreFnSig> = extended
        .iter()
        .map(|f| (f.name(), f.sig().clone()))
        .collect();
    let widened_tails: BTreeSet<Sym> = fns
        .iter()
        .zip(&extended)
        .filter(|(before, after)| before.sig() != after.sig())
        .map(|(_, after)| after.name())
        .collect();
    let mut reifier = reify::Reifier {
        row: row.clone(),
        island: row.clone(),
        home: row.clone(),
        ambients: &ambients,
        open: false,
        answering: None,
        ambient: EffRow::Empty,
        reified: &plan.reified,
        fused: &plan.ops,
        members: &members,
        env,
        ids,
        flow,
        driven,
        sigs: &sigs,
        extended: &widened_tails,
        latent: credited,
        names: BTreeMap::new(),
        reifying_quantifiers: &reifying,
        reifying: BTreeSet::new(),
        drivers: Vec::new(),
        answer: None,
        quantifiers: Vec::new(),
        fresh,
        why: None,
    };

    let mut out = Vec::with_capacity(fns.len());
    let mut generated = Vec::new();
    let mut widened: BTreeMap<Sym, CoreFnSig> = BTreeMap::new();
    for f in &extended {
        // A member answering cells over its row quantifier (the tail of its
        // declared row, extended by the island and given no ambient) answers
        // them over the island's labels ahead of that quantifier, as a
        // threaded one does ahead of its ambient: a caller in closed cells
        // instantiates the quantifier away, and one at its own quantifier
        // hands it through, so the values the body types over the quantifier
        // meet its own calls.
        let cells = match ambients.get(&f.name()) {
            Some(cells) => cells.clone(),
            None if reifier.answering_quantifier(f.name()).is_some() => EffRow::canonical(
                row.labels().into_iter().cloned(),
                f.sig().body().effects().tail().clone(),
            ),
            None if members.contains(&f.name())
                || reify::hosts_driver(f, &plan.reified)
                || !reify::installs_handler_for(f, &threaded) =>
            {
                row.clone()
            }
            None => {
                let declared = residual_row(f.sig().body().effects(), &plan.ops, env);
                match union_rows(&declared, &row) {
                    Ok(cells) => cells,
                    Err(why) => {
                        return analysis.decline(format!(
                            "`{}`: a row the island's row does not join ({why})",
                            f.name().as_str()
                        ))
                    }
                }
            }
        };
        reifier.row = cells.clone();
        if members.contains(&f.name()) {
            let Some(body) = reifier
                .enter(f)
                .and_then(|()| reifier.comp_at(f.body(), Some(f.sig().body().result())))
            else {
                return analysis.decline(format!(
                    "`{}`: {}",
                    f.name().as_str(),
                    reifier
                        .why
                        .unwrap_or_else(|| "no reified rewrite".to_string())
                ));
            };
            // The member declares what it still performs after its reified
            // labels are gone, joined with the island's row its cells code runs
            // at; the threader subtracts the rest.
            let declared = reifier.ambient.clone();
            generated.append(&mut reifier.drivers);
            out.push(TypedCoreFn::new(
                f.name(),
                f.params().to_vec(),
                body,
                reify::producer_signature(f, reifier.residual_params(f), &cells, declared),
                f.dict_arity(),
            ));
            continue;
        }
        let Some((lowered, mut minted)) = reify::reify_handles(f, &plan.reified, &mut reifier)
        else {
            return analysis.decline(format!(
                "`{}`: {}",
                f.name().as_str(),
                reifier
                    .why
                    .unwrap_or_else(|| "no reified rewrite".to_string())
            ));
        };
        // A host that drives the island is called at the island's row
        // wherever it is called.
        if !minted.is_empty() {
            widened.insert(lowered.name(), lowered.sig().clone());
        }
        generated.append(&mut minted);
        out.push(lowered);
    }
    out.append(&mut generated);
    // Every row in the program is read at its residual once the island's
    // members answer cells: what a member's caller hands it is typed by the
    // caller's declaration, which still spells the reified labels.
    if !widened.is_empty() || !members.is_empty() {
        let mut resign = reify::Resign {
            widened: &widened,
            reified: &plan.reified,
            env,
            fresh,
        };
        out = out.iter().map(|f| resign.function(f, &())).collect();
    }
    Some(out)
}

/// The signature a function declares once its fused operations are threaded.
///
/// A consumer's declared row is its original row with the discharged effects
/// subtracted, not whatever its rewritten tail locally reports: the handle
/// removed exactly those labels, and every call site's expectation is computed
/// from this signature. A producer's is the residual it was planned under.
/// The parameter positions the reified rewrite reads as cells: the flow says
/// the thunk there performs a reified operation, or a driver in the callee
/// forces it. Such a position is typed by that rewrite and takes no evidence:
/// the cells behind it were built where the evidence of every threaded label
/// they perform is in scope, and no handler for such a label stands between
/// the building and the forcing, since a handle over cells is promoted.
fn cells_positions(
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    flow: &ThunkFlow,
    driven: &BTreeMap<Sym, BTreeSet<usize>>,
) -> BTreeMap<Sym, BTreeSet<usize>> {
    if plan.reified.is_empty() {
        return BTreeMap::new();
    }
    fns.iter()
        .map(|f| {
            let mut positions = driven.get(&f.name()).cloned().unwrap_or_default();
            if let Some(params) = flow.param.get(&f.name()) {
                positions.extend(
                    params
                        .iter()
                        .enumerate()
                        .filter(|(_, sig)| sig.iter().any(|m| plan.reified.contains(&m.id)))
                        .map(|(i, _)| i),
                );
            }
            (f.name(), positions)
        })
        .filter(|(_, positions)| !positions.is_empty())
        .collect()
}

/// The parameter positions each function's callers drive as cells, by the
/// function's own signature: a thunk parameter whose row performs a reified
/// operation. Decided once per threading, so every reader agrees.
fn driven_positions(
    fns: &[TypedCoreFn],
    reified: &BTreeSet<Sym>,
) -> BTreeMap<Sym, BTreeSet<usize>> {
    fns.iter()
        .map(|f| (f.name(), reify::driven_params(f, reified)))
        .filter(|(_, positions)| !positions.is_empty())
        .collect()
}

/// The labels the bodies of thunk literals handed to cells positions keep
/// beyond the fused operations.
struct HandedThunks<'a, F: Fn(Sym, usize) -> bool> {
    carries: F,
    ops: &'a BTreeSet<Sym>,
    env: &'a VerifyEnv,
    /// Names bound directly to a thunk literal, with the literal's row.
    bound: BTreeMap<Sym, EffRow>,
    labels: BTreeSet<Label>,
}

impl<F: Fn(Sym, usize) -> bool> Visit for HandedThunks<'_, F> {
    fn comp(&mut self, comp: &TypedComp) -> bool {
        match comp.kind() {
            TypedCompKind::Bind(first, binder, _) => {
                if let TypedCompKind::Return(value) = first.kind() {
                    if let Some(row) = literal_thunk_row(value) {
                        self.bound.insert(binder.name(), row.clone());
                    }
                }
            }
            TypedCompKind::Call { callee, args, .. } => {
                for (position, arg) in args.iter().enumerate() {
                    if !(self.carries)(*callee, position) {
                        continue;
                    }
                    let row = match &arg.kind {
                        TypedValueKind::Var { name, .. } => self.bound.get(name),
                        _ => literal_thunk_row(arg),
                    };
                    if let Some(row) = row {
                        let residual = residual_row(row, self.ops, self.env);
                        self.labels.extend(residual.labels().into_iter().cloned());
                    }
                }
            }
            _ => {}
        }
        true
    }
}

/// The row a thunk literal's body runs at, wrappers peeled.
fn literal_thunk_row(value: &TypedValue) -> Option<&EffRow> {
    let inner = peel(value);
    if !matches!(inner.kind, TypedValueKind::Thunk(_)) {
        return None;
    }
    match inner.ty() {
        CoreType::Thunk(sig) => Some(thunk_row(inner.ty()).unwrap_or_else(|| sig.effects())),
        _ => None,
    }
}

/// The analysis the threader reads once the reified rewrite has minted its
/// drivers. A driver's clauses call what the handler's clauses called, so a
/// driver reaching a threaded operation is a producer of it and its callers
/// hand it evidence; its own parameters, cells and queues, carry nothing. The
/// functions the analysis already saw keep their answers, which the rewrite
/// narrows where it answers with cells and widens where it hands a cell a
/// thunk: that thunk is forced with nothing, so what it performs reads the
/// evidence of the function that built it.
fn minted_analysis(fns: &[TypedCoreFn], latent: &Latent, flow: &ThunkFlow) -> (Latent, ThunkFlow) {
    let bodies: BTreeMap<Sym, &TypedComp> = fns.iter().map(|f| (f.name(), f.body())).collect();
    let seed: Latent = fns
        .iter()
        .map(|f| (f.name(), latent.get(&f.name()).cloned().unwrap_or_default()))
        .collect();
    let extended = prism_common::fixpoint::least_fixpoint(seed, |name, cur| {
        let mut set = latent.get(name).cloned().unwrap_or_default();
        latent::latent(bodies[name], cur, &mut set);
        set
    });
    let mut param = flow.param.clone();
    let mut ret = flow.ret.clone();
    let mut fresh = BTreeSet::new();
    for f in fns {
        param
            .entry(f.name())
            .or_insert_with(|| vec![Sig::new(); f.params().len()]);
        if let std::collections::btree_map::Entry::Vacant(entry) = ret.entry(f.name()) {
            entry.insert(Sig::new());
            fresh.insert(f.name());
        }
    }
    let mut flow = ThunkFlow {
        ret,
        param,
        carriers: flow.carriers.clone(),
    };
    // A driver answers with what its handler's clauses answered with: a
    // lambda among them performs what its body performs, and the driver's
    // callers force it with that evidence.
    loop {
        let mut changed = false;
        for f in fns.iter().filter(|f| fresh.contains(&f.name())) {
            let sig = flow::result_sig_in(f.body(), &flow::param_loc(f, &flow), &extended, &flow);
            let slot = flow.ret.entry(f.name()).or_default();
            let before = slot.len();
            slot.extend(sig);
            changed |= slot.len() != before;
        }
        if !changed {
            break;
        }
    }
    (extended, flow)
}

fn threaded_signature(
    f: &TypedCoreFn,
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    analysis: &StateAnalysis<'_>,
    cells: &BTreeMap<Sym, BTreeSet<usize>>,
) -> Result<CoreFnSig, String> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
        ..
    } = analysis;
    // A function the analysis never saw was minted by the reified rewrite
    // and performs nothing the threader answers; it keeps its shape.
    let Some(sigs) = flow.param.get(&f.name()) else {
        return Ok(f.sig().clone());
    };
    let ops = producer_ops(f, &plan.ops, latent);
    let producer = if ops.is_empty() {
        None
    } else {
        Some(plan_producer(f, &ops, plan, ids, fns, latent, env)?)
    };
    let row = producer.as_ref().map_or_else(
        || residual_row(f.sig().body().effects(), &plan.ops, env),
        |producer| producer.row.clone(),
    );
    let mut param_tys: Vec<CoreType> = f.sig().params().to_vec();
    for (index, sig) in sigs.iter().enumerate() {
        let carried: BTreeSet<Sym> = sig
            .iter()
            .map(|m| m.id)
            .filter(|id| plan.ops.contains(id))
            .collect();
        let declared = param_tys
            .get(index)
            .ok_or("more parameters in the flow than declared")?;
        if cells
            .get(&f.name())
            .is_some_and(|positions| positions.contains(&index))
        {
            continue;
        }
        let declared = widen_buried(declared, plan, ids, env)?;
        param_tys[index] = if carried.is_empty() || !threads_at_position(&declared, plan) {
            stripped_type(&declared, plan, env)
        } else {
            threaded_thunk_type(
                &declared,
                &carried,
                plan,
                ids,
                env,
                Some(&row),
                Some(f.sig().body().effects()),
            )?
        };
    }
    match producer {
        // A consumer's result follows its returned thunk when the flow says
        // the result carries fused operations.
        None => {
            let ret_ops = returned_ops(f, plan, latent, flow);
            let declared = widen_buried(f.sig().body().result(), plan, ids, env)?;
            let mut quantifiers = f.sig().quantifiers().to_vec();
            let result = if ret_ops.is_empty() || !threads_at_position(&declared, plan) {
                stripped_type(&declared, plan, env)
            } else if let Some(ambient) = returned_ambient(&declared, &ret_ops, plan, ids, env) {
                quantifiers.push(CoreQuantifier::Row(ambient));
                threaded_thunk_type(
                    &declared,
                    &ret_ops,
                    plan,
                    ids,
                    env,
                    Some(&EffRow::Var(ambient)),
                    Some(f.sig().body().effects()),
                )?
            } else {
                threaded_thunk_type(
                    &declared,
                    &ret_ops,
                    plan,
                    ids,
                    env,
                    None,
                    Some(f.sig().body().effects()),
                )?
            };
            Ok(CoreFnSig::new(
                quantifiers,
                param_tys,
                CompSig::new(result, row),
            ))
        }
        Some(producer) => {
            // A value-threaded producer returning a fused thunk would need its
            // declared result widened; nothing does that yet.
            if producer.accumulator.is_none()
                && flow
                    .ret
                    .get(&f.name())
                    .is_some_and(|s| s.iter().any(|m| plan.ops.contains(&m.id)))
            {
                return Err("a value producer returning a thunk that carries".into());
            }
            let mut all = param_tys;
            all.extend(producer.evidence.iter().map(|b| b.ty().clone()));
            all.extend(producer.accumulator.iter().map(|b| b.ty().clone()));
            Ok(CoreFnSig::new(
                producer.quantifiers.clone(),
                all,
                CompSig::new(producer.result.clone(), producer.row.clone()),
            ))
        }
    }
}

/// Thread one function under the plan, against the signatures the prepass
/// declared for every function.
fn thread_function(
    threader: &mut Threader<'_>,
    f: &TypedCoreFn,
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    analysis: &StateAnalysis<'_>,
    evs: &BTreeMap<Sym, Sym>,
) -> Option<TypedCoreFn> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
        ..
    } = analysis;
    let Some(sigs) = flow.param.get(&f.name()) else {
        return Some(f.clone());
    };
    let loc: Loc = f
        .params()
        .iter()
        .map(TypedBinder::name)
        .zip(sigs.iter().cloned())
        .collect();
    let ops = producer_ops(f, &plan.ops, latent);
    let producer = if ops.is_empty() {
        None
    } else {
        Some(plan_producer(f, &ops, plan, ids, fns, latent, env).ok()?)
    };
    let row = producer.as_ref().map_or_else(
        || residual_row(f.sig().body().effects(), &plan.ops, env),
        |producer| producer.row.clone(),
    );
    threader.evidence_types.clear();
    // Source binder names are lexical, so the retype map is
    // declaration-local: a widened `g` from one instance method must not
    // leak into the next method's differently-shaped `g`.
    threader.retyped = Retyped::new();
    // A thunk-valued parameter that performs a fused operation arrives
    // already threaded whoever receives it, producer or consumer: its
    // declared type is the threaded thunk type, and every read of that
    // parameter follows it.
    let sigs = flow.param.get(&f.name())?;
    let mut params = f.params().to_vec();
    for (index, sig) in sigs.iter().enumerate() {
        let carried: BTreeSet<Sym> = sig
            .iter()
            .map(|m| m.id)
            .filter(|id| plan.ops.contains(id))
            .collect();
        let declared = params.get(index)?;
        if threader
            .cells
            .get(&f.name())
            .is_some_and(|positions| positions.contains(&index))
        {
            continue;
        }
        let buried = widen_buried(declared.ty(), plan, ids, env).ok()?;
        let widened = if carried.is_empty() || !threads_at_position(&buried, plan) {
            stripped_type(&buried, plan, env)
        } else {
            threaded_thunk_type(
                &buried,
                &carried,
                plan,
                ids,
                env,
                Some(&row),
                Some(f.sig().body().effects()),
            )
            .ok()?
        };
        if widened == *declared.ty() {
            continue;
        }
        threader.retyped.insert(declared.name(), widened.clone());
        params[index] = TypedBinder::new(declared.name(), widened);
    }
    if ops.is_empty() {
        // A consumer's body runs at its residual row: a call it makes to a
        // producer widens that producer's ambient to it. A result that
        // carries is threaded to the row the prepass declared for it.
        threader.row = row.clone();
        let ret_ops = returned_ops(f, plan, latent, flow);
        let result_row = threader
            .signatures
            .get(&f.name())
            .filter(|_| !ret_ops.is_empty())
            .and_then(|sig| thunk_row(sig.body().result()))
            .cloned();
        // The quantifier a returned carrier binds lives on this function's own
        // scheme, so the lambda that returns it must not bind it a second time
        // inside its own type.
        let quantifiers = threader.signatures.get(&f.name()).map_or_else(
            || f.sig().quantifiers().to_vec(),
            |sig| sig.quantifiers().to_vec(),
        );
        threader.scheme_row = result_row
            .as_ref()
            .and_then(|row| match row.tail() {
                EffRow::Var(name) => Some(*name),
                _ => None,
            })
            .filter(|name| {
                quantifiers
                    .iter()
                    .any(|q| matches!(q, CoreQuantifier::Row(bound) if bound == name))
            });
        let body = match result_row {
            Some(result_row) => threader.rewrite_tail(f.body(), &loc, evs, &result_row, &ret_ops),
            None => threader.rewrite(f.body(), &loc, evs),
        };
        threader.row = EffRow::Empty;
        threader.scheme_row = None;
        let body = body?;
        let sig = CoreFnSig::new(
            quantifiers,
            params.iter().map(|p| p.ty().clone()).collect(),
            CompSig::new(body.sig().result().clone(), row),
        );
        Some(TypedCoreFn::new(
            f.name(),
            params,
            body,
            sig,
            f.dict_arity(),
        ))
    } else {
        let producer = producer?;
        for binder in &producer.evidence {
            threader
                .evidence_types
                .insert(binder.name(), binder.ty().clone());
        }
        threader.row = producer.row.clone();
        // A top-level producer in an early-exit program threads a stepped
        // accumulator, and its guards consume the same one Step decision a
        // handle scope would have published for it. A value producer
        // threads under its own abort, if any.
        let body = if let Some(accumulator) = &producer.accumulator {
            threader.step.clone_from(&producer.step);
            let body = threader.thread_st(f.body(), evs, &loc, accumulator);
            threader.step = None;
            body
        } else {
            threader.abort.clone_from(&producer.abort);
            let early = producer.abort.is_some();
            let body = threader.thread_val(f.body(), evs, &loc, early);
            threader.abort = None;
            body
        };
        threader.row = EffRow::Empty;
        let body = body?;
        // A producer's declared row is its ambient, and its body has to end
        // there. A call to a consumer of the effect this function also
        // produces keeps the function's own declared residual instead, which
        // is a second open tail beside the ambient, and no rule unions two.
        if let (EffRow::Var(ambient), EffRow::Var(tail)) =
            (producer.row.tail(), body.sig().effects().tail())
        {
            if ambient != tail {
                return threader
                    .bail("a consumer called where its residual row is not this scope's ambient");
            }
        }
        let params = producer.params(&params);
        // The declared row is the planned residual, whatever the body's
        // final node locally says: it ends in the ambient variable, which
        // a caller instantiates away.
        let sig = CoreFnSig::new(
            producer.quantifiers.clone(),
            params.iter().map(|p| p.ty().clone()).collect(),
            CompSig::new(body.sig().result().clone(), producer.row.clone()),
        );
        Some(TypedCoreFn::new(
            f.name(),
            params,
            body,
            sig,
            f.dict_arity(),
        ))
    }
}
