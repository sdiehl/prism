//! Whole-program orchestration for state threading.

use prism_common::fresh::Fresh;

use super::super::subtract::subtract_row;
use super::thread::Threader;
use super::uniformity::producer_ops;
use super::{
    names, plan_producer, threaded_thunk_type, BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreType,
    DriftLog, EffRow, FoldPlan, Loc, Retyped, StateAnalysis, Sym, TypedBinder, TypedCoreFn,
};

pub fn thread_program(
    fns: &[TypedCoreFn],
    plan: &FoldPlan,
    analysis: &StateAnalysis<'_>,
    drift: &DriftLog,
    fresh: &mut Fresh,
) -> Option<Vec<TypedCoreFn>> {
    let StateAnalysis {
        ids,
        latent,
        flow,
        env,
    } = analysis;
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
        latent,
        flow,
        drift,
        retyped: Retyped::new(),
        evidence_types: BTreeMap::new(),
        signatures: BTreeMap::new(),
        step: None,
        row: EffRow::Empty,
        fresh,
    };
    // Signature prepass: every call site rebuilds from its callee's
    // transformed signature, so those signatures exist before any body does.
    for f in fns {
        let sigs = flow.param.get(&f.name())?;
        let mut param_tys: Vec<CoreType> = f.sig().params().to_vec();
        for (index, sig) in sigs.iter().enumerate() {
            let carried: BTreeSet<Sym> = sig
                .iter()
                .map(|m| m.id)
                .filter(|id| plan.ops.contains(id))
                .collect();
            if carried.is_empty() {
                continue;
            }
            let declared = param_tys.get(index)?;
            param_tys[index] = threaded_thunk_type(declared, &carried, plan, ids, env)?;
        }
        let ops = producer_ops(f, &plan.ops, latent);
        let new_sig = if ops.is_empty() {
            // A consumer: residual row, and a result that follows its returned
            // thunk when the flow says the result carries fused operations.
            let mut residual = f.sig().body().effects().clone();
            for op in &plan.ops {
                if let Some(operation) = env.operation(*op) {
                    residual = subtract_row(&residual, operation.effect().name);
                }
            }
            let ret_ops: BTreeSet<Sym> = flow
                .ret
                .get(&f.name())
                .map(|s| {
                    s.iter()
                        .map(|m| m.id)
                        .filter(|id| plan.ops.contains(id))
                        .collect()
                })
                .unwrap_or_default();
            let result = if ret_ops.is_empty() {
                f.sig().body().result().clone()
            } else {
                threaded_thunk_type(f.sig().body().result(), &ret_ops, plan, ids, env)?
            };
            CoreFnSig::new(
                f.sig().quantifiers().to_vec(),
                param_tys,
                CompSig::new(result, residual),
            )
        } else {
            let producer = plan_producer(f, &ops, plan, ids, fns, latent, env)?;
            let mut all = param_tys;
            all.extend(producer.evidence.iter().map(|b| b.ty().clone()));
            all.push(producer.accumulator.ty().clone());
            CoreFnSig::new(
                producer.quantifiers.clone(),
                all,
                CompSig::new(
                    producer.accumulator.ty().clone(),
                    EffRow::Var(producer.ambient),
                ),
            )
        };
        threader.signatures.insert(f.name(), new_sig);
    }

    let mut out = Vec::with_capacity(fns.len());
    for f in fns {
        let loc: Loc = f
            .params()
            .iter()
            .map(TypedBinder::name)
            .zip(flow.param.get(&f.name())?.iter().cloned())
            .collect();
        let ops = producer_ops(f, &plan.ops, latent);
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
            if carried.is_empty() {
                continue;
            }
            let declared = params.get(index)?;
            let widened = threaded_thunk_type(declared.ty(), &carried, plan, ids, env)?;
            threader.retyped.insert(declared.name(), widened.clone());
            params[index] = TypedBinder::new(declared.name(), widened);
        }
        let lowered = if ops.is_empty() {
            let body = threader.rewrite(f.body(), &loc, &evs)?;
            // A consumer's declared row is its original row with the discharged
            // effects subtracted, not whatever its rewritten tail locally
            // reports: the handle removed exactly those labels, and every call
            // site's expectation is computed from this signature.
            let mut residual = f.sig().body().effects().clone();
            for op in &plan.ops {
                if let Some(operation) = env.operation(*op) {
                    residual = subtract_row(&residual, operation.effect().name);
                }
            }
            let sig = CoreFnSig::new(
                f.sig().quantifiers().to_vec(),
                params.iter().map(|p| p.ty().clone()).collect(),
                CompSig::new(body.sig().result().clone(), residual),
            );
            TypedCoreFn::new(f.name(), params, body, sig, f.dict_arity())
        } else {
            let producer = plan_producer(f, &ops, plan, ids, fns, latent, env)?;
            let producer_evs: BTreeMap<Sym, Sym> = evs
                .iter()
                .filter(|(operation, _)| ops.contains(operation))
                .map(|(operation, evidence)| (*operation, *evidence))
                .collect();
            for binder in &producer.evidence {
                threader
                    .evidence_types
                    .insert(binder.name(), binder.ty().clone());
            }
            threader.row = EffRow::Var(producer.ambient);
            // A top-level producer in an early-exit program threads a stepped
            // accumulator, and its guards consume the same one Step decision a
            // handle scope would have published for it.
            threader.step.clone_from(&producer.step);
            let body = threader.thread_st(f.body(), &producer_evs, &loc, &producer.accumulator)?;
            threader.step = None;
            threader.row = EffRow::Empty;
            let params = producer.params(&params);
            // The declared row is the ambient variable, whatever the body's
            // final node locally says: the residual of a threaded producer
            // rides its ambient quantifier, and a caller instantiates it away.
            let sig = CoreFnSig::new(
                producer.quantifiers.clone(),
                params.iter().map(|p| p.ty().clone()).collect(),
                CompSig::new(body.sig().result().clone(), EffRow::Var(producer.ambient)),
            );
            TypedCoreFn::new(f.name(), params, body, sig, f.dict_arity())
        };
        out.push(lowered);
    }
    Some(out)
}
