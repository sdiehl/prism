//! Whole-program, confined-region, and selective orchestration.

use super::{
    abi, flow, union_effects, BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreQuantifier, Decline,
    EffRow, Fresh, Monadic, MonadicScope, OpIds, Refusal, Region, Rows, Sym, TypedCoreFn,
    ENTRY_POINT,
};

fn monadic_quantifiers(function: &TypedCoreFn, row: &EffRow) -> Vec<CoreQuantifier> {
    let mut quantifiers = function.sig().quantifiers().to_vec();
    if let EffRow::Var(ambient) = row.tail() {
        if !quantifiers.contains(&CoreQuantifier::Row(*ambient)) {
            quantifiers.push(CoreQuantifier::Row(*ambient));
        }
    }
    quantifiers
}

/// Put every function in one monadic calling convention.
///
/// Each declaration's row retains the direct effects that remain after source
/// operations are reified; call instantiation aligns the callee with its
/// current caller.
///
/// # Errors
/// The refusal this builder recorded, attributed to the declaration it stopped
/// in. Nothing is left to widen to at this scope, so the caller reports it; a
/// refusal that names neither the declaration nor the form costs the reader the
/// whole diagnosis, which is why the builder's own record is carried out here
/// rather than collapsed into a single "no rewrite exists" verdict.
pub fn lower_whole<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
) -> Result<Vec<TypedCoreFn>, Decline> {
    let signatures: BTreeMap<Sym, CoreFnSig> = functions
        .iter()
        .map(|function| {
            let row = rows
                .row(function.name())
                .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?;
            Ok((
                function.name(),
                CoreFnSig::new(
                    monadic_quantifiers(function, &row),
                    function.sig().params().to_vec(),
                    CompSig::new(abi::eff(row.clone()), row),
                ),
            ))
        })
        .collect::<Result<_, Decline>>()?;
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    let mut lowered = Vec::with_capacity(functions.len());
    for function in functions {
        let row = rows
            .row(function.name())
            .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?;
        monadic.set_row(row.clone());
        monadic.quantifiers = monadic_quantifiers(function, &row);
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        // A resume alias belongs to one handler's dynamic scope; it must not
        // leak into the next function, or a plain source binder that happens to
        // share the continuation's name (a map's key `k` beside a handler's
        // `resume k`) is mistyped as the reified continuation. `lower_region`
        // already clears this per member; whole-program lowering must match.
        monadic.resume_aliases.clear();
        // Thunk signatures are per-declaration for the same reason: they are
        // keyed by binder name, and two declarations share names freely.
        monadic.thunk_sigs.clear();
        let body = monadic
            .comp(function.body())
            .ok_or_else(|| monadic.declined(function.name()))?;
        let entry = function.name().as_str() == ENTRY_POINT;
        let body = if entry {
            monadic.unwrap_entry(body, function.sig().body().result().clone())
        } else {
            body
        };
        let signature = if entry {
            CoreFnSig::new(
                monadic_quantifiers(function, &row),
                function.sig().params().to_vec(),
                CompSig::new(function.sig().body().result().clone(), row.clone()),
            )
        } else {
            signatures
                .get(&function.name())
                .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?
                .clone()
        };
        lowered.push(TypedCoreFn::new(
            function.name(),
            function.params().to_vec(),
            body,
            signature,
            function.dict_arity(),
        ));
    }
    lowered.append(&mut monadic.generated);
    Ok(lowered)
}

/// Lower one clean `LocalPartial` component in the whole-style convention while
/// retaining direct signatures for the fused rest's inert callees.
///
/// Region entries unwrap their `Eff` result for the direct caller across the
/// split.
///
/// # Errors
/// The refusal that stopped the region: a member with no planned row, a plan
/// naming a declaration the program does not define, or a member body the
/// builder has no rewrite for. The plan is already committed by the time this
/// runs, so none of these widen; the caller reports them.
pub fn lower_region<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    region: &BTreeSet<Sym>,
    entries: &BTreeSet<Sym>,
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
) -> Result<Vec<TypedCoreFn>, Decline> {
    let planned_rows: BTreeMap<Sym, EffRow> = functions
        .iter()
        .filter(|function| region.contains(&function.name()))
        .map(|function| {
            rows.row(function.name())
                .map(|row| (function.name(), row))
                .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))
        })
        .collect::<Result<_, _>>()?;
    if let Some(missing) = region.iter().find(|name| !planned_rows.contains_key(name)) {
        return Err(Decline::whole(Refusal::PlanMismatch, *missing));
    }
    let signatures: BTreeMap<Sym, CoreFnSig> = functions
        .iter()
        .map(|function| {
            let signature = if region.contains(&function.name()) {
                let row = planned_rows
                    .get(&function.name())
                    .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?;
                CoreFnSig::new(
                    monadic_quantifiers(function, row),
                    function.sig().params().to_vec(),
                    CompSig::new(abi::eff(row.clone()), row.clone()),
                )
            } else {
                function.sig().clone()
            };
            Ok((function.name(), signature))
        })
        .collect::<Result<_, Decline>>()?;
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    let mut lowered = Vec::with_capacity(region.len());
    for function in functions
        .iter()
        .filter(|function| region.contains(&function.name()))
    {
        let row = planned_rows
            .get(&function.name())
            .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?;
        monadic.set_row(row.clone());
        monadic.quantifiers = monadic_quantifiers(function, row);
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        monadic.resume_aliases.clear();
        monadic.thunk_sigs.clear();
        let body = monadic
            .comp(function.body())
            .ok_or_else(|| monadic.declined(function.name()))?;
        let entry = entries.contains(&function.name());
        let body = if entry {
            monadic.unwrap_entry(body, function.sig().body().result().clone())
        } else {
            body
        };
        let signature = if entry {
            CoreFnSig::new(
                monadic_quantifiers(function, row),
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    body.sig().effects().clone(),
                ),
            )
        } else {
            signatures
                .get(&function.name())
                .cloned()
                .ok_or_else(|| Decline::whole(Refusal::PlanMismatch, function.name()))?
        };
        lowered.push(TypedCoreFn::new(
            function.name(),
            function.params().to_vec(),
            body,
            signature,
            function.dict_arity(),
        ));
    }
    lowered.append(&mut monadic.generated);
    Ok(lowered)
}

/// Lower only declarations selected by a pre-rewrite region plan.
///
/// Functions outside the region keep their source convention and are traversed
/// only to discharge closed handlers; region entries unwrap their `Eff` result
/// for the direct caller named by the plan.
///
/// A refusal is returned rather than dropped: the caller answers it by widening
/// the plan, and what it answered is what the plan artifact and the fallback
/// warning report.
///
/// # Errors
/// The [`Decline`] the region recorded: the shape it has no confined rewrite
/// for, and where it met it.
///
/// # Panics
/// Panics if the plan is not a confined one. Which scope a plan carries is the
/// caller's to dispatch on, so a whole-program plan arriving here is a bug in
/// the cascade rather than a program the region refused.
pub fn lower_selective<R: Rows + ?Sized>(
    functions: &[TypedCoreFn],
    ops: &OpIds,
    fresh: &mut Fresh,
    rows: &R,
    region: &Region<'_>,
) -> Result<Vec<TypedCoreFn>, Decline> {
    let plan = region.plan;
    assert_eq!(
        plan.scope,
        MonadicScope::Selective,
        "confined lowering needs a confined plan"
    );
    let mut signatures: BTreeMap<Sym, CoreFnSig> = BTreeMap::new();
    for function in functions {
        let signature = if plan.members.contains(&function.name()) {
            let row = rows
                .row(function.name())
                .ok_or_else(|| Decline::whole(Refusal::MissingRow, function.name()))?;
            CoreFnSig::new(
                monadic_quantifiers(function, &row),
                function.sig().params().to_vec(),
                CompSig::new(abi::eff(row.clone()), row),
            )
        } else {
            function.sig().clone()
        };
        signatures.insert(function.name(), signature);
    }
    let mut monadic = Monadic::new(ops, fresh, EffRow::Empty, &signatures);
    monadic.configure_region(region);
    let mut lowered = Vec::with_capacity(functions.len());
    for function in functions {
        let member = plan.members.contains(&function.name());
        let missing_row = || Decline::whole(Refusal::MissingRow, function.name());
        if member {
            let row = rows.row(function.name()).ok_or_else(missing_row)?;
            monadic.set_row(row.clone());
            monadic.quantifiers = monadic_quantifiers(function, &row);
        } else {
            // A declaration outside the region keeps its source row, but the
            // computations it suspends for the region reify what its residual
            // plan says the declaration's whole body performs, thunks included.
            // Those labels sit over the declaration's own tail rather than the
            // region's: only a member quantifies the phase-private row, so a
            // suspension built here has to stay inside the rows the direct
            // declaration already binds.
            let source = function.sig().body().effects().clone();
            let residual = rows.row(function.name()).ok_or_else(missing_row)?;
            monadic.set_direct_row(
                source.clone(),
                EffRow::canonical(
                    residual.labels().into_iter().cloned(),
                    source.tail().clone(),
                ),
            );
            monadic.quantifiers = function.sig().quantifiers().to_vec();
        }
        monadic.locals = function
            .params()
            .iter()
            .map(|parameter| (parameter.name(), parameter.ty().clone()))
            .collect();
        monadic.word_binders.clear();
        monadic.resume_aliases.clear();
        // Seed the scope from the interprocedural solution: what flowed into
        // each thunk-valued parameter is what forcing that parameter performs,
        // and reading it from the same place the plan did is what keeps the
        // membership decision and the rewrite from disagreeing.
        monadic.thunk_sigs = flow::param_loc(function, region.flow);
        let entry = plan.entries.contains(&function.name());
        let rewritten = if member {
            monadic.comp(function.body())
        } else {
            monadic.direct(function.body())
        };
        let Some(body) = rewritten else {
            return Err(monadic.declined(function.name()));
        };
        let body = if member && entry {
            monadic.unwrap_entry(body, function.sig().body().result().clone())
        } else {
            body
        };
        let signature = if member && !entry {
            signatures
                .get(&function.name())
                .ok_or_else(missing_row)?
                .clone()
        } else if member {
            CoreFnSig::new(
                monadic_quantifiers(
                    function,
                    &rows.row(function.name()).ok_or_else(missing_row)?,
                ),
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    body.sig().effects().clone(),
                ),
            )
        } else {
            CoreFnSig::new(
                function.sig().quantifiers().to_vec(),
                function.sig().params().to_vec(),
                CompSig::new(
                    function.sig().body().result().clone(),
                    // A declaration outside the region may only ever *widen*: the
                    // rewrite can add a residual effect, and the verifier admits a
                    // body row that is a subrow of the declaration, so a body whose
                    // recomputed row is narrower than the source row must not pull
                    // the declaration down with it. Narrowing here breaks every
                    // call node already emitted against the wider row, and the
                    // first of those is the declaration's own recursive call,
                    // rewritten before this signature exists.
                    union_effects(function.sig().body().effects(), body.sig().effects()),
                ),
            )
        };
        monadic
            .generated_signatures
            .insert(function.name(), signature.clone());
        lowered.push(TypedCoreFn::new(
            function.name(),
            function.params().to_vec(),
            body,
            signature,
            function.dict_arity(),
        ));
    }
    lowered.append(&mut monadic.generated);
    Ok(lowered)
}
