//! Closure-application dispatch: the curry adapters and the `prism_apply_n`
//! dispatchers. `App` nodes call an unknown closure, so every arity an `App`
//! reaches (and every lambda arity) gets one total dispatcher that resolves
//! exact / under- / over-application against the closure's tag. Under-application
//! mints a curry adapter closure; the planning fixpoint below registers those
//! before any body is emitted so a stateful backend realizes each on first use.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::slice;

use super::abi::{idx64, HDR_BYTES, TAG_OFF, WORD_BYTES};
use super::emit::{Cg, LamBody, LamInfo};
use super::isa::{Buf, Isa};
use super::rt;
use crate::core::{Comp, Value};
use crate::names::{closure_cap, closure_rem};
use crate::sym::Sym;

impl<I: Isa> Cg<'_, I> {
    // Tag of the curry adapter that under-applies `target` (arity m, with
    // `target_fvs` captured free vars) to `n` arguments: a lambda of arity m-n
    // capturing target_fvs+n values. Allocated on first request and memoized so
    // planning and emission resolve the same tag.
    fn curry_adapter(&mut self, target: usize, target_fvs: usize, n: usize) -> usize {
        if let Some(&tag) = self.adapters.get(&(target, n)) {
            return tag;
        }
        let index = self.lams.len();
        let owner = self.lams[target].owner;
        let tag = self
            .mint_closure_tag(owner)
            .expect("curry adapter closure tag is unique");
        let m = self.lams[target].params.len();
        let free_vars = (0..target_fvs + n)
            .map(|i| Sym::new(&closure_cap(i)))
            .collect();
        let params = (0..m - n).map(|i| Sym::new(&closure_rem(i))).collect();
        self.lams.push(LamInfo {
            tag,
            owner,
            params,
            free_vars,
            body: LamBody::Curry { target },
        });
        self.adapters.insert((target, n), index);
        index
    }

    // Register (without emitting) the curry adapters and follow-on apply arities
    // a `prism_apply_n` dispatcher will reference. Stateful backends realize each
    // function on first emission, so this must reach a fixpoint before any lambda
    // body is emitted. Applying zero arguments is the identity on the closure
    // (see `apply_dispatch`), so n == 0 needs no adapter; skipping it also keeps
    // the fixpoint finite, since an n == 0 under-application would mint a
    // same-arity adapter that regenerates forever. Every other adapter has arity
    // m - n < m, so the chain of adapters-of-adapters strictly shrinks.
    // Every lambda arity plus every arity an `App` actually calls. The planning
    // fixpoint and the final dispatcher emission both iterate exactly this set.
    pub(super) fn apply_arities(&self) -> BTreeSet<usize> {
        let mut a: BTreeSet<usize> = self.lams.iter().map(|l| l.params.len()).collect();
        a.extend(self.used_apply.iter().copied());
        a
    }

    pub(super) fn plan_dispatch(&mut self, n: usize) {
        if n == 0 {
            return;
        }
        for tag in 0..self.lams.len() {
            let m = self.lams[tag].params.len();
            let fvs = self.lams[tag].free_vars.len();
            match m.cmp(&n) {
                Ordering::Greater => {
                    self.curry_adapter(tag, fvs, n);
                }
                Ordering::Less => {
                    self.used_apply.insert(n - m);
                }
                Ordering::Equal => {}
            }
        }
    }

    // One `prism_apply_n` dispatcher, total over every lambda tag, dispatching
    // per the lambda's parameter count m against the n supplied args: exact
    // (m == n, call it), under (m > n, build a curry adapter closure of arity
    // m-n), or over (m < n, call with the first m then apply the remaining n-m to
    // the result). All adapters and follow-on apply arities must already be
    // planned (see `plan_dispatch`), so this never grows `lams` and references
    // only emitted functions. Applying zero arguments only ever lands on an
    // arity-0 thunk, so for n == 0 the sole reachable case is m == 0;
    // positive-arity tags route to `_dead` like any non-applicable value.
    pub(super) fn apply_dispatch(&mut self, n: usize) -> String {
        let lams: Vec<(usize, LamInfo)> = self
            .lams
            .iter()
            .enumerate()
            .filter(|(_, lambda)| n > 0 || lambda.params.is_empty())
            .map(|(index, lambda)| (index, lambda.clone()))
            .collect();
        let mut params = vec!["%_clos".to_string()];
        params.extend((0..n).map(|i| format!("%_a{i}")));
        let header = self.isa.fn_define(&format!("prism_apply_{n}"), &params);

        let mut b = Buf::default();
        self.isa.open_entry(&mut b);

        self.isa.inttoptr(&mut b, "%_cp", "%_clos");
        self.isa.gep(&mut b, "%_tp", "%_cp", TAG_OFF);
        self.isa.load(&mut b, "%_tag", "%_tp");

        if lams.is_empty() {
            self.isa.call_void(&mut b, rt::APPLY_ERROR, &[]);
            self.isa.unreachable(&mut b);
            return format!("{header}{}{}", b.body, self.isa.fn_close());
        }

        let cases: Vec<(i64, String)> = lams
            .iter()
            .map(|(_, lambda)| (idx64(lambda.tag), format!("_lam{}", lambda.tag)))
            .collect();
        self.isa.switch(&mut b, "%_tag", "_dead", &cases);
        self.isa.open_block(&mut b, "_dead");
        self.isa.call_void(&mut b, rt::APPLY_ERROR, &[]);
        self.isa.unreachable(&mut b);

        let mut preds: Vec<(String, String)> = Vec::new();
        for (index, lam) in &lams {
            let tag = lam.tag;
            let m = lam.params.len();
            let fvs = lam.free_vars.len();
            self.isa.open_block(&mut b, &format!("_lam{tag}"));

            let mut captured: Vec<String> = Vec::new();
            for i in 0..fvs {
                let fp = format!("%_fp{tag}_{i}");
                let fv = format!("%_fv{tag}_{i}");
                let off = HDR_BYTES + idx64(i) * WORD_BYTES;
                self.isa.gep(&mut b, &fp, "%_cp", off);
                self.isa.load(&mut b, &fv, &fp);
                captured.push(fv);
            }
            let args: Vec<String> = (0..n).map(|i| format!("%_a{i}")).collect();
            let r = format!("%_r{tag}");

            match m.cmp(&n) {
                Ordering::Equal => {
                    let mut call_args = captured;
                    call_args.extend(args);
                    self.isa
                        .call(&mut b, &r, &format!("prism_lam_{tag}"), &call_args);
                }
                Ordering::Greater => {
                    // Under-application: capture (fvs ++ args) into an adapter
                    // closure expecting the remaining m-n. The fvs are still owned
                    // by `%_clos` (the caller drops it after this apply), so dup
                    // them; the args were handed to us and move in.
                    let adapter = self.curry_adapter(*index, fvs, n);
                    let mut fields = captured;
                    for fv in &fields {
                        self.isa.call_void(&mut b, rt::RC_INC, slice::from_ref(fv));
                    }
                    fields.extend(args);
                    let nf = self.isa.const_int(&mut b, idx64(fields.len()));
                    let cp = format!("%_ac{tag}");
                    self.isa
                        .call_ptr(&mut b, &cp, rt::ALLOC, slice::from_ref(&nf));
                    let tp = format!("%_atp{tag}");
                    self.isa.gep(&mut b, &tp, &cp, TAG_OFF);
                    let tv = self.isa.const_int(&mut b, idx64(self.lams[adapter].tag));
                    self.isa.store(&mut b, &tv, &tp);
                    for (i, fld) in fields.iter().enumerate() {
                        let off = HDR_BYTES + idx64(i) * WORD_BYTES;
                        let fp = format!("%_afp{tag}_{i}");
                        self.isa.gep(&mut b, &fp, &cp, off);
                        self.isa.store(&mut b, fld, &fp);
                    }
                    self.isa.ptrtoint(&mut b, &r, &cp);
                }
                Ordering::Less => {
                    // Over-application: ANF saturates every call, so a closure
                    // receiving more args than its arity is a lowering bug. The
                    // interpreter traps this shape (`eval`, the differential
                    // oracle); trap identically here rather than implement the
                    // extra application, which would silently fork native
                    // semantics from the oracle on a shape neither should see.
                    self.isa.call_void(&mut b, rt::APPLY_ERROR, &[]);
                    self.isa.unreachable(&mut b);
                    continue;
                }
            }
            self.isa.jump_merge(&mut b, "_merge", &r);
            preds.push((r, format!("_lam{tag}")));
        }
        // Every arm may have trapped (each lambda's arity below n): the merge
        // block then has no predecessors and must not be emitted.
        if preds.is_empty() {
            return format!("{header}{}{}", b.body, self.isa.fn_close());
        }
        self.isa.open_merge(&mut b, "_merge", "%_result", &preds);
        self.isa.ret(&mut b, "%_result");
        format!("{header}{}{}", b.body, self.isa.fn_close())
    }
}

pub(super) fn partial_app_body(
    name: &str,
    n_given: usize,
    arity: usize,
) -> (Vec<Sym>, Vec<Sym>, Comp) {
    let cap_names: Vec<Sym> = (0..n_given).map(|i| Sym::new(&closure_cap(i))).collect();
    let rem_names: Vec<Sym> = (0..arity - n_given)
        .map(|i| Sym::new(&closure_rem(i)))
        .collect();
    let call_args = cap_names
        .iter()
        .chain(rem_names.iter())
        .map(|n| Value::Var(*n))
        .collect();
    let mut body = Comp::Call(name.into(), call_args);
    for cn in &cap_names {
        body = Comp::Bind(
            Box::new(Comp::Dup(Value::Var(*cn))),
            "_".into(),
            Box::new(body),
        );
    }
    (cap_names, rem_names, body)
}
