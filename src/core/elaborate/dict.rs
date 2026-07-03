use super::{
    builtin, dict_ctor, instance_method, wrap_binds, Builtin, BuiltinKind, Comp, CorePat, Dict,
    Elab, Error, FloatOp, IoOp, NodeId, Sym, Type, Value,
};
use crate::names;
use crate::types::SHOW_CLASS;

impl Elab<'_> {
    pub(super) fn needs_dict(&self, name: &str) -> bool {
        self.checked.methods.contains_key(&Sym::from(name))
            || self.checked.constrained.contains_key(&Sym::from(name))
    }

    pub(super) fn value_global(&self, name: &str) -> Result<Comp, Error> {
        if let Some(info) = self.ctor(name) {
            let (tag, n) = (info.tag, info.args.len());
            if n == 0 {
                return Ok(Comp::Return(Value::Ctor(name.into(), tag, vec![])));
            }
            let ps: Vec<String> = (0..n).map(|i| format!("_p{i}")).collect();
            let vals = ps.iter().map(|p| Value::Var(p.clone().into())).collect();
            let body = Comp::Return(Value::Ctor(name.into(), tag, vals));
            return Ok(Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                ps.into_iter().map(Sym::from).collect(),
                Box::new(body),
            )))));
        }
        let n = self
            .arity
            .get(name)
            .copied()
            .ok_or_else(|| Error::Ice(format!("no arity for global `{name}`")))?;
        let ps: Vec<String> = (0..n).map(|i| format!("_p{i}")).collect();
        let vals: Vec<Value> = ps.iter().map(|p| Value::Var(p.clone().into())).collect();
        let body = Self::head_call(name, vals)?;
        Ok(Comp::Return(Value::Thunk(Box::new(Comp::Lam(
            ps.into_iter().map(Sym::from).collect(),
            Box::new(body),
        )))))
    }

    pub(super) fn method_sig(&self, class: Sym, idx: usize) -> Result<(String, usize), Error> {
        let methods = &self
            .checked
            .classes
            .get(&class)
            .ok_or_else(|| Error::Ice(format!("no class info for `{class}`")))?
            .methods;
        let (name, sig) = methods.get(idx).ok_or_else(|| {
            Error::Ice(format!(
                "method index {idx} out of range for class `{class}`"
            ))
        })?;
        let arity = match sig {
            Type::Fun(doms, _, _) => doms.len(),
            _ => 0,
        };
        Ok((name.to_string(), arity))
    }

    // A dictionary as a core value: the i-th hidden parameter of the enclosing
    // function, or a top-level instance applied to its context dictionaries.
    pub(super) fn dict_value(
        &mut self,
        d: &Dict,
        binds: &mut Vec<(Comp, String)>,
    ) -> Result<Value, Error> {
        Ok(match d {
            Dict::Param(i) => Value::Var(format!("_c{i}").into()),
            Dict::Global(inst, ctxs) => {
                let mut vals = Vec::new();
                for c in ctxs {
                    vals.push(self.dict_value(c, binds)?);
                }
                let v = self.fresh();
                binds.push((Comp::Call(inst.clone().into(), vals), v.clone()));
                Value::Var(v.into())
            }
            // Project a superclass dict from a subclass dict cell: the super
            // fields lead the cell, so the field index is the super index.
            Dict::Super(d, subclass, idx) => {
                let parent = self.dict_value(d, binds)?;
                let cls = self
                    .checked
                    .classes
                    .get(&Sym::from(subclass))
                    .ok_or_else(|| Error::Ice(format!("no class info for `{subclass}`")))?;
                let n = cls.supers.len() + cls.methods.len();
                let fv = self.fresh();
                let binders = (0..n)
                    .map(|j| (j == *idx).then(|| Sym::from(&fv)))
                    .collect();
                let pat = CorePat::Ctor(Sym::from(&dict_ctor(subclass)), binders);
                let out = self.fresh();
                binds.push((
                    Comp::Case(parent, vec![(pat, Comp::Return(Value::Var(fv.into())))]),
                    out.clone(),
                ));
                Value::Var(out.into())
            }
            // Build a `Show` dict cell for a tuple: one method thunk that matches
            // the tuple and prints `(e0, e1, ...)`, each element shown through its
            // component dictionary. Matches the print-site tuple generator.
            Dict::Tuple(comps) => {
                let ps: Vec<Sym> = (0..comps.len())
                    .map(|i| Sym::from(format!("_t{i}")))
                    .collect();
                let mut elems = vec![Comp::Return(Value::Str("(".into()))];
                for (i, (comp, p)) in comps.iter().zip(&ps).enumerate() {
                    if i > 0 {
                        elems.push(Comp::Return(Value::Str(", ".into())));
                    }
                    elems.push(self.method_invoke(
                        Sym::from(SHOW_CLASS),
                        0,
                        comp,
                        vec![Value::Var(*p)],
                    )?);
                }
                elems.push(Comp::Return(Value::Str(")".into())));
                let inner = self.concat_comps(elems);
                let param = self.fresh();
                let pat = CorePat::Tuple(ps.into_iter().map(Some).collect());
                let body = Comp::Case(Value::Var(param.clone().into()), vec![(pat, inner)]);
                let show_thunk =
                    Value::Thunk(Box::new(Comp::Lam(vec![param.into()], Box::new(body))));
                let cell = Value::Ctor(dict_ctor(SHOW_CLASS).into(), 0, vec![show_thunk]);
                let v = self.fresh();
                binds.push((Comp::Return(cell), v.clone()));
                Value::Var(v.into())
            }
        })
    }

    // Saturated method invocation: a known instance becomes a direct call to
    // its method function. A dictionary parameter is projected and forced.
    pub(super) fn method_invoke(
        &mut self,
        class: Sym,
        idx: usize,
        d: &Dict,
        vals: Vec<Value>,
    ) -> Result<Comp, Error> {
        Ok(match d {
            Dict::Global(inst, ctxs) => {
                let (mname, _) = self.method_sig(class, idx)?;
                let mut binds = Vec::new();
                let mut all = Vec::new();
                for c in ctxs.clone() {
                    all.push(self.dict_value(&c, &mut binds)?);
                }
                all.extend(vals);
                wrap_binds(binds, Comp::Call(instance_method(inst, &mname).into(), all))
            }
            // A dict parameter or a superclass projection: compute the dict cell
            // value (a `_c{i}` var, or a Case that projects a super field) and
            // pull the method out of it. Methods follow the leading super fields.
            other => {
                let mut binds = Vec::new();
                let dv = self.dict_value(other, &mut binds)?;
                let cls = self
                    .checked
                    .classes
                    .get(&class)
                    .ok_or_else(|| Error::Ice(format!("no class info for `{class}`")))?;
                let nsup = cls.supers.len();
                let n = nsup + cls.methods.len();
                let field = nsup + idx;
                let mv = self.fresh();
                let binders = (0..n)
                    .map(|j| (j == field).then(|| Sym::from(&mv)))
                    .collect();
                let pat = CorePat::Ctor(Sym::from(&dict_ctor(class.as_str())), binders);
                wrap_binds(
                    binds,
                    Comp::Case(
                        dv,
                        vec![(
                            pat,
                            Comp::App(Box::new(Comp::Force(Value::Var(mv.into()))), vals),
                        )],
                    ),
                )
            }
        })
    }

    // A constrained global at value position: a closure that captures the
    // resolved dictionaries.
    pub(super) fn constrained_value(&mut self, name: &str, id: NodeId) -> Result<Comp, Error> {
        let ds = self.dicts.get(&id).cloned().ok_or_else(|| {
            Error::Ice(format!("no dictionary resolution for `{name}` at {id:?}"))
        })?;
        if let Some((class, idx)) = self.checked.methods.get(&Sym::from(name)).copied() {
            let (_, arity) = self.method_sig(class, idx)?;
            let ps: Vec<String> = (0..arity).map(|i| format!("_p{i}")).collect();
            let vals = ps.iter().map(|p| Value::Var(p.clone().into())).collect();
            let body = self.method_invoke(class, idx, first_dict(&ds, name)?, vals)?;
            return Ok(Comp::Return(Value::Thunk(Box::new(Comp::Lam(
                ps.into_iter().map(Sym::from).collect(),
                Box::new(body),
            )))));
        }
        let n = self
            .arity
            .get(name)
            .copied()
            .ok_or_else(|| Error::Ice(format!("no arity for global `{name}`")))?;
        let ps: Vec<String> = (0..n).map(|i| format!("_p{i}")).collect();
        let mut binds = Vec::new();
        let mut all: Vec<Value> = ds
            .iter()
            .map(|d| self.dict_value(d, &mut binds))
            .collect::<Result<_, _>>()?;
        all.extend(ps.iter().map(|p| Value::Var(p.clone().into())));
        let body = wrap_binds(binds, Comp::Call(name.into(), all));
        Ok(Comp::Return(Value::Thunk(Box::new(Comp::Lam(
            ps.into_iter().map(Sym::from).collect(),
            Box::new(body),
        )))))
    }

    pub(super) fn dict_call(
        &mut self,
        name: &str,
        id: NodeId,
        vals: Vec<Value>,
        binds: &mut Vec<(Comp, String)>,
    ) -> Result<Comp, Error> {
        let ds = self.dicts.get(&id).cloned().ok_or_else(|| {
            Error::Ice(format!("no dictionary resolution for `{name}` at {id:?}"))
        })?;
        // A `sort`/`sort_by_ord` whose `Ord` is a canonical primitive instance
        // lowers to the native sort kernel. A user instance (e.g. a reversed
        // ordering) or a polymorphic dict param keeps the generic merge sort.
        if vals.len() == 1 {
            if let Some(kind) = sort_kind(name, &ds) {
                let mut args = vec![Value::Int(kind)];
                args.extend(vals);
                return Ok(Comp::StrBuiltin(Builtin::SortPrim, args));
            }
        }
        if let Some((class, idx)) = self.checked.methods.get(&Sym::from(name)).copied() {
            let (_, arity) = self.method_sig(class, idx)?;
            if vals.len() == arity {
                return self.method_invoke(class, idx, first_dict(&ds, name)?, vals);
            }
        } else if let Some(n) = self.arity.get(name).copied() {
            if vals.len() == n {
                let mut all: Vec<Value> = ds
                    .iter()
                    .map(|d| self.dict_value(d, binds))
                    .collect::<Result<_, _>>()?;
                all.extend(vals);
                return Ok(Comp::Call(name.into(), all));
            }
        }
        let cf = self.constrained_value(name, id)?;
        let fv = self.fresh();
        binds.push((cf, fv.clone()));
        Ok(Comp::App(
            Box::new(Comp::Force(Value::Var(fv.into()))),
            vals,
        ))
    }

    pub(super) fn head_call(name: &str, args: Vec<Value>) -> Result<Comp, Error> {
        let first = |args: Vec<Value>| args.into_iter().next().unwrap_or(Value::Unit);
        // The kind classification and the `FloatOp`/`Builtin` name tables are
        // separate mirrors of the same set; a drift here is a compiler bug, so it
        // surfaces as a structured ICE rather than a panic.
        let resolve_float = || {
            FloatOp::from_name(name)
                .ok_or_else(|| Error::Ice(format!("float builtin `{name}` not in FloatOp")))
        };
        let resolve_str = || {
            Builtin::from_name(name)
                .ok_or_else(|| Error::Ice(format!("str builtin `{name}` not in Builtin")))
        };
        Ok(match builtin(name).map(|(_, kind)| kind) {
            Some(BuiltinKind::Print) => Comp::Io(IoOp::Print, vec![first(args)]),
            Some(BuiltinKind::Println) => Comp::Bind(
                Box::new(Comp::Io(IoOp::Print, vec![first(args)])),
                "_".into(),
                Box::new(Comp::Io(IoOp::PrintNl, vec![])),
            ),
            Some(BuiltinKind::ReadInt) => Comp::Io(IoOp::ReadInt, vec![]),
            Some(BuiltinKind::ReadLine) => Comp::Io(IoOp::ReadLine, vec![]),
            Some(BuiltinKind::Rand) => Comp::Io(IoOp::Rand, vec![]),
            Some(BuiltinKind::Srand) => Comp::Io(IoOp::Srand, vec![first(args)]),
            Some(BuiltinKind::Error) => Comp::Error(first(args)),
            Some(BuiltinKind::Float) => Comp::FloatBuiltin(resolve_float()?, first(args)),
            Some(BuiltinKind::Str | BuiltinKind::Int) => Comp::StrBuiltin(resolve_str()?, args),
            // `ord`/`chr` are nominal coercions between Char and its codepoint
            // Int. The runtime representation is identical, so they vanish.
            Some(BuiltinKind::Coerce) => Comp::Return(first(args)),
            None => Comp::Call(name.into(), args),
        })
    }
}

// The head dictionary of a resolved constraint set. A method/constrained name
// always resolves to at least one dictionary, so an empty set is a typechecker
// invariant break surfaced as a structured ICE rather than an index panic.
fn first_dict<'a>(ds: &'a [Dict], name: &str) -> Result<&'a Dict, Error> {
    ds.first()
        .ok_or_else(|| Error::Ice(format!("no dictionary for `{name}`")))
}

// The native-sort key for a `sort`/`sort_by_ord` call, or `None` to keep the
// generic path. A single `Dict::Global` means the `Ord` dictionary is a
// statically known instance (not a runtime dict parameter); matching it against
// the canonical primitive instance names is then sufficient, because coherence
// makes each such name the one true ordering for its type. Its superclass
// context (every `Ord` carries an `Eq` dict, since `Ord(a) given Eq(a)`) is
// irrelevant here: the native kernel compares by the element type, not through
// the dictionary, so a non-empty context must NOT veto specialization. The
// instance-name and kind-tag families both live in `names`
// (`SORT_PRIM_INSTANCES`), the single place the tags agree with `prism_sort_prim`.
fn sort_kind(name: &str, ds: &[Dict]) -> Option<i64> {
    if name != names::SORT_FN && name != names::SORT_BY_ORD_FN {
        return None;
    }
    let [Dict::Global(inst, _ctxs)] = ds else {
        return None;
    };
    names::sort_prim_kind(inst.as_str())
}
