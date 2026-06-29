use super::{
    builtin, dict_ctor, instance_method, wrap_binds, Builtin, BuiltinKind, Comp, CorePat, Dict,
    Elab, Error, FloatOp, NodeId, Sym, Type, Value,
};

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

    pub(super) fn method_sig(&self, class: Sym, idx: usize) -> (String, usize) {
        let (name, sig) = &self.checked.classes[&class].methods[idx];
        let arity = match sig {
            Type::Fun(doms, _, _) => doms.len(),
            _ => 0,
        };
        (name.to_string(), arity)
    }

    // A dictionary as a core value: the i-th hidden parameter of the enclosing
    // function, or a top-level instance applied to its context dictionaries.
    pub(super) fn dict_value(&mut self, d: &Dict, binds: &mut Vec<(Comp, String)>) -> Value {
        match d {
            Dict::Param(i) => Value::Var(format!("_c{i}").into()),
            Dict::Global(inst, ctxs) => {
                let mut vals = Vec::new();
                for c in ctxs {
                    vals.push(self.dict_value(c, binds));
                }
                let v = self.fresh();
                binds.push((Comp::Call(inst.clone().into(), vals), v.clone()));
                Value::Var(v.into())
            }
            // Project a superclass dict from a subclass dict cell: the super
            // fields lead the cell, so the field index is the super index.
            Dict::Super(d, subclass, idx) => {
                let parent = self.dict_value(d, binds);
                let cls = &self.checked.classes[&Sym::from(subclass)];
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
        }
    }

    // Saturated method invocation: a known instance becomes a direct call to
    // its method function. A dictionary parameter is projected and forced.
    pub(super) fn method_invoke(
        &mut self,
        class: Sym,
        idx: usize,
        d: &Dict,
        vals: Vec<Value>,
    ) -> Comp {
        match d {
            Dict::Global(inst, ctxs) => {
                let (mname, _) = self.method_sig(class, idx);
                let mut binds = Vec::new();
                let mut all = Vec::new();
                for c in ctxs.clone() {
                    all.push(self.dict_value(&c, &mut binds));
                }
                all.extend(vals);
                wrap_binds(binds, Comp::Call(instance_method(inst, &mname).into(), all))
            }
            // A dict parameter or a superclass projection: compute the dict cell
            // value (a `_c{i}` var, or a Case that projects a super field) and
            // pull the method out of it. Methods follow the leading super fields.
            other => {
                let mut binds = Vec::new();
                let dv = self.dict_value(other, &mut binds);
                let cls = &self.checked.classes[&class];
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
        }
    }

    // A constrained global at value position: a closure that captures the
    // resolved dictionaries.
    pub(super) fn constrained_value(&mut self, name: &str, id: NodeId) -> Result<Comp, Error> {
        let ds = self.dicts.get(&id).cloned().ok_or_else(|| {
            Error::Ice(format!("no dictionary resolution for `{name}` at {id:?}"))
        })?;
        if let Some((class, idx)) = self.checked.methods.get(&Sym::from(name)).copied() {
            let (_, arity) = self.method_sig(class, idx);
            let ps: Vec<String> = (0..arity).map(|i| format!("_p{i}")).collect();
            let vals = ps.iter().map(|p| Value::Var(p.clone().into())).collect();
            let body = self.method_invoke(class, idx, &ds[0], vals);
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
        let mut all: Vec<Value> = ds.iter().map(|d| self.dict_value(d, &mut binds)).collect();
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
            let (_, arity) = self.method_sig(class, idx);
            if vals.len() == arity {
                return Ok(self.method_invoke(class, idx, &ds[0], vals));
            }
        } else if let Some(n) = self.arity.get(name).copied() {
            if vals.len() == n {
                let mut all: Vec<Value> = ds.iter().map(|d| self.dict_value(d, binds)).collect();
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
            Some(BuiltinKind::Print) => Comp::Print(first(args)),
            Some(BuiltinKind::Println) => Comp::Bind(
                Box::new(Comp::Print(first(args))),
                "_".into(),
                Box::new(Comp::PrintNl),
            ),
            Some(BuiltinKind::ReadInt) => Comp::ReadInt,
            Some(BuiltinKind::ReadLine) => Comp::ReadLine,
            Some(BuiltinKind::Rand) => Comp::Rand,
            Some(BuiltinKind::Srand) => Comp::Srand(first(args)),
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

// The native-sort key for a `sort`/`sort_by_ord` call, or `None` to keep the
// generic path. Matches the canonical primitive `Ord` instances by name so a
// user instance with a different ordering is never silently specialized; the
// dict must be a concrete instance with no superclass context. The kind tags
// match `prism_sort_prim`: 0 Integer, 1 I64, 2 U64, 3 Float.
fn sort_kind(name: &str, ds: &[Dict]) -> Option<i64> {
    if name != "sort" && name != "sort_by_ord" {
        return None;
    }
    let [Dict::Global(inst, ctxs)] = ds else {
        return None;
    };
    if !ctxs.is_empty() {
        return None;
    }
    match inst.as_str() {
        "ordInt" => Some(0),
        "ordI64" => Some(1),
        "ordU64" => Some(2),
        "ordFloat" => Some(3),
        _ => None,
    }
}
