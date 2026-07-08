use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::env::{collect_row_vars, collect_type_vars, convert_data, wrap_forall};
use super::{
    Canon, ClassInfo, CtorInfo, DataInfo, Dict, Env, HeadKey, InstInfo, InstKeys, Tc, Wanted,
    Warning,
};
use crate::error::TypeError;
use crate::names::{dict_ctor, module_of};
use crate::sym::Sym;
use crate::syntax::ast::{self, Core, NodeId, Program};
use crate::types::ty::{EffRow, Kind, Type};
use crate::types::{EQ_CLASS, ORD_CLASS, SHOW_CLASS};

// Cap on recursive instance resolution: a cyclic or diverging instance set
// reports an error instead of overflowing the stack.
const MAX_INSTANCE_DEPTH: usize = 32;

impl Tc<'_> {
    // Instantiate a constrained scheme with fresh existentials and record the
    // wanted constraints for end-of-declaration resolution.
    pub(super) fn instantiate_constrained(
        &mut self,
        scheme: &Type,
        cs: &[(Sym, Type)],
        id: NodeId,
        span: Span,
        explicit: Option<&[String]>,
    ) -> Type {
        let mut body = scheme.clone();
        let mut subs: Vec<(Sym, Type)> = Vec::new();
        let mut row_subs: Vec<(Sym, EffRow)> = Vec::new();
        loop {
            match body {
                Type::Forall(n, b) => {
                    let e = self.push_ex();
                    subs.push((n, Type::Exist(e)));
                    body = *b;
                }
                Type::RowForall(n, b) => {
                    let r = self.push_ex_row();
                    row_subs.push((n, EffRow::Exist(r)));
                    body = *b;
                }
                other => {
                    body = other;
                    break;
                }
            }
        }
        for (n, t) in &subs {
            body = body.subst_var(*n, t);
        }
        for (n, r) in &row_subs {
            body = body.subst_row_var(*n, r);
        }
        let items: Vec<_> = cs
            .iter()
            .enumerate()
            .map(|(i, (class, cty))| {
                let mut ct = cty.clone();
                for (n, t) in &subs {
                    ct = ct.subst_var(*n, t);
                }
                (class.to_string(), ct, explicit.map(|ns| ns[i].clone()))
            })
            .collect();
        if !items.is_empty() {
            self.wanted.push(Wanted { id, span, items });
        }
        body
    }

    pub(super) fn resolve_all(&mut self) -> Result<(), TypeError> {
        // Resolve deferred indexed reads/writes before everything else: by now a
        // `var`'s state existential is solved by its initializer, so the
        // receiver's head type is known. Dispatch it, constrain the key/element
        // (and value, for a write), and solve the read's result existential.
        for op in std::mem::take(&mut self.index_ops) {
            let recv = self.apply(&op.recv);
            let Some((kty, elem, writable)) = super::infer::index_container(&recv) else {
                return Err(TypeError::Other {
                    span: op.recv_span,
                    msg: format!("type `{}` is not indexable with `[]`", recv.show()),
                });
            };
            let elem = self.apply(&elem);
            self.subtype(&op.key, &kty).map_err(|e| e.at(op.span))?;
            self.subtype(&Type::Exist(op.result), &elem)
                .map_err(|e| e.at(op.span))?;
            if let Some(val) = op.val {
                if !writable {
                    return Err(TypeError::Other {
                        span: op.recv_span,
                        msg: format!(
                            "type `{}` does not support indexed assignment `a[i] := v`",
                            recv.show()
                        ),
                    });
                }
                self.subtype(&val, &elem).map_err(|e| e.at(op.span))?;
            }
        }
        // Resolve deferred numeric/comparison operands next, so dictionary
        // resolution below sees their final types. Arithmetic leftovers default
        // to `Int`; Eq/Ord leftovers either select a primitive lane or raise the
        // corresponding class obligation on the final non-primitive type.
        for (id, span, t, class) in std::mem::take(&mut self.num_default) {
            let t = self.apply(&t);
            if let Some(class) = class {
                match (&t, class) {
                    (Type::Int, _) => {}
                    (Type::I64 | Type::U64, _)
                    | (Type::Float, EQ_CLASS | ORD_CLASS)
                    | (Type::Bool | Type::Str, EQ_CLASS) => {
                        self.fixed.insert(id, t);
                    }
                    (Type::Exist(_), _) => {
                        self.default_numeric(&t, span)?;
                    }
                    _ => {
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(class.into(), t, None)],
                        });
                    }
                }
            } else {
                match &t {
                    Type::Int => {}
                    // `Float` joined the arithmetic operators with the tower, so a
                    // deferred operand that resolved to it is recorded like a
                    // fixed-width lane rather than rejected.
                    Type::I64 | Type::U64 | Type::Float => {
                        self.fixed.insert(id, t);
                    }
                    other => {
                        self.default_numeric(other, span)?;
                    }
                }
            }
        }
        // Unary-minus operands still ambiguous: negation admits `Float` (unlike
        // the integer operators above), records `I64`/`Float` for the elaborator,
        // rejects unsigned `U64`, and lets a leftover existential default to `Int`.
        for (id, span, t) in std::mem::take(&mut self.neg_default) {
            let t = self.apply(&t);
            match &t {
                Type::Int => {}
                Type::I64 | Type::Float => {
                    self.fixed.insert(id, t);
                }
                Type::U64 => return Err(Self::neg_unsigned(span)),
                other => {
                    self.default_numeric(other, span)?;
                }
            }
        }
        let wanted = std::mem::take(&mut self.wanted);
        for w in wanted {
            let mut ds = Vec::new();
            for (class, ty, explicit) in &w.items {
                let t = self.apply(ty);
                ds.push(self.resolve(class, &t, w.span, explicit.as_deref(), &[])?);
            }
            match self.dicts.get(&w.id) {
                Some(prev) if *prev != ds => {
                    return Err(TypeError::Ice {
                        msg: format!("conflicting dict records at {:?}", w.span),
                    })
                }
                Some(_) => {}
                None => {
                    self.dicts.insert(w.id, ds);
                }
            }
        }
        Ok(())
    }

    fn resolve(
        &mut self,
        class: &str,
        t: &Type,
        span: Span,
        explicit: Option<&str>,
        chain: &[(String, Type)],
    ) -> Result<Dict, TypeError> {
        // Two distinct non-termination modes. A *cycle* is when an identical goal
        // reappears on the resolution stack (`Eq(Foo)` needing `Eq(Bar)` needing
        // `Eq(Foo)`); that is a genuine program error and reported precisely. A
        // goal that keeps *growing* without repeating (`C(a)` :- `C([a])` :-
        // `C([[a]])`) never recurs exactly, so no cycle check can catch it; the
        // depth bound is the standard fuel backstop.
        let goal = (class.to_string(), t.clone());
        if chain.contains(&goal) {
            return Err(TypeError::Other {
                span,
                msg: format!(
                    "cyclic instance resolution: {class}({}) depends on itself",
                    t.show()
                ),
            });
        }
        if chain.len() > MAX_INSTANCE_DEPTH {
            return Err(TypeError::Other {
                span,
                msg: format!("instance resolution for {class}({}) is too deep", t.show()),
            });
        }
        let inst_name = if let Some(name) = explicit {
            let info = self
                .instances
                .get(&Sym::from(name))
                .ok_or_else(|| TypeError::Other {
                    span,
                    msg: format!("unknown instance `{name}`"),
                })?;
            if info.class.as_str() != class {
                return Err(TypeError::Other {
                    span,
                    msg: format!(
                        "instance `{name}` is for class {}, expected {class}",
                        info.class
                    ),
                });
            }
            name.to_string()
        } else {
            let cur_constraints = self
                .cur_self
                .as_ref()
                .map(|s| s.constraints.clone())
                .unwrap_or_default();
            for (i, (cclass, cty)) in cur_constraints.iter().enumerate() {
                if cclass == class && self.apply(cty) == *t {
                    return Ok(Dict::Param(i));
                }
            }
            // No direct constraint, but a `given D(t)` whose class D has `class`
            // among its (transitive) superclasses entails it: project the super
            // dictionary out of D's param dict cell.
            for (i, (cclass, cty)) in cur_constraints.iter().enumerate() {
                if self.apply(cty) == *t {
                    if let Some(path) = self.super_path(cclass, class) {
                        let mut d = Dict::Param(i);
                        for (sub, idx) in path {
                            d = Dict::Super(Box::new(d), sub, idx);
                        }
                        return Ok(d);
                    }
                }
            }
            // A tuple has no nominal head to key an instance on, so its `Show`
            // dictionary is synthesized from the component `Show` dictionaries.
            if class == SHOW_CLASS {
                if let Type::Tuple(elems) = t {
                    let mut child = chain.to_vec();
                    child.push(goal);
                    let comps = elems
                        .iter()
                        .map(|e| {
                            let e = self.apply(e);
                            self.resolve(class, &e, span, None, &child)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(Dict::Tuple(comps));
                }
            }
            let key = Self::head_key(class, t, span)?;
            match self
                .inst_keys
                .get(&(Sym::from(class), key.clone()))
                .map(Vec::as_slice)
            {
                Some([one]) => one.to_string(),
                Some(many @ [_, _, ..]) => {
                    // Several instances share this head, so implicit resolution
                    // uses the canonical designation. Coherence checking rejects
                    // 2+ undesignated instances at definition, so a missing entry
                    // here is a backstop, not a reachable user error.
                    let Some(name) = self.canonical.get(&(Sym::from(class), key)) else {
                        let listed = provenance_list(self.instances, many);
                        return Err(TypeError::Other {
                            span,
                            msg: format!(
                                "ambiguous instance for {class}({h}): {listed}; \
                                 designate one with `canonical {class}({h}) = name`",
                                h = t.show(),
                            ),
                        });
                    };
                    name.to_string()
                }
                _ => {
                    return Err(TypeError::Other {
                        span,
                        msg: format!("no instance for {class}({})", t.show()),
                    })
                }
            }
        };
        let info = self.instances[&Sym::from(&inst_name)].clone();
        let mut vars = BTreeSet::new();
        collect_type_vars(&info.head, &mut vars);
        let subs: Vec<(Sym, Type)> = vars
            .into_iter()
            .map(|v| (v, Type::Exist(self.push_ex())))
            .collect();
        let mut head = info.head.clone();
        for (n, x) in &subs {
            head = head.subst_var(*n, x);
        }
        self.equate(t, &head).map_err(|e| {
            e.or(TypeError::Other {
                span,
                msg: format!(
                    "instance `{inst_name}` : {class}({}) does not match {}",
                    info.head.show(),
                    t.show()
                ),
            })
        })?;
        // This goal joins the resolution stack while we discharge its context and
        // superclass obligations, so a child that asks for it again is a cycle.
        let mut child = chain.to_vec();
        child.push(goal);
        let mut ctx_dicts = Vec::new();
        for (cclass, cty) in &info.context {
            let mut ct = cty.clone();
            for (n, x) in &subs {
                ct = ct.subst_var(*n, x);
            }
            let ct = self.apply(&ct);
            ctx_dicts.push(self.resolve(cclass.as_str(), &ct, span, None, &child)?);
        }
        // Superclass dictionaries follow the declared context, in the same order
        // the instance constructor lays them out as leading dict-cell fields.
        for (sclass, sty) in &info.supers {
            let mut st = sty.clone();
            for (n, x) in &subs {
                st = st.subst_var(*n, x);
            }
            let st = self.apply(&st);
            ctx_dicts.push(self.resolve(sclass.as_str(), &st, span, None, &child)?);
        }
        Ok(Dict::Global(inst_name, ctx_dicts))
    }

    // The field-index path projecting class `want` out of a `from` dictionary
    // via superclasses, or `None` if `want` is not a superclass of `from`. Each
    // step names the class whose dict cell is being projected and the leading
    // field index of the superclass within it.
    fn super_path(&self, from: &str, want: &str) -> Option<Vec<(String, usize)>> {
        self.super_path_d(from, want, 0)
    }

    // `build_classes` already rejects superclass cycles, so this never loops in
    // practice; the depth bound is a defensive backstop that degrades to `None`
    // rather than overflowing if a cycle ever slips through.
    fn super_path_d(&self, from: &str, want: &str, depth: usize) -> Option<Vec<(String, usize)>> {
        if depth > MAX_INSTANCE_DEPTH {
            return None;
        }
        let info = self.classes.get(&Sym::from(from))?;
        for (idx, s) in info.supers.iter().enumerate() {
            if s.as_str() == want {
                return Some(vec![(from.to_string(), idx)]);
            }
            if let Some(mut rest) = self.super_path_d(s.as_str(), want, depth + 1) {
                rest.insert(0, (from.to_string(), idx));
                return Some(rest);
            }
        }
        None
    }

    fn head_key(class: &str, t: &Type, span: Span) -> Result<HeadKey, TypeError> {
        head_name(t).ok_or_else(|| {
            let msg = match t {
                Type::Exist(_) => format!(
                    "cannot infer the type for constraint {class}(_); add a type annotation"
                ),
                Type::Var(v) => format!(
                    "cannot discharge constraint {class}({v}); add `given {class}({v})` to the enclosing function"
                ),
                other => format!("no instance for {class}({})", other.show()),
            };
            TypeError::Other { span, msg }
        })
    }
}

type BuildClassResult = (
    BTreeMap<Sym, ClassInfo>,
    BTreeMap<Sym, InstInfo>,
    InstKeys,
    Canon,
    BTreeMap<Sym, (Sym, usize)>,
    BTreeMap<Sym, (Type, Vec<(Sym, Type)>)>,
    Vec<Warning>,
);

const fn head_name(t: &Type) -> Option<HeadKey> {
    match t {
        Type::Int => Some(HeadKey::Int),
        Type::I64 => Some(HeadKey::I64),
        Type::U64 => Some(HeadKey::U64),
        Type::Bool => Some(HeadKey::Bool),
        Type::Float => Some(HeadKey::Float),
        Type::Char => Some(HeadKey::Char),
        Type::Str => Some(HeadKey::Str),
        Type::Unit => Some(HeadKey::Unit),
        Type::Con(n, _) => Some(HeadKey::Con(*n)),
        Type::Tuple(elems) => Some(HeadKey::Tuple(elems.len())),
        _ => None,
    }
}

// Reject a cyclic superclass hierarchy (`class A given B`, `class B given A`)
// with a readable path instead of letting `super_path` overflow the stack at the
// first use site. Three-color DFS; a gray (on-stack) target is a back edge.
fn check_superclass_cycles(
    classes: &BTreeMap<Sym, ClassInfo>,
    decls: &[ast::ClassDecl],
) -> Result<(), TypeError> {
    fn dfs<'a>(
        node: &'a str,
        classes: &'a BTreeMap<Sym, ClassInfo>,
        color: &mut BTreeMap<&'a str, u8>,
        path: &mut Vec<&'a str>,
    ) -> Option<Vec<String>> {
        color.insert(node, 1);
        path.push(node);
        if let Some(info) = classes.get(&Sym::from(node)) {
            for s in &info.supers {
                if !classes.contains_key(s) {
                    continue;
                }
                let skey: &str = s.as_str();
                match color.get(skey).copied().unwrap_or(0) {
                    1 => {
                        let from = path.iter().position(|p| *p == skey).unwrap_or(0);
                        let mut cyc: Vec<String> =
                            path[from..].iter().map(|p| (*p).to_string()).collect();
                        cyc.push(skey.to_string());
                        return Some(cyc);
                    }
                    0 => {
                        if let Some(cyc) = dfs(skey, classes, color, path) {
                            return Some(cyc);
                        }
                    }
                    _ => {}
                }
            }
        }
        path.pop();
        color.insert(node, 2);
        None
    }
    let mut color: BTreeMap<&str, u8> = BTreeMap::new();
    // `Sym` keys order by intern id; sort on the name so the reported cycle is
    // deterministic when several independent cycles exist.
    let mut starts: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
    starts.sort_unstable();
    for start in starts {
        if color.get(start).copied().unwrap_or(0) != 0 {
            continue;
        }
        let mut path = Vec::new();
        if let Some(cyc) = dfs(start, classes, &mut color, &mut path) {
            let span = decls
                .iter()
                .find(|d| cyc.contains(&d.name))
                .map_or_else(Span::default, |d| d.span);
            return Err(TypeError::Other {
                span,
                msg: format!("superclass cycle: {}", cyc.join(" -> ")),
            });
        }
    }
    Ok(())
}

pub(super) fn build_classes(
    prog: &Program<Core>,
    data: &mut BTreeMap<String, DataInfo>,
    ctors: &mut BTreeMap<String, CtorInfo>,
    env: &mut Env,
) -> Result<BuildClassResult, TypeError> {
    let fn_names: BTreeSet<&str> = prog.fns.iter().map(|d| d.name.as_str()).collect();
    let mut classes: BTreeMap<Sym, ClassInfo> = BTreeMap::new();
    let mut instances: BTreeMap<Sym, InstInfo> = BTreeMap::new();
    let mut inst_keys = InstKeys::new();
    let mut warnings: Vec<Warning> = Vec::new();
    let mut methods: BTreeMap<Sym, (Sym, usize)> = BTreeMap::new();
    let mut constrained: BTreeMap<Sym, (Type, Vec<(Sym, Type)>)> = BTreeMap::new();
    for c in &prog.classes {
        if classes.contains_key(&Sym::from(&c.name)) {
            return Err(TypeError::Other {
                span: c.span,
                msg: format!("duplicate class {}", c.name),
            });
        }
        let mut infos = Vec::new();
        for (idx, (mname, sig)) in c.methods.iter().enumerate() {
            let t = convert_data(sig);
            if !matches!(t, Type::Fun(..)) {
                return Err(TypeError::Other {
                    span: c.span,
                    msg: format!("class method `{mname}` must have a function type"),
                });
            }
            let mut vars = BTreeSet::new();
            collect_type_vars(&t, &mut vars);
            if !vars.contains(&Sym::from(&c.param)) {
                return Err(TypeError::Other {
                    span: c.span,
                    msg: format!(
                        "class method `{mname}` must mention the class parameter `{}`",
                        c.param
                    ),
                });
            }
            if env.contains_key(&Sym::from(mname))
                || methods.contains_key(&Sym::from(mname))
                || fn_names.contains(mname.as_str())
            {
                return Err(TypeError::Other {
                    span: c.span,
                    msg: format!("class method `{mname}` clashes with an existing definition"),
                });
            }
            let sorted: Vec<Sym> = vars.into_iter().collect();
            let scheme = quantify(&t, &sorted);
            env.insert(Sym::from(mname), scheme.clone());
            methods.insert(Sym::from(mname), (Sym::from(&c.name), idx));
            constrained.insert(
                Sym::from(mname),
                (
                    scheme,
                    vec![(Sym::from(&c.name), Type::Var(Sym::from(&c.param)))],
                ),
            );
            infos.push((Sym::from(mname), t));
        }
        let dname = dict_ctor(&c.name);
        // The dictionary cell is structurally typed, not a row of placeholders:
        // a leading field per superclass (that class's dictionary over the same
        // parameter), then one field per method carrying the method's own type
        // generalized over its type/row variables, with the class parameter left
        // free as the dictionary's parameter.
        let param = Sym::from(&c.param);
        let mut dict_args: Vec<Type> = c
            .supers
            .iter()
            .map(|s| Type::Con(Sym::from(&dict_ctor(s)), vec![Type::Var(param)]))
            .collect();
        for (_, mt) in &infos {
            let mut tvars = BTreeSet::new();
            collect_type_vars(mt, &mut tvars);
            tvars.remove(&param);
            let scheme = quantify(mt, &tvars.into_iter().collect::<Vec<_>>());
            dict_args.push(scheme);
        }
        data.insert(
            dname.clone(),
            DataInfo {
                params: vec![c.param.clone()],
                param_kinds: vec![Kind::Type],
                ctors: vec![dname.clone()],
            },
        );
        ctors.insert(
            dname.clone(),
            CtorInfo {
                type_name: Sym::from(&dname),
                params: vec![param],
                param_kinds: vec![Kind::Type],
                args: dict_args,
                tag: 0,
                fields: vec![],
            },
        );
        classes.insert(
            Sym::from(&c.name),
            ClassInfo {
                param: Sym::from(&c.param),
                supers: c.supers.iter().map(Sym::from).collect(),
                methods: infos,
            },
        );
    }
    // Superclass edges may point forward, so the cycle check waits until every
    // class is registered. A cyclic hierarchy would otherwise send `super_path`
    // into unbounded recursion at the first use site.
    check_superclass_cycles(&classes, &prog.classes)?;
    for i in &prog.instances {
        let class = classes
            .get(&Sym::from(&i.class))
            .ok_or_else(|| TypeError::Other {
                span: i.span,
                msg: format!("unknown class {}", i.class),
            })?;
        if instances.contains_key(&Sym::from(&i.name))
            || env.contains_key(&Sym::from(&i.name))
            || fn_names.contains(i.name.as_str())
        {
            return Err(TypeError::Other {
                span: i.span,
                msg: format!(
                    "instance name `{}` clashes with an existing definition",
                    i.name
                ),
            });
        }
        let (head, key, head_vars) = convert_instance_head(i, data)?;
        let context = instance_context(i, &classes, &head_vars)?;
        check_instance_methods(class, i)?;
        // Each declared superclass of the class becomes an obligation `S(head)`
        // discharged at every use site and embedded as a leading dict field.
        let mut supers = Vec::new();
        for s in &class.supers {
            if !classes.contains_key(s) {
                return Err(TypeError::Other {
                    span: i.span,
                    msg: format!("class {} names unknown superclass {s}", i.class),
                });
            }
            supers.push((*s, head.clone()));
        }
        if let Some(w) = orphan_warning(i, &head) {
            warnings.push(w);
        }
        inst_keys
            .entry((Sym::from(&i.class), key))
            .or_default()
            .push(Sym::from(&i.name));
        instances.insert(
            Sym::from(&i.name),
            InstInfo {
                class: Sym::from(&i.class),
                head,
                module: i.module.clone(),
                context,
                supers,
            },
        );
    }
    let canonical = build_canonical(prog, &inst_keys, &instances)?;
    Ok((
        classes,
        instances,
        inst_keys,
        canonical,
        methods,
        constrained,
        warnings,
    ))
}

// An instance head must be a primitive or a data-type constructor applied to
// distinct type variables. Returns the converted head, its store key, and the
// head's variable set (the only variables an instance context may constrain).
fn convert_instance_head(
    i: &ast::InstanceDecl<Core>,
    data: &BTreeMap<String, DataInfo>,
) -> Result<(Type, HeadKey, BTreeSet<Sym>), TypeError> {
    let head = convert_data(&i.head);
    let key = head_name(&head).ok_or_else(|| TypeError::Other {
        span: i.span,
        msg: "instance head must be a primitive type or a data type constructor".to_string(),
    })?;
    // Both a data-type head `T(a, b)` and a tuple head `(a, b)` carry argument
    // slots that must be distinct type variables; a tuple has no nominal name to
    // check against `data`, a `Con` does.
    let args: &[Type] = match &head {
        Type::Con(n, args) => {
            if !data.contains_key(n.as_str()) {
                return Err(TypeError::Other {
                    span: i.span,
                    msg: format!("unknown type {n}"),
                });
            }
            args
        }
        Type::Tuple(args) => args,
        _ => &[],
    };
    let mut head_vars = BTreeSet::new();
    for a in args {
        match a {
            Type::Var(v) if !head_vars.contains(v) => {
                head_vars.insert(*v);
            }
            _ => {
                return Err(TypeError::Other {
                    span: i.span,
                    msg: "instance head arguments must be distinct type variables".to_string(),
                })
            }
        }
    }
    Ok((head, key, head_vars))
}

// An instance context may constrain only the head's type variables. Returns the
// resolved `(class, type)` obligations.
fn instance_context(
    i: &ast::InstanceDecl<Core>,
    classes: &BTreeMap<Sym, ClassInfo>,
    head_vars: &BTreeSet<Sym>,
) -> Result<Vec<(Sym, Type)>, TypeError> {
    let mut context = Vec::new();
    for ct in &i.context {
        if !classes.contains_key(&Sym::from(&ct.class)) {
            return Err(TypeError::Other {
                span: ct.span,
                msg: format!("unknown class {}", ct.class),
            });
        }
        match &ct.ty {
            ast::Ty::Var(v) if head_vars.contains(&Sym::from(v)) => {
                context.push((Sym::from(&ct.class), Type::Var(Sym::from(v))));
            }
            _ => {
                return Err(TypeError::Other {
                    span: ct.span,
                    msg: "instance context constraints must be over the head's type variables"
                        .to_string(),
                })
            }
        }
    }
    Ok(context)
}

// Validate an instance's method block against its class: no duplicates, every
// method belongs to the class, signatures are inherited (no annotations), arity
// matches, and no class method is left unimplemented.
fn check_instance_methods(class: &ClassInfo, i: &ast::InstanceDecl<Core>) -> Result<(), TypeError> {
    let mut seen = BTreeSet::new();
    for m in &i.methods {
        if !seen.insert(Sym::from(&m.name)) {
            return Err(TypeError::Other {
                span: m.span,
                msg: format!("duplicate method `{}` in instance `{}`", m.name, i.name),
            });
        }
        let Some((_, sig)) = class
            .methods
            .iter()
            .find(|(n, _)| n.as_str() == m.name.as_str())
        else {
            return Err(TypeError::Other {
                span: m.span,
                msg: format!("class {} has no method `{}`", i.class, m.name),
            });
        };
        if m.params.iter().any(|p| p.ty.is_some())
            || m.ret.is_some()
            || m.eff.is_some()
            || !m.constraints.is_empty()
        {
            return Err(TypeError::Other {
                span: m.span,
                msg: format!(
                    "instance method `{}` takes its signature from class {}; drop the annotations",
                    m.name, i.class
                ),
            });
        }
        let arity = match sig {
            Type::Fun(doms, _, _) => doms.len(),
            _ => 0,
        };
        if m.params.len() != arity {
            return Err(TypeError::Other {
                span: m.span,
                msg: format!(
                    "method `{}` of class {} takes {arity} parameter(s), got {}",
                    m.name,
                    i.class,
                    m.params.len()
                ),
            });
        }
    }
    let missing: Vec<&str> = class
        .methods
        .iter()
        .filter(|(n, _)| !seen.contains(n))
        .map(|(n, _)| n.as_str())
        .collect();
    if !missing.is_empty() {
        return Err(TypeError::Other {
            span: i.span,
            msg: format!(
                "instance `{}` is missing method(s): {}",
                i.name,
                missing.join(", ")
            ),
        });
    }
    Ok(())
}

// The orphan rule: an instance must be anchored to the module that defines its
// class or its head type. Returns a warning when it is anchored to neither
// (primitive heads count as prelude-defined). Once packages and separate
// compilation land, a cross-package orphan becomes an error.
fn orphan_warning(i: &ast::InstanceDecl<Core>, head: &Type) -> Option<Warning> {
    let inst_mod = i.module.as_str();
    let class_mod = module_of(&i.class);
    let head_mod = match head {
        Type::Con(n, _) => module_of(n.as_str()),
        _ => "",
    };
    if class_mod == inst_mod || head_mod == inst_mod {
        return None;
    }
    let where_ = if inst_mod.is_empty() {
        "this program".to_string()
    } else {
        format!("module `{inst_mod}`")
    };
    // A root-program instance's span indexes the entry source, so it can carry a
    // caret; an imported module's span belongs to another file, so leave it empty
    // and the warning renders as a plain line.
    let span = if inst_mod.is_empty() {
        i.span
    } else {
        Span::default()
    };
    Some(Warning {
        span,
        msg: format!(
            "orphan instance `{}` for {}({}): neither the class nor the type is \
             defined in {where_}; define it alongside the class or the type",
            i.name,
            i.class,
            head.show()
        ),
    })
}

// Build the canonical-instance store from `canonical Class(Head) = name` decls
// and enforce coherence. Each designation must name a registered instance for
// its `(class, head)` and may appear once; then every head shared by two or more
// instances must have a designation, else implicit resolution would be ambient.
// The error is raised at definition, not deferred to each use site.
fn build_canonical(
    prog: &Program<Core>,
    inst_keys: &InstKeys,
    instances: &BTreeMap<Sym, InstInfo>,
) -> Result<Canon, TypeError> {
    let mut canonical: Canon = BTreeMap::new();
    for c in &prog.canonicals {
        let head = convert_data(&c.head);
        let key = head_name(&head).ok_or_else(|| TypeError::Other {
            span: c.span,
            msg: "canonical head must be a primitive type or a data type constructor".to_string(),
        })?;
        let registered = inst_keys
            .get(&(Sym::from(&c.class), key.clone()))
            .is_some_and(|ns| ns.contains(&Sym::from(&c.name)));
        if !registered {
            return Err(TypeError::Other {
                span: c.span,
                msg: format!(
                    "`{}` is not an instance of {}({})",
                    c.name,
                    c.class,
                    head.show()
                ),
            });
        }
        if canonical
            .insert((Sym::from(&c.class), key), Sym::from(&c.name))
            .is_some()
        {
            return Err(TypeError::Other {
                span: c.span,
                msg: format!(
                    "duplicate canonical designation for {}({})",
                    c.class,
                    head.show()
                ),
            });
        }
    }
    // Iterate in name order: `Sym` keys order by intern id, so sort on the class
    // name to keep the chosen diagnostic deterministic across runs.
    let mut entries: Vec<_> = inst_keys.iter().collect();
    entries.sort_by_key(|((class, key), _)| (class.as_str(), key.clone()));
    for ((class, key), names) in entries {
        if names.len() < 2 || canonical.contains_key(&(*class, key.clone())) {
            continue;
        }
        let head = instances
            .get(&names[0])
            .map(|i| i.head.show())
            .unwrap_or_default();
        // Caret a root-local instance decl when one exists; an imported decl's
        // span belongs to another file, so fall back to a plain line.
        let span = prog
            .instances
            .iter()
            .find(|i| names.contains(&Sym::from(&i.name)) && i.module.is_empty())
            .map_or_else(Span::default, |i| i.span);
        return Err(TypeError::Other {
            span,
            msg: format!(
                "{n} instances for {class}({head}): {listed}; \
                 designate one with `canonical {class}({head}) = name`",
                n = names.len(),
                listed = provenance_list(instances, names),
            ),
        });
    }
    Ok(canonical)
}

// Generalize a method/dictionary-field type over the given type variables and,
// additionally, over every effect-row variable it mentions, so an effect-
// polymorphic method (`fmap : (.. ! {e}, ..) -> .. ! {e}`) is row-polymorphic
// rather than carrying a free row var.
fn quantify(ty: &Type, tvars: &[Sym]) -> Type {
    let mut scheme = wrap_forall(tvars, ty.clone());
    let mut rvars = BTreeSet::new();
    collect_row_vars(ty, &mut rvars);
    for rv in rvars {
        scheme = Type::RowForall(rv, Box::new(scheme));
    }
    scheme
}

/// Render a list of instance names with their defining module, for overlap and
/// ambiguity diagnostics: `` `eqStack` (module `Data.Stack`), `eqRev` (this
/// program) ``.
fn provenance_list(instances: &BTreeMap<Sym, InstInfo>, names: &[Sym]) -> String {
    names
        .iter()
        .map(|n| match instances.get(n).map(|i| i.module.as_str()) {
            Some(m) if !m.is_empty() => format!("`{n}` (module `{m}`)"),
            _ => format!("`{n}` (this program)"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}
