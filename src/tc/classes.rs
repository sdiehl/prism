use std::collections::{BTreeMap, BTreeSet};

use marginalia::Span;

use super::env::{collect_row_vars, collect_type_vars, convert_data, wrap_forall};
use super::{
    ClassInfo, CtorInfo, DataInfo, Dict, Env, HeadKey, InstInfo, InstKeys, Tc, Wanted, Warning,
};
use crate::error::TypeError;
use crate::names::{dict_ctor, module_of};
use crate::sym::Sym;
use crate::syntax::ast::{self, Core, Program};
use crate::types::ty::{EffRow, Type};

// Cap on recursive instance resolution: a cyclic or diverging instance set
// reports an error instead of overflowing the stack.
const MAX_INSTANCE_DEPTH: usize = 32;

impl Tc<'_> {
    // Instantiate a constrained scheme with fresh existentials and record the
    // wanted constraints for end-of-declaration resolution.
    pub(super) fn instantiate_constrained(
        &mut self,
        scheme: &Type,
        cs: &[(String, Type)],
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
                (class.clone(), ct, explicit.map(|ns| ns[i].clone()))
            })
            .collect();
        if !items.is_empty() {
            self.wanted.push(Wanted { span, items });
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
        // Resolve deferred numeric operands next, so dictionary resolution below
        // sees their final types. An operand a later use already pinned to a
        // fixed-width lane is recorded; one still ambiguous defaults to `Int`; a
        // `Float` or non-numeric one (an int operator on a float) is rejected.
        for (span, t) in std::mem::take(&mut self.num_default) {
            let t = self.apply(&t);
            match &t {
                Type::Int => {}
                Type::I64 | Type::U64 => {
                    self.fixed.insert(span, t);
                }
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
                ds.push(self.resolve(class, &t, w.span, explicit.as_deref(), 0)?);
            }
            match self.dicts.get(&w.span) {
                Some(prev) if *prev != ds => {
                    return Err(TypeError::Ice {
                        msg: format!("conflicting dict records at {:?}", w.span),
                    })
                }
                Some(_) => {}
                None => {
                    self.dicts.insert(w.span, ds);
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
        depth: usize,
    ) -> Result<Dict, TypeError> {
        if depth > MAX_INSTANCE_DEPTH {
            return Err(TypeError::Other {
                span,
                msg: format!("instance resolution for {class}({}) is too deep", t.show()),
            });
        }
        let inst_name = if let Some(name) = explicit {
            let info = self.instances.get(name).ok_or_else(|| TypeError::Other {
                span,
                msg: format!("unknown instance `{name}`"),
            })?;
            if info.class != class {
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
            let key = Self::head_key(class, t, span)?;
            match self
                .inst_keys
                .get(&(class.to_string(), key))
                .map(Vec::as_slice)
            {
                Some([one]) => one.clone(),
                Some(many @ [_, _, ..]) => {
                    // Name the defining module of each candidate when they span
                    // more than one; for purely root-local named instances the
                    // bare list is clearer (and keeps the message stable).
                    let cross_module = many
                        .iter()
                        .filter_map(|n| self.instances.get(n))
                        .any(|i| !i.module.is_empty());
                    let listed = if cross_module {
                        provenance_list(self.instances, many)
                    } else {
                        many.join(", ")
                    };
                    return Err(TypeError::Other {
                        span,
                        msg: format!(
                            "ambiguous instance for {class}({}): {listed}; select one with f[name]",
                            t.show(),
                        ),
                    });
                }
                _ => {
                    return Err(TypeError::Other {
                        span,
                        msg: format!("no instance for {class}({})", t.show()),
                    })
                }
            }
        };
        let info = self.instances[&inst_name].clone();
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
        let mut ctx_dicts = Vec::new();
        for (cclass, cty) in &info.context {
            let mut ct = cty.clone();
            for (n, x) in &subs {
                ct = ct.subst_var(*n, x);
            }
            let ct = self.apply(&ct);
            ctx_dicts.push(self.resolve(cclass, &ct, span, None, depth + 1)?);
        }
        // Superclass dictionaries follow the declared context, in the same order
        // the instance constructor lays them out as leading dict-cell fields.
        for (sclass, sty) in &info.supers {
            let mut st = sty.clone();
            for (n, x) in &subs {
                st = st.subst_var(*n, x);
            }
            let st = self.apply(&st);
            ctx_dicts.push(self.resolve(sclass, &st, span, None, depth + 1)?);
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
        let info = self.classes.get(from)?;
        for (idx, s) in info.supers.iter().enumerate() {
            if s == want {
                return Some(vec![(from.to_string(), idx)]);
            }
            if let Some(mut rest) = self.super_path_d(s, want, depth + 1) {
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
                    "cannot discharge constraint {class}({v}); add `where {class}({v})` to the enclosing function"
                ),
                other => format!("no instance for {class}({})", other.show()),
            };
            TypeError::Other { span, msg }
        })
    }
}

type BuildClassResult = (
    BTreeMap<String, ClassInfo>,
    BTreeMap<String, InstInfo>,
    InstKeys,
    BTreeMap<String, (String, usize)>,
    BTreeMap<String, (Type, Vec<(String, Type)>)>,
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
        _ => None,
    }
}

// Reject a cyclic superclass hierarchy (`class A given B`, `class B given A`)
// with a readable path instead of letting `super_path` overflow the stack at the
// first use site. Three-color DFS; a gray (on-stack) target is a back edge.
fn check_superclass_cycles(
    classes: &BTreeMap<String, ClassInfo>,
    decls: &[ast::ClassDecl],
) -> Result<(), TypeError> {
    fn dfs<'a>(
        node: &'a str,
        classes: &'a BTreeMap<String, ClassInfo>,
        color: &mut BTreeMap<&'a str, u8>,
        path: &mut Vec<&'a str>,
    ) -> Option<Vec<String>> {
        color.insert(node, 1);
        path.push(node);
        if let Some(info) = classes.get(node) {
            for s in &info.supers {
                let Some((skey, _)) = classes.get_key_value(s.as_str()) else {
                    continue;
                };
                match color.get(skey.as_str()).copied().unwrap_or(0) {
                    1 => {
                        let from = path.iter().position(|p| *p == skey.as_str()).unwrap_or(0);
                        let mut cyc: Vec<String> =
                            path[from..].iter().map(|p| (*p).to_string()).collect();
                        cyc.push(skey.clone());
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
    for start in classes.keys() {
        if color.get(start.as_str()).copied().unwrap_or(0) != 0 {
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
    let mut classes: BTreeMap<String, ClassInfo> = BTreeMap::new();
    let mut instances: BTreeMap<String, InstInfo> = BTreeMap::new();
    let mut inst_keys = InstKeys::new();
    let mut warnings: Vec<Warning> = Vec::new();
    let mut methods: BTreeMap<String, (String, usize)> = BTreeMap::new();
    let mut constrained: BTreeMap<String, (Type, Vec<(String, Type)>)> = BTreeMap::new();
    for c in &prog.classes {
        if classes.contains_key(&c.name) {
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
                || methods.contains_key(mname)
                || fn_names.contains(mname.as_str())
            {
                return Err(TypeError::Other {
                    span: c.span,
                    msg: format!("class method `{mname}` clashes with an existing definition"),
                });
            }
            let sorted: Vec<Sym> = vars.into_iter().collect();
            let mut scheme = wrap_forall(&sorted, t.clone());
            // Generalize over the method's effect-row variables too, so an
            // effect-polymorphic method (`fmap : (.. ! {e}, ..) -> .. ! {e}`)
            // is row-polymorphic rather than carrying a free row var.
            let mut rvars = BTreeSet::new();
            collect_row_vars(&t, &mut rvars);
            for rv in rvars {
                scheme = Type::RowForall(rv, Box::new(scheme));
            }
            env.insert(Sym::from(mname), scheme.clone());
            methods.insert(mname.clone(), (c.name.clone(), idx));
            constrained.insert(
                mname.clone(),
                (
                    scheme,
                    vec![(c.name.clone(), Type::Var(Sym::from(&c.param)))],
                ),
            );
            infos.push((mname.clone(), t));
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
            let mut scheme = wrap_forall(&tvars.into_iter().collect::<Vec<_>>(), mt.clone());
            let mut rvars = BTreeSet::new();
            collect_row_vars(mt, &mut rvars);
            for rv in rvars {
                scheme = Type::RowForall(rv, Box::new(scheme));
            }
            dict_args.push(scheme);
        }
        data.insert(
            dname.clone(),
            DataInfo {
                params: vec![c.param.clone()],
                ctors: vec![dname.clone()],
            },
        );
        ctors.insert(
            dname.clone(),
            CtorInfo {
                type_name: Sym::from(&dname),
                params: vec![param],
                args: dict_args,
                tag: 0,
                fields: vec![],
            },
        );
        classes.insert(
            c.name.clone(),
            ClassInfo {
                param: c.param.clone(),
                supers: c.supers.clone(),
                methods: infos,
            },
        );
    }
    // Superclass edges may point forward, so the cycle check waits until every
    // class is registered. A cyclic hierarchy would otherwise send `super_path`
    // into unbounded recursion at the first use site.
    check_superclass_cycles(&classes, &prog.classes)?;
    for i in &prog.instances {
        let class = classes.get(&i.class).ok_or_else(|| TypeError::Other {
            span: i.span,
            msg: format!("unknown class {}", i.class),
        })?;
        if instances.contains_key(&i.name)
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
        let head = convert_data(&i.head);
        let key = head_name(&head).ok_or_else(|| TypeError::Other {
            span: i.span,
            msg: "instance head must be a primitive type or a data type constructor".to_string(),
        })?;
        let mut head_vars = BTreeSet::new();
        if let Type::Con(n, args) = &head {
            if !data.contains_key(n.as_str()) {
                return Err(TypeError::Other {
                    span: i.span,
                    msg: format!("unknown type {n}"),
                });
            }
            for a in args {
                match a {
                    Type::Var(v) if !head_vars.contains(v) => {
                        head_vars.insert(*v);
                    }
                    _ => {
                        return Err(TypeError::Other {
                            span: i.span,
                            msg: "instance head arguments must be distinct type variables"
                                .to_string(),
                        })
                    }
                }
            }
        }
        let mut context = Vec::new();
        for ct in &i.context {
            if !classes.contains_key(&ct.class) {
                return Err(TypeError::Other {
                    span: ct.span,
                    msg: format!("unknown class {}", ct.class),
                });
            }
            match &ct.ty {
                ast::Ty::Var(v) if head_vars.contains(&Sym::from(v)) => {
                    context.push((ct.class.clone(), Type::Var(Sym::from(v))));
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
        let mut seen = BTreeSet::new();
        for m in &i.methods {
            if !seen.insert(m.name.clone()) {
                return Err(TypeError::Other {
                    span: m.span,
                    msg: format!("duplicate method `{}` in instance `{}`", m.name, i.name),
                });
            }
            let Some((_, sig)) = class.methods.iter().find(|(n, _)| n == &m.name) else {
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
        let missing: Vec<String> = class
            .methods
            .iter()
            .map(|(n, _)| n.clone())
            .filter(|n| !seen.contains(n))
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
            supers.push((s.clone(), head.clone()));
        }
        // Orphan rule: an instance must be anchored to the module that defines
        // its class or its head type. Anywhere else it is an orphan, warned now
        // and (once packages and separate compilation land) an error across a
        // package boundary. Primitive heads count as prelude-defined.
        let inst_mod = i.module.as_str();
        let class_mod = module_of(&i.class);
        let head_mod = match &head {
            Type::Con(n, _) => module_of(n.as_str()),
            _ => "",
        };
        if class_mod != inst_mod && head_mod != inst_mod {
            let where_ = if inst_mod.is_empty() {
                "this program".to_string()
            } else {
                format!("module `{inst_mod}`")
            };
            // A root-program instance's span indexes the entry source, so it can
            // carry a caret; an imported module's span belongs to another file,
            // so leave it empty and the warning renders as a plain line.
            let span = if inst_mod.is_empty() {
                i.span
            } else {
                Span::default()
            };
            warnings.push(Warning {
                span,
                msg: format!(
                    "orphan instance `{}` for {}({}): neither the class nor the type is \
                     defined in {where_}; define it alongside the class or the type",
                    i.name,
                    i.class,
                    head.show()
                ),
            });
        }
        inst_keys
            .entry((i.class.clone(), key))
            .or_default()
            .push(i.name.clone());
        instances.insert(
            i.name.clone(),
            InstInfo {
                class: i.class.clone(),
                head,
                module: i.module.clone(),
                context,
                supers,
            },
        );
    }
    // Overlap: two or more instances for the same (class, head) are allowed (the
    // use site disambiguates with `f[name]`), but when they come from different
    // modules the conflict is invisible at definition time, so flag it. Instances
    // from a single module (or all root-local, the deliberate named-instance
    // case) are left alone.
    for ((class, _key), names) in &inst_keys {
        if names.len() < 2 {
            continue;
        }
        let mods: BTreeSet<&str> = names
            .iter()
            .filter_map(|n| instances.get(n))
            .map(|i| i.module.as_str())
            .collect();
        if mods.len() < 2 {
            continue;
        }
        warnings.push(Warning {
            span: Span::default(),
            msg: format!(
                "overlapping instances for {class}: {}; uses must disambiguate with f[name]",
                provenance_list(&instances, names)
            ),
        });
    }
    Ok((
        classes,
        instances,
        inst_keys,
        methods,
        constrained,
        warnings,
    ))
}

/// Render a list of instance names with their defining module, for overlap and
/// ambiguity diagnostics: `` `eqStack` (module `Data.Stack`), `eqRev` (this
/// program) ``.
fn provenance_list(instances: &BTreeMap<String, InstInfo>, names: &[String]) -> String {
    names
        .iter()
        .map(|n| match instances.get(n).map(|i| i.module.as_str()) {
            Some(m) if !m.is_empty() => format!("`{n}` (module `{m}`)"),
            _ => format!("`{n}` (this program)"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}
