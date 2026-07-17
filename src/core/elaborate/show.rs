use super::{
    subst_ty, wrap_binds, BTreeMap, BTreeSet, Builtin, Comp, CoreFn, CorePhase, Elab, Error, Expr,
    IoOp, Locals, NodeId, Pattern, Span, Spanned, Sym, Type, TypeError, Value, CONS, LIST, NIL, S,
};
use crate::core::typed::core_fn_sig;
use crate::names;

// Name prefix for a generated structural `show` function, completed by the
// type's injective mangling.
const SHOW_FN_PREFIX: &str = "_show_";

impl Elab<'_> {
    fn record_show_sig(&mut self, name: &str, input: Type) -> Result<(), Error> {
        let signature =
            core_fn_sig(&Type::fun(vec![input], Type::Str), Vec::new()).map_err(|error| {
                Error::InternalInvariant(format!("generated show signature: {error}"))
            })?;
        self.show_sigs.insert(Sym::from(name), signature);
        Ok(())
    }

    // Like `local_ty`, but for printing: resolve the print-site type to a
    // concrete printable monotype, or None when the caller must fall back to the
    // integer printer. See `default_printable` for the defaulting rationale.
    pub(super) fn printable_ty(&self, e: &S<Expr<CorePhase>>, locals: &Locals) -> Option<Type> {
        // Default each candidate type to a printable monotype and take the first
        // that resolves. Both a generalized scheme `forall a. List(a)` and an
        // under-determined `List(?n)` describe a provably empty container (the
        // free theorem: nothing could have built a `Cons`/`Some`), so their
        // leaves default to Int and the spine prints as the interpreter's does.
        // A *free* rigid var is an enclosing function's parameter, which needs
        // runtime type info, so it stays unresolved and the caller falls back.
        [self.hir.node_type(e.id).cloned(), self.local_ty(e, locals)]
            .into_iter()
            .flatten()
            .find_map(default_printable)
    }

    // Direct lowering of a `print`/`println` argument to the runtime printer,
    // used when no `Output` handler is in scope (a prelude-free program). The
    // value reaches the printer immediately, so output is not interceptable.
    pub(super) fn print_dispatch(
        &mut self,
        v: Value,
        arg_expr: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        Ok(match self.printable_ty(arg_expr, locals) {
            Some(Type::Float) => Comp::Io(IoOp::PrintF, vec![v]),
            Some(Type::Str) => Comp::Io(IoOp::PrintS, vec![v]),
            // Int prints through the runtime integer printer. `None` is a value
            // whose type is a free rigid var (an enclosing parameter): its type
            // is unknowable here, so it likewise lowers to the raw printer, which
            // self-dispatches on the cell tag at runtime (Int/Unit/String/bignum)
            // and traps on any other cell rather than misread it. A structural
            // value can only reach that path through a truly polymorphic `print`,
            // which no static type could have shown.
            Some(Type::Int) | None => Comp::Io(IoOp::Print, vec![v]),
            // Everything else (ADTs, tuples, lists, I64/U64/Bool, Unit) reuses the
            // type-directed structural printer so native matches the interpreter.
            // A known-but-unshowable type (e.g. a function) is a hard error here,
            // not a silent fall-through to the raw printer that would garble it.
            Some(ty) => {
                let show = self.show_for_type(v, &ty, arg_expr.span)?;
                let s = self.fresh();
                Comp::Bind(
                    Box::new(show),
                    s.clone().into(),
                    Box::new(Comp::Io(IoOp::PrintS, vec![Value::Var(s.into())])),
                )
            }
        })
    }

    // Lower a `print`/`println` call to a perform of the `Output` capability so
    // the output is interceptable (run_io discharges it to the real printer,
    // replay/durable drop it during a replayed prefix). The type-directed show
    // stays here at the call site: Float and structural types are pre-rendered to
    // a String because the runtime printer behind `prim_print` cannot show them,
    // while Int/Str/unknown values pass through raw (it self-dispatches on the
    // cell tag). `newline` selects `out_println` over `out_print`.
    pub(super) fn out_perform(
        &mut self,
        v: Value,
        arg_expr: &S<Expr<CorePhase>>,
        locals: &Locals,
        newline: bool,
    ) -> Result<Comp, Error> {
        // The `Output` ops carry a `String`, so the value is rendered here at the
        // call site where its type is concrete, then handed to the op.
        let val = self.display_comp(v, arg_expr, locals)?;
        let op = names::output_op(newline);
        let s = self.fresh();
        Ok(Comp::Bind(
            Box::new(val),
            s.clone().into(),
            Box::new(Comp::Do(op.into(), vec![Value::Var(s.into())])),
        ))
    }

    // The type-directed "display" rendering of a value to a `String`, shared by
    // `print`/`println` and by string interpolation. It renders a top-level
    // `String` raw (a message or interpolated string is inserted verbatim, not
    // quoted); only nested strings inside a structure quote, matching `Show`.
    // This is the documented "magic" printer; `show` is the canonical,
    // dictionary-dispatched one. It requires a concrete type: a polymorphic hole
    // is handled by the caller (dictionary-or-reject, exactly like a polymorphic
    // `print`), never silently rendered as an integer.
    pub(super) fn display_comp(
        &mut self,
        v: Value,
        arg_expr: &S<Expr<CorePhase>>,
        locals: &Locals,
    ) -> Result<Comp, Error> {
        Ok(match self.printable_ty(arg_expr, locals) {
            Some(Type::Str) => Comp::Return(v),
            Some(Type::Float) => Comp::StrBuiltin(Builtin::ShowFloat, vec![v]),
            Some(Type::Int) => Comp::StrBuiltin(Builtin::ShowInt, vec![v]),
            Some(ty) => self.show_for_type(v, &ty, arg_expr.span)?,
            // A free rigid var (an enclosing parameter): no static type to
            // render. Reaching here means the caller expected a concrete type;
            // reject rather than assume Int, which would misread a non-Int value
            // and diverge native output from the interpreter.
            None => return Err(polymorphic_print(arg_expr.span)),
        })
    }

    // Emit a print of an already-rendered `String` computation. Mirrors the two
    // routing modes of the concrete-type path: through the interceptable `Output`
    // capability when a world handler is in scope, else straight to the runtime
    // string printer. Used for the polymorphic (dictionary-rendered) print.
    pub(super) fn print_string(&mut self, shown: Comp, newline: bool) -> Comp {
        let s = self.fresh();
        let tail = if self.route_output {
            let op = names::output_op(newline);
            Comp::Do(op.into(), vec![Value::Var(s.clone().into())])
        } else {
            let put = Comp::Io(IoOp::PrintS, vec![Value::Var(s.clone().into())]);
            if newline {
                Comp::Bind(
                    Box::new(put),
                    self.fresh().into(),
                    Box::new(Comp::Io(IoOp::PrintNl, vec![])),
                )
            } else {
                put
            }
        };
        Comp::Bind(Box::new(shown), s.into(), Box::new(tail))
    }

    pub(super) fn show_for_type(&mut self, v: Value, ty: &Type, span: Span) -> Result<Comp, Error> {
        Ok(match ty {
            Type::Int => Comp::StrBuiltin(Builtin::ShowInt, vec![v]),
            Type::I64 => Comp::StrBuiltin(Builtin::ShowI64, vec![v]),
            Type::U64 => Comp::StrBuiltin(Builtin::ShowU64, vec![v]),
            Type::Bool => Comp::StrBuiltin(Builtin::ShowBool, vec![v]),
            Type::Float => Comp::StrBuiltin(Builtin::ShowFloat, vec![v]),
            Type::Char => Comp::StrBuiltin(Builtin::ShowChar, vec![v]),
            // A nested string renders quoted and escaped, matching the `Show`
            // instance. A top-level `print`/`show` of a bare string is handled
            // by the caller before it reaches here, so it stays raw.
            Type::Str => Comp::Call(names::STR_ESCAPE_FN.into(), vec![v]),
            Type::Unit => Comp::Return(Value::Str("()".into())),
            Type::Con(name, args) => Comp::Call(
                self.ensure_show_con(name.as_str(), args, span)?.into(),
                vec![v],
            ),
            Type::Tuple(tys) => Comp::Call(self.ensure_show_tuple(tys, span)?.into(), vec![v]),
            other => return Err(unshowable(Some(other), span)),
        })
    }

    pub(super) fn concat_comps(&mut self, comps: Vec<Comp>) -> Comp {
        let mut binds = Vec::new();
        let mut vars = Vec::new();
        for c in comps {
            let v = self.fresh();
            binds.push((c, v.clone()));
            vars.push(Value::Var(v.into()));
        }
        let mut it = vars.into_iter();
        let Some(first) = it.next() else {
            return Comp::Return(Value::Str(String::new()));
        };
        let Some(second) = it.next() else {
            return wrap_binds(binds, Comp::Return(first));
        };
        let mut acc = Comp::StrBuiltin(Builtin::Concat, vec![first, second]);
        for v in it {
            let r = self.fresh();
            acc = Comp::Bind(
                Box::new(acc),
                r.clone().into(),
                Box::new(Comp::StrBuiltin(
                    Builtin::Concat,
                    vec![Value::Var(r.into()), v],
                )),
            );
        }
        wrap_binds(binds, acc)
    }

    // The rendering for one constructor, matching the derived `Show` instance
    // (kept in lockstep by `print_show_consistency`): a nullary constructor is
    // its bare name, a record constructor prints `Name { f = v, ... }`, and a
    // positional one prints `Name(v, ...)`. `fields` is empty unless the
    // constructor has named fields.
    pub(super) fn show_arm_body(
        &mut self,
        label: String,
        field_tys: &[Type],
        fields: &[Sym],
        span: Span,
    ) -> Result<(Vec<String>, Comp), Error> {
        let fvars: Vec<String> = (0..field_tys.len()).map(|i| format!("_f{i}")).collect();
        if field_tys.is_empty() {
            return Ok((fvars, Comp::Return(Value::Str(label))));
        }
        let record = fields.len() == field_tys.len();
        let mut comps = vec![Comp::Return(Value::Str(if record {
            format!("{label} {{ ")
        } else {
            format!("{label}(")
        }))];
        for (i, (fv, fty)) in fvars.iter().zip(field_tys).enumerate() {
            if i > 0 {
                comps.push(Comp::Return(Value::Str(", ".into())));
            }
            if record {
                comps.push(Comp::Return(Value::Str(format!("{} = ", fields[i]))));
            }
            comps.push(self.show_for_type(Value::Var(fv.clone().into()), fty, span)?);
        }
        comps.push(Comp::Return(Value::Str(if record {
            " }".into()
        } else {
            ")".into()
        })));
        let body = self.concat_comps(comps);
        Ok((fvars, body))
    }

    pub(super) fn ensure_show_con(
        &mut self,
        name: &str,
        args: &[Type],
        span: Span,
    ) -> Result<String, Error> {
        let mangled = mangle_con(name, args)
            .ok_or_else(|| unshowable(Some(&Type::Con(name.into(), args.to_vec())), span))?;
        let fname = format!("{SHOW_FN_PREFIX}{mangled}");
        if self.show_seen.contains(&fname) {
            return Ok(fname);
        }
        self.show_seen.insert(fname.clone());
        if name == LIST {
            if let [elem] = args {
                return self.ensure_show_list(fname, &elem.clone(), span);
            }
        }
        let ctor_names = self
            .checked
            .data
            .get(name)
            .map(|d| d.ctors.clone())
            .unwrap_or_default();
        let mut arms = Vec::new();
        for cn in ctor_names {
            let info = self.ctors.get(&cn).cloned().ok_or_else(|| {
                Error::InternalInvariant(format!("data decl names ctor `{cn}` with no CtorInfo"))
            })?;
            let subst: BTreeMap<String, Type> = info
                .params
                .into_iter()
                .map(|p| p.to_string())
                .zip(args.iter().cloned())
                .collect();
            let field_tys: Vec<Type> = info.args.iter().map(|a| subst_ty(a, &subst)).collect();
            let (fvars, body) = self.show_arm_body(cn.clone(), &field_tys, &info.fields, span)?;
            let subs = fvars
                .iter()
                .map(|fv| Spanned {
                    id: NodeId::DUMMY,
                    synth: false,
                    node: Pattern::Var(fv.clone()),
                    span: Span::new(0, 0),
                })
                .collect();
            arms.push((Pattern::Ctor(cn, subs), body));
        }
        let body = self.compile_match(Value::Var("_sv".into()), arms)?;
        self.record_show_sig(&fname, Type::Con(Sym::from(name), args.to_vec()))?;
        self.show_fns.push(CoreFn {
            name: fname.clone().into(),
            params: vec!["_sv".into()],
            dict_arity: 0,
            body,
        });
        Ok(fname)
    }

    pub(super) fn ensure_show_list(
        &mut self,
        fname: String,
        elem: &Type,
        span: Span,
    ) -> Result<String, Error> {
        let tail = format!("{fname}_tl");
        let pvar = |n: &str| Spanned {
            id: NodeId::DUMMY,
            synth: false,
            node: Pattern::Var(n.into()),
            span: Span::new(0, 0),
        };
        for (fun, sep, end) in [(&fname, "[", "[]"), (&tail, ", ", "]")] {
            let head = self.show_for_type(Value::Var("_h".into()), elem, span)?;
            let cons = self.concat_comps(vec![
                Comp::Return(Value::Str(sep.into())),
                head,
                Comp::Call(tail.clone().into(), vec![Value::Var("_t".into())]),
            ]);
            let arms = vec![
                (
                    Pattern::Ctor(NIL.into(), vec![]),
                    Comp::Return(Value::Str(end.into())),
                ),
                (
                    Pattern::Ctor(CONS.into(), vec![pvar("_h"), pvar("_t")]),
                    cons,
                ),
            ];
            let body = self.compile_match(Value::Var("_sv".into()), arms)?;
            self.record_show_sig(fun, Type::Con(Sym::from(LIST), vec![elem.clone()]))?;
            self.show_fns.push(CoreFn {
                name: fun.clone().into(),
                params: vec!["_sv".into()],
                dict_arity: 0,
                body,
            });
        }
        Ok(fname)
    }

    pub(super) fn ensure_show_tuple(&mut self, tys: &[Type], span: Span) -> Result<String, Error> {
        let tup = Type::Tuple(tys.to_vec());
        let mangled = mangle_ty(&tup).ok_or_else(|| unshowable(Some(&tup), span))?;
        let fname = format!("{SHOW_FN_PREFIX}{mangled}");
        if self.show_seen.contains(&fname) {
            return Ok(fname);
        }
        self.show_seen.insert(fname.clone());
        let fvars: Vec<String> = (0..tys.len()).map(|i| format!("_f{i}")).collect();
        let mut comps = vec![Comp::Return(Value::Str("(".into()))];
        for (i, (fv, fty)) in fvars.iter().zip(tys).enumerate() {
            if i > 0 {
                comps.push(Comp::Return(Value::Str(", ".into())));
            }
            comps.push(self.show_for_type(Value::Var(fv.clone().into()), fty, span)?);
        }
        comps.push(Comp::Return(Value::Str(")".into())));
        let body = self.concat_comps(comps);
        let subs = fvars
            .iter()
            .map(|fv| Spanned {
                id: NodeId::DUMMY,
                synth: false,
                node: Pattern::Var(fv.clone()),
                span: Span::new(0, 0),
            })
            .collect();
        let arm = (Pattern::Tuple(subs), body);
        let cased = self.compile_match(Value::Var("_sv".into()), vec![arm])?;
        self.record_show_sig(&fname, tup)?;
        self.show_fns.push(CoreFn {
            name: fname.clone().into(),
            params: vec!["_sv".into()],
            dict_arity: 0,
            body: cased,
        });
        Ok(fname)
    }
}

// Resolve a print-site type to a concrete printable monotype, or None when it
// still mentions a free rigid var (an enclosing parameter). Leading `forall`s
// are locally quantified, so their vars label empty containers and default to
// Int along with any free existentials.
fn default_printable(t: Type) -> Option<Type> {
    // A local var (existential or generalized) is safe to default only when it
    // is guarded by an ADT constructor: there it is the element of a container
    // the free theorem proves empty, so its show is dead code. A bare or
    // tuple-component local var is a *present* value (a not-yet-generalized
    // parameter), which would be miscompiled, so bail.
    if !local_guarded(&t, &mut Vec::new(), false) {
        return None;
    }
    let t = strip_foralls(t);
    let mut ex = BTreeSet::new();
    t.free_exist(&mut ex);
    let d = ex.iter().fold(t, |t, v| t.subst_exist(*v, &Type::Int));
    (!has_var(&d)).then_some(d)
}

// Whether every local var (an existential, or a var bound by a `forall` within
// this type) appears only under an ADT constructor. A free rigid var (an
// enclosing parameter) is left for `has_var` to reject after defaulting.
fn local_guarded(t: &Type, bound: &mut Vec<Sym>, under_con: bool) -> bool {
    match t {
        Type::Exist(_) => under_con,
        Type::Var(n) => !bound.contains(n) || under_con,
        Type::Con(_, ps) => ps.iter().all(|p| local_guarded(p, bound, true)),
        Type::Tuple(ps) => ps.iter().all(|p| local_guarded(p, bound, under_con)),
        Type::Fun(ps, _, r) => {
            ps.iter().all(|p| local_guarded(p, bound, under_con))
                && local_guarded(r, bound, under_con)
        }
        Type::Forall(n, b) => {
            bound.push(*n);
            let ok = local_guarded(b, bound, under_con);
            bound.pop();
            ok
        }
        Type::RowForall(_, b) => local_guarded(b, bound, under_con),
        _ => true,
    }
}

// Eliminate every (possibly nested) `forall` by defaulting its bound var to Int;
// each is a local generalization labelling an empty container.
fn strip_foralls(t: Type) -> Type {
    match t {
        Type::Forall(n, body) => strip_foralls(body.subst_var(n, &Type::Int)),
        Type::RowForall(n, body) => Type::RowForall(n, Box::new(strip_foralls(*body))),
        Type::Con(n, ps) => Type::Con(n, ps.into_iter().map(strip_foralls).collect()),
        Type::Tuple(ps) => Type::Tuple(ps.into_iter().map(strip_foralls).collect()),
        Type::Fun(ps, row, r) => Type::Fun(
            ps.into_iter().map(strip_foralls).collect(),
            row,
            Box::new(strip_foralls(*r)),
        ),
        other => other,
    }
}

// Whether a type still mentions a rigid type variable, which the structural
// printer cannot resolve without runtime type information.
fn has_var(t: &Type) -> bool {
    match t {
        Type::Var(_) => true,
        Type::Con(_, ps) | Type::Tuple(ps) => ps.iter().any(has_var),
        Type::Fun(ps, _, r) => ps.iter().any(has_var) || has_var(r),
        Type::Forall(_, b) | Type::RowForall(_, b) => has_var(b),
        _ => false,
    }
}

// A `print`/`println` whose argument type is still a free rigid variable (an
// enclosing function's parameter, not a defaultable empty container) has no
// static show: no type here could render the value, and lowering it to the raw
// printer would abort at runtime on a structural cell. Rejected at the print
// call site; the raw-printer runtime trap remains behind it as defense in depth.
pub(super) fn polymorphic_print(span: Span) -> Error {
    Error::Type(TypeError::TypeFailure {
        span,
        msg: "cannot print a value of polymorphic type: its type is not known \
              here, so no printer can render it. Use `show(x)` with a `Show` \
              constraint, or annotate the argument with a concrete type"
            .into(),
    })
}

fn unshowable(ty: Option<&Type>, span: Span) -> Error {
    let is_fn = |t: &Type| {
        let mut t = t;
        while let Type::Forall(_, inner) | Type::RowForall(_, inner) = t {
            t = inner;
        }
        matches!(t, Type::Fun(..))
    };
    let msg = match ty {
        Some(t) if is_fn(t) => format!("cannot show a function of type {}", t.show()),
        _ => "cannot infer the type to show; annotate the argument, e.g. (e : List(Int))".into(),
    };
    Error::Type(TypeError::TypeFailure { span, msg })
}

// An injective mangling of a showable type into a `_show_*` function name.
// `None` for a type with no derivable `show` (a function or a quantified type
// nested in a structure): collapsing those to one key would alias distinct
// generated show functions, so the caller turns `None` into an `unshowable`
// diagnostic instead.
fn mangle_ty(ty: &Type) -> Option<String> {
    Some(match ty {
        Type::Unit => "Unit".into(),
        Type::Int => "Int".into(),
        Type::I64 => "I64".into(),
        Type::U64 => "U64".into(),
        Type::Bool => "Bool".into(),
        Type::Float => "Float".into(),
        Type::Char => "Char".into(),
        Type::Str => "Str".into(),
        Type::Con(n, args) => mangle_con(n.as_str(), args)?,
        Type::Tuple(tys) => {
            let mut s = format!("Tup{}", tys.len());
            for t in tys {
                mangle_chunk(&mut s, &mangle_ty(t)?);
            }
            s
        }
        _ => return None,
    })
}

// Length-prefix the name and every argument so the encoding is injective:
// distinct types never produce the same key, so generated show functions cannot
// alias. A bare `_` join is ambiguous because type names may contain `_` (`Foo`
// applied to `Bar` and a type named `Foo_Bar` both joining to `Foo_Bar`, so one
// show function served both and the other's values misbehaved). Each
// `{len}_{mangled}` chunk is self-delimiting, so a `_` inside a name can no
// longer read as a structural boundary.
fn mangle_con(name: &str, args: &[Type]) -> Option<String> {
    let mut s = String::new();
    mangle_chunk(&mut s, name);
    for a in args {
        mangle_chunk(&mut s, &mangle_ty(a)?);
    }
    Some(s)
}

// Append a self-delimiting `{len}_{chunk}` so a `_` inside `chunk` cannot be
// read as a boundary.
fn mangle_chunk(s: &mut String, chunk: &str) {
    s.push_str(&chunk.len().to_string());
    s.push('_');
    s.push_str(chunk);
}
