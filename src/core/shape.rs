//! Structural shape digests of datatype and effect declarations.
//!
//! The content hasher (`super::hash`) fingerprints term *behavior* over Core.
//! Datatypes and effects have no Core body, so they would otherwise reach a
//! hash only as leaf names inside the terms that use them. A shape digest closes
//! that gap: it hashes the format-relevant structure of a declaration, so a
//! constructor added, a field reordered, or an operation's type changed moves
//! the digest, while a doc-comment or a reformat does not.
//!
//! The encoding mirrors `super::hash`: a stable tag per node, length-prefixed
//! names, and type-parameter spelling erased to positional indices so
//! `List(a)` and `List(b)` are the same shape. Referenced types enter by name,
//! not by digest (a flat, not per-type-Merkle, scheme): the stdlib root folds
//! every declaration's digest, so any type change already moves the root without
//! transitive substitution. Effect operations are addressed by name, so they are
//! encoded in name order (a set); a datatype's constructors are ordered (their
//! position is their tag), so they are encoded in declaration order.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use crate::syntax::ast::{ClassDecl, Ctor, DataDecl, EffectDecl, Kind, Row, Ty};

use super::hash::{hex, SCHEME};

/// Map from a declaration name to its structural digest (hex).
pub type Shapes = BTreeMap<String, String>;

/// Shape-digest every datatype and effect declaration. Keyed by the declaration
/// name, so the result merges directly into the namespace root alongside the
/// per-definition behavior hashes.
#[must_use]
pub fn shape_digests(types: &[DataDecl], effects: &[EffectDecl]) -> Shapes {
    // A datatype and an effect are distinct declarations that may share a name
    // (they live in different judgement forms), so keying both by the bare name
    // would let one silently overwrite the other and vanish from the root. Only a
    // genuine clash needs disambiguating; unique names keep their bare key so the
    // common no-collision case is unchanged.
    let eff_names: BTreeSet<&str> = effects.iter().map(|e| e.name.as_str()).collect();
    let type_names: BTreeSet<&str> = types.iter().map(|d| d.name.as_str()).collect();
    let mut out = Shapes::new();
    for d in types {
        let key = if eff_names.contains(d.name.as_str()) {
            format!("data {}", d.name)
        } else {
            d.name.clone()
        };
        out.insert(key, hex(&encode_data(d)));
    }
    for e in effects {
        let key = if type_names.contains(e.name.as_str()) {
            format!("effect {}", e.name)
        } else {
            e.name.clone()
        };
        out.insert(key, hex(&encode_effect(e)));
    }
    out
}

/// Shape-digest every type-class declaration: its name, superclass constraints,
/// and method signatures, keyed by class name.
///
/// Folding this into the root makes a class-interface change move the fingerprint
/// even when no term realizes it (a default body change already moves the root
/// via its own `CoreFn`).
#[must_use]
pub fn class_digests(classes: &[ClassDecl]) -> Shapes {
    let mut out = Shapes::new();
    for c in classes {
        out.insert(c.name.clone(), hex(&encode_class(c)));
    }
    out
}

/// Content digest of one instance: its class, the type head, and the behavior
/// hashes of its already-elaborated method implementations.
///
/// `methods` maps each method name to the hash `hash_program` gave its
/// `i@<inst>@<method>` `CoreFn`. This is both the instance's displayed identity
/// and the `(class, head) -> hash` value a content-addressed coherence check
/// would bind, so it is the cheap seed for coherence: the method hashes already
/// exist, this only folds them.
#[must_use]
pub fn instance_digest(class: &str, head: &Ty, methods: &BTreeMap<String, String>) -> String {
    // Head type variables are alpha-normalized (positional), so `Eq(List(a))` and
    // `Eq(List(b))` share an identity.
    let mut e = Enc::new(&free_vars(head));
    e.out.push_str(SCHEME);
    e.out.push_str("|instance");
    e.tok(class);
    e.ty(head);
    // Methods are addressed by name; the map iterates in name order.
    e.out.push('{');
    for (name, hash) in methods {
        e.tok(name);
        e.tok(hash);
    }
    e.out.push('}');
    hex(&e.out)
}

fn encode_data(d: &DataDecl) -> String {
    let mut e = Enc::new(&d.params);
    e.out.push_str(SCHEME);
    e.out.push_str("|data");
    e.tok(&d.name);
    let _ = write!(e.out, "nt{}", u8::from(d.newtype));
    // Commit the parameter arity, not just the kinds: `param_kinds` is legally empty
    // (kinds default to Type), and without the count `data Phantom a` and
    // `data Phantom a b` would encode identically.
    let _ = write!(e.out, "K{}", d.params.len());
    for k in &d.param_kinds {
        e.kind(k);
    }
    // Constructor order is load-bearing (position is the runtime tag), so keep it.
    e.out.push('{');
    for c in &d.ctors {
        e.ctor(c);
    }
    e.out.push('}');
    e.out
}

fn encode_effect(eff: &EffectDecl) -> String {
    let mut e = Enc::new(&eff.params);
    e.out.push_str(SCHEME);
    e.out.push_str("|effect");
    e.tok(&eff.name);
    // Operations are addressed by name, not position, so encode in name order.
    let mut ops: Vec<&crate::syntax::ast::EffOp> = eff.ops.iter().collect();
    ops.sort_by(|a, b| a.name.cmp(&b.name));
    e.out.push('{');
    for op in ops {
        e.tok(&op.name);
        e.out.push('(');
        for p in &op.params {
            e.ty(p);
        }
        e.out.push(')');
        e.ty(&op.ret);
    }
    e.out.push('}');
    e.out
}

fn encode_class(c: &ClassDecl) -> String {
    // The class parameter is the sole type variable in method signatures; erase
    // its spelling to a positional index.
    let mut e = Enc::new(std::slice::from_ref(&c.param));
    e.out.push_str(SCHEME);
    e.out.push_str("|class");
    e.tok(&c.name);
    // Superclasses form a set: sort by name.
    let mut supers: Vec<&String> = c.supers.iter().collect();
    supers.sort();
    e.out.push('<');
    for s in supers {
        e.tok(s);
    }
    e.out.push('>');
    // Methods are addressed by name: sort, then encode (name, signature).
    let mut methods: Vec<&(String, Ty)> = c.methods.iter().collect();
    methods.sort_by(|a, b| a.0.cmp(&b.0));
    e.out.push('{');
    for (name, ty) in methods {
        e.tok(name);
        e.ty(ty);
    }
    e.out.push('}');
    e.out
}

// Free type variables of a head type, in first-seen order, for alpha-normalizing
// an instance head. A `Con` name is a type constructor (a leaf), not a variable.
fn free_vars(t: &Ty) -> Vec<String> {
    fn go(t: &Ty, acc: &mut Vec<String>) {
        match t {
            Ty::Var(x) => {
                if !acc.contains(x) {
                    acc.push(x.clone());
                }
            }
            Ty::App(head, args) => {
                if !acc.contains(head) {
                    acc.push(head.clone());
                }
                for a in args {
                    go(a, acc);
                }
            }
            Ty::Con(_, args) | Ty::Tuple(args) => {
                for a in args {
                    go(a, acc);
                }
            }
            Ty::Fun(ps, _, r) => {
                for p in ps {
                    go(p, acc);
                }
                go(r, acc);
            }
            Ty::Forall(_, b) => go(b, acc),
            _ => {}
        }
    }
    let mut acc = Vec::new();
    go(t, &mut acc);
    acc
}

struct Enc {
    // Type-parameter names in binding order; a `Ty::Var`/`App` head that names one
    // is rendered by its index, erasing parameter spelling.
    params: Vec<String>,
    out: String,
}

impl Enc {
    fn new(params: &[String]) -> Self {
        Self {
            params: params.to_vec(),
            out: String::new(),
        }
    }

    /// Length-prefixed token, so no name can be confused with its neighbours.
    fn tok(&mut self, s: &str) {
        let _ = write!(self.out, "{}:{s}", s.len());
    }

    /// A type name in reference position: a bound parameter by index, else a leaf
    /// name (a referenced type or a free variable).
    fn name_ref(&mut self, s: &str) {
        if let Some(i) = self.params.iter().position(|p| p == s) {
            let _ = write!(self.out, "p{i}");
        } else {
            self.out.push('n');
            self.tok(s);
        }
    }

    fn ctor(&mut self, c: &Ctor) {
        self.tok(&c.name);
        // Record constructor: field order is part of the shape; field names are
        // part of the public surface, so commit to them. Positional otherwise.
        if let Some(fields) = &c.fields {
            self.out.push('r');
            for (name, ty) in fields {
                self.tok(name);
                self.ty(ty);
            }
        } else {
            self.out.push('a');
            for ty in &c.args {
                self.ty(ty);
            }
        }
        self.out.push(';');
    }

    fn kind(&mut self, k: &Kind) {
        match k {
            Kind::Type => self.out.push_str("kt"),
            Kind::Row => self.out.push_str("kr"),
            Kind::Fun(a, b) => {
                self.out.push_str("kf");
                self.kind(a);
                self.kind(b);
            }
        }
    }

    fn ty(&mut self, t: &Ty) {
        match t {
            Ty::Int => self.out.push_str("<i>"),
            Ty::I64 => self.out.push_str("<j>"),
            Ty::U64 => self.out.push_str("<u>"),
            Ty::Bool => self.out.push_str("<b>"),
            Ty::Unit => self.out.push_str("<1>"),
            Ty::Float => self.out.push_str("<f>"),
            Ty::Char => self.out.push_str("<c>"),
            Ty::Str => self.out.push_str("<s>"),
            Ty::Var(x) => {
                self.out.push_str("<v>");
                self.name_ref(x);
            }
            Ty::App(head, args) => {
                self.out.push_str("<A>");
                self.name_ref(head);
                self.tys(args);
            }
            Ty::Con(name, args) => {
                self.out.push_str("<C>");
                self.name_ref(name);
                self.tys(args);
            }
            Ty::Tuple(args) => {
                self.out.push_str("<T>");
                self.tys(args);
            }
            Ty::Fun(params, row, ret) => {
                self.out.push_str("<F>");
                self.tys(params);
                self.row(row);
                self.ty(ret);
            }
            // Bound variables are positional; extend the parameter map for the body.
            Ty::Forall(vars, body) => {
                self.out.push_str("<Q>");
                let base = self.params.len();
                self.params.extend(vars.iter().cloned());
                self.ty(body);
                self.params.truncate(base);
            }
            Ty::RowLit(row) => {
                self.out.push_str("<R>");
                self.row(row);
            }
            // Desugar-only; never in a surviving annotation, but encode defensively.
            Ty::State(n) => {
                let _ = write!(self.out, "<S>{n}");
            }
        }
    }

    fn tys(&mut self, ts: &[Ty]) {
        self.out.push('[');
        for t in ts {
            self.ty(t);
        }
        self.out.push(']');
    }

    fn row(&mut self, r: &Row) {
        match r {
            Row::Empty => self.out.push_str("re"),
            // Effect labels form a set: sort by name so order is not load-bearing.
            Row::Cons(labels, tail) => {
                self.out.push_str("rc");
                let mut ls: Vec<&crate::syntax::ast::EffLabel> = labels.iter().collect();
                ls.sort_by(|a, b| a.name.cmp(&b.name));
                for l in ls {
                    self.tok(&l.name);
                    self.tys(&l.args);
                }
                match tail {
                    Some(v) => {
                        self.out.push('|');
                        self.name_ref(v);
                    }
                    None => self.out.push('.'),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::shape_digests;
    use crate::syntax::ast::{Ctor, DataDecl, Ty};

    fn data(name: &str, params: &[&str], ctors: Vec<Ctor>) -> DataDecl {
        DataDecl {
            name: name.into(),
            params: params.iter().map(|s| (*s).into()).collect(),
            param_kinds: Vec::new(),
            ctors,
            deriving: Vec::new(),
            newtype: false,
            span: crate::syntax::ast::Span::default(),
        }
    }

    fn ctor(name: &str, args: Vec<Ty>) -> Ctor {
        Ctor {
            name: name.into(),
            args,
            fields: None,
        }
    }

    // `Box(a)` and `Box(b)` are the same shape: parameter spelling is erased.
    #[test]
    fn type_parameter_spelling_is_erased() {
        let a = data("Box", &["a"], vec![ctor("Box", vec![Ty::Var("a".into())])]);
        let b = data("Box", &["b"], vec![ctor("Box", vec![Ty::Var("b".into())])]);
        assert_eq!(
            shape_digests(&[a], &[])["Box"],
            shape_digests(&[b], &[])["Box"]
        );
    }

    // Adding a constructor is a format-breaking change and must move the digest.
    #[test]
    fn adding_a_constructor_moves_the_digest() {
        let one = data("T", &[], vec![ctor("A", vec![])]);
        let two = data("T", &[], vec![ctor("A", vec![]), ctor("B", vec![])]);
        assert_ne!(
            shape_digests(&[one], &[])["T"],
            shape_digests(&[two], &[])["T"]
        );
    }

    // Constructor order is the runtime tag order, so reordering moves the digest.
    #[test]
    fn constructor_order_is_significant() {
        let ab = data("T", &[], vec![ctor("A", vec![]), ctor("B", vec![])]);
        let ba = data("T", &[], vec![ctor("B", vec![]), ctor("A", vec![])]);
        assert_ne!(
            shape_digests(&[ab], &[])["T"],
            shape_digests(&[ba], &[])["T"]
        );
    }
}
