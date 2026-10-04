//! Locals whose witness the lowering changed.
//!
//! Rewriting a definition can give a local a type its binder was not
//! elaborated with, and every later read of that local has to carry the new
//! type or the stored witness and the term disagree, which the independent
//! verifier rejects (and rightly: a swapped parameter would otherwise be
//! invisible). The map here records the change once and rebuilds each read
//! through it, including through the source representation wrappers whose
//! proofs must survive the rebuild rather than be laundered away.

use std::collections::BTreeMap;

use prism_common::sym::Sym;

use super::super::super::verify::representation_preserving;
use super::super::super::{CompSig, CoreFnSig, CoreType, TypedValue, TypedValueKind};
use crate::types::ty::EffRow;

/// The locals whose type threading has changed, and the type each now has.
#[derive(Default, Debug)]
pub(super) struct Retyped(BTreeMap<Sym, CoreType>);

impl Retyped {
    #[must_use]
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn insert(&mut self, name: Sym, ty: CoreType) -> Option<CoreType> {
        self.0.insert(name, ty)
    }

    pub(super) fn remove(&mut self, name: Sym) -> Option<CoreType> {
        self.0.remove(&name)
    }

    pub(super) fn restore(&mut self, name: Sym, previous: Option<CoreType>) {
        match previous {
            Some(ty) => {
                self.0.insert(name, ty);
            }
            None => {
                self.0.remove(&name);
            }
        }
    }

    // A `Var` reading a retyped local, rebuilt at its new type.
    #[must_use]
    pub(super) fn lookup(&self, v: &TypedValue) -> Option<TypedValue> {
        let TypedValueKind::Var { name, .. } = v.kind() else {
            return None;
        };
        let ty = self.0.get(name)?;
        Some(TypedValue::new(
            ty.clone(),
            TypedValueKind::Var {
                name: *name,
                instantiation: Vec::new(),
            },
        ))
    }

    #[must_use]
    pub(super) fn rebuild(&self, v: &TypedValue) -> TypedValue {
        self.lookup(v).unwrap_or_else(|| v.clone())
    }

    /// Rebuild a local through its source wrappers. An identity
    /// reinterpretation follows its operand's new type; any other keeps its
    /// target while the representation judgment admits it, and otherwise
    /// yields the operand, whose new witness is the authoritative one.
    #[must_use]
    pub(super) fn rebuild_through(&self, v: &TypedValue) -> TypedValue {
        match v.kind() {
            TypedValueKind::Reinterpret(inner) => {
                let inner2 = self.rebuild_through(inner);
                let target = if v.ty() == inner.ty() {
                    inner2.ty().clone()
                } else {
                    v.ty().clone()
                };
                reinterpret_at(inner2.clone(), target).unwrap_or(inner2)
            }
            _ => self.try_rebuild(v).unwrap_or_else(|| v.clone()),
        }
    }

    // Rebuild a local through source representation wrappers without erasing
    // the proof those wrappers carry. A changed operand may keep an existing
    // reinterpretation only when the verifier's representation judgment still
    // admits its target. A newtype field is declared at the convention its
    // stored carrier is widened to, so the operand's new type is the field's.
    fn try_rebuild(&self, v: &TypedValue) -> Option<TypedValue> {
        match v.kind() {
            TypedValueKind::Reinterpret(inner) => {
                reinterpret_at(self.try_rebuild(inner)?, v.ty().clone())
            }
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value,
            } => {
                let value2 = self.try_rebuild(value)?;
                Some(TypedValue::new(
                    v.ty().clone(),
                    TypedValueKind::NewtypeRepr {
                        constructor: *constructor,
                        instantiation: instantiation.clone(),
                        value: Box::new(value2),
                    },
                ))
            }
            // A lowered bridge keeps its target while the proof still admits
            // the rebuilt operand. A bridge onto an arrow whose operand grew
            // parameters grows the same ones: the bridge changes what the
            // closure answers with, never what it is applied to.
            TypedValueKind::LoweredRepr { value, proof } => {
                let value2 = self.try_rebuild(value)?;
                let target = graft_arrow(v.ty(), innermost(value).ty(), innermost(&value2).ty());
                proof.validates(value2.ty(), &target).then(|| {
                    TypedValue::new(
                        target,
                        TypedValueKind::LoweredRepr {
                            value: Box::new(value2),
                            proof: proof.clone(),
                        },
                    )
                })
            }
            _ => Some(self.rebuild(v)),
        }
    }
}

// Retain a source reinterpretation after its operand has been threaded. Equal
// witnesses need no wrapper; otherwise the same representation proof the
// verifier checks must still hold. A convention change is not a row relabel
// and makes the attempt decline instead of laundering the new value through
// the old target.
fn reinterpret_at(value: TypedValue, expected: CoreType) -> Option<TypedValue> {
    if value.ty() == &expected {
        return Some(value);
    }
    representation_preserving(value.ty(), &expected)
        .then(|| TypedValue::new(expected, TypedValueKind::Reinterpret(Box::new(value))))
}

/// The value under every lowered bridge.
pub(super) fn innermost(v: &TypedValue) -> &TypedValue {
    match v.kind() {
        TypedValueKind::LoweredRepr { value, .. } => innermost(value),
        _ => v,
    }
}

/// `target` with the quantifiers and parameters `after` has where `before`
/// had the ones `target` was spelled with, and with a row `after` runs at
/// wherever `target` ran at `before`'s; anything but a bridge between thunks
/// of functions keeps its target.
pub(super) fn graft_arrow(target: &CoreType, before: &CoreType, after: &CoreType) -> CoreType {
    if before == after {
        return target.clone();
    }
    let (CoreType::Thunk(sig), CoreType::Thunk(was), CoreType::Thunk(wide)) =
        (target, before, after)
    else {
        return target.clone();
    };
    let (CoreType::Function(fun), CoreType::Function(had), CoreType::Function(grown)) =
        (sig.result(), was.result(), wide.result())
    else {
        return target.clone();
    };
    let follow = |mine: &EffRow, theirs: &EffRow, now: &EffRow| {
        if mine == theirs {
            now.clone()
        } else {
            mine.clone()
        }
    };
    CoreType::Thunk(Box::new(CompSig::new(
        CoreType::Function(Box::new(CoreFnSig::new(
            grown.quantifiers().to_vec(),
            grown.params().to_vec(),
            CompSig::new(
                fun.body().result().clone(),
                follow(
                    fun.body().effects(),
                    had.body().effects(),
                    grown.body().effects(),
                ),
            ),
        ))),
        follow(sig.effects(), was.effects(), wide.effects()),
    )))
}

#[cfg(test)]
mod tests {
    use crate::core::typed::verify::{ConstructorSig, VerifyEnv};
    use crate::core::typed::{
        verify, EffectLowered, TypedBinder, TypedComp, TypedCompKind, TypedCoreFn,
        UncheckedTypedCore,
    };
    use crate::types::ty::{EffRow, Label};
    use crate::types::Type;

    use super::super::super::super::{CompSig, CoreFnSig};
    use super::*;

    fn sym(name: &str) -> Sym {
        Sym::new(name)
    }

    fn int() -> CoreType {
        CoreType::Source(Type::Int)
    }

    #[test]
    fn retyped_reads_preserve_representation_wrappers() {
        let callable = |effects| {
            CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(CoreFnSig::new(
                    Vec::new(),
                    vec![int()],
                    CompSig::new(int(), effects),
                ))),
                EffRow::Empty,
            )))
        };
        let name = sym("f");
        let original = callable(EffRow::singleton(sym("Read")));
        let mapped = callable(EffRow::singleton(sym("Write")));
        let target = callable(EffRow::canonical(
            [Label::bare(sym("Read")), Label::bare(sym("Write"))],
            EffRow::Empty,
        ));
        let bare = TypedValue::new(
            original,
            TypedValueKind::Var {
                name,
                instantiation: Vec::new(),
            },
        );
        let wrapped = TypedValue::new(
            target.clone(),
            TypedValueKind::Reinterpret(Box::new(bare.clone())),
        );
        let mut retyped = Retyped::new();
        retyped.insert(name, mapped.clone());

        assert_eq!(
            retyped.lookup(&bare).expect("bare read retypes").ty(),
            &mapped
        );
        assert!(
            retyped.lookup(&wrapped).is_none(),
            "lookup must not flatten a representation wrapper"
        );
        let rebuilt = retyped
            .try_rebuild(&wrapped)
            .expect("both rows are representable at the aggregate target");
        assert_eq!(rebuilt.ty(), &target);
        let TypedValueKind::Reinterpret(inner) = rebuilt.kind() else {
            panic!("the aggregate row target remains explicit")
        };
        assert_eq!(inner.ty(), &mapped);

        let wrong_convention = CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                vec![CoreType::Source(Type::Bool)],
                CompSig::new(int(), EffRow::Empty),
            ))),
            EffRow::Empty,
        )));
        retyped.insert(name, wrong_convention.clone());
        assert!(
            retyped.try_rebuild(&wrapped).is_none(),
            "a wrapper cannot conceal a changed calling convention"
        );
        let newtype = TypedValue::new(
            target.clone(),
            TypedValueKind::NewtypeRepr {
                constructor: sym("FnBox"),
                instantiation: Vec::new(),
                value: Box::new(bare),
            },
        );
        let rebuilt = retyped
            .try_rebuild(&newtype)
            .expect("a newtype field follows its operand to the stored convention");
        assert_eq!(rebuilt.ty(), &target);
        let TypedValueKind::NewtypeRepr { value, .. } = rebuilt.kind() else {
            panic!("the constructor stays explicit")
        };
        assert_eq!(value.ty(), &wrong_convention);
    }

    fn thunked_arrow(params: Vec<CoreType>, effects: EffRow) -> CoreType {
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                params,
                CompSig::new(int(), effects),
            ))),
            EffRow::Empty,
        )))
    }

    fn read(name: Sym, ty: CoreType) -> TypedValue {
        TypedValue::new(
            ty,
            TypedValueKind::Var {
                name,
                instantiation: Vec::new(),
            },
        )
    }

    // A newtype over a callable, constructed from a parameter in one function
    // and projected back out in another, so the verifier sees both ends of
    // the coercion against one declaration.
    fn newtype_program(
        stored: &CoreType,
        projected: &CoreType,
        rebuild: &Retyped,
    ) -> Vec<TypedCoreFn> {
        let boxed = CoreType::Source(Type::Con(sym("FnBox"), Vec::new()));
        let f = TypedBinder::new(sym("f"), stored.clone());
        let construction = rebuild.rebuild_through(&TypedValue::new(
            boxed.clone(),
            TypedValueKind::NewtypeRepr {
                constructor: sym("FnBox"),
                instantiation: Vec::new(),
                value: Box::new(read(sym("f"), thunked_arrow(vec![int()], EffRow::Empty))),
            },
        ));
        let wrap_body = TypedComp::new(
            CompSig::new(boxed.clone(), EffRow::Empty),
            TypedCompKind::Return(construction),
        );
        let wrap = TypedCoreFn::new(
            sym("wrap"),
            vec![f],
            wrap_body,
            CoreFnSig::new(
                Vec::new(),
                vec![stored.clone()],
                CompSig::new(boxed.clone(), EffRow::Empty),
            ),
            0,
        );
        let b = TypedBinder::new(sym("b"), boxed.clone());
        let projection = TypedValue::new(
            projected.clone(),
            TypedValueKind::NewtypeRepr {
                constructor: sym("FnBox"),
                instantiation: Vec::new(),
                value: Box::new(read(sym("b"), boxed.clone())),
            },
        );
        let unwrap_body = TypedComp::new(
            CompSig::new(projected.clone(), EffRow::Empty),
            TypedCompKind::Return(projection),
        );
        let unwrap = TypedCoreFn::new(
            sym("unwrap"),
            vec![b],
            unwrap_body,
            CoreFnSig::new(
                Vec::new(),
                vec![boxed],
                CompSig::new(projected.clone(), EffRow::Empty),
            ),
            0,
        );
        vec![wrap, unwrap]
    }

    fn verify_newtype(declared_field: &CoreType, program: Vec<TypedCoreFn>) -> Result<(), String> {
        let mut env = VerifyEnv::new();
        env.insert_constructor(
            sym("FnBox"),
            ConstructorSig::new(
                Vec::new(),
                0,
                vec![declared_field.clone()],
                CoreType::Source(Type::Con(sym("FnBox"), Vec::new())),
            ),
        );
        env.mark_newtype_constructor(sym("FnBox"));
        verify(UncheckedTypedCore::<EffectLowered>::new(program), &env)
            .map(|_| ())
            .map_err(|violations| format!("{violations:?}"))
    }

    // The independent verifier is what holds the stored convention to the
    // declaration. A rebuilt operand that follows a retyped local to a wider
    // calling convention passes only when the constructor's declaration was
    // widened the same way and its projection reads the widened field; the
    // same operand against the original declaration, or a projection that
    // did not follow, is refused. A field whose widening failed keeps its
    // declaration and its untouched operand, which the verifier accepts.
    #[test]
    fn newtype_operand_and_declaration_must_agree_under_the_verifier() {
        let original = thunked_arrow(vec![int()], EffRow::Empty);
        let widened = thunked_arrow(vec![int(), int()], EffRow::Empty);
        let mut followed = Retyped::new();
        followed.insert(sym("f"), widened.clone());
        let untouched = Retyped::new();

        verify_newtype(&original, newtype_program(&original, &original, &untouched))
            .expect("an unwidened field with its untouched operand and projection");
        verify_newtype(&widened, newtype_program(&widened, &widened, &followed))
            .expect("a widened declaration with a rebuilt operand and a following projection");

        let stale_declaration =
            verify_newtype(&original, newtype_program(&widened, &original, &followed))
                .expect_err("a rebuilt operand against the original declaration");
        assert!(
            stale_declaration.contains("NewtypeCoercionDisconnected"),
            "{stale_declaration}"
        );
        let stale_projection =
            verify_newtype(&widened, newtype_program(&widened, &original, &followed))
                .expect_err("a projection that did not follow the widened declaration");
        assert!(
            stale_projection.contains("NewtypeCoercionDisconnected"),
            "{stale_projection}"
        );
    }
}
