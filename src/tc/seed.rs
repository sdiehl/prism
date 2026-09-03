//! Construction, validation, and deterministic merging for dependency facts.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::hir::NodeFacts;
use crate::sym::Sym;
use crate::types::{CtorInfo, DeclInfo, EffOpInfo, Type};

use super::{
    classes, Canon, Checked, CheckedView, ClassConstraint, ClassInfo, ConstrainedScheme,
    ConstrainedSchemes, DataInfo, DeclFacts, DispatchFacts, Env, InstInfo, InstKeys,
    InterfaceFacts, MethodRef, Reports,
};

/// Checked dependency facts used to typecheck one module without dependency
/// implementation bodies.
#[derive(Clone, Debug, Default)]
pub struct TypecheckSeed {
    env: Env,
    data: BTreeMap<String, DataInfo>,
    ctors: BTreeMap<String, CtorInfo>,
    eff_ops: BTreeMap<String, EffOpInfo>,
    classes: BTreeMap<Sym, ClassInfo>,
    instances: BTreeMap<Sym, InstInfo>,
    inst_keys: InstKeys,
    canonical: Canon,
    methods: BTreeMap<Sym, MethodRef>,
    constrained: ConstrainedSchemes,
}

/// A dependency seed contained conflicting or relationally invalid facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypecheckSeedError {
    /// Two dependency interfaces assigned different facts to the same key.
    Conflict {
        /// The fact table whose key collided.
        table: &'static str,
        /// The rendered key.
        key: String,
    },
    /// One fact refers to a missing or incompatible fact in another table.
    Invalid {
        /// The fact table being validated.
        table: &'static str,
        /// The rendered key.
        key: String,
        /// The violated relationship.
        reason: String,
    },
}

impl fmt::Display for TypecheckSeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Conflict { table, key } => {
                write!(f, "conflicting typecheck seed {table} entry {key}")
            }
            Self::Invalid { table, key, reason } => {
                write!(f, "invalid typecheck seed {table} entry {key}: {reason}")
            }
        }
    }
}

impl std::error::Error for TypecheckSeedError {}

pub(crate) struct SeedClassMethod {
    pub(crate) name: Sym,
    pub(crate) ty: Type,
    pub(crate) scheme: Type,
}

pub(crate) struct TypecheckSeedBuilder {
    seed: TypecheckSeed,
}

impl TypecheckSeed {
    /// Clone all checker facts from an already checked dependency closure.
    ///
    /// # Errors
    /// Returns an error if the checked aggregate contains inconsistent
    /// cross-table facts.
    pub fn try_from_checked(checked: &Checked) -> Result<Self, TypecheckSeedError> {
        let seed = Self {
            env: checked.interface.env.clone(),
            data: checked.defs.data.clone(),
            ctors: checked.defs.ctors.clone(),
            eff_ops: checked.defs.eff_ops.clone(),
            classes: checked.dispatch.classes.clone(),
            instances: checked.dispatch.instances.clone(),
            inst_keys: checked.dispatch.inst_keys.clone(),
            canonical: checked.dispatch.canonical.clone(),
            methods: checked.dispatch.methods.clone(),
            constrained: checked.dispatch.constrained.clone(),
        };
        seed.validate()?;
        Ok(seed)
    }

    /// The value environment carried by this dependency closure.
    #[must_use]
    pub const fn environment(&self) -> &Env {
        &self.env
    }

    /// Checked nominal datatype facts.
    #[must_use]
    pub const fn data_types(&self) -> &BTreeMap<String, DataInfo> {
        &self.data
    }

    /// Checked constructor facts.
    #[must_use]
    pub const fn constructors(&self) -> &BTreeMap<String, CtorInfo> {
        &self.ctors
    }

    /// Checked effect-operation facts.
    #[must_use]
    pub const fn effect_operations(&self) -> &BTreeMap<String, EffOpInfo> {
        &self.eff_ops
    }

    /// Checked class facts.
    #[must_use]
    pub const fn classes(&self) -> &BTreeMap<Sym, ClassInfo> {
        &self.classes
    }

    /// Checked instance facts.
    #[must_use]
    pub const fn instances(&self) -> &BTreeMap<Sym, InstInfo> {
        &self.instances
    }

    /// Instance candidates indexed by class and head.
    #[must_use]
    pub const fn instance_keys(&self) -> &InstKeys {
        &self.inst_keys
    }

    /// Canonical instance selections.
    #[must_use]
    pub const fn canonical_instances(&self) -> &Canon {
        &self.canonical
    }

    /// Class method owner and field indexes.
    #[must_use]
    pub const fn methods(&self) -> &BTreeMap<Sym, MethodRef> {
        &self.methods
    }

    /// Schemes carrying class constraints.
    #[must_use]
    pub const fn constrained(&self) -> &ConstrainedSchemes {
        &self.constrained
    }

    pub(crate) fn try_extend(&mut self, other: Self) -> Result<(), TypecheckSeedError> {
        let mut merged = self.clone();
        merged.merge(other)?;
        merged.validate()?;
        *self = merged;
        Ok(())
    }

    pub(crate) fn remove_value(&mut self, name: Sym) {
        self.env.remove(&name);
        self.constrained.remove(&name);
    }

    pub(crate) fn into_rehydrated_checked(
        self,
        decls: Vec<DeclInfo>,
        facts: NodeFacts,
        seeds: u32,
    ) -> Checked {
        Checked::new(CheckedView {
            interface: InterfaceFacts {
                env: self.env,
                seeds,
            },
            defs: DeclFacts {
                data: self.data,
                ctors: self.ctors,
                decls,
                eff_ops: self.eff_ops,
            },
            facts,
            dispatch: DispatchFacts {
                classes: self.classes,
                instances: self.instances,
                inst_keys: self.inst_keys,
                canonical: self.canonical,
                methods: self.methods,
                method_effects: BTreeMap::new(),
                constrained: self.constrained,
            },
            reports: Reports {
                warnings: Vec::new(),
                holes: Vec::new(),
            },
        })
    }

    fn merge(&mut self, other: Self) -> Result<(), TypecheckSeedError> {
        merge_env(&mut self.env, &other.env)?;
        merge_map(&mut self.data, other.data, "datatype", same_data_info)?;
        merge_map(&mut self.ctors, other.ctors, "constructor", PartialEq::eq)?;
        merge_map(
            &mut self.eff_ops,
            other.eff_ops,
            "effect operation",
            same_effect_op,
        )?;
        merge_map(&mut self.classes, other.classes, "class", same_class_info)?;
        merge_map(
            &mut self.instances,
            other.instances,
            "instance",
            same_instance_info,
        )?;
        for (key, names) in other.inst_keys {
            let entries = self.inst_keys.entry(key).or_default();
            entries.extend(names);
            entries.sort_by_key(|name| name.as_str());
            entries.dedup();
        }
        merge_map(
            &mut self.canonical,
            other.canonical,
            "canonical instance",
            PartialEq::eq,
        )?;
        merge_map(&mut self.methods, other.methods, "method", PartialEq::eq)?;
        merge_map(
            &mut self.constrained,
            other.constrained,
            "constrained scheme",
            PartialEq::eq,
        )?;
        Ok(())
    }

    fn validate(&self) -> Result<(), TypecheckSeedError> {
        let mut metadata_values = BTreeSet::new();
        for name in self.ctors.keys() {
            reserve_metadata_value(&mut metadata_values, Sym::from(name.as_str()))?;
        }
        for name in self.eff_ops.keys() {
            reserve_metadata_value(&mut metadata_values, Sym::from(name.as_str()))?;
        }
        for name in self.methods.keys() {
            reserve_metadata_value(&mut metadata_values, *name)?;
        }
        for (name, info) in &self.data {
            for (tag, ctor_name) in info.ctors.iter().enumerate() {
                let ctor = self.ctors.get(ctor_name).ok_or_else(|| {
                    seed_invalid(
                        "datatype",
                        name,
                        format!("constructor {ctor_name} is missing"),
                    )
                })?;
                require_seed(
                    ctor.type_name.as_str() == name,
                    "datatype",
                    name,
                    format!("constructor {ctor_name} belongs to {}", ctor.type_name),
                )?;
                require_seed(
                    ctor.tag == tag,
                    "datatype",
                    name,
                    format!(
                        "constructor {ctor_name} has tag {}, expected {tag}",
                        ctor.tag
                    ),
                )?;
            }
        }
        for (name, info) in &self.ctors {
            require_seed(
                info.params.len() == info.param_kinds.len(),
                "constructor",
                name,
                "parameter names and kinds have different lengths",
            )?;
            let data = self.data.get(info.type_name.as_str()).ok_or_else(|| {
                seed_invalid(
                    "constructor",
                    name,
                    format!("datatype {} is missing", info.type_name),
                )
            })?;
            require_seed(
                data.ctors.get(info.tag) == Some(name),
                "constructor",
                name,
                format!(
                    "datatype {} does not list it at tag {}",
                    info.type_name, info.tag
                ),
            )?;
            require_seed(
                info.params
                    .iter()
                    .copied()
                    .map(Sym::as_str)
                    .eq(data.params.iter().map(|param| param.name.as_str())),
                "constructor",
                name,
                format!("parameter names differ from datatype {}", info.type_name),
            )?;
            require_seed(
                info.param_kinds == data.param_kinds(),
                "constructor",
                name,
                format!("parameter kinds differ from datatype {}", info.type_name),
            )?;
            // A declared constructor is instantiated from its scheme at every
            // use site, so the scheme has to travel with the fact. A class
            // dictionary is the one constructor with no use site in surface
            // syntax: the elaborator builds and matches it directly in Core, so
            // it is deliberately absent from the value environment and its
            // presence there would make `_D<Class>` a name a program could
            // write. Both directions are checked, so neither drifts.
            let has_scheme = self.env.get(&Sym::from(name.as_str())).is_some();
            if crate::names::is_dict_ctor(name) {
                require_seed(
                    !has_scheme,
                    "constructor",
                    name,
                    "class dictionary constructor has a value-environment scheme",
                )?;
            } else {
                require_seed(
                    has_scheme,
                    "constructor",
                    name,
                    "constructor scheme is missing from the value environment",
                )?;
            }
        }
        for name in self.eff_ops.keys() {
            require_seed(
                self.env.get(&Sym::from(name.as_str())).is_some(),
                "effect operation",
                name,
                "operation scheme is missing from the value environment",
            )?;
        }
        for (class, info) in &self.classes {
            for (index, (method, _)) in info.methods.iter().enumerate() {
                require_seed(
                    self.methods.get(method)
                        == Some(&MethodRef {
                            class: *class,
                            index,
                        }),
                    "class",
                    class.to_string(),
                    format!("method {method} has no matching owner/index entry"),
                )?;
                require_seed(
                    self.env.get(method).is_some(),
                    "class",
                    class.to_string(),
                    format!("method {method} is missing from the value environment"),
                )?;
            }
        }
        for (method, method_ref) in &self.methods {
            let matches = self
                .classes
                .get(&method_ref.class)
                .and_then(|info| info.methods.get(method_ref.index))
                .is_some_and(|(name, _)| name == method);
            require_seed(
                matches,
                "method",
                method.to_string(),
                format!(
                    "owner {} has no matching method at index {}",
                    method_ref.class, method_ref.index
                ),
            )?;
        }
        for (name, constrained) in &self.constrained {
            require_seed(
                self.env.get(name) == Some(&constrained.scheme),
                "constrained scheme",
                name.to_string(),
                "scheme differs from or is missing in the value environment",
            )?;
        }
        for (name, instance) in &self.instances {
            let key = classes::head_name(&instance.head).ok_or_else(|| {
                seed_invalid(
                    "instance",
                    name.to_string(),
                    "instance head has no dispatch key",
                )
            })?;
            let indexed = self
                .inst_keys
                .get(&(instance.class, key))
                .is_some_and(|names| names.contains(name));
            require_seed(
                indexed,
                "instance",
                name.to_string(),
                "instance is missing from its class/head index",
            )?;
        }
        for ((class, head), names) in &self.inst_keys {
            for name in names {
                let matches = self.instances.get(name).is_some_and(|instance| {
                    instance.class == *class
                        && classes::head_name(&instance.head) == Some(head.clone())
                });
                require_seed(
                    matches,
                    "instance index",
                    format!("{class}/{head:?}"),
                    format!("indexed instance {name} has incompatible facts"),
                )?;
            }
        }
        for (key, selected) in &self.canonical {
            require_seed(
                self.inst_keys
                    .get(key)
                    .is_some_and(|names| names.contains(selected)),
                "canonical instance",
                format!("{}/{:?}", key.0, key.1),
                format!("selected instance {selected} is not indexed"),
            )?;
        }
        Ok(())
    }
}

impl TypecheckSeedBuilder {
    pub(crate) fn new(env: Env) -> Self {
        Self {
            seed: TypecheckSeed {
                env,
                ..TypecheckSeed::default()
            },
        }
    }

    pub(crate) fn insert_constrained(
        &mut self,
        name: Sym,
        scheme: Type,
        constraints: Vec<(Sym, Type)>,
    ) -> Result<(), TypecheckSeedError> {
        insert_map(
            &mut self.seed.constrained,
            name,
            ConstrainedScheme {
                scheme,
                constraints: constraints
                    .into_iter()
                    .map(|(class, head)| ClassConstraint { class, head })
                    .collect(),
            },
            "constrained scheme",
            PartialEq::eq,
        )
    }

    pub(crate) fn insert_data(
        &mut self,
        name: String,
        info: DataInfo,
    ) -> Result<(), TypecheckSeedError> {
        insert_map(&mut self.seed.data, name, info, "datatype", same_data_info)
    }

    pub(crate) fn insert_constructor(
        &mut self,
        name: String,
        scheme: Type,
        info: CtorInfo,
    ) -> Result<(), TypecheckSeedError> {
        insert_env(&mut self.seed.env, Sym::from(name.as_str()), scheme)?;
        insert_map(
            &mut self.seed.ctors,
            name,
            info,
            "constructor",
            PartialEq::eq,
        )
    }

    pub(crate) fn insert_effect_operation(
        &mut self,
        name: String,
        scheme: Type,
        info: EffOpInfo,
    ) -> Result<(), TypecheckSeedError> {
        insert_env(&mut self.seed.env, Sym::from(name.as_str()), scheme)?;
        insert_map(
            &mut self.seed.eff_ops,
            name,
            info,
            "effect operation",
            same_effect_op,
        )
    }

    pub(crate) fn insert_class(
        &mut self,
        name: Sym,
        param: Sym,
        supers: Vec<Sym>,
        methods: Vec<SeedClassMethod>,
    ) -> Result<(), TypecheckSeedError> {
        for (index, method) in methods.iter().enumerate() {
            insert_env(&mut self.seed.env, method.name, method.scheme.clone())?;
            insert_map(
                &mut self.seed.methods,
                method.name,
                MethodRef { class: name, index },
                "method",
                PartialEq::eq,
            )?;
            insert_map(
                &mut self.seed.constrained,
                method.name,
                ConstrainedScheme {
                    scheme: method.scheme.clone(),
                    constraints: vec![ClassConstraint {
                        class: name,
                        head: Type::Var(param),
                    }],
                },
                "constrained scheme",
                PartialEq::eq,
            )?;
        }
        insert_map(
            &mut self.seed.classes,
            name,
            ClassInfo {
                param,
                supers,
                methods: methods
                    .into_iter()
                    .map(|method| (method.name, method.ty))
                    .collect(),
            },
            "class",
            same_class_info,
        )
    }

    pub(crate) fn insert_instance(
        &mut self,
        name: Sym,
        info: InstInfo,
        canonical: bool,
    ) -> Result<(), TypecheckSeedError> {
        let head = classes::head_name(&info.head).ok_or_else(|| {
            seed_invalid(
                "instance",
                name.to_string(),
                "instance head has no dispatch key",
            )
        })?;
        let key = (info.class, head);
        self.seed
            .inst_keys
            .entry(key.clone())
            .or_default()
            .push(name);
        if canonical {
            insert_map(
                &mut self.seed.canonical,
                key,
                name,
                "canonical instance",
                PartialEq::eq,
            )?;
        }
        insert_map(
            &mut self.seed.instances,
            name,
            info,
            "instance",
            same_instance_info,
        )
    }

    pub(crate) fn finish(mut self) -> Result<TypecheckSeed, TypecheckSeedError> {
        for names in self.seed.inst_keys.values_mut() {
            names.sort_by_key(|name| name.as_str());
            names.dedup();
        }
        self.seed.validate()?;
        Ok(self.seed)
    }
}

fn merge_env(target: &mut Env, source: &Env) -> Result<(), TypecheckSeedError> {
    for (name, ty) in source.iter() {
        insert_env(target, *name, ty.clone())?;
    }
    Ok(())
}

fn insert_env(target: &mut Env, name: Sym, ty: Type) -> Result<(), TypecheckSeedError> {
    if let Some(current) = target.get(&name) {
        if current != &ty {
            return Err(TypecheckSeedError::Conflict {
                table: "environment",
                key: name.to_string(),
            });
        }
    } else {
        target.insert(name, ty);
    }
    Ok(())
}

fn merge_map<K, V>(
    target: &mut BTreeMap<K, V>,
    source: BTreeMap<K, V>,
    table: &'static str,
    same: impl Fn(&V, &V) -> bool,
) -> Result<(), TypecheckSeedError>
where
    K: Ord + fmt::Debug,
{
    for (key, value) in source {
        insert_map(target, key, value, table, &same)?;
    }
    Ok(())
}

fn insert_map<K, V>(
    target: &mut BTreeMap<K, V>,
    key: K,
    value: V,
    table: &'static str,
    same: impl Fn(&V, &V) -> bool,
) -> Result<(), TypecheckSeedError>
where
    K: Ord + fmt::Debug,
{
    if let Some(current) = target.get(&key) {
        if !same(current, &value) {
            return Err(TypecheckSeedError::Conflict {
                table,
                key: format!("{key:?}"),
            });
        }
    } else {
        target.insert(key, value);
    }
    Ok(())
}

fn same_data_info(left: &DataInfo, right: &DataInfo) -> bool {
    left.params == right.params && left.ctors == right.ctors && left.repr == right.repr
}

fn same_effect_op(left: &EffOpInfo, right: &EffOpInfo) -> bool {
    left.effect_name == right.effect_name
        && left.eff_params == right.eff_params
        && left.params == right.params
        && left.ret == right.ret
        && left.grade == right.grade
}

fn same_class_info(left: &ClassInfo, right: &ClassInfo) -> bool {
    left.param == right.param && left.supers == right.supers && left.methods == right.methods
}

fn same_instance_info(left: &InstInfo, right: &InstInfo) -> bool {
    left.class == right.class
        && left.head == right.head
        && left.module == right.module
        && left.context == right.context
        && left.supers == right.supers
}

fn seed_invalid(
    table: &'static str,
    key: impl Into<String>,
    reason: impl Into<String>,
) -> TypecheckSeedError {
    TypecheckSeedError::Invalid {
        table,
        key: key.into(),
        reason: reason.into(),
    }
}

fn require_seed(
    condition: bool,
    table: &'static str,
    key: impl Into<String>,
    reason: impl Into<String>,
) -> Result<(), TypecheckSeedError> {
    if condition {
        Ok(())
    } else {
        Err(seed_invalid(table, key, reason))
    }
}

fn reserve_metadata_value(names: &mut BTreeSet<Sym>, name: Sym) -> Result<(), TypecheckSeedError> {
    if names.insert(name) {
        Ok(())
    } else {
        Err(TypecheckSeedError::Conflict {
            table: "value namespace",
            key: name.to_string(),
        })
    }
}

#[cfg(test)]
mod seed_tests {
    use super::super::NominalRepr;
    use super::{DataInfo, Env, TypecheckSeed, TypecheckSeedBuilder, TypecheckSeedError};
    use crate::sym::Sym;
    use crate::syntax::ast::Grade;
    use crate::types::{CtorInfo, EffOpInfo, Type};

    fn environment_seed(ty: Type) -> TypecheckSeed {
        let mut env = Env::new();
        env.insert(Sym::new("shared"), ty);
        TypecheckSeed {
            env,
            ..TypecheckSeed::default()
        }
    }

    #[test]
    fn conflicting_dependency_merge_is_rejected_atomically() {
        let mut seed = environment_seed(Type::Int);
        let error = seed
            .try_extend(environment_seed(Type::Bool))
            .expect_err("conflicting schemes must not overwrite one another");
        assert_eq!(
            error,
            TypecheckSeedError::Conflict {
                table: "environment",
                key: "shared".to_string(),
            }
        );
        assert_eq!(
            seed.environment().get(&Sym::new("shared")),
            Some(&Type::Int)
        );
    }

    #[test]
    fn builder_rejects_constructor_missing_from_parent_index() {
        let mut builder = TypecheckSeedBuilder::new(Env::new());
        builder
            .insert_data(
                "Container".to_string(),
                DataInfo {
                    params: Vec::new(),
                    ctors: Vec::new(),
                    repr: NominalRepr::BoxedCell,
                },
            )
            .expect("datatype fact is unique");
        builder
            .insert_constructor(
                "Hidden".to_string(),
                Type::Con(Sym::new("Container"), Vec::new()),
                CtorInfo {
                    type_name: Sym::new("Container"),
                    params: Vec::new(),
                    param_kinds: Vec::new(),
                    args: Vec::new(),
                    tag: 0,
                    fields: Vec::new(),
                },
            )
            .expect("constructor fact is unique");
        let error = builder
            .finish()
            .expect_err("a constructor must be indexed by its parent datatype");
        assert!(matches!(
            error,
            TypecheckSeedError::Invalid {
                table: "constructor",
                key,
                ..
            } if key == "Hidden"
        ));
    }

    // A class dictionary is built and matched in Core, never named in source, so
    // it is the one constructor whose scheme must stay out of the value
    // environment. Pinned from this side because the acceptance side (a seed
    // carrying the dictionary fact alone) is what every module using a class
    // already exercises.
    #[test]
    fn builder_rejects_dictionary_constructor_with_a_value_scheme() {
        let mut builder = TypecheckSeedBuilder::new(Env::new());
        builder
            .insert_data(
                "_DShow".to_string(),
                DataInfo {
                    params: Vec::new(),
                    ctors: vec!["_DShow".to_string()],
                    repr: NominalRepr::BoxedCell,
                },
            )
            .expect("datatype fact is unique");
        builder
            .insert_constructor(
                "_DShow".to_string(),
                Type::Con(Sym::new("_DShow"), Vec::new()),
                CtorInfo {
                    type_name: Sym::new("_DShow"),
                    params: Vec::new(),
                    param_kinds: Vec::new(),
                    args: Vec::new(),
                    tag: 0,
                    fields: Vec::new(),
                },
            )
            .expect("constructor fact is unique");
        let error = builder
            .finish()
            .expect_err("a dictionary constructor must not be nameable from source");
        assert!(matches!(
            error,
            TypecheckSeedError::Invalid {
                table: "constructor",
                key,
                ..
            } if key == "_DShow"
        ));
    }

    #[test]
    fn builder_rejects_cross_kind_value_scheme_conflict() {
        let mut builder = TypecheckSeedBuilder::new(Env::new());
        builder
            .insert_constructor(
                "shared".to_string(),
                Type::Int,
                CtorInfo {
                    type_name: Sym::new("Container"),
                    params: Vec::new(),
                    param_kinds: Vec::new(),
                    args: Vec::new(),
                    tag: 0,
                    fields: Vec::new(),
                },
            )
            .expect("first value fact is unique");
        let error = builder
            .insert_effect_operation(
                "shared".to_string(),
                Type::Bool,
                EffOpInfo {
                    effect_name: Sym::new("Effect"),
                    eff_params: Vec::new(),
                    params: Vec::new(),
                    ret: Type::Bool,
                    grade: Grade::Many,
                },
            )
            .expect_err("different metadata kinds must not overwrite a value scheme");
        assert_eq!(
            error,
            TypecheckSeedError::Conflict {
                table: "environment",
                key: "shared".to_string(),
            }
        );
    }

    #[test]
    fn builder_rejects_cross_kind_value_roles_with_equal_schemes() {
        let mut builder = TypecheckSeedBuilder::new(Env::new());
        builder
            .insert_data(
                "Container".to_string(),
                DataInfo {
                    params: Vec::new(),
                    ctors: vec!["shared".to_string()],
                    repr: NominalRepr::BoxedCell,
                },
            )
            .expect("datatype fact is unique");
        let scheme = Type::Con(Sym::new("Container"), Vec::new());
        builder
            .insert_constructor(
                "shared".to_string(),
                scheme.clone(),
                CtorInfo {
                    type_name: Sym::new("Container"),
                    params: Vec::new(),
                    param_kinds: Vec::new(),
                    args: Vec::new(),
                    tag: 0,
                    fields: Vec::new(),
                },
            )
            .expect("constructor scheme is unique");
        builder
            .insert_effect_operation(
                "shared".to_string(),
                scheme.clone(),
                EffOpInfo {
                    effect_name: Sym::new("Effect"),
                    eff_params: Vec::new(),
                    params: Vec::new(),
                    ret: scheme,
                    grade: Grade::Many,
                },
            )
            .expect("the equal environment scheme does not hide the role collision");
        let error = builder
            .finish()
            .expect_err("one value name cannot denote two metadata roles");
        assert_eq!(
            error,
            TypecheckSeedError::Conflict {
                table: "value namespace",
                key: "shared".to_string(),
            }
        );
    }
}
