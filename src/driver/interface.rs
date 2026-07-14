use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::sym::Sym;
use crate::syntax::ast::{Grade, Program};
use crate::types::ty::Kind;
use crate::types::{
    Canon, Checked, ClassInfo, CtorInfo, DataInfo, EffOpInfo, Env, InstInfo, InstKeys, Type,
    TypecheckSeed,
};

use super::identity::{interface_entry, ModuleInterface, ModuleInterfaceEntry};

const VALUE_METADATA_KIND: &str = "value-metadata";
const DATA_METADATA_KIND: &str = "data-metadata";
const CTOR_METADATA_KIND: &str = "constructor-metadata";
const EFFECT_OP_METADATA_KIND: &str = "effect-op-metadata";
const CLASS_METADATA_KIND: &str = "class-metadata";
const INSTANCE_METADATA_KIND: &str = "instance-metadata";

/// Checked interface facts reconstructed without dependency implementation bodies.
#[derive(Clone, Debug)]
pub struct RehydratedModuleInterface {
    pub env: Env,
    pub constrained: BTreeMap<Sym, (Type, Vec<(Sym, Type)>)>,
    pub data: BTreeMap<String, DataInfo>,
    pub ctors: BTreeMap<String, CtorInfo>,
    pub eff_ops: BTreeMap<String, EffOpInfo>,
    pub classes: BTreeMap<Sym, ClassInfo>,
    pub methods: BTreeMap<Sym, (Sym, usize)>,
    pub instances: BTreeMap<Sym, InstInfo>,
    pub inst_keys: InstKeys,
    pub canonical: Canon,
}

impl RehydratedModuleInterface {
    /// Convert these facts into the typechecker's dependency seed.
    #[must_use]
    pub fn typecheck_seed(&self) -> TypecheckSeed {
        TypecheckSeed {
            env: self.env.clone(),
            data: self.data.clone(),
            ctors: self.ctors.clone(),
            eff_ops: self.eff_ops.clone(),
            classes: self.classes.clone(),
            instances: self.instances.clone(),
            inst_keys: self.inst_keys.clone(),
            canonical: self.canonical.clone(),
            methods: self.methods.clone(),
            constrained: self.constrained.clone(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum KindWire {
    Type,
    Row,
    Nat,
    Fun(Box<Self>, Box<Self>),
}

#[derive(Serialize, Deserialize)]
struct ValuePayload {
    scheme: String,
    constraints: Vec<(String, String)>,
}

#[derive(Serialize, Deserialize)]
struct DataPayload {
    params: Vec<String>,
    param_kinds: Vec<KindWire>,
    ctors: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct CtorPayload {
    type_name: String,
    params: Vec<String>,
    param_kinds: Vec<KindWire>,
    args: Vec<String>,
    tag: usize,
    fields: Vec<String>,
    scheme: String,
}

#[derive(Serialize, Deserialize)]
struct EffectOpPayload {
    effect_name: String,
    eff_params: Vec<String>,
    params: Vec<String>,
    ret: String,
    grade: String,
    scheme: String,
}

#[derive(Serialize, Deserialize)]
struct ClassPayload {
    param: String,
    supers: Vec<String>,
    methods: Vec<MethodPayload>,
}

#[derive(Serialize, Deserialize)]
struct MethodPayload {
    name: String,
    ty: String,
    scheme: String,
}

#[derive(Serialize, Deserialize)]
struct InstancePayload {
    class: String,
    head: String,
    module: String,
    context: Vec<(String, String)>,
    supers: Vec<(String, String)>,
    canonical: bool,
}

pub(super) fn exported_names(entry: &Program, module_path: Option<&str>) -> BTreeSet<String> {
    entry
        .exports
        .iter()
        .map(|name| module_path.map_or_else(|| name.clone(), |path| format!("{path}.{name}")))
        .collect()
}

pub(super) fn metadata_entries(
    entry: &Program,
    module_path: Option<&str>,
    checked: &Checked,
) -> Result<Vec<ModuleInterfaceEntry>, serde_json::Error> {
    let exports = exported_names(entry, module_path);
    let opaques = entry
        .opaques
        .iter()
        .map(|name| module_path.map_or_else(|| name.clone(), |path| format!("{path}.{name}")))
        .collect::<BTreeSet<_>>();
    let mut entries = Vec::new();
    for name in &exports {
        if let Some((scheme, constraints)) = checked.constrained.get(&Sym::from(name.as_str())) {
            entries.push(payload_entry(
                VALUE_METADATA_KIND,
                name,
                &ValuePayload {
                    scheme: scheme.show(),
                    constraints: show_constraints(constraints),
                },
            )?);
        }
        if let Some(info) = checked.data.get(name) {
            entries.push(payload_entry(
                DATA_METADATA_KIND,
                name,
                &DataPayload {
                    params: info.params.clone(),
                    param_kinds: info.param_kinds.iter().map(kind_to_wire).collect(),
                    ctors: if opaques.contains(name) {
                        Vec::new()
                    } else {
                        info.ctors.clone()
                    },
                },
            )?);
            if !opaques.contains(name) {
                for ctor_name in &info.ctors {
                    if let Some(ctor) = checked.ctors.get(ctor_name) {
                        let scheme = checked
                            .env
                            .get(&Sym::from(ctor_name.as_str()))
                            .map_or_else(String::new, Type::show);
                        entries.push(payload_entry(
                            CTOR_METADATA_KIND,
                            ctor_name,
                            &CtorPayload {
                                type_name: ctor.type_name.to_string(),
                                params: ctor.params.iter().map(ToString::to_string).collect(),
                                param_kinds: ctor.param_kinds.iter().map(kind_to_wire).collect(),
                                args: ctor.args.iter().map(Type::show).collect(),
                                tag: ctor.tag,
                                fields: ctor.fields.iter().map(ToString::to_string).collect(),
                                scheme,
                            },
                        )?);
                    }
                }
            }
        }
        if let Some(class) = checked.classes.get(&Sym::from(name.as_str())) {
            entries.push(payload_entry(
                CLASS_METADATA_KIND,
                name,
                &ClassPayload {
                    param: class.param.to_string(),
                    supers: class.supers.iter().map(ToString::to_string).collect(),
                    methods: class
                        .methods
                        .iter()
                        .map(|(method, ty)| MethodPayload {
                            name: method.to_string(),
                            ty: ty.show(),
                            scheme: checked.env.get(method).map_or_else(String::new, Type::show),
                        })
                        .collect(),
                },
            )?);
        }
    }
    for (name, op) in &checked.eff_ops {
        if exports.contains(op.effect_name.as_str()) {
            entries.push(payload_entry(
                EFFECT_OP_METADATA_KIND,
                name,
                &EffectOpPayload {
                    effect_name: op.effect_name.to_string(),
                    eff_params: op.eff_params.iter().map(ToString::to_string).collect(),
                    params: op.params.iter().map(Type::show).collect(),
                    ret: op.ret.show(),
                    grade: op.grade.word().to_string(),
                    scheme: checked
                        .env
                        .get(&Sym::from(name.as_str()))
                        .map_or_else(String::new, Type::show),
                },
            )?);
        }
    }
    let root_instances = entry
        .instances
        .iter()
        .map(|instance| instance.name.as_str())
        .collect::<BTreeSet<_>>();
    for (name, instance) in &checked.instances {
        let exported_head = matches!(
            &instance.head,
            Type::Con(head, _) if exports.contains(head.as_str())
        );
        let owns_module = module_path.map_or_else(
            || instance.module.is_empty(),
            |path| instance.module == path,
        );
        if owns_module && (root_instances.contains(name.as_str()) || exported_head) {
            entries.push(payload_entry(
                INSTANCE_METADATA_KIND,
                name.as_str(),
                &InstancePayload {
                    class: instance.class.to_string(),
                    head: instance.head.show(),
                    module: instance.module.clone(),
                    context: show_constraints(&instance.context),
                    supers: show_constraints(&instance.supers),
                    canonical: checked.canonical.values().any(|selected| selected == name),
                },
            )?);
        }
    }
    Ok(entries)
}

pub(super) fn rehydrate(interface: &ModuleInterface) -> Result<RehydratedModuleInterface, String> {
    let mut facts = RehydratedModuleInterface {
        env: interface.exported_value_env()?,
        constrained: BTreeMap::new(),
        data: BTreeMap::new(),
        ctors: BTreeMap::new(),
        eff_ops: BTreeMap::new(),
        classes: BTreeMap::new(),
        methods: BTreeMap::new(),
        instances: BTreeMap::new(),
        inst_keys: BTreeMap::new(),
        canonical: BTreeMap::new(),
    };
    for entry in &interface.entries {
        match entry.kind.as_str() {
            VALUE_METADATA_KIND => {
                let payload: ValuePayload = parse_payload(entry)?;
                facts.constrained.insert(
                    Sym::from(entry.name.as_str()),
                    (
                        parse_type(&entry.name, &payload.scheme)?,
                        parse_constraints(&entry.name, payload.constraints)?,
                    ),
                );
            }
            DATA_METADATA_KIND => {
                let payload: DataPayload = parse_payload(entry)?;
                facts.data.insert(
                    entry.name.clone(),
                    DataInfo {
                        params: payload.params,
                        param_kinds: payload
                            .param_kinds
                            .into_iter()
                            .map(kind_from_wire)
                            .collect(),
                        ctors: payload.ctors,
                    },
                );
            }
            CTOR_METADATA_KIND => {
                let payload: CtorPayload = parse_payload(entry)?;
                let args = parse_types(&entry.name, payload.args)?;
                let scheme = parse_type(&entry.name, &payload.scheme)?;
                facts.env.insert(Sym::from(entry.name.as_str()), scheme);
                facts.ctors.insert(
                    entry.name.clone(),
                    CtorInfo {
                        type_name: Sym::from(payload.type_name),
                        params: payload.params.into_iter().map(Sym::from).collect(),
                        param_kinds: payload
                            .param_kinds
                            .into_iter()
                            .map(kind_from_wire)
                            .collect(),
                        args,
                        tag: payload.tag,
                        fields: payload.fields.into_iter().map(Sym::from).collect(),
                    },
                );
            }
            EFFECT_OP_METADATA_KIND => {
                let payload: EffectOpPayload = parse_payload(entry)?;
                facts.env.insert(
                    Sym::from(entry.name.as_str()),
                    parse_type(&entry.name, &payload.scheme)?,
                );
                facts.eff_ops.insert(
                    entry.name.clone(),
                    EffOpInfo {
                        effect_name: Sym::from(payload.effect_name),
                        eff_params: payload.eff_params.into_iter().map(Sym::from).collect(),
                        params: parse_types(&entry.name, payload.params)?,
                        ret: parse_type(&entry.name, &payload.ret)?,
                        grade: Grade::parse(&payload.grade)
                            .ok_or_else(|| format!("invalid effect grade {:?}", payload.grade))?,
                    },
                );
            }
            CLASS_METADATA_KIND => {
                let payload: ClassPayload = parse_payload(entry)?;
                let methods = payload
                    .methods
                    .into_iter()
                    .map(|method| {
                        Ok((
                            Sym::from(method.name),
                            parse_type(&entry.name, &method.ty)?,
                            parse_type(&entry.name, &method.scheme)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                let class_name = Sym::from(entry.name.as_str());
                let class_param = Sym::from(payload.param.as_str());
                for (index, (name, _, scheme)) in methods.iter().enumerate() {
                    facts.env.insert(*name, scheme.clone());
                    facts.methods.insert(*name, (class_name, index));
                    facts.constrained.insert(
                        *name,
                        (scheme.clone(), vec![(class_name, Type::Var(class_param))]),
                    );
                }
                facts.classes.insert(
                    class_name,
                    ClassInfo {
                        param: class_param,
                        supers: payload.supers.into_iter().map(Sym::from).collect(),
                        methods: methods
                            .into_iter()
                            .map(|(name, ty, _)| (name, ty))
                            .collect(),
                    },
                );
            }
            INSTANCE_METADATA_KIND => {
                let payload: InstancePayload = parse_payload(entry)?;
                let name = Sym::from(entry.name.as_str());
                let class = Sym::from(payload.class);
                let head = parse_type(&entry.name, &payload.head)?;
                let key = crate::tc::instance_head_key(&head)
                    .ok_or_else(|| format!("invalid instance head {} in interface", head.show()))?;
                facts
                    .inst_keys
                    .entry((class, key.clone()))
                    .or_default()
                    .push(name);
                if payload.canonical {
                    facts.canonical.insert((class, key), name);
                }
                facts.instances.insert(
                    name,
                    InstInfo {
                        class,
                        head,
                        module: payload.module,
                        context: parse_constraints(&entry.name, payload.context)?,
                        supers: parse_constraints(&entry.name, payload.supers)?,
                    },
                );
            }
            _ => {}
        }
    }
    Ok(facts)
}

fn payload_entry(
    kind: &str,
    name: &str,
    payload: &impl Serialize,
) -> Result<ModuleInterfaceEntry, serde_json::Error> {
    Ok(interface_entry(kind, name, serde_json::to_string(payload)?))
}

fn parse_payload<T: for<'de> Deserialize<'de>>(entry: &ModuleInterfaceEntry) -> Result<T, String> {
    serde_json::from_str(&entry.signature)
        .map_err(|error| format!("invalid {} row {}: {error}", entry.kind, entry.name))
}

fn parse_type(name: &str, ty: &str) -> Result<Type, String> {
    crate::tc::parse_checked_signature(name, ty).map_err(|error| error.to_string())
}

fn parse_types(name: &str, types: Vec<String>) -> Result<Vec<Type>, String> {
    types.into_iter().map(|ty| parse_type(name, &ty)).collect()
}

fn show_constraints(constraints: &[(Sym, Type)]) -> Vec<(String, String)> {
    constraints
        .iter()
        .map(|(class, ty)| (class.to_string(), ty.show()))
        .collect()
}

fn parse_constraints(
    name: &str,
    constraints: Vec<(String, String)>,
) -> Result<Vec<(Sym, Type)>, String> {
    constraints
        .into_iter()
        .map(|(class, ty)| Ok((Sym::from(class), parse_type(name, &ty)?)))
        .collect()
}

fn kind_to_wire(kind: &Kind) -> KindWire {
    match kind {
        Kind::Type => KindWire::Type,
        Kind::Row => KindWire::Row,
        Kind::Nat => KindWire::Nat,
        Kind::Fun(param, result) => KindWire::Fun(
            Box::new(kind_to_wire(param)),
            Box::new(kind_to_wire(result)),
        ),
    }
}

fn kind_from_wire(kind: KindWire) -> Kind {
    match kind {
        KindWire::Type => Kind::Type,
        KindWire::Row => Kind::Row,
        KindWire::Nat => Kind::Nat,
        KindWire::Fun(param, result) => Kind::Fun(
            Box::new(kind_from_wire(*param)),
            Box::new(kind_from_wire(*result)),
        ),
    }
}
