use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::sym::Sym;
use crate::syntax::ast::{Grade, Program};
use crate::tc::{SeedClassMethod, TypecheckSeedBuilder};
use crate::types::ty::Kind;
use crate::types::{
    Checked, CtorInfo, DataInfo, EffOpInfo, InstInfo, NominalRepr, Type, TypeParameter,
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
    seed: TypecheckSeed,
}

impl RehydratedModuleInterface {
    /// Convert these facts into the typechecker's dependency seed.
    #[must_use]
    pub fn typecheck_seed(&self) -> TypecheckSeed {
        self.seed.clone()
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
    repr: NominalReprWire,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum NominalReprWire {
    BoxedCell,
    Transparent,
    Vec128,
}

impl From<NominalRepr> for NominalReprWire {
    fn from(repr: NominalRepr) -> Self {
        match repr {
            NominalRepr::BoxedCell => Self::BoxedCell,
            NominalRepr::Transparent => Self::Transparent,
            NominalRepr::Vec128 => Self::Vec128,
        }
    }
}

impl From<NominalReprWire> for NominalRepr {
    fn from(repr: NominalReprWire) -> Self {
        match repr {
            NominalReprWire::BoxedCell => Self::BoxedCell,
            NominalReprWire::Transparent => Self::Transparent,
            NominalReprWire::Vec128 => Self::Vec128,
        }
    }
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

// The canonical names a module re-exports through its `pub import`s. An
// explicit list names each forwarded item; a glob forwards everything the
// source module contributed to this module's checked seed, recognized by its
// canonical prefix. The payloads all live in `checked` already, because the
// source's interface seeded this module's check, so forwarding is a lookup,
// not a recomputation. A consumer's environment then rehydrates re-exported
// values, types, and constructors without loading the source module's own
// interface, which the module build does not do for transitive dependencies.
fn reexported_names(entry: &Program, checked: &Checked) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for import in entry.imports.iter().filter(|import| import.reexport) {
        let path = import.path.join(".");
        if let Some(names) = &import.names {
            for name in names {
                out.insert(format!("{path}.{name}"));
            }
        } else {
            let prefix = format!("{path}.");
            for key in checked.defs.data.keys() {
                if key.starts_with(&prefix) {
                    out.insert(key.clone());
                }
            }
            for key in checked.dispatch.constrained.keys() {
                let key = key.to_string();
                if key.starts_with(&prefix) {
                    out.insert(key);
                }
            }
            for key in checked.dispatch.classes.keys() {
                let key = key.to_string();
                if key.starts_with(&prefix) {
                    out.insert(key);
                }
            }
        }
    }
    out
}

pub(super) fn metadata_entries(
    entry: &Program,
    module_path: Option<&str>,
    checked: &Checked,
) -> Result<Vec<ModuleInterfaceEntry>, serde_json::Error> {
    let mut exports = exported_names(entry, module_path);
    exports.extend(reexported_names(entry, checked));
    let opaques = entry
        .opaques
        .iter()
        .map(|name| module_path.map_or_else(|| name.clone(), |path| format!("{path}.{name}")))
        .collect::<BTreeSet<_>>();
    let mut entries = Vec::new();
    for name in &exports {
        if let Some(constrained) = checked.dispatch.constrained.get(&Sym::from(name.as_str())) {
            let constraints = constrained
                .constraints
                .iter()
                .map(|c| (c.class, c.head.clone()))
                .collect::<Vec<_>>();
            entries.push(payload_entry(
                VALUE_METADATA_KIND,
                name,
                &ValuePayload {
                    scheme: constrained.scheme.show(),
                    constraints: show_constraints(&constraints),
                },
            )?);
        }
        if let Some(info) = checked.defs.data.get(name) {
            entries.push(payload_entry(
                DATA_METADATA_KIND,
                name,
                &DataPayload {
                    params: info.param_names(),
                    param_kinds: info.param_kinds().iter().map(kind_to_wire).collect(),
                    ctors: if opaques.contains(name) {
                        Vec::new()
                    } else {
                        info.ctors.clone()
                    },
                    repr: info.repr.into(),
                },
            )?);
            if !opaques.contains(name) {
                for ctor_name in &info.ctors {
                    if let Some(ctor) = checked.defs.ctors.get(ctor_name) {
                        let scheme = checked
                            .interface
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
        if let Some(class) = checked.dispatch.classes.get(&Sym::from(name.as_str())) {
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
                            scheme: checked
                                .interface
                                .env
                                .get(method)
                                .map_or_else(String::new, Type::show),
                        })
                        .collect(),
                },
            )?);
        }
    }
    for (name, op) in &checked.defs.eff_ops {
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
                        .interface
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
    for (name, instance) in &checked.dispatch.instances {
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
                    canonical: checked
                        .dispatch
                        .canonical
                        .values()
                        .any(|selected| selected == name),
                },
            )?);
        }
    }
    Ok(entries)
}

pub(super) fn rehydrate(interface: &ModuleInterface) -> Result<RehydratedModuleInterface, String> {
    let mut facts = TypecheckSeedBuilder::new(interface.exported_value_env()?);
    for entry in &interface.entries {
        match entry.kind.as_str() {
            VALUE_METADATA_KIND => {
                let payload: ValuePayload = parse_payload(entry)?;
                facts
                    .insert_constrained(
                        Sym::from(entry.name.as_str()),
                        parse_type(&entry.name, &payload.scheme)?,
                        parse_constraints(&entry.name, payload.constraints)?,
                    )
                    .map_err(|error| error.to_string())?;
            }
            DATA_METADATA_KIND => {
                let payload: DataPayload = parse_payload(entry)?;
                if payload.params.len() != payload.param_kinds.len() {
                    return Err(format!(
                        "data `{}` has {} parameters but {} kinds",
                        entry.name,
                        payload.params.len(),
                        payload.param_kinds.len()
                    ));
                }
                facts
                    .insert_data(
                        entry.name.clone(),
                        DataInfo {
                            params: payload
                                .params
                                .into_iter()
                                .zip(payload.param_kinds.into_iter().map(kind_from_wire))
                                .map(|(name, kind)| TypeParameter { name, kind })
                                .collect(),
                            ctors: payload.ctors,
                            repr: payload.repr.into(),
                        },
                    )
                    .map_err(|error| error.to_string())?;
            }
            CTOR_METADATA_KIND => {
                let payload: CtorPayload = parse_payload(entry)?;
                let args = parse_types(&entry.name, payload.args)?;
                let scheme = parse_type(&entry.name, &payload.scheme)?;
                facts
                    .insert_constructor(
                        entry.name.clone(),
                        scheme,
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
                    )
                    .map_err(|error| error.to_string())?;
            }
            EFFECT_OP_METADATA_KIND => {
                let payload: EffectOpPayload = parse_payload(entry)?;
                let scheme = parse_type(&entry.name, &payload.scheme)?;
                facts
                    .insert_effect_operation(
                        entry.name.clone(),
                        scheme,
                        EffOpInfo {
                            effect_name: Sym::from(payload.effect_name),
                            eff_params: payload.eff_params.into_iter().map(Sym::from).collect(),
                            params: parse_types(&entry.name, payload.params)?,
                            ret: parse_type(&entry.name, &payload.ret)?,
                            grade: Grade::parse(&payload.grade).ok_or_else(|| {
                                format!("invalid effect grade {:?}", payload.grade)
                            })?,
                        },
                    )
                    .map_err(|error| error.to_string())?;
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
                facts
                    .insert_class(
                        class_name,
                        class_param,
                        payload.supers.into_iter().map(Sym::from).collect(),
                        methods
                            .into_iter()
                            .map(|(name, ty, scheme)| SeedClassMethod { name, ty, scheme })
                            .collect(),
                    )
                    .map_err(|error| error.to_string())?;
            }
            INSTANCE_METADATA_KIND => {
                let payload: InstancePayload = parse_payload(entry)?;
                let name = Sym::from(entry.name.as_str());
                let class = Sym::from(payload.class);
                let head = parse_type(&entry.name, &payload.head)?;
                facts
                    .insert_instance(
                        name,
                        InstInfo {
                            class,
                            head,
                            module: payload.module,
                            context: parse_constraints(&entry.name, payload.context)?,
                            supers: parse_constraints(&entry.name, payload.supers)?,
                        },
                        payload.canonical,
                    )
                    .map_err(|error| error.to_string())?;
            }
            _ => {}
        }
    }
    facts
        .finish()
        .map(|seed| RehydratedModuleInterface { seed })
        .map_err(|error| error.to_string())
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
