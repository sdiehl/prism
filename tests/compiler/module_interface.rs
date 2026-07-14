use prism::{
    check_with_seed, module_interface, with_prelude, ModuleInterface, Root, Sym,
    MODULE_INTERFACE_FORMAT,
};

const FIRST_CTOR_TAG: usize = 0;
const SECOND_CTOR_TAG: usize = 1;

fn interface(src: &str) -> ModuleInterface {
    module_interface(
        src,
        &with_prelude(src),
        &[Root::Embedded(prism::stdlib::STDLIB)],
    )
    .unwrap()
}

#[test]
fn implementation_edit_preserves_checked_interface() {
    let before = interface("pub fn answer(x : Int) : Int = x + 1\n");
    let after = interface("pub fn answer(x : Int) : Int = x + 2\n");
    assert_eq!(before.digest, after.digest);
    assert_eq!(before.entries, after.entries);
    let importer = "fn use_answer() : Int = answer(41)\n";
    let before_checked =
        check_with_seed(importer, &before.rehydrate().unwrap().typecheck_seed()).unwrap();
    let after_checked =
        check_with_seed(importer, &after.rehydrate().unwrap().typecheck_seed()).unwrap();
    assert_eq!(
        before_checked
            .decls
            .first()
            .expect("before importer")
            .ty
            .show(),
        after_checked
            .decls
            .first()
            .expect("after importer")
            .ty
            .show()
    );

    let signature_edit = interface("pub fn answer(x : Int) : String = show(x)\n");
    assert_ne!(before.digest, signature_edit.digest);
}

#[test]
fn interface_projection_is_versioned_and_self_verifying() {
    let mut interface = interface("pub fn answer() : Int = 42\n");
    assert_eq!(interface.format, MODULE_INTERFACE_FORMAT);
    let json = interface.to_json().unwrap();
    assert_eq!(ModuleInterface::from_json(&json).unwrap(), interface);

    let corrupt = json.replace(&interface.digest, &"0".repeat(interface.digest.len()));
    assert!(ModuleInterface::from_json(&corrupt).is_err());

    interface.entries[0].digest = "0".repeat(interface.entries[0].digest.len());
    let error = ModuleInterface::from_json(&interface.to_json().unwrap()).unwrap_err();
    assert!(error.contains("row"));
    assert!(interface.exported_value_env().is_err());
}

#[test]
fn exported_value_schemes_rehydrate_without_bodies() {
    let interface = interface("pub fn answer(x : Int) : Int = x + 1\n");
    let env = interface.exported_value_env().unwrap();
    let answer = env.get(&Sym::from("answer")).expect("exported answer");
    assert_eq!(answer.show(), "(Int) -> Int");
    assert!(!env.contains_key(&Sym::from("println")));
}

#[test]
fn effectful_exported_value_scheme_rehydrates_once() {
    let interface = interface(concat!(
        "effect Pulse\n",
        "  pulse(Int) : Unit\n",
        "pub fn emit(x : Int) : Unit ! {Pulse} = pulse(x)\n",
    ));
    let entry = interface
        .entries
        .iter()
        .find(|entry| entry.kind == "value" && entry.name == "emit")
        .expect("effectful export row");
    assert_eq!(entry.signature, "(Int) -> Unit ! {Pulse}");
    let env = interface.exported_value_env().unwrap();
    let emit = env.get(&Sym::from("emit")).expect("exported emit");
    assert_eq!(emit.show(), "(Int) -> Unit ! {Pulse}");
}

#[test]
fn transparent_data_shape_and_constructor_facts_rehydrate() {
    let interface = interface(
        "pub type Shape = Circle(Int) | Square(Int) deriving (Eq)\n\
         pub fn area(_shape : Shape) : Int = 0\n",
    );
    let json = interface.to_json().unwrap();
    let decoded = ModuleInterface::from_json(&json).unwrap();
    let facts = decoded.rehydrate().unwrap();

    let shape = facts.data.get("Shape").expect("exported data metadata");
    assert_eq!(shape.ctors, ["Circle", "Square"]);
    assert_eq!(facts.ctors["Circle"].tag, FIRST_CTOR_TAG);
    assert_eq!(facts.ctors["Square"].tag, SECOND_CTOR_TAG);
    assert!(facts.env.contains_key(&Sym::from("Circle")));
    assert!(facts.env.contains_key(&Sym::from("Square")));
    assert!(facts
        .instances
        .values()
        .any(|instance| instance.head.show() == "Shape"));

    let importer = r"fn radius(shape : Shape) : Int =
  match shape of
    Circle(r) => r
    Square(w) => w
";
    let checked = check_with_seed(importer, &facts.typecheck_seed()).unwrap();
    assert!(checked.decls.iter().any(|decl| decl.name == "radius"));
}

#[test]
fn opaque_data_rehydrates_shape_without_constructors() {
    let interface = interface(
        "opaque type Counter = Counter(Int)\n\
         pub fn zero() : Counter = Counter(0)\n",
    );
    let facts = interface.rehydrate().unwrap();
    assert!(facts.data["Counter"].ctors.is_empty());
    assert!(!facts.ctors.contains_key("Counter"));
    assert!(!facts.env.contains_key(&Sym::from("Counter")));
}

#[test]
fn effect_class_and_instance_facts_rehydrate() {
    let interface = interface(
        r"pub effect Tick
  tick(Unit) : Int
pub class Identity(a)
  identity : (a) -> a
instance identityInt : Identity(Int)
  fn identity(x) = x
canonical Identity(Int) = identityInt
pub fn generic(x : a) : a given Identity(a) = identity(x)
",
    );
    let facts = interface.rehydrate().unwrap();

    let tick = facts
        .eff_ops
        .get("tick")
        .expect("exported effect operation");
    assert_eq!(tick.effect_name, Sym::from("Tick"));
    let identity = facts
        .classes
        .get(&Sym::from("Identity"))
        .expect("exported class");
    assert_eq!(
        identity.methods.first().expect("identity method").0,
        Sym::from("identity")
    );
    assert!(facts.env.contains_key(&Sym::from("identity")));
    assert!(facts.constrained.contains_key(&Sym::from("generic")));
    assert_eq!(
        facts.methods[&Sym::from("identity")].0,
        Sym::from("Identity")
    );
    assert!(facts.instances.contains_key(&Sym::from("identityInt")));
    assert!(facts
        .inst_keys
        .values()
        .any(|instances| instances.contains(&Sym::from("identityInt"))));
    assert!(facts
        .canonical
        .values()
        .any(|instance| *instance == Sym::from("identityInt")));

    let importer = r"fn use_tick() : Int ! {Tick} = tick(())
fn use_identity(x : Int) : Int = identity(x)
fn use_generic(x : Int) : Int = generic(x)
";
    let checked = check_with_seed(importer, &facts.typecheck_seed()).unwrap();
    assert!(checked.decls.iter().any(|decl| decl.name == "use_tick"));
    assert!(checked.decls.iter().any(|decl| decl.name == "use_identity"));
    assert!(checked.decls.iter().any(|decl| decl.name == "use_generic"));
}
