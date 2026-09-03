use prism::core::Digest;
use prism::types::NominalRepr;
use prism::{
    check_with_seed, module_interface, with_prelude, Error, ModuleInterface, Root, Sym,
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
            .defs
            .decls
            .first()
            .expect("before importer")
            .ty
            .show(),
        after_checked
            .defs
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

    let corrupt = json.replace(
        interface.digest.as_str(),
        &"0".repeat(interface.digest.len()),
    );
    assert!(ModuleInterface::from_json(&corrupt).is_err());

    interface.entries[0].digest = Digest::from("0".repeat(interface.entries[0].digest.len()));
    let error = ModuleInterface::from_json(&interface.to_json().unwrap()).unwrap_err();
    assert!(error.contains("row"));
    assert!(interface.exported_value_env().is_err());
}

#[test]
fn multiplicity_rows_survive_the_interface() {
    let interface = interface(
        "pub fn twice(g : ((Int) -> Int) @ many, x : Int) : Int = g(g(x))\n\
         pub fn apply1(g : ((Int) -> Int) @ once, x : Int) : Int = g(x)\n",
    );
    let env = interface.exported_value_env().unwrap();
    assert_eq!(
        env.get(&Sym::from("twice")).expect("exported twice").show(),
        "(((Int) -> Int) @ many, Int) -> Int"
    );
    assert_eq!(
        env.get(&Sym::from("apply1"))
            .expect("exported apply1")
            .show(),
        "(((Int) -> Int) @ once, Int) -> Int"
    );
    // The rehydrated schemes still carry the contravariant multiplicity
    // relation: a `@ once` closure fits the imported `@ once` slot but is
    // rejected by the imported `@ many` slot.
    let seed = interface.rehydrate().unwrap().typecheck_seed();
    let ok = "fn f(g : ((Int) -> Int) @ once) : Int = apply1(g, 1)\n";
    assert!(
        check_with_seed(ok, &seed).is_ok(),
        "a `@ once` closure must fit an imported `@ once` slot"
    );
    let bad = "fn f(g : ((Int) -> Int) @ once) : Int = twice(g, 1)\n";
    assert!(
        check_with_seed(bad, &seed).is_err(),
        "a `@ once` closure must be rejected by an imported `@ many` slot"
    );
}

#[test]
fn callable_noalloc_demand_survives_the_interface() {
    let interface =
        interface("pub fn iterate(f : ((Int) -> Int) @ noalloc, x : Int) : Int = f(f(x))\n");
    let env = interface.exported_value_env().unwrap();
    assert_eq!(
        env.get(&Sym::from("iterate"))
            .expect("exported iterate")
            .show(),
        "(((Int) -> Int) @ noalloc, Int) -> Int"
    );
    interface.rehydrate().unwrap();
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
    let seed = decoded.rehydrate().unwrap().typecheck_seed();

    let shape = seed
        .data_types()
        .get("Shape")
        .expect("exported data metadata");
    assert_eq!(shape.ctors, ["Circle", "Square"]);
    assert_eq!(shape.repr, NominalRepr::BoxedCell);
    assert_eq!(seed.constructors()["Circle"].tag, FIRST_CTOR_TAG);
    assert_eq!(seed.constructors()["Square"].tag, SECOND_CTOR_TAG);
    assert!(seed.environment().contains_key(&Sym::from("Circle")));
    assert!(seed.environment().contains_key(&Sym::from("Square")));
    assert!(seed
        .instances()
        .values()
        .any(|instance| instance.head.show() == "Shape"));

    let importer = r"fn radius(shape : Shape) : Int =
  match shape of
    Circle(r) => r
    Square(w) => w
";
    let checked = check_with_seed(importer, &seed).unwrap();
    assert!(checked.defs.decls.iter().any(|decl| decl.name == "radius"));
}

#[test]
fn opaque_data_rehydrates_shape_without_constructors() {
    let interface = interface(
        "opaque type Counter = Counter(Int)\n\
         pub fn zero() : Counter = Counter(0)\n",
    );
    let seed = interface.rehydrate().unwrap().typecheck_seed();
    assert!(seed.data_types()["Counter"].ctors.is_empty());
    assert_eq!(seed.data_types()["Counter"].repr, NominalRepr::BoxedCell);
    assert!(!seed.constructors().contains_key("Counter"));
    assert!(!seed.environment().contains_key(&Sym::from("Counter")));

    check_with_seed("fn maybe(x : Counter) : OrNull(Counter) = This(x)\n", &seed)
        .expect("opaque ordinary data retains its boxed representation evidence");
}

#[test]
fn opaque_newtype_keeps_transparent_representation_evidence() {
    let interface = interface(
        "opaque newtype Zero = Zero(Unit)\n\
         pub fn zero() : Zero = Zero(())\n",
    );
    let seed = interface.rehydrate().unwrap().typecheck_seed();
    assert!(seed.data_types()["Zero"].ctors.is_empty());
    assert_eq!(seed.data_types()["Zero"].repr, NominalRepr::Transparent);

    let error = check_with_seed("fn maybe(x : Zero) : OrNull(Zero) = This(x)\n", &seed)
        .expect_err("opacity cannot turn a transparent newtype into a boxed cell");
    let Error::Type(error) = error else {
        panic!("expected a type error, got {error}");
    };
    assert_eq!(error.code(), Some("E1019"));
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
    let seed = interface.rehydrate().unwrap().typecheck_seed();

    let tick = seed
        .effect_operations()
        .get("tick")
        .expect("exported effect operation");
    assert_eq!(tick.effect_name, Sym::from("Tick"));
    let identity = seed
        .classes()
        .get(&Sym::from("Identity"))
        .expect("exported class");
    assert_eq!(
        identity.methods.first().expect("identity method").0,
        Sym::from("identity")
    );
    assert!(seed.environment().contains_key(&Sym::from("identity")));
    assert!(seed.constrained().contains_key(&Sym::from("generic")));
    assert_eq!(
        seed.methods()[&Sym::from("identity")].class,
        Sym::from("Identity")
    );
    assert!(seed.instances().contains_key(&Sym::from("identityInt")));
    assert!(seed
        .instance_keys()
        .values()
        .any(|instances| instances.contains(&Sym::from("identityInt"))));
    assert!(seed
        .canonical_instances()
        .values()
        .any(|instance| *instance == Sym::from("identityInt")));

    let importer = r"fn use_tick() : Int ! {Tick} = tick(())
fn use_identity(x : Int) : Int = identity(x)
fn use_generic(x : Int) : Int = generic(x)
";
    let checked = check_with_seed(importer, &seed).unwrap();
    assert!(checked
        .defs
        .decls
        .iter()
        .any(|decl| decl.name == "use_tick"));
    assert!(checked
        .defs
        .decls
        .iter()
        .any(|decl| decl.name == "use_identity"));
    assert!(checked
        .defs
        .decls
        .iter()
        .any(|decl| decl.name == "use_generic"));
}

// A `pub import` re-export must survive into the module's checked interface:
// the project build checks each consumer against dependency interfaces alone,
// so an interface that omits re-exported entries strands every consumer of
// the re-export with an unbound canonical name at build while `check` and
// `run`, which flatten the whole program, resolve it fine. The forwarded
// entries carry the canonical names the source module's interface proved.
#[test]
fn reexports_survive_module_interfaces() {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    let sub = "pub type Shade = Bright | Dim deriving (Eq, Show)\n";
    let module = "import Sub (..)\n\npub import Sub (..)\n\npub fn shade_word(s : Shade) : String = show(s)\n";
    let modules: BTreeMap<String, String> = [("Sub".to_string(), sub.to_string())].into();
    let roots = vec![
        Root::SourceBundle {
            label: "reexport-interface".into(),
            identity: None,
            modules: Arc::new(modules),
        },
        Root::Embedded(prism::stdlib::STDLIB),
    ];
    let interface = module_interface(module, &with_prelude(module), &roots).unwrap();
    let seed = interface.rehydrate().unwrap().typecheck_seed();
    assert!(
        seed.data_types().contains_key("Sub.Shade"),
        "the re-exported type must rehydrate from the interface"
    );
    assert!(
        seed.constructors().contains_key("Sub.Bright")
            && seed.constructors().contains_key("Sub.Dim"),
        "the re-exported constructors must rehydrate from the interface"
    );
}
