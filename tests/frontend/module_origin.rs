//! An error raised inside an imported module names that module and carries its
//! source, so its spans are read against the right text on every check path.

use std::collections::BTreeMap;
use std::path::Path;

use prism::{
    check_modules_on, check_validated_on_in, default_roots, with_prelude, Config, Error, Root,
};

const ROOT: &str = "import Util\n\nfn main() : Unit = println(show_int(Util.twice(2)))\n";

fn roots(util: &str) -> Vec<Root> {
    let mut roots = vec![Root::source_bundle(
        "modules".to_string(),
        BTreeMap::from([("Util".to_string(), util.to_string())]),
    )];
    roots.extend(default_roots(Path::new(".")));
    roots
}

// The error's module, and the text its primary span covers in that module.
fn located(err: &Error) -> (String, String) {
    let origin = err.origin().expect("the error names its module");
    let source = origin
        .source
        .as_deref()
        .expect("the driver attached the module text");
    let span = err.primary_span().expect("the error has a span");
    (origin.module.clone(), source[span].to_string())
}

#[test]
fn a_type_error_in_a_module_points_into_that_module() {
    let util = "pub fn twice(x : Int) : Int = x + \"a\"\n";
    let whole = check_validated_on_in(&with_prelude(ROOT), &roots(util), &Config::default())
        .expect_err("the module does not check");
    assert_eq!(located(&whole), ("Util".to_string(), "\"a\"".to_string()));
    let modular = check_modules_on(&with_prelude(ROOT), &roots(util), &Config::default())
        .expect_err("the module does not check");
    assert_eq!(located(&modular), ("Util".to_string(), "\"a\"".to_string()));
}

#[test]
fn a_scope_error_in_a_module_points_into_that_module() {
    let util = "pub fn twice(x : Int) : Int = x + Nope.y\n";
    let err = check_validated_on_in(&with_prelude(ROOT), &roots(util), &Config::default())
        .expect_err("the module does not resolve");
    assert_eq!(located(&err).0, "Util");
}

#[test]
fn a_root_error_names_no_module() {
    let err = check_validated_on_in(
        &with_prelude("fn main() : Int = \"a\"\n"),
        &default_roots(Path::new(".")),
        &Config::default(),
    )
    .expect_err("the root does not check");
    assert!(err.origin().is_none());
}
