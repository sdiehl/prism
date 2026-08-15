//! Two effects claiming one operation name fail identically on every entry path.
//!
//! Operations dispatch by name within a module, so a second effect declaring an
//! operation the module already has would silently shadow the first. The surface
//! pass that rejects it runs before typechecking on all three paths (whole-program
//! check, the modular checker a project build uses, and the CLI over a project on
//! disk), so a program the interpreter refuses is refused by a build too.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use prism::{check_modules_on, check_validated_on_in, default_roots, with_prelude, Config, Root};

// The code the collision carries wherever it is found.
const DUPLICATE_OP: &str = "E6007";

// Two effects, one operation name, in a single source.
const COLLIDING: &str = "effect Ping\n  beep(Int) : Unit\n\n\
                         effect Pong\n  beep(Int) : Unit\n\n\
                         fn main() = println(1)\n";

// A library module carrying the same collision, imported by a root that never
// mentions the operation: the modular checker sees the module on its own.
const MODULE_ROOT: &str = "import Beeper\nfn main() = println(1)\n";

fn module_roots() -> Vec<Root> {
    vec![Root::source_bundle(
        "modules".to_string(),
        BTreeMap::from([(
            "Beeper".to_string(),
            "pub effect Ping\n  beep(Int) : Unit\n\n\
             pub effect Pong\n  beep(Int) : Unit\n"
                .to_string(),
        )]),
    )]
}

fn dup_effect_op_project() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("projects")
        .join("dup_effect_op")
}

#[test]
fn whole_program_check_rejects_the_collision() {
    let err = check_validated_on_in(
        &with_prelude(COLLIDING),
        &default_roots(Path::new(".")),
        &Config::default(),
    )
    .expect_err("two effects claiming one operation name is refused");
    assert_eq!(err.code().to_string(), DUPLICATE_OP);
}

#[test]
fn the_modular_checker_rejects_the_same_collision() {
    let err = check_modules_on(MODULE_ROOT, &module_roots(), &Config::default())
        .expect_err("a module's own collision is refused by the modular checker");
    assert_eq!(err.code().to_string(), DUPLICATE_OP);
}

#[test]
fn the_diagnostic_names_both_effects() {
    let err = check_validated_on_in(
        &with_prelude(COLLIDING),
        &default_roots(Path::new(".")),
        &Config::default(),
    )
    .expect_err("two effects claiming one operation name is refused");
    let msg = err.to_string();
    assert!(
        msg.contains("`beep`") && msg.contains("Ping") && msg.contains("Pong"),
        "the message must name the operation and both owning effects, got {msg}"
    );
}

#[test]
fn checking_the_project_on_disk_reports_the_same_code() {
    let output = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("check")
        .arg(dup_effect_op_project())
        .output()
        .expect("runs prism check");
    assert!(!output.status.success(), "the project must fail to check");
    let rendered = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        rendered.contains(DUPLICATE_OP),
        "expected {DUPLICATE_OP} from the project path, got {rendered}"
    );
}
