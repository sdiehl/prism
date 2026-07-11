//! A source file named after the module it imports must never resolve that
//! import back to itself (a same-named-file self-import; on a case-insensitive
//! filesystem `import Quickcheck` from `quickcheck.pr` lands on the importer).
//! An embedded/stdlib module of that name wins; a genuine self-import with no
//! fallback names the collision instead of cascading into unknown-name errors.

use std::fs;
use std::path::PathBuf;

use prism::{check_on, default_roots, with_prelude};

// A throwaway directory under the system temp root, removed on drop.
struct TempDir(PathBuf);

impl TempDir {
    fn new(tag: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("prism_selfimp_{tag}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        Self(dir)
    }
    fn write(&self, name: &str, src: &str) {
        fs::write(self.0.join(name), src).expect("write fixture");
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check_err(dir: &TempDir, src: &str) -> String {
    check_on(&with_prelude(src), &default_roots(&dir.0))
        .expect_err("import should not resolve to the importing file")
        .to_string()
}

#[test]
fn self_named_file_falls_through_to_the_stdlib_module() {
    // A local `Quickcheck.pr` that imports `Quickcheck` shadows the stdlib one
    // with its own text. It must be skipped so the real module wins: importing a
    // name only this shadow defines fails as "does not export", proving the
    // stdlib `Quickcheck` (which lacks it) is what got loaded.
    let dir = TempDir::new("stdlib_wins");
    dir.write(
        "Quickcheck.pr",
        "import Quickcheck\npub fn fixture_only() : Int = 1\n",
    );
    let e = check_err(
        &dir,
        "import Quickcheck (fixture_only)\nfn main() = print(0)",
    );
    assert!(e.contains("does not export `fixture_only`"), "{e}");
}

#[test]
fn genuine_self_import_names_the_collision() {
    // No stdlib `Widget` to fall through to: the loader reports the self-import
    // directly rather than loading the self-copy and emitting a cascade of
    // unknown-type / unbound-value errors pointing at <prelude>.
    let dir = TempDir::new("genuine");
    dir.write("Widget.pr", "import Widget\nfn helper() : Int = 0\n");
    let e = check_err(&dir, "import Widget\nfn main() = print(0)");
    assert!(e.contains("imports itself"), "{e}");
    assert!(e.contains("Widget"), "{e}");
}
