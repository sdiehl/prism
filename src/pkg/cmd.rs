//! The `prism add` and `prism why` command bodies.
//!
//! Both operate on the project at (or above) the current directory and the
//! content-addressed store at the configured root. `add` edits `prism.toml` and
//! `prism.lock` in place; `why` reads the lock and reports which dependency edge
//! pulled a hash into the build's Merkle closure. Neither is on the compile path,
//! so a failure here never corrupts a build.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use crate::core::HASH_PREFIX_HEX;
use crate::driver::Config;
use crate::error::Error;
use crate::project::{self, DepSource};
use crate::store::disk::{resolve_store_path, Store};

use super::lock::{Lock, LockEntry};
use super::resolve::{resolve_closure, trace};
use super::transport::DiskTransport;
use super::writer::{render_source, set_dependency};

const MANIFEST: &str = "prism.toml";
const LOCKFILE: &str = "prism.lock";

/// `prism pkg init`: create a minimal package directory from scratch.
///
/// # Errors
/// Fails when the package name or directory is empty, the package name is not a
/// simple manifest name, the target directory already exists, or a filesystem
/// write fails.
pub fn init(name: &str, dir: &Path) -> Result<String, Error> {
    let name = name.trim();
    if name.is_empty() {
        return Err(Error::ResolvePackage("package name cannot be empty".into()));
    }
    if !is_package_name(name) {
        return Err(Error::ResolvePackage(format!(
            "package name `{name}` must contain only ASCII letters, digits, `_`, or `-`"
        )));
    }
    if dir.as_os_str().is_empty() {
        return Err(Error::ResolvePackage(
            "directory name cannot be empty".into(),
        ));
    }
    if dir.exists() {
        return Err(Error::ResolvePackage(format!(
            "`{}` already exists; `prism pkg init` creates a new package directory",
            dir.display()
        )));
    }

    fs::create_dir_all(dir.join("src"))?;
    fs::write(
        dir.join(MANIFEST),
        format!("[package]\nname = \"{name}\"\n\n[bin]\nentry = \"src/main.pr\"\n"),
    )?;
    fs::write(
        dir.join("src").join("main.pr"),
        "fn main() = println(\"Hello World from Prism! Taste the rainbow.\")\n",
    )?;

    Ok(format!("created package `{name}` at {}", dir.display()))
}

/// `prism add <git-url-or-hash>`: record a dependency in `prism.toml`, and pin its
/// resolved root hash in `prism.lock` when it can be resolved locally.
///
/// The argument is a bare content-hash pin (`<scheme>:<hex>` or a bare hex digest)
/// or a git reference `<url>@<tag>`. A hash pin resolves to itself and is always
/// locked; a git reference names an opaque release tag whose mapping to a root
/// hash needs the signed index and transport, so it is written to the manifest and
/// left for `prism build` to resolve once those land.
///
/// # Errors
/// Fails when no project is found, the argument is neither a pin nor a git
/// reference, or a filesystem error occurs.
pub fn add(arg: &str, cfg: &Config) -> Result<String, Error> {
    let root = project_root(Path::new("."))?;
    let (name, source) = parse_add_arg(arg)?;

    let manifest_path = root.join(MANIFEST);
    let text = fs::read_to_string(&manifest_path)?;
    let edited = set_dependency(&text, &name, &render_source(&source));
    fs::write(&manifest_path, &edited)?;

    let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
    let mut report = format!("added dependency `{name}` to {MANIFEST}");

    if let Some(pin) = lockable_pin(&name, &source, cfg)? {
        let mut lock = load_lock(&root)?;
        lock.set(LockEntry {
            name: name.clone(),
            scheme: pin.scheme.clone(),
            hash: pin.hash.clone(),
            source,
        });
        write_lock(&root, &lock)?;
        let _ = write!(report, "\npinned `{name}` to {} in {LOCKFILE}", pin.hash);
        if !store.has(&pin.hash) {
            report.push_str("\n  (object not in the local store yet; `prism build` will fetch it)");
        }
    } else {
        report.push_str(
            "\n  (a git tag resolves to a root hash through the signed index; \
             `prism build` will pin it once transport lands)",
        );
    }
    Ok(report)
}

/// `prism why <name-or-hash>`: trace which dependency edge pulled a hash into the
/// build's closure.
///
/// The closure is the Merkle closure of the locked root hashes over the local
/// store. The target may be a dependency name (resolved through the lock) or a
/// content hash (a pin string or a bare hex); the output is the chain of hashes
/// from a pinned root down to it.
///
/// # Errors
/// Fails when no project is found, the lock is missing or malformed, the closure
/// cannot be walked over the local store, or the target is not in the closure.
pub fn why(target: &str, cfg: &Config) -> Result<String, Error> {
    let root = project_root(Path::new("."))?;
    let lock = load_lock(&root)?;
    lock.validate_current_scheme()?;
    if lock.entries.is_empty() {
        return Err(Error::ResolvePackage(format!(
            "{LOCKFILE} pins no dependencies; run `prism add` first"
        )));
    }
    // Local-store-only resolution: a disk transport over the configured store.
    // The git-backed transport is a drop-in here when a build must reach a
    // remote; the resolver does not change.
    let transport = DiskTransport::open(resolve_store_path(cfg.flags.store_path.as_deref()))?;
    let roots: Vec<String> = lock.entries.iter().map(|e| e.hash.clone()).collect();
    let closure =
        resolve_closure(&transport, &roots).map_err(|e| Error::ResolvePackage(e.to_string()))?;

    let store = transport.store();
    let hash = target_hash(target, &lock, store)?;
    let Some(chain) = trace(&closure, &roots, &hash) else {
        return Err(Error::ResolvePackage(format!(
            "{target} ({hash}) is not in the closure of the locked roots"
        )));
    };

    let mut out = format!("why {target} ({hash}):\n");
    for (depth, h) in chain.iter().enumerate() {
        let label = store_name(store, h).unwrap_or_else(|| short(h));
        let arrow = if depth == 0 { "root" } else { "->" };
        let _ = writeln!(out, "  {arrow} {label} ({h})");
    }
    Ok(out)
}

// The nearest enclosing project root, or an error if the caller is not inside a
// project.
fn project_root(start: &Path) -> Result<PathBuf, Error> {
    let start = start.canonicalize().unwrap_or_else(|_| start.to_path_buf());
    project::find_manifest(&start)
        .and_then(|m| m.parent().map(Path::to_path_buf))
        .ok_or_else(|| {
            Error::ResolvePackage(format!(
                "no {MANIFEST} found: `prism add`/`prism why` operate inside a project"
            ))
        })
}

// Classify an `add` argument into a dependency name and source. A hash pin (with
// or without the scheme prefix) becomes a `Hash` dep named by a short prefix; a
// `<url>@<tag>` becomes a `Git` dep named by the url's last path component.
fn parse_add_arg(arg: &str) -> Result<(String, DepSource), Error> {
    if let Some(hex) = hex_pin(arg) {
        return Ok((short(hex), DepSource::Hash(hex.to_string())));
    }
    if let Some((url, version)) = arg.rsplit_once('@') {
        if url.is_empty() || version.is_empty() {
            return Err(Error::ResolvePackage(format!(
                "`{arg}` is not a valid git reference; expected `<url>@<tag>`"
            )));
        }
        return Ok((
            git_name(url),
            DepSource::Git {
                url: url.to_string(),
                version: version.to_string(),
            },
        ));
    }
    Err(Error::ResolvePackage(format!(
        "`{arg}` is neither a content-hash pin (`{scheme}:<hex>` or a bare hex digest) nor a git \
         reference (`<url>@<tag>`)",
        scheme = crate::core::HASH_SCHEME
    )))
}

// The hex digest of an `add` argument that is a hash pin: the scheme-prefixed pin
// form, or a bare hex digest at least a prefix wide (so a short git host is not
// mistaken for a hash).
fn hex_pin(arg: &str) -> Option<&str> {
    if let Some(hex) = project::parse_hash_pin(arg) {
        return Some(hex);
    }
    let hexlike = arg.len() >= HASH_PREFIX_HEX && arg.bytes().all(|b| b.is_ascii_hexdigit());
    hexlike.then_some(arg)
}

// The dependency name derived from a git url: its last path component, with a
// trailing `.git` removed. `github.com/prism-lang/http` -> `http`.
fn git_name(url: &str) -> String {
    url.trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or(url)
        .trim_end_matches(".git")
        .to_string()
}

struct ResolvedPin {
    scheme: String,
    hash: String,
}

// The root hash a source locks to: a hash pin is its own root hash; a git tag
// resolves through the signed index when the local store has one. The scheme is
// carried with the hash so lock creation never reconstructs identity from a bare
// digest after verification.
fn lockable_pin(
    name: &str,
    source: &DepSource,
    cfg: &Config,
) -> Result<Option<ResolvedPin>, Error> {
    match source {
        DepSource::Hash(hex) => Ok(Some(ResolvedPin {
            scheme: crate::core::HASH_SCHEME.to_string(),
            hash: hex.clone(),
        })),
        DepSource::Path(_) => Ok(None),
        DepSource::Git { url, version } => {
            let store_root = resolve_store_path(cfg.flags.store_path.as_deref());
            let pointer =
                crate::pkg::signed_index_pointer(url, name, version, &store_root, &cfg.flags)?;
            Ok(Some(ResolvedPin {
                scheme: pointer.scheme,
                hash: pointer.root,
            }))
        }
    }
}

// Resolve a `why` target to a content hash: a pin string or bare hex is taken
// verbatim; otherwise it is a dependency name looked up in the lock, then the
// store's name index.
fn target_hash(target: &str, lock: &Lock, store: &Store) -> Result<String, Error> {
    if let Some(hex) = hex_pin(target) {
        return Ok(hex.to_string());
    }
    if let Some(entry) = lock.get(target) {
        return Ok(entry.hash.clone());
    }
    if let Some(hash) = store.lookup_name(target)? {
        return Ok(hash);
    }
    Err(Error::ResolvePackage(format!(
        "no dependency or definition named `{target}` in {LOCKFILE} or the store"
    )))
}

// A stored object's human name from the metadata layer, if any.
fn store_name(store: &Store, hash: &str) -> Option<String> {
    store.get_meta(hash).ok().flatten().map(|m| m.name)
}

// A short, human-facing hash prefix for labels, the same width the dumps use.
fn short(hash: &str) -> String {
    hash.chars().take(HASH_PREFIX_HEX).collect()
}

fn is_package_name(name: &str) -> bool {
    name.bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
}

fn load_lock(root: &Path) -> Result<Lock, Error> {
    match fs::read_to_string(root.join(LOCKFILE)) {
        Ok(text) => {
            let lock = Lock::parse(&text)?;
            lock.validate_current_scheme()?;
            Ok(lock)
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Lock::default()),
        Err(e) => Err(Error::Io(e)),
    }
}

fn write_lock(root: &Path, lock: &Lock) -> Result<(), Error> {
    fs::write(root.join(LOCKFILE), lock.render()?)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_scheme_pin_argument() {
        let (name, source) = parse_add_arg(&project::hash_pin("9f86d0818800")).unwrap();
        assert_eq!(source, DepSource::Hash("9f86d0818800".to_string()));
        assert_eq!(name, "9f86d0818800");
    }

    #[test]
    fn parses_a_bare_hex_argument() {
        let hex = "abcdef0123456789ab";
        let (_, source) = parse_add_arg(hex).unwrap();
        assert_eq!(source, DepSource::Hash(hex.to_string()));
    }

    #[test]
    fn parses_a_git_reference_and_names_it_by_repo() {
        let (name, source) = parse_add_arg("github.com/prism-lang/http@2.0").unwrap();
        assert_eq!(name, "http");
        assert_eq!(
            source,
            DepSource::Git {
                url: "github.com/prism-lang/http".to_string(),
                version: "2.0".to_string(),
            }
        );
    }

    #[test]
    fn rejects_a_bare_url_with_no_tag() {
        assert!(parse_add_arg("github.com/prism-lang/http").is_err());
    }

    #[test]
    fn git_name_strips_dot_git_suffix() {
        assert_eq!(git_name("github.com/x/http.git"), "http");
    }
}
