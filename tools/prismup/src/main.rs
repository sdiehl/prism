// prismup: install and manage released versions of the Prism compiler.
//
// A fork of Michel Boucey's prismup (BSD-3-Clause), rewritten against a
// minimal dependency set: blocking HTTP over rustls, no async runtime, and a
// plain-text version manifest instead of the GitHub API. Layout:
// ~/.prismup/prism/<version>/ holds each installed toolchain,
// ~/.prismup/bin/prism is a symlink naming the current version, and
// ~/.cache/prismup/ holds the manifest cache and in-flight downloads.

use std::env;
use std::fmt;
use std::fmt::Write as _;
use std::fs;
use std::io::{self, IsTerminal, Read};
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::thread;
use std::time::{Duration, SystemTime};

use flate2::read::GzDecoder;
use sha2::{Digest, Sha256};
use tar::Archive;

/// Released versions, one per line, ascending; published by the release
/// pipeline next to the shell installer.
const MANIFEST_URL: &str = "https://sdiehl.github.io/prism/versions.txt";
const DOWNLOAD_BASE: &str = "https://github.com/sdiehl/prism/releases/download";
const MANIFEST_TTL: Duration = Duration::from_secs(3600);
const DOWNLOAD_ATTEMPTS: u32 = 4;
const BACKOFF_BASE_MS: u64 = 500;
const SHA256_HEX_LEN: usize = 64;
const HASH_CHUNK: usize = 64 * 1024;

/// Hosts with prebuilt Prism release tarballs, as (std OS, std ARCH, target).
const TARGETS: &[(&str, &str, &str)] = &[
    ("linux", "x86_64", "x86_64-unknown-linux-gnu"),
    ("linux", "aarch64", "aarch64-unknown-linux-gnu"),
    ("macos", "aarch64", "aarch64-apple-darwin"),
];
const ALPINE_RELEASE: &str = "/etc/alpine-release";
const MUSL_LOADER_PREFIX: &str = "ld-musl-";
const LIB_DIR: &str = "/lib";

const BOLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const GREEN: &str = "\x1b[32m";
const RESET: &str = "\x1b[0m";

const HELP: &str = "\
A CLI tool to install and manage versions of the Prism language.

Usage: prismup [OPTIONS]

Options:
  -v, --version                   Print PrismUp version
  -c, --current-version           Print the current Prism version
  -u, --upgrade                   Install and set the latest Prism version
  -l, --versions-list             Show list of available Prism versions
  -i, --install-version <SEMVER>  Install Prism in the given version
  -s, --set-version <SEMVER>      Set the current Prism to the given version
  -r, --remove-version <SEMVER>   Remove the given Prism version
  -h, --help                      Print help";

type Res<T> = Result<T, String>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Version {
    major: u64,
    minor: u64,
    patch: u64,
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl Version {
    /// The first X.Y.Z run of digits anywhere in the string, so "v0.17.0",
    /// "0.17.0", and a symlink target ending in ".../0.17.0/prism" all parse.
    fn parse(s: &str) -> Res<Self> {
        let bytes = s.as_bytes();
        for i in 0..bytes.len() {
            if bytes[i].is_ascii_digit() && (i == 0 || !bytes[i - 1].is_ascii_digit()) {
                if let Some(v) = Self::parse_at(&s[i..]) {
                    return Ok(v);
                }
            }
        }
        Err(format!("no X.Y.Z version found in '{s}'"))
    }

    fn parse_at(s: &str) -> Option<Self> {
        let mut parts = [0u64; 3];
        let mut rest = s;
        for (k, slot) in parts.iter_mut().enumerate() {
            let end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            *slot = rest[..end].parse().ok()?;
            rest = &rest[end..];
            if k < 2 {
                rest = rest.strip_prefix('.')?;
            }
        }
        Some(Self {
            major: parts[0],
            minor: parts[1],
            patch: parts[2],
        })
    }
}

struct Dirs {
    root: PathBuf,
    cache: PathBuf,
}

impl Dirs {
    fn discover() -> Res<Self> {
        let home = env::var("HOME").map_err(|_| "HOME is not set".to_string())?;
        let home = PathBuf::from(home);
        Ok(Self {
            root: home.join(".prismup"),
            cache: home.join(".cache").join("prismup"),
        })
    }

    fn ensure(&self) -> Res<()> {
        for dir in [&self.bin(), &self.versions(), &self.cache] {
            fs::create_dir_all(dir).map_err(|e| format!("creating {}: {e}", dir.display()))?;
        }
        Ok(())
    }

    fn bin(&self) -> PathBuf {
        self.root.join("bin")
    }

    fn versions(&self) -> PathBuf {
        self.root.join("prism")
    }

    fn version_dir(&self, v: Version) -> PathBuf {
        self.versions().join(v.to_string())
    }

    fn version_link(&self, v: Version) -> PathBuf {
        self.bin().join(format!("prism-{v}"))
    }

    fn current_link(&self) -> PathBuf {
        self.bin().join("prism")
    }
}

fn style(code: &str, s: &str) -> String {
    if io::stdout().is_terminal() {
        format!("{code}{s}{RESET}")
    } else {
        s.to_string()
    }
}

fn fetch_text(url: &str) -> Res<String> {
    let mut res = ureq::get(url)
        .call()
        .map_err(|e| format!("GET {url}: {e}"))?;
    res.body_mut()
        .read_to_string()
        .map_err(|e| format!("reading {url}: {e}"))
}

fn fetch_file(url: &str, out: &Path) -> Res<()> {
    let mut res = ureq::get(url)
        .call()
        .map_err(|e| format!("GET {url}: {e}"))?;
    let mut file = fs::File::create(out).map_err(|e| format!("creating {}: {e}", out.display()))?;
    io::copy(&mut res.body_mut().as_reader(), &mut file)
        .map_err(|e| format!("writing {}: {e}", out.display()))?;
    Ok(())
}

fn fetch_file_backoff(url: &str, out: &Path) -> Res<()> {
    let mut last = String::new();
    for attempt in 0..DOWNLOAD_ATTEMPTS {
        if attempt > 0 {
            thread::sleep(Duration::from_millis(BACKOFF_BASE_MS << attempt));
        }
        match fetch_file(url, out) {
            Ok(()) => return Ok(()),
            Err(e) => last = e,
        }
    }
    Err(last)
}

/// The manifest of released versions, ascending: served from the pages site,
/// cached for an hour, and falling back to a stale cache when offline.
fn released_versions(dirs: &Dirs) -> Res<Vec<Version>> {
    let cache = dirs.cache.join("versions.txt");
    let fresh = fs::metadata(&cache)
        .and_then(|m| m.modified())
        .ok()
        .and_then(|t| SystemTime::now().duration_since(t).ok())
        .is_some_and(|age| age < MANIFEST_TTL);
    if !fresh {
        match fetch_text(MANIFEST_URL) {
            Ok(text) => {
                fs::write(&cache, &text).map_err(|e| format!("caching manifest: {e}"))?;
            }
            Err(e) if !cache.exists() => return Err(e),
            Err(_) => {}
        }
    }
    let text = fs::read_to_string(&cache).map_err(|e| format!("reading manifest cache: {e}"))?;
    let mut versions = Vec::new();
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty()) {
        versions.push(Version::parse(line)?);
    }
    versions.sort();
    Ok(versions)
}

fn installed_versions(dirs: &Dirs) -> Vec<Version> {
    let mut versions: Vec<Version> = fs::read_dir(dirs.versions())
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|e| Version::parse(&e.file_name().to_string_lossy()).ok())
        .collect();
    versions.sort();
    versions
}

fn current_version(dirs: &Dirs) -> Option<Version> {
    let target = fs::read_link(dirs.current_link()).ok()?;
    Version::parse(target.to_str()?).ok()
}

fn musl_host() -> bool {
    Path::new(ALPINE_RELEASE).exists()
        || fs::read_dir(LIB_DIR).is_ok_and(|entries| {
            entries.flatten().any(|e| {
                e.file_name()
                    .to_string_lossy()
                    .starts_with(MUSL_LOADER_PREFIX)
            })
        })
}

fn host_target() -> Res<&'static str> {
    if env::consts::OS == "linux" && musl_host() {
        return Err(
            "musl libc detected; the prebuilt Prism binary is glibc-linked and will not run. \
             Use the container image: docker run ghcr.io/sdiehl/prism"
                .to_string(),
        );
    }
    TARGETS
        .iter()
        .find(|(os, arch, _)| *os == env::consts::OS && *arch == env::consts::ARCH)
        .map(|(_, _, target)| *target)
        .ok_or_else(|| {
            format!(
                "no prebuilt Prism for {} on {}; see https://github.com/sdiehl/prism#install",
                env::consts::OS,
                env::consts::ARCH
            )
        })
}

fn sha256_hex(path: &Path) -> Res<String> {
    let mut file = fs::File::open(path).map_err(|e| format!("opening {}: {e}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buf = [0u8; HASH_CHUNK];
    loop {
        let n = file
            .read(&mut buf)
            .map_err(|e| format!("hashing {}: {e}", path.display()))?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let mut hex = String::with_capacity(SHA256_HEX_LEN);
    for byte in hasher.finalize() {
        let _ = write!(hex, "{byte:02x}");
    }
    Ok(hex)
}

fn replace_symlink(target: &Path, link: &Path) -> Res<()> {
    if fs::symlink_metadata(link).is_ok() {
        fs::remove_file(link).map_err(|e| format!("removing {}: {e}", link.display()))?;
    }
    symlink(target, link)
        .map_err(|e| format!("linking {} -> {}: {e}", link.display(), target.display()))
}

fn install(dirs: &Dirs, version: Version) -> Res<()> {
    let target = host_target()?;
    let pkg = format!("prism-{version}-{target}");
    let url = format!("{DOWNLOAD_BASE}/v{version}/{pkg}.tar.gz");
    let tarball = dirs.cache.join(format!("{pkg}.tar.gz"));

    println!("Downloading {pkg}.tar.gz...");
    fetch_file_backoff(&url, &tarball)?;

    let sidecar = fetch_text(&format!("{url}.sha256"))?;
    let expected = sidecar
        .get(..SHA256_HEX_LEN)
        .ok_or_else(|| format!("invalid checksum file for {pkg}.tar.gz"))?;
    let actual = sha256_hex(&tarball)?;
    if actual != expected {
        let _ = fs::remove_file(&tarball);
        return Err(format!(
            "SHA256 mismatch for {pkg}.tar.gz\n  expected: {expected}\n  actual:   {actual}\n\
             The download is corrupt or has been tampered with. Nothing was installed."
        ));
    }

    let file = fs::File::open(&tarball).map_err(|e| format!("opening {pkg}.tar.gz: {e}"))?;
    Archive::new(GzDecoder::new(file))
        .unpack(dirs.versions())
        .map_err(|e| format!("unpacking {pkg}.tar.gz: {e}"))?;
    let _ = fs::remove_file(&tarball);

    let version_dir = dirs.version_dir(version);
    if version_dir.exists() {
        fs::remove_dir_all(&version_dir)
            .map_err(|e| format!("replacing {}: {e}", version_dir.display()))?;
    }
    fs::rename(dirs.versions().join(&pkg), &version_dir)
        .map_err(|e| format!("placing {}: {e}", version_dir.display()))?;

    replace_symlink(&version_dir.join("prism"), &dirs.version_link(version))?;
    println!("Prism {} installed.", style(BOLD, &version.to_string()));
    Ok(())
}

fn set_current(dirs: &Dirs, version: Version) -> Res<()> {
    if current_version(dirs) == Some(version) {
        println!(
            "Prism version {} is already set as your current Prism compiler.",
            style(BOLD, &version.to_string())
        );
        return Ok(());
    }
    let binary = dirs.version_dir(version).join("prism");
    if !binary.exists() {
        return Err(format!("Prism {version} is not installed"));
    }
    replace_symlink(&binary, &dirs.current_link())?;
    println!(
        "Set Prism version {} as your current Prism compiler.",
        style(BOLD, &version.to_string())
    );
    Ok(())
}

fn remove(dirs: &Dirs, version: Version) -> Res<()> {
    if current_version(dirs) == Some(version) {
        return Err(format!(
            "Prism version {version} is your current Prism compiler.\n\
             Please set another Prism version before removing this one."
        ));
    }
    if !installed_versions(dirs).contains(&version) {
        return Err(format!("{version} is not an installed version of Prism."));
    }
    let _ = fs::remove_file(dirs.version_link(version));
    fs::remove_dir_all(dirs.version_dir(version))
        .map_err(|e| format!("removing Prism {version}: {e}"))?;
    println!(
        "Prism version {} removed.",
        style(BOLD, &version.to_string())
    );
    Ok(())
}

fn install_and_set(dirs: &Dirs, version: Version) -> Res<()> {
    let released = released_versions(dirs)?;
    if !released.contains(&version) {
        return Err(format!("{version} is not a released Prism version."));
    }
    if installed_versions(dirs).contains(&version) {
        println!(
            "Prism {} already installed.",
            style(BOLD, &version.to_string())
        );
    } else {
        install(dirs, version)?;
    }
    Ok(())
}

fn upgrade(dirs: &Dirs) -> Res<()> {
    let released = released_versions(dirs)?;
    let latest = *released
        .last()
        .ok_or_else(|| "no Prism version released yet".to_string())?;
    if installed_versions(dirs).contains(&latest) {
        println!(
            "The latest Prism version {} is already installed.",
            style(BOLD, &latest.to_string())
        );
    } else {
        println!(
            "Installation of the latest Prism compiler ({}).",
            style(BOLD, &latest.to_string())
        );
        install(dirs, latest)?;
    }
    set_current(dirs, latest)
}

fn list(dirs: &Dirs) -> Res<()> {
    let released = released_versions(dirs)?;
    let installed = installed_versions(dirs);
    let current = current_version(dirs);
    for version in released.iter().rev() {
        if installed.contains(version) {
            let status = if current == Some(*version) {
                "(installed, current)"
            } else {
                "(installed)"
            };
            println!(
                "{} {} {}",
                style(BOLD, "Prism"),
                style(BOLD, &version.to_string()),
                style(GREEN, status)
            );
        } else {
            println!(
                "{} {}",
                style(DIM, "Prism"),
                style(DIM, &version.to_string())
            );
        }
    }
    Ok(())
}

enum Cmd {
    PrintVersion,
    Current,
    Upgrade,
    List,
    Install(String),
    Set(String),
    Remove(String),
    Default,
    Help,
}

fn parse_args() -> Res<Cmd> {
    let mut args = env::args().skip(1);
    let Some(flag) = args.next() else {
        return Ok(Cmd::Default);
    };
    let mut value = |name: &str| {
        args.next()
            .ok_or_else(|| format!("{name} requires a version argument"))
    };
    let cmd = match flag.as_str() {
        "-v" | "--version" => Cmd::PrintVersion,
        "-c" | "--current-version" => Cmd::Current,
        "-u" | "--upgrade" => Cmd::Upgrade,
        "-l" | "--versions-list" => Cmd::List,
        "-i" | "--install-version" => Cmd::Install(value(&flag)?),
        "-s" | "--set-version" => Cmd::Set(value(&flag)?),
        "-r" | "--remove-version" => Cmd::Remove(value(&flag)?),
        "-h" | "--help" => Cmd::Help,
        other => return Err(format!("unknown option '{other}'\n\n{HELP}")),
    };
    Ok(cmd)
}

fn run() -> Res<()> {
    let dirs = Dirs::discover()?;
    dirs.ensure()?;
    match parse_args()? {
        Cmd::PrintVersion => {
            println!(
                "PrismUp {} released under the 3-Clause BSD License",
                style(BOLD, env!("CARGO_PKG_VERSION"))
            );
            println!("Copyright (c) 2026 Michel Boucey (michel.boucey@gmail.com)");
            Ok(())
        }
        Cmd::Help => {
            println!("{HELP}");
            Ok(())
        }
        Cmd::Current => {
            match current_version(&dirs) {
                Some(version) => println!("Prism {}", style(BOLD, &version.to_string())),
                None => println!("No Prism version set"),
            }
            Ok(())
        }
        Cmd::List => list(&dirs),
        Cmd::Upgrade => upgrade(&dirs),
        Cmd::Install(s) => install_and_set(&dirs, Version::parse(&s)?),
        Cmd::Set(s) => {
            let version = Version::parse(&s)?;
            if !installed_versions(&dirs).contains(&version) {
                install_and_set(&dirs, version)?;
            }
            set_current(&dirs, version)
        }
        Cmd::Remove(s) => remove(&dirs, Version::parse(&s)?),
        Cmd::Default => {
            if installed_versions(&dirs).is_empty() {
                println!("No Prism compiler installed yet.");
                upgrade(&dirs)?;
                println!("Please add '$HOME/.prismup/bin/' to your PATH.");
            } else {
                match current_version(&dirs) {
                    Some(version) => println!("Prism {}", style(BOLD, &version.to_string())),
                    None => println!("No Prism version set"),
                }
                println!("Run 'prismup --help' for usage.");
            }
            Ok(())
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("prismup: {message}");
            ExitCode::FAILURE
        }
    }
}
