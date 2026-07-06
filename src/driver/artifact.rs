use std::env;
use std::fmt::Write as _;
#[cfg(not(target_arch = "wasm32"))]
use std::process::Command;

use crate::core::{CorePass, OptLevel, PassSpec, HASH_SCHEME};

use super::Config;

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)]
pub struct ArtifactIdentity {
    pub compiler_version: &'static str,
    pub hash_scheme: &'static str,
    pub target: &'static str,
    pub backend: String,
    pub source_root: Option<String>,
    pub stdlib_root: Option<String>,
    pub package_roots: Vec<String>,
    pub opt: &'static str,
    pub passes: String,
    pub disabled: String,
    pub backend_opt: String,
    pub scheduler: &'static str,
    pub effect_tier: &'static str,
    pub native_effects: bool,
    pub trampoline: bool,
    pub cek_spike: bool,
    pub fuse: bool,
    pub rt_checks: bool,
    pub native_kont_frames: bool,
    pub native_toolchain: Option<NativeToolchainIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeToolchainIdentity {
    pub cc: String,
    pub cc_version: String,
    pub cc_flags: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArtifactRows {
    Full,
    Portable,
}

impl ArtifactIdentity {
    #[must_use]
    pub fn from_config(cfg: &Config, backend: impl Into<String>) -> Self {
        let backend = backend.into();
        let native_toolchain = native_toolchain_identity(&backend);
        Self {
            compiler_version: env!("CARGO_PKG_VERSION"),
            hash_scheme: HASH_SCHEME,
            target: env!("PRISM_TARGET"),
            backend,
            source_root: None,
            stdlib_root: None,
            package_roots: Vec::new(),
            opt: opt_label(cfg.opt),
            passes: pass_spec_label(cfg.passes.as_ref()),
            disabled: disabled_label(&cfg.disabled),
            backend_opt: cfg.backend_opt.clone(),
            scheduler: cfg.scheduler.label(),
            effect_tier: cfg.flags.effect_tier.label(),
            native_effects: cfg.flags.native_effects,
            trampoline: cfg.flags.trampoline,
            cek_spike: cfg.flags.cek_spike,
            fuse: cfg.flags.fuse,
            rt_checks: cfg.flags.rt_checks,
            native_kont_frames: cfg.flags.native_kont_frames,
            native_toolchain,
        }
    }

    #[must_use]
    pub fn with_source_root(mut self, root: impl Into<String>) -> Self {
        self.source_root = Some(root.into());
        self
    }

    #[must_use]
    pub fn with_stdlib_root(mut self, root: impl Into<String>) -> Self {
        self.stdlib_root = Some(root.into());
        self
    }

    #[must_use]
    pub fn with_package_roots(mut self, roots: impl IntoIterator<Item = String>) -> Self {
        self.package_roots.extend(roots);
        self.package_roots.sort();
        self.package_roots.dedup();
        self
    }

    #[must_use]
    pub fn fingerprint(&self) -> String {
        let mut out = String::new();
        for (key, value) in self.rows() {
            write!(out, "{key}={value};").unwrap();
        }
        out
    }

    #[must_use]
    pub fn rows(&self) -> Vec<(&'static str, String)> {
        self.rows_for(ArtifactRows::Full)
    }

    #[must_use]
    pub fn portable_rows(&self) -> Vec<(&'static str, String)> {
        self.rows_for(ArtifactRows::Portable)
    }

    fn rows_for(&self, mode: ArtifactRows) -> Vec<(&'static str, String)> {
        let mut rows = vec![
            ("compiler", self.compiler_version.to_string()),
            ("hash-scheme", self.hash_scheme.to_string()),
            ("target", self.target.to_string()),
            ("backend", self.backend.clone()),
        ];
        if let Some(root) = &self.source_root {
            rows.push(("source-root", scheme_root(self.hash_scheme, root)));
        }
        if let Some(root) = &self.stdlib_root {
            rows.push(("stdlib-root", scheme_root(self.hash_scheme, root)));
        }
        rows.extend(
            self.package_roots
                .iter()
                .map(|root| ("package-root", root.clone())),
        );
        rows.extend([
            ("opt", self.opt.to_string()),
            ("passes", self.passes.clone()),
            ("disabled", self.disabled.clone()),
            ("backend-opt", self.backend_opt.clone()),
            ("scheduler", self.scheduler.to_string()),
            ("effect-tier", self.effect_tier.to_string()),
            ("native-effects", self.native_effects.to_string()),
            ("trampoline", self.trampoline.to_string()),
            ("cek-spike", self.cek_spike.to_string()),
            ("fuse", self.fuse.to_string()),
            ("rt-checks", self.rt_checks.to_string()),
            ("native-kont-frames", self.native_kont_frames.to_string()),
        ]);
        if let (ArtifactRows::Full, Some(toolchain)) = (mode, &self.native_toolchain) {
            rows.extend([
                ("native-cc", toolchain.cc.clone()),
                ("native-cc-version", toolchain.cc_version.clone()),
                ("native-cc-flags", toolchain.cc_flags.clone()),
            ]);
        }
        rows
    }
}

fn native_toolchain_identity(backend: &str) -> Option<NativeToolchainIdentity> {
    matches!(backend, "llvm" | "mlir").then(native_toolchain_for_backend)
}

#[cfg(not(target_arch = "wasm32"))]
fn native_toolchain_for_backend() -> NativeToolchainIdentity {
    let cc = env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").to_string());
    let cc_flags = env::var("PRISM_CC_FLAGS").unwrap_or_default();
    let cc_version = native_cc_version(&cc);
    NativeToolchainIdentity {
        cc,
        cc_version,
        cc_flags,
    }
}

#[cfg(target_arch = "wasm32")]
fn native_toolchain_for_backend() -> NativeToolchainIdentity {
    NativeToolchainIdentity {
        cc: String::new(),
        cc_version: String::new(),
        cc_flags: String::new(),
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn native_cc_version(cc: &str) -> String {
    Command::new(cc)
        .arg("--version")
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .and_then(|version| version.lines().next().map(str::trim).map(str::to_string))
        .filter(|version| !version.is_empty())
        .unwrap_or_else(|| {
            if env::var("PRISM_CC").is_ok() {
                "unavailable".to_string()
            } else {
                env!("PRISM_BUILD_CC_VERSION").to_string()
            }
        })
}

fn scheme_root(scheme: &str, root: &str) -> String {
    format!("{scheme}:{root}")
}

const fn opt_label(opt: OptLevel) -> &'static str {
    match opt {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
    }
}

fn pass_spec_label(spec: Option<&PassSpec>) -> String {
    spec.map_or_else(
        || "level-default".to_string(),
        |spec| {
            format!(
                "pre:{};late:{}",
                pass_list_label(&spec.pre),
                pass_list_label(&spec.late)
            )
        },
    )
}

fn disabled_label(disabled: &[CorePass]) -> String {
    if disabled.is_empty() {
        return "none".to_string();
    }
    let mut names: Vec<&str> = disabled.iter().map(|pass| pass.name()).collect();
    names.sort_unstable();
    names.join(",")
}

fn pass_list_label(passes: &[CorePass]) -> String {
    if passes.is_empty() {
        return "none".to_string();
    }
    passes
        .iter()
        .map(|pass| pass.name())
        .collect::<Vec<_>>()
        .join(",")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row_keys(identity: &ArtifactIdentity) -> Vec<&'static str> {
        identity.rows().into_iter().map(|(key, _)| key).collect()
    }

    #[test]
    fn native_backend_identity_names_linker_inputs() {
        let identity = ArtifactIdentity::from_config(&Config::default(), "llvm");
        let rows = row_keys(&identity);
        assert!(rows.contains(&"native-cc"));
        assert!(rows.contains(&"native-cc-version"));
        assert!(rows.contains(&"native-cc-flags"));
    }

    #[test]
    fn non_native_identity_omits_linker_inputs() {
        let identity = ArtifactIdentity::from_config(&Config::default(), "interpreter");
        let rows = row_keys(&identity);
        assert!(!rows.contains(&"native-cc"));
        assert!(!rows.contains(&"native-cc-version"));
        assert!(!rows.contains(&"native-cc-flags"));
    }

    #[test]
    fn portable_rows_omit_host_toolchain_strings() {
        let identity = ArtifactIdentity::from_config(&Config::default(), "llvm");
        let rows: Vec<&'static str> = identity
            .portable_rows()
            .into_iter()
            .map(|(key, _)| key)
            .collect();
        assert!(!rows.contains(&"native-cc"));
        assert!(!rows.contains(&"native-cc-version"));
        assert!(!rows.contains(&"native-cc-flags"));
    }
}
