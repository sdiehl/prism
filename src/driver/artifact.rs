use std::fmt::Write as _;
#[cfg(feature = "native")]
use std::process::Command;

// The C-toolchain seam lives in `codegen::rt`, which is `native`-only, so the
// native-toolchain identity is gated on the same feature (not merely on a
// non-wasm target: a non-native host build has no native backend either).
#[cfg(feature = "native")]
use crate::codegen::rt::{cc, cc_flags, cc_overridden};
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
pub enum ArtifactField {
    Compiler,
    HashScheme,
    Target,
    Backend,
    SourceRoot,
    StdlibRoot,
    PackageRoot,
    Opt,
    Passes,
    Disabled,
    BackendOpt,
    Scheduler,
    EffectTier,
    NativeEffects,
    Trampoline,
    Fuse,
    RuntimeChecks,
    NativeKontFrames,
    NativeCc,
    NativeCcVersion,
    NativeCcFlags,
}

impl ArtifactField {
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Compiler => "compiler",
            Self::HashScheme => "hash-scheme",
            Self::Target => "target",
            Self::Backend => "backend",
            Self::SourceRoot => "source-root",
            Self::StdlibRoot => "stdlib-root",
            Self::PackageRoot => "package-root",
            Self::Opt => "opt",
            Self::Passes => "passes",
            Self::Disabled => "disabled",
            Self::BackendOpt => "backend-opt",
            Self::Scheduler => "scheduler",
            Self::EffectTier => "effect-tier",
            Self::NativeEffects => "native-effects",
            Self::Trampoline => "trampoline",
            Self::Fuse => "fuse",
            Self::RuntimeChecks => "rt-checks",
            Self::NativeKontFrames => "native-kont-frames",
            Self::NativeCc => "native-cc",
            Self::NativeCcVersion => "native-cc-version",
            Self::NativeCcFlags => "native-cc-flags",
        }
    }

    #[must_use]
    pub const fn is_input_root(self) -> bool {
        matches!(
            self,
            Self::SourceRoot | Self::StdlibRoot | Self::PackageRoot
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArtifactRow {
    pub field: ArtifactField,
    pub value: String,
}

impl ArtifactRow {
    fn new(field: ArtifactField, value: impl Into<String>) -> Self {
        Self {
            field,
            value: value.into(),
        }
    }
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
            opt: opt_label(cfg.opt()),
            passes: pass_spec_label(cfg.passes.as_ref()),
            disabled: disabled_label(&cfg.disabled),
            backend_opt: cfg.backend_opt().as_str().to_string(),
            scheduler: cfg.scheduler().label(),
            effect_tier: cfg.flags.effect_tier.label(),
            native_effects: cfg.flags.native_effects,
            trampoline: cfg.flags.trampoline,
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
        for row in self.rows() {
            write!(out, "{}={};", row.field.label(), row.value).unwrap();
        }
        out
    }

    #[must_use]
    pub fn rows(&self) -> Vec<ArtifactRow> {
        self.rows_for(ArtifactRows::Full)
    }

    #[must_use]
    pub fn portable_rows(&self) -> Vec<ArtifactRow> {
        self.rows_for(ArtifactRows::Portable)
    }

    fn rows_for(&self, mode: ArtifactRows) -> Vec<ArtifactRow> {
        let mut rows = vec![
            ArtifactRow::new(ArtifactField::Compiler, self.compiler_version),
            ArtifactRow::new(ArtifactField::HashScheme, self.hash_scheme),
            ArtifactRow::new(ArtifactField::Target, self.target),
            ArtifactRow::new(ArtifactField::Backend, self.backend.clone()),
        ];
        if let Some(root) = &self.source_root {
            rows.push(ArtifactRow::new(
                ArtifactField::SourceRoot,
                scheme_root(self.hash_scheme, root),
            ));
        }
        if let Some(root) = &self.stdlib_root {
            rows.push(ArtifactRow::new(
                ArtifactField::StdlibRoot,
                scheme_root(self.hash_scheme, root),
            ));
        }
        rows.extend(
            self.package_roots
                .iter()
                .map(|root| ArtifactRow::new(ArtifactField::PackageRoot, root.clone())),
        );
        rows.extend([
            ArtifactRow::new(ArtifactField::Opt, self.opt),
            ArtifactRow::new(ArtifactField::Passes, self.passes.clone()),
            ArtifactRow::new(ArtifactField::Disabled, self.disabled.clone()),
            ArtifactRow::new(ArtifactField::BackendOpt, self.backend_opt.clone()),
            ArtifactRow::new(ArtifactField::Scheduler, self.scheduler),
            ArtifactRow::new(ArtifactField::EffectTier, self.effect_tier),
            ArtifactRow::new(
                ArtifactField::NativeEffects,
                self.native_effects.to_string(),
            ),
            ArtifactRow::new(ArtifactField::Trampoline, self.trampoline.to_string()),
            ArtifactRow::new(ArtifactField::Fuse, self.fuse.to_string()),
            ArtifactRow::new(ArtifactField::RuntimeChecks, self.rt_checks.to_string()),
            ArtifactRow::new(
                ArtifactField::NativeKontFrames,
                self.native_kont_frames.to_string(),
            ),
        ]);
        if let (ArtifactRows::Full, Some(toolchain)) = (mode, &self.native_toolchain) {
            rows.extend([
                ArtifactRow::new(ArtifactField::NativeCc, toolchain.cc.clone()),
                ArtifactRow::new(ArtifactField::NativeCcVersion, toolchain.cc_version.clone()),
                ArtifactRow::new(ArtifactField::NativeCcFlags, toolchain.cc_flags.clone()),
            ]);
        }
        rows
    }
}

fn native_toolchain_identity(backend: &str) -> Option<NativeToolchainIdentity> {
    matches!(backend, "llvm" | "mlir").then(native_toolchain_for_backend)
}

#[cfg(feature = "native")]
fn native_toolchain_for_backend() -> NativeToolchainIdentity {
    let cc = cc();
    let cc_flags = cc_flags();
    let cc_version = native_cc_version(&cc);
    NativeToolchainIdentity {
        cc,
        cc_version,
        cc_flags,
    }
}

#[cfg(not(feature = "native"))]
fn native_toolchain_for_backend() -> NativeToolchainIdentity {
    NativeToolchainIdentity {
        cc: String::new(),
        cc_version: String::new(),
        cc_flags: String::new(),
    }
}

#[cfg(feature = "native")]
fn native_cc_version(cc: &str) -> String {
    Command::new(cc)
        .arg("--version")
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .and_then(|version| version.lines().next().map(str::trim).map(str::to_string))
        .filter(|version| !version.is_empty())
        .unwrap_or_else(|| {
            if cc_overridden() {
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

    fn row_fields(identity: &ArtifactIdentity) -> Vec<ArtifactField> {
        identity.rows().into_iter().map(|row| row.field).collect()
    }

    #[test]
    fn native_backend_identity_names_linker_inputs() {
        let identity = ArtifactIdentity::from_config(&Config::default(), "llvm");
        let rows = row_fields(&identity);
        assert!(rows.contains(&ArtifactField::NativeCc));
        assert!(rows.contains(&ArtifactField::NativeCcVersion));
        assert!(rows.contains(&ArtifactField::NativeCcFlags));
    }

    #[test]
    fn non_native_identity_omits_linker_inputs() {
        let identity = ArtifactIdentity::from_config(&Config::default(), "interpreter");
        let rows = row_fields(&identity);
        assert!(!rows.contains(&ArtifactField::NativeCc));
        assert!(!rows.contains(&ArtifactField::NativeCcVersion));
        assert!(!rows.contains(&ArtifactField::NativeCcFlags));
    }

    #[test]
    fn portable_rows_omit_host_toolchain_strings() {
        let identity = ArtifactIdentity::from_config(&Config::default(), "llvm");
        let rows: Vec<ArtifactField> = identity
            .portable_rows()
            .into_iter()
            .map(|row| row.field)
            .collect();
        assert!(!rows.contains(&ArtifactField::NativeCc));
        assert!(!rows.contains(&ArtifactField::NativeCcVersion));
        assert!(!rows.contains(&ArtifactField::NativeCcFlags));
    }
}
