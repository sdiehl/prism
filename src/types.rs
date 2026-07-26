//! The compiler-side type seam.
//!
//! The vocabulary lives in `prism-core`; the checker's entry points and
//! checked-program facts re-export here so `types::{check, Checked, ...}`
//! stays the one import surface the driver, evaluator, and docs generator
//! share.

pub use prism_core::types::*;

pub use crate::tc::{
    check, check_allow_holes, check_seeded, check_seeded_allow_holes, hole_error, infer_expr,
    infer_expr_allow_holes, infer_expr_dicts, infer_expr_dicts_allow_holes, infer_expr_env, Canon,
    Checked, ClassInfo, DataInfo, Dict, DictTable, Env, HeadKey, HoleBinding, HoleCandidate,
    HoleReport, InstInfo, InstKeys, PathRes, TypecheckSeed, Warning,
};
