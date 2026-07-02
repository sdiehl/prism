//! Single source of truth for the C runtime symbols codegen calls by name.
//!
//! These are the `prism_*` intrinsics defined in `runtime/prism_rt.c` that the
//! emitter references directly: allocation, reference counting, boxing, the IO
//! ops, local mutable refs, the bignum arithmetic helpers, and the effect-machine
//! instrumentation. Spelling each as a named constant here (rather than a string
//! literal scattered across the emitter) means a rename happens in one place, and
//! the drift guard below pins every name to a definition in the runtime so a
//! mismatch fails the build instead of the linker.
//!
//! The surface builtins (`concat`, `show_int`, the fixed-width arithmetic, ...)
//! are not here: their symbols are derived once from [`crate::core::builtins::Builtin::sym`].

// Allocation and reference counting.
pub(super) const ALLOC: &str = "prism_alloc";
pub(super) const REUSE_ALLOC: &str = "prism_reuse_alloc";
pub(super) const REUSE_TOKEN: &str = "prism_reuse_token";
pub(super) const RC_INC: &str = "prism_rc_inc";
pub(super) const RC_DEC: &str = "prism_rc_dec";

// Tagging: box/unbox a 63-bit payload, and the interned string-literal cell.
pub(super) const BOX: &str = "prism_box";
pub(super) const UNBOX: &str = "prism_unbox";
pub(super) const STR_LIT: &str = "prism_str_lit";

// IO intrinsics (the lowered forms of `Comp::Io`).
pub(super) const PRINT_INT: &str = "prism_print_int";
pub(super) const PRINT_FLOAT: &str = "prism_print_float";
pub(super) const PRINT_NL: &str = "prism_print_nl";
pub(super) const READ_INT: &str = "prism_prim_read_int";
pub(super) const READ_LINE: &str = "prism_prim_read_line";
pub(super) const RAND: &str = "prism_prim_rand";
pub(super) const SRAND: &str = "prism_srand";
pub(super) const FATAL: &str = "prism_fatal";

// Local mutable cells (the runtime form of an escape-checked `var`).
pub(super) const REF_NEW: &str = "prism_ref_new";
pub(super) const REF_GET: &str = "prism_ref_get";
pub(super) const REF_SET: &str = "prism_ref_set";

// Bignum arithmetic, the slow path of the tagged-int operators.
pub(super) const INT_ADD: &str = "prism_rt_int_add";
pub(super) const INT_SUB: &str = "prism_rt_int_sub";
pub(super) const INT_MUL: &str = "prism_rt_int_mul";
pub(super) const INT_DIV: &str = "prism_rt_int_div";
pub(super) const INT_REM: &str = "prism_rt_int_rem";
pub(super) const INT_CMP: &str = "prism_rt_int_cmp";

// Effect-machine instrumentation and the over-application trap.
pub(super) const EFFOP_ALLOC: &str = "prism_effop_alloc";
pub(super) const DRIVE_STEP: &str = "prism_drive_step";
pub(super) const APPLY_ERROR: &str = "prism_apply_error";

// Every runtime symbol named above, for the drift guard.
#[cfg(test)]
const ALL: &[&str] = &[
    ALLOC,
    REUSE_ALLOC,
    REUSE_TOKEN,
    RC_INC,
    RC_DEC,
    BOX,
    UNBOX,
    STR_LIT,
    PRINT_INT,
    PRINT_FLOAT,
    PRINT_NL,
    READ_INT,
    READ_LINE,
    RAND,
    SRAND,
    FATAL,
    REF_NEW,
    REF_GET,
    REF_SET,
    INT_ADD,
    INT_SUB,
    INT_MUL,
    INT_DIV,
    INT_REM,
    INT_CMP,
    EFFOP_ALLOC,
    DRIVE_STEP,
    APPLY_ERROR,
];

#[cfg(test)]
mod tests {
    use super::ALL;

    // Every runtime symbol the emitter calls must be defined in the C runtime.
    // A rename on one side without the other would otherwise surface only as a
    // link failure (or, worse, a call to a stale symbol); this turns it into a
    // build failure naming the offender.
    #[test]
    fn symbols_defined_in_runtime() {
        let rt = include_str!("../../runtime/prism_rt.c");
        for sym in ALL {
            assert!(
                rt.contains(sym),
                "runtime symbol `{sym}` (codegen::rt) is not defined in runtime/prism_rt.c"
            );
        }
    }
}
