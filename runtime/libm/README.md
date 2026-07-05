# Vendored double-precision libm

These files are the double-precision subset of [musl libc](https://musl.libc.org/)'s math library (`src/math`, `src/internal/libm.h`, `arch/generic/fp_arch.h`), vendored verbatim from musl 1.2.6 (commit 5122f9f), MIT licensed (see `COPYRIGHT`).

## Why this exists

Prism's determinism contract is byte-for-byte reproducibility across backends and platforms. The system libm is the actual source of cross-platform float divergence (glibc, macOS, and BSD libm all round transcendentals differently in the last bit), so Prism owns one fixed implementation instead. Every `FloatOp` transcendental on every backend routes through these files:

- native codegen emits calls to the `prism_m_*` wrappers in `../prism_libm.c`;
- the interpreter FFIs the same `prism_m_*` symbols (the compiler binary links this runtime), so interpreter and native are bit-identical by construction, not merely by test;
- the wasm interpreter (no C toolchain in that build) falls back to the `libm` crate, which differs from this vendored copy by about 1 ULP on a few functions; that is a documented, ungated, browser-only boundary this release (there is no native backend in the browser to diverge from).

The contract is determinism, not correct rounding: correctly-rounded transcendentals are an explicit non-goal deferred to a later release.

## Local patches

Kept as small as possible so a re-vendor is a near-clean copy:

- `libm.h`: `#include <endian.h>` (musl-only) replaced with a portable little-endian `__BYTE_ORDER` definition (every target we compile for is little-endian); the `hidden` visibility macro (musl defines it in its own `libc.h`) defined as a no-op.
- `exp_data.h`, `log_data.h`, `log2_data.h`, `pow_data.h`: `#include <features.h>` (musl-only, only supplied `hidden`) removed.

Every math symbol these files need resolves within this set (no `-lm`); `sqrt` for internal callers is provided by `../prism_libm.c` as the hardware IEEE square root.

## Determinism flag

All of this is compiled with `-ffp-contract=off` (pinned in `build.rs` and the driver link step). Without it a compiler may fuse `a*b+c` into an FMA on one platform and not another, diverging the last bit of both ordinary arithmetic and these functions' internals.
