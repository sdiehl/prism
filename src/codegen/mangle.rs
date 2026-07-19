//! One home for native-symbol mangling: the reserved, lexically disjoint
//! symbol namespaces, the injective Core-name encoder and its tested inverse,
//! and the per-family symbol builders every backend and code generator shares.

/// The native symbol namespaces, and the one rule that keeps them apart.
///
/// Several definers emit symbols into a single flat native namespace: Core
/// functions (whose names come from user source, so they are attacker-chosen as
/// far as the backend is concerned), the codegen-generated families, and the
/// C runtime. A user function named `bump`, `alloc`, or `box` must not be able
/// to spell a symbol one of the others already defines.
///
/// Detection is the wrong tool here: rejecting `fn bump` is a language
/// regression, and a check against today's runtime symbol table would rot the
/// moment the runtime gains a function. So the prefixes are chosen to make
/// collision a *lexical impossibility*. Each is `prism` followed by a distinct
/// character at index 5:
///
/// | definer | prefix | index 5 |
/// | --- | --- | --- |
/// | Core functions ([`native_symbol`]) | `prismfn_` | `f` |
/// | codegen lambdas | `prismlam_` | `l` |
/// | codegen apply dispatchers | `prismap_` | `a` |
/// | codegen TRMC helpers ([`trmc_symbol`]) | `prismtrmc_` | `t` |
/// | C runtime (`runtime/*.c`) | `prism_` | `_` |
///
/// No two strings agreeing at index 5 can differ in prefix, and no two of these
/// prefixes agree there, so no name any definer chooses can ever collide with
/// another's, whatever either side is renamed to later. `rt::tests` pins the
/// runtime half of the argument: nothing under `runtime/` may define a symbol
/// outside the `prism_` prefix.
///
/// A generated family earns a prefix rather than a decoration on a Core name,
/// because a decoration is forgeable. Giving the family its own namespace is
/// what makes a user spelling of the same suffix irrelevant instead of merely
/// unlikely.
///
/// This is the root they all share; the byte right after it is the discriminant.
pub(crate) const SYM_NAMESPACE: &str = "prism";
pub(crate) const SYM_FN: &str = "prismfn_";
pub(crate) const SYM_LAM: &str = "prismlam_";
pub(crate) const SYM_APPLY: &str = "prismap_";
pub(crate) const SYM_TRMC: &str = "prismtrmc_";
pub(crate) const SYM_RUNTIME: &str = "prism_";

// GHC-style escape codes for the punctuation carried by real Core names. `Z`
// introduces every escape and therefore escapes itself; the generic `ZxHH`
// form keeps the encoder total over UTF-8 without assigning raw punctuation any
// backend-specific meaning.
const NAME_ESCAPE: u8 = b'Z';
const HEX: &[u8; 16] = b"0123456789abcdef";

/// Byte that distinguishes `prefix`'s namespace, given that it opens with
/// [`SYM_NAMESPACE`].
const fn discriminant(prefix: &str) -> u8 {
    let (bytes, root) = (prefix.as_bytes(), SYM_NAMESPACE.as_bytes());
    assert!(
        bytes.len() > root.len(),
        "prefix must extend the namespace root"
    );
    let mut i = 0;
    while i < root.len() {
        assert!(
            bytes[i] == root[i],
            "prefix must open with the namespace root"
        );
        i += 1;
    }
    bytes[root.len()]
}

// The disjointness argument, checked when the compiler compiles: every prefix
// extends `prism` and no two agree on the byte that follows it. A change that
// broke this would silently reopen the collision class where a user function
// named after a runtime intrinsic (`bump`, `alloc`, `box`) emits a duplicate
// definition of it, so it fails here rather than in a user's link step.
const _: () = {
    let (f, l, a, t, r) = (
        discriminant(SYM_FN),
        discriminant(SYM_LAM),
        discriminant(SYM_APPLY),
        discriminant(SYM_TRMC),
        discriminant(SYM_RUNTIME),
    );
    assert!(
        f != l
            && f != a
            && f != t
            && f != r
            && l != a
            && l != t
            && l != r
            && a != t
            && a != r
            && t != r,
        "native symbol prefixes must be pairwise disjoint"
    );
};

/// Injectively encode one Core name into the portable native-symbol alphabet.
///
/// ASCII letters, digits, and `_` remain readable. `Z` is doubled, and the
/// punctuation Core actually mints has a short code:
///
/// | Core byte | native spelling |
/// | --- | --- |
/// | `Z` | `ZZ` |
/// | `.` | `Zd` |
/// | `@` | `Za` |
/// | `$` | `Zs` |
/// | `%` | `Zp` |
/// | `#` | `Zh` |
///
/// Every other byte is `ZxHH`. Since a literal `Z` never survives unescaped,
/// these forms are prefix-decodable. The decoder below is a left inverse, which
/// is the constructive injectivity proof used by the tests.
fn encode_core_name(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for byte in name.bytes() {
        match byte {
            b'Z' => out.push_str("ZZ"),
            b'.' => out.push_str("Zd"),
            b'@' => out.push_str("Za"),
            b'$' => out.push_str("Zs"),
            b'%' => out.push_str("Zp"),
            b'#' => out.push_str("Zh"),
            b if b.is_ascii_alphanumeric() || b == b'_' => out.push(b as char),
            b => {
                out.push(NAME_ESCAPE as char);
                out.push('x');
                out.push(HEX[(b >> 4) as usize] as char);
                out.push(HEX[(b & 0x0f) as usize] as char);
            }
        }
    }
    out
}

#[cfg(test)]
fn decode_core_name(encoded: &str) -> Option<String> {
    fn hex(byte: u8) -> Option<u8> {
        match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        }
    }

    let bytes = encoded.as_bytes();
    let mut decoded = Vec::with_capacity(encoded.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != NAME_ESCAPE {
            if !bytes[i].is_ascii_alphanumeric() && bytes[i] != b'_' {
                return None;
            }
            decoded.push(bytes[i]);
            i += 1;
            continue;
        }

        let code = *bytes.get(i + 1)?;
        match code {
            b'Z' => {
                decoded.push(b'Z');
                i += 2;
            }
            b'd' => {
                decoded.push(b'.');
                i += 2;
            }
            b'a' => {
                decoded.push(b'@');
                i += 2;
            }
            b's' => {
                decoded.push(b'$');
                i += 2;
            }
            b'p' => {
                decoded.push(b'%');
                i += 2;
            }
            b'h' => {
                decoded.push(b'#');
                i += 2;
            }
            b'x' => {
                let hi = hex(*bytes.get(i + 2)?)?;
                let lo = hex(*bytes.get(i + 3)?)?;
                decoded.push((hi << 4) | lo);
                i += 4;
            }
            _ => return None,
        }
    }
    String::from_utf8(decoded).ok()
}

/// Native symbol name for a Core function.
///
/// Core names use `.` for exported module members, `@` for private/hygienic
/// names, and `$`/`%`/`#` in synthesized names. Replacing one separator with
/// another is not injective (`Wire@dec_list` and `Wire.dec_list` used to alias),
/// so `encode_core_name` gives each byte a reversible spelling accepted
/// unquoted by LLVM and MLIR.
///
/// The `SYM_FN` prefix is what keeps a user function named after a runtime
/// intrinsic from colliding with it; see the namespace table above.
#[must_use]
pub fn native_symbol(name: &str) -> String {
    format!("{SYM_FN}{}", encode_core_name(name))
}

/// Native symbol for the codegen-generated lambda body carrying `tag`.
#[must_use]
pub(crate) fn lam_symbol(tag: usize) -> String {
    format!("{SYM_LAM}{tag}")
}

/// Native symbol for the codegen-generated apply dispatcher of arity `n`.
#[must_use]
pub(crate) fn apply_symbol(n: usize) -> String {
    format!("{SYM_APPLY}{n}")
}

/// Native symbol for the codegen-generated TRMC helper of the Core function
/// `name`: the hole-passing loop a tail-modulo-constructor call lowers to.
#[must_use]
pub fn trmc_symbol(name: &str) -> String {
    format!("{SYM_TRMC}{}", encode_core_name(name))
}

/// The program entry point's native symbol.
///
/// This is the single place the C runtime reaches into the `SYM_FN` namespace:
/// `main` is an ordinary Prism function, so the runtime calls it by its mangled
/// name like any other. Spelled out rather than built from [`native_symbol`]
/// because the C runtime and several test harnesses need it as a `&'static str`;
/// `entry_symbol_matches_native_symbol` pins it to the generated spelling so the
/// two cannot drift.
pub const MAIN_SYMBOL: &str = "prismfn_main";

#[cfg(test)]
mod tests {
    use super::{
        apply_symbol, decode_core_name, encode_core_name, lam_symbol, native_symbol, trmc_symbol,
        MAIN_SYMBOL, SYM_APPLY, SYM_FN, SYM_LAM, SYM_RUNTIME, SYM_TRMC,
    };
    use crate::names::ENTRY_POINT;

    #[test]
    fn entry_symbol_matches_native_symbol() {
        assert_eq!(MAIN_SYMBOL, native_symbol(ENTRY_POINT));
    }

    // Every generated name must actually land in its own namespace, including
    // the runtime-colliding names that motivated the split. Pairwise disjointness
    // of the prefixes themselves is asserted at compile time above.
    #[test]
    fn generated_symbols_land_in_their_namespace() {
        for name in ["bump", "alloc", "box", "main", "lam_0", "apply_1"] {
            let sym = native_symbol(name);
            assert!(sym.starts_with(SYM_FN), "`{sym}` escaped the fn namespace");
            assert!(
                !sym.starts_with(SYM_RUNTIME),
                "user name `{name}` reached the runtime namespace as `{sym}`"
            );
        }
        assert!(lam_symbol(0).starts_with(SYM_LAM));
        assert!(apply_symbol(1).starts_with(SYM_APPLY));
        // A TRMC helper must not be spellable as a Core name. Decorating the
        // Core spelling would put `bump.trmc` and module `bump`'s `trmc` on the
        // same symbol; its own namespace is what rules that out.
        assert_ne!(trmc_symbol("bump"), native_symbol("bump.trmc"));
        assert!(trmc_symbol("bump").starts_with(SYM_TRMC));
    }

    #[test]
    fn core_name_encoding_is_injective() {
        let cases = [
            "",
            "main",
            "unwrap_or",
            "Wire.dec_list",
            "Wire@dec_list",
            "f$sp3",
            "%fu@0",
            "reuse#slot",
            "0@driver",
            "1@step",
            "2@lift",
            "prismfn_bump",
            "Zed",
            "λ@worker",
        ];
        for name in cases {
            let encoded = encode_core_name(name);
            assert_eq!(
                decode_core_name(&encoded).as_deref(),
                Some(name),
                "`{name}` did not round-trip through `{encoded}`"
            );
            assert!(
                encoded
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_'),
                "`{name}` escaped the portable symbol alphabet as `{encoded}`"
            );
        }

        assert_eq!(encode_core_name("Wire.dec_list"), "WireZddec_list");
        assert_eq!(encode_core_name("Wire@dec_list"), "WireZadec_list");
        assert_eq!(encode_core_name("f$sp3"), "fZssp3");
        assert_eq!(encode_core_name("%fu@0"), "ZpfuZa0");
        assert_eq!(encode_core_name("0@driver"), "0Zadriver");
        assert_eq!(encode_core_name("1@step"), "1Zastep");
        assert_eq!(encode_core_name("2@lift"), "2Zalift");
        assert_eq!(encode_core_name("reuse#slot"), "reuseZhslot");
        assert_eq!(encode_core_name("Zed"), "ZZed");
        assert_eq!(encode_core_name("λ@worker"), "ZxceZxbbZaworker");
        assert_ne!(
            native_symbol("Wire.dec_list"),
            native_symbol("Wire@dec_list"),
            "exported and private module members must not alias"
        );
        assert_ne!(
            native_symbol("prismfn_bump"),
            native_symbol("bump"),
            "a source binder containing the Core-function prefix must still be data"
        );
        assert_eq!(native_symbol("prismfn_bump"), "prismfn_prismfn_bump");
    }

    #[test]
    fn core_name_decoder_rejects_malformed_spellings() {
        for malformed in ["Z", "Zq", "Zx", "Zx0", "Zx0g", ".", "@"] {
            assert_eq!(
                decode_core_name(malformed),
                None,
                "accepted malformed native name `{malformed}`"
            );
        }
    }
}
