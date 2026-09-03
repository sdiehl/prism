//! Driver pipeline tests: typed lowering routes, the export envelope,
//! content-hash canonicity, and prelude-relative source maps.

mod typed_post_route_tests {
    use crate::core::residual_effects;

    use crate::driver::*;
    use crate::flags::EffectTier;

    fn assert_route(source: &str, cfg: &Config) {
        let (_, core, _, sigs) = reuse_lowered_core(source, &[], cfg).expect("typed route");
        balanced(&core, &sigs).expect("the final typed term is balanced");
        residual_effects(&core).expect("effect nodes do not cross the final boundary");
    }

    #[test]
    fn production_route_finishes_a_pure_program() {
        assert_route("fn main() : Int = 42\n", &Config::default());
    }

    #[test]
    fn production_route_finishes_an_evidence_handler() {
        assert_route(
            "effect Ask\n  ask() : Int\n\nfn reader() : Int ! {Ask} = ask() + 1\n\nfn main() : Int =\n  handle reader() with {\n    ask() resume k => k(41),\n    return x => x\n  }\n",
            &Config::default(),
        );
    }

    #[test]
    fn production_route_finishes_a_whole_program_lowering() {
        let mut cfg = Config::default();
        cfg.update_flags(|flags| flags.effect_tier = EffectTier::FreeMonad);
        cfg.update_flags(|flags| flags.quiet = true);
        assert_route(
            "effect Ask\n  ask() : Int\n\nfn make() = \\() -> let answer = ask() in answer\n\nfn main() =\n  let _unused = make()\n  0\n",
            &cfg,
        );
    }

    #[test]
    fn production_route_accepts_the_verified_typed_control_shape() {
        // A bare `forever` loop can only leave through `return`. Typed control
        // erasure omits the legacy builder's unreachable `SMore(Unit)` branch,
        // whose Unit witness is invalid at the function's Int answer type. The
        // verified typed tree is the sole effect-lowering result.
        let src = with_prelude(include_str!("../../examples/imperative.pr"));
        let roots = default_roots(Path::new("."));
        let mut cfg = Config::default();
        cfg.update_flags(|flags| flags.compiler_cache = false);
        cfg.update_flags(|flags| flags.quiet = true);
        let (program, checked, _, typed, verify_env) =
            run_front(&src, &roots, &cfg, FrontRequest::Full)
                .expect("front")
                .into_typed_pre();
        let sigs = borrow_sigs(&program);
        let lowered = lower_opt(
            typed,
            &verify_env,
            &checked.defs.ctors,
            &checked.op_grades(),
            &cfg,
        )
        .expect("typed lowering");
        let final_core = finish_lowered(lowered, &sigs, &cfg)
            .expect("typed final route")
            .into_core();
        balanced(&final_core, &sigs).expect("balanced typed final");
        residual_effects(&final_core).expect("no residual effect nodes");
    }

    #[test]
    fn num_float_ieee_has_no_post_lowering_structural_delta() {
        let src = with_prelude(include_str!("../../tests/cases/run/num_float_ieee.pr"));
        let roots = default_roots(Path::new("."));
        let mut cfg = Config::default();
        cfg.update_flags(|flags| flags.compiler_cache = false);
        cfg.update_flags(|flags| flags.quiet = true);
        let (program, checked, _, typed, verify_env) =
            run_front(&src, &roots, &cfg, FrontRequest::Full)
                .expect("front")
                .into_typed_pre();
        let sigs = borrow_sigs(&program);
        let lowered = lower_opt(
            typed,
            &verify_env,
            &checked.defs.ctors,
            &checked.op_grades(),
            &cfg,
        )
        .expect("typed lowering");
        finish_lowered(lowered, &sigs, &cfg).expect("typed final route");
    }

    #[test]
    fn production_route_finishes_with_inferred_borrows() {
        let mut cfg = Config::default();
        cfg.update_flags(|flags| flags.borrow_infer = true);
        cfg.update_flags(|flags| flags.quiet = true);
        // The row reaches `len` as the result of a call, which stays let-bound
        // through optimization, so the borrowed position is covered by a named
        // token at the call site (a literal constructor argument would force
        // the parameter back to owned).
        let src = "type Row = Tip | Node(Int, Row)\n\nfn build(n : Int) : Row =\n  if n == 0 then Tip else Node(n, build(n - 1))\n\nfn len(r : Row) : Int =\n  match r of\n    Tip => 0\n    Node(_, rest) => 1 + len(rest)\n\nfn main() : Int =\n  len(build(2))\n";
        let (_, core, _, sigs) = reuse_lowered_core(src, &[], &cfg).expect("typed route");
        balanced(&core, &sigs).expect("balanced with inferred borrows");
        residual_effects(&core).expect("no residual effect nodes");
        let mask = sigs
            .get(&Sym::new("len"))
            .expect("len earns an inferred loan");
        assert!(
            mask.iter().any(|b| *b),
            "len keeps at least one borrowed parameter"
        );
    }

    #[test]
    fn interpreter_preparation_returns_the_unlowered_core() {
        let src = with_prelude(
            "effect Ask\n  ask() : Int\n\nfn main() : Int =\n  handle ask() with {\n    ask() resume k => k(42),\n    return x => x\n  }\n",
        );
        let roots = default_roots(Path::new("."));
        let mut cfg = Config::default();
        cfg.update_flags(|flags| flags.compiler_cache = false);
        cfg.update_flags(|flags| flags.quiet = true);
        let (_, _, expected, _, _) = run_front(&src, &roots, &cfg, FrontRequest::Full)
            .expect("front")
            .into_typed_pre();
        let actual = prepared_core(&src, &roots, &cfg).expect("prepared interpreter core");
        assert_eq!(
            serde_json::to_vec(&*actual).expect("expected bytes"),
            serde_json::to_vec(&*expected).expect("actual bytes"),
            "the interpreter must keep evaluating pre-effect-lowering Core"
        );
        assert!(
            residual_effects(&actual).is_err(),
            "the interpreter must retain the source effect nodes"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn report_uses_the_same_verified_final_core() {
        let output = report::report_on("fn main() : Int = 42\n", &[], &Config::default());
        assert!(output.contains("== llvm =="));
        assert!(!output.contains("(skipped:"), "{output}");
    }
}

mod envelope_tests {
    #[cfg(feature = "native")]
    use std::collections::BTreeMap;
    #[cfg(feature = "native")]
    use std::path::Path;

    #[cfg(feature = "native")]
    use crate::resolve::{Root, SourceBundleIdentity};
    #[cfg(feature = "native")]
    use crate::stdlib::STDLIB;

    use crate::core::HASH_SCHEME;
    #[cfg(feature = "native")]
    use crate::driver::identity::native_kont_table_for;
    #[cfg(feature = "native")]
    use crate::driver::{default_roots, dump_on, Config};
    use crate::driver::{dump, example_program, EnvelopeHeader, WireKind, NAMESPACE_FORMAT};
    #[cfg(feature = "native")]
    use prism_native::MAIN_SYMBOL;

    const STORE_PKG_NAME: &str = "StorePkg";
    #[cfg(feature = "native")]
    const STORE_PKG_SOURCE: &str = "pub fn answer() : Int = 41\n";
    #[cfg(feature = "native")]
    const STORE_PKG_ROOT: &str = "abc123";

    #[test]
    fn example_program_keeps_leading_imports_outside_main() {
        let source = "import Data.Tensor (..)\n\nstrides(new([2, 3], 0.0))\n";
        let program = example_program(source);
        assert!(program.starts_with("import Data.Tensor (..)\nfn main() =\n"));
        assert!(program.contains("  strides(new([2, 3], 0.0))"));
        assert_eq!(example_program(&program), program, "wrapping is idempotent");
    }

    /// The five-kind family: textual tags are distinct, varints are the distinct
    /// contiguous discriminants the binary codec will reuse, and `parse` inverts
    /// `tag`. This checks the family so the text header and the future body cannot
    /// drift out of a shared ordering.
    #[test]
    fn kind_family_is_pinned() {
        let all = [
            WireKind::Value,
            WireKind::Def,
            WireKind::Protocol,
            WireKind::Kont,
            WireKind::Cert,
        ];
        for (i, k) in all.into_iter().enumerate() {
            assert_eq!(WireKind::parse(k.tag()), Some(k));
            assert_eq!(usize::from(k.varint()), i);
        }
        assert_eq!(WireKind::parse("gremlin"), None);
    }

    /// A `dump namespace` export parses back to its header: scheme accepted, kind
    /// and contract digest recoverable, format matched.
    #[test]
    fn namespace_header_round_trips() {
        let out = dump("namespace", "let main = 1\n").expect("namespace export");
        let doc: serde_json::Value = serde_json::from_str(&out).expect("valid json export");
        let hdr = EnvelopeHeader::parse(&doc).expect("header parses");
        assert_eq!(hdr.kind, WireKind::Def);
        assert_eq!(hdr.format, NAMESPACE_FORMAT);
        assert!(!hdr.contract.is_empty());
    }

    #[test]
    fn artifact_identity_fingerprint_names_roots() {
        let identity = crate::driver::Config::default()
            .artifact_identity_for("llvm")
            .with_source_root("source123")
            .with_stdlib_root("std456")
            .with_package_roots([format!("{STORE_PKG_NAME}@{HASH_SCHEME}:pkg789")]);
        let fingerprint = identity.fingerprint();
        assert!(fingerprint.contains(&format!("source-root={HASH_SCHEME}:source123;")));
        assert!(fingerprint.contains(&format!("stdlib-root={HASH_SCHEME}:std456;")));
        assert!(fingerprint.contains(&format!(
            "package-root={STORE_PKG_NAME}@{HASH_SCHEME}:pkg789;"
        )));
    }

    /// Native kont serialization needs this table as its code-identity bridge:
    /// raw native symbols are paired with the same definition hashes used by the
    /// interpreter kont envelope.
    #[cfg(feature = "native")]
    #[test]
    fn native_kont_table_names_native_symbols_by_hash() {
        let out = dump("native-kont-table", "fn main() = 1\n").expect("native kont table");
        assert!(out.starts_with(&format!("scheme  {HASH_SCHEME}\nbundle  ")));
        assert!(
            out.contains(&format!("compiler  {}\n", env!("CARGO_PKG_VERSION")))
                && out.contains(&format!("target  {}\n", env!("PRISM_TARGET")))
                && out.contains("backend  llvm\n")
                && out.contains("flag  scheduler  cooperative\n")
                && out.contains("flag  backend-opt  2\n")
                && out.contains("flag  effect-tier  auto\n"),
            "native table includes portable artifact identity:\n{out}"
        );
        assert!(
            !out.contains("native-cc-version"),
            "dumped native table must not embed host-specific C compiler strings:\n{out}"
        );
        assert!(
            out.contains(&format!("flag  source-root  {HASH_SCHEME}:"))
                && out.contains(&format!("flag  stdlib-root  {HASH_SCHEME}:")),
            "native table names source and Std roots:\n{out}"
        );
        assert!(
            out.lines().any(|line| {
                line.starts_with(&format!("fn      {MAIN_SYMBOL}  ")) && line.ends_with("  main")
            }),
            "native table includes the main symbol and its definition hash:\n{out}"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn native_kont_table_names_package_source_roots() {
        let mut modules = BTreeMap::new();
        modules.insert(STORE_PKG_NAME.to_string(), STORE_PKG_SOURCE.to_string());
        let bundle_identity =
            SourceBundleIdentity::package(STORE_PKG_NAME, HASH_SCHEME, STORE_PKG_ROOT);
        let expected = format!("flag  package-root  {}\n", bundle_identity.descriptor());
        let roots = vec![
            Root::identified_source_bundle(
                format!("<package {STORE_PKG_NAME} {STORE_PKG_ROOT}>"),
                bundle_identity,
                modules,
            ),
            Root::Embedded(STDLIB),
        ];
        let out = native_kont_table_for(
            "import StorePkg (answer)\nfn main() : Int = answer() + 1\n",
            &roots,
            &Config::default(),
        )
        .expect("native kont table");
        assert!(
            out.contains(&expected),
            "native table names package roots:\n{out}"
        );
        assert!(
            out.contains("flag  native-cc  ")
                && out.contains("flag  native-cc-version  ")
                && out.contains("flag  native-cc-flags  "),
            "native build table names native linker inputs:\n{out}"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn native_kont_state_map_names_entry_abi_words() {
        let out = dump(
            "native-kont-state-map",
            "fn count(i, last) = if i > last then i else count(i + 1, last)\n\nfn main() = count(1, 2)\n",
        )
        .expect("native kont state map");
        assert!(out.starts_with(&format!("state-map 1\nscheme  {HASH_SCHEME}\nbundle  ")));
        assert!(
            out.contains("slot-format prism-native-abi-word-v1")
                && out.contains("backend  llvm\n")
                && out.contains("flag  scheduler  cooperative\n")
                && out.contains(&format!("state {} ", prism_native::native_symbol("count")))
                && out.contains(" count arity 2 slots abi-word[arg0=%a0:word,arg1=%a1:word]"),
            "native state map includes concrete entry ABI words:\n{out}"
        );
    }

    // The other side of the instrumentation gate: under the DEFAULT flags the
    // metadata table must still be embedded while the enter/arg/leave calls and
    // shadow-name constants must be absent, so neither half of the opt-in can
    // silently flip.
    #[cfg(feature = "native")]
    #[test]
    fn llvm_dump_default_has_table_without_frame_instrumentation() {
        let out = dump("llvm", "fn main() = 1\n").expect("llvm dump");
        assert!(
            out.contains("@prism_native_kont_table = constant"),
            "default LLVM IR embeds the native kont table global:\n{out}"
        );
        assert!(
            !out.contains("@prism_native_kont_enter") && !out.contains(".kont.shadow."),
            "default LLVM IR must not carry opt-in frame instrumentation:\n{out}"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn llvm_dump_embeds_native_kont_table_global() {
        // The native kont metadata globals are always emitted, but the enter/arg/leave
        // ABI instrumentation calls are gated behind `native_kont_frames`. Enable that
        // flag (leaving every other flag at the ambient default) so this dump exercises
        // both the metadata table and the instrumented lowering under one assertion set.
        let mut cfg = Config::from_env();
        cfg.update_flags(|flags| flags.native_kont_frames = true);
        let roots = default_roots(Path::new("."));
        let llvm = |src: &str| dump_on("llvm", src, &roots, &cfg).expect("llvm dump");

        let out = llvm("fn main() = 1\n");
        assert!(
            out.contains("@prism_native_kont_table = constant"),
            "LLVM IR embeds the native kont table global:\n{out}"
        );
        assert!(
            out.contains("@prism_native_kont_state_map = constant")
                && out.contains("state-map 1")
                && out.contains("slot-format prism-native-abi-word-v1")
                && out.contains("slots abi-word[]"),
            "LLVM IR embeds the native kont state-map:\n{out}"
        );
        let out = llvm(
            "fn count(i, last) = if i > last then i else count(i + 1, last)\n\nfn main() = count(1, 2)\n",
        );
        assert!(
            out.contains(&format!("state {} ", prism_native::native_symbol("count")))
                && out.contains(" count arity 2 slots abi-word[arg0=%a0:word,arg1=%a1:word]"),
            "LLVM IR embeds concrete ABI-word slots for native arguments:\n{out}"
        );
        assert!(
            out.contains("call void @prism_native_kont_enter")
                && out.contains("call void @prism_native_kont_arg")
                && out.contains("call void @prism_native_kont_leave"),
            "LLVM IR instruments native kont entry ABI values:\n{out}"
        );
        assert!(
            out.contains(MAIN_SYMBOL) && out.contains(" main\\0A"),
            "LLVM IR table includes the native main symbol and Core name:\n{out}"
        );
        assert!(
            out.contains("@prism_native_kont_ptrs = constant")
                && out.contains("@prism_native_kont_ptrs_len = constant")
                && out.contains(&format!("ptr @{MAIN_SYMBOL}")),
            "LLVM IR embeds an exact function-pointer kont lookup table:\n{out}"
        );
    }

    /// A mismatched scheme is rejected on the header, before any body is decoded.
    #[test]
    fn foreign_scheme_is_rejected() {
        let doc = serde_json::json!({
            "envelope": {
                "scheme": "some-other-scheme-v9",
                "kind": WireKind::Def.tag(),
                "contract": "deadbeef",
                "format": NAMESPACE_FORMAT,
            },
        });
        assert_eq!(EnvelopeHeader::parse(&doc), None);
    }
}

mod content_hash_canonicity_tests {
    use crate::driver::{check_on_in, Config};
    use crate::resolve::default_roots;
    use std::path::Path;

    // The elaboration content hash folds each declaration's `Type::show()`
    // rendering (`hash_meta`), so a stable content address rests on alpha-
    // equivalent definitions rendering byte-identically. Generalization assigns
    // canonical variable names in structural order, so two programs that differ
    // only in the spelling of a type variable must yield the same rendered
    // scheme; if this ever regressed, equal definitions would receive different
    // addresses and content addressing would no longer be a pure function of
    // meaning. This pins the invariant the hash silently depends on.
    #[test]
    fn alpha_equivalent_signatures_render_canonically() {
        let roots = default_roots(Path::new("."));
        let mut cfg = Config::default();
        cfg.update_flags(|flags| flags.quiet = true);
        let show_id = |src: &str| {
            check_on_in(src, &roots, &cfg)
                .expect("program checks")
                .defs
                .decls
                .iter()
                .find(|d| d.name == "id")
                .map(|d| d.ty.show())
        };
        let left = show_id("fn id(x : a) : a = x\n").expect("id present");
        let right = show_id("fn id(x : zebra) : zebra = x\n").expect("id present");
        assert_eq!(
            left, right,
            "alpha-equivalent signatures must render identically"
        );
        // Generalization canonicalizes the source-chosen name away, proving the
        // rendering is a function of structure, not of the written variable.
        assert!(
            left.starts_with("forall a."),
            "generalization renames to the canonical `a`, got {left}"
        );
        assert!(!right.contains("zebra"), "canonical rename dropped `zebra`");
    }
}

mod source_map_tests {
    use crate::driver::{with_custom_prelude, with_prelude};
    use crate::error::SourceMap;

    // Diagnostics under a custom prelude must be user-relative, exactly like
    // the built-in path: the composed source carries the boundary mark, and
    // SourceMap reads it back. This was silently wrong (offset by the whole
    // custom prelude) before the mark existed.
    #[test]
    fn custom_prelude_positions_are_user_relative() {
        let user_src = "fn main() =\n  oops()\n";
        let full = with_custom_prelude("fn helper() = 1\nfn helper2() = 2", user_src);
        let map = SourceMap::new(&full);
        assert_eq!(map.user(), user_src);
        let off = map.prelude_len() + map.user().find("oops").unwrap();
        assert_eq!(map.at(off), "line 2:3");
    }

    // The built-in prelude path is unchanged: located by its known text, no
    // boundary mark involved.
    #[test]
    fn builtin_prelude_positions_are_user_relative() {
        let user_src = "fn main() = 1\n";
        let full = with_prelude(user_src);
        let map = SourceMap::new(&full);
        assert_eq!(map.user(), user_src);
        assert_eq!(map.at(map.prelude_len()), "line 1:1");
    }
}
