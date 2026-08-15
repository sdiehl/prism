//! The surface-language target: type system and elaboration behavior, the
//! diagnostic catalogue and warning surfaces, and the formatter's layout and
//! idempotence laws.

fn ast_no_spans(src: &str) -> String {
    prism::dump("ast", src)
        .expect("must parse")
        .lines()
        .filter(|line| {
            let trimmed = line.trim_start();
            let range = trimmed.trim_end_matches(',');
            let is_range = matches!(range.split_once(".."), Some((start, end))
                if !start.is_empty()
                    && start.bytes().all(|byte| byte.is_ascii_digit())
                    && end.bytes().all(|byte| byte.is_ascii_digit()));
            !trimmed.starts_with("span:") && !is_range
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn assert_format(src: &str, expected: &str) {
    let once = prism::format(src).expect("input must parse");
    assert_eq!(once, expected, "layout drift:\n{once}");
    let twice = prism::format(&once).expect("formatted output must reparse");
    assert_eq!(once, twice, "not idempotent:\n{once}\n-->\n{twice}");
}

fn assert_format_semantics(src: &str, expected: &str) {
    assert_format(src, expected);
    assert_eq!(
        ast_no_spans(src),
        ast_no_spans(expected),
        "formatting changed the parsed meaning:\n{src}\n-->\n{expected}"
    );
}

mod support;

#[path = "language/captures.rs"]
mod captures;
#[path = "language/core_hash.rs"]
mod core_hash;
#[path = "language/decl_order.rs"]
mod decl_order;
#[path = "language/derive.rs"]
mod derive;
#[path = "language/effect_rows.rs"]
mod effect_rows;
#[path = "language/grammar_ebnf.rs"]
mod grammar_ebnf;
#[path = "language/hash_parity.rs"]
mod hash_parity;
#[path = "language/let_else.rs"]
mod let_else;
#[path = "language/local_generalize.rs"]
mod local_generalize;
#[path = "language/match_oracle.rs"]
mod match_oracle;
#[path = "language/module_self_import.rs"]
mod module_self_import;
#[path = "language/modules.rs"]
mod modules;
#[path = "language/num_tower.rs"]
mod num_tower;
#[path = "language/ordered_witness.rs"]
mod ordered_witness;
#[path = "language/param_annot.rs"]
mod param_annot;
#[path = "language/path_lit.rs"]
mod path_lit;
#[path = "language/query.rs"]
mod query;
#[path = "language/reflect.rs"]
mod reflect;
#[path = "language/rigid_sig_vars.rs"]
mod rigid_sig_vars;
#[path = "language/skolem_escape.rs"]
mod skolem_escape;
#[path = "language/soundness.rs"]
mod soundness;
#[path = "language/suggestions.rs"]
mod suggestions;
#[path = "language/tier_explain.rs"]
mod tier_explain;
#[path = "language/typed_holes.rs"]
mod typed_holes;

#[path = "formatter/fmt_break.rs"]
mod fmt_break;
#[path = "formatter/fmt_contracts.rs"]
mod fmt_contracts;
#[path = "formatter/fmt_control.rs"]
mod fmt_control;
#[path = "formatter/fmt_deriving.rs"]
mod fmt_deriving;
#[path = "formatter/fmt_let_else.rs"]
mod fmt_let_else;
#[path = "formatter/fmt_list_patterns.rs"]
mod fmt_list_patterns;
#[path = "formatter/fmt_modifiers.rs"]
mod fmt_modifiers;
#[path = "formatter/fmt_parens.rs"]
mod fmt_parens;
#[path = "formatter/fmt_path_lit.rs"]
mod fmt_path_lit;
#[path = "formatter/fmt_path_stmt.rs"]
mod fmt_path_stmt;
#[path = "formatter/fmt_records_optics.rs"]
mod fmt_records_optics;
#[path = "formatter/fmt_stable.rs"]
mod fmt_stable;
#[path = "formatter/fmt_trivia.rs"]
mod fmt_trivia;
#[path = "formatter/fmt_tuples.rs"]
mod fmt_tuples;
#[path = "formatter/fmt_using.rs"]
mod fmt_using;

#[path = "frontend/contracts.rs"]
mod contracts;
#[path = "frontend/effect_op_collision.rs"]
mod effect_op_collision;
#[path = "frontend/env_knobs.rs"]
mod env_knobs;
#[path = "frontend/error_codes.rs"]
mod error_codes;
#[path = "frontend/holes.rs"]
mod holes;
#[path = "frontend/prelude_capture.rs"]
mod prelude_capture;
#[path = "frontend/row_laws.rs"]
mod row_laws;
#[path = "frontend/semantic_patch.rs"]
mod semantic_patch;
#[path = "frontend/totality.rs"]
mod totality;
#[path = "frontend/type_query.rs"]
mod type_query;
#[path = "frontend/warn_dupes.rs"]
mod warn_dupes;
