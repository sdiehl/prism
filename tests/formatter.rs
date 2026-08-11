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
