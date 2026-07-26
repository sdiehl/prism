pub(super) fn fmt_float(f: f64) -> String {
    let s = format!("{f}");
    if f.is_finite() && !s.contains(['.', 'e', 'E']) {
        format!("{s}.0")
    } else {
        s
    }
}

pub(super) fn fmt_char(c: char) -> String {
    let inner = match c {
        '\\' => "\\\\".into(),
        '\'' => "\\'".into(),
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        '\r' => "\\r".into(),
        c => c.to_string(),
    };
    format!("'{inner}'")
}

pub(super) fn escape_str(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            c => out.push(c),
        }
    }
    out
}
