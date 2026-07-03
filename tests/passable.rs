use std::path::Path;

#[test]
fn test_passable_compiles() {
    let src = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/Passable.pr"),
    )
    .unwrap();
    // with_prelude prepends the prelude, check type-checks the whole thing
    let _checked = prism::check(&prism::with_prelude(&src)).unwrap();
}

#[test]
fn test_10_doc_examples() {
    let doc_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("docs/research/ocapn-actors/01-passable-datatype.md");
    let examples = extract_doc_examples(&doc_path);
    assert!(!examples.is_empty(), "expected at least one doc example in {doc_path:?}");
    run_doc_tests(&examples);
}

// ---------------------------------------------------------------------------
// Doc example infrastructure (based on makecounter.rs)
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct DocExample {
    origin: String,
    code: String,
    compile_fail: bool,
    ignore: bool,
}

fn extract_doc_examples(path: &Path) -> Vec<DocExample> {
    let text = std::fs::read_to_string(path).unwrap();
    let mut out = Vec::new();
    let mut lines = text.lines();
    let mut line_no = 0;
    while let Some(line) = lines.next() {
        line_no += 1;
        let trimmed = line.trim_start();
        let Some(info) = trimmed.strip_prefix("```") else {
            continue;
        };
        let is_prism = info
            .split([',', ' '])
            .next()
            .map(|t| t.trim() == "prism")
            .unwrap_or(false);
        if !is_prism {
            continue;
        }
        let attrs: Vec<&str> = info.split([',', ' ']).map(str::trim).collect();
        let ignore = attrs.contains(&"ignore");
        let compile_fail = attrs.contains(&"compile_fail");
        let mut code = String::new();
        for body in lines.by_ref() {
            line_no += 1;
            if body.trim_start().starts_with("```") {
                break;
            }
            code.push_str(body);
            code.push('\n');
        }
        out.push(DocExample {
            origin: format!("{}:{}", path.file_name().unwrap().to_string_lossy(), line_no),
            code,
            compile_fail,
            ignore,
        });
    }
    out
}

fn run_doc_tests(examples: &[DocExample]) {
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut passed = 0usize;
    let mut failed: Vec<(String, String)> = Vec::new();

    for ex in examples {
        if ex.ignore {
            continue;
        }
        let full = prism::with_prelude(&prism::example_program(&ex.code));
        let checked = prism::check_at(&full, &base);

        let outcome = if ex.compile_fail {
            match checked {
                Ok(_) => Err("expected compile error but it compiled".into()),
                Err(_) => Ok(()),
            }
        } else {
            match checked {
                Err(e) => Err(format!("compile error: {e}")),
                Ok(checked) => {
                    let has_main = checked.decls.iter().any(|d| d.name == "main");
                    if has_main {
                        match prism::interpret_at(&full, &base) {
                            Ok(_) => Ok(()),
                            Err(e) => Err(format!("run error: {e}")),
                        }
                    } else {
                        Ok(())
                    }
                }
            }
        };

        match outcome {
            Ok(()) => {
                passed += 1;
                println!("  PASS: {}", ex.origin);
            }
            Err(msg) => {
                eprintln!("  FAIL: {}: {msg}", ex.origin);
                failed.push((ex.origin.clone(), msg));
            }
        }
    }

    let total = examples.len();
    let ignored = total - passed - failed.len();
    println!("\ndoc test result: {passed} passed; {failed_len} failed; {ignored} ignored; 0 measured",
        failed_len = failed.len());
    assert!(
        failed.is_empty(),
        "{failed_count} doc example(s) failed:\n{failures}",
        failed_count = failed.len(),
        failures = failed
            .iter()
            .map(|(o, m)| format!("  {o}: {m}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
