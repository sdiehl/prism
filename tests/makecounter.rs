use std::path::Path;

fn manifest_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn run_example(name: &str) -> String {
    let src = std::fs::read_to_string(manifest_dir().join(format!("examples/{name}")))
        .unwrap();
    let full = prism::with_prelude(&src);
    let run = prism::interpret(&full).unwrap();
    run.term.trim().to_string()
}

// ---------------------------------------------------------------------------
// Doctests extracted from the research document
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct DocExample {
    origin: String,
    code: String,
    compile_fail: bool,
    ignore: bool,
}

/// Extract all ```prism fenced blocks from a markdown file.
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

fn run_doc_tests(path: &Path) {
    let examples = extract_doc_examples(path);
    assert!(!examples.is_empty(), "expected at least one doc example in {path:?}");

    let mut passed = 0usize;
    let mut failed: Vec<(String, String)> = Vec::new();
    let base = manifest_dir();

    for ex in &examples {
        if ex.ignore {
            continue;
        }
        let full = prism::with_prelude(&prism::example_program(&ex.code));
        let checked = prism::check_at(&full, base);

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
                        match prism::interpret_at(&full, base) {
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

/// Run all doc examples from the research document.
#[test]
fn test_doc_examples_09() {
    run_doc_tests(&manifest_dir().join("docs/research/ocapn-actors/03-makecounter-actor.md"));
}

// ---------------------------------------------------------------------------
// Standalone example tests
// ---------------------------------------------------------------------------

#[test]
fn test_makecounter() {
    let out = run_example("makecounter.pr");
    println!("--- makecounter output ---\n{out}");
    assert_eq!(out, "1\n2\n1", "expected incr→1, incr→2, decr→1");
}

#[test]
fn test_makecounter_pola() {
    let out = run_example("makecounter_pola.pr");
    println!("--- makecounter_pola output ---\n{out}");
    assert_eq!(out, "4\n4", "expected b=4, c=4 after incr×4 decr×1");
}

#[test]
fn test_makecounter_pure() {
    let out = run_example("makecounter_pure.pr");
    println!("--- makecounter_pure output ---\n{out}");
    assert_eq!(out, "1\n2\n1", "expected 1, 2, 1");
}


