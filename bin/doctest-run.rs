use std::env;
use std::fs;
use std::path::Path;
use std::process;

#[derive(Debug)]
struct DocExample {
    origin: String,
    code: String,
    compile_fail: bool,
    ignore: bool,
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run --bin doctest-run -- <markdown-file-path>");
        process::exit(1);
    }

    let file_path = Path::new(&args[1]);
    if !file_path.exists() {
        eprintln!("Error: File not found at {:?}", file_path);
        process::exit(1);
    }

    println!("Running doctests for: {}", file_path.display());
    let examples = extract_doc_examples(file_path);
    if examples.is_empty() {
        println!("No prism doctest blocks found.");
        process::exit(0);
    }

    let base_dir = file_path.parent().unwrap_or_else(|| Path::new("."));
    let mut passed = 0;
    let mut failed = Vec::new();

    for ex in &examples {
        if ex.ignore {
            println!("  [IGNORED] {}", ex.origin);
            continue;
        }

        let full = prism::with_prelude(&prism::example_program(&ex.code));
        let checked = prism::check_at(&full, base_dir);

        let outcome = if ex.compile_fail {
            match checked {
                Ok(_) => Err("expected compile error but it compiled".to_string()),
                Err(_) => Ok(()),
            }
        } else {
            match checked {
                Err(e) => Err(format!("compile error: {e}")),
                Ok(checked) => {
                    let has_main = checked.decls.iter().any(|d| d.name == "main");
                    if has_main {
                        match prism::interpret_at(&full, base_dir) {
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
                println!("  [PASS]    {}", ex.origin);
            }
            Err(msg) => {
                eprintln!("  [FAIL]    {}: {msg}", ex.origin);
                failed.push((ex.origin.clone(), msg));
            }
        }
    }

    println!(
        "\nResult: {} passed, {} failed, {} ignored",
        passed,
        failed.len(),
        examples.len() - passed - failed.len()
    );

    if !failed.is_empty() {
        eprintln!("\nFailures:");
        for (origin, msg) in failed {
            eprintln!("  - {}: {}", origin, msg);
        }
        process::exit(1);
    }

    println!("All doctests passed successfully!");
}

fn extract_doc_examples(path: &Path) -> Vec<DocExample> {
    let text = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("Error reading file: {e}");
        process::exit(1);
    });
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
