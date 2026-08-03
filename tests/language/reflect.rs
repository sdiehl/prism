// `reflect fn f` / `reflect type T`: a declaration quoting its own canonical
// rendering as a compile-time string.
//
// The properties the form rests on are checked here: the quotation is the
// formatter's rendering (canonical, and carrying the comment block written
// above its target rather than the author's whitespace), it reaches only
// declarations of the same file, and it survives a reformat unchanged. Its
// identity consequence, that a comment-only edit to a quoting file moves that
// file's semantic digest, is checked where the digest is computed.

use std::io::Write;
use std::process::{Command, Stdio};

// What a program prints, which for these is the splice's output as the rest of
// the language sees it: an ordinary string.
fn run(src: &str) -> String {
    prism::interpret(&prism::with_prelude(src)).unwrap().term
}

fn refused(src: &str) -> String {
    prism::check(&prism::with_prelude(src))
        .expect_err("must be refused")
        .to_string()
}

#[test]
fn a_quotation_renders_the_declaration_with_its_leading_comment() {
    let out = run("-- Twice its argument.\nfn double(x : Int) : Int = x * 2\n\
                   fn main() = print(reflect fn double)\n");
    assert_eq!(
        out,
        "-- Twice its argument.\nfn double(x : Int) : Int = x * 2"
    );
}

#[test]
fn a_quotation_renders_a_type_declaration_too() {
    let out = run("type Light = Red | Amber | Green\n\
                   fn main() = print(reflect type Light)\n");
    assert_eq!(out, "type Light = Red | Amber | Green");
}

// The rendering is the formatter's, not a slice of the file: two spellings of
// one declaration quote identically, so reformatting the target does not change
// what the program prints.
#[test]
fn two_spellings_of_one_declaration_quote_identically() {
    let tidy = run("fn double(x : Int) : Int = x * 2\nfn main() = print(reflect fn double)\n");
    let messy = run("fn double(x:Int):Int   =    x*2\nfn main() = print(reflect fn double)\n");
    assert_eq!(messy, tidy);
}

#[test]
fn a_quotation_of_a_declaration_the_file_lacks_is_refused() {
    let msg = refused("fn main() = print(reflect fn missing)\n");
    assert!(msg.contains("cannot reflect `fn missing`"), "{msg}");
}

// The keyword decides where to look, so a name that is only a `fn` answers no
// `type` quotation.
#[test]
fn a_quotation_looks_only_in_the_form_it_names() {
    let msg = refused("fn double(x : Int) : Int = x * 2\nfn main() = print(reflect type double)\n");
    assert!(msg.contains("cannot reflect `type double`"), "{msg}");
}

// The prelude is prepended to every program, but it is not the author's text: a
// quotation reaches the file it is written in and nothing else.
#[test]
fn a_prelude_declaration_is_not_quotable() {
    let msg = refused("fn main() = print(reflect fn map)\n");
    assert!(msg.contains("cannot reflect `fn map`"), "{msg}");
}

// Every entry that feeds a checker has to answer quotations, not only the one
// `run`/`build` takes: the documentation generator type-checks each module it
// documents, and a quotation left unanswered there is an internal error rather
// than a program. The one property is that the quoting file gets documented at
// all.
#[test]
fn the_documentation_generator_answers_a_quotation() {
    let module = prism::ModuleSource {
        dotted: "Quoting".to_string(),
        title: "Quoting".to_string(),
        source: "-- | Twice its argument.\npub fn double(x : Int) : Int = x * 2\n\n\
                 pub fn shown() : String = reflect fn double\n"
            .to_string(),
        source_path: "Quoting.pr".to_string(),
        is_prelude: false,
    };
    let roots = prism::default_roots(std::path::Path::new("."));
    let generated = prism::project_pages(vec![module], &roots, "Quoting").expect("must document");
    let page = generated
        .pages
        .iter()
        .find(|page| page.module == "Quoting")
        .expect("the quoting module has a page");
    assert!(page.markdown.contains("Twice its argument"), "{page:?}");
}

// The interactive shell has no file, so its unit is the session: a quotation
// typed at the prompt reaches what the session has loaded, through the same
// splice a declaration body goes through.
#[test]
fn a_prompt_expression_quotes_the_session() {
    let dir = std::env::temp_dir().join("prism-reflect-repl");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let file = dir.join("Twice.pr");
    std::fs::write(
        &file,
        "-- Twice its argument.\npub fn double(x : Int) : Int = x * 2\n",
    )
    .expect("write session file");

    let mut child = Command::new(env!("CARGO_BIN_EXE_prism"))
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn repl");
    write!(
        child.stdin.as_mut().expect("repl stdin"),
        ":load {}\nreflect fn double\n",
        file.display()
    )
    .expect("drive repl");
    let out = child.wait_with_output().expect("repl exits");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("-- Twice its argument."), "{text}");
}

#[test]
fn a_quotation_round_trips_through_the_formatter() {
    let src = "fn double(x : Int) : Int = x * 2\n\ntype Light = Red | Amber | Green\n\n\
               fn main() =\n  print(reflect fn double)\n  print(reflect type Light)\n";
    let once = prism::format(src).expect("must parse");
    assert!(once.contains("reflect fn double"), "{once}");
    assert!(once.contains("reflect type Light"), "{once}");
    assert_eq!(prism::format(&once).expect("must reparse"), once);
}
