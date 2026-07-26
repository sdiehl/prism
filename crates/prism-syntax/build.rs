fn main() {
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .process()
        .expect("lalrpop grammar generation");
    println!("cargo:rerun-if-changed=src/grammar.lalrpop");
}
