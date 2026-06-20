fn main() {
    let src = "fn fact(n) = if n == 0 then 1 else n * fact(n - 1)\n\
               fn main() = let r = fact(5) in let u = print(r) in r\n";
    print!("{}", tiny_prism::report(src));
}
