# Prism Lean Model

This is the Lean 4 model of Prism Core. It is a small, executable account of the language fragment the compiler lowers into. Rust and Lean meet at the Core representation. Rust emits Core, and Lean defines the CEK interpreter, replay semantics, effect-stack facts, and certificate checks for that fragment.

The same Core artifacts the compiler produces are fed to the Lean oracle, and the native LLVM codegen path is checked against the Lean CEK result across the standard library and fixtures. The proofs fix the machine semantics; the differential path keeps the implementation honest at the boundary where Rust hands execution to Core.

The `models/Tc` tree is only a scaffold for a future typechecker proof. It does not prove Prism's typechecker sound today. The files show the shape of a possible mechanization, but the real proof work is still open and large enough that it should not be cited as a completed guarantee.

Run the formal model with `lake build`.
