# Typechecker Model Scaffold

This directory is a Prism typechecker-proof scaffold. The concrete layer is proved today: canonical row normalization (sorted multiset form, membership, tail preservation), kind soundness of the algorithmic checker, and preservation plus idempotence of substitution. The algorithmic layer (unification, expression inference) and the Rust boundary are still stubs, so their soundness theorems hold vacuously or by assumed placeholder, each marked in place; implementing a stub resurfaces the real obligation by breaking its proof.

The files sketch what the full mechanization COULD look like. But it's a bloody hard problem to do.

Treat this as a map for someone (an ambitious student perhaps) who wants to do the full thing. This is what it would look like.
