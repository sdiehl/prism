// Statics: PFPL-style judgement declarations first, then rules.
// Included from semantics.typ. Prose is minimal; XXX marks unwritten parts.

#import "@preview/curryst:0.5.1": rule, prooftree

#let judgment-table(rows) = table(
  columns: (0.32fr, 0.68fr),
  inset: 6pt,
  stroke: (x: none, y: 0.35pt + rgb("d1d5db")),
  align: (left, left),
  table.header([*Judgement*], [*Meaning*]),
  ..rows.flatten(),
)

#let todo(body) = block(
  fill: luma(246),
  stroke: (left: 2pt + luma(110)),
  inset: 7pt,
  width: 100%,
  [#text(weight: "bold")[XXX ] #body],
)

#let rules(..args) = align(center, args.pos().map(prooftree).join(h(2.2em)))

= Statics

This section is a rough sketch. The plan is to formalize all of it in Lean
later; what follows is the pseudocode form, written loosely and subject to
change.

Value types $A, B$, computation types $X$, effect rows $epsilon$ over operation
names $ell$. Typing hypotheses are $Gamma ::= dot | Gamma, x : A$; $Sigma$
assigns each operation its signature and $Phi$ each top-level function its type.

#todo[the dynamics sections use $Gamma$ for the program table; reconcile
$Gamma$ (hypotheses) and $Phi$ (function typings) with it when type safety is
stated.]

== Types and rows

$
  A, B ::= "Int" | "Float64" | "Bool" | "Unit" | "String"
         | T(overline(A)) | (overline(A)) | "U"(X)
$
$
  X ::= A ! epsilon | (overline(A)) -> X
  quad quad quad
  epsilon ::= chevron.l chevron.r | rho | chevron.l ell | epsilon chevron.r
$

$"U"(X)$ types a thunk. Rows are unordered sets of distinct labels, optionally
open in a row variable $rho$; $chevron.l overline(ell) | epsilon chevron.r$
abbreviates iterated extension.

#todo[surface-level polymorphism: $forall$, schemes, the kind context $Delta$,
and the $"Row"$ and $"Nat"$ kinds. The Core typed here is monomorphic.]

== Judgement forms

#judgment-table((
  ([$tack epsilon "row"$], [row formation: the labels of $epsilon$ are distinct]),
  ([$epsilon tilde.equiv epsilon'$], [row equivalence: identification up to label order]),
  ([$Gamma tack v : A$], [value typing]),
  ([$Gamma tack c : X$], [computation typing]),
  ([$Sigma(ell) = (overline(A)) -> A$], [operation signature lookup]),
  ([$Phi(f) = (overline(A)) -> X$], [top-level function type lookup]),
))

All typing judgements are implicitly closed under $tilde.equiv$.

== Row formation and equivalence

#rules(
  rule(name: smallcaps("wf-emp"), $tack chevron.l chevron.r "row"$),
  rule(name: smallcaps("wf-var"), $tack rho "row"$),
  rule(name: smallcaps("wf-head"),
    $tack chevron.l ell | epsilon chevron.r "row"$,
    $tack epsilon "row"$, $ell in.not "labels"(epsilon)$),
)

#v(0.4em)

#rules(
  rule(name: smallcaps("eq-swap"),
    $chevron.l ell_1 | chevron.l ell_2 | epsilon chevron.r chevron.r tilde.equiv
     chevron.l ell_2 | chevron.l ell_1 | epsilon chevron.r chevron.r$,
    $ell_1 eq.not ell_2$),
  rule(name: smallcaps("eq-head"),
    $chevron.l ell | epsilon_1 chevron.r tilde.equiv chevron.l ell | epsilon_2 chevron.r$,
    $epsilon_1 tilde.equiv epsilon_2$),
)

together with reflexivity, symmetry, and transitivity. No row is equivalent to
one containing itself; the unification occurs check enforces this.

#todo[row unification: unify-empty, unify-var with occurs check, head hoisting
on closed and open rows, fresh-tail side condition.]

== Value typing

#rules(
  rule(name: smallcaps("var"), $Gamma tack x : A$, $x : A in Gamma$),
  rule(name: smallcaps("int"), $Gamma tack n : "Int"$),
  rule(name: smallcaps("unit"), $Gamma tack () : "Unit"$),
)

#v(0.4em)

#rules(
  rule(name: smallcaps("tup"),
    $Gamma tack (overline(v)) : (overline(A))$,
    $Gamma tack v_i : A_i quad (forall i)$),
  rule(name: smallcaps("thunk"),
    $Gamma tack "thunk" med c : "U"(X)$,
    $Gamma tack c : X$),
)

#todo[remaining literals ($d$, $b$, $s$) and constructor values $K_i
(overline(v))$, which need the datatype signature and its field/arity lookup.]

== Computation typing

A value is pure: $"return"$ types at any well-formed row.

#rules(
  rule(name: smallcaps("ret"),
    $Gamma tack "return" v : A ! epsilon$,
    $Gamma tack v : A$),
  rule(name: smallcaps("seq"),
    $Gamma tack c_1 "to" x. c_2 : B ! epsilon$,
    $Gamma tack c_1 : A ! epsilon$,
    $Gamma, x : A tack c_2 : B ! epsilon$),
)

#v(0.4em)

#rules(
  rule(name: smallcaps("force"),
    $Gamma tack "force" v : X$,
    $Gamma tack v : "U"(X)$),
  rule(name: smallcaps("lam"),
    $Gamma tack lambda overline(x). c : (overline(A)) -> X$,
    $Gamma, overline(x : A) tack c : X$),
)

#v(0.4em)

#rules(
  rule(name: smallcaps("app"),
    $Gamma tack c(overline(v)) : X$,
    $Gamma tack c : (overline(A)) -> X$,
    $Gamma tack v_i : A_i quad (forall i)$),
  rule(name: smallcaps("if"),
    $Gamma tack "if" v "then" c_1 "else" c_2 : X$,
    $Gamma tack v : "Bool"$,
    $Gamma tack c_1 : X$,
    $Gamma tack c_2 : X$),
)

#v(0.4em)

#rules(
  rule(name: smallcaps("call"),
    $Gamma tack f(overline(v)) : X$,
    $Phi(f) = (overline(A)) -> X$,
    $Gamma tack v_i : A_i quad (forall i)$),
  rule(name: smallcaps("do"),
    $Gamma tack "do" med ell(overline(v)) : A ! chevron.l ell | epsilon chevron.r$,
    $Sigma(ell) = (overline(A)) -> A$,
    $Gamma tack v_i : A_i quad (forall i)$),
)

#v(0.4em)

Handling subtracts the handled labels; masking adds them back. Below,
$overline(h) = overline(ell_i (overline(x_i), k) => c_i)$ and the resumption is
typed as a thunked function from the operation's result into the handler's
answer.

#rules(
  rule(name: smallcaps("handle"),
    $Gamma tack "handle" c "with" \{ c_r; overline(h) \} : B ! epsilon$,
    $Gamma tack c : A ! chevron.l overline(ell) | epsilon chevron.r$,
    $Gamma, x : A tack c_r : B ! epsilon$,
    $Gamma, overline(x_i : A_i), k : "U"((A'_i) -> B ! epsilon) tack c_i : B ! epsilon quad (forall i)$),
)

#v(0.4em)

#rules(
  rule(name: smallcaps("mask"),
    $Gamma tack "mask" overline(ell) "in" c : A ! chevron.l overline(ell) | epsilon chevron.r$,
    $Gamma tack c : A ! epsilon$),
)

where in #smallcaps("handle") each $Sigma(ell_i) = (overline(A_i)) -> A'_i$.

#todo[$"case"$ (pattern typing $p : A => Gamma'$ and exhaustiveness),
$delta_(op)$ and $"neg"_lambda$ lane signatures, $"builtin"_a$ signatures,
$"error"$, and the RC instrumentation ($"dup"$, $"drop"$, $"with-reuse"$,
$"reuse"$), which types transparently but carries the linear token discipline.]

== Grades, a coeffect sketch

$
  g ::= "never" | "once" | "many"
  quad quad
  "never" < "once" < "many"
$

A grade is a coeffect on the resumption binding: it bounds how a clause may use
$k$, with $"never"$ meaning $k$ is unused, $"once"$ exactly one use in tail
position, and $"many"$ unrestricted. An operation declares a grade,
$Sigma(ell) = (overline(A)) ->^g A$, and a clause may use $k$ at any grade at
or below it:

#rules(
  rule(name: smallcaps("grade"),
    $Gamma, overline(x : A), k :_g' "U"((A') -> B ! epsilon) tack c : B ! epsilon$,
    $Sigma(ell) = (overline(A)) ->^g A'$,
    $g' lt.eq g$),
)

#todo[the counting judgement behind $k :_g'$: usage intervals $"never" = [0,0]$,
$"once" = [1,1]$ in tail position, $"many" = [0,infinity)$, and its structural
rules. The #smallcaps("handle") rule above types every resumption as multishot,
matching the runtime; the graded refinement replaces its $k$ premise.]

#todo[surface statics lowering into this Core: bidirectional higher-rank
inference, generalization over type and row variables, defaulting, rigid
annotated rows, row skolem escape, and the usage-fact ($@$) boundary
judgements.]
