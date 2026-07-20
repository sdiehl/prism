#import "@preview/curryst:0.5.1": rule, prooftree

#set document(title: "Prism Semantics")
#set page(
  paper: "a4",
  margin: (x: 24mm, y: 22mm),
  numbering: "1",
)
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.")
#show heading.where(level: 1): set text(size: 15pt, weight: "bold")
#show heading.where(level: 2): set text(size: 12pt, weight: "bold")
#show table.cell: set text(size: 9.3pt)

#let syntax-row(lhs, rhs, meaning) = (
  lhs,
  rhs,
  meaning,
)

#let meaning-table(rows) = table(
  columns: (0.18fr, 0.43fr, 0.39fr),
  inset: 6pt,
  stroke: (x: none, y: 0.35pt + rgb("d1d5db")),
  align: (left, left, left),
  table.header(
    [*Family*],
    [*Notation*],
    [*Meaning*],
  ),
  ..rows.flatten(),
)

#grid(
  columns: (30mm, 1fr),
  gutter: 7mm,
  align: (center + horizon, left + horizon),
  image("/assets/prism.png", width: 27mm),
  [
    #text(size: 20pt, weight: "bold")[Prism Semantics]
    #v(0.35em)
    #text(size: 10.5pt, style: "italic", fill: rgb("4b5563"))[Unverified sketch]
  ],
)

#v(0.45em)
#rect(width: 100%, height: 2pt, fill: gradient.linear(
  rgb("8b5cf6"), rgb("22d3ee"), rgb("facc15"), angle: 90deg,
))
#v(0.8em)

= Conventions

Sequences are written with an overbar, as in $overline(v)$, and may be empty.
Comma-separated extension is left-biased: the newest binding shadows an older
binding with the same name. Square brackets denote syntactic substitution;
angle brackets denote machine configurations. A superscript star on a relation
denotes reflexive-transitive closure.

#meaning-table((
  syntax-row([$x, y, z$], [$in "Var"$], [term variables]),
  syntax-row([$f$], [$in "FnName"$], [top-level Core function names]),
  syntax-row([$K$], [$in "CtorName"$], [data-constructor names]),
  syntax-row([$ell$], [$in "OpName"$], [effect-operation names]),
  syntax-row([$n, i$], [$in bb(Z), in bb(N)$], [integer literals and natural tags]),
  syntax-row([$d$], [$in "Float64"$], [IEEE-754 binary64 literals]),
  syntax-row([$b, s$], [$in bb(B), in "String"$], [booleans and strings]),
  syntax-row([$overline(a)$], [$in "List"(a)$], [a finite sequence of objects of family $a$]),
))

= Static Core terms

The calculus is in computation-passing form: syntactic values $v$ are inert,
while computations $c$ describe evaluation. Patterns $p$ occur only in case
arms. Handler clauses $h$ bind operation parameters and a resumption variable.

== Patterns

$
  p ::= _
      | x
      | n
      | d
      | b
      | K(overline(p))
      | (overline(p))
      | K \{ overline(x : p) \}_omega
$

The subscript $omega in {"open", "closed"}$ records whether a record pattern
admits fields not explicitly listed. Pattern matching produces a finite binding
environment when it succeeds.

== Values

$
  v ::= x
      | n
      | d
      | b
      | ()
      | s
      | "thunk"\ c
      | K_i(overline(v))
      | (overline(v))
$

$K_i$ pairs a constructor name with its natural-number runtime tag. A thunk is
syntax here; it becomes a closure over an environment when converted to a
runtime value.

#pagebreak(weak: true)

== Handler clauses and computations

$
  h ::= ell(overline(x), k) => c
$

Here $k$ is the variable bound to the captured, multishot resumption.

#align(center)[
  #text(size: 10.5pt)[
    #grid(
      columns: (auto, auto),
      column-gutter: 0.55em,
      row-gutter: 0.32em,
      align: (right, left),
      [$c ::= $], [$"return" v | c "to" x. c$],
      [], [$| "force" v | lambda overline(x). c$],
      [], [$| c(overline(v))$],
      [], [$| "if" v "then" c "else" c$],
      [], [$| delta_(op) (v_1, v_2) | "neg"_lambda(v)$],
      [], [$| f(overline(v)) | "case" v "of" overline(p => c)$],
      [], [$| "do" ell(overline(v))$],
      [], [$| "handle" c "with" \{ c_r; overline(h) \}$],
      [], [$| "mask" overline(ell) "in" c | "builtin"_a(overline(v))$],
      [], [$| "dup" v | "drop" v$],
      [], [$| "with-reuse" t = v "in" c | "reuse" t "as" v$],
      [], [$| "error" v$],
    )
  ]
]

$op$ ranges over the integer, boolean, and floating primitive operations;
$lambda in {"Int", "I64", "Float64"}$ is a negation lane. The metavariable $a$
names an opaque runtime builtin. The optional return clause $c_r$ binds the
handled computation's ordinary result. Print, string, float, and input nodes are
included in the $"builtin"_a$ family in this presentation; the Lean syntax keeps
their constructors separate.

== Programs

$
  F ::= f(overline(x)) = c
  quad
  Gamma ::= \{ overline(F) \}
$

$Gamma$ is a closed Core program: a finite table of named functions. Function
lookup is written $Gamma(f)$ and is partial.

= Runtime terms

Runtime values are distinct from syntactic values because closures, thunks, and
resumptions carry dynamic context.

$
  r ::= n
      | d
      | b
      | ()
      | s
      | "closure"(overline(x), c, rho)
      | "thunk"(c, rho)
      | K_i(overline(r))
      | (overline(r))
      | "resume"(kappa)
$

$
  rho ::= emptyset | rho[x mapsto r]
$

$rho$ is a left-biased runtime environment. Lookup is $rho(x)$, and simultaneous
extension is $rho[overline(x mapsto r)]$.

== Continuation machine

$
  phi ::= "bind"(x, c, rho)
       | "args"(overline(v), rho)
       | "handler"(overline(h), c_r, rho)
       | "mask"(overline(ell))
$

$
  kappa ::= epsilon | phi :: kappa
  quad
  mu ::= "eval"(c, rho) | "ret"(r)
  quad
  q ::= chevron.l mu, kappa chevron.r
$

$phi$ is one continuation frame, $kappa$ a stack of frames, $mu$ the CEK control
state, and $q$ a complete machine configuration. The initial configuration for
a closed computation is

$
  "load"(c) = chevron.l "eval"(c, emptyset), epsilon chevron.r.
$

= Auxiliary notation

#meaning-table((
  syntax-row([$c[v slash x]$], [capture-avoiding substitution], [replace free $x$ in $c$ by syntactic value $v$]),
  syntax-row([$c[overline(v slash x)]$], [simultaneous substitution], [apply a finite parameter-to-argument binding]),
  syntax-row([$delta (op, r_1, r_2) = r$], [primitive interpretation], [evaluate a binary primitive when its lane and operands are valid]),
  syntax-row([$"neg"(lambda, r) = r'$], [unary primitive interpretation], [evaluate lane-specific numeric negation]),
  syntax-row([$p "matches" r = theta$], [pattern matching], [match $p$ against $r$ and return bindings $theta$]),
  syntax-row([$rho tack v arrow.b.double r$], [atomic value evaluation], [resolve a syntactic value in $rho$, closing thunks over $rho$]),
  syntax-row([$Gamma(f) = (overline(x), c)$], [function lookup], [find $f$'s parameters and body in the Core table]),
  syntax-row([$H(ell) = (overline(x), k, c)$], [handler-clause lookup], [find the clause for operation $ell$ in handler $H$]),
  syntax-row([$"find"(ell, overline(r), j, kappa)$], [handler search], [find the nearest matching handler after skipping $j$ masked matches]),
))

All of these operations are partial. An undefined result is written $bot$.
This notation does not identify machine failure with semantic divergence:
halting, an explicit error, and a stuck configuration will be distinguished when
the dynamic rules are written.

= Reserved judgement forms

The following declarations fix how later rules will be read. They do not yet
define when any judgement is derivable.

#meaning-table((
  syntax-row([$Gamma tack c arrow.r c'$], [Core one-step reduction], [$c$ reduces to $c'$ under program $Gamma$]),
  syntax-row([$Gamma tack c arrow.r^* c'$], [Core many-step reduction], [reflexive-transitive closure of Core reduction]),
  syntax-row([$Gamma tack q mapsto q'$], [CEK transition], [configuration $q$ takes one machine step to $q'$]),
  syntax-row([$Gamma tack q mapsto^* q'$], [CEK run], [zero or more CEK transitions]),
  syntax-row([$Gamma; rho tack c arrow.b.double r$], [natural evaluation], [$c$ evaluates to runtime value $r$ in $rho$]),
  syntax-row([$"terminal"_Gamma(c)$], [terminal computation], [$c$ is a Core result or function]),
  syntax-row([$"stuck"_Gamma(c)$], [explicitly blocked computation], [$c$ is nonterminal and has no Core successor]),
  syntax-row([$"handles"(ell, j, kappa)$], [handler coverage], [$kappa$ handles $ell$ after $j$ matching handlers are skipped]),
  syntax-row([$"tunnels"(ell, kappa)$], [transparent stack segment], [$kappa$ contains no frame that traps or masks $ell$]),
))
