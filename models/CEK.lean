import Prism

/-
An environment-based CEK abstract machine for the Prism core, mirroring the
reference interpreter in `src/eval/mod.rs` (the differential-testing "oracle").
Where `Prism.lean` gives a substitution small-step `Step`, this file gives the
machine the compiler actually runs: explicit runtime values `Rv` carrying
closures/thunks over an environment, a continuation `Stack` of `Frame`s, and a
deterministic transition `step` transcribing the Rust `step`/`cont`/`perform`.

The machine is a *function* `step : Core -> Conf -> Option Conf` (`none` = halt or
stuck), so it is deterministic by construction and executable: `run` reduces a
closed program and `Sanity.lean` checks concrete oracle runs by `rfl`. Effects
(`doOp`/`handle`/`mask`) are modeled faithfully, including the Koka-style mask
skip count and deep (handler-included) continuation capture that makes `resume`
multishot. Pure I/O (`print`/`readInt`/builtins) erases to a value, matching the
model's stance that effects are lowered away before this core runs.
-/
namespace Prism

mutual

inductive Rv where
  | int (n : Int)
  | float (f : Float)
  | bool (b : Bool)
  | unit
  | str (s : String)
  | closure (ps : List String) (body : Comp) (env : List (String × Rv))
  | thunk (c : Comp) (env : List (String × Rv))
  | data (name : String) (tag : Nat) (args : List Rv)
  | tuple (args : List Rv)
  | resume (frames : List Frame)

inductive Frame where
  | bind (x : String) (n : Comp) (env : List (String × Rv))
  | args (as : List Value) (env : List (String × Rv))
  | handle (ops : List HandleOp) (retVar : Option String) (retBody : Option Comp) (env : List (String × Rv))
  | mask (ops : List String)

end

abbrev Env := List (String × Rv)

abbrev Stack := List Frame

inductive MState where
  | eval (c : Comp) (env : Env)
  | ret (v : Rv)

abbrev Conf := MState × Stack

def envLookup : Env → String → Option Rv
  | [], _ => none
  | (y, w) :: rest, x => if x = y then some w else envLookup rest x

/-- Mirrors `atom` in `src/eval/mod.rs`: resolve a syntactic value against the
    environment into a runtime value. Thunks close over the current environment. -/
def atomEval (env : Env) : Value → Option Rv
  | .var x => envLookup env x
  | .int n => some (.int n)
  | .float f => some (.float f)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | .str s => some (.str s)
  | .thunk c => some (.thunk c env)
  | .ctor n t args => (atomEvalL env args).map (.data n t)
  | .tuple args => (atomEvalL env args).map .tuple
where
  atomEvalL (env : Env) : List Value → Option (List Rv)
    | [] => some []
    | v :: vs => match atomEval env v, atomEvalL env vs with
      | some w, some ws => some (w :: ws)
      | _, _ => none

/-- `delta` on runtime values: the integer/boolean fragment of `Prism.delta`,
    plus the float arithmetic and comparisons the executable machine evaluates
    (the substitution `delta` leaves floats abstract; the machine does not). -/

def deltaR : BinOp → Rv → Rv → Option Rv
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int _, .int 0 => none
  | .rem, .int _, .int 0 => none
  | .div, .int a, .int b => some (.int (a / b))
  | .rem, .int a, .int b => some (.int (a % b))
  | .eq, .int a, .int b => some (.bool (a == b))
  | .ne, .int a, .int b => some (.bool (a != b))
  | .lt, .int a, .int b => some (.bool (a < b))
  | .le, .int a, .int b => some (.bool (a ≤ b))
  | .gt, .int a, .int b => some (.bool (a > b))
  | .ge, .int a, .int b => some (.bool (a ≥ b))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or, .bool a, .bool b => some (.bool (a || b))
  | .addf, .float a, .float b => some (.float (a + b))
  | .subf, .float a, .float b => some (.float (a - b))
  | .mulf, .float a, .float b => some (.float (a * b))
  | .divf, .float a, .float b => some (.float (a / b))
  | .eqf, .float a, .float b => some (.bool (a == b))
  | .nef, .float a, .float b => some (.bool (a != b))
  | .ltf, .float a, .float b => some (.bool (a < b))
  | .lef, .float a, .float b => some (.bool (a ≤ b))
  | .gtf, .float a, .float b => some (.bool (a > b))
  | .gef, .float a, .float b => some (.bool (a ≥ b))
  | _, _, _ => none

/-- Pattern match against a runtime value, mirroring `match_pat`. -/
def matchPatR : Pat → Rv → Option (List (String × Rv))
  | .wild, _ => some []
  | .var x, v => some [(x, v)]
  | .int n, .int m => if n = m then some [] else none
  | .bool b, .bool c => if b = c then some [] else none
  | .ctor name args, .data name' _ vs => if name = name' then matchPatRL args vs else none
  | .tuple args, .tuple vs => matchPatRL args vs
  | _, _ => none
where
  matchPatRL : List Pat → List Rv → Option (List (String × Rv))
    | [], [] => some []
    | p :: ps, v :: vs =>
        match matchPatR p v, matchPatRL ps vs with
        | some b1, some b2 => some (b1 ++ b2)
        | _, _ => none
    | _, _ => none

def matchArmsR (scrut : Rv) : List (Pat × Comp) → Option (Comp × List (String × Rv))
  | [] => none
  | (p, c) :: rest =>
    match matchPatR p scrut with
      | some binds => some (c, binds)
      | none => matchArmsR scrut rest

/-- Look up the handler clause for `op` in a handler's op list. -/
def handlerFor (op : String) : List HandleOp → Option (List String × String × Comp)
  | [] => none
  | .mk name ps r b :: rest => if op = name then some (ps, r, b) else handlerFor op rest

def opNames : List HandleOp → List String
  | [] => []
  | .mk name _ _ _ :: rest => name :: opNames rest

/-- Bind a parameter list to argument values, prepended onto an environment
    (front-of-list wins, so this is the machine's `insert`). -/
def extendEnv : List String → List Rv → Env → Env
  | x :: xs, w :: ws, env => (x, w) :: extendEnv xs ws env
  | _, _, env => env

/-- Walk the stack to the nearest handler for `op` not shadowed by a matching
    mask, capturing the crossed frames (handler included: deep semantics). The
    captured slice becomes a `resume` value, reversed so replay order matches. -/
def findHandler (op : String) (argvs : List Rv) : Nat → List Frame → Stack → Option Conf
  | _, _, [] => none
  | skip, captured, fr :: rest =>
    match fr with
      | .args _ _ => findHandler op argvs skip captured rest
      | .mask ops =>
        let skip' := if ops.contains op then skip + 1 else skip
        findHandler op argvs skip' (.mask ops :: captured) rest
      | .handle ops rv rb henv =>
        match handlerFor op ops with
          | some (ps, resumeVar, body) => if skip > 0 then
            findHandler op argvs (skip - 1) (.handle ops rv rb henv :: captured) rest
          else
            let captured' := (.handle ops rv rb henv :: captured).reverse
            let env2 := extendEnv ps argvs ((resumeVar, .resume captured') :: henv)
            some (.eval body env2, rest)
          | none => findHandler op argvs skip (.handle ops rv rb henv :: captured) rest
      | .bind x n env => findHandler op argvs skip (.bind x n env :: captured) rest

/-- One transition of the machine, transcribing `step`/`cont`/`perform`.
    `none` means a halted (`ret` on empty stack) or stuck/error configuration. -/
def step (Γ : Core) : Conf → Option Conf
  | (.eval c env, stk) =>
    match c with
      | .ret v => (atomEval env v).map (fun w => (.ret w, stk))
      | .bind m x n => some (.eval m env, .bind x n env :: stk)
      | .force v =>
        match atomEval env v with
          | some (.thunk c e) => some (.eval c e, stk)
          | some other => some (.ret other, stk)
          | none => none
      | .lam xs body => some (.ret (.closure xs body env), stk)
      | .app f args => some (.eval f env, .args args env :: stk)
      | .ite cnd t e =>
        match atomEval env cnd with
          | some (.bool true) => some (.eval t env, stk)
          | some (.bool false) => some (.eval e env, stk)
          | _ => none
      | .prim op a b =>
        match atomEval env a, atomEval env b with
          | some av, some bv => (deltaR op av bv).map (fun w => (.ret w, stk))
          | _, _ => none
      | .call name args =>
        match lookupFn Γ name, atomEval.atomEvalL env args with
          | some f, some avs => if avs.length < f.params.length then some (.ret (.closure (f.params.drop avs.length) f.body (extendEnv f.params avs [])), stk) else some (.eval f.body (extendEnv f.params avs []), stk)
          | _, _ => none
      | .case scrut arms =>
        match atomEval env scrut with
          | some sv =>
            match matchArmsR sv arms with
              | some (body, binds) => some (.eval body (binds ++ env), stk)
              | none => none
          | none => none
      | .doOp op args =>
        match atomEval.atomEvalL env args with
          | some avs => findHandler op avs 0 [] stk
          | none => none
      | .handle body rv rb ops => some (.eval body env, .handle ops rv rb env :: stk)
      | .mask ops body => some (.eval body env, .mask ops :: stk)
      | .withReuse tok _ body => some (.eval body ((tok, .unit) :: env), stk)
      | .reuse _ v => (atomEval env v).map (fun w => (.ret w, stk))
      | .dup _ => some (.ret .unit, stk)
      | .drop _ => some (.ret .unit, stk)
      -- I/O and builtins erase to a value (effects are lowered before this core).
      | .print _ => some (.ret .unit, stk)
      | .printf _ => some (.ret .unit, stk)
      | .prints _ => some (.ret .unit, stk)
      | .readInt => some (.ret (.int 0), stk)
      | .floatBuiltin _ _ => some (.ret .unit, stk)
      | .strBuiltin _ _ => some (.ret .unit, stk)
      | .err _ => none
  | (.ret w, stk) =>
    match stk with
      | [] => none
      | fr :: rest =>
        match fr with
          | .bind x n env => some (.eval n ((x, w) :: env), rest)
          | .mask _ => some (.ret w, rest)
          | .handle _ rv rb env =>
            match rv, rb with
              | some r, some body => some (.eval body ((r, w) :: env), rest)
              | _, _ => some (.ret w, rest)
          | .args args env =>
            match atomEval.atomEvalL env args with
              | some avs =>
                match w with
                  | .closure ps body cenv => if avs.length < ps.length then some (.ret (.closure (ps.drop avs.length) body (extendEnv ps avs cenv)), rest) else some (.eval body (extendEnv ps avs cenv), rest)
                  | .resume frames =>
                    match avs with
                      | a :: _ => some (.ret a, frames ++ rest)
                      | [] => none
                  | _ => none
              | none => none

/-- Iterate the machine for at most `fuel` steps, stopping when it halts. -/
def run : Nat → Core → Conf → Conf
  | 0, _, c => c
  | n + 1, Γ, c =>
    match step Γ c with
      | some c' => run n Γ c'
      | none => c

/-- Load a closed computation into an initial configuration. -/
def load (c : Comp) : Conf := (.eval c [], [])

/-- The machine transition as a relation. Since `step` is a function, this is
    deterministic by construction (the oracle has at most one next state). -/
def MStep (Γ : Core) (a b : Conf) : Prop := step Γ a = some b

theorem MStep.deterministic {Γ : Core} {a b c : Conf} (h1 : MStep Γ a b) (h2 : MStep Γ a c) : b = c :=
  by
    unfold MStep at h1 h2
    rw [h1] at h2
    exact Option.some.inj h2

/-- Reflexive-transitive closure of the machine transition: a full run. -/
inductive Runs (Γ : Core) : Conf → Conf → Prop where
  | refl : Runs Γ a a
  | step : step Γ a = some b → Runs Γ b c → Runs Γ a c

theorem Runs.trans {Γ : Core} {a b c : Conf} (hab : Runs Γ a b) (hbc : Runs Γ b c) : Runs Γ a c :=
  by induction hab with
      | refl => exact hbc
      | step hs _ ih => exact Runs.step hs (ih hbc)

/--
Big-step environment natural semantics for the effect-free core, the
specification the CEK machine must implement. `BEval Γ env c w` reads "in
environment `env`, computation `c` evaluates to runtime value `w`". The rules
mirror the recursive intent of `src/eval/mod.rs` directly (no continuation
stack), so they double as a readable denotation of the oracle.
-/
inductive BEval (Γ : Core) : Env → Comp → Rv → Prop where
  | ret : atomEval env v = some w → BEval Γ env (.ret v) w
  | bind : BEval Γ env m wm → BEval Γ ((x, wm) :: env) n w → BEval Γ env (.bind m x n) w
  | forceThunk : atomEval env v = some (.thunk c e) → BEval Γ e c w → BEval Γ env (.force v) w
  | forceVal : atomEval env v = some w → (∀ c e, w ≠ .thunk c e) → BEval Γ env (.force v) w
  | lam : BEval Γ env (.lam xs body) (.closure xs body env)
  | appFull : BEval Γ env f (.closure ps body cenv) → atomEval.atomEvalL env args = some avs → ¬avs.length < ps.length → BEval Γ (extendEnv ps avs cenv) body w → BEval Γ env (.app f args) w
  | appPart : BEval Γ env f (.closure ps body cenv) → atomEval.atomEvalL env args = some avs → avs.length < ps.length → BEval Γ env (.app f args) (.closure (ps.drop avs.length) body (extendEnv ps avs cenv))
  | iteT : atomEval env cnd = some (.bool true) → BEval Γ env t w → BEval Γ env (.ite cnd t e) w
  | iteF : atomEval env cnd = some (.bool false) → BEval Γ env e w → BEval Γ env (.ite cnd t e) w
  | prim : atomEval env a = some av → atomEval env b = some bv → deltaR op av bv = some w → BEval Γ env (.prim op a b) w
  | callFull : lookupFn Γ name = some f → atomEval.atomEvalL env args = some avs → ¬avs.length < f.params.length → BEval Γ (extendEnv f.params avs []) f.body w → BEval Γ env (.call name args) w
  | callPart : lookupFn Γ name = some f → atomEval.atomEvalL env args = some avs → avs.length < f.params.length → BEval Γ env (.call name args) (.closure (f.params.drop avs.length) f.body (extendEnv f.params avs []))
  | case : atomEval env scrut = some sv → matchArmsR sv arms = some (body, binds) → BEval Γ (binds ++ env) body w → BEval Γ env (.case scrut arms) w
  | withReuse : BEval Γ ((tok, .unit) :: env) body w → BEval Γ env (.withReuse tok freed body) w
  | reuse : atomEval env v = some w → BEval Γ env (.reuse tok v) w
  | dup : BEval Γ env (.dup v) .unit
  | drop : BEval Γ env (.drop v) .unit
  | print : BEval Γ env (.print v) .unit
  | printf : BEval Γ env (.printf v) .unit
  | prints : BEval Γ env (.prints v) .unit
  | readInt : BEval Γ env .readInt (.int 0)
  | floatBuiltin : BEval Γ env (.floatBuiltin n v) .unit
  | strBuiltin : BEval Γ env (.strBuiltin n args) .unit

/--
Forward simulation / oracle correctness: whatever the natural semantics
evaluates, the CEK machine computes, under any continuation stack `S`. The
machine's stack discipline is therefore a faithful realization of the spec.
Specialized to the empty stack this is `BEval Γ [] c w → Runs Γ (load c) (.ret w, [])`.
-/
theorem bigstep_runs {Γ : Core} {env : Env} {c : Comp} {w : Rv} (h : BEval Γ env c w) : ∀ S, Runs Γ (.eval c env, S) (.ret w, S) :=
  by induction h with
      | ret hv =>
        intro S
        exact Runs.step (by
          simp [step, hv]) .refl
      | bind _ _ ihm ihn =>
        intro S
        refine Runs.step rfl ?_
        refine (ihm _).trans ?_
        exact Runs.step rfl (ihn S)
      | forceThunk hv _ ih =>
        intro S
        exact Runs.step (by
          simp [step, hv]) (ih S)
      | forceVal hv hne =>
        intro S
        refine Runs.step ?_ .refl
        revert hv hne
        cases w <;> intro hv hne <;> first | exact absurd rfl (hne _ _) | simp [step, hv]
      | lam =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | appFull _ hargs hlen _ ihf ihb =>
        intro S
        refine Runs.step rfl ?_
        refine (ihf _).trans ?_
        refine Runs.step ?_ (ihb S)
        simp [step, hargs, hlen]
      | appPart _ hargs hlen ihf =>
        intro S
        refine Runs.step rfl ?_
        refine (ihf _).trans ?_
        refine Runs.step ?_ .refl
        simp [step, hargs, hlen]
      | iteT hc _ ih =>
        intro S
        exact Runs.step (by
          simp [step, hc]) (ih S)
      | iteF hc _ ih =>
        intro S
        exact Runs.step (by
          simp [step, hc]) (ih S)
      | prim ha hb hd =>
        intro S
        exact Runs.step (by
          simp [step, ha, hb, hd]) .refl
      | callFull hf hargs hlen _ ihb =>
        intro S
        exact Runs.step (by
          simp [step, hf, hargs, hlen]) (ihb S)
      | callPart hf hargs hlen =>
        intro S
        exact Runs.step (by
          simp [step, hf, hargs, hlen]) .refl
      | case hs hm _ ih =>
        intro S
        exact Runs.step (by
          simp [step, hs, hm]) (ih S)
      | withReuse _ ih =>
        intro S
        exact Runs.step (by
          simp [step]) (ih S)
      | reuse hv =>
        intro S
        exact Runs.step (by
          simp [step, hv]) .refl
      | dup =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | drop =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | print =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | printf =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | prints =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | readInt =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | floatBuiltin =>
        intro S
        exact Runs.step (by
          simp [step]) .refl
      | strBuiltin =>
        intro S
        exact Runs.step (by simp [step]) .refl

/-- Oracle adequacy on closed programs: the natural semantics and the machine
    agree on the final value. -/
theorem load_runs {Γ : Core} {c : Comp} {w : Rv} (h : BEval Γ [] c w) : Runs Γ (load c) (.ret w, []) :=
  bigstep_runs h []

/-- A run to a halted (non-stepping) configuration is unique: the machine being a
    deterministic function, two maximal runs from the same start coincide. This is
    `MStep.deterministic` lifted to whole runs. -/
theorem runs_to_halt_unique {Γ : Core} {a n1 : Conf} (h1 : Runs Γ a n1) : step Γ n1 = none → ∀ {n2}, Runs Γ a n2 → step Γ n2 = none → n1 = n2 :=
  by induction h1 with
      | refl =>
        intro hn1 n2 h2 hn2
        cases h2 with
          | refl => rfl
          | step hs _ => simp [hs] at hn1
      | step hs _ ih =>
        intro hn1 n2 h2 hn2
        cases h2 with
          | refl => simp [hs] at hn2
          | step hs2 hrest2 =>
            have hb := Option.some.inj (hs.symm.trans hs2)
            subst hb
            exact ih hn1 hrest2 hn2

/--
Oracle soundness: the machine is a faithful realization of the big-step natural
semantics. Whenever the specification evaluates a closed program `c` to `w`, the
machine halts on exactly `w` (`load_runs`), and it halts on no other value
(`runs_to_halt_unique`). Together with `MStep.deterministic` this is what
licenses the CEK machine as the differential oracle: its observable result is
the natural semantics' value, uniquely determined.
-/
theorem oracle_sound {Γ : Core} {c : Comp} {w : Rv} (h : BEval Γ [] c w) : Runs Γ (load c) (.ret w, []) ∧ ∀ {w'}, Runs Γ (load c) (.ret w', []) → w' = w :=
  by
    refine ⟨load_runs h, ?_⟩
    intro w' h'
    have heq : ((.ret w : MState), ([] : Stack)) = ((.ret w' : MState), ([] : Stack)) := runs_to_halt_unique (load_runs h) rfl h' rfl
    simp only [Prod.mk.injEq, MState.ret.injEq] at heq
    exact heq.1.symm

end Prism
