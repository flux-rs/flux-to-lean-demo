import Lean

open Lean Elab Tactic Meta in
private partial def zapCore : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => return ()
  | g :: restGoals =>
    let ty ← whnfR (← g.getType)
    if ty.isForall then
      -- goal is `p → q` or `∀ x, P x`: introduce
      evalTactic (← `(tactic| intro _))
      zapCore
    else if ty.isAppOfArity ``And 2 then
      -- goal is `p ∧ q`: split into two subgoals
      evalTactic (← `(tactic| and_intros))
      zapCore
    else
      -- Leaf goal: try grind, then rfl; if either closes the goal, continue with siblings.
      -- If both fail, skip this goal, process siblings, then restore it.
      let leafOk ← try evalTactic (← `(tactic| grind)); pure true catch _ =>
                   try evalTactic (← `(tactic| rfl));   pure true catch _ => pure false
      if leafOk then
        zapCore  -- g is closed; carry on with restGoals
      else
        setGoals restGoals
        zapCore
        let remaining ← getGoals
        setGoals (g :: remaining)

/-- decomposes implications (`p → q`) and conjunctions (`p ∧ q`)
    recursively via `intro` and `and_intros`, and applies `grind`
    (falling back to `rfl`) at leaf goals. -/
elab "zap" : tactic => zapCore


-- Build `fun x₁ x₂ … xₙ => True` for a type of the form `t₁ → t₂ → … → tₙ → Prop`.
open Lean Elab Tactic Meta in
private partial def mkTrueWitness (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isForall then
    let body ← mkTrueWitness ty.bindingBody!
    return .lam ty.bindingName! ty.bindingDomain! body ty.bindingInfo!
  else
    return mkConst ``True

open Lean Elab Tactic Meta in
private partial def trivialkCore : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => return ()
  | g :: _ =>
    let goalType ← whnfR (← g.getType)
    unless goalType.isAppOfArity ``Exists 2 do return ()
    let varType := goalType.appFn!.appArg!
    let varTypeWhnf ← whnfR varType
    unless varTypeWhnf.isForall do return ()
    let witness ← mkTrueWitness varType
    -- Extract the predicate directly from the goal type instead of
    -- letting mkAppM infer it, then build the Exists.intro application manually
    let pred := goalType.appArg!
    let u ← getLevel varType
    let newGoals ← g.apply (mkApp3 (mkConst ``Exists.intro [u]) varType pred witness)
    -- let newGoals ← g.apply (mkApp3 (mkConst ``Exists.intro) varType pred witness)
    setGoals newGoals
    trivialkCore


/-- For a goal `∃ f : t₁ → t₂ → … → tₙ → Prop, P f` (n ≥ 1),
    provides `fun x₁ x₂ … xₙ => True` as the witness and recurses
    until the top-level goal is no longer such an existential. -/
elab "trivialk" : tactic => trivialkCore

/-- Sequences `trivialk`, `simp`, and `zap`. -/
macro "zapt" : tactic => `(tactic| (trivialk; simp; zap))




open Lean Elab Tactic Meta in
private partial def splitAndsAllCore : TacticM Unit := do
  let ctx ← getLCtx
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let ty ← whnf decl.type
    if ty.isAppOf ``And then
      let h  := mkIdent decl.userName
      let h1 := mkIdent (decl.userName.appendAfter "₁")
      let h2 := mkIdent (decl.userName.appendAfter "₂")
      evalTactic (← `(tactic| obtain ⟨$h1, $h2⟩ := $h))
      splitAndsAllCore
      return

elab "split_ands_all" : tactic => splitAndsAllCore


-- ---------------------------------------------------------------------------
-- zapTrue: simplify a goal by replacing grind-provable conjuncts with True
-- ---------------------------------------------------------------------------

-- Return type for zapTrueExpr: (simplified proposition, backward proof)
-- Using a plain Prod to avoid anonymous-constructor elaboration quirks.
private abbrev ZTR := Lean.Expr × Lean.Expr

open Lean Elab Tactic Meta in
/-- Try to prove `e` using `grind` in a side goal.
    Returns the proof expression if successful, `none` otherwise.
    The current goal list is left unchanged. -/
private def tryGrindProve (e : Expr) : TacticM (Option Expr) := do
  let mvar      ← mkFreshExprMVar e
  let saved     ← saveState
  let prevGoals ← getGoals
  setGoals [mvar.mvarId!]
  let ok ←
    try
      evalTactic (← `(tactic| grind))
      let remaining ← getGoals
      pure remaining.isEmpty
    catch _ => pure false
  if ok then
    let proof ← instantiateMVars mvar
    setGoals prevGoals
    return some proof
  else
    restoreState saved
    return none

open Lean Elab Tactic Meta in
/-- Recurse under `∃` and `∧`, replacing `grind`-provable leaf propositions
    with `True`. Returns `(simplified, backward)` where `backward` proves
    `simplified → original`. -/
private partial def zapTrueExpr (e : Expr) : TacticM ZTR := do
  let e ← whnfR e
  if e.isAppOfArity ``Exists 2 then
    let α := e.appFn!.appArg!
    let P := e.appArg!
    -- Recurse under the binder with a fresh free variable, preserving the original name
    let (P', implFun) ← withLocalDecl P.bindingName! .default α fun x => do
      let (body', toOrig) ← zapTrueExpr (P.beta #[x])
      -- P' = fun x => simplified body
      let P'      ← mkLambdaFVars #[x] body'
      -- implFun : ∀ x, P' x → P x  (used to build the backward proof)
      let implFun ← withLocalDecl `hx .default body' fun hx =>
        mkLambdaFVars #[x, hx] (mkApp toOrig hx)
      return (P', implFun)
    -- simplified : ∃ x, P' x  (α is implicit in Exists, inferred from P')
    let simplified ← mkAppM ``Exists #[P']
    -- backward : (∃ x, P' x) → ∃ x, P x
    let backward   ← mkAppM ``Exists.imp #[implFun]
    return (simplified, backward)

  else if e.isAppOfArity ``And 2 then
    let p := e.appFn!.appArg!
    let q := e.appArg!
    let (p', backP) ← zapTrueExpr p
    let (q', backQ) ← zapTrueExpr q
    -- simplified : p' ∧ q'
    let simplified ← mkAppM ``And #[p', q']
    -- backward : p' ∧ q' → p ∧ q
    let backward   ← mkAppM ``And.imp #[backP, backQ]
    return (simplified, backward)

  else if e.isForall then
    -- goal is `∀ x : α, P x` (or `p → q`): recurse under the binder
    let α := e.bindingDomain!
    let (simplified, backward) ← withLocalDecl e.bindingName! e.bindingInfo! α fun x => do
      let (body', toOrig) ← zapTrueExpr (e.bindingBody!.instantiate1 x)
      if body' == mkConst ``True then
        -- The body fully simplified to True; collapse the whole forall to True.
        -- backward : True → ∀ x : α, original_body  =  fun _ x => toOrig trivial
        let backward ← withLocalDecl `_h .default (mkConst ``True) fun _h =>
          mkLambdaFVars #[_h, x] (mkApp toOrig (mkConst ``True.intro))
        return (mkConst ``True, backward)
      else
        -- simplified : ∀ x, body'
        let simplified ← mkForallFVars #[x] body'
        -- backward : (∀ x, body') → ∀ x, original_body
        --          = fun h x => toOrig (h x)
        let backward ← withLocalDecl `h .default simplified fun h =>
          mkLambdaFVars #[h, x] (mkApp toOrig (mkApp h x))
        return (simplified, backward)
    return (simplified, backward)

  else
    -- Leaf: try grind
    match ← tryGrindProve e with
    | some proof =>
      -- Replace leaf with True; backward: fun _ => proof
      let backward ← withLocalDecl `_h .default (mkConst ``True) fun _h =>
        mkLambdaFVars #[_h] proof
      return (mkConst ``True, backward)
    | none =>
      -- Keep as-is; backward = identity
      let backward ← withLocalDecl `h .default e fun h =>
        mkLambdaFVars #[h] h
      return (e, backward)

open Lean Elab Tactic Meta in
/-- Simplify the current goal by recursing under `∃`, `∧`, and `∀` (/ `→`),
    discharging `grind`-provable leaves and replacing them with `True`,
    then cleaning up with `simp [and_true, true_and]`.

    Examples:
    · `⊢ ∃ x, x > 100 ∧ 4 > 2`          ↝  `⊢ ∃ x, x > 100`
    · `⊢ ∃ x, P x ∧ (Q x → Q x)`        ↝  `⊢ ∃ x, P x`
    · `⊢ ∀ x, P x ∧ 4 > 2`              ↝  `⊢ ∀ x, P x`
    · `⊢ ∀ x, (x > 0 → x > 0) ∧ Q x`   ↝  `⊢ ∀ x, Q x` -/
private def zapTrueCore : TacticM Unit := do
  let goal ← getMainGoal
  let ty   ← goal.getType
  let (ty', backward) ← zapTrueExpr ty
  -- Introduce a new goal with the simplified type.
  -- Close the original goal via: original ← backward (proof of simplified).
  let newGoal ← mkFreshExprMVar ty' (kind := .syntheticOpaque)
  goal.assign (mkApp backward newGoal)
  setGoals [newGoal.mvarId!]
  -- Erase any remaining `_ ∧ True` / `True ∧ _` residue (no-op if none)
  try evalTactic (← `(tactic| simp only [and_true, true_and])) catch _ => pure ()

elab "zapTrue" : tactic => zapTrueCore



example : ∃ x : Nat, x > 100 ∧ 4 > 2 := by
  zapTrue  -- goal becomes: ∃ x : Nat, x > 100
  exact ⟨101, by omega⟩

example (P Q : Nat → Prop) : ∃ x, P x ∧ (Q x → Q x) := by
  zapTrue  -- goal becomes: ∃ x, P x
  sorry

def ex1 {P Q: Prop}: (P -> Q) ∧ 5 > 0 := by
    zapTrue -- some_tactic // turns goal into `P -> Q`
    sorry

def ex2 {P Q: Prop}: (P -> P) ∧ Q := by
    zapTrue -- // turns goal into `∀x, Q
    sorry

def ex3 {P Q: Prop}: P -> (P ∧ Q) := by
    zapTrue -- // turns goal into `∀x, Q
    sorry

def ex4: ∃ k1 k2 : Int -> Prop,
  ∀ x,  ((k1 x /\ 10 < x) -> (0 < x))
     /\ ∀ y, k2 y /\ 10 < x /\ 20 < y -> 30 < x + y := by
  zapTrue
  exists (fun _ => True), (fun _ => True)
  grind

def ex5: ∃ k1 k2 : Int -> Prop,
  ∀ x,  (k1 x -> 10 < x -> 0 < x)
     /\ (∀ y, k2 y -> 10 < x -> 20 < y -> 30 < x + y) := by
  zapTrue
  exists (fun _ => True), (fun _ => True)
  grind

def nl_ex1 {P Q: Prop}: (P -> Q) ∧ 5 > 0 := by
    zapTrue -- turns goal into `P -> Q`
    sorry

def nl_ex2 {P Q: Prop}: P ∧ Q ∧ 5 > 0 := by
    zapTrue -- turns goal into `P ∧ Q`
    sorry

def nl_ex3 {P Q: Prop}: (P-> P) ∧ Q := by
    zapTrue -- some_tactic // turns goal into `Q`
    sorry

def nl_ex4 {P Q: Prop}: P -> (Q ∧ P) := by
    zapTrue -- turns goal into `P -> Q`
    sorry

def nl_ex5 {P Q : α -> Prop} : ∀x, (P x -> P x) ∧ Q x := by
    zapTrue -- some_tactic turns goal into `∀x, Q x`
    sorry

def nl_ex6 : ∃ x: Nat, x > 100 ∧ 4 > 2 := by
    zapTrue -- turns goal into ∃ x: Nat, x > 100
    sorry
