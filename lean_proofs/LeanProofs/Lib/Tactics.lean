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
