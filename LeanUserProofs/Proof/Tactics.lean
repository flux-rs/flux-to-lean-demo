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
