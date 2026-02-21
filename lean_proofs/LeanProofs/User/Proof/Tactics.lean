import Lean

open Lean Elab Tactic Meta in
private partial def monkeyCore : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => return ()
  | g :: restGoals =>
    let ty ← whnfR (← g.getType)
    if ty.isForall then
      -- goal is `p → q` or `∀ x, P x`: introduce
      evalTactic (← `(tactic| intro _))
      monkeyCore
    else if ty.isAppOfArity ``And 2 then
      -- goal is `p ∧ q`: split into two subgoals
      evalTactic (← `(tactic| and_intros))
      monkeyCore
    else
      -- Leaf goal: try grind; if it closes the goal, continue with siblings.
      -- If grind fails, skip this goal, process siblings, then restore it.
      let grindOk ← try evalTactic (← `(tactic| grind)); pure true catch _ => pure false
      if grindOk then
        monkeyCore  -- g is closed; carry on with restGoals
      else
        setGoals restGoals
        monkeyCore
        let remaining ← getGoals
        setGoals (g :: remaining)

/-- `monkey` decomposes implications (`p → q`) and conjunctions (`p ∧ q`)
    recursively via `intro` and `and_intros`, stopping at leaf goals. -/
elab "smash" : tactic => monkeyCore
