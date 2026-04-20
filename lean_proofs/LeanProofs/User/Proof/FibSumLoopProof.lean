import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSumLoop
import LeanFixpoint

namespace F

-- @[simp]
-- def k0 (i : Int) (total : Int) (n : Int) : Prop :=
--   0 <= i /\ i <= n /\ total = fib_spec_sum i

@[qualif] def q1 (a b : Int)    := a ≤ b
@[qualif] def q2 (i : Int)      := 0 ≤ i
@[qualif] def q3 (i total: Int) := total = fib_spec_sum i

def FibSumLoop_proof : FibSumLoop := by
  solve_fixpoint

end F
