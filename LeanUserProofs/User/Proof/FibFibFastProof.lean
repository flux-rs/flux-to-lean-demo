import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast
import Flex

namespace F

@[qualif] private def q_le (a b : Int) : Prop := a ≤ b
@[qualif] private def q_gt_one (v : Int) : Prop := v > 1
@[qualif] private def q_eq_fib (v i : Int) : Prop := v = fib_spec_fib i
@[qualif] private def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)

def FibFibFast_proof : FibFibFast := by
  solve_fixpoint

end F
