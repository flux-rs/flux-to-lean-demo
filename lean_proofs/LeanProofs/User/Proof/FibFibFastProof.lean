import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast
import LeanFixpoint

namespace F

@[qualif] def q_le          (a b : Int) : Prop := a ≤ b
@[qualif] def q_gt_one      (v : Int)   : Prop := v > 1
@[qualif] def q_eq_fib      (v i : Int) : Prop := v = fib_spec_fib i
@[qualif] def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)

def FibFibFast_proof : FibFibFast := by
  solve_fixpoint

end F
