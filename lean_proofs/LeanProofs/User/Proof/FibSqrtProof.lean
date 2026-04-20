import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSqrt
import LeanFixpoint

namespace F

@[qualif] def q1 (i : Int) := i > 0
@[qualif] def q2 (i x : Int) :=
  i^2 > x → (i - 1)^2 ≤ x

def FibSqrt_proof : FibSqrt := by
  solve_fixpoint

end F
