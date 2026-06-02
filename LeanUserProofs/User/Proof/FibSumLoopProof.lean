import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSumLoop
import LeanProofs.Lib.Tactics

namespace F

@[simp]
def inv (total : Int) (i : Int)  (n : Int) : Prop :=
  0 <= i /\ i <= n /\ total = fib_spec_sum i

def FibSumLoop_proof : FibSumLoop := by
  unfold FibSumLoop; exists inv; simp; grind

end F
