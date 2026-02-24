import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSumLoop
import LeanProofs.User.Proof.Tactics

namespace F

@[simp]
def k0 (i : Int) (total : Int) (n : Int) : Prop :=
  0 <= i /\ i <= n /\ total = fib_spec_sum i

def FibSumLoop_proof : FibSumLoop := by
  unfold FibSumLoop; exists k0; simp; zap


end F
