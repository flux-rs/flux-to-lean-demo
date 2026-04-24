import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast
import LeanProofs.Lib.Tactics

namespace F

-- Loop invariant: i > 1 ∧ i ≤ n ∧ prev = fib(i-1) ∧ curr = fib(i)
@[simp]
def fib_fast_inv (i : Int) (prev : Int) (curr : Int) (n : Int) : Prop :=
  i > 1 ∧ i ≤ n ∧ prev = fib_spec_fib (i - 1) ∧ curr = fib_spec_fib i

def FibFibFast_proof : FibFibFast := by
  unfold FibFibFast; exists fib_fast_inv; simp
  zap

end F
