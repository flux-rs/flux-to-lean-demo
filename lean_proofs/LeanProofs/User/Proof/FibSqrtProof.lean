import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSqrt
import LeanProofs.Lib.Tactics

namespace F

@[simp]
def fib_sqrt_inv(i: Int) (x: Int) : Prop :=
  i >= 0 /\
  x >= 0 /\
  (i * i > x -> (i-1) * (i-1) <= x)

def FibSqrt_proof : FibSqrt := by
  unfold FibSqrt
  exists fib_sqrt_inv; simp
  zap



end F
