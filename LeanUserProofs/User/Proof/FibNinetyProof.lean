import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibNinety

namespace F

def FibNinety_proof : FibNinety := by
  unfold FibNinety fib_spec_ninety
  simp

end F
