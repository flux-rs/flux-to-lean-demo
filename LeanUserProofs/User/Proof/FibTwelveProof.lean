import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibTwelve
import Flex

namespace F

def FibTwelve_proof : FibTwelve := by
  unfold FibTwelve
  solve_fixpoint

end F
