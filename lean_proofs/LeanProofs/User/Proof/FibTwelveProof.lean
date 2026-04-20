import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibTwelve
import LeanFixpoint

namespace F

def FibTwelve_proof : FibTwelve := by
  solve_fusion

end F
