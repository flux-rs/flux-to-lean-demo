import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibSlow
import LeanFixpoint

namespace F

def FibFibSlow_proof : FibFibSlow := by
  solve_fusion

end F
