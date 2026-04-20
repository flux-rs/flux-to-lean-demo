import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSeven
import LeanFixpoint

namespace F

def FibSeven_proof : FibSeven := by
  solve_fusion

end F
