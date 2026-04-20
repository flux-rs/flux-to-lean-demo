import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibTestBozo
import LeanFixpoint

namespace F

def FibTestBozo_proof : FibTestBozo := by
  solve_fusion
  
end F
