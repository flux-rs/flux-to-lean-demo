import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibSlow
import LeanProofs.Lib.Tactics

namespace F

def FibFibSlow_proof : FibFibSlow := by
  unfold FibFibSlow
  zap

end F
