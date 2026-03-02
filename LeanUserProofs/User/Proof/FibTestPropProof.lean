import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibTestProp

namespace F

def FibTestProp_proof : FibTestProp := by
  unfold FibTestProp
  grind

end F
