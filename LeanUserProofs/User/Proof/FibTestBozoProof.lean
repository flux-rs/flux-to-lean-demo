import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibTestBozo

namespace F

def FibTestBozo_proof : FibTestBozo := by
  unfold FibTestBozo
  grind

end F
