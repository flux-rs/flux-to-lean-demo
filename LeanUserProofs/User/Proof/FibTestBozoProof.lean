import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibTestBozo

namespace F

def FibTestBozo_proof : FibTestBozo := by
  unfold FibTestBozo fib_bozo_val
  grind

end F
