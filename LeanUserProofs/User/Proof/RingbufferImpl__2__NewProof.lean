import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__New
import LeanFixpoint
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__New_proof : RingbufferImpl__2__New := by
  unfold RingbufferImpl__2__New
  grind

end F
