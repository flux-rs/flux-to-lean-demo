import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferRingBufferATHasElements
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferRingBufferATHasElements_proof : RingbufferRingBufferATHasElements := by
  unfold RingbufferRingBufferATHasElements
  grind

end F
