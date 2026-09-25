import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferRingBufferATLen
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferRingBufferATLen_proof : RingbufferRingBufferATLen := by
  unfold RingbufferRingBufferATLen
  grind

end F
