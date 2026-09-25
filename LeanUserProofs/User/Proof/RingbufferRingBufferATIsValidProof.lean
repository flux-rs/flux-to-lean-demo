import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferRingBufferATIsValid
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferRingBufferATIsValid_proof : RingbufferRingBufferATIsValid := by
  unfold RingbufferRingBufferATIsValid
  grind

end F
