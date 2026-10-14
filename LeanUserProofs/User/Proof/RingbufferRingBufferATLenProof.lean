import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferRingBufferATLen
import Flex
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferRingBufferATLen_proof : RingbufferRingBufferATLen := by
  unfold RingbufferRingBufferATLen
  zap
  grind

end F
