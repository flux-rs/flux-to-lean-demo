import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferRingBufferATIsFull
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferRingBufferATIsFull_proof : RingbufferRingBufferATIsFull := by
  unfold RingbufferRingBufferATIsFull ringbuffer_rb_next_index
  grind

end F
