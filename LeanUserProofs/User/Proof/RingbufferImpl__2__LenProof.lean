import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__Len
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__Len_proof : RingbufferImpl__2__Len := by
  unfold RingbufferImpl__2__Len
  grind

end F
