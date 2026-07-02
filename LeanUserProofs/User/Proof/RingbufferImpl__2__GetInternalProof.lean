import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__GetInternal
import LeanFixpoint
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__GetInternal_proof: RingbufferImpl__2__GetInternal := by
  unfold RingbufferImpl__2__GetInternal
  grind

end F
