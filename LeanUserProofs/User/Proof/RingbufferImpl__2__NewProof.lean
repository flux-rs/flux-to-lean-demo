import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__New
import LeanFixpoint
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__New_proof : RingbufferImpl__2__New := by
  unfold RingbufferImpl__2__New
  intros len init _ idx _ _
  simp_all
  have := @Int.emod_nonneg idx len
  grind


end F
