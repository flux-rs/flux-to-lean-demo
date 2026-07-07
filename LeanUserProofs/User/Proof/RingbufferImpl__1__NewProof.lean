import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__1__New
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__1__New_proof : RingbufferImpl__1__New := by
  unfold RingbufferImpl__1__New
  intros len init elems _ _
  simp_all
  and_intros
  · intro idx
    have := @Int.emod_nonneg idx len
    grind
  · omega

end F
