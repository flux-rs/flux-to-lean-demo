import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferRingBufferATNew
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferRingBufferATNew_proof : RingbufferRingBufferATNew := by
  unfold RingbufferRingBufferATNew
  intros len init elems _ _
  simp_all
  and_intros
  · intro idx
    have := @Int.emod_nonneg idx len
    grind
  · omega

end F
