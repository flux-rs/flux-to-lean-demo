import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__IsValid
import LeanFixpoint

open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__IsValid_proof : RingbufferImpl__2__IsValid := by
  unfold RingbufferImpl__2__IsValid
  solve_fixpoint

end F
