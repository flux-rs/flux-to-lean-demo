import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__IsFull
import LeanFixpoint

open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__IsFull_proof : RingbufferImpl__2__IsFull := by
  solve_fixpoint

end F
