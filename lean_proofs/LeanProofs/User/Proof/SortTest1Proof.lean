import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortTest1
import LeanProofs.Lib.Tactics

namespace F

def SortTest1_proof : SortTest1 := by
  unfold SortTest1
  zapt <;> simp_all []

end F
