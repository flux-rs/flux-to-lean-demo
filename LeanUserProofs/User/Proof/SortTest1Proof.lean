import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortTest1
-- import LeanProofs.Lib.Tactics
import LeanFixpoint

namespace F

def SortTest1_proof : SortTest1 := by
  unfold SortTest1
  fusion
  solve_fixpoint

end F
