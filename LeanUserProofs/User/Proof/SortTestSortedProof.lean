import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortTestSorted
import LeanProofs.Lib.Lemmas
-- import LeanProofs.Lib.Tactics
import LeanFixpoint

namespace F

def SortTestSorted_proof : SortTestSorted := by
  unfold SortTestSorted
  fusion
  solve_fixpoint
  exact left 0 1 (by omega) (by omega) (by omega)

end F
