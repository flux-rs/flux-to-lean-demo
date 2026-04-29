import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortTestSorted
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics

namespace F

def SortTestSorted_proof : SortTestSorted := by
  unfold SortTestSorted
  simp
  zapt
  apply_assumption <;> grind

end F
