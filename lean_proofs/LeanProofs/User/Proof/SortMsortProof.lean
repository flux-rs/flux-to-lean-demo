import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMsort
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def SortMsort_proof : SortMsort := by
  unfold SortMsort
  zapt

end F
