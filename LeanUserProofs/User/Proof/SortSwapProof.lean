import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortSwap
import Flex
open Classical

set_option linter.unusedVariables false


namespace F

def SortSwap_proof : SortSwap := by
  unfold SortSwap
  fusion
  solve_fixpoint

end F
