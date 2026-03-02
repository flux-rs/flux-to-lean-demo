import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortSwap
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F

def SortSwap_proof : SortSwap := by
  unfold SortSwap
  zapt
  rename_i old m_ind n _ _ _ _ _ _ _ _ _ i j _ _ _ _
  by_cases j < m_ind - 1
  . grind
  . by_cases j = m_ind - 1
    . grind
    . sorry

end F
