import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksort
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas
import LeanFixpoint

open Classical

namespace F
def SortQuicksort_proof : SortQuicksort := by
  solve_fixpoint

-- def SortQuicksort_proof : SortQuicksort := by
--   unfold SortQuicksort; simp; zap

end F
