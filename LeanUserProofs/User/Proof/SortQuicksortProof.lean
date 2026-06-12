import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksort
import LeanFixpoint
import LeanProofs.Lib.Lemmas

open Classical

namespace F

def SortQuicksort_proof : SortQuicksort := by
  solve_fixpoint

end F
