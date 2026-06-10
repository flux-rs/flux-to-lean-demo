import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksort
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

open Classical

namespace F

def SortQuicksort_proof : SortQuicksort := by
  unfold SortQuicksort; simp; zap

end F
