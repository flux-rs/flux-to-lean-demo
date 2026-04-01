import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksortRange
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics
open Classical

namespace F

open SortQuicksortRangeKVarSolutions in

def SortQuicksortRange_proof : SortQuicksortRange := by
  unfold SortQuicksortRange
  exists k0; exists k1;
  simp [k0, k1]
  zap
  . simp [is_perm]; grind
  . simp [is_frame]
  . rename_i arr' pa arr'' pb i j _ _ _
    rcases pa with pa1 | pa2 <;> rcases pb with pb1 | pb2
    . sorry
    . sorry
    . sorry
    . grind
  . sorry -- is-perm
  . sorry -- is-frame

end F
