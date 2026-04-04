import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksortRange
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics
open Classical

namespace F
theorem bigger_perm :
  sort_is_bigger a lo p p -> sort_is_perm a a' lo (p-1) -> sort_is_bigger a' lo p p
  := by
  sorry

end F

namespace F


open SortQuicksortRangeKVarSolutions in

def SortQuicksortRange_proof : SortQuicksortRange := by
  unfold SortQuicksortRange
  exists k0; exists k1;
  simp [k0, k1]
  zap
  . simp [is_perm]; grind
  . simp [is_frame]
  . rename_i arr1 pa arr2 pb i j _ _ _
    rename_i old lo hi _ _ _ _ _ _ p arr0 _ _ _ _ _ _ _ _ _ _ _
    split_hyps <;> try grind
    . simp_all
      rename_i war1 war2 war0 _ _ _ _ _ _ _ _ _ _ _ _
      sorry
    . sorry
    . sorry
  . sorry -- is-perm
  . sorry -- is-frame

end F
