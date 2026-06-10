import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMergesortRange
open Classical

namespace F

open SortMergesortRangeKVarSolutions

theorem is_sorted_between_h (v1 v2 : Arr Int)
  (h1 : sort_is_sorted_between v1 m (r + 1))
  (h2 : sort_is_perm v2 v1 m r)
  (h3 : sort_is_sorted_between v2 l m)
  (h4 : v1 (m - 1) ≤ v1 m)
  : sort_is_sorted_between v1 l (r + 1) := by
  intro i j hijs
  rcases hijs with ⟨hli, hij, hjr⟩
  have hframe := h2.2
  by_cases hjm : j < m
  · have him : i < m := by omega
    have hs : v2 i ≤ v2 j := h3 i j ⟨hli, hij, hjm⟩
    have hi_eq : v1 i = v2 i := hframe.1 i him
    have hj_eq : v1 j = v2 j := hframe.1 j hjm
    simpa [hi_eq, hj_eq] using hs
  · have hmj : m ≤ j := by omega
    by_cases him : i < m
    · have hi_eq : v1 i = v2 i := hframe.1 i him
      have hm1_lt_m : m - 1 < m := by omega
      have hm1_eq : v1 (m - 1) = v2 (m - 1) := hframe.1 (m - 1) hm1_lt_m
      have hi_le_m1 : v1 i ≤ v1 (m - 1) := by
        by_cases him1 : i < m - 1
        · have hs : v2 i ≤ v2 (m - 1) := h3 i (m - 1) ⟨hli, him1, by omega⟩
          simpa [hi_eq, hm1_eq] using hs
        · have hi_eq_m1 : i = m - 1 := by omega
          simp [hi_eq_m1]
      have hi_le_m : v1 i ≤ v1 m := by omega
      by_cases hjeq : j = m
      · simpa [hjeq] using hi_le_m
      · have hmj' : m < j := by omega
        have hm_le_j : v1 m ≤ v1 j := h1 m j ⟨by omega, hmj', hjr⟩
        omega
    · exact h1 i j ⟨by omega, hij, hjr⟩

attribute [grind] sort_is_perm
attribute [grind] is_frame
attribute [grind] is_perm
attribute [grind .] is_sorted_between_h
attribute [grind] vectors_arr_get
attribute [grind] sort_is_sorted_between

set_option maxHeartbeats 1000000

def SortMergesortRange_proof : SortMergesortRange := by
  unfold SortMergesortRange
  exists k0 ; exists k1
  unfold k0 k1
  zap
end F
