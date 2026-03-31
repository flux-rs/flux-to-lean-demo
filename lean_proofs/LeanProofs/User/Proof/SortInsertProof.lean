import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertSwap
import LeanProofs.Lib.Tactics

open Classical

namespace F

def inv_insert (k : Int) (arr_elems : (Arr Int)) (arr_len : Int) (_old_elems : (Arr Int)) (old_len : Int) (n : Int) : Prop :=
     0 <= k
  /\ k <= n
  /\ n < arr_len
  /\ arr_len = old_len
  /\ sort_is_sorted_between_exc arr_elems 0 (n + 1) k

open SortInsertSwapKVarSolutions in

def SortInsertSwap_proof : SortInsertSwap := by
  unfold SortInsertSwap
  exists inv_insert; exists k1; exists k2; exists k3
  simp [LeanProofs.Lib.Lemmas.arr_get, inv_insert, k1, k2, k3]
  zap
  split_ands_all
  . rename_i _ k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i j _ _ _ _
    by_cases j < k - 1
    . grind
    . by_cases j = k
      . by_cases i = k - 1
        . grind
        . have i_lt_k_minus_1 : i < k - 1 := by grind
          have i_ne_k : i ≠ k := by grind
          simp_all []
          rename_i hyp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          apply hyp <;> grind
      . have j_gt_k : j > k := by grind
        by_cases i > k
        . grind
        . by_cases i = k
          . simp_all []
            rename_i hyp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            apply hyp <;> grind
          . grind
  . rename_i old n _ _ _ _ _ k arr _ _ _ _ ihyp hyp i j _ _ _
    rcases hyp with ha | hb
    . by_cases j = k
      . simp_all
        by_cases i = k - 1
        . grind
        . have hh : arr.elems i <= arr.elems (k - 1) := by
             apply ihyp <;> grind
          grind
      . grind
    . obtain ⟨hb1, hb2⟩ := hb
      have k_0 : k = 0 := by grind
      grind



end F
