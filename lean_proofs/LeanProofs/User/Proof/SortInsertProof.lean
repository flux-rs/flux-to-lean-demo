import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsert
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas


namespace F

def inv_insert (k : Int) (arr_elems : (Arr Int)) (arr_len : Int) (_old_elems : (Arr Int)) (old_len : Int) (n : Int) : Prop :=
     0 <= k
  /\ k <= n
  /\ n < arr_len
  /\ arr_len = old_len
  /\ sort_is_sorted_between_exc arr_elems 0 (n + 1) k

open SortInsertKVarSolutions in

def SortInsert_proof : SortInsert := by
  unfold SortInsert
  refine ⟨inv_insert, k1, k2, k3, k4, k5, k6, k7, k8, ?_⟩
  simp [LeanProofs.Lib.Lemmas.arr_get, inv_insert, k1, k2, k3, k4, k5, k6, k7, k8]
  zap
  split_ands_all
  . rename_i k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i j _ _ _ _
    by_cases j < k - 1
    . grind
    . by_cases j = k
      . by_cases i = k - 1
        . grind
        . have i_lt_k_minus_1 : i < k - 1 := by grind
          simp_all []
          rw [LeanProofs.Lib.Lemmas.set_get_neq']
          . rw [LeanProofs.Lib.Lemmas.set_get_neq']
            . rw [LeanProofs.Lib.Lemmas.set_get_eq']
              apply_assumption <;> grind
            . grind
          . grind
      . have j_gt_k : j > k := by grind
        by_cases i > k
        . grind
        . by_cases i = k
          . simp_all [LeanProofs.Lib.Lemmas.set_get_eq']
            rw [LeanProofs.Lib.Lemmas.set_get_neq']
            . rw [LeanProofs.Lib.Lemmas.set_get_neq']
              . apply_assumption <;> grind
              . grind
            . grind
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
