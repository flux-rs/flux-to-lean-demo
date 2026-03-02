import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertRec
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F

def SortInsertRec_proof : SortInsertRec := by
  unfold SortInsertRec
  exists SortInsertRecKVarSolutions.k0
  exists SortInsertRecKVarSolutions.k1
  exists SortInsertRecKVarSolutions.k2
  exists SortInsertRecKVarSolutions.k3
  exists SortInsertRecKVarSolutions.k4
  simp [LeanProofs.Lib.Lemmas.arr_get, SortInsertRecKVarSolutions.k0, SortInsertRecKVarSolutions.k1, SortInsertRecKVarSolutions.k2, SortInsertRecKVarSolutions.k3, SortInsertRecKVarSolutions.k4]
  zap
  . rename_i old n k hyp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i j _ _ _ _
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
              . rename_i hyp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                apply hyp <;> grind
            . grind
          . grind
      . have j_gt_k : j > k := by grind
        by_cases i > k
        . grind
        . by_cases i = k
          . simp_all [LeanProofs.Lib.Lemmas.set_get_eq']
            rw [LeanProofs.Lib.Lemmas.set_get_neq']
            . rw [LeanProofs.Lib.Lemmas.set_get_neq']
              . rename_i hyp _ _ _ _ _ _ _ _ _ _ _ _ _
                apply hyp <;> grind
              . grind
            . grind
          . grind
  . rename_i old n k _ _ _ _ _ _ _ hyp i j _ _ _
    rcases hyp with ha | hb
    . by_cases j = k
      . simp_all
        by_cases i = k - 1
        . grind
        . have i_lt_mid_minus_1 : i < k - 1 := by grind
          have hh : old.elems i <= old.elems (k - 1) := by
            split_ands_all
            obtain ⟨hA, hB⟩ := ha
            apply hA <;> grind
          grind
      . grind
    . obtain ⟨hb1, hb2⟩ := hb
      have k_0 : k = 0 := by grind
      grind
end F
