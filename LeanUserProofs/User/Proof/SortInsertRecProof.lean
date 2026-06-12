import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertRec
import LeanFixpoint
import LeanProofs.Lib.Lemmas

namespace F

def SortInsertRec_proof : SortInsertRec := by
  unfold SortInsertRec
  fusion
  simp [LeanProofs.Lib.Lemmas.arr_get]
  intro old n k hsx h1n hnlen hkn hlen hn hk
  refine ⟨?_, ?_⟩
  · intro hk0
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro hlt
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega⟩
    intro i j hi hij hjn hjk1
    by_cases hjk : j = k
    · by_cases hik1 : i = k - 1
      · grind                                                            -- old k ≤ old (k-1) via hlt
      · have key := hsx i (k - 1) (by omega) (by omega) (by omega) (by omega); grind
    · by_cases hik : i = k
      · have key := hsx (k - 1) j (by omega) (by omega) (by omega) (by omega); grind
      · by_cases hik1 : i = k - 1
        · have key := hsx k j (by omega) (by omega) (by omega) (by omega); grind
        · have key := hsx i j (by omega) (by omega) (by omega) (by omega); grind
  · rintro (hk0 | ⟨hk0, hord⟩) i j hi hij hjn
    · exact hsx i j (by omega) hij (by omega) (by omega)
    · by_cases hjk : j = k
      · by_cases hik1 : i = k - 1
        · grind                                                          -- old (k-1) ≤ old k via hord
        · have key := hsx i (k - 1) (by omega) (by omega) (by omega) (by omega); grind
      · exact hsx i j (by omega) hij (by omega) (by omega)

end F
