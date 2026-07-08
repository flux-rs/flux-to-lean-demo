import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsert
-- import LeanProofs.Lib.Tactics
import Flex

open Classical

namespace F

def inv_insert (k : Int) (arr_elems : (Arr Int)) (arr_len : Int) (_old_elems : (Arr Int)) (old_len : Int) (n : Int) : Prop :=
     0 <= k
  /\ k <= n
  /\ n < arr_len
  /\ arr_len = old_len
  /\ sort_is_sorted_between_exc arr_elems 0 (n + 1) k

private theorem swap_le (arr : Arr Int) (n k i j : Int)
    (hsx : ∀ a b, 0 ≤ a → a < b → b < n + 1 → ¬ b = k → arr a ≤ arr b)
    (hk : 0 < k) (hlt : arr k < arr (k - 1))
    (hi : 0 ≤ i) (hij : i < j) (hjn : j < n + 1) (hjk1 : ¬ j = k - 1) :
    (if i = k then arr (k - 1) else if i = k - 1 then arr k else arr i) ≤
    (if j = k then arr (k - 1) else if j = k - 1 then arr k else arr j) := by
  by_cases hjk : j = k
  · by_cases hik1 : i = k - 1
    · grind                                                            -- arr k ≤ arr (k-1) via hlt
    · have key := hsx i (k - 1) (by omega) (by omega) (by omega) (by omega); grind
  · by_cases hik : i = k
    · have key := hsx (k - 1) j (by omega) (by omega) (by omega) (by omega); grind
    · by_cases hik1 : i = k - 1
      · have key := hsx k j (by omega) (by omega) (by omega) (by omega); grind
      · have key := hsx i j (by omega) (by omega) (by omega) (by omega); grind

private theorem done_le (arr : Arr Int) (n k i j : Int)
    (hsx : ∀ a b, 0 ≤ a → a < b → b < n + 1 → ¬ b = k → arr a ≤ arr b)
    (hk : 0 ≤ k) (hcond : k ≤ 0 ∨ (0 < k ∧ arr (k - 1) ≤ arr k))
    (hi : 0 ≤ i) (hij : i < j) (hjn : j < n + 1) : arr i ≤ arr j := by
  rcases hcond with hk0 | ⟨hk0, hord⟩
  · exact hsx i j hi hij hjn (by omega)
  · by_cases hjk : j = k
    · by_cases hik1 : i = k - 1
      · grind                                                          -- arr (k-1) ≤ arr k via hord
      · have key := hsx i (k - 1) (by omega) (by omega) (by omega) (by omega); grind
    · exact hsx i j hi hij hjn (by omega)

def SortInsert_proof : SortInsert := by
  unfold SortInsert
  fusion
  exists inv_insert;
  simp [LeanProofs.Lib.Lemmas.arr_get, inv_insert]
  elim_leaves
  · apply swap_le <;> assumption
  · apply done_le <;> assumption

end F
