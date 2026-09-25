import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortBinarySearchExt
open Classical
set_option linter.unusedVariables false


namespace F

/-- Loop invariant: `lo` and `hi` are in bounds, everything before `lo` is smaller than `target`,
    and everything from `hi` onwards is bigger than `target`. -/
def inv_bs (lo hi : Int) (arr : Arr Int) (len target : Int) : Prop :=
     0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ len
  ∧ sort_all_lt_between arr 0 lo target
  ∧ sort_all_gt_between arr hi len target

/-- If `arr[mid] < target` then everything up to (and including) `mid` is smaller than `target`. -/
private theorem step_lo (arr : Arr Int) (len target lo mid : Int)
    (hsorted : ∀ i j, 0 ≤ i ∧ i < j ∧ j < len → arr i ≤ arr j)
    (hlt : ∀ i, 0 ≤ i ∧ i < lo → arr i < target)
    (hlo : 0 ≤ lo) (hmid : lo ≤ mid) (hmidlen : mid < len) (hv : arr mid < target) :
    ∀ i, 0 ≤ i ∧ i < mid + 1 → arr i < target := by
  intro i ⟨h0, hi⟩
  by_cases hil : i < lo
  · exact hlt i ⟨h0, hil⟩
  · by_cases him : i = mid
    · subst him; exact hv
    · have := hsorted i mid ⟨h0, by omega, hmidlen⟩; omega

/-- If `target < arr[mid]` then everything from `mid` onwards is bigger than `target`. -/
private theorem step_hi (arr : Arr Int) (len target hi mid : Int)
    (hsorted : ∀ i j, 0 ≤ i ∧ i < j ∧ j < len → arr i ≤ arr j)
    (hgt : ∀ i, hi ≤ i ∧ i < len → arr i > target)
    (hmid0 : 0 ≤ mid) (hmid : mid < hi) (hv : ¬ arr mid < target) (hne : arr mid ≠ target) :
    ∀ i, mid ≤ i ∧ i < len → arr i > target := by
  intro i ⟨hm, hl⟩
  by_cases hih : hi ≤ i
  · exact hgt i ⟨hih, hl⟩
  · by_cases him : i = mid
    · subst him; omega
    · have := hsorted mid i ⟨hmid0, by omega, hl⟩; omega

def SortBinarySearchExt_proof : SortBinarySearchExt := by
  unfold SortBinarySearchExt
  refine ⟨inv_bs,
          fun p _ _ _ lo _ => p = lo,
          fun _ _ _ _ _ _ => True,
          fun lo₁ hi₁ arr len target _ _ => inv_bs lo₁ hi₁ arr len target,
          fun p _ _ _ lo hi => p = lo + (hi - lo) / 2, ?_⟩
  intro ⟨arr, len⟩ target hsorted hlen
  simp only [inv_bs, sort_all_lt_between, sort_all_gt_between, sort_is_sorted_between,
    vectors_arr_get, LeanProofs.Lib.Lemmas.arr_get] at *
  refine ⟨⟨Int.le_refl _, hlen, Int.le_refl _, fun i _ => by omega, fun i _ => by omega⟩, ?_⟩
  intro lo hi ⟨hlo, hlohi, hhi, hlt, hgt⟩
  refine ⟨?exit, ?body⟩
  · -- loop exit: `lo = hi`, so the invariant gives the `Err` postcondition
    intro hexit
    refine ⟨trivial, ?_⟩
    intro p hp
    subst p
    have heq : lo = hi := by omega
    subst heq
    exact ⟨hhi, hlt, hgt⟩
  · intro hlohi'
    refine ⟨by omega, fun _ => trivial, by omega, fun _ => ⟨?ne, ?eq⟩⟩
    · -- `arr[mid] ≠ target`: move `lo` or `hi` and re-establish the invariant
      intro hne
      refine ⟨?gt, ?lt, fun lo₁ hi₁ h => h⟩
      · intro hv
        exact ⟨hlo, by omega, by omega, hlt,
               step_hi arr len target hi _ hsorted hgt (by omega) (by omega) hv hne⟩
      · intro hv
        exact ⟨by omega, by omega, hhi,
               step_lo arr len target lo _ hsorted hlt hlo (by omega) (by omega) hv, hgt⟩
    · -- `arr[mid] = target`: return `Ok(mid)`
      intro heq
      refine ⟨trivial, ?_⟩
      intro p hp
      subst p
      exact ⟨by omega, by simpa using heq⟩

end F
