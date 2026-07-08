import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMerge
import LeanProofs.Lib.Lemmas
import Flex

open Classical
set_option linter.unusedVariables false

namespace F

open SortMergeKVarSolutions
open LeanProofs.Lib.Lemmas

def is_mix (v1 v2 v3 : Arr Int) (l1 l2 l3 r1 r2 r3 : Int) : Prop :=
  ∀ i, (l1 ≤ i ∧ i < r1) → (∃ j, (l2 ≤ j ∧ j < r2) ∧ v1 i = v2 j) ∨ (∃ k, (l3 ≤ k ∧ k < r3) ∧ v1 i = v3 k)

def sortmerge_k0 (k : Int) (a2 : (Arr Int)) (a2len : Int) (old : (Arr Int)) (oldlen : Int) (lo : Int) (_ : Int) (hi : Int) (auxo : (Arr Int)) (_ : Int) : Prop :=
  ((k ≥ 0) ∧ (k ≥ lo) ∧ (k ≤ oldlen) ∧ k ≤ hi + 1) ∧
  a2len = oldlen ∧
  is_frame auxo a2 lo (hi + 1) ∧
  vectors_arr_eq_between a2 old lo k

def sortmerge_k1 : Int → Int → Arr Int → Int → Arr Int → Int → Int → Int → Int → Arr Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ _ _ _ => True



-- ((k2 i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
def sortmerge_k2 (i : Int) (j : Int) (out : Int) (a6 : (Arr Int)) (a6len : Int)  (old : (Arr Int)) (oldlen : Int) (lo : Int) (mid : Int) (hi : Int) (_ : (Arr Int)) (_ : Int) (a'₈₂ : Int) (a2 : (Arr Int)) (a2len : Int) : Prop :=
  ((out ≥ 0) ∧ (out ≥ i) ∧ (out ≥ lo) ∧ (out ≤ a'₈₂) ∧ (out ≤ oldlen)) ∧
  a6len = oldlen ∧ a2len = a6len ∧
  sort_is_sorted_between a6 lo out ∧
  is_frame old a6 lo hi ∧
  lo ≤ i ∧ mid + 1 ≤ j ∧
  i + j - lo - mid - 1 = out - lo ∧
  out ≤ hi + 1 ∧
  is_mix a6 a2 a2 lo lo (mid + 1) out i j ∧
  i ≤ hi + 1 ∧ j ≤ hi + 1 ∧
  (out = lo ∨ (out > lo ∧ (i ≤ mid → a6 (out - 1) ≤ a2 i) ∧ (j ≤ hi → a6 (out - 1) ≤ a2 j)))

def sortmerge_k3 (a'₂₆ : Int) (a'₂₇ : Int) (a'₂₈ : Int) (a'₂₉ : Int) (a'₃₀ : (Arr Int)) (a'₃₁ : Int) (a'₃₂ : (Arr Int)) (a'₃₃ : Int) (a'₃₄ : Int) (a'₃₅ : Int) (a'₃₆ : Int) (a'₃₇ : (Arr Int)) (a'₃₈ : Int) (a'₃₉ : Int) (a'₄₀ : (Arr Int)) (a'₄₁ : Int) : Prop :=
  True

attribute [grind] sortmerge_k0
attribute [grind] sortmerge_k1
attribute [grind] sortmerge_k2
attribute [grind] sortmerge_k3
attribute [grind] k4
attribute [grind] k5
attribute [grind] k6
attribute [grind] k7
attribute [grind] k8
attribute [grind] k9
attribute [grind] k10
attribute [grind] k11
attribute [grind] sort_is_sorted_between
attribute [grind] is_frame
attribute [simp] LeanProofs.Lib.Lemmas.arr_get
attribute [simp] LeanProofs.Lib.Lemmas.arr_set

theorem eq_mix_perm (old a3 a7 : Arr Int) (lo mid hi out i j k : Int)
  (h1 : vectors_arr_eq_between a3 old lo k)
  (h2 : is_mix a7 a3 a3 lo lo (mid + 1) out i j)
  (hlm : lo ≤ mid)
  (hout : hi < out)
  (hi_hi : i ≤ hi + 1)
  (hj_hi : j ≤ hi + 1)
  (hk_hi : hi < k)
  (hijout : i + j - lo - mid - 1 = out - lo)
  : is_perm old a7 lo hi := by
  intro x hx
  have hx' : lo ≤ x ∧ x ≤ hi := by
    simpa using hx
  rcases hx' with ⟨hlox, xlehi⟩
  have xltout : x < out := by omega
  have hmix := h2 x ⟨hlox, xltout⟩
  rcases hmix with hleft | hright
  · rcases hleft with ⟨y, hy⟩
    rcases hy with ⟨hy_range, hxy⟩
    rcases hy_range with ⟨hylo, hyi⟩
    have ylehi : y ≤ hi := by omega
    have hyk : y < k := by omega
    have h_eq : a3 y = old y := h1 y ⟨hylo, hyk⟩
    refine ⟨y, ?_⟩
    refine ⟨hylo, ylehi, ?_⟩
    simpa [h_eq] using hxy
  · rcases hright with ⟨y, hy⟩
    rcases hy with ⟨hy_range, hxy⟩
    rcases hy_range with ⟨hmidy, hyj⟩
    have hylo : lo ≤ y := by omega
    have ylehi : y ≤ hi := by omega
    have hyk : y < k := by omega
    have h_eq : a3 y = old y := h1 y ⟨hylo, hyk⟩
    refine ⟨y, ?_⟩
    refine ⟨hylo, ylehi, ?_⟩
    simpa [h_eq] using hxy

theorem sorted_set (v : Arr Int) (l r elem : Int)
  (h1 : sort_is_sorted_between v l r)
  (h2 : v (r - 1 ) ≤ elem)
  : sort_is_sorted_between (vectors_arr_set v r elem) l (r + 1) := by
  intro i j hij
  rcases hij with ⟨hli, hij, hjr1⟩
  have hj_cases : j = r ∨ j < r := by omega
  rcases hj_cases with hjeq | hjr
  · have hi_cases : i = r - 1 ∨ i < r - 1 := by omega
    subst j
    rcases hi_cases with hieq | hirm1
    · subst i
      calc
        (vectors_arr_set v r elem) (r - 1) = v (r - 1) := by
          simp [vectors_arr_set]
          grind
        _ ≤ elem := h2
        _ = (vectors_arr_set v r elem) r := by
          symm
          simp [vectors_arr_set]
    · have hivrm1 : v i ≤ v (r - 1) := by
        apply h1 i (r - 1)
        omega
      calc
        (vectors_arr_set v r elem) i = v i := by
          simp [vectors_arr_set]
          grind
        _ ≤ v (r - 1) := hivrm1
        _ ≤ elem := h2
        _ = (vectors_arr_set v r elem) r := by
          symm
          simp [vectors_arr_set]
  · have hisorted : v i ≤ v j := by
      exact h1 i j ⟨hli, hij, hjr⟩
    calc
      (vectors_arr_set v r elem) i = v i := by
        simp [vectors_arr_set]
        grind
      _ ≤ v j := hisorted
      _ = (vectors_arr_set v r elem) j := by
        symm
        simp [vectors_arr_set]
        grind

theorem is_mix_set_l (v1 v2 : Arr Int)
  (h1 : is_mix v1 v2 v2 lo lo (mid + 1) out i j)
  (hloi : lo ≤ i)
  : is_mix (arr_set v1 out (v2 i)) v2 v2 lo lo (mid + 1) (out + 1) (i + 1) j := by
  intro x hx
  have hx_cases : x = out ∨ x < out := by omega
  rcases hx_cases with rfl | hxlto
  · left
    refine ⟨i, ?_⟩
    refine ⟨⟨hloi, by omega⟩, by simp [arr_set]⟩
  · have hmix : (∃ j', (lo ≤ j' ∧ j' < i) ∧ v1 x = v2 j') ∨
      (∃ k, (mid + 1 ≤ k ∧ k < j) ∧ v1 x = v2 k) := by
      apply h1
      omega
    rcases hmix with hleft | hright
    · left
      rcases hleft with ⟨j', hj', heq⟩
      refine ⟨j', ?_⟩
      refine ⟨?_, ?_⟩
      · rcases hj' with ⟨hjlo, hjlt⟩
        exact ⟨hjlo, by omega⟩
      · have hxne : x ≠ out := by omega
        simpa [arr_set, hxne] using heq
    · right
      rcases hright with ⟨k, hk, heq⟩
      refine ⟨k, ?_⟩
      refine ⟨hk, ?_⟩
      have hxne : x ≠ out := by omega
      simpa [arr_set, hxne] using heq

theorem is_mix_set_r (v1 v2 : Arr Int)
  (h1 : is_mix v1 v2 v2 lo lo (mid + 1) out i j)
  (hmidj : mid + 1 ≤ j)
  : is_mix (arr_set v1 out (v2 j)) v2 v2 lo lo (mid + 1) (out + 1) i (j + 1) := by
  intro x hx
  have hx_cases : x = out ∨ x < out := by omega
  rcases hx_cases with rfl | hxlto
  · right
    refine ⟨j, ?_⟩
    refine ⟨⟨hmidj, by omega⟩, by simp [arr_set]⟩
  · have hmix : (∃ j', (lo ≤ j' ∧ j' < i) ∧ v1 x = v2 j') ∨
      (∃ k, (mid + 1 ≤ k ∧ k < j) ∧ v1 x = v2 k) := by
      apply h1
      omega
    rcases hmix with hleft | hright
    · left
      rcases hleft with ⟨j', hj', heq⟩
      refine ⟨j', ?_⟩
      refine ⟨hj', ?_⟩
      have hxne : x ≠ out := by omega
      simpa [arr_set, hxne] using heq
    · right
      rcases hright with ⟨k, hk, heq⟩
      refine ⟨k, ?_⟩
      refine ⟨?_, ?_⟩
      · rcases hk with ⟨hklo, hklt⟩
        exact ⟨hklo, by omega⟩
      · have hxne : x ≠ out := by omega
        simpa [arr_set, hxne] using heq

/-- `a3` equals `old` on `[lo, k)`, `old` is sorted on the left half `[lo, mid+1)` and
    the right half `[mid+1, hi+1)`. Then `a3 m ≤ a3 n` whenever `m < n` and both indices
    lie inside the same half. The two sortedness hypotheses have rigid window shapes so
    `assumption` matches them to the correct (distinct) facts, and `omega` picks the half. -/
private theorem a3_le_merge (a3 old : Arr Int) (lo k mid hi m n : Int)
    (heqb : vectors_arr_eq_between a3 old lo k)
    (hL : sort_is_sorted_between old lo (mid + 1))
    (hR : sort_is_sorted_between old (mid + 1) (hi + 1))
    (hmn : m < n) (hlom : lo ≤ m) (hnk : n < k)
    (hcase : (lo ≤ m ∧ n < mid + 1) ∨ (mid + 1 ≤ m ∧ n < hi + 1)) :
    a3 m ≤ a3 n := by
  have em : a3 m = old m := heqb m ⟨by omega, by omega⟩
  have en : a3 n = old n := heqb n ⟨by omega, by omega⟩
  rw [em, en]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hL m n ⟨h1, hmn, h2⟩
  · exact hR m n ⟨h1, hmn, h2⟩

set_option maxHeartbeats 1500000

theorem SortMerge_proof : SortMerge := by
  unfold SortMerge
  fusion
  exists sortmerge_k0 ; exists sortmerge_k1 ; exists sortmerge_k2; exists sortmerge_k3 ;
  intros _ lo
  zap
  all_goals (try unfold sortmerge_k0 sortmerge_k2 sortmerge_k3 at *)
  all_goals (try split_hyps)
  all_goals
    first
      | (apply sorted_set <;> (first | assumption | grind | (simp_all <;> grind)))
      | (apply is_mix_set_l <;> assumption)
      | (apply is_mix_set_r <;> assumption)
      | (right ; and_intros <;>
          (first
            | grind only
            | (intros; subst_vars;
                simp only [vectors_arr_set, vectors_arr_get, arr_set, arr_get,
                           show ∀ z : Int, z + 1 - 1 = z from fun z => by omega, if_true];
                (first | (apply a3_le_merge <;> (first | assumption | omega)) | omega))
            | simp_all))
      | (simp only [vectors_arr_set, vectors_arr_get, arr_set, arr_get] <;> grind [is_frame])
      | grind only [is_mix]
      | (simp_all [vectors_arr_eq_between] ; grind only)
      | grind only [eq_mix_perm]
  -- mop up the trivial ≤ comparison leftovers from the merge-ordering branches
  all_goals omega
end F
