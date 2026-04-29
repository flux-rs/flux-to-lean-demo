import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMerge
import LeanProofs.Lib.Lemmas
open Classical

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

def sortmerge_k2 (out : Int) (a6 : (Arr Int)) (a6len : Int) (j : Int) (i : Int) (old : (Arr Int)) (oldlen : Int) (lo : Int) (mid : Int) (hi : Int) (_ : (Arr Int)) (_ : Int) (a'₈₂ : Int) (a2 : (Arr Int)) (a2len : Int) : Prop :=
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

def sortmerge_k3 : Int → Int → Arr Int → Int → Int → Int → Arr Int → Int → Int → Int → Int → Arr Int → Int → Int → Arr Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

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
attribute [grind] k12
attribute [grind] k13
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

set_option maxHeartbeats 1500000

def SortMerge_proof : SortMerge := by
  unfold SortMerge
  exists sortmerge_k0 ; exists sortmerge_k1 ; exists sortmerge_k2
  exists sortmerge_k3 ; exists k4 ; exists k5
  exists k6 ; exists k7 ; exists k8 ; exists k9
  exists k10 ; exists k11 ; exists k12 ; exists k13
  intros _ lo
  zap
  · grind only [is_mix]
  · grind only [sortmerge_k0, sortmerge_k2, eq_mix_perm]
  · unfold sortmerge_k0 sortmerge_k2 k4 k5 k6 at *
    split_hyps
    · grind only [sort_is_sorted_between]
    · simp_all [-sort_is_sorted_between]
      apply sorted_set
      assumption
      assumption
  · unfold sortmerge_k0 sortmerge_k2 k4 k5 k6 at *
    split_hyps
    all_goals (simp_all ; grind)
  · unfold sortmerge_k0 sortmerge_k2 k5 k6 at *
    split_hyps
    all_goals (simp_all ; grind)
  · unfold sortmerge_k2 at *
    split_hyp_ands ; simp_all
    apply is_mix_set_l
    assumption
    assumption
  · right ; and_intros
    · grind only [sortmerge_k2]
    · intros
      unfold sortmerge_k0 sortmerge_k2 at *
      rename_i i _ _ _ _ _ _ _ _ _ _
      have : lo ≤ i := by omega
      simp_all [vectors_arr_eq_between]
      split_hyp_ands
      rename_i h _ _ _
      rw [h, h]
      apply_assumption
      all_goals omega
    · intros
      unfold sortmerge_k2 at *
      split_hyps <;> simp_all
  · unfold sortmerge_k0 sortmerge_k2 k8 at *
    split_hyps
      <;> simp_all [-sort_is_sorted_between]
      <;> try grind
    · apply sorted_set
      assumption
      grind only
    · apply sorted_set
      assumption
      grind only
    · apply sorted_set
      assumption
      grind only
  · unfold sortmerge_k0 sortmerge_k2 k8 at *
    split_hyps
      <;> simp_all
      <;> grind
  · unfold sortmerge_k0 sortmerge_k2 k8 at *
    split_hyps
      <;> simp_all
      <;> grind
  · rename_i out _ _ _ _ _ _ _ _ _
    unfold k8 at *
    split_hyps
      <;> simp_all
      <;> unfold sortmerge_k2 at *
      <;> split_hyp_ands
      <;> grind [is_mix_set_l, is_mix_set_r]
  · right ; and_intros
    · grind only [sortmerge_k2]
    · intros
      unfold sortmerge_k0 sortmerge_k2 k8 at *
      split_hyps <;> simp_all [vectors_arr_eq_between]
      any_goals grind
      rename_i h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [h, h]
      any_goals grind
      apply_assumption
      all_goals grind
    · intros
      unfold sortmerge_k0 sortmerge_k2 k8 at *
      split_hyps <;> simp_all [vectors_arr_eq_between]
      any_goals grind
      rename_i h1 _ _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [h, h]
      any_goals grind
      apply h1
      assumption
      omega
      grind only
      rename_i h1 _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [h, h]
      any_goals grind
      apply h1
      assumption
      omega
      grind only
      rename_i h1 _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [h, h]
      any_goals grind
      apply h1
      assumption
      omega
      grind only
  · unfold sortmerge_k0 k12 at *
    split_hyps
    simp_all ; grind only [is_frame]
  · unfold sortmerge_k0 k12 at *
    split_hyps
    simp_all ; grind only [is_frame]
  · simp_all [vectors_arr_eq_between, sortmerge_k0, k12]
    grind only
end F
