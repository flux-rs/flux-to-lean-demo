import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMerge
import LeanProofs.Lib.Lemmas
open Classical

namespace F

open SortMergeKVarSolutions
open LeanProofs.Lib.Lemmas

def is_mix (v1 v2 v3 : Arr Int) (l1 l2 l3 r1 r2 r3 : Int) : Prop :=
  ∀ i, (l1 ≤ i ∧ i < r1) → (∃ j, (l2 ≤ j ∧ j < r2) ∧ v1 i = v2 j) ∨ (∃ k, (l3 ≤ k ∧ k < r3) ∧ v1 i = v3 k)

def maintains_order (v1 v2 : Arr Int) (l1 l2 r1 r2 : Int) : Prop :=
  ∀ i j, (l1 ≤ i ∧ i < r1) → (i < j ∧ j < r1) → (∃ i', (l2 ≤ i' ∧ i' < r2) ∧ v1 i = v2 i' ∧ ∃ j', (i' < j' ∧ j' < r2 ∧ v1 j = v2 j'))

def is_ordered_mix (v1 v2 v3 : Arr Int) (l1 l2 l3 r1 r2 r3 : Int) : Prop :=
  is_mix v1 v2 v3 l1 l2 l3 r1 r2 r3 ∧
  maintains_order v1 v2 l1 l2 r1 r2 ∧
  maintains_order v1 v3 l1 l3 r1 r3

def k0 (k : Int) (a2 : (Arr Int)) (a2len : Int) (ol : (Arr Int)) (oldlen : Int) (lo : Int) (mid : Int) (hi : Int) (auxo : (Arr Int)) (auxolen : Int) : Prop :=
  ((k ≥ 0) ∧ (k ≥ lo) ∧ (k ≤ oldlen) ∧ k ≤ hi + 1) ∧
  a2len = oldlen ∧
  is_frame auxo a2 lo (hi + 1) ∧
  vectors_arr_eq_between a2 ol lo k

def k1 (a'₆₀ : Int) (a'₆₁ : Int) (a'₆₂ : (Arr Int)) (a'₆₃ : Int) (a'₆₄ : (Arr Int)) (a'₆₅ : Int) (a'₆₆ : Int) (a'₆₇ : Int) (a'₆₈ : Int) (a'₆₉ : (Arr Int)) (a'₇₀ : Int) : Prop :=
  True

def k2 (out : Int) (j : Int) (a6 : (Arr Int)) (a6len : Int) (i : Int) (old : (Arr Int)) (oldlen : Int) (lo : Int) (mid : Int) (hi : Int) (auxo : (Arr Int)) (auxolen : Int) (a'₈₂ : Int) (a2 : (Arr Int)) (a2len : Int) : Prop :=
  ((out ≥ 0) ∧ (out ≥ i) ∧ (out ≥ lo) ∧ (out ≤ a'₈₂) ∧ (out ≤ oldlen)) ∧
  a6len = oldlen ∧ a2len = a6len ∧
  sort_is_sorted_between a6 lo out ∧
  is_frame old a6 lo hi ∧
  i + j - lo - mid - 1 = out - lo ∧
  out ≤ hi + 1 ∧
  is_ordered_mix a6 a2 a2 lo lo (mid + 1) out i j ∧
  i ≤ hi + 1 ∧ j ≤ hi + 1

def k3 (a'₃₄ : Int) (a'₃₅ : Int) (a'₃₆ : Int) (a'₃₇ : (Arr Int)) (a'₃₈ : Int) (a'₃₉ : Int) (a'₄₀ : (Arr Int)) (a'₄₁ : Int) (a'₄₂ : Int) (a'₄₃ : Int) (a'₄₄ : Int) (a'₄₅ : (Arr Int)) (a'₄₆ : Int) (a'₄₇ : Int) (a'₄₈ : (Arr Int)) (a'₄₉ : Int) : Prop :=
  True

attribute [grind] k0
attribute [grind] k1
attribute [grind] k2
attribute [grind] k3
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
attribute [grind] k14
attribute [grind] k15
attribute [grind] k16
attribute [grind] k17
attribute [grind] sort_is_sorted_between
attribute [grind] is_frame

--     -- veqb a3 old l k
--     -- is_mix a7 a3 a3 lo lo (mid + 1) out i j
--     -- is_perm old a7 lo hi
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

-- -- a28 = arr_set a7 out (arr_get a3 i)
--       -- is_mix a7 a3 a3 lo lo (mid + 1) out i j
--       -- sorted_between a7 lo out

-- theorem grind_set_mix_sorted_sorted
--   (a28 a7 a3 : Arr Int)
--   (h1 : a28 = vectors_arr_set a7 out (vectors_arr_get a3 i))
--   (h2 : is_mix a7 a3 a3 lo lo (mid + 1) out i j)
--   (h3 : sort_is_sorted_between a7 lo out)
--   (hlast_ge : out = lo ∨ a7 (out - 1) ≤ vectors_arr_get a3 i)
--   (hlm : lo ≤ mid)
--   (hi_hi : i ≤ hi + 1)
--   (hj_hi : j ≤ hi + 1)
--   (hijout : i + j - lo - mid - 1 = out - lo)
--   : sort_is_sorted_between a28 lo (out + 1) := by
--   subst h1
--   intro x y hxy
--   rcases hxy with ⟨hxlo, hxy_lt, hy_out1⟩
--   have hy_le_out : y ≤ out := by omega
--   by_cases hy_eq_out : y = out
--   · have hx_out : x < out := by omega
--     have hx_ne_out : x ≠ out := by omega
--     have hx_bound : a7 x ≤ vectors_arr_get a3 i := by
--       rcases hlast_ge with h_out_lo | h_last
--       · exfalso
--         omega
--       · by_cases hx_last : x = out - 1
--         · simpa [hx_last] using h_last
--         · have hx_lt_last : x < out - 1 := by omega
--           have hs : a7 x ≤ a7 (out - 1) := h3 x (out - 1) ⟨hxlo, hx_lt_last, by omega⟩
--           calc
--             a7 x ≤ a7 (out - 1) := hs
--             _ ≤ vectors_arr_get a3 i := h_last
--     simpa [vectors_arr_set, hy_eq_out, hx_ne_out] using hx_bound
--   · have hy_out : y < out := by omega
--     have hs : a7 x ≤ a7 y := h3 x y ⟨hxlo, hxy_lt, hy_out⟩
--     have hx_ne_out : x ≠ out := by omega
--     have hy_ne_out : y ≠ out := by omega
--     simpa [vectors_arr_set, hx_ne_out, hy_ne_out] using hs

set_option maxHeartbeats 600000

def SortMerge_proof : SortMerge := by
  unfold SortMerge
  exists k0 ; exists k1 ; exists k2 ; exists k3
  exists k4 ; exists k5 ; exists k6 ; exists k7
  exists k8 ; exists k9 ; exists k10 ; exists k11
  exists k12 ; exists k13 ; exists k14 ; exists k15
  exists k16 ; exists k17
  zap
  · grind [is_mix]
  · grind [maintains_order]
  · grind [maintains_order]
  · grind [is_ordered_mix, eq_mix_perm]
  · unfold k0 k2 k13 at *
    split_hyps
    any_goals grind
    -- sorted old lo (mid + 1)
    -- sorted old (mid + 1) (hi + 1)
    -- eq_b a3 old lo k
    -- sorted a7 lo out
    -- ordered_mix a7 a3 a3 lo lo (mid + 1) out i j
  · unfold k0 k2 k13 at *
    split_hyps
    · sorry
    · sorry
    · grind
    · grind
    · sorry
    · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

end F
