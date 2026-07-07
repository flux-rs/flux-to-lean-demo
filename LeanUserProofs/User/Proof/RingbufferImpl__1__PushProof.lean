import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__1__Push
open Classical
set_option linter.unusedVariables false


namespace F

theorem mod_non_neg (a b : Int) : 0 < b -> 0 <= (a % b) := by
  intro h
  exact Int.emod_nonneg a (by omega)

theorem mod_lt (a b : Int) : 0 < b -> (a % b) < b := by
  intro h
  exact Int.emod_lt_of_pos a h

theorem mod_silly (a b : Int) : 0 <= a -> 0 <= b -> a < b -> (a % b) = a := by
  intro ha hb hab
  exact Int.emod_eq_of_lt ha hab

theorem mod_succ (a len : Int) (ha0 : 0 ≤ a) (hal : a < len) :
    (a + 1) % len = a + 1 ∨ (a + 1) % len = 0 ∧ a + 1 = len := by
  by_cases h : a + 1 < len
  · exact .inl (by apply mod_silly <;> omega)
  · have : a + 1 = len := by omega
    exact .inr ⟨by rw [this, Int.emod_self], this⟩

/-- `(a2 + len - hd) % len` as a linear expression, given `0 ≤ a2, hd < len`. -/
theorem circ_diff (a hd len : Int) (ha0 : 0 ≤ a) (hal : a < len) (hhd0 : 0 ≤ hd) (hhdl : hd < len) :
    (a + len - hd) % len = if a ≥ hd then a - hd else len - hd + a := by
  split
  · rename_i h
    have heq : a + len - hd = (a - hd) + len := by omega
    rw [heq, ← Int.emod_eq_add_self_emod]
    apply Int.emod_eq_of_lt <;> omega
  · rename_i h
    have heq2 : a + len - hd = len - hd + a := by omega
    rw [heq2]
    apply Int.emod_eq_of_lt <;> omega

/-- If `a2`'s circular distance from `hd+1` is within the new occupancy bound, and `hd = (tl+1)%len`
    (i.e. the buffer is full), then `a2`'s circular distance from `hd` is within the old bound. -/
theorem circ_shift (hd tl len a2 : Int) (h1 : 1 < len) (h2 : 0 ≤ hd) (h3 : hd < len)
    (h4 : 0 ≤ tl) (h5 : tl < len) (hC : hd = (tl + 1) % len) (ha20 : 0 ≤ a2) (ha2l : a2 < len)
    (hnewdist : (a2 + len - ((hd + 1) % len)) % len <
      (if tl > (hd + 1) % len then tl - (hd + 1) % len
       else if tl < (hd + 1) % len then len - (hd + 1) % len + tl else 0)) :
    (a2 + len - hd) % len < (if tl > hd then tl - hd else if tl < hd then len - hd + tl else 0) := by
  have hcd : (a2 + len - hd) % len = if a2 ≥ hd then a2 - hd else len - hd + a2 :=
    circ_diff a2 hd len ha20 ha2l h2 h3
  rw [hcd]
  rcases mod_succ tl len (by omega) (by omega) with hmtl | ⟨hmtl, hmtl2⟩
  · rcases mod_succ hd len (by omega) (by omega) with hm2 | ⟨hm2, hm3⟩
    · have hlt : hd + 1 < len := by
        have := Int.emod_lt_of_pos (hd + 1) (show 0 < len by omega)
        omega
      rw [hm2] at hnewdist
      have hcd2 : (a2 + len - (hd + 1)) % len = if a2 ≥ hd + 1 then a2 - (hd + 1) else len - (hd + 1) + a2 :=
        circ_diff a2 (hd + 1) len ha20 ha2l (by omega) (by omega)
      rw [hcd2] at hnewdist
      omega
    · have hnew0 : (hd + 1) % len = 0 := hm2
      rw [hnew0] at hnewdist
      have hcd2 : (a2 + len - 0) % len = if a2 ≥ 0 then a2 - 0 else len - 0 + a2 :=
        circ_diff a2 0 len ha20 ha2l (by omega) (by omega)
      rw [hcd2] at hnewdist
      omega
  · have hhd0 : hd = 0 := by omega
    have hnew0 : (hd + 1) % len = 1 := by
      rw [hhd0]
      apply mod_silly <;> omega
    rw [hnew0] at hnewdist
    have hcd2 : (a2 + len - 1) % len = if a2 ≥ 1 then a2 - 1 else len - 1 + a2 :=
      circ_diff a2 1 len ha20 ha2l (by omega) (by omega)
    rw [hcd2] at hnewdist
    omega

/-- Non-full case: pushing at `tl` only grows the occupancy window by one slot (at `tl` itself);
    an index other than `tl` that fits in the new window already fit in the old one. -/
theorem circ_step (hd tl len a5 : Int) (h1 : 1 < len) (h2 : 0 ≤ hd) (h3 : hd < len)
    (h4 : 0 ≤ tl) (h5 : tl < len) (ha50 : 0 ≤ a5) (ha5l : a5 < len) (hnetl : a5 ≠ tl)
    (hnewdist : (a5 + len - hd) % len <
      (if (tl + 1) % len > hd then (tl + 1) % len - hd
       else if (tl + 1) % len < hd then len - hd + (tl + 1) % len else 0)) :
    (a5 + len - hd) % len < (if tl > hd then tl - hd else if tl < hd then len - hd + tl else 0) := by
  have hcd : (a5 + len - hd) % len = if a5 ≥ hd then a5 - hd else len - hd + a5 :=
    circ_diff a5 hd len ha50 ha5l h2 h3
  have hcdtl : (tl + len - hd) % len = if tl ≥ hd then tl - hd else len - hd + tl :=
    circ_diff tl hd len (by omega) (by omega) h2 h3
  rcases mod_succ tl len (by omega) (by omega) with hm | ⟨hm, hm2⟩
  · rw [hm] at hnewdist
    rw [hcd]
    omega
  · rw [hm] at hnewdist
    rw [hcd]
    omega

def RingbufferImpl__1__Push_proof : RingbufferImpl__1__Push := by
  unfold RingbufferImpl__1__Push
  fusion
  repeat' (first | (intro) | apply And.intro | grind)
  · rename_i s0 val0 inv_hyp inv0 hC hd_ge0 tl_ge0
    obtain ⟨hlen1, hhd0, hhdl, htl0, htll, hlenset⟩ := inv0
    rw [← hlenset] at hC
    have hC' : s0.hd = (s0.tl + 1) % s0.len := not_not.mp hC
    refine inv_hyp s0.hd ⟨hd_ge0, hhdl⟩ ?_
    dsimp only
    rw [circ_diff s0.hd s0.hd s0.len hd_ge0 hhdl hd_ge0 hhdl]
    rcases mod_succ s0.tl s0.len (by omega) (by omega) with hm | ⟨hm, hm2⟩ <;> omega
  · rename_i s0 val0 inv_hyp inv0 hC hd_ge0 tl_ge0 hex len_ge0 len_ne0 a2 ha2bound hdist
    obtain ⟨hlen1, hhd0, hhdl, htl0, htll, hlenset⟩ := inv0
    rw [← hlenset] at hC
    have hC' : s0.hd = (s0.tl + 1) % s0.len := not_not.mp hC
    obtain ⟨ha20, ha2l⟩ := ha2bound
    dsimp only at hdist
    exact inv_hyp a2 ⟨ha20, ha2l⟩
      (circ_shift s0.hd s0.tl s0.len a2 hlen1 hd_ge0 hhdl tl_ge0 htll hC' ha20 ha2l hdist)
  · apply mod_non_neg; rename_i s0 val0 inv_hyp inv0 _; omega
  · apply mod_lt; rename_i s0 val0 inv_hyp inv0 _; omega
  · rename_i s0 val0 inv_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0 a5 ha5bound hdist
    have hlen : a3.len = s0.len := by grind
    have htl : a3.tl = s0.tl := by grind
    have hinit : a3.init = s0.init := by grind
    obtain ⟨hlen1, hhd0, hhdl, htl0, htll, hlenset⟩ := inv0
    dsimp only at hdist ha5bound ⊢
    rw [hlen] at ha5bound hdist
    obtain ⟨ha50, ha5l⟩ := ha5bound
    rw [hinit, htl]
    by_cases hcond : s0.hd ≠ (s0.tl + 1) % s0.len
    · have hhd : a3.hd = s0.hd := by grind
      rw [htl, hhd] at hdist
      by_cases heq : a5 = s0.tl
      · simp [SmtMap_select, SmtMap_store, heq]
      · have hsel : SmtMap_select s0.init a5 :=
          inv_hyp a5 ⟨ha50, by omega⟩
            (circ_step s0.hd s0.tl s0.len a5 hlen1 hhd0 hhdl htl0 htll ha50 ha5l heq hdist)
        simp only [SmtMap_select, SmtMap_store]
        rw [if_neg]
        · exact hsel
        · simp [heq]
    · have hhd : a3.hd = (s0.hd + 1) % s0.len := by grind
      have hC' : s0.hd = (s0.tl + 1) % s0.len := not_not.mp hcond
      by_cases heq : a5 = s0.tl
      · simp [SmtMap_select, SmtMap_store, heq]
      · have hcd5 : (a5 + s0.len - s0.hd) % s0.len =
            if a5 ≥ s0.hd then a5 - s0.hd else s0.len - s0.hd + a5 :=
          circ_diff a5 s0.hd s0.len ha50 ha5l hhd0 hhdl
        have holddist : (a5 + s0.len - s0.hd) % s0.len <
            (if s0.tl > s0.hd then s0.tl - s0.hd else if s0.tl < s0.hd then s0.len - s0.hd + s0.tl else 0) := by
          rcases mod_succ s0.tl s0.len (by omega) (by omega) with hm | ⟨hm, hm2⟩ <;> omega
        have hsel : SmtMap_select s0.init a5 := inv_hyp a5 ⟨ha50, by omega⟩ holddist
        simp only [SmtMap_select, SmtMap_store]
        rw [if_neg]
        · exact hsel
        · simp [heq]
  · rename_i s0 val0 inv_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0
    have hlen : a3.len = s0.len := by grind
    by_cases hcond : s0.hd ≠ (s0.tl + 1) % ringbuffer_fslice_len s0.elems
    · have hhd : a3.hd = s0.hd := by grind
      omega
    · have hhd : a3.hd = (s0.hd + 1) % s0.len := by grind
      have hmod2 : (s0.hd + 1) % s0.len < s0.len := by apply mod_lt; omega
      omega
  · rename_i s0 val0 inv_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0
    apply mod_non_neg
    have hlen : a3.len = s0.len := by grind
    omega
  · rename_i s0 val0 inv_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0
    apply mod_lt
    have hlen : a3.len = s0.len := by grind
    omega

end F
