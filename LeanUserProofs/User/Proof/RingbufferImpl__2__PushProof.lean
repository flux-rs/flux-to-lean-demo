import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__Push
import LeanFixpoint
import LeanProofs.Lib.Tactics
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

/-- `(a+1) % len` is either `a+1` (no wraparound) or `0` (wraps exactly to `len`). -/
theorem mod_succ (a len : Int) (ha0 : 0 ≤ a) (hal : a < len) :
    (a + 1) % len = a + 1 ∨ (a + 1) % len = 0 ∧ a + 1 = len := by
  by_cases h : a + 1 < len
  · exact .inl (by apply mod_silly <;> omega)
  · have : a + 1 = len := by omega
    exact .inr ⟨by rw [this, Int.emod_self], this⟩

def RingbufferImpl__2__Push_proof : RingbufferImpl__2__Push := by
  unfold RingbufferImpl__2__Push
  fusion
  repeat' (first | (intro) | apply And.intro | grind)
  · rename_i s0 val0 inv_hyp enq_len_hyp inv0 hC hd_ge0 tl_ge0
    have hC' : s0.hd = (s0.tl + 1) % s0.len := by grind
    refine inv_hyp s0.hd ⟨hd_ge0, ?_⟩
    by_cases hnl : s0.num_enqueues < s0.len
    · obtain ⟨htl, hhd⟩ := enq_len_hyp hnl
      rw [if_pos hnl]
      rcases mod_succ s0.tl s0.len (by omega) (by omega) with hm | ⟨hm, hm2⟩ <;> omega
    · rw [if_neg hnl]; omega
  · rename_i s0 val0 inv_hyp enq_len_hyp inv0 hC hd_ge0 tl_ge0 _ len_ge0 len_ne0 hnl
    have hC' : s0.hd = (s0.tl + 1) % s0.len := by grind
    obtain ⟨htl, hhd⟩ := enq_len_hyp hnl
    rcases mod_succ s0.tl s0.len (by omega) (by omega) with hm | ⟨hm, hm2⟩
    · omega -- hd = tl + 1 contradicts hhd : hd ≤ tl
    · have hhd0 : s0.hd = 0 := by omega
      have hmod2 : (s0.hd + 1) % s0.len = s0.hd + 1 := by rw [hhd0]; apply mod_silly <;> omega
      omega
  · apply mod_non_neg; rename_i s0 val0 inv_hyp enq_len_hyp inv0 _; omega
  · apply mod_lt; rename_i s0 val0 inv_hyp enq_len_hyp inv0 _; omega
  · rename_i s0 val0 inv_hyp enq_len_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0 hnl
    have hlen : a3.len = s0.len := by grind
    have htl : a3.tl = s0.tl := by grind
    have hnum : a3.num_enqueues = s0.num_enqueues := by grind
    obtain ⟨htl0, hhd0⟩ := enq_len_hyp (by omega)
    rw [hlen, htl, hnum]
    rcases mod_succ s0.tl s0.len (by omega) (by omega) with hm | ⟨hm, hm2⟩ <;> omega
  · -- here `hnl : a3.num_enqueues + 1 < a3.len` already forces `s0.tl + 1 < s0.len` (no wrap)
    rename_i s0 val0 inv_hyp enq_len_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0 hnl
    have hlen : a3.len = s0.len := by grind
    have htl : a3.tl = s0.tl := by grind
    have hnum : a3.num_enqueues = s0.num_enqueues := by grind
    obtain ⟨htl0, hhd0⟩ := enq_len_hyp (by omega)
    have hmod : (s0.tl + 1) % s0.len = s0.tl + 1 := by apply mod_silly <;> omega
    rw [hlen, htl]
    by_cases hcond : s0.hd ≠ (s0.tl + 1) % ringbuffer_fslice_len s0.elems
    · have hhd : a3.hd = s0.hd := by grind
      rw [hhd]; omega
    · have hhd : a3.hd = (s0.hd + 1) % s0.len := by grind
      have hlen_eq_s0 : s0.len = ringbuffer_fslice_len s0.elems := by grind
      have hC'' : s0.hd = (s0.tl + 1) % s0.len := by rw [hlen_eq_s0]; omega
      have hltnum : s0.hd < s0.num_enqueues := by omega
      have hmod2 : (s0.hd + 1) % s0.len = s0.hd + 1 := by apply mod_silly <;> omega
      rw [hhd]; omega
  · rename_i s0 val0 inv_hyp enq_len_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0
    have hlen : a3.len = s0.len := by grind
    by_cases hcond : s0.hd ≠ (s0.tl + 1) % ringbuffer_fslice_len s0.elems
    · have hhd : a3.hd = s0.hd := by grind
      omega
    · have hhd : a3.hd = (s0.hd + 1) % s0.len := by grind
      have hmod2 : (s0.hd + 1) % s0.len < s0.len := by apply mod_lt; omega
      omega
  · rename_i s0 val0 inv_hyp enq_len_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0
    apply mod_non_neg
    have hlen : a3.len = s0.len := by grind
    omega
  · rename_i s0 val0 inv_hyp enq_len_hyp inv0 result a3 hbig len_eq hd_ge0 tl_ge0 set_eq len_ge0 len_ne0
    apply mod_lt
    have hlen : a3.len = s0.len := by grind
    omega

end F
