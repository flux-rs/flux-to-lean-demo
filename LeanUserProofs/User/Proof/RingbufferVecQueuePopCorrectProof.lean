import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferVecQueuePopCorrect
open Classical
set_option linter.unusedVariables false


namespace F

theorem pop_front_subslice (s : FSlice Int) (h : l < r) (hl : 0 ≤ l) :
    ringbuffer_fslice_pop_front (ringbuffer_fslice_subslice s l r) =
    ringbuffer_fslice_subslice s (l + 1) r := by
  simp only [ringbuffer_fslice_pop_front, ringbuffer_fslice_subslice]
  rw [List.drop_take, List.drop_drop]
  have h1 : l.toNat + 1 = (l + 1).toNat := by omega
  have h2 : r.toNat - l.toNat - 1 = r.toNat - (l + 1).toNat := by omega
  rw [h1, h2]

theorem pop_front_append_subslice (s : FSlice Int) (t : FSlice Int)
    (hl : 0 ≤ l) (hlt : l + 1 ≤ r) (hr : r.toNat ≤ s.length) :
    ringbuffer_fslice_pop_front (ringbuffer_fslice_append
      (ringbuffer_fslice_subslice s l r) t) =
    ringbuffer_fslice_append (ringbuffer_fslice_subslice s (l + 1) r) t := by
  simp only [ringbuffer_fslice_pop_front, ringbuffer_fslice_append, ringbuffer_fslice_subslice]
  rw [List.drop_append_of_le_length]
  · rw [List.drop_take, List.drop_drop]
    have h1 : l.toNat + 1 = (l + 1).toNat := by omega
    have h2 : r.toNat - l.toNat - 1 = r.toNat - (l + 1).toNat := by omega
    rw [h1, h2]
  · simp [List.length_take, Nat.min_def]
    split <;> omega

theorem pop_front_singleton_append (s : FSlice Int) (t : FSlice Int)
    (hl : 0 ≤ l) (hend : l + 1 = r) (hr : r.toNat ≤ s.length) :
    ringbuffer_fslice_pop_front (ringbuffer_fslice_append
      (ringbuffer_fslice_subslice s l r) t) = t := by
  simp only [ringbuffer_fslice_pop_front, ringbuffer_fslice_append, ringbuffer_fslice_subslice]
  rw [List.drop_append_of_le_length]
  · rw [List.drop_take, List.drop_drop]
    have h0 : r.toNat - l.toNat - 1 = 0 := by omega
    simp [h0]
  · simp [List.length_take, Nat.min_def]
    split <;> omega

def RingbufferVecQueuePopCorrect_proof : RingbufferVecQueuePopCorrect := by
  unfold RingbufferVecQueuePopCorrect
  intro rb vq vqeq hdne hvqlen _ _ ⟨hringlen, hhdlb, hhdhb, htllb, htlhb, _⟩ n1 n2 n3
  simp only [if_pos hdne] at n1 n2 n3 ⊢
  by_cases hdgttl : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) > rb.tl
  · rw [if_pos hdgttl]
    by_cases hcase : rb.hd > rb.tl
    · rw [if_pos hcase] at vqeq
      by_cases hnotlast : rb.hd + 1 < ringbuffer_fslice_len rb.elems
      · have hnewhd_eq : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) = rb.hd + 1 := by
          apply Int.emod_eq_of_lt <;> grind
        rw [vqeq, hnewhd_eq]
        grind [pop_front_append_subslice, ringbuffer_fslice_len]
      · exfalso
        have heq : rb.hd + 1 = ringbuffer_fslice_len rb.elems := by grind
        have hmod0 : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) = 0 := by
          rw [heq, Int.emod_self]
        grind
    · simp at hcase
      have hlt : rb.hd < rb.tl := by grind
      have hnewhd_eq : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) = rb.hd + 1 := by
        apply Int.emod_eq_of_lt <;> grind
      grind
  · rw [if_neg hdgttl]
    by_cases hcase : rb.hd > rb.tl
    · rw [if_pos hcase] at vqeq
      by_cases hwrap : rb.hd = ringbuffer_fslice_len rb.elems - 1
      · have hnewhd0 : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) = 0 := by
          have hrlen : ringbuffer_fslice_len rb.elems - 1 + 1 = ringbuffer_fslice_len rb.elems := by
            have := hringlen; omega
          rw [hwrap, hrlen, Int.emod_self]
        rw [vqeq, hnewhd0]
        grind [pop_front_singleton_append]
      · have hnotlast : rb.hd + 1 < ringbuffer_fslice_len rb.elems := by
          grind
        have hnewhd_eq : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) = rb.hd + 1 := by
          apply Int.emod_eq_of_lt <;> grind
        grind
    · rw [if_neg hcase] at vqeq
      simp at hcase
      have hlt : rb.hd < rb.tl := by grind
      have hnewhd_eq : (rb.hd + 1) % (ringbuffer_fslice_len rb.elems) = rb.hd + 1 := by
        apply Int.emod_eq_of_lt <;> grind
      rw [vqeq, hnewhd_eq]
      exact pop_front_subslice rb.elems hlt hhdlb

end F
