import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferVecQueuePushCorrect
open Classical
set_option linter.unusedVariables false


namespace F

theorem slice_set (s : FSlice Int) (h1 : i.toNat < l.toNat ∨ i.toNat > r.toNat) (h2 : l.toNat <= r.toNat)
  : ringbuffer_fslice_subslice (ringbuffer_fslice_set s i e) l r = ringbuffer_fslice_subslice s l r := by
    grind [List.drop_set, List.take_set_of_le]

theorem add_one_sub (h : l <= r) : r + 1 - l = (r - l) + 1 := by omega

theorem slice_set_push (s : FSlice Int) (h1 : r < s.length) (h2 : l.toNat ≤ r)
  : ringbuffer_fslice_subslice (ringbuffer_fslice_set s r e) l (r + 1) = ringbuffer_fslice_subslice s l r ++ [e] := by
    simp [ringbuffer_fslice_subslice, ringbuffer_fslice_set]
    rw [add_one_sub]
    rw [List.take_add_one]
    simp_all
    grind [List.drop_set, List.take_set_of_le]
    assumption

theorem slice00 (s : FSlice Int)
  : ringbuffer_fslice_subslice s 0 0 = [] := by grind

def RingbufferVecQueuePushCorrect_proof : RingbufferVecQueuePushCorrect := by
  unfold RingbufferVecQueuePushCorrect
  intro rb vq elem vqeq c1 c2 success nrb _ _ seq nrbeq successHyp
  rw [seq] at successHyp
  rw [if_pos successHyp] at nrbeq
  have nrbtleq : nrb.tl = (rb.tl + 1) % (ringbuffer_fslice_len rb.elems) := by rw [nrbeq]
  have nrbringeq : nrb.elems = ringbuffer_fslice_set rb.elems rb.tl elem := by rw [nrbeq]
  by_cases hdgttl : nrb.hd > nrb.tl
  · rw [if_pos hdgttl]
    by_cases h : rb.hd > rb.tl
    · rw [if_pos h] at vqeq
      rw [vqeq]
      unfold ringbuffer_fslice_append ringbuffer_fslice_push
      have heq : ringbuffer_fslice_subslice nrb.elems nrb.hd (ringbuffer_fslice_len nrb.elems) = ringbuffer_fslice_subslice rb.elems rb.hd (ringbuffer_fslice_len rb.elems) := by
        grind [slice_set]
      rw [List.append_assoc, heq, List.append_cancel_left_eq]
      have htl : nrb.tl = rb.tl + 1 := by
        grind [←Int.emod_eq_of_lt]
      rw [htl, nrbringeq]
      grind [slice_set_push]
    · by_cases h' : rb.tl = ringbuffer_fslice_len rb.elems - 1
      · have htl : nrb.tl = 0 := by
          rw [nrbtleq, h'] ; simp
        rw [htl]
        rw [if_neg h] at vqeq
        simp at h
        have foo : ringbuffer_fslice_len rb.elems = ringbuffer_fslice_len nrb.elems := by grind
        rw [vqeq, slice00, ringbuffer_fslice_append, ringbuffer_fslice_push, List.append_nil]
        rw [←foo, nrbringeq]
        conv => rhs ; arg 3 ; rw [←Int.sub_add_cancel (ringbuffer_fslice_len rb.elems) 1]
        rw [←h']
        grind [slice_set_push]
      · have htl : nrb.tl = rb.tl + 1 := by
          rw [nrbtleq]
          apply Int.emod_eq_of_lt
          omega
          omega
        grind
  · rw [if_neg hdgttl]
    by_cases h : rb.hd > rb.tl
    · rw [if_pos h] at vqeq
      by_cases h'' : rb.tl = ringbuffer_fslice_len rb.elems - 1
      · grind
      · rw [vqeq]
        have htl : nrb.tl = rb.tl + 1 := by grind [←Int.emod_eq_of_lt]
        rw [htl, nrbringeq]
        grind
    · rw [if_neg h] at vqeq
      rw [vqeq]
      simp at h
      by_cases h'' : rb.tl = ringbuffer_fslice_len rb.elems - 1
      · simp [*] at * ; grind
      · have htl : nrb.tl = rb.tl + 1 := by
          simp_all ; grind [←Int.emod_eq_of_lt]
        rw [htl, nrbringeq, ringbuffer_fslice_push]
        grind [slice_set_push]

end F
