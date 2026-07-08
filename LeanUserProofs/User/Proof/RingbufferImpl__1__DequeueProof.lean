import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__1__Dequeue
import Flex
open Classical
set_option linter.unusedVariables false


namespace F

private theorem mod_non_neg (a b : Int) : 0 < b -> 0 <= (a % b) := by
  intro h
  exact Int.emod_nonneg a (by omega)

private theorem mod_lt (a b : Int) : 0 < b -> (a % b) < b := by
  intro h
  exact Int.emod_lt_of_pos a h

private theorem mod_silly (a b : Int) : 0 <= a -> 0 <= b -> a < b ->  (a % b) = a := by
  intro ha hb hab
  exact Int.emod_eq_of_lt ha hab

def RingbufferImpl__1__Dequeue_proof : RingbufferImpl__1__Dequeue := by
  unfold RingbufferImpl__1__Dequeue
  fusion
  simp_all
  repeat' (first | (intro) | apply And.intro | grind)
  · rename_i s hInv hL hH0 hHL hT0 hTL hLeq hHneT
    apply hInv s.hd hH0 hHL
    have hz : (s.hd + s.len - s.hd) % s.len = 0 := by
      have hzz : s.hd + s.len - s.hd = s.len := by omega
      rw [hzz]; exact Int.emod_self
    rw [hz]
    split <;> omega
  · rename_i old hInvOld hLOld hH0Old hHLOld hT0Old hTLOld hLeqOld hHneTOld
      s hInv hL hH0 hHL hT0 hTL hLeq hHneT
      hLenEq hHdEq hTlEq hInitEq hElemsEq hLge0 hLneZero a1 ha0 haL hPos
    have hb1 : 0 ≤ (s.hd + 1) % ringbuffer_fslice_len s.elems := mod_non_neg _ _ (by omega)
    have hb2 : (s.hd + 1) % ringbuffer_fslice_len s.elems < ringbuffer_fslice_len s.elems := mod_lt _ _ (by omega)
    apply hInv a1 ha0 (by omega)
    rw [hLeq]
    by_cases hc2 : s.hd + 1 = ringbuffer_fslice_len s.elems <;>
      by_cases hcA : s.hd ≤ a1 <;>
      by_cases hcB : s.hd + 1 ≤ a1
    all_goals
      first
      | (have hf1 : (s.hd + 1) % ringbuffer_fslice_len s.elems = 0 := by rw [hc2]; exact Int.emod_self)
      | (have hf1 : (s.hd + 1) % ringbuffer_fslice_len s.elems = s.hd + 1 :=
           mod_silly _ _ (by omega) (by omega) (by omega))
    all_goals
      first
      | (have hg0 : (a1 + ringbuffer_fslice_len s.elems - s.hd) % ringbuffer_fslice_len s.elems = a1 - s.hd := by
           have heqn : a1 + ringbuffer_fslice_len s.elems - s.hd
               = (a1 - s.hd) + ringbuffer_fslice_len s.elems * 1 := by omega
           rw [heqn, Int.add_mul_emod_self_left]
           exact mod_silly _ _ (by omega) (by omega) (by omega))
      | (have hg0 : (a1 + ringbuffer_fslice_len s.elems - s.hd) % ringbuffer_fslice_len s.elems
            = a1 + ringbuffer_fslice_len s.elems - s.hd :=
           mod_silly _ _ (by omega) (by omega) (by omega))
    all_goals
      first
      | (have hg1 : (a1 + ringbuffer_fslice_len s.elems - (s.hd + 1)) % ringbuffer_fslice_len s.elems
            = a1 - (s.hd + 1) := by
           have heqn : a1 + ringbuffer_fslice_len s.elems - (s.hd + 1)
               = (a1 - (s.hd + 1)) + ringbuffer_fslice_len s.elems * 1 := by omega
           rw [heqn, Int.add_mul_emod_self_left]
           exact mod_silly _ _ (by omega) (by omega) (by omega))
      | (have hg1 : (a1 + ringbuffer_fslice_len s.elems - (s.hd + 1)) % ringbuffer_fslice_len s.elems
            = a1 + ringbuffer_fslice_len s.elems - (s.hd + 1) :=
           mod_silly _ _ (by omega) (by omega) (by omega))
    all_goals
      (rw [hg1, hf1] at hPos
       rw [hg0]
       (try split at hPos) <;> (try split) <;> omega)
  · apply Int.emod_nonneg
    grind
  · apply Int.emod_lt_of_pos
    grind

end F
