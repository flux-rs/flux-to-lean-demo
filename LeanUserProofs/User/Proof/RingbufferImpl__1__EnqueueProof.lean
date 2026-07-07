import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__1__Enqueue
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

theorem mod_silly (a b : Int) : 0 <= a -> 0 <= b -> a < b ->  (a % b) = a := by
  intro ha hb hab
  exact Int.emod_eq_of_lt ha hab

theorem RingbufferImpl__1__Enqueue_proof : RingbufferImpl__1__Enqueue := by
  unfold RingbufferImpl__1__Enqueue
  zapNamed <;> simp_all
  · rename_i hInv hBounds hHneT hHge hTge hLeq hLge0 hLneZero hIn hPos
    intro hne
    apply hInv a'₁ hIn.1 hIn.2
    by_cases hc1 : s₀.hd ≤ a'₁ <;> by_cases hc2 : s₀.tl + 1 = ringbuffer_fslice_len s₀.elems
    · have hg : (a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd) % ringbuffer_fslice_len s₀.elems = a'₁ - s₀.hd := by
        have heqn : a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd
            = (a'₁ - s₀.hd) + ringbuffer_fslice_len s₀.elems * 1 := by omega
        rw [heqn, Int.add_mul_emod_self_left]
        exact mod_silly _ _ (by omega) (by omega) (by omega)
      have hf : (s₀.tl + 1) % ringbuffer_fslice_len s₀.elems = 0 := by rw [hc2]; exact Int.emod_self
      rw [hg]
      rw [hf] at hPos
      (try split at hPos) <;> (try split) <;> omega
    · have hg : (a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd) % ringbuffer_fslice_len s₀.elems = a'₁ - s₀.hd := by
        have heqn : a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd
            = (a'₁ - s₀.hd) + ringbuffer_fslice_len s₀.elems * 1 := by omega
        rw [heqn, Int.add_mul_emod_self_left]
        exact mod_silly _ _ (by omega) (by omega) (by omega)
      have hf : (s₀.tl + 1) % ringbuffer_fslice_len s₀.elems = s₀.tl + 1 :=
        mod_silly _ _ (by omega) (by omega) (by omega)
      rw [hg]
      rw [hf] at hPos
      (try split at hPos) <;> (try split) <;> omega
    · have hg : (a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd) % ringbuffer_fslice_len s₀.elems
          = a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd :=
        mod_silly _ _ (by omega) (by omega) (by omega)
      have hf : (s₀.tl + 1) % ringbuffer_fslice_len s₀.elems = 0 := by rw [hc2]; exact Int.emod_self
      rw [hg]
      rw [hf] at hPos
      (try split at hPos) <;> (try split) <;> omega
    · have hg : (a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd) % ringbuffer_fslice_len s₀.elems
          = a'₁ + ringbuffer_fslice_len s₀.elems - s₀.hd :=
        mod_silly _ _ (by omega) (by omega) (by omega)
      have hf : (s₀.tl + 1) % ringbuffer_fslice_len s₀.elems = s₀.tl + 1 :=
        mod_silly _ _ (by omega) (by omega) (by omega)
      rw [hg]
      rw [hf] at hPos
      (try split at hPos) <;> (try split) <;> omega
  · apply Int.emod_nonneg
    grind
  · apply Int.emod_lt_of_pos
    grind

end F
