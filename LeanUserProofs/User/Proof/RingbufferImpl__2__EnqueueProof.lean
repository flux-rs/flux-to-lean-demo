import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__Enqueue
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

def RingbufferImpl__2__Enqueue_proof : RingbufferImpl__2__Enqueue := by
  unfold RingbufferImpl__2__Enqueue
  zapNamed
  · obtain ⟨htl, _⟩ := ‹s₀.num_enqueues < s₀.len → s₀.tl = s₀.num_enqueues ∧ s₀.hd ≤ s₀.tl› (by omega)
    rw [htl]
    apply mod_silly <;> omega
  · obtain ⟨htl, hhd⟩ := ‹s₀.num_enqueues < s₀.len → s₀.tl = s₀.num_enqueues ∧ s₀.hd ≤ s₀.tl› (by omega)
    have heq : (s₀.tl + 1) % s₀.len = s₀.num_enqueues + 1 := by rw [htl]; apply mod_silly <;> omega
    omega
  · apply mod_non_neg; omega
  · apply mod_lt; omega
end F
