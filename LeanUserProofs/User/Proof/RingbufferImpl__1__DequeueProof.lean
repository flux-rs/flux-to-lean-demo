import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__1__Dequeue
import LeanFixpoint
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

def RingbufferImpl__1__Dequeue_proof : RingbufferImpl__1__Dequeue := by
  unfold RingbufferImpl__1__Dequeue
  fusion
  simp_all
  repeat' (first | (intro) | apply And.intro | grind)
  · apply_assumption <;> simp_all [Int.add_comm]
    omega
  · rename_i s₀ hInv hL hH0 hHL hT0 hTL hHneT hLge hLne a'₁ ha0 haL hPos
    have hb1 : 0 ≤ (s₀.hd + 1) % s₀.len := mod_non_neg _ _ hL
    have hb2 : (s₀.hd + 1) % s₀.len < s₀.len := mod_lt _ _ hL
    apply hInv a'₁ ha0 haL
    by_cases hc2 : s₀.hd + 1 = s₀.len <;>
      by_cases hcA : s₀.hd ≤ a'₁ <;>
      by_cases hcB : s₀.hd + 1 ≤ a'₁
    all_goals
      first
      | (have hf1 : (s₀.hd + 1) % s₀.len = 0 := by rw [hc2]; exact Int.emod_self)
      | (have hf1 : (s₀.hd + 1) % s₀.len = s₀.hd + 1 :=
           mod_silly _ _ (by omega) (by omega) (by omega))
    all_goals
      first
      | (have hg0 : (a'₁ + s₀.len - s₀.hd) % s₀.len = a'₁ - s₀.hd := by
           have heqn : a'₁ + s₀.len - s₀.hd = (a'₁ - s₀.hd) + s₀.len * 1 := by omega
           rw [heqn, Int.add_mul_emod_self_left]
           exact mod_silly _ _ (by omega) (by omega) (by omega))
      | (have hg0 : (a'₁ + s₀.len - s₀.hd) % s₀.len = a'₁ + s₀.len - s₀.hd :=
           mod_silly _ _ (by omega) (by omega) (by omega))
    all_goals
      first
      | (have hg1 : (a'₁ + s₀.len - (s₀.hd + 1)) % s₀.len
            = a'₁ - (s₀.hd + 1) := by
           have heqn : a'₁ + s₀.len - (s₀.hd + 1)
               = (a'₁ - (s₀.hd + 1)) + s₀.len * 1 := by omega
           rw [heqn, Int.add_mul_emod_self_left]
           exact mod_silly _ _ (by omega) (by omega) (by omega))
      | (have hg1 : (a'₁ + s₀.len - (s₀.hd + 1)) % s₀.len
            = a'₁ + s₀.len - (s₀.hd + 1) :=
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
