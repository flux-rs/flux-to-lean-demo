import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__Dequeue
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

def RingbufferImpl__2__Dequeue_proof : RingbufferImpl__2__Dequeue := by
  unfold RingbufferImpl__2__Dequeue
  zapNamed
  · have heq : (old₀.hd + 1) % old₀.len = old₀.hd + 1 := by apply mod_silly <;> omega
    omega
  · apply mod_non_neg; omega
  · apply mod_lt; omega
  · have hrw : old₀.hd + old₀.len - old₀.hd = old₀.len := by omega
    rw [hrw, Int.emod_self]
    by_cases h : old₀.hd = old₀.tl
    · simp [h]
    · by_cases htgt : old₀.tl > old₀.hd
      · simp [h, htgt]
      · have htlt : old₀.tl < old₀.hd := by omega
        simp [h, htgt, htlt]
        omega

end F
