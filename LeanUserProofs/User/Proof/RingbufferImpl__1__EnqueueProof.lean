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
  zapNamed
  · rename_i hInv hBounds hHneT hHge hTge hLge hLne hIn hPos
    obtain ⟨hL, hH0, hHL, hT0, hTL⟩ := hBounds
    by_cases heq : a'₂ = s₀.tl
    · subst heq
      simp [SmtMap_store, SmtMap_select]
    · have hsel : SmtMap_select (SmtMap_store s₀.init s₀.tl True) a'₂ = SmtMap_select s₀.init a'₂ := by
        simp [SmtMap_store, SmtMap_select, heq]
      rw [hsel]
      dsimp only at hIn
      obtain ⟨ha0, haL⟩ := hIn
      apply hInv a'₂ ⟨ha0, haL⟩
      dsimp only at hPos ⊢
      by_cases hc1 : s₀.hd ≤ a'₂ <;> by_cases hc2 : s₀.tl + 1 = s₀.len
      · have hg : (a'₂ + s₀.len - s₀.hd) % s₀.len = a'₂ - s₀.hd := by
          have heqn : a'₂ + s₀.len - s₀.hd = (a'₂ - s₀.hd) + s₀.len * 1 := by omega
          rw [heqn, Int.add_mul_emod_self_left]
          exact mod_silly _ _ (by omega) (by omega) (by omega)
        have hf : (s₀.tl + 1) % s₀.len = 0 := by rw [hc2]; exact Int.emod_self
        rw [hg] at hPos ⊢
        rw [hf] at hPos
        (try split at hPos) <;> (try split) <;> omega
      · have hg : (a'₂ + s₀.len - s₀.hd) % s₀.len = a'₂ - s₀.hd := by
          have heqn : a'₂ + s₀.len - s₀.hd = (a'₂ - s₀.hd) + s₀.len * 1 := by omega
          rw [heqn, Int.add_mul_emod_self_left]
          exact mod_silly _ _ (by omega) (by omega) (by omega)
        have hf : (s₀.tl + 1) % s₀.len = s₀.tl + 1 :=
          mod_silly _ _ (by omega) (by omega) (by omega)
        rw [hg] at hPos ⊢
        rw [hf] at hPos
        (try split at hPos) <;> (try split) <;> omega
      · have hg : (a'₂ + s₀.len - s₀.hd) % s₀.len = a'₂ + s₀.len - s₀.hd :=
          mod_silly _ _ (by omega) (by omega) (by omega)
        have hf : (s₀.tl + 1) % s₀.len = 0 := by rw [hc2]; exact Int.emod_self
        rw [hg] at hPos ⊢
        rw [hf] at hPos
        (try split at hPos) <;> (try split) <;> omega
      · have hg : (a'₂ + s₀.len - s₀.hd) % s₀.len = a'₂ + s₀.len - s₀.hd :=
          mod_silly _ _ (by omega) (by omega) (by omega)
        have hf : (s₀.tl + 1) % s₀.len = s₀.tl + 1 :=
          mod_silly _ _ (by omega) (by omega) (by omega)
        rw [hg] at hPos ⊢
        rw [hf] at hPos
        (try split at hPos) <;> (try split) <;> omega
  · apply Int.emod_nonneg
    grind
  · apply Int.emod_lt_of_pos
    grind

end F
