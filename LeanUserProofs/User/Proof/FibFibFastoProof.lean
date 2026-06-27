import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFasto
import LeanFixpoint
open Classical
set_option linter.unusedVariables false


namespace F

@[qualif] def q_nat (a : Int) : Prop := 0 ≤ a
@[qualif] def q_le (a b : Int) : Prop := a ≤ b
@[qualif] def q_gt_one (v : Int) : Prop := v > 1
@[qualif] def q_eq_fib (v i : Int) : Prop := v = fib_spec_fib i
@[qualif] def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)

theorem spec_fib_nat: ∀ (n : Int), 0 ≤ n → 0 <= fib_spec_fib n := by
  intro n hn
  induction n using fib_spec_fib.induct
  all_goals grind

-- srsly?
theorem spec_fib_mono: ∀ (i j : Int), 0 ≤ i → 0 ≤ j → i ≤ j → fib_spec_fib i ≤ fib_spec_fib j := by
  intro i j hi hj hij
  induction j using fib_spec_fib.induct generalizing i with
  | case1 j hj1 =>
      have hij1 : i ≤ 1 := by omega
      have hj_eq : j = 0 ∨ j = 1 := by omega
      have hi_eq : i = 0 ∨ i = 1 := by omega
      rcases hj_eq with rfl | rfl <;> rcases hi_eq with rfl | rfl <;> simp [fib_spec_fib]
  | case2 j hj1 ih1 ih2 =>
      by_cases hijm1 : i ≤ j - 1
      · have hstep : fib_spec_fib i ≤ fib_spec_fib (j - 1) := ih1 i hi (by omega) hijm1
        have hnonneg : 0 ≤ fib_spec_fib (j - 2) := spec_fib_nat (j - 2) (by omega)
        have hj_expand : fib_spec_fib j = fib_spec_fib (j - 1) + fib_spec_fib (j - 2) := by
          rw [fib_spec_fib.eq_1]
          simp [hj1]
        rw [hj_expand]
        omega
      · have hij_eq : i = j := by omega
        simp [hij_eq]

def FibFibFasto_proof : FibFibFasto := by
  unfold FibFibFasto
  solve_fixpoint
  have _ : fib_spec_fib (i₀ + 1) <= fib_spec_fib n₀ := by apply spec_fib_mono <;> grind
  grind

end F
