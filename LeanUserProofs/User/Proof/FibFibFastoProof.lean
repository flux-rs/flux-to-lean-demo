import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFasto
import Flex
open Classical
set_option linter.unusedVariables false


namespace F

@[qualif] private def q_nat (a : Int) : Prop := 0 ≤ a
@[qualif] private def q_le (a b : Int) : Prop := a ≤ b
@[qualif] private def q_gt_one (v : Int) : Prop := v > 1
@[qualif] private def q_eq_fib (v i : Int) : Prop := v = fib_spec_fib i
@[qualif] private def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)

theorem spec_fib_mono: ∀ (i j : Int), 0 ≤ i → 0 ≤ j → i ≤ j → fib_spec_fib i ≤ fib_spec_fib j := by
  intros i j hi hj hij
  induction j using fib_spec_fib.induct generalizing i with grind

def FibFibFasto_proof : FibFibFasto := by
  unfold FibFibFasto
  solve_fixpoint
  have _ : fib_spec_fib (i₀ + 1) <= fib_spec_fib n₀ := by apply spec_fib_mono <;> grind
  grind

end F
