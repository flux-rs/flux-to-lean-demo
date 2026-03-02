import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast
import LeanProofs.Lib.Tactics

namespace F

-- Loop invariant: i > 1 ∧ i ≤ n ∧ prev = fib(i-1) ∧ curr = fib(i)
@[simp]
def fib_fast_inv (i : Int) (prev : Int) (curr : Int) (n : Int) : Prop :=
  i > 1 ∧ i ≤ n ∧ prev = fib_spec_fib (i - 1) ∧ curr = fib_spec_fib i

def FibFibFast_proof : FibFibFast := by
  unfold FibFibFast; exists fib_fast_inv; simp
  zap


def FibFibFast_claude_proof : FibFibFast := by
  unfold FibFibFast
  exists fib_fast_inv
  intro n₀ hn₀
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Int.not_le, Int.not_lt]
  constructor
  · -- Case: n₀ > 1
    intro hgt
    constructor
    · -- Initial: fib_fast_inv 2 1 2 n₀
      simp only [fib_fast_inv]
      constructor
      · omega
      constructor
      · omega
      constructor
      · -- 1 = fib_spec_fib 1
        conv => rhs; unfold fib_spec_fib
        simp
      · -- 2 = fib_spec_fib 2
        conv => rhs; unfold fib_spec_fib
        simp only [Int.reduceLE, ↓reduceIte]
        conv => rhs; rhs; unfold fib_spec_fib
        conv => rhs; lhs; unfold fib_spec_fib
        simp
    · -- Loop body
      intro i₀ prev₀ curr₀ hinv
      simp only [fib_fast_inv] at hinv
      obtain ⟨hi_gt, hi_le, hprev, hcurr⟩ := hinv
      constructor
      · -- Post-condition: i₀ ≥ n₀ → curr₀ = fib_spec_fib n₀
        intro hexit
        have hi_eq : i₀ = n₀ := by omega
        rw [hi_eq] at hcurr
        exact hcurr
      · -- Preservation: i₀ < n₀ → fib_fast_inv (i₀+1) curr₀ (prev₀+curr₀) n₀
        intro hcont
        simp only [fib_fast_inv]
        constructor
        · omega
        constructor
        · omega
        constructor
        · -- curr₀ = fib_spec_fib ((i₀+1) - 1) = fib_spec_fib i₀
          simp only [Int.add_sub_cancel]
          exact hcurr
        · -- prev₀ + curr₀ = fib_spec_fib (i₀+1)
          conv => rhs; unfold fib_spec_fib
          have h : ¬(i₀ + 1 ≤ 1) := by omega
          simp only [h, ↓reduceIte]
          have heq1 : i₀ + 1 - 1 = i₀ := by omega
          have heq2 : i₀ + 1 - 2 = i₀ - 1 := by omega
          simp only [heq1, heq2]
          rw [hprev, hcurr]
          omega
  · -- Case: n₀ ≤ 1
    intro hle
    conv => rhs; unfold fib_spec_fib
    simp only [if_pos hle]

end F
