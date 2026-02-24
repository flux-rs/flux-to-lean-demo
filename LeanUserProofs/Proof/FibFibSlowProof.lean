import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibSlow
import LeanProofs.User.Proof.Tactics

namespace F

def FibFibSlow_proof : FibFibSlow := by
  unfold FibFibSlow
  zap

-- For reference...

def FibFibSlow_claude_proof : FibFibSlow := by
  unfold FibFibSlow
  intro n₀ hn₀
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Int.not_le]
  constructor
  · -- Case: n₀ > 1
    intro hgt
    constructor
    · omega
    · intro _
      constructor
      · omega
      · intro _
        have h : ¬(n₀ ≤ 1) := by omega
        conv => rhs; unfold fib_spec_fib
        simp only [if_neg h]
  · -- Case: n₀ ≤ 1
    intro hle
    conv => rhs; unfold fib_spec_fib
    simp only [if_pos hle]

end F
