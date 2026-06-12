import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSqrt
-- import LeanProofs.Lib.Tactics
import LeanFixpoint

namespace F


@[qualif] def q_nonneg    (v : Int)   : Prop := 0 ≤ v                       -- ↦ 0≤i, 0≤x
@[qualif] def q_predsq_le (a b : Int) : Prop := (a - 1) * (a - 1) ≤ b       -- ↦ (i-1)²≤x   ← the key one
@[qualif] def q_sq_le     (a b : Int) : Prop := a * a ≤ b                   -- ↦ i²≤x
@[qualif] def q_sq_gt     (a b : Int) : Prop := a * a > b

def FibSqrt_proof : FibSqrt := by
  unfold FibSqrt
  fixpoint

end F
