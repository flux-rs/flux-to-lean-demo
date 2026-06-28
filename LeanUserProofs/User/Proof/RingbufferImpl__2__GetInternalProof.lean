import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__GetInternal
import LeanFixpoint
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false

namespace F

def RingbufferImpl__2__GetInternal_proof: RingbufferImpl__2__GetInternal := by
  unfold RingbufferImpl__2__GetInternal
  fusion
  intros s0 index0 ix_len inv_hyp enq_len_hyp inv0 idx_nonneg
  constructor
  · intro hC _ _
    simp [hC]
  · intro hC _ _
    by_cases h : s0.num_enqueues < s0.len
    · by_cases hd_eq_tl : s0.hd = s0.tl
      · exfalso
        rw [hd_eq_tl] at hC
        rw [if_neg (show ¬ s0.tl > s0.tl by omega), if_neg (show ¬ s0.tl < s0.tl by omega)] at hC
        have hmod : 0 ≤ (index0 + s0.len - s0.tl) % s0.len := Int.emod_nonneg _ (by omega)
        omega
      · have hd_lt_tl : s0.hd < s0.tl := by omega
        rw [if_pos hd_lt_tl] at hC
        by_cases hge : index0 ≥ s0.hd
        · have hrw : index0 + s0.len - s0.hd = (index0 - s0.hd) + s0.len * 1 := by omega
          rw [hrw, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)] at hC
          grind
        · grind
    · grind

end F
