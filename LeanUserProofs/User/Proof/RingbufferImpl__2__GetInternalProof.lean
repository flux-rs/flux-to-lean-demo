import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__GetInternal
import LeanFixpoint
-- import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def RingbufferImpl__2__GetInternal_proof: RingbufferImpl__2__GetInternal := by
  unfold RingbufferImpl__2__GetInternal
  intros s0 index0
  intros _ _ _ _ _
  and_intros
  . and_intros
    intros _ _ _
    grind
  . intros _ _ _
    rename_i ix_len inv_hyp enq_len_hyp _ _ _ _ _
    by_cases h : s0.num_enqueues < s0.len
    . simp_all []
      apply inv_hyp
      . grind
      . obtain ⟨ h1a, h1b ⟩ := enq_len_hyp
        simp_all []
        by_cases hd_enq : s0.hd = s0.num_enqueues
        . simp_all []
          have h_nn : 0 ≤ (index0 + s0.len - s0.num_enqueues) % s0.len :=
            Int.emod_nonneg _ (by omega)
          omega
        . have _ : s0.hd < s0.num_enqueues := by omega
          simp_all
          rename_i _ _ h_mod _ _
          by_cases h_idx_hd : index0 ≥ s0.hd
          · have hrw : index0 + s0.len - s0.hd = (index0 - s0.hd) + s0.len * 1 := by omega
            rw [hrw, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)] at h_mod
            omega
          · exfalso
            rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_mod
            omega
    . simp only [ringbuffer_init_inv, SmtMap_select, my_min] at inv_hyp ⊢
      apply inv_hyp
      constructor
      · omega
      · simp only [show ¬(s0.num_enqueues < s0.len) from h, ite_false]
        omega

end F
