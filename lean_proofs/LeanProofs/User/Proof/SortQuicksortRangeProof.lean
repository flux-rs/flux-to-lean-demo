import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksortRange
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics
-- import Aesop
open Classical

namespace F

theorem bigger_perm :
  sort_is_bigger a lo p p -> sort_is_perm a a' lo (p-1) -> sort_is_bigger a' lo p p
  := by
  intros; simp_all [sort_is_bigger, sort_is_perm, is_perm, is_frame]; grind

theorem sort_is_perm_trans :
  sort_is_perm old new lo hi -> sort_is_perm new new' lo hi -> sort_is_perm old new' lo hi
  := by
  intros; simp_all [sort_is_perm, is_perm, is_frame]; grind


theorem sort_is_perm_id : sort_is_perm arr arr lo hi := by
  intros; simp_all [sort_is_perm, is_perm, is_frame]; intros i _ _; exists i

theorem is_perm_trans :
  is_perm old new lo hi -> is_perm new new' lo hi -> is_perm old new' lo hi
  := by
  intros; simp_all [is_perm]; grind

theorem is_perm_id : is_perm arr arr lo hi := by
  intros; simp_all [is_perm]; intros i _ _; exists i

-- theorem is_smaller_perm :
--   sort_is_smaller a lo p p -> sort_is_perm a a' lo (p-1) -> sort_is_smaller a' lo p p
--   := by
--   intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_smaller_perm' :
  sort_is_smaller a p hi p -> sort_is_perm a a' lo (p - 1) -> sort_is_smaller a' p hi p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_smaller_perm :
  sort_is_smaller a1 p (hi + 1) p -> sort_is_perm a1 a2 (p + 1) hi -> sort_is_smaller a2 p (hi + 1) p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_sorted_using_pivot :
  sort_is_sorted_between a lo p ->
  sort_is_sorted_between a (p + 1) (hi + 1) ->
  sort_is_bigger a lo p p ->
  sort_is_smaller a p (hi + 1) p ->
  sort_is_sorted_between a lo (hi + 1)
  := by
  simp_all [sort_is_smaller, sort_is_bigger, sort_is_sorted_between]; grind

end F

namespace F

def qs_k1 (p : Int) (_hi : Int) (a1 a0 : VectorsAVec Int) (lo : Int) (old : VectorsAVec Int) (_a2_elems : Arr Int) (a2_len : Int) (_ : Arr Int) (_ : Int) (_ _ _ : Int) (_ : Arr Int) (_ : Int) (_ : Arr Int) (_ : Int) : Prop :=
  a0.len = old.len /\ a1.len = old.len /\ a2_len = old.len /\
  sort_is_sorted_between a1.elems lo p /\
  is_perm a0.elems a1.elems lo p /\
  a1.elems p = a0.elems p /\
  sort_is_smaller a1.elems lo p (a1.elems p)

open SortQuicksortRangeKVarSolutions in

def SortQuicksortRange_proof : SortQuicksortRange := by
  unfold SortQuicksortRange
  exists k0; exists k1;
  zap
  . simp [sort_is_sorted_between]; grind
  . simp [is_perm]; grind
  . simp_all [k0]
  . grind [k0]
  . -- k1
    sorry
  . grind [k0]
  . grind [k0]
  . -- k1
    sorry
  . simp_all [k1]; grind
  . -- sorted_between
    rename_i old lo hi _ _ _ _ _ _ p a0 hyp0 _ _ a1 hyp1 a2 hyp2
    have h_lo_p : sort_is_sorted_between a2.elems lo p := by
      have h0 : sort_is_sorted_between a1.elems lo p := by
        rw [k0] at hyp1; split_hyp_ors
        . rename_i hh; obtain ⟨_ , _⟩ := hh; grind
        . grind [sort_is_sorted_between]
      simp_all [k1, sort_is_perm, is_frame, is_perm]; grind

    have h_p_bigger : sort_is_bigger a2.elems lo p p := by
      have h3 : sort_is_bigger a0.elems lo p p       := by
        simp_all [k0]
      have h4 : sort_is_bigger a1.elems lo p p       := by
        simp_all [k0, sort_is_perm, is_frame, is_perm]; grind
      simp_all [k1, sort_is_perm, is_frame, is_perm]; grind

    have h_p_hi : sort_is_sorted_between a2.elems (p + 1) (hi + 1) := by
      simp_all [k1]; grind

    have h8 : a1.elems p = a0.elems p := by
      rw [k0] at hyp1; split_hyp_ors
      . rename_i hh
        obtain ⟨ ⟨ arr1' , hh' ⟩ , _⟩ := hh
        grind [sort_is_perm, is_perm, is_frame]
      . grind
    have h9 : sort_is_perm a0.elems a1.elems lo (p - 1) := by
      rw [k0] at hyp1; split_hyp_ors
      . rename_i hh
        obtain ⟨ ⟨ a1' , ⟨ _, hh', _ ⟩ ⟩ , _⟩ := hh
        have eq_els : a1.elems = a1'.elems := by grind
        rw [eq_els]
        assumption
      . have eq_els : a1.elems = a0.elems := by grind
        rw [eq_els]
        apply sort_is_perm_id

    have h7 : sort_is_smaller a0.elems p (hi + 1) p := by
      rw [sort_is_partitioned_by] at hyp0; grind
    have h10 : sort_is_smaller a1.elems p (hi + 1) p := by
      rw [k0] at hyp1; split_hyp_ors
      . rename_i hh
        obtain ⟨ ⟨ a1' , hh' ⟩ , _⟩ := hh
        have eq_els : a1.elems = a1'.elems := by grind
        rw [eq_els]
        obtain ⟨ _ , ⟨ hh2, _ ⟩⟩ := hh'
        apply is_smaller_perm'
        apply h7
        apply hh2
      . grind
    have h11 : sort_is_smaller a2.elems p (hi + 1) p := by
      rw [k1] at hyp2; split_hyp_ors
      . rename_i hh
        obtain ⟨ ⟨ a2', hh' ⟩ , _⟩ := hh
        apply is_smaller_perm
        . apply h10
        . grind
      . grind
    apply is_sorted_using_pivot <;> assumption
  . -- is_perm
    rename_i old lo hi _ _ _ _ _ _ p a0 _ _ _ a1 _ a2 _
    have h0 : is_perm old.elems a0.elems lo hi := by simp_all [sort_is_perm]
    have h01 : is_perm a0.elems a1.elems lo hi := by simp_all [k0, sort_is_perm, is_perm, is_frame]; grind
    have h1 : is_perm old.elems a1.elems lo hi := by apply is_perm_trans; apply h0; assumption
    have h12 : is_perm a1.elems a2.elems lo hi := by simp_all [k1, sort_is_perm, is_perm, is_frame]; grind
    have h2 : is_perm old.elems a2.elems lo hi := by apply is_perm_trans; apply h1; assumption
    assumption
  . simp_all [k1, sort_is_perm, is_frame]; grind
  . simp_all [k1, sort_is_perm, is_frame]; grind



end F
