import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksortRange
import LeanProofs.Lib.Lemmas
import LeanFixpoint

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

theorem perm_widen_lo :
  sort_is_perm v a lo (p - 1) -> p ≤ hi -> sort_is_perm v a lo hi
  := by
  intro h hp; simp_all [sort_is_perm, is_perm, is_frame]; grind

theorem perm_widen_hi :
  sort_is_perm a b (p + 1) hi -> lo ≤ p -> sort_is_perm a b lo hi
  := by
  intro h hp; simp_all [sort_is_perm, is_perm, is_frame]; grind

end F

namespace F

theorem SortQuicksortRange_proof' : SortQuicksortRange := by
  unfold SortQuicksortRange
  fusion
  intro old₀ lo₀ hi₀ hlolen hhilen hlen hlo hhi
  refine ⟨?_, ?_⟩
  · -- base case: ¬ lo₀ < hi₀
    intro hnlt
    refine ⟨rfl, ?_, ?_⟩
    · simp [sort_is_sorted_between]; grind
    · apply sort_is_perm_id
  · -- recursive case: lo₀ < hi₀
    intro hlt p₀ v₀ hv₀ hv₀len hp₀
    obtain ⟨hv₀_len, hpart, hperm₀, hlop, hphi⟩ := hv₀
    refine ⟨?_, ?_⟩
    · intro hlolt; refine ⟨by omega, by omega, by omega⟩
    · intro a'₃ hbranch
      -- hbranch : (¬lo₀ < p₀ ∧ …) ∨ (lo₀ < p₀ ∧ ∃ v₁, …) — the lower-half recursive call result
      -- facts about a'₃ (result of sorting the lower half [lo₀, p₀))
      have ha3len : a'₃.len = old₀.len := by
        rcases hbranch with ⟨_, h⟩ | ⟨_, _, h⟩ <;> grind
      have ha3sorted : sort_is_sorted_between a'₃.elems lo₀ p₀ := by
        rcases hbranch with ⟨hn, h⟩ | ⟨_, vv, h⟩ <;> simp_all [sort_is_sorted_between]; grind
      have ha3p : a'₃.elems p₀ = v₀.elems p₀ := by
        rcases hbranch with ⟨_, h⟩ | ⟨_, vv, ⟨_, _, hpm⟩, _, h⟩ <;>
          (try simp only [sort_is_perm, is_frame] at hpm) <;> grind
      have ha3perm : sort_is_perm v₀.elems a'₃.elems lo₀ (p₀ - 1) := by
        rcases hbranch with ⟨_, h⟩ | ⟨_, vv, ⟨_, _, hpm⟩, _, h⟩ <;>
          simp only [sort_is_perm, is_perm, is_frame] at * <;> grind
      have ha3bigger : sort_is_bigger a'₃.elems lo₀ p₀ p₀ := bigger_perm hpart.1 ha3perm
      have ha3smaller : sort_is_smaller a'₃.elems p₀ (hi₀ + 1) p₀ := is_smaller_perm' hpart.2 ha3perm
      refine ⟨?_, ?_⟩
      · intro hph; exact ⟨by omega, by omega⟩
      · intro a'₅ hbr5
        have ha5len : a'₅.len = old₀.len := by
          rcases hbr5 with ⟨_, h⟩ | ⟨_, vv, h⟩ <;> grind
        have ha5sorted_hi : sort_is_sorted_between a'₅.elems (p₀ + 1) (hi₀ + 1) := by
          rcases hbr5 with ⟨hn, h⟩ | ⟨_, vv, h⟩ <;> simp_all [sort_is_sorted_between]; grind
        have ha5perm : sort_is_perm a'₃.elems a'₅.elems (p₀ + 1) hi₀ := by
          rcases hbr5 with ⟨_, h⟩ | ⟨_, vv, ⟨_, _, hpm⟩, _, h⟩ <;>
            (try simp only [sort_is_perm, is_perm, is_frame] at hpm) <;>
            simp only [sort_is_perm, is_perm, is_frame] <;> grind
        -- a'₅ agrees with a'₃ on the lower half (frame of the upper-half sort)
        have hframe5 : ∀ i, i < p₀ + 1 → a'₅.elems i = a'₃.elems i := by
          have h := ha5perm; simp only [sort_is_perm, is_frame] at h; exact h.2.1
        have h11 : sort_is_smaller a'₅.elems p₀ (hi₀ + 1) p₀ := is_smaller_perm ha3smaller ha5perm
        have h_lo_p : sort_is_sorted_between a'₅.elems lo₀ p₀ := by
          intro i j hij
          rw [hframe5 i (by omega), hframe5 j (by omega)]; exact ha3sorted i j hij
        have h_p_bigger : sort_is_bigger a'₅.elems lo₀ p₀ p₀ := by
          intro ix hix
          rw [hframe5 ix (by omega), hframe5 p₀ (by omega)]; exact ha3bigger ix hix
        refine ⟨ha5len, is_sorted_using_pivot h_lo_p ha5sorted_hi h_p_bigger h11, ?_⟩
        exact sort_is_perm_trans hperm₀
          (sort_is_perm_trans (perm_widen_lo ha3perm hphi) (perm_widen_hi ha5perm hlop))

end F
