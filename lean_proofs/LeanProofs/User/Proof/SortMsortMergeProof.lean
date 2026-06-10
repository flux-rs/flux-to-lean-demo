import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMsortMerge
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

theorem sort_subseq:
  sort_is_sorted_between a lo hi ->
  lo <= lo' ->
  hi' <= hi ->
  sort_is_sorted_between a lo' hi'
  := by
  simp_all [sort_is_sorted_between]
  zapNamed


theorem sort_extend :
  sort_is_sorted_between a lo hi ->
  sort_all_smaller a lo hi b ii jj ->
  ii < jj ->
  sort_is_sorted_between (vectors_arr_set a hi (vectors_arr_get b ii))  lo (hi + 1)
  := by
  simp_all [sort_is_sorted_between, sort_all_smaller]
  zapNamed
  rename_i hyp_sorted hyp_smaller _ _ _ _
  by_cases i = hi
  . by_cases j = hi <;> grind
  . by_cases j = hi
    . have _ : a i <= b ii := by apply hyp_smaller <;> grind
      grind
    . grind

theorem smaller_extend :
  sort_is_sorted_between a lo hi ->
  sort_is_sorted_between b ii jj ->
  sort_all_smaller a lo hi b ii jj ->
  ii < jj ->
  sort_all_smaller (vectors_arr_set a hi (vectors_arr_get b ii))  lo (hi + 1) b (ii + 1) jj
  := by
  simp_all [sort_is_sorted_between, sort_all_smaller]
  zapNamed
  rename_i h_sort_a h_sort_b h_smaller _ _ _ _ _
  by_cases i = hi
  . by_cases j = hi <;> grind
  . by_cases j = hi
    . simp_all; apply h_smaller <;> grind
    . simp_all; apply h_smaller <;> grind

theorem smaller_extend' :
  sort_is_sorted_between a lo hi ->
  sort_is_sorted_between b ii jj ->
  sort_all_smaller a lo hi b ii jj ->
  ii < jj ->
  v <= vectors_arr_get b ii ->
  sort_all_smaller (vectors_arr_set a hi v) lo (hi + 1) b ii jj
  := by
  simp_all [sort_is_sorted_between, sort_all_smaller]
  zapNamed
  rename_i h_sort_a h_sort_b h_smaller _ _ _ _ _ _
  by_cases i = hi <;> try simp_all
  . by_cases j = ii <;> try simp_all
    have _ : b ii <= b j := by apply h_sort_b <;> grind
    grind
  . by_cases j = ii <;> try simp_all
    . apply h_smaller <;> grind
    . apply h_smaller <;> grind

theorem subset_extend :
   src_lo <= src_hi ->
   dst_lo <= dst_hi ->
   sort_is_subset src src_lo src_hi dst dst_lo dst_hi ->
   sort_is_subset src src_lo (src_hi + 1) (vectors_arr_set dst dst_hi (vectors_arr_get src src_hi)) dst_lo (dst_hi + 1)
   := by
   simp_all [sort_is_subset]
   intros _ _ h_subset
   zapNamed
   by_cases i = src_hi <;> try simp_all
   . exists dst_hi; grind
   . have hj : ∃ j, dst_lo ≤ j ∧ j < dst_hi ∧ src i = dst j := by apply h_subset <;> grind
     grind

theorem subset_extend' :
   src_lo <= src_hi ->
   dst_lo <= dst_hi ->
   sort_is_subset src src_lo src_hi dst dst_lo dst_hi ->
   sort_is_subset src src_lo src_hi (vectors_arr_set dst dst_hi v) dst_lo (dst_hi + 1)
   := by
   simp_all [sort_is_subset]
   intros _ _ h_subset
   zapNamed


def SortMsortMerge_proof : SortMsortMerge := by
  unfold SortMsortMerge
  exists SortMsortMergeKVarSolutions.k0
  zapNamed

  . apply sort_extend <;> (first | grind | assumption)

  . rename_i bob _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    apply smaller_extend <;> (try grind)
    apply (sort_subseq bob) <;> grind

  . rename_i _ bob _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    apply smaller_extend' <;> (try grind)
    apply (sort_subseq bob) <;> grind

  . sorry
  . sorry
  . sorry

  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry

end F
