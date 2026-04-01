import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortPartition
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics

open Classical

namespace F

-- ((k1 j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->

@[reducible]
def inv (j: Int) (arr : Arr Int) (arr_len i : Int) (old_elems: Arr Int) (old_len lo hi: Int) :=
     arr_len == old_len
  /\ 0 <= lo /\ hi < arr_len /\ lo <= i /\ i <= hi
  /\ lo <= j /\ j <= hi
  /\ i <= j
  /\ old_elems hi == arr hi
  /\ sort_is_perm old_elems arr lo hi
  /\ (sort_is_partitioned_by arr lo i j hi)

open SortPartitionKVarSolutions in

def SortPartition_proof : SortPartition := by
  unfold SortPartition
  exists k0; exists inv; exists k2; exists k3
  simp [LeanProofs.Lib.Lemmas.arr_get, LeanProofs.Lib.Lemmas.arr_set, sort_is_perm, inv, k0, k2, k3]
  zap
  . simp [is_perm]; grind
  . simp [is_frame]
  . simp_all [is_perm, is_frame]; grind
  . simp_all [is_perm, is_frame]; grind
  . rename_i h; rcases h
    . simp_all; grind
    . grind
  . rename_i h
    rename_i old lo hi _ _ _ _ _ _ _ _ _  _ _ _ j new i _  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' _
    rcases h with hp | hq
    . obtain ⟨ new_def , _ ⟩ := hp
      have new_elems' : new'.elems = swap new.elems i j := by grind [swap]
      rw [new_elems']
      apply swap_is_perm <;> try grind
    . grind
  . rename_i h
    rename_i old lo hi _  _ _ _ _ _ _ _ _ _ _ _ j new i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' _
    rcases h with hp | hq
    . obtain ⟨ new_def , _ ⟩ := hp
      have new_elems' : new'.elems = swap new.elems i j := by grind [swap]
      rw [new_elems']
      apply swap_is_frame <;> grind
    . grind
  . rename_i h _ _ _
    rename_i old lo hi _  _ _ _ _ _ _ _ _ _ _ _ j new i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' _ ix _ _
    rcases h with hp | hq
    . split_ands_all
      obtain ⟨ new_def , _ ⟩ := hp
      have pivot_eq : new.elems hi = new'.elems hi := by
        simp_all; grind
      have new'_at_i : new'.elems i = new.elems j := by
        simp [new_def]; grind
      by_cases h_ix : ix = i
      . grind
      . have _ : ix < i := by grind
        have _ : new'.elems ix = new.elems ix := by simp [new_def]; grind
        grind
    . grind
  . rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j new i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' i' h ix _ _
    rcases h with hp | hq
    . obtain ⟨ new_def , _ ⟩ := hp
      have pivot_eq : new.elems hi = new'.elems hi := by
        simp_all; grind
      have new'_at_j : new'.elems j = new.elems i := by
        simp [new_def]
      by_cases h_ix : ix = j
      . grind
      . have _ : ix < j := by grind
        have _ : new'.elems ix = new.elems ix := by simp [new_def]; grind
        grind
    . grind


end F
