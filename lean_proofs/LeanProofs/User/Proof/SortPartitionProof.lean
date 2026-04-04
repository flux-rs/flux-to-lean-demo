import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortPartition
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics

open Classical

namespace F

-- ((k1 j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->

@[reducible]
def part_inv (j: Int) (arr : Arr Int) (arr_len i : Int) (old_elems: Arr Int) (old_len lo hi: Int) :=
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
  exists k0; exists part_inv; exists k2; exists k3
  simp [LeanProofs.Lib.Lemmas.arr_get, LeanProofs.Lib.Lemmas.arr_set, sort_is_perm, part_inv, k0, k2, k3]
  zap
  . rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j arr i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arr' _ h
    obtain ⟨ old_def , _ ⟩ := h
    . rw [old_def]; grind
    . grind
  . -- perm
    rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _  j arr i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  arr' i' h  ix _ _
    obtain ⟨ old_def , _ ⟩ := h
    . rw [old_def]; grind
    . grind
  . -- frame ix < i
    rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j arr i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  arr' _ h ix _
    obtain ⟨ old_def , _ ⟩ := h
    . rw [old_def]; grind
    . grind
  . -- frame hi < *
    rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j arr i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  arr' _ h ix _
    obtain ⟨ old_def , _ ⟩ := h
    . rw [old_def]; grind
    . grind
  . -- lo <= ix < i -> arr ix <= pivot
    rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j arr i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arr' i' h ix _ _
    obtain ⟨ old_def , _ ⟩ := h
    . rw [old_def]; grind
    . grind
  . -- i <= ix < j -> pivot <= arr ix
    rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j arr i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arr' i' h ix _ _
    obtain ⟨ old_def , _ ⟩ := h
    . rw [old_def]; grind
    . grind

end F
