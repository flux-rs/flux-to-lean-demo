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
  . split_hyps  <;> try grind
    . rename_i upd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [upd] ; grind -- WTF!

  . split_hyps <;> try grind
    . sorry
    -- . apply swap_is_perm <;> try grind
    -- simp_all [is_perm, is_frame]; grind

  . split_hyps <;> try grind
    . rename_i upd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [upd] ; grind
  . split_hyps <;> try grind
    . simp_all []; grind
  . split_hyps <;> try grind
    . simp_all; sorry
  . rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j arr i _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _  _ _ _ _ _ _ _ _ _ _ _ _ arr' i' h ix _ _
    split_hyps
    . rename_i new_def _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have _ : arr'.elems j = arr.elems i := by
        rw [new_def]
        apply swap_val_j'
      by_cases h_ix : ix = j
      . rename_i new_def _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        rw [h_ix]
        rename_i bb
        have hh : arr'.elems hi = arr.elems hi := by
          rw [new_def]
          sorry
        rw [hh, bb]
        -- rename_i foo _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        -- apply foo
        sorry
        -- grind
      . sorry
    . sorry
  -- . rename_i h
  --   rename_i old lo hi _ _ _ _ _ _ _ _ _  _ _ _ j new i _  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' _
  --   rcases h with hp | hq
  --   . obtain ⟨ new_def , _ ⟩ := hp
  --     have new_elems' : new'.elems = swap new.elems i j := by grind [swap]
  --     rw [new_elems']
  --     apply swap_is_perm <;> try grind
  --   . grind

  -- . rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j new i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' _ _ i' _
  --   split_hyps
  --   . simp_all [is_frame]; grind
  --   . simp_all [is_frame]
  -- . rename_i old lo hi _  _ _ _ _ _ _ _ _ _ _ _ j new i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  new' _ h ix _
  --   split_hyps
  --   . have _ : new'.elems ix = new.elems ix := by simp_all []; grind
  --     simp_all [is_frame]
  --   . simp_all [is_frame]
  -- . rename_i old lo hi _ _ _ _ _ _ _ _ _ _ _ _ j new i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ new' i' h ix _ _
  --   split_hyps
  --   . have pivot_eq : new.elems hi = new'.elems hi := by simp_all; grind
  --     by_cases h_ix : ix = i
  --     . have _ : new'.elems i = new.elems j := by
  --         rename_i new_def _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  --         rw [new_def]; grind
  --       grind
  --     . rename_i new_def _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  --       have _ : ix < j := by grind
  --       have _ : new'.elems ix = new.elems ix := by simp [new_def]; grind
  --       grind
  --   . grind

end F
