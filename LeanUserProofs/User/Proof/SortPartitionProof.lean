import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortPartition
import LeanProofs.Lib.Lemmas
import Flex
--import LeanProofs.Lib.Tactics

open Classical

namespace F

@[reducible]
def part_inv (i j : Int)  (arr : Arr Int) (arr_len : Int) (old_elems: Arr Int) (old_len lo hi: Int) :=
     arr_len == old_len
  /\ 0 <= lo /\ hi < arr_len /\ lo <= i /\ i <= hi
  /\ lo <= j /\ j <= hi
  /\ i <= j
  /\ old_elems hi == arr hi
  /\ sort_is_perm old_elems arr lo hi
  /\ (sort_is_partitioned_by arr lo i j hi)

set_option maxHeartbeats 1600000 in
def SortPartition_proof : SortPartition := by
  unfold SortPartition
  fusion
  exists part_inv;
  simp [LeanProofs.Lib.Lemmas.arr_get, LeanProofs.Lib.Lemmas.arr_set, sort_is_perm, is_frame, is_perm, part_inv]
  solve_fixpoint

end F
