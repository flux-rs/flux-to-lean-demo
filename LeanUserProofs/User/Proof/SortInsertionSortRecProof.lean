import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertionSortRec
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F

def inv (n : Int) (arr_elems : Arr Int) (arr_len : Int) (_old_elems : Arr Int) (old_len : Int) : Prop :=
     0 < n
  /\ n <= arr_len
  /\ arr_len = old_len
  /\ sort_is_sorted_between arr_elems 0 n


def SortInsertionSortRec_proof : SortInsertionSortRec := by
  unfold SortInsertionSortRec
  exists inv; simp [inv]
  zap

end F
