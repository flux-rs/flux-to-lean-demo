import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertionSort
import LeanProofs.Lib.Lemmas
import LeanProofs.Lib.Tactics

open F

def inv (n : Int) (arr_elems : Arr Int) (arr_len : Int) (_old_elems : Arr Int) (old_len : Int) : Prop :=
     0 < n
  /\ n <= arr_len
  /\ arr_len = old_len
  /\ sort_is_sorted_between arr_elems 0 n


def SortInsertionSort_proof : SortInsertionSort := by
  unfold SortInsertionSort
  exists inv; simp [inv]
  grind
