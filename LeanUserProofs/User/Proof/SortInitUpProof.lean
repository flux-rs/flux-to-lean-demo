import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInitUp
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F

@[grind]
def bigger (a: Arr Int) (i: Int) (v: Int) : Prop :=
    (∀ j, 0 <= j /\ j < i → a j < v)

def init_up_inv (this_elems : Arr Int) (this_len : Int) (i : Int) (_old_elems : Arr Int) (old_len : Int) : Prop :=
     0 <= i
  /\ i <= old_len
  /\ this_len = old_len
  /\ sort_is_sorted_between this_elems 0 i
  /\ bigger this_elems i i

def SortInitUp_proof : SortInitUp := by
   unfold SortInitUp
   exists init_up_inv; simp [init_up_inv]
   grind

end F
