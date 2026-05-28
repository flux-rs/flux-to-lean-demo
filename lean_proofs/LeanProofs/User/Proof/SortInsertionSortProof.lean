import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertionSort
import LeanProofs.Lib.Lemmas
-- import LeanProofs.Lib.Tactics
import LeanFixpoint

namespace F

@[qualif] def KPA.q_le (a b : Int) : Prop := a ≤ b
@[qualif] def KPA.q_lt (a b : Int) : Prop := a < b
@[qualif] def KPA.q_eq (a b : Int) : Prop := a = b
@[qualif] def KPA.q_ge_zero (a : Int) : Prop := a ≥ 0
@[qualif] def KPA.q_eq_zero (a : Int) : Prop := a = 0
@[qualif] def KPA (a : Int) : Prop := 0 < a
@[qualif] def q (arr_elems : Arr Int) (n : Int) : Prop :=
    sort_is_sorted_between arr_elems 0 n

def SortInsertionSort_proof : SortInsertionSort := by
  solve_fixpoint

end F
