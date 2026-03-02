import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsertNew
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F


@[simp]
def inv00 (m_ind : Int) (arr_elems : Arr Int) (arr_len : Int) (old_elems: Arr Int) (old_len : Int) (n : Int) : Prop :=
     arr_len == old_len
  /\ 0 <= m_ind
  /\ m_ind <= n
  /\ n < arr_len
  /\ sort_is_sorted_between_exc arr_elems 0 (n + 1) m_ind


def SortInsertNew_proof : SortInsertNew := by
  unfold SortInsertNew
  exists inv00; simp [inv00]
  exists SortInsertNewKVarSolutions.k1
  exists SortInsertNewKVarSolutions.k2
  exists SortInsertNewKVarSolutions.k3
  simp [SortInsertNewKVarSolutions.k1, SortInsertNewKVarSolutions.k2, SortInsertNewKVarSolutions.k3]
  zap
  sorry

end F
