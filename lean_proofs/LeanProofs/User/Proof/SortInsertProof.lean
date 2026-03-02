import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsert
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F

-- ((k0 m_ind₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->

@[simp]
def inv0 (m_ind : Int) (arr_elems : Arr Int) (arr_len : Int) (old_elems: Arr Int) (old_len : Int) (n : Int) : Prop :=
     arr_len == old_len
  /\ 0 <= m_ind
  /\ m_ind <= n
  /\ n < arr_len
  /\ ∀ i j, 0 ≤ i ∧ i < j ∧ j < n + 1 ∧ j ≠ m_ind → arr_elems i ≤ arr_elems j

-- ((k1 a'₃ m_ind₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->

@[simp]
def inv1 (a'₁₉ : Int) (a'₂₀ : Int) (a'₂₁ : (Arr Int)) (a'₂₂ : Int) (a'₂₃ : (Arr Int)) (a'₂₄ : Int) (a'₂₅ : Int) : Prop :=
  True


def SortInsert_proof : SortInsert := by
  unfold SortInsert
  exists inv0; exists inv1
  exists SortInsertKVarSolutions.k2
  exists SortInsertKVarSolutions.k3
  exists SortInsertKVarSolutions.k4
  exists SortInsertKVarSolutions.k5
  exists SortInsertKVarSolutions.k6
  exists SortInsertKVarSolutions.k7
  exists SortInsertKVarSolutions.k8
  exists SortInsertKVarSolutions.k9
  simp
  zap
  . sorry

end F
