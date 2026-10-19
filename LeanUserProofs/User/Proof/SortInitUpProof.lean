import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInitUp
-- import LeanProofs.Lib.Tactics
import Flex
import LeanProofs.Lib.Lemmas

namespace F

@[grind]
def bigger (a: Arr Int) (i: Int) (v: Int) : Prop :=
    (∀ j, 0 <= j /\ j < i → a j < v)

def init_up_inv (i : Int) (this_elems : Arr Int) (this_len : Int) (_old_elems : Arr Int) (old_len : Int) : Prop :=
     0 <= i
  /\ i <= old_len
  /\ this_len = old_len
  /\ sort_is_sorted_between this_elems 0 i
  /\ bigger this_elems i i

def SortInitUp_proof : SortInitUp := by
   unfold SortInitUp
   refine ⟨init_up_inv, ?_⟩
   intro old₀ hlen
   refine ⟨?_, ?_⟩
   · refine ⟨Int.le_refl _, hlen, rfl, ?_, ?_⟩
     · intro i j h; omega
     · intro j h; omega
   · intro i₀ a'₂ ⟨hi0, hile, hlen2, hsorted, hbig⟩
     refine ⟨?_, ?_⟩
     · intro hge i j h
       exact hsorted i j (by omega)
     · intro hlt
       refine ⟨by omega, ?_⟩
       intro _
       simp only [init_up_inv, vectors_arr_set]
       refine ⟨by omega, by omega, hlen2, ?_, ?_⟩
       · intro i j h
         rw [LeanProofs.Lib.Lemmas.set_get_neq' _ _ _ _ (by simp; omega)]
         by_cases hj : j = i₀
         · subst hj; rw [LeanProofs.Lib.Lemmas.set_get_eq']; have := hbig i (by omega); omega
         · rw [LeanProofs.Lib.Lemmas.set_get_neq' _ _ _ _ (by simp; omega)]; exact hsorted i j (by omega)
       · intro j h
         by_cases hj : j = i₀
         · subst hj; rw [LeanProofs.Lib.Lemmas.set_get_eq']; omega
         · rw [LeanProofs.Lib.Lemmas.set_get_neq' _ _ _ _ (by simp; omega)]; have := hbig j (by omega); omega

end F
