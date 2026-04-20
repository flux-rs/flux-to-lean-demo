import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInitUp
-- import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas
import LeanFixpoint

namespace F

@[grind]
def bigger (a: Arr Int) (i: Int) (v: Int) : Prop :=
    (∀ j, 0 <= j /\ j < i → a j < v)

-- def init_up_inv (this_elems : Arr Int) (this_len : Int) (i : Int) (_old_elems : Arr Int) (old_len : Int) : Prop :=
--      0 <= i
--   /\ i <= old_len
--   /\ this_len = old_len
--   /\ sort_is_sorted_between this_elems 0 i
--   /\ bigger this_elems i i
-- 1. Matches: 0 <= i
@[qualif] def q_zero_le  (v : Int) : Prop := 0 ≤ v

-- 2. Matches: i <= old_len
@[qualif] def q_le       (a b : Int) : Prop := a ≤ b

-- 3. Matches: this_len = old_len
@[qualif] def q_eq       (a b : Int) : Prop := a = b

-- 4. Matches: sort_is_sorted_between this_elems 0 i
-- (We bake `0` into the qualifier assuming 0 might not be explicitly
-- tracked as a bindable variable in the fixpoint environment).
@[qualif] def q_sorted_0 (a : Arr Int) (i : Int) : Prop := sort_is_sorted_between a 0 i

-- 5. Matches: bigger this_elems i i
@[qualif] def q_bigger   (a : Arr Int) (i v : Int) : Prop := bigger a i i

set_option maxRecDepth 1600000 in
def SortInitUp_proof : SortInitUp := by
   solve_fixpoint


end F
