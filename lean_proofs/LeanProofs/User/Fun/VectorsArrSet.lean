import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Lib.Lemmas

namespace F

@[simp]
def vectors_arr_set {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) (v: t0) : Arr t0 :=
  LeanProofs.Lib.Lemmas.arr_set arr idx v


end F
