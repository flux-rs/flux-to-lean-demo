import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
open Classical

namespace F

@[ext]
structure VectorsAVec (t0 : Type) [Inhabited t0] where
  mkVectorsAVec₀ ::
    elems : (Arr t0) 
    len : Int 


end F
