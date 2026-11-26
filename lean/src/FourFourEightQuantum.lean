import FourFourEightResidual
import TwoCycleMatchings
import TwoAnchorUnionGlue

namespace QGI.Coherent.FourFourEight
open Relations SixTenCoordinates

/-- A quantum isomorphism is classical on the 4+4+8 fiber profile. -/
theorem isomorphic_of_four_four_eight {G H : Graph 16} (a b y : Fin 16)
    (ha : (fiber G a).card=4) (hb : (fiber G b).card=4) (hy : (fiber G y).card=8)
    (apart : a ∉ fiber G b) (q : QuantumIso G H) : Isomorphic G H := by
  rcases isomorphic_or_equal_phase a b y ha hb hy apart q with hit |
    ⟨l,r,v,lr,lv,rv,F,S,Y,cover,uniform,u,w,B,D,fb,sd,⟨hB⟩,⟨hD⟩,_⟩
  · exact hit
  · exact TwoAnchorUnionGlue.isomorphic lr lv rv F S Y cover uniform
      (TwoCycleMatchings.two_base (sourceLaws _) F S Y uniform u w B D fb sd hB hD) q

end QGI.Coherent.FourFourEight
