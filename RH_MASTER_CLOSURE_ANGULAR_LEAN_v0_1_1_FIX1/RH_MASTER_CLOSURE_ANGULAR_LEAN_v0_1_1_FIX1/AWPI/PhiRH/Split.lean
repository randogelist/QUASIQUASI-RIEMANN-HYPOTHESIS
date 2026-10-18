import AWPI.PhiRH.Forward
import AWPI.PhiRH.Reverse

namespace AWPI.PhiRH

universe u v
variable {Point : Type u} {Jet : Type v}
variable {M : Model Point Jet}

/-- Matched terminal split: under B, C iff RH. -/
theorem constructorIffRHUnderBackground
    (v23 : NormalizedDyadicMultiplierFacts M) (scale : Scale2Facts M)
    (hB : Background M) : Constructor M ↔ M.RH := by
  constructor
  · exact Forward.PHIRH286_C_IMPLIES_RH v23 scale
  · intro hRH
    exact Reverse.PHIRH287_BACKGROUND_AND_RH_IMPLIES_C hB hRH

end AWPI.PhiRH
