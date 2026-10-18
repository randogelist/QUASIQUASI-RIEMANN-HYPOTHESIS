import TaylorProdigy.Closure
import TaylorProdigy.Reverse

/-! The unchanged Taylor's Prodigy premise is equivalent to Mathlib's native RH. -/

namespace TaylorsProdigy

/-- Exact equivalence for the original locally integrable finite-rate premise. -/
theorem TAYLORS_PRODIGY_PREMISE_iff_RH :
    TAYLORS_PRODIGY_PREMISE ↔ _root_.RiemannHypothesis :=
  ⟨native_RH_of_TAYLORS_PRODIGY_PREMISE, TAYLORS_PRODIGY_PREMISE_of_native_RH⟩

end TaylorsProdigy
