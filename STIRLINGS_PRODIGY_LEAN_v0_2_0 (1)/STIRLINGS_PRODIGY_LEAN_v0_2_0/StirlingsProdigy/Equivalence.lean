import StirlingsProdigy.Local
import AngularMaster.ActualHadamard

/-!
# Native RH equivalence for the separately named local criterion

The reverse implication uses the retained proved actual-theta factorization.
No factorization, monotonicity, or sign bridge is introduced as an assumption.
The original global affine STIRLINGS_PRODIGY remains unchanged and is only a
sufficient premise; no converse to that original implication is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace StirlingsProdigy

/-- Actual RH implies the local premise through the proved Hadamard development. -/
theorem STIRLINGS_PRODIGY_LOCAL_of_RH
    (hRH : _root_.RiemannHypothesis) : STIRLINGS_PRODIGY_LOCAL := by
  have hd : AngularMaster.DerivativeNonnegative AngularMaster.actualProfile :=
    AngularMaster.derivativeNonnegative_of_profileMaster
      (AngularMaster.actual_profileMaster_of_native_RH hRH)
  have hm := AngularMaster.profile_monotone_of_derivativeNonnegative_interior
    AngularMaster.actualProfile_continuousOn
    AngularMaster.actualProfile_interior_differentiable hd
  intro r hr x hx₀ hx₁
  exact localFirstOrderAt_of_monotoneOn (hm r hr) ⟨hx₀, hx₁⟩

/-- Genuine equivalence for the new local premise, not for the original affine premise. -/
theorem STIRLINGS_PRODIGY_LOCAL_IFF_RH :
    STIRLINGS_PRODIGY_LOCAL ↔ _root_.RiemannHypothesis :=
  ⟨RH_of_STIRLINGS_PRODIGY_LOCAL, STIRLINGS_PRODIGY_LOCAL_of_RH⟩

/-- The same native equivalence with RH displayed first. -/
theorem RH_IFF_STIRLINGS_PRODIGY_LOCAL :
    _root_.RiemannHypothesis ↔ STIRLINGS_PRODIGY_LOCAL :=
  STIRLINGS_PRODIGY_LOCAL_IFF_RH.symm

end StirlingsProdigy
