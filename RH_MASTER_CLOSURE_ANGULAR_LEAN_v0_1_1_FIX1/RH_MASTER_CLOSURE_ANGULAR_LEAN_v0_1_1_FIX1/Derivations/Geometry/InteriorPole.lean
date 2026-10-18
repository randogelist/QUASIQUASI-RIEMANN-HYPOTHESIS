import Derivations.Geometry.LocalLaurent
import Derivations.Geometry.ActualCayleyObservable

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo

/--
!!! ACTUAL CAYLEY POLE THEOREM
The actual Theta-derived observable has an interior pole under not-RH.
This theorem has no compatibility/frontier parameter.
-/
theorem NOT_RH_IMPLIES_INTERIOR_CAYLEY_POLE
    (T : CenteredThetaData)
    (hNotRH : ¬ RiemannHypothesis T.geometry) :
    ∃ a r : ℝ,
      PositiveAnchor a ∧
      InteriorRadius r ∧
      (actualThetaCayleyObservable T).eval a r = none :=
  NOT_RH_IMPLIES_ACTUAL_INTERIOR_CAYLEY_POLE T hNotRH

end NativeSolobolo.Derivations.Geometry
