import Derivations.BKQR.PiMetricCofinality
import Derivations.Geometry.MetricPiObstruction

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo
open NativeSolobolo.Frontier
open NativeSolobolo.Derivations.Geometry

/--
!!! BKQR-PI -> RH WITH THE OBSTRUCTION SIDE INTERNAL.
The only analytic transfer input in this theorem is that a uniform finite-BKQR
energy bound at depth eta gives regularity of the actual Theta Cayley observable
at that same depth.  The non-RH -> bad sub-pi depth statement is derived.
-/
theorem BKQR_PI_ENERGY_TO_ACTUAL_CAYLEY_REGULARITY_IMPLIES_RH
    (T : CenteredThetaData)
    {energy : Nat → ℝ → ℝ}
    (hmono : EnergyMonotoneInDepth energy)
    (hPi : BKQRPiEnergyFrontier energy)
    (energy_to_actual : ∀ eta : ℝ,
      0 ≤ eta → eta < Real.pi →
      UniformEnergyAdmissible energy eta →
      ActualCayleyMetricRegularAt T eta) :
    RiemannHypothesis T.geometry := by
  have hMetricEnergy : MetricPiEnergy energy :=
    (BKQR_PI_ENERGY_IFF_METRIC_PI_ENERGY hmono).1 hPi
  have hReg : MetricPi (ActualCayleyMetricRegularAt T) := by
    intro eta heta hlt
    exact energy_to_actual eta heta hlt (hMetricEnergy eta heta hlt)
  exact FULL_ACTUAL_METRIC_REGULARITY_IMPLIES_RH
    T (ACTUAL_CAYLEY_METRIC_PI_OBSTRUCTION T) hReg

end NativeSolobolo.Derivations.BKQR
