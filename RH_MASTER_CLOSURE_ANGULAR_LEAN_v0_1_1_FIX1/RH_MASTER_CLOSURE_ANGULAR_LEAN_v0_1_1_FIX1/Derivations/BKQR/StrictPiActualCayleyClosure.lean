import Derivations.BKQR.StrictPiCofinality
import Derivations.Geometry.MetricPiObstruction

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo
open NativeSolobolo.Frontier
open NativeSolobolo.Derivations.Geometry

/--
!!! HARDY-READY BKQR-PI -> RH CLOSURE.
The same-depth L2-to-pointwise transfer is not assumed.
Instead, every target eta is assigned a strictly deeper certified xi < pi,
and only the mathematically natural deeper-energy -> shallower-regularity
transfer is required.  The non-RH obstruction remains fully internal.
-/
theorem BKQR_PI_DEEPER_ENERGY_TO_ACTUAL_CAYLEY_REGULARITY_IMPLIES_RH
    (T : CenteredThetaData)
    {energy : Nat → ℝ → ℝ}
    (hmono : EnergyMonotoneInDepth energy)
    (hPi : BKQRPiEnergyFrontier energy)
    (B : BKQRDeeperEnergyToActualCayleyBridge T energy) :
    RiemannHypothesis T.geometry := by
  have hStrict : StrictBKQRPiApprox (UniformEnergyAdmissible energy) :=
    BKQR_PI_ENERGY_IMPLIES_STRICT_SUBPI_ENERGY hmono hPi
  have hReg : MetricPi (ActualCayleyMetricRegularAt T) := by
    intro eta heta hlt
    obtain ⟨xi, hEtaXi, hXiPi, hEnergy⟩ := hStrict eta heta hlt
    exact B.deeper_energy_to_regular eta xi heta hEtaXi hXiPi hEnergy
  exact FULL_ACTUAL_METRIC_REGULARITY_IMPLIES_RH
    T (ACTUAL_CAYLEY_METRIC_PI_OBSTRUCTION T) hReg

end NativeSolobolo.Derivations.BKQR
