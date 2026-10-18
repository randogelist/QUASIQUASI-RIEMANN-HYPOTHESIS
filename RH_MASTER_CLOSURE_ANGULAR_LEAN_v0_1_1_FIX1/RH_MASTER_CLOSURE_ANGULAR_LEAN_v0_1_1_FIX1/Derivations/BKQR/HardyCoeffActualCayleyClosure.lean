import Derivations.BKQR.HardyCoefficientTransfer
import Derivations.BKQR.PiMetricCofinality
import Derivations.Geometry.MetricPiObstruction

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo
open NativeSolobolo.Frontier
open NativeSolobolo.Derivations.Geometry

/--
!!! COFINAL BKQR-PI COEFFICIENT ENVELOPE -> RH.
The deeper-radius Hardy transfer is fully derived.  The only local analytic
input is identification of the absolutely convergent coefficient germ with the
literal actual theta'/theta Cayley observable.
-/
theorem BKQR_PI_COEFF_PLUS_ACTUAL_CAYLEY_JET_BRIDGE_IMPLIES_RH
    (T : CenteredThetaData)
    {mu : ℝ → Nat → ℝ}
    (hPi : StrictBKQRPiCoeffFrontier mu)
    (J : ActualCayleyJetBridge T mu) :
    RiemannHypothesis T.geometry := by
  have hAbs : MetricPi (AbsoluteCayleySeriesRegularAt mu) :=
    BKQR_PI_COEFF_IMPLIES_ALL_SUBPI_ABSOLUTE_CAYLEY_SERIES hPi
  have hReg : MetricPi (ActualCayleyMetricRegularAt T) := by
    intro eta heta hEtaPi
    exact J.absolute_series_to_actual eta heta hEtaPi (hAbs eta heta hEtaPi)
  exact FULL_ACTUAL_METRIC_REGULARITY_IMPLIES_RH
    T (ACTUAL_CAYLEY_METRIC_PI_OBSTRUCTION T) hReg

/--
!!! CROSS-ROUTE CLOSURE.
A contractive BKQR orbit plus the actual local Cayley jet identification already
implies RH; the weighted coefficient and strict Hardy-transfer layers are all
derived in between.
-/
theorem CONTRACTIVE_ORBIT_PLUS_ACTUAL_CAYLEY_JET_BRIDGE_IMPLIES_RH
    (T : CenteredThetaData)
    {mu : ℝ → Nat → ℝ}
    (hOrbit : BKQRContractiveOrbitFrontier mu)
    (J : ActualCayleyJetBridge T mu) :
    RiemannHypothesis T.geometry := by
  exact BKQR_PI_COEFF_PLUS_ACTUAL_CAYLEY_JET_BRIDGE_IMPLIES_RH
    T (CONTRACTIVE_ORBIT_FRONTIER_IMPLIES_STRICT_BKQR_PI_COEFF hOrbit) J

end NativeSolobolo.Derivations.BKQR
