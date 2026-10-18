import Derivations.BKQR.PiMetricCofinality
import Frontier.BKQRStrictPiFrontier

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo
open NativeSolobolo.Frontier

/--
!!! Full metric-pi admissibility automatically supplies a STRICTLY deeper
certificate below pi.  The canonical choice is the midpoint `(eta + pi)/2`.
-/
theorem METRIC_PI_IMPLIES_STRICT_BKQR_PI
    {P : ℝ → Prop}
    (hMetric : MetricPi P) :
    StrictBKQRPiApprox P := by
  intro eta heta hlt
  let xi : ℝ := (eta + Real.pi) / 2
  have hEtaXi : eta < xi := by
    dsimp [xi]
    linarith
  have hXiPi : xi < Real.pi := by
    dsimp [xi]
    linarith
  have hXi0 : 0 ≤ xi := le_trans heta (le_of_lt hEtaXi)
  exact ⟨xi, hEtaXi, hXiPi, hMetric xi hXi0 hXiPi⟩

/--
!!! The existing approximative BKQR-pi statement, together with downward
closure, already contains strict cofinality below pi.  No new certificate
hypothesis is introduced.
-/
theorem BKQR_PI_IMPLIES_STRICT_BKQR_PI
    {P : ℝ → Prop}
    (hdown : DownwardClosedOnNonnegative P)
    (hPi : BKQRPiApprox P) :
    StrictBKQRPiApprox P := by
  have hMetric : MetricPi P := BKQR_PI_IMPLIES_METRIC_PI hdown hPi
  exact METRIC_PI_IMPLIES_STRICT_BKQR_PI hMetric

/-- Strict cofinality also fills all shallower depths for a downward-closed property. -/
theorem STRICT_BKQR_PI_IMPLIES_METRIC_PI
    {P : ℝ → Prop}
    (hdown : DownwardClosedOnNonnegative P)
    (hStrict : StrictBKQRPiApprox P) :
    MetricPi P := by
  intro eta heta hlt
  obtain ⟨xi, hEtaXi, _hXiPi, hP⟩ := hStrict eta heta hlt
  exact hdown heta (le_of_lt hEtaXi) hP

/-- !!! Strict cofinality is equivalent to metric-pi for downward-closed predicates. -/
theorem STRICT_BKQR_PI_IFF_METRIC_PI
    {P : ℝ → Prop}
    (hdown : DownwardClosedOnNonnegative P) :
    StrictBKQRPiApprox P ↔ MetricPi P := by
  constructor
  · exact STRICT_BKQR_PI_IMPLIES_METRIC_PI hdown
  · exact METRIC_PI_IMPLIES_STRICT_BKQR_PI

/--
!!! Energy specialization: the already-proved BKQR-pi energy frontier yields
uniform energy control at a STRICTLY deeper certified depth for every target
eta < pi.
-/
theorem BKQR_PI_ENERGY_IMPLIES_STRICT_SUBPI_ENERGY
    {energy : Nat → ℝ → ℝ}
    (hmono : EnergyMonotoneInDepth energy)
    (hPi : BKQRPiEnergyFrontier energy) :
    StrictBKQRPiApprox (UniformEnergyAdmissible energy) := by
  exact BKQR_PI_IMPLIES_STRICT_BKQR_PI
    (UNIFORM_ENERGY_ADMISSIBLE_DOWNWARD hmono) hPi

end NativeSolobolo.Derivations.BKQR
