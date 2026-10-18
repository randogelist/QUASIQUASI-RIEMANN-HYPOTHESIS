import Frontier.BKQRPiFrontier

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo
open NativeSolobolo.Frontier

/-- !! Monotone finite energies make uniform admissibility downward closed. -/
theorem UNIFORM_ENERGY_ADMISSIBLE_DOWNWARD
    {energy : Nat → ℝ → ℝ}
    (hmono : EnergyMonotoneInDepth energy) :
    DownwardClosedOnNonnegative (UniformEnergyAdmissible energy) := by
  intro xi eta hxi hle hEta
  obtain ⟨C, hC⟩ := hEta
  refine ⟨C, ?_⟩
  intro N
  exact le_trans (hmono N xi eta hxi hle) (hC N)

/-- !!! Cofinal BKQR-pi certificates fill every metric depth below pi. -/
theorem BKQR_PI_IMPLIES_METRIC_PI
    {P : ℝ → Prop}
    (hdown : DownwardClosedOnNonnegative P)
    (hPi : BKQRPiApprox P) :
    MetricPi P := by
  intro eta heta hlt
  obtain ⟨xi, hle, _hxiPi, hP⟩ := hPi eta heta hlt
  exact hdown heta hle hP

/-- !! Full metric-pi trivially supplies cofinal approximative BKQR-pi certificates. -/
theorem METRIC_PI_IMPLIES_BKQR_PI
    {P : ℝ → Prop}
    (hMetric : MetricPi P) :
    BKQRPiApprox P := by
  intro eta heta hlt
  exact ⟨eta, le_rfl, hlt, hMetric eta heta hlt⟩

/-- !!! BKQR pi <-> metric pi for every downward-closed admissibility notion. -/
theorem BKQR_PI_IFF_METRIC_PI
    {P : ℝ → Prop}
    (hdown : DownwardClosedOnNonnegative P) :
    BKQRPiApprox P ↔ MetricPi P := by
  constructor
  · exact BKQR_PI_IMPLIES_METRIC_PI hdown
  · exact METRIC_PI_IMPLIES_BKQR_PI

/--
!!! Any arbitrary metric sequence below pi is pointwise majorized by a sequence
of certified BKQR depths, still strictly below pi.
-/
theorem BKQR_PI_MAJORISES_ANY_METRIC_SEQUENCE
    {P : ℝ → Prop}
    (hPi : BKQRPiApprox P)
    (s : Nat → ℝ)
    (hs : MetricSequenceBelowPi s) :
    ∃ t : Nat → ℝ,
      (∀ n : Nat, s n ≤ t n) ∧
      MetricSequenceBelowPi t ∧
      (∀ n : Nat, P (t n)) := by
  classical
  have hcert : ∀ n : Nat,
      ∃ xi : ℝ, s n ≤ xi ∧ xi < Real.pi ∧ P xi := by
    intro n
    exact hPi (s n) (hs n).1 (hs n).2
  let t : Nat → ℝ := fun n => Classical.choose (hcert n)
  have ht_spec : ∀ n : Nat,
      s n ≤ t n ∧ t n < Real.pi ∧ P (t n) := by
    intro n
    exact Classical.choose_spec (hcert n)
  refine ⟨t, ?_, ?_, ?_⟩
  · intro n
    exact (ht_spec n).1
  · intro n
    constructor
    · exact le_trans (hs n).1 (ht_spec n).1
    · exact (ht_spec n).2.1
  · intro n
    exact (ht_spec n).2.2

/-- !!! Energy specialization: cofinal BKQR-pi energy iff every sub-pi depth has a uniform energy bound. -/
theorem BKQR_PI_ENERGY_IFF_METRIC_PI_ENERGY
    {energy : Nat → ℝ → ℝ}
    (hmono : EnergyMonotoneInDepth energy) :
    BKQRPiEnergyFrontier energy ↔ MetricPiEnergy energy := by
  exact BKQR_PI_IFF_METRIC_PI (UNIFORM_ENERGY_ADMISSIBLE_DOWNWARD hmono)

/--
!! Transfer a metric-pi energy statement through the analytic BKQR -> GP bridge.
-/
theorem METRIC_PI_ENERGY_IMPLIES_FULL_ACTUAL_REGULARITY
    {energy : Nat → ℝ → ℝ}
    (B : BKQRToActualMetricBridge energy)
    (hMetric : MetricPiEnergy energy) :
    MetricPi B.regularAt := by
  intro eta heta hlt
  exact B.energy_to_regular eta heta hlt (hMetric eta heta hlt)

/-- !!! Full sub-pi actual regularity excludes the non-RH obstruction. -/
theorem FULL_ACTUAL_METRIC_REGULARITY_IMPLIES_RH
    (T : CenteredThetaData)
    {regularAt : ℝ → Prop}
    (O : ActualMetricPiObstruction T regularAt)
    (hReg : MetricPi regularAt) :
    RiemannHypothesis T.geometry := by
  exact Classical.byContradiction (by
    intro hNotRH
    obtain ⟨eta, heta, hlt, hbad⟩ := O.notRH_bad_depth hNotRH
    exact hbad (hReg eta heta hlt))

/--
!!! BKQR-PI REGULARITY CLOSURE.
The order/set-theoretic part is fully derived.  To obtain RH one supplies only:
(1) pointwise depth-monotonicity of the finite BKQR energies;
(2) cofinal uniform BKQR energy certificates below pi;
(3) the analytic transfer of such a bound to actual GP regularity;
(4) the already-isolated fact that non-RH causes sub-pi regularity failure.
-/
theorem BKQR_PI_ENERGY_BRIDGES_IMPLY_RH
    (T : CenteredThetaData)
    {energy : Nat → ℝ → ℝ}
    (hmono : EnergyMonotoneInDepth energy)
    (hPi : BKQRPiEnergyFrontier energy)
    (B : BKQRToActualMetricBridge energy)
    (O : ActualMetricPiObstruction T B.regularAt) :
    RiemannHypothesis T.geometry := by
  have hMetricEnergy : MetricPiEnergy energy :=
    (BKQR_PI_ENERGY_IFF_METRIC_PI_ENERGY hmono).1 hPi
  have hReg : MetricPi B.regularAt :=
    METRIC_PI_ENERGY_IMPLIES_FULL_ACTUAL_REGULARITY B hMetricEnergy
  exact FULL_ACTUAL_METRIC_REGULARITY_IMPLIES_RH T O hReg

end NativeSolobolo.Derivations.BKQR
