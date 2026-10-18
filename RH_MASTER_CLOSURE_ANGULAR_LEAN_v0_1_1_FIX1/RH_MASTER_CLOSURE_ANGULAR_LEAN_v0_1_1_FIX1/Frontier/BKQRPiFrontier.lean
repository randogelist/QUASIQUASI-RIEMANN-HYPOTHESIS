import Frontier.ContractiveOrbitFrontier
import Core.ActualThetaCayley

namespace NativeSolobolo

/-- Uniform boundedness in the finite BKQR approximation index at metric depth `eta`. -/
def UniformEnergyAdmissible (energy : Nat → ℝ → ℝ) (eta : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : Nat, energy N eta ≤ C

/-- The only structural property needed to pass from a deeper metric certificate to a shallower one. -/
def DownwardClosedOnNonnegative (P : ℝ → Prop) : Prop :=
  ∀ ⦃xi eta : ℝ⦄, 0 ≤ xi → xi ≤ eta → P eta → P xi

/-- Every nonnegative metric depth strictly below pi is admissible. -/
def MetricPi (P : ℝ → Prop) : Prop :=
  ∀ eta : ℝ, 0 ≤ eta → eta < Real.pi → P eta

/--
!!! BKQR PI, APPROXIMATIVE/COFINAL FORM.
Every requested metric depth below pi is dominated by some certified BKQR depth
which is still strictly below pi.  No certificate is required at the endpoint pi.
-/
def BKQRPiApprox (P : ℝ → Prop) : Prop :=
  ∀ eta : ℝ, 0 ≤ eta → eta < Real.pi →
    ∃ xi : ℝ, eta ≤ xi ∧ xi < Real.pi ∧ P xi

/-- A completely arbitrary metric sequence living below the pi barrier. -/
def MetricSequenceBelowPi (s : Nat → ℝ) : Prop :=
  ∀ n : Nat, 0 ≤ s n ∧ s n < Real.pi

/-- Pointwise monotonicity of finite BKQR energies in the metric depth. -/
def EnergyMonotoneInDepth (energy : Nat → ℝ → ℝ) : Prop :=
  ∀ (N : Nat) (xi eta : ℝ), 0 ≤ xi → xi ≤ eta →
    energy N xi ≤ energy N eta

namespace Frontier

/-- BKQR-pi formulated directly for a finite-approximation energy family. -/
def BKQRPiEnergyFrontier (energy : Nat → ℝ → ℝ) : Prop :=
  BKQRPiApprox (UniformEnergyAdmissible energy)

/-- Metric-pi formulated directly for a finite-approximation energy family. -/
def MetricPiEnergy (energy : Nat → ℝ → ℝ) : Prop :=
  MetricPi (UniformEnergyAdmissible energy)

/--
Analytic transfer interface: a uniform BKQR energy bound at a sub-pi depth
produces actual GP regularity at that same depth.
-/
structure BKQRToActualMetricBridge (energy : Nat → ℝ → ℝ) where
  regularAt : ℝ → Prop
  energy_to_regular : ∀ eta : ℝ,
    0 ≤ eta → eta < Real.pi →
    UniformEnergyAdmissible energy eta → regularAt eta

/--
Actual GP obstruction interface: non-RH forces failure of regularity at some
strictly sub-pi metric depth.  This is the analytic pole/regularity statement.
-/
structure ActualMetricPiObstruction
    (T : CenteredThetaData)
    (regularAt : ℝ → Prop) where
  notRH_bad_depth : ¬ RiemannHypothesis T.geometry →
    ∃ eta : ℝ, 0 ≤ eta ∧ eta < Real.pi ∧ ¬ regularAt eta

end Frontier
end NativeSolobolo
