import Frontier.BKQRPiFrontier

namespace NativeSolobolo

/--
!!! STRICT BKQR PI, APPROXIMATIVE/COFINAL FORM.
Every requested metric depth below pi is strictly dominated by a certified depth
which still lies below pi.  This is the Hardy-ready form: control at the deeper
radius may be transferred to pointwise control at the shallower radius.
-/
def StrictBKQRPiApprox (P : ℝ → Prop) : Prop :=
  ∀ eta : ℝ, 0 ≤ eta → eta < Real.pi →
    ∃ xi : ℝ, eta < xi ∧ xi < Real.pi ∧ P xi

namespace Frontier

/--
Analytic transfer interface in its correct strict form: a uniform finite-BKQR
energy bound at a strictly deeper sub-pi depth `xi` produces actual Cayley
regularity at the shallower target depth `eta`.

Unlike the previous same-depth interface, this shape is compatible with the
standard Hardy/power-series estimate: bounded coefficient energy at a larger
radius controls point evaluations at every strictly smaller radius.
-/
structure BKQRDeeperEnergyToActualCayleyBridge
    (T : CenteredThetaData)
    (energy : Nat → ℝ → ℝ) where
  deeper_energy_to_regular : ∀ eta xi : ℝ,
    0 ≤ eta → eta < xi → xi < Real.pi →
    UniformEnergyAdmissible energy xi →
    ActualCayleyMetricRegularAt T eta

end Frontier
end NativeSolobolo
