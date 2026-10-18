import Frontier.FreeEnergyFrontier

namespace NativeSolobolo.Derivations.GP

open NativeSolobolo
open NativeSolobolo.Derivations.BKQR

/-- !!! Equal free-energy curvature gives equality of the two base moments. -/
theorem FREE_ENERGY_CURVATURE_IMPLIES_BASE_MOMENT_EQUALITY
    {BKVec Value : Type}
    {G : GPObservable Value}
    {QBKQR : ScalarProductGeometry ℝ BKVec}
    {C : CayleyMomentCodec ℝ Value}
    (A : GPWidderGeneratedModel G C)
    (M : BKQRWidderGeneratedModel BKVec Value QBKQR C)
    (F : GPBKQRFreeEnergyCurvature A M) :
    ∀ a : ℝ, A.baseMoment a = M.baseMoment a := by
  intro a
  rw [F.gp_base a, F.bkqr_base a]
  unfold logScaleCurvature
  rw [F.curvature_eq (Real.log a)]

end NativeSolobolo.Derivations.GP
