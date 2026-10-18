import Derivations.GP.WidderRecursion
import Derivations.OurFrontierDerivation

namespace NativeSolobolo.Derivations

open NativeSolobolo
open NativeSolobolo.Frontier
open NativeSolobolo.Derivations.BKQR

/-- !!! Free-energy curvature now derives common moments with no recursion interface. -/
theorem FREE_ENERGY_FRONTIER_IMPLIES_COMMON_MOMENT_FRONTIER
    {BKVec Value : Type}
    (G : GPObservable Value)
    (QBKQR : ScalarProductGeometry ℝ BKVec)
    (hFree : GPBKQRFreeEnergyCurvatureFrontier G QBKQR) :
    GPBKQRCommonMomentFrontier G QBKQR := by
  obtain ⟨Wit⟩ := hFree
  let A := Wit.gpModel.toTransferMomentModel
  let M := Wit.bkqrModel.toCayleyModel
  refine ⟨Wit.codec, A, M, ?_⟩
  exact ⟨NativeSolobolo.Derivations.GP.FREE_ENERGY_CURVATURE_IMPLIES_COMMON_MOMENTS
    Wit.gpModel Wit.bkqrModel Wit.freeEnergy⟩

/-- !!! SOLOBOLO CLOSURE: actual Cayley + the single free-energy curvature frontier. -/
theorem ACTUAL_CAYLEY_AND_FREE_ENERGY_FRONTIER_IMPLIES_RH
    {BKVec : Type}
    (T : CenteredThetaData)
    (QBKQR : ScalarProductGeometry ℝ BKVec)
    (hFree : GPBKQRFreeEnergyCurvatureFrontier
      (actualThetaCayleyObservable T) QBKQR) :
    RiemannHypothesis T.geometry := by
  exact ACTUAL_CAYLEY_AND_COMMON_MOMENT_FRONTIER_IMPLIES_RH T QBKQR
    (FREE_ENERGY_FRONTIER_IMPLIES_COMMON_MOMENT_FRONTIER
      (actualThetaCayleyObservable T) QBKQR hFree)

end NativeSolobolo.Derivations
