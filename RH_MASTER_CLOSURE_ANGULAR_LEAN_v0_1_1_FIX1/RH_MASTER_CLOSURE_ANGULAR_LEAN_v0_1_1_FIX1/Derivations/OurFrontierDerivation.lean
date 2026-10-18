import Derivations.Geometry.InteriorPole
import Derivations.GP.CayleyObservable
import Derivations.Hopf.CayleyHopf

namespace NativeSolobolo.Derivations

open NativeSolobolo
open NativeSolobolo.Frontier
open NativeSolobolo.Derivations.BKQR

/-- !!! Common-moment frontier derives the downstream Cayley-transfer frontier. -/
theorem COMMON_MOMENT_FRONTIER_IMPLIES_CAYLEY_TRANSFER_FRONTIER
    {Scalar BKVec Value : Type}
    (G : GPObservable Value)
    (QBKQR : ScalarProductGeometry Scalar BKVec)
    (hOur : GPBKQRCommonMomentFrontier G QBKQR) :
    GPBKQRCayleyTransferFrontier G QBKQR := by
  obtain ⟨C, A, M, hH⟩ := hOur
  obtain ⟨H⟩ := hH
  refine ⟨C, A, M, ?_⟩
  exact NativeSolobolo.Derivations.GP.COMMON_MOMENTS_IMPLIES_TRANSFER_MATCH A M H

/--
!!! ZERO-RESEARCH-AXIOM SOLOBOLO CLOSURE — ACTUAL CAYLEY VERSION
The actual Theta/Cayley observable creates an interior pole under not-RH;
the common GP/BKQR moment identity reconstructs a finite positive BKQR value there.
-/
theorem ACTUAL_CAYLEY_AND_COMMON_MOMENT_FRONTIER_IMPLIES_RH
    {Scalar BKVec : Type}
    (T : CenteredThetaData)
    (QBKQR : ScalarProductGeometry Scalar BKVec)
    (hOur : GPBKQRCommonMomentFrontier (actualThetaCayleyObservable T) QBKQR) :
    RiemannHypothesis T.geometry := by
  exact Classical.byContradiction (by
    intro hNotRH
    obtain ⟨a, r, ha, hr, hNone⟩ :=
      NativeSolobolo.Derivations.Geometry.NOT_RH_IMPLIES_INTERIOR_CAYLEY_POLE T hNotRH
    obtain ⟨C, A, M, hH⟩ := hOur
    obtain ⟨H⟩ := hH
    obtain ⟨v, hv⟩ :=
      NativeSolobolo.Derivations.GP.INTERIOR_GP_VALUE_IS_SOME_FROM_COMMON_MOMENTS
        A M H a r ha hr
    rw [hNone] at hv
    cases hv)

end NativeSolobolo.Derivations
