import Frontier.OurFrontier

namespace NativeSolobolo.Derivations.GP

open NativeSolobolo
open NativeSolobolo.Derivations.BKQR

/-- !!! Common moment identity gives equality of the whole moment function. -/
theorem COMMON_MOMENTS_IMPLIES_MOMENT_FUNCTION_EQUALITY
    {Scalar BKVec Value : Type}
    {G : GPObservable Value}
    {QBKQR : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (A : GPTransferMomentModel G C)
    (M : BKQRCayleyModel Scalar BKVec Value QBKQR C)
    (H : GPBKQRCommonMomentIdentity A M)
    (a : ℝ) :
    A.moment a = M.widderCoeff a := by
  funext n
  exact H.moment_eq a n

/--
!!! COMMON MOMENTS -> TRANSFER MATCH
No GP Gram/intertwiner hypothesis is required.  Both transfer functions are
reconstructed from the identical scalar moment function through the common
Cayley codec.
-/
theorem COMMON_MOMENTS_IMPLIES_TRANSFER_MATCH
    {Scalar BKVec Value : Type}
    {G : GPObservable Value}
    {QBKQR : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (A : GPTransferMomentModel G C)
    (M : BKQRCayleyModel Scalar BKVec Value QBKQR C)
    (H : GPBKQRCommonMomentIdentity A M) :
    GPCayleyTransferMatch G QBKQR C A M := by
  intro a r ha hr
  have hm : A.moment a = M.widderCoeff a :=
    COMMON_MOMENTS_IMPLIES_MOMENT_FUNCTION_EQUALITY A M H a
  calc
    G.eval a r = some (C.decode a r (A.moment a)) := A.reconstruct a r ha hr
    _ = some (C.decode a r (M.widderCoeff a)) := by rw [hm]
    _ = some (M.interiorValue a r) := by rw [M.reconstruct a r]

/-- !!! Common moments make the actual GP observable finite at every interior point. -/
theorem INTERIOR_GP_VALUE_IS_SOME_FROM_COMMON_MOMENTS
    {Scalar BKVec Value : Type}
    {G : GPObservable Value}
    {QBKQR : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (A : GPTransferMomentModel G C)
    (M : BKQRCayleyModel Scalar BKVec Value QBKQR C)
    (H : GPBKQRCommonMomentIdentity A M)
    (a r : ℝ)
    (ha : PositiveAnchor a)
    (hr : InteriorRadius r) :
    ∃ v : Value, G.eval a r = some v := by
  have hMatch := COMMON_MOMENTS_IMPLIES_TRANSFER_MATCH A M H
  exact ⟨M.interiorValue a r, hMatch a r ha hr⟩

end NativeSolobolo.Derivations.GP
