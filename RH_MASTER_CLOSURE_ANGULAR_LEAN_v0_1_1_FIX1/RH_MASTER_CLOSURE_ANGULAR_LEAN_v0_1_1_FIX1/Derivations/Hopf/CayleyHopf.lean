import Derivations.BKQR.CayleySquares

namespace NativeSolobolo.Derivations.Hopf

open NativeSolobolo
open NativeSolobolo.Derivations.BKQR

/-- !! The positive BKQR model has nonnegative Widder energies at every depth. -/
theorem ALL_WIDDER_DEPTHS_NONNEGATIVE
    {Scalar BKVec Value : Type}
    {Q : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (M : BKQRCayleyModel Scalar BKVec Value Q C)
    (a : ℝ) :
    ∀ m : Nat, Q.nonnegative (M.widderCoeff a m) := by
  intro m
  exact NativeSolobolo.Derivations.BKQR.WIDDER_COEFF_NONNEGATIVE M a m

end NativeSolobolo.Derivations.Hopf
