import Frontier.OurFrontier

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo

/-- !!! Every BKQR transfer/Widder coefficient is a genuine Q-square. -/
theorem WIDDER_COEFF_IS_SQUARE
    {Scalar BKVec Value : Type}
    {Q : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (M : BKQRCayleyModel Scalar BKVec Value Q C)
    (a : ℝ) (m : Nat) :
    M.widderCoeff a m = Q.normSq (M.widderVector a m) := by
  exact M.widder_square a m

/-- !!! Therefore every modeled Widder coefficient is nonnegative. -/
theorem WIDDER_COEFF_NONNEGATIVE
    {Scalar BKVec Value : Type}
    {Q : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (M : BKQRCayleyModel Scalar BKVec Value Q C)
    (a : ℝ) (m : Nat) :
    Q.nonnegative (M.widderCoeff a m) := by
  rw [M.widder_square a m]
  exact Q.normSq_nonnegative (M.widderVector a m)

end NativeSolobolo.Derivations.BKQR
