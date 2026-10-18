import Core.Observable
import Derivations.BKQR.ScalarProduct

namespace NativeSolobolo

open Derivations.BKQR

/--
! Common moment-to-transfer decoder.
Both GP and BKQR induce the same scalar transfer observable from one scalar
moment sequence.  The concrete analytic decoder may later be instantiated by
  W_a(r) = sum_n mu_n(a) r^n
or the equivalent Cayley resolvent formula.
-/
structure CayleyMomentCodec (Scalar Value : Type) where
  decode : ℝ → ℝ → (Nat → Scalar) → Value

/--
!! GP transfer/moment model.
No GP scalar-product structure is required for RH closure: only the scalar
moment sequence and reconstruction of the actual GP Cayley observable.
-/
structure GPTransferMomentModel
    {Scalar Value : Type}
    (G : GPObservable Value)
    (C : CayleyMomentCodec Scalar Value) where
  moment : ℝ → Nat → Scalar
  reconstruct : ∀ a r,
    PositiveAnchor a →
    InteriorRadius r →
    G.eval a r = some (C.decode a r (moment a))

/--
!! Positive BKQR Cayley model.
Its Widder/Cayley coefficients are genuine diagonal Q-squares and reconstruct
its interior transfer value using the same decoder.
-/
structure BKQRCayleyModel
    (Scalar BKVec Value : Type)
    (Q : ScalarProductGeometry Scalar BKVec)
    (C : CayleyMomentCodec Scalar Value) where
  interiorValue : ℝ → ℝ → Value
  widderCoeff : ℝ → Nat → Scalar
  widderVector : ℝ → Nat → BKVec
  widder_square : ∀ a m, widderCoeff a m = Q.normSq (widderVector a m)
  reconstruct : ∀ a r, interiorValue a r = C.decode a r (widderCoeff a)

/--
!!! GP-BKQR COMMON MOMENT IDENTITY
This is the reduced algebraic frontier.  It is strictly smaller than full
scalar-product intertwining: equality of the induced scalar moment sequence is
enough to force equality of the transfer observable.
-/
structure GPBKQRCommonMomentIdentity
    {Scalar BKVec Value : Type}
    {G : GPObservable Value}
    {QBKQR : ScalarProductGeometry Scalar BKVec}
    {C : CayleyMomentCodec Scalar Value}
    (A : GPTransferMomentModel G C)
    (M : BKQRCayleyModel Scalar BKVec Value QBKQR C) where
  moment_eq : ∀ a n, A.moment a n = M.widderCoeff a n

/-- Derived scalar transfer equality. -/
def GPCayleyTransferMatch
    {Scalar BKVec Value : Type}
    (G : GPObservable Value)
    (QBKQR : ScalarProductGeometry Scalar BKVec)
    (C : CayleyMomentCodec Scalar Value)
    (A : GPTransferMomentModel G C)
    (M : BKQRCayleyModel Scalar BKVec Value QBKQR C) : Prop :=
  ∀ a r,
    PositiveAnchor a →
    InteriorRadius r →
    G.eval a r = some (M.interiorValue a r)

namespace Frontier

/--
!!! OUR REDUCED FRONTIER — COMMON MOMENT FORM
Construct the actual GP moment model and a positive BKQR Cayley model with the
same induced moments.  Full GP scalar-product intertwining is no longer needed
for the direct RH closure.
-/
def GPBKQRCommonMomentFrontier
    {Scalar BKVec Value : Type}
    (G : GPObservable Value)
    (QBKQR : ScalarProductGeometry Scalar BKVec) : Prop :=
  ∃ C : CayleyMomentCodec Scalar Value,
  ∃ A : GPTransferMomentModel G C,
  ∃ M : BKQRCayleyModel Scalar BKVec Value QBKQR C,
    Nonempty (GPBKQRCommonMomentIdentity A M)

/-- Downstream transfer frontier, now derived from common moments. -/
def GPBKQRCayleyTransferFrontier
    {Scalar BKVec Value : Type}
    (G : GPObservable Value)
    (QBKQR : ScalarProductGeometry Scalar BKVec) : Prop :=
  ∃ C : CayleyMomentCodec Scalar Value,
  ∃ A : GPTransferMomentModel G C,
  ∃ M : BKQRCayleyModel Scalar BKVec Value QBKQR C,
    GPCayleyTransferMatch G QBKQR C A M

end Frontier
end NativeSolobolo
