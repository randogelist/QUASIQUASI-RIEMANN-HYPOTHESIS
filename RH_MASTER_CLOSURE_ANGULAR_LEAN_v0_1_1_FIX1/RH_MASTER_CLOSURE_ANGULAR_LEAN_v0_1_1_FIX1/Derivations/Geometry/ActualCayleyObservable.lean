import Core.ActualThetaCayley
import Derivations.Geometry.CayleyRadius

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo

/-- ! At the canonical radius, a*r = gamma^2. -/
theorem ANCHOR_MUL_RADIUS
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    X.anchor z * X.radius z = X.gamma z ^ 2 := by
  unfold CenteredXiGeometry.radius
  have ha : X.anchor z ≠ 0 := ne_of_gt (ANCHOR_POSITIVE X z)
  field_simp [ha]

/-- ! The complementary Cayley mass is beta^2. -/
theorem ANCHOR_MUL_ONE_SUB_RADIUS
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    X.anchor z * (1 - X.radius z) = X.beta z ^ 2 := by
  have har := ANCHOR_MUL_RADIUS X z
  calc
    X.anchor z * (1 - X.radius z)
        = X.anchor z - X.anchor z * X.radius z := by ring
    _ = X.anchor z - X.gamma z ^ 2 := by rw [har]
    _ = X.beta z ^ 2 := by
      unfold CenteredXiGeometry.anchor
      ring

/-- !! Real part of the canonical Cayley pair is beta^2-gamma^2. -/
theorem CAYLEY_REAL_PART_AT_ZERO
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    X.anchor z * (1 - 2 * X.radius z) =
      X.beta z ^ 2 - X.gamma z ^ 2 := by
  have har := ANCHOR_MUL_RADIUS X z
  calc
    X.anchor z * (1 - 2 * X.radius z)
        = X.anchor z - 2 * (X.anchor z * X.radius z) := by ring
    _ = X.anchor z - 2 * X.gamma z ^ 2 := by rw [har]
    _ = X.beta z ^ 2 - X.gamma z ^ 2 := by
      unfold CenteredXiGeometry.anchor
      ring

/-- !! Imaginary magnitude of the canonical pair is 2*|beta*gamma|. -/
theorem CAYLEY_IMAG_MAGNITUDE_AT_ZERO
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    cayleyImagMagnitude (X.anchor z) (X.radius z) =
      2 * |X.beta z * X.gamma z| := by
  have har := ANCHOR_MUL_RADIUS X z
  have hac := ANCHOR_MUL_ONE_SUB_RADIUS X z
  unfold cayleyImagMagnitude
  rw [har, hac]
  have hsq : X.gamma z ^ 2 * X.beta z ^ 2 =
      (X.beta z * X.gamma z) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq_eq_abs]

/--
!!! CANONICAL CAYLEY PAIR HITS THE CENTERED THETA ZERO
Depending only on the sign of beta*gamma, one member of the conjugate Cayley
pair is exactly z = (beta+i gamma)^2.
-/
theorem THETA_ZERO_POINT_EQ_CAYLEY_PLUS_OR_MINUS
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    X.thetaZeroPoint z =
        cayleyPointPlus (X.anchor z) (X.radius z) ∨
    X.thetaZeroPoint z =
        cayleyPointMinus (X.anchor z) (X.radius z) := by
  have hre := CAYLEY_REAL_PART_AT_ZERO X z
  have him := CAYLEY_IMAG_MAGNITUDE_AT_ZERO X z
  by_cases hsgn : 0 ≤ X.beta z * X.gamma z
  · left
    apply Complex.ext
    · simp [CenteredXiGeometry.thetaZeroPoint, cayleyPointPlus, hre]
    · simp [CenteredXiGeometry.thetaZeroPoint, cayleyPointPlus, him,
        abs_of_nonneg hsgn]
      ring
  · right
    have hneg : X.beta z * X.gamma z < 0 := lt_of_not_ge hsgn
    apply Complex.ext
    · simp [CenteredXiGeometry.thetaZeroPoint, cayleyPointMinus, hre]
    · simp [CenteredXiGeometry.thetaZeroPoint, cayleyPointMinus, him,
        abs_of_neg hneg]
      ring

/-- !!! The actual Theta Cayley observable is undefined at every canonical zero point. -/
theorem ACTUAL_THETA_CAYLEY_NONE_AT_ZERO
    (T : CenteredThetaData)
    (z : T.geometry.Zero) :
    (actualThetaCayleyObservable T).eval
      (T.geometry.anchor z) (T.geometry.radius z) = none := by
  have hp := THETA_ZERO_POINT_EQ_CAYLEY_PLUS_OR_MINUS T.geometry z
  have hz :
      T.theta (cayleyPointPlus (T.geometry.anchor z) (T.geometry.radius z)) = 0 ∨
      T.theta (cayleyPointMinus (T.geometry.anchor z) (T.geometry.radius z)) = 0 := by
    cases hp with
    | inl hplus =>
        left
        rw [← hplus]
        exact T.theta_zero z
    | inr hminus =>
        right
        rw [← hminus]
        exact T.theta_zero z
  simp [actualThetaCayleyObservable, hz]

/--
!!! ACTUAL OFF-LINE ZERO -> INTERIOR ACTUAL-GP CAYLEY POLE
No Theta/GP pole-compatibility frontier is used: the observable is defined
literally from theta'/theta, and the canonical pair hits the theta zero.
-/
theorem OFFLINE_ZERO_GIVES_ACTUAL_INTERIOR_CAYLEY_POLE
    (T : CenteredThetaData)
    (z : T.geometry.Zero)
    (hb : T.geometry.beta z ≠ 0) :
    PositiveAnchor (T.geometry.anchor z) ∧
    InteriorRadius (T.geometry.radius z) ∧
    (actualThetaCayleyObservable T).eval
      (T.geometry.anchor z) (T.geometry.radius z) = none := by
  exact ⟨ANCHOR_POSITIVE T.geometry z,
    OFFLINE_ZERO_GIVES_INTERIOR_RADIUS T.geometry z hb,
    ACTUAL_THETA_CAYLEY_NONE_AT_ZERO T z⟩

/-- !!! Failure of RH gives an interior pole of the actual Theta/GP Cayley observable. -/
theorem NOT_RH_IMPLIES_ACTUAL_INTERIOR_CAYLEY_POLE
    (T : CenteredThetaData)
    (hNotRH : ¬ RiemannHypothesis T.geometry) :
    ∃ a r : ℝ,
      PositiveAnchor a ∧
      InteriorRadius r ∧
      (actualThetaCayleyObservable T).eval a r = none := by
  obtain ⟨z, hb⟩ := NOT_RH_GIVES_OFFLINE_ZERO T.geometry hNotRH
  exact ⟨T.geometry.anchor z, T.geometry.radius z,
    OFFLINE_ZERO_GIVES_ACTUAL_INTERIOR_CAYLEY_POLE T z hb⟩

end NativeSolobolo.Derivations.Geometry
