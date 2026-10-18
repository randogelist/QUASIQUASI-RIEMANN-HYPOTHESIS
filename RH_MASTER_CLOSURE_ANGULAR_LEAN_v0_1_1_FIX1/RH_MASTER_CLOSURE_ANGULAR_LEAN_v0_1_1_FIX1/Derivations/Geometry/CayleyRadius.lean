import Core.Observable

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo

/-- ! A nontrivial centered zero has a strictly positive Cayley anchor. -/
theorem ANCHOR_POSITIVE
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    PositiveAnchor (X.anchor z) := by
  unfold PositiveAnchor CenteredXiGeometry.anchor
  have hg : 0 < X.gamma z ^ 2 := sq_pos_of_ne_zero (X.gamma_ne_zero z)
  nlinarith [sq_nonneg (X.beta z)]

/-- !! Off-line means q = 1 + beta^2/gamma^2 is strictly larger than one. -/
theorem CAYLEY_Q_GT_ONE
    (X : CenteredXiGeometry)
    (z : X.Zero)
    (hb : X.beta z ≠ 0) :
    1 < X.cayleyQ z := by
  unfold CenteredXiGeometry.cayleyQ CenteredXiGeometry.anchor
  have hg : 0 < X.gamma z ^ 2 := sq_pos_of_ne_zero (X.gamma_ne_zero z)
  have hb2 : 0 < X.beta z ^ 2 := sq_pos_of_ne_zero hb
  rw [lt_div_iff₀ hg]
  nlinarith

/-- !!! The canonical Cayley radius of an off-line zero lies strictly in (0,1). -/
theorem OFFLINE_ZERO_GIVES_INTERIOR_RADIUS
    (X : CenteredXiGeometry)
    (z : X.Zero)
    (hb : X.beta z ≠ 0) :
    InteriorRadius (X.radius z) := by
  unfold InteriorRadius CenteredXiGeometry.radius
  have ha : 0 < X.anchor z := ANCHOR_POSITIVE X z
  have hg : 0 < X.gamma z ^ 2 := sq_pos_of_ne_zero (X.gamma_ne_zero z)
  constructor
  · exact div_pos hg ha
  · rw [div_lt_one ha]
    unfold CenteredXiGeometry.anchor
    have hb2 : 0 < X.beta z ^ 2 := sq_pos_of_ne_zero hb
    nlinarith

/-- !!! The two Cayley coordinates are exact reciprocals. -/
theorem CAYLEY_Q_MUL_RADIUS
    (X : CenteredXiGeometry)
    (z : X.Zero) :
    X.cayleyQ z * X.radius z = 1 := by
  unfold CenteredXiGeometry.cayleyQ CenteredXiGeometry.radius
  have ha : X.anchor z ≠ 0 := ne_of_gt (ANCHOR_POSITIVE X z)
  have hg : X.gamma z ^ 2 ≠ 0 := pow_ne_zero 2 (X.gamma_ne_zero z)
  calc
    (X.anchor z / (X.gamma z ^ 2)) * ((X.gamma z ^ 2) / X.anchor z)
        = (X.anchor z * (X.gamma z ^ 2)) / ((X.gamma z ^ 2) * X.anchor z) := by
            rw [div_mul_div_comm]
    _ = (X.anchor z * (X.gamma z ^ 2)) / (X.anchor z * (X.gamma z ^ 2)) := by
          rw [mul_comm (X.gamma z ^ 2) (X.anchor z)]
    _ = 1 := by
          exact div_self (mul_ne_zero ha hg)

/-- ! Failure of RH is exactly existence of an off-line centered zero. -/
theorem NOT_RH_GIVES_OFFLINE_ZERO
    (X : CenteredXiGeometry)
    (h : ¬ RiemannHypothesis X) :
    ∃ z : X.Zero, X.beta z ≠ 0 := by
  unfold RiemannHypothesis at h
  push_neg at h
  exact h

end NativeSolobolo.Derivations.Geometry
