import AWPI.PhiRH.Core

namespace AWPI.PhiRH.Geometry

open AWPI.PhiRH

universe u v
variable {Point : Type u} {Jet : Type v}
variable {M : Model Point Jet}

/-- Rocq v0.24 PHIRH240. -/
theorem PHIRH240_CENTERED_ZERO_IFF_CRITICAL_LINE (rho : Point) :
    M.centered rho = 0 ↔ M.criticalLine rho := by
  unfold Model.centered Model.criticalLine
  constructor <;> intro h <;> linarith

/-- Rocq v0.24 PHIRH242, exposed from the two-field scale interface. -/
theorem PHIRH242_SCALE2_AT_ZERO (scale : Scale2Facts M) : M.scale2 0 = 1 :=
  scale.PHIRH242_SCALE2_AT_ZERO

/-- Rocq v0.24 PHIRH243. -/
theorem PHIRH243_SCALE2_STRICTLY_INCREASING (scale : Scale2Facts M) :
    StrictMono M.scale2 :=
  scale.PHIRH243_SCALE2_STRICTLY_INCREASING

/-- Rocq v0.24 PHIRH244. -/
theorem PHIRH244_SCALE2_LE_ONE_IMPLIES_NONPOSITIVE
    (scale : Scale2Facts M) (a : ℝ) (h : M.scale2 a ≤ 1) : a ≤ 0 := by
  by_contra hnot
  have ha : 0 < a := lt_of_not_ge hnot
  have hstrict : M.scale2 0 < M.scale2 a :=
    scale.PHIRH243_SCALE2_STRICTLY_INCREASING ha
  rw [scale.PHIRH242_SCALE2_AT_ZERO] at hstrict
  linarith

/-- Scalar core used by Rocq PHIRH253. -/
theorem FORWARD_GAIN_LE_ONE_IMPLIES_CENTERED_NONPOSITIVE
    (scale : Scale2Facts M) (rho : Point) (hgain : M.gainPlus rho ≤ 1) :
    M.centered rho ≤ 0 := by
  change M.scale2 (2 * M.centered rho) ≤ 1 at hgain
  have harg := PHIRH244_SCALE2_LE_ONE_IMPLIES_NONPOSITIVE scale
    (2 * M.centered rho) hgain
  linarith

/-- Scalar core used by Rocq PHIRH254. -/
theorem BACKWARD_GAIN_LE_ONE_IMPLIES_CENTERED_NONNEGATIVE
    (scale : Scale2Facts M) (rho : Point) (hgain : M.gainMinus rho ≤ 1) :
    0 ≤ M.centered rho := by
  change M.scale2 (-2 * M.centered rho) ≤ 1 at hgain
  have harg := PHIRH244_SCALE2_LE_ONE_IMPLIES_NONPOSITIVE scale
    (-2 * M.centered rho) hgain
  linarith

/-- Rocq v0.28 PHIRH283, now proved rather than stored in a generic Laws bundle. -/
theorem PHIRH283_CRITICAL_LINE_GIVES_FORWARD_GAIN_ONE
    (scale : Scale2Facts M) (rho : Point) (hcrit : M.criticalLine rho) :
    M.gainPlus rho = 1 := by
  have hc : M.centered rho = 0 :=
    (PHIRH240_CENTERED_ZERO_IFF_CRITICAL_LINE rho).2 hcrit
  simp [Model.gainPlus, hc, scale.PHIRH242_SCALE2_AT_ZERO]

/-- Rocq v0.28 PHIRH284. -/
theorem PHIRH284_CRITICAL_LINE_GIVES_BACKWARD_GAIN_ONE
    (scale : Scale2Facts M) (rho : Point) (hcrit : M.criticalLine rho) :
    M.gainMinus rho = 1 := by
  have hc : M.centered rho = 0 :=
    (PHIRH240_CENTERED_ZERO_IFF_CRITICAL_LINE rho).2 hcrit
  simp [Model.gainMinus, hc, scale.PHIRH242_SCALE2_AT_ZERO]

end AWPI.PhiRH.Geometry
