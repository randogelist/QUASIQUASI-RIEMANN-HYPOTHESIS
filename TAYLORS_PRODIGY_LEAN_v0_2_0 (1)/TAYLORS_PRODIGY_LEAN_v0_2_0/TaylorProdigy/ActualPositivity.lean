import TaylorProdigy.Objects

noncomputable section
open Set

namespace TaylorsProdigy

/-- Under RH the actual squared-modulus profile is positive everywhere on the
semicircle except possibly its critical endpoint. This includes `x = 1`. -/
theorem actualProfile_pos_of_RH (hRH : _root_.RiemannHypothesis)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioc (-1 : ℝ) 1) :
    0 < AngularMaster.actualProfile r x := by
  change 0 < Complex.normSq (AWPIRH.theta (AngularMaster.circlePoint r x))
  apply Complex.normSq_pos.mpr
  intro hz
  have hzero := (AngularMaster.native_RH_iff_theta_zeros_nonpositive.mp hRH) _ hz
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hpos : 0 < (AngularMaster.circlePoint r x).im := by
      rw [AngularMaster.circlePoint_im]
      exact mul_pos hr (Real.sqrt_pos.mpr (sqrtArgument_pos ⟨hx.1, hlt⟩))
    rw [hzero.1] at hpos
    exact lt_irrefl 0 hpos
  · have hre : 0 < (AngularMaster.circlePoint r x).re := by
      rw [AngularMaster.circlePoint_re, heq, mul_one]
      exact hr
    exact (not_lt_of_ge hzero.2) hre

end TaylorsProdigy
