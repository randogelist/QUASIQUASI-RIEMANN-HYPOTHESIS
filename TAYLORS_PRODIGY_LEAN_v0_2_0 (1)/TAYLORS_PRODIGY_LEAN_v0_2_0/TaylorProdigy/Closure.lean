import TaylorProdigy.Objects
import TaylorProdigy.Comparison
import TaylorProdigy.ZeroExclusion
import AngularMaster.ZeroFreeSeed

/-!
# Conditional closure from Taylor's Prodigy premise

The sole research premise is transported to actual theta zero exclusion.
No positive endpoint derivative or independent positive-slope seed is assumed.
An alleged interior zero produces its own positive-slope seed by the
mean-value theorem and analytic uniqueness. Real-axis exclusion uses the
retained unconditional explicit low-height theta-kernel estimate.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate

namespace TaylorsProdigy

theorem F_positive_propagates
    (h : TAYLORS_PRODIGY_PREMISE) {r a b : ℝ} (hr : 0 < r)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi)
    (hseed : 0 < F r a) : 0 < F r b := by
  obtain ⟨rate, hi, hn, hd⟩ := h r hr
  have hb0 : 0 < b := ha.trans_le hab
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) Real.pi := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hirest : IntegrableOn rate (Icc a b) := by
    have hi0b : IntegrableOn rate (Icc 0 b) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hb0.le).1 (hi b hb0 hb)
    exact hi0b.mono_set (Icc_subset_Icc ha.le le_rfl)
  apply positive_of_integrable_relative_decay hab ((F_continuousOn r).mono hsub)
    (fun t ht => F_differentiableAt (hsub ⟨ht.1.le, ht.2.le⟩)) hseed hirest
  · intro t ht
    exact hn t (hsub ht)
  · intro t ht hp
    exact hd t (hsub ⟨ht.1.le, ht.2.le⟩) hp

theorem angularSlopePositivePropagatesLeft_of_premise
    (h : TAYLORS_PRODIGY_PREMISE) : AngularSlopePositivePropagatesLeft := by
  intro r hr x hx y hy hxy hpos
  have hseed : 0 < F r (Real.arccos y) := by
    simpa only [F, H, Real.cos_arccos hy.1.le hy.2.le] using hpos
  have hresult := F_positive_propagates h hr (Real.arccos_pos.mpr hy.2)
    (Real.arccos_le_arccos hxy) (Real.arccos_lt_pi.mpr hx.1) hseed
  simpa only [F, H, Real.cos_arccos hx.1.le hx.2.le] using hresult

/-- The finite-rate premise excludes actual theta zeros on every open upper
semicircle, without a positive-anchor hypothesis. -/
theorem actual_theta_no_zero_interior_of_premise
    (h : TAYLORS_PRODIGY_PREMISE) {r x : ℝ}
    (hr : 0 < r) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AWPIRH.theta (AngularMaster.circlePoint r x) ≠ 0 :=
  actual_no_zero_on_interior_circle
    (angularSlopePositivePropagatesLeft_of_premise h) hr hx

/-- An actual theta zero cannot be positive real. This is unconditional and
uses the retained explicit low-height zero-free estimate. -/
theorem actual_theta_zero_real_nonpositive {z : ℂ}
    (hz : AWPIRH.theta z = 0) (hi : z.im = 0) : z.re ≤ 0 := by
  by_contra h
  have hp : 0 < z.re := lt_of_not_ge h
  have hsq := AWPIRH.complex_sqrt_sq z
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hrne : (Complex.sqrt z).re ≠ 0 := by
    intro heq
    rw [heq] at hre
    nlinarith [sq_nonneg (Complex.sqrt z).im]
  have hisqrt : (Complex.sqrt z).im = 0 := by
    rw [hi] at him
    have hprod : (Complex.sqrt z).re * (Complex.sqrt z).im = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left hrne
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + Complex.sqrt z) = 0 := hz
  have hh := AngularMaster.actual_xi_zero_one_lt_abs_im hxi
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im,
    zero_div, zero_add, hisqrt, abs_zero] at hh
  exact (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 1)) hh

/-- Actual theta zero exclusion: the only research input is the named
first-order finite-rate premise. -/
theorem theta_zeros_nonpositive_of_premise
    (h : TAYLORS_PRODIGY_PREMISE) : AngularMaster.ThetaZerosNonpositive := by
  have hupper : ∀ w : ℂ, 0 < w.im → AWPIRH.theta w = 0 → False := by
    intro w hw hzero
    have hwne : w ≠ 0 := by
      intro heq
      rw [heq] at hw
      simp at hw
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    have hbounds := abs_lt.mp (Complex.abs_re_lt_norm.mpr (ne_of_gt hw))
    have hx : w.re / ‖w‖ ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · apply (lt_div_iff₀ hn).2
        simpa only [neg_one_mul] using hbounds.1
      · apply (div_lt_iff₀ hn).2
        simpa only [one_mul] using hbounds.2
    have hrepr := AngularMaster.circlePoint_norm_re_div hwne hw.le
    apply actual_theta_no_zero_interior_of_premise h hn hx
    rw [hrepr]
    exact hzero
  intro z hz
  have hi : z.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · apply hupper (conj z) (by simpa only [Complex.conj_im] using neg_pos.mpr hneg)
      exact AngularMaster.theta_zero_conj hz
    · exact hupper z hpos hz
  exact ⟨hi, actual_theta_zero_real_nonpositive hz hi⟩

/-- The conditional endpoint is Mathlib's native Riemann hypothesis. -/
theorem native_RH_of_TAYLORS_PRODIGY_PREMISE
    (h : TAYLORS_PRODIGY_PREMISE) : _root_.RiemannHypothesis :=
  AngularMaster.native_RH_iff_theta_zeros_nonpositive.mpr
    (theta_zeros_nonpositive_of_premise h)

end TaylorsProdigy
