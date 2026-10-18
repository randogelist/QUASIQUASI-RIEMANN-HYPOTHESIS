import AngularMaster.QQRHGeometry
import AngularMaster.ComplexScaleProduct

/-! Weak zero-height bounds imply the slope-two geometry. All analytic input
is explicit in these transport lemmas; the unconditional input is supplied
separately by the theta-kernel estimate. -/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

theorem square_angle_le_cutoff_of_le_abs_im {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : w ≠ 0) (h : m * |w.re| ≤ |w.im|) :
    (w ^ 2).re / ‖w ^ 2‖ ≤ slopeCutoff m := by
  have hsum : 0 < w.re ^ 2 + w.im ^ 2 := by
    rw [← norm_square_eq_re_sq_add_im_sq]
    exact norm_pos_iff.mpr (pow_ne_zero 2 hw)
  have hden : 0 < 1 + m ^ 2 := by positivity
  have hsquare : (m * |w.re|) ^ 2 ≤ |w.im| ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  rw [mul_pow, sq_abs, sq_abs] at hsquare
  rw [square_re_eq_re_sq_sub_im_sq, norm_square_eq_re_sq_add_im_sq, slopeCutoff]
  apply (div_le_div_iff₀ hsum hden).2
  nlinarith only [hsquare]

theorem theta_zero_angle_le_neg_three_fifths_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → 1 < |s.im|)
    {z : ℂ} (hz0 : z ≠ 0) (hz : AWPIRH.theta z = 0) :
    z.re / ‖z‖ ≤ -(3 / 5 : ℝ) := by
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hw : w ≠ 0 := by
    intro h
    apply hz0
    rw [← hsq, h]
    simp
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hstrip := xi_zero_mem_critical_strip hxi
  have hbig := hheight _ hxi
  have hwre : |w.re| < (1 / 2 : ℝ) := by
    apply abs_lt.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : 1 < |w.im| := by
    simpa using hbig
  have hangle := square_angle_le_cutoff_of_le_abs_im
    (by norm_num : (0 : ℝ) < 2) hw (by linarith : 2 * |w.re| ≤ |w.im|)
  simpa only [hsq, slopeCutoff_two] using hangle

theorem actualComplexScale_sector_of_zero_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → 1 < |s.im|)
    (i : ActualPairIndex) :
    -(actualComplexScale i).re / ‖actualComplexScale i‖ ≤ -(3 / 5 : ℝ) := by
  have h := theta_zero_angle_le_neg_three_fifths_of_height hheight
    (neg_ne_zero.mpr (actualComplexScale_ne_zero i))
    (actual_theta_neg_complexScale_zero i)
  simpa only [Complex.neg_re, norm_neg] using h

theorem QQRH_two_of_xi_zero_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → 1 < |s.im|) : QQRH 2 := by
  apply QQRH_two_of_theta_sector_nonvanishing
  intro z hz0 hx hz
  exact not_lt_of_ge (theta_zero_angle_le_neg_three_fifths_of_height hheight hz0 hz) hx

end AngularMaster
