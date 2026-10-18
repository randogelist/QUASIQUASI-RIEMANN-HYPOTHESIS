import MisterPremise.Cutoff
import AngularMaster.AnchorHeight
import AngularMaster.QQRHGeometry

/-! Actual xi/theta zeros lie inside the domain of MISTERPREMISE. -/

set_option autoImplicit false
noncomputable section

namespace MisterPremise

open AWPIRH AngularMaster

theorem theta_zero_radius_large {z : ℂ} (hz : theta z = 0) :
    (169 / 4 : ℝ) < ‖z‖ := by
  let w := Complex.sqrt z
  have hxi : xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hg := actual_xi_zero_thirteen_halves_lt_abs_im hxi
  have hg' : (13 / 2 : ℝ) < |w.im| := by
    simpa only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
      zero_add] using hg
  have hs : w ^ 2 = z := complex_sqrt_sq z
  rw [← hs, norm_square_eq_re_sq_add_im_sq]
  nlinarith [sq_abs w.im, sq_nonneg w.re]

theorem theta_zero_angle_lt_neg_kappa {z : ℂ} (hz : theta z = 0) :
    z.re / ‖z‖ < -kappa ‖z‖ := by
  let w := Complex.sqrt z
  have hxi : xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hstrip := xi_zero_mem_critical_strip hxi
  have hlow : -(1 / 2 : ℝ) < w.re := by
    have : 0 < (1 / 2 : ℝ) + w.re := by
      simpa using hstrip.1
    linarith
  have hhigh : w.re < (1 / 2 : ℝ) := by
    have : (1 / 2 : ℝ) + w.re < 1 := by
      simpa using hstrip.2
    linarith
  have hh : w.re ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos (by linarith : 0 < (1 / 2 : ℝ) - w.re)
      (by linarith : 0 < (1 / 2 : ℝ) + w.re)]
  have hg := actual_xi_zero_thirteen_halves_lt_abs_im hxi
  have hg' : (13 / 2 : ℝ) < |w.im| := by
    simpa only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
      zero_add] using hg
  have hg2 : (169 / 4 : ℝ) < w.im ^ 2 := by
    nlinarith [sq_abs w.im]
  have hs : w ^ 2 = z := complex_sqrt_sq z
  have hn : ‖z‖ = w.im ^ 2 + w.re ^ 2 := by
    rw [← hs, norm_square_eq_re_sq_add_im_sq]
    ring
  have hre : z.re = w.re ^ 2 - w.im ^ 2 := by
    rw [← hs, square_re_eq_re_sq_sub_im_sq]
  rw [hre, hn]
  exact square_angle_lt_neg_kappa hg2 hh

theorem nonreal_angle_mem_Ioo {z : ℂ} (hi : z.im ≠ 0) :
    z.re / ‖z‖ ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hz : z ≠ 0 := by
    intro h
    apply hi
    simp [h]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsq := Complex.sq_norm_sub_sq_re z
  have him : 0 < z.im ^ 2 := sq_pos_of_ne_zero hi
  have hre := Complex.abs_re_le_norm z
  have hb := abs_le.mp hre
  constructor
  · apply (lt_div_iff₀ hn).2
    nlinarith
  · apply (div_lt_iff₀ hn).2
    nlinarith

/-- The original premise is needed at every hypothetical nonreal zero, with
strict room on both sides of its angular coordinate. -/
theorem theta_nonreal_zero_in_premise_region {z : ℂ}
    (hz : theta z = 0) (hi : z.im ≠ 0) :
    (255 / 7 : ℝ) < ‖z‖ ∧
      -1 < z.re / ‖z‖ ∧ z.re / ‖z‖ < -kappa ‖z‖ := by
  refine ⟨?_, (nonreal_angle_mem_Ioo hi).1, theta_zero_angle_lt_neg_kappa hz⟩
  have h := theta_zero_radius_large hz
  linarith

end MisterPremise
