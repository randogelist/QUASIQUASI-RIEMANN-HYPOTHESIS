import AngularMaster.ZeroFreeSeed

/-! A sharper elementary bound for the quadratic xi prefactor. -/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

/-- On the closed critical strip, AM–GM improves the coarse bound `1+t²`. -/
theorem norm_mul_sub_one_le_im_sq_add_half {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖s * (s - 1)‖ ≤ s.im ^ 2 + 1 / 2 := by
  have hre : s.re ^ 2 + (s.re - 1) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hn : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hn' : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero]
    ring
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

theorem norm_mul_sub_one_le_height_sq_add_half {s : ℂ} {H : ℝ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ H) :
    ‖s * (s - 1)‖ ≤ H ^ 2 + 1 / 2 := by
  have him : s.im ^ 2 ≤ H ^ 2 := by
    simpa only [← sq, sq_abs] using
      mul_self_le_mul_self (abs_nonneg s.im) ht
  exact (norm_mul_sub_one_le_im_sq_add_half hs0 hs1).trans (by linarith)

end AngularMaster
