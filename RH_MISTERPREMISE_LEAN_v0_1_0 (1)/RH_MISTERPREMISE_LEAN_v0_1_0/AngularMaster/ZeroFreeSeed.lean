import AngularMaster.ZeroGeometry
import AngularMaster.ThetaKernelExplicitBound

/-!
An explicit low-height zero-free seed from the theta Mellin representation.
The constants are quantitative and independent of RH or any computed zeros.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

open OverflowResidueRH Complex

private def thetaExplicitDecay
    (hupper : ∀ x : ℝ, 1 ≤ x →
      ‖hurwitzThetaMellinKernel x‖ ≤ (3 / 8 : ℝ) * Real.exp (-x)) :
    MellinTwoSidedExponentialDecay hurwitzThetaMellinKernel := by
  refine
    { k := 1 / 2
      p := 1
      A := 3 / 8
      p_pos := by norm_num
      A_nonneg := by norm_num
      upper := by simpa using hupper
      lower := ?_ }
  intro x hx hxone
  have hypos : 0 < 1 / x := one_div_pos.mpr hx
  have hyone : 1 ≤ 1 / x := one_le_one_div hx hxone
  have hinv : hurwitzThetaMellinKernel x =
      ((((1 / x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        hurwitzThetaMellinKernel (1 / x)) := by
    simpa [hx.ne'] using
      hurwitzThetaMellinKernel_inversion (1 / x) hypos
  rw [hinv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hypos.le _)]
  calc
    (1 / x) ^ (1 / 2 : ℝ) * ‖hurwitzThetaMellinKernel (1 / x)‖ ≤
        (1 / x) ^ (1 / 2 : ℝ) * ((3 / 8 : ℝ) * Real.exp (-(1 / x))) :=
      mul_le_mul_of_nonneg_left (hupper (1 / x) hyone)
        (Real.rpow_nonneg hypos.le _)
    _ = (3 / 8 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / x)) := by
      rw [one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
      ring

private theorem completedZeta₀_norm_le_of_explicit_upper
    (hupper : ∀ x : ℝ, 1 ≤ x →
      ‖hurwitzThetaMellinKernel x‖ ≤ (3 / 8 : ℝ) * Real.exp (-x))
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (3 / 8 : ℝ) := by
  let D := thetaExplicitDecay hupper
  have hu : (s / 2).re - 1 ≤ (0 : ℕ) := by
    norm_num
    linarith
  have hl : -(0 : ℝ) - 2 ≤ (s / 2).re - 1 - D.k := by
    change -(0 : ℝ) - 2 ≤ (s / 2).re - 1 - 1 / 2
    simp only [Complex.div_ofNat_re]
    linarith
  have h := D.norm_mellin_le_factorial (s / 2) 0 hu (by simpa using hl)
    (hurwitzThetaMellinKernel_convergent (s / 2))
  norm_num [D, thetaExplicitDecay] at h
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div, Complex.norm_two]
  linarith

theorem norm_mul_sub_one_le_two {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 1) :
    ‖s * (s - 1)‖ ≤ 2 := by
  have him : s.im ^ 2 ≤ 1 := by
    have h := mul_self_le_mul_self (abs_nonneg s.im) ht
    simpa only [← sq, sq_abs, one_pow] using h
  have hre : s.re ^ 2 ≤ 1 := by nlinarith
  have hre' : (s.re - 1) ^ 2 ≤ 1 := by nlinarith
  have hn : ‖s‖ ^ 2 ≤ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hn' : ‖s - 1‖ ^ 2 ≤ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

private theorem xi_ne_zero_of_explicit_upper
    (hupper : ∀ x : ℝ, 1 ≤ x →
      ‖hurwitzThetaMellinKernel x‖ ≤ (3 / 8 : ℝ) * Real.exp (-x))
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 1) :
    AWPIRH.xi s ≠ 0 := by
  intro hz
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ (3 / 4 : ℝ) := by
    rw [norm_mul]
    calc
      ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤
          2 * (3 / 8 : ℝ) :=
        mul_le_mul (norm_mul_sub_one_le_two hs0 hs1 ht)
          (completedZeta₀_norm_le_of_explicit_upper hupper hs0 hs1)
          (norm_nonneg _) (by norm_num)
      _ = (3 / 4 : ℝ) := by norm_num
  linarith

/-- The pole-subtracted completed zeta function has a concrete uniform bound
on the closed critical strip. This comes from the literal theta kernel. -/
theorem actual_completedZeta₀_norm_le_three_eighths {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (3 / 8 : ℝ) :=
  completedZeta₀_norm_le_of_explicit_upper
    hurwitzThetaMellinKernel_explicit_upper_bound hs0 hs1

/-- The actual completed xi has no zeros at height at most one in the closed
critical strip. No zero computation, RH assumption, or sign premise is used. -/
theorem actual_xi_ne_zero_of_low_height {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 1) :
    AWPIRH.xi s ≠ 0 :=
  xi_ne_zero_of_explicit_upper hurwitzThetaMellinKernel_explicit_upper_bound
    hs0 hs1 ht

theorem actual_xi_zero_one_lt_abs_im {s : ℂ} (hz : AWPIRH.xi s = 0) :
    1 < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  exact actual_xi_ne_zero_of_low_height hs.1.le hs.2.le (le_of_not_gt hn) hz

end AngularMaster
