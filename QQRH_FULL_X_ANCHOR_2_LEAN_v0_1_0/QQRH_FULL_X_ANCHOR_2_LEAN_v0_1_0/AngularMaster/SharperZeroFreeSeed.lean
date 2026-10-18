import AngularMaster.ZeroGeometry
import AngularMaster.ThetaKernelSharperBound
import AngularMaster.MellinEndpointBound

/-!
An unconditional explicit zero-free height bound from the actual theta kernel.
Keeping the endpoints of the Mellin integrals improves the completed-zeta norm
bound to 1/31 on the closed critical strip and excludes xi zeros at height ≤ 5.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

open OverflowResidueRH Complex

private def thetaSharperDecay :
    MellinTwoSidedExponentialDecay hurwitzThetaMellinKernel := by
  refine
    { k := 1 / 2
      p := 31 / 10
      A := 21 / 10
      p_pos := by norm_num
      A_nonneg := by norm_num
      upper := hurwitzThetaMellinKernel_sharper_upper_bound
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
        (1 / x) ^ (1 / 2 : ℝ) *
          ((21 / 10 : ℝ) * Real.exp (-((31 / 10 : ℝ) * (1 / x)))) :=
      mul_le_mul_of_nonneg_left
        (hurwitzThetaMellinKernel_sharper_upper_bound (1 / x) hyone)
        (Real.rpow_nonneg hypos.le _)
    _ = (21 / 10 : ℝ) * x ^ (-(1 / 2 : ℝ)) *
        Real.exp (-((31 / 10 : ℝ) / x)) := by
      rw [one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
      simp only [div_eq_mul_inv]
      ring

theorem actual_completedZeta₀_norm_le_one_thirtyone {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (1 / 31 : ℝ) := by
  let D := thetaSharperDecay
  have hu : (s / 2).re - 1 ≤ (0 : ℝ) := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hl : -(2 : ℝ) ≤ (s / 2).re - 1 - D.k := by
    change -(2 : ℝ) ≤ (s / 2).re - 1 - 1 / 2
    simp only [Complex.div_ofNat_re]
    linarith
  have h := norm_mellin_le_endpoint D (s / 2) hu hl
    (hurwitzThetaMellinKernel_convergent (s / 2))
  norm_num [D, thetaSharperDecay] at h
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div, Complex.norm_two]
  nlinarith [exp_neg_thirtyone_tenths_le]

private theorem norm_mul_sub_one_le_twenty_six {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 5) :
    ‖s * (s - 1)‖ ≤ 26 := by
  have him : s.im ^ 2 ≤ 25 := by
    have h := mul_self_le_mul_self (abs_nonneg s.im) ht
    nlinarith [sq_abs s.im]
  have hre : s.re ^ 2 ≤ 1 := by nlinarith
  have hre' : (s.re - 1) ^ 2 ≤ 1 := by nlinarith
  have hn : ‖s‖ ^ 2 ≤ 26 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hn' : ‖s - 1‖ ^ 2 ≤ 26 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

theorem actual_xi_ne_zero_of_height_le_five {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 5) :
    AWPIRH.xi s ≠ 0 := by
  intro hz
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ (26 / 31 : ℝ) := by
    rw [norm_mul]
    calc
      ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤
          26 * (1 / 31 : ℝ) :=
        mul_le_mul (norm_mul_sub_one_le_twenty_six hs0 hs1 ht)
          (actual_completedZeta₀_norm_le_one_thirtyone hs0 hs1)
          (norm_nonneg _) (by norm_num)
      _ = (26 / 31 : ℝ) := by norm_num
  linarith

theorem actual_xi_zero_five_lt_abs_im {s : ℂ} (hz : AWPIRH.xi s = 0) :
    5 < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  exact actual_xi_ne_zero_of_height_le_five hs.1.le hs.2.le (le_of_not_gt hn) hz

end AngularMaster
