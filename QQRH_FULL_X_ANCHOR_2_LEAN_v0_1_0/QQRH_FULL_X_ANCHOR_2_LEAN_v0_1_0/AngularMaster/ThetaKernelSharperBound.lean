import AngularMaster.ThetaKernelExplicitBound

/-!
A sharper explicit exponential bound for the actual modified theta kernel.
The rational rate is 31/10 and the amplitude is 21/10. All constants are
derived from Mathlib's pi bound and a finite exponential Taylor lower bound.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

open Complex Real OverflowResidueRH

theorem exp_neg_thirtyone_tenths_le :
    Real.exp (-(31 / 10 : ℝ)) ≤ (1 / 21 : ℝ) := by
  have hexp : (21 : ℝ) ≤ Real.exp (31 / 10 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 31 / 10) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos (31 / 10))).2 (by linarith)

private theorem jacobiTheta_sharper_upper_bound (x : ℝ) (hx : 1 ≤ x) :
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ ≤
      (21 / 10 : ℝ) * Real.exp (-((31 / 10 : ℝ) * x)) := by
  have hxpos : 0 < x := by linarith
  have hpi : (31 / 10 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hpx : (31 / 10 : ℝ) ≤ Real.pi * x := by nlinarith
  have hE : Real.exp (-Real.pi * x) ≤ (1 / 21 : ℝ) := by
    exact (Real.exp_le_exp.mpr
      (by nlinarith : -Real.pi * x ≤ -(31 / 10 : ℝ))).trans
        exp_neg_thirtyone_tenths_le
  have hrate : Real.exp (-Real.pi * x) ≤
      Real.exp (-((31 / 10 : ℝ) * x)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hden : 0 < 1 - Real.exp (-Real.pi * x) := by linarith
  have hfrac : 2 / (1 - Real.exp (-Real.pi * x)) ≤ (21 / 10 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have htheta := norm_jacobiTheta_sub_one_le
    (τ := Complex.I * (x : ℂ)) (by simpa using hxpos)
  simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at htheta
  calc
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ ≤
        2 / (1 - Real.exp (-Real.pi * x)) * Real.exp (-Real.pi * x) := htheta
    _ ≤ (21 / 10 : ℝ) * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)
    _ ≤ (21 / 10 : ℝ) * Real.exp (-((31 / 10 : ℝ) * x)) :=
      mul_le_mul_of_nonneg_left hrate (by norm_num)

theorem hurwitzThetaMellinKernel_sharper_upper_bound (x : ℝ) (hx : 1 ≤ x) :
    ‖OverflowResidueRH.hurwitzThetaMellinKernel x‖ ≤
      (21 / 10 : ℝ) * Real.exp (-((31 / 10 : ℝ) * x)) := by
  by_cases hxeq : x = 1
  · subst x
    rw [hurwitzThetaMellinKernel_one, norm_zero]
    positivity
  have hxlt : 1 < x := lt_of_le_of_ne hx (Ne.symm hxeq)
  rw [hurwitzThetaMellinKernel_eq_evenKernel_sub_one hxlt]
  have heven : (HurwitzZeta.evenKernel 0 x : ℂ) =
      jacobiTheta (Complex.I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  rw [Complex.ofReal_sub, Complex.ofReal_one, heven]
  exact jacobiTheta_sharper_upper_bound x hx

end AngularMaster
