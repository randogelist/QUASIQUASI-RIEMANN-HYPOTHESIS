import RiemannHypothesis.Xi.ThetaKernelMellinGrowth
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section

namespace AngularMaster

open Complex Real OverflowResidueRH

private theorem exp_neg_two_le : Real.exp (-2) ≤ (9 / 64 : ℝ) := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    exact h
  have hsq : (64 / 9 : ℝ) ≤ Real.exp 2 := by
    have hpos := Real.exp_pos 1
    have htwo : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [htwo]
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos 2)).2 (by nlinarith)

private theorem theta_decay_upper (x : ℝ) (hx : 1 ≤ x) :
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ ≤
      (3 / 8 : ℝ) * Real.exp (-x) := by
  have hxpos : 0 < x := by linarith
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpx : (3 : ℝ) ≤ Real.pi * x := by nlinarith
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hnegthree : Real.exp (-3) ≤ (1 / 4 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 3)).2 (by linarith)
  have hE : Real.exp (-Real.pi * x) ≤ (1 / 4 : ℝ) := by
    exact (Real.exp_le_exp.mpr (by nlinarith : -Real.pi * x ≤ -3)).trans hnegthree
  have hEmul : Real.exp (-Real.pi * x) ≤
      (9 / 64 : ℝ) * Real.exp (-x) := by
    calc
      Real.exp (-Real.pi * x) ≤ Real.exp (-x + (-2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-x) * Real.exp (-2) := Real.exp_add _ _
      _ ≤ Real.exp (-x) * (9 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_left exp_neg_two_le (Real.exp_nonneg _)
      _ = _ := by ring
  have hden : 0 < 1 - Real.exp (-Real.pi * x) := by linarith
  have hfrac : 2 / (1 - Real.exp (-Real.pi * x)) ≤ (8 / 3 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have htheta := norm_jacobiTheta_sub_one_le
    (τ := Complex.I * (x : ℂ)) (by simpa using hxpos)
  simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at htheta
  calc
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ ≤
        2 / (1 - Real.exp (-Real.pi * x)) * Real.exp (-Real.pi * x) := htheta
    _ ≤ (8 / 3 : ℝ) * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)
    _ ≤ (8 / 3 : ℝ) * ((9 / 64 : ℝ) * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hEmul (by norm_num)
    _ = _ := by ring

theorem hurwitzThetaMellinKernel_explicit_upper_bound (x : ℝ) (hx : 1 ≤ x) :
    ‖OverflowResidueRH.hurwitzThetaMellinKernel x‖ ≤
      (3 / 8 : ℝ) * Real.exp (-x) := by
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
  exact theta_decay_upper x hx

end AngularMaster
