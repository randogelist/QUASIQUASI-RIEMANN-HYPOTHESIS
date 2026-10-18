import AngularMaster.ThetaKernelExplicitBound

set_option autoImplicit false
noncomputable section

namespace AngularMaster
open Complex Real OverflowResidueRH

abbrev anchorRate : ℝ := 6283 / 2000
abbrev anchorExpCap : ℝ := 100 / 2313
abbrev anchorAmplitude : ℝ := 2 / (1 - anchorExpCap ^ 3)

theorem exp_neg_anchorRate_le :
    Real.exp (-anchorRate) ≤ anchorExpCap := by
  have hexp : (2313 / 100 : ℝ) ≤ Real.exp anchorRate := by
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num [anchorRate] : (0 : ℝ) ≤ anchorRate) 12
    norm_num [anchorRate, Finset.sum_range_succ, Nat.factorial] at h
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos anchorRate)).2 (by
    norm_num [anchorExpCap] at *
    linarith)

private theorem theta_anchor_term_bound (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    ‖Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 *
      (Complex.I * (x : ℂ)))‖ ≤
      Real.exp (-(anchorRate * x)) * (anchorExpCap ^ 3) ^ n := by
  have hp : 0 < anchorRate := by norm_num [anchorRate]
  have hpi : anchorRate ≤ Real.pi := by
    norm_num [anchorRate] at *
    linarith [Real.pi_gt_d4]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    simpa only [sq] using (show (n : ℝ) ≤ n * n by exact_mod_cast Nat.le_mul_self n)
  have hsq : (1 : ℝ) + 3 * n ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hnx : (n : ℝ) ≤ x * n := by nlinarith
  have hexponent : -Real.pi * x * ((n : ℝ) + 1) ^ 2 ≤
      -(anchorRate * x) + (-anchorRate) * (3 * n) := by
    have h1 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ anchorRate * x by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpi
      (show 0 ≤ x * ((n : ℝ) + 1) ^ 2 by positivity)
    nlinarith
  have heq : (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 *
      (Complex.I * (x : ℂ))).re = -Real.pi * x * ((n : ℝ) + 1) ^ 2 := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [Complex.norm_exp, heq]
  calc
    Real.exp (-Real.pi * x * ((n : ℝ) + 1) ^ 2) ≤
        Real.exp (-(anchorRate * x) + (-anchorRate) * (3 * n)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-(anchorRate * x)) * (Real.exp (-anchorRate) ^ 3) ^ n := by
      rw [Real.exp_add]
      congr 1
      rw [← pow_mul]
      convert Real.exp_nat_mul (-anchorRate) (3 * n) using 1 <;> push_cast <;> ring
    _ ≤ Real.exp (-(anchorRate * x)) * (anchorExpCap ^ 3) ^ n := by
      gcongr
      exact exp_neg_anchorRate_le

private theorem jacobiTheta_anchor_upper_bound (x : ℝ) (hx : 1 ≤ x) :
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ ≤
      anchorAmplitude * Real.exp (-(anchorRate * x)) := by
  have hxpos : 0 < x := by linarith
  have hτ : 0 < (Complex.I * (x : ℂ)).im := by simpa using hxpos
  have hq0 : (0 : ℝ) ≤ anchorExpCap ^ 3 := by norm_num [anchorExpCap]
  have hq1 : anchorExpCap ^ 3 < (1 : ℝ) := by norm_num [anchorExpCap]
  have hs : HasSum (fun n : ℕ => Real.exp (-(anchorRate * x)) * (anchorExpCap ^ 3) ^ n)
      (Real.exp (-(anchorRate * x)) / (1 - anchorExpCap ^ 3)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-(anchorRate * x)))
  have hterm := theta_anchor_term_bound x hx
  have hsum : Summable (fun n : ℕ =>
      ‖Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 *
        (Complex.I * (x : ℂ)))‖) :=
    .of_nonneg_of_le (fun n => norm_nonneg _) hterm hs.summable
  have hnorm := (norm_tsum_le_tsum_norm hsum).trans
    ((hsum.tsum_mono hs.summable hterm).trans_eq hs.tsum_eq)
  calc
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ =
        2 * ‖∑' n : ℕ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 *
          (Complex.I * (x : ℂ)))‖ := by
      rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ), norm_mul, Complex.norm_two]
    _ ≤ 2 * (Real.exp (-(anchorRate * x)) / (1 - anchorExpCap ^ 3)) := by gcongr
    _ = anchorAmplitude * Real.exp (-(anchorRate * x)) := by
      dsimp [anchorAmplitude]
      ring

theorem hurwitzThetaMellinKernel_anchor_upper_bound (x : ℝ) (hx : 1 ≤ x) :
    ‖hurwitzThetaMellinKernel x‖ ≤
      anchorAmplitude * Real.exp (-(anchorRate * x)) := by
  by_cases hxeq : x = 1
  · subst x
    rw [hurwitzThetaMellinKernel_one, norm_zero]
    norm_num [anchorAmplitude, anchorExpCap]
    positivity
  have hxlt : 1 < x := lt_of_le_of_ne hx (Ne.symm hxeq)
  rw [hurwitzThetaMellinKernel_eq_evenKernel_sub_one hxlt]
  have heven : (HurwitzZeta.evenKernel 0 x : ℂ) =
      jacobiTheta (Complex.I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  rw [Complex.ofReal_sub, Complex.ofReal_one, heven]
  exact jacobiTheta_anchor_upper_bound x hx

end AngularMaster
