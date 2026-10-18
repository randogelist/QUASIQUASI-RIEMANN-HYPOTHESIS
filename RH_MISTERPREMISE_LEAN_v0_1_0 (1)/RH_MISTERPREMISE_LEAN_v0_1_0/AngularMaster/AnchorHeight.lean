import AngularMaster.ThetaKernelAnchorBound
import AngularMaster.MellinAnchorBound
import AngularMaster.MellinPairedBound
import AngularMaster.StripProductBound

set_option autoImplicit false
noncomputable section

namespace AngularMaster
open OverflowResidueRH Complex MeasureTheory Set

private def thetaAnchorDecay :
    MellinTwoSidedExponentialDecay hurwitzThetaMellinKernel := by
  refine
    { k := 1 / 2
      p := anchorRate
      A := anchorAmplitude
      p_pos := by norm_num [anchorRate]
      A_nonneg := by norm_num [anchorAmplitude, anchorExpCap]
      upper := hurwitzThetaMellinKernel_anchor_upper_bound
      lower := ?_ }
  intro x hx hxone
  have hypos : 0 < 1 / x := one_div_pos.mpr hx
  have hyone : 1 ≤ 1 / x := one_le_one_div hx hxone
  have hinv : hurwitzThetaMellinKernel x =
      ((((1 / x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        hurwitzThetaMellinKernel (1 / x)) := by
    simpa [hx.ne'] using hurwitzThetaMellinKernel_inversion (1 / x) hypos
  rw [hinv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hypos.le _)]
  calc
    (1 / x) ^ (1 / 2 : ℝ) * ‖hurwitzThetaMellinKernel (1 / x)‖ ≤
        (1 / x) ^ (1 / 2 : ℝ) *
          (anchorAmplitude * Real.exp (-(anchorRate * (1 / x)))) :=
      mul_le_mul_of_nonneg_left
        (hurwitzThetaMellinKernel_anchor_upper_bound (1 / x) hyone)
        (Real.rpow_nonneg hypos.le _)
    _ = anchorAmplitude * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(anchorRate / x)) := by
      rw [one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
      simp only [div_eq_mul_inv]
      ring

private theorem anchor_weighted_integral_le :
    (∫ x : ℝ in Ioi 1, (x ^ (-1 : ℝ) + x ^ (-(1/2) : ℝ)) *
      Real.exp (-(anchorRate * x))) ≤
      Real.exp (-anchorRate) / anchorRate *
        (2 - 1 / (anchorRate + 2) - 1 / (2 * anchorRate + 3)) := by
  have hp : 0 < anchorRate := by norm_num [anchorRate]
  have h1 := integral_Ioi_one_rpow_neg_exp_le (a := 1) (by norm_num) hp
  have hhalf := integral_Ioi_one_rpow_neg_exp_le (a := 1/2) (by norm_num) hp
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ) *
      Real.exp (-(anchorRate * x))) (Ioi 1) :=
    integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat 0 hp (by norm_num)
  have hihalf : IntegrableOn (fun x : ℝ => x ^ (-(1/2) : ℝ) *
      Real.exp (-(anchorRate * x))) (Ioi 1) :=
    integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat 0 hp (by norm_num)
  simp_rw [add_mul]
  rw [integral_add hi1 hihalf]
  norm_num [anchorRate] at h1 hhalf ⊢
  linarith

/-- An explicit analytic bound on the pole-subtracted completed zeta.
It uses a rational theta-series bound and weighted Mellin integrals only. -/
theorem actual_completedZeta₀_norm_le_nine_three_eightyfive {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (9 / 385 : ℝ) := by
  let D := thetaAnchorDecay
  have hs0' : 0 ≤ (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hs1' : (s / 2).re ≤ (1 / 2 : ℝ) := by
    simp only [Complex.div_ofNat_re]
    linarith
  have h := norm_mellin_le_paired_endpoint D (by rfl) (s / 2) hs0' hs1'
    (hurwitzThetaMellinKernel_convergent (s / 2))
  simp only [show (-1 / 2 : ℝ) = -(1/2 : ℝ) by ring] at h
  change ‖mellin hurwitzThetaMellinKernel (s / 2)‖ ≤
    anchorAmplitude * (∫ x : ℝ in Ioi 1,
      (x ^ (-1 : ℝ) + x ^ (-(1/2) : ℝ)) * Real.exp (-(anchorRate * x))) at h
  have hA : 0 ≤ anchorAmplitude := by norm_num [anchorAmplitude, anchorExpCap]
  have hi := mul_le_mul_of_nonneg_left anchor_weighted_integral_le hA
  have hcap := exp_neg_anchorRate_le
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div, Complex.norm_two]
  norm_num [anchorRate, anchorAmplitude, anchorExpCap] at h hi hcap ⊢
  nlinarith

/-- All actual xi zeros lie strictly above height 13/2 in absolute value. -/
theorem actual_xi_zero_thirteen_halves_lt_abs_im {s : ℂ} (hz : AWPIRH.xi s = 0) :
    (13 / 2 : ℝ) < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  have ht : |s.im| ≤ (13 / 2 : ℝ) := le_of_not_gt hn
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hprod := norm_mul_sub_one_le_height_sq_add_half hs.1.le hs.2.le ht
  have hc := actual_completedZeta₀_norm_le_nine_three_eightyfive hs.1.le hs.2.le
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ (1539 / 1540 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ ((13 / 2 : ℝ) ^ 2 + 1 / 2) * (9 / 385 : ℝ) :=
        mul_le_mul hprod hc (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  linarith

end AngularMaster
