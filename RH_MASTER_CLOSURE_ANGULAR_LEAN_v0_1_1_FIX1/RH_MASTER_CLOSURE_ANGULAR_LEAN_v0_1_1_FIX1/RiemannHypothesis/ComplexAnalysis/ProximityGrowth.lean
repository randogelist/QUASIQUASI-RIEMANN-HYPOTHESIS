/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.Divisor
import RiemannHypothesis.ComplexAnalysis.RealPartGrowth

/-!
# Nevanlinna proximity bounds and pointwise logarithmic growth

This module avoids pointwise lower estimates for a denominator.  The First
Main Theorem bounds the proximity of a quotient represented codiscretely as
`f * g⁻¹` by the characteristics of `f` and `g`, up to an explicit constant.
Poisson's formula then turns the circle average of `log⁺ ‖q‖` into a
pointwise upper bound for the real part of any entire logarithm of `q`.
-/

open Filter Metric Real Set
open ValueDistribution

namespace OverflowResidueRH

/-- The Nevanlinna proximity `m(r,q)` is `o(r²)` at infinity. -/
def HasSubquadraticProximityGrowthAtInfinity (q : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ r : ℝ, R ≤ r → proximity q ⊤ r ≤ ε * r ^ 2

/-- A pointwise subquadratic upper logarithmic bound implies subquadratic
circle-average proximity. -/
theorem HasSubquadraticLogNormGrowthAtInfinity.toProximityGrowthAtInfinity
    {f : ℂ → ℂ}
    (hgrowth : HasSubquadraticLogNormGrowthAtInfinity f)
    (hf : Continuous f) :
    HasSubquadraticProximityGrowthAtInfinity f := by
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hgrowth ε hε
  refine ⟨R, hR, fun r hr ↦ ?_⟩
  rw [proximity_top]
  apply circleAverage_mono_on_of_le_circle
    ((continuous_posLog.comp
      (continuous_norm.comp hf)).continuousOn.circleIntegrable')
  intro z hz
  have hr0 : 0 ≤ r := le_trans hR hr
  have hzr : ‖z‖ = r := by
    have : dist z 0 = |r| := by
      simpa [mem_sphere] using hz
    simpa [dist_zero_right, abs_of_nonneg hr0] using this
  have hzR : R ≤ ‖z‖ := by simpa [hzr] using hr
  have hzbound := hbound z hzR
  rw [hzr] at hzbound
  exact max_le (mul_nonneg (le_of_lt hε) (sq_nonneg r)) hzbound

/-- Poisson's formula upgrades subquadratic circle-average proximity to the
pointwise one-sided logarithmic norm estimate.  On the circle of radius
`2‖z‖`, the Poisson kernel lies between `0` and `3`. -/
theorem HasSubquadraticProximityGrowthAtInfinity.toLogNormGrowthAtInfinity
    {q h : ℂ → ℂ} (hprox : HasSubquadraticProximityGrowthAtInfinity q)
    (hh : Differentiable ℂ h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    HasSubquadraticLogNormGrowthAtInfinity q := by
  intro ε hε
  obtain ⟨R, hR, hprox_bound⟩ := hprox (ε / 12) (by positivity)
  let R₀ : ℝ := max 1 R
  refine ⟨R₀, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro z hz
  let r : ℝ := ‖z‖
  have hr1 : 1 ≤ r := le_trans (le_max_left (1 : ℝ) R) hz
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hRr : R ≤ 2 * r := by
    have : R ≤ r := le_trans (le_max_right (1 : ℝ) R) hz
    linarith
  have hzball : z ∈ ball (0 : ℂ) (2 * r) := by
    simpa [r, mem_ball, dist_zero_right] using (show r < 2 * r by linarith)
  let u : ℂ → ℝ := fun w ↦ (h w).re
  have hu_harm : InnerProductSpace.HarmonicOnNhd u
      (closedBall (0 : ℂ) (2 * r)) := by
    intro w _hw
    exact (hh.analyticAt w).harmonicAt_re
  have hpoisson := hu_harm.circleAverage_poissonKernel_smul hzball
  have hqdiff : Differentiable ℂ q := by
    have hfun : (fun w : ℂ ↦ Complex.exp (h w)) = q := funext hexp
    rw [← hfun]
    exact hh.cexp
  have hposInt : CircleIntegrable (fun w : ℂ ↦ log⁺ ‖q w‖)
      0 (2 * r) :=
    (continuous_posLog.comp
      (continuous_norm.comp hqdiff.continuous)).continuousOn.circleIntegrable'
  have hden : ∀ w ∈ sphere (0 : ℂ) |2 * r|, w - z ≠ 0 := by
    intro w hw hwz
    have hw_eq : w = z := sub_eq_zero.mp hwz
    subst w
    have hz_norm : ‖z‖ = |2 * r| := by
      simpa [mem_sphere, dist_zero_right] using hw
    rw [show ‖z‖ = r from rfl,
      abs_of_pos (show 0 < 2 * r by positivity)] at hz_norm
    linarith
  have hleftInt : CircleIntegrable (poissonKernel 0 z • u) 0 (2 * r) := by
    change CircleIntegrable (fun w ↦ poissonKernel 0 z w * u w) 0 (2 * r)
    apply ContinuousOn.circleIntegrable'
    apply ContinuousOn.mul
    · rw [poissonKernel_eq_re_herglotzRieszKernel]
      simp only [Function.comp_def, herglotzRieszKernel_def]
      intro w hw
      have hwden : w - 0 - (z - 0) ≠ 0 := by simpa using hden w hw
      apply Complex.continuous_re.continuousAt.comp_continuousWithinAt
      exact ((continuousAt_id.sub continuousAt_const).add
        (continuousAt_const.sub continuousAt_const)).div
          ((continuousAt_id.sub continuousAt_const).sub
            (continuousAt_const.sub continuousAt_const)) hwden |>.continuousWithinAt
    · exact (Complex.continuous_re.comp hh.continuous).continuousOn
  have hpointwise : ∀ w ∈ sphere (0 : ℂ) |2 * r|,
      (poissonKernel 0 z • u) w ≤ 3 * log⁺ ‖q w‖ := by
    intro w hw
    have hw' : w ∈ sphere (0 : ℂ) (2 * r) := by
      simpa [abs_of_pos (show 0 < 2 * r by positivity)] using hw
    have hk_le : poissonKernel 0 z w ≤ 3 := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      simp only [Function.comp_apply, herglotzRieszKernel_def, sub_zero]
      have hk := re_herglotzRieszKernel_le hw' hzball
      calc
        ((w + z) / (w - z)).re ≤
            (2 * r + ‖z‖) / (2 * r - ‖z‖) := by
          simpa using hk
        _ = 3 := by
          rw [show ‖z‖ = r from rfl]
          field_simp [ne_of_gt hr_pos]
          ring
    have hk_nonneg : 0 ≤ poissonKernel 0 z w := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      simp only [Function.comp_apply, herglotzRieszKernel_def, sub_zero]
      have hk := le_re_herglotzRieszKernel hw' hzball
      calc
        0 ≤ (2 * r - ‖z‖) / (2 * r + ‖z‖) := by
          rw [show ‖z‖ = r from rfl]
          apply div_nonneg <;> linarith
        _ ≤ ((w + z) / (w - z)).re := by simpa using hk
    have hu_log : u w = log ‖q w‖ := by
      dsimp [u]
      rw [← hexp w, Complex.norm_exp, Real.log_exp]
    have hu_le : u w ≤ log⁺ ‖q w‖ := by
      rw [hu_log]
      exact le_max_right _ _
    change poissonKernel 0 z w * u w ≤ 3 * log⁺ ‖q w‖
    calc
      poissonKernel 0 z w * u w ≤
          poissonKernel 0 z w * log⁺ ‖q w‖ := by gcongr
      _ ≤ 3 * log⁺ ‖q w‖ := by gcongr; exact posLog_nonneg
  have havg : circleAverage (poissonKernel 0 z • u) 0 (2 * r) ≤
      circleAverage (fun w : ℂ ↦ 3 * log⁺ ‖q w‖) 0 (2 * r) := by
    apply circleAverage_mono hleftInt
    · simpa [smul_eq_mul] using hposInt.const_fun_smul (a := (3 : ℝ))
    · exact hpointwise
  have hprox_z : proximity q ⊤ (2 * r) ≤ (ε / 12) * (2 * r) ^ 2 :=
    hprox_bound (2 * r) hRr
  calc
    log ‖q z‖ = u z := by
      dsimp [u]
      rw [← hexp z, Complex.norm_exp, Real.log_exp]
    _ = circleAverage (poissonKernel 0 z • u) 0 (2 * r) := hpoisson.symm
    _ ≤ circleAverage (fun w : ℂ ↦ 3 * log⁺ ‖q w‖) 0 (2 * r) := havg
    _ = 3 * proximity q ⊤ (2 * r) := by
      calc
        circleAverage (fun w : ℂ ↦ 3 * log⁺ ‖q w‖) 0 (2 * r) =
            3 * circleAverage (fun w : ℂ ↦ log⁺ ‖q w‖) 0 (2 * r) := by
          simpa [smul_eq_mul] using
            (circleAverage_fun_smul (f := fun w : ℂ ↦ log⁺ ‖q w‖)
              (c := 0) (R := 2 * r) (a := (3 : ℝ)))
        _ = 3 * proximity q ⊤ (2 * r) := by rw [proximity_top]
    _ ≤ 3 * ((ε / 12) * (2 * r) ^ 2) := by gcongr
    _ = ε * ‖z‖ ^ 2 := by dsimp [r]; ring

/-- The Nevanlinna characteristic `T(r,f)` is `o(r²)` at infinity. -/
def HasSubquadraticCharacteristicGrowthAtInfinity (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ r : ℝ, R ≤ r → characteristic f ⊤ r ≤ ε * r ^ 2

/-- Since proximity is the nonnegative summand of the characteristic, a
subquadratic characteristic has subquadratic proximity. -/
theorem
    HasSubquadraticCharacteristicGrowthAtInfinity.toProximityGrowthAtInfinity
    {f : ℂ → ℂ}
    (hgrowth : HasSubquadraticCharacteristicGrowthAtInfinity f) :
    HasSubquadraticProximityGrowthAtInfinity f := by
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hgrowth ε hε
  let R₀ : ℝ := max 1 R
  refine ⟨R₀, le_trans zero_le_one (le_max_left _ _), fun r hr ↦ ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left (1 : ℝ) R) hr
  have hrR : R ≤ r := le_trans (le_max_right (1 : ℝ) R) hr
  have hcount : 0 ≤ logCounting f ⊤ r := logCounting_nonneg hr1
  have hchar := hbound r hrR
  simp only [characteristic, Pi.add_apply] at hchar
  linarith

/-- For an entire analytic function there are no poles, so its characteristic
equals its proximity. -/
theorem
    HasSubquadraticProximityGrowthAtInfinity.toCharacteristicGrowthAtInfinity_of_analytic
    {f : ℂ → ℂ} (hgrowth : HasSubquadraticProximityGrowthAtInfinity f)
    (hf : AnalyticOnNhd ℂ f univ) :
    HasSubquadraticCharacteristicGrowthAtInfinity f := by
  have hcount : logCounting f ⊤ = 0 := by
    rw [logCounting_top]
    rw [negPart_eq_zero.mpr
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)]
    exact map_zero _
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hgrowth ε hε
  exact ⟨R, hR, fun r hr ↦ by
    simpa [characteristic, hcount] using hbound r hr⟩

/-- For a quotient, proximity control of the numerator and characteristic
control of the denominator suffice.  The First Main Theorem controls the
proximity of the reciprocal denominator up to a fixed constant. -/
theorem
    hasSubquadraticProximityGrowthAtInfinity_of_proximity_and_characteristic
    {f g q : ℂ → ℂ}
    (hfmer : Meromorphic f) (hgmer : Meromorphic g)
    (hquot : q =ᶠ[codiscrete ℂ] f * g⁻¹)
    (hfprox : HasSubquadraticProximityGrowthAtInfinity f)
    (hgchar : HasSubquadraticCharacteristicGrowthAtInfinity g) :
    HasSubquadraticProximityGrowthAtInfinity q := by
  intro ε hε
  obtain ⟨Rf, hRf, hfbound⟩ := hfprox (ε / 4) (by positivity)
  obtain ⟨Rg, hRg, hgbound⟩ := hgchar (ε / 4) (by positivity)
  let C : ℝ := max |log ‖g 0‖| |log ‖meromorphicTrailingCoeffAt g 0‖|
  let Rc : ℝ := max 1 (2 * C / ε)
  let R : ℝ := max Rf (max Rg Rc)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_max_of_le_left (abs_nonneg _)
  have hRnonneg : 0 ≤ R := hRf.trans (le_max_left _ _)
  refine ⟨R, hRnonneg, ?_⟩
  intro r hr
  have hrRf : Rf ≤ r := le_trans (le_max_left _ _) hr
  have hrRg : Rg ≤ r :=
    le_trans (le_max_left Rg Rc) (le_trans (le_max_right Rf _) hr)
  have hrRc : Rc ≤ r :=
    le_trans (le_max_right Rg Rc) (le_trans (le_max_right Rf _) hr)
  have hr1 : 1 ≤ r := le_trans (le_max_left (1 : ℝ) _) hrRc
  have hr_ne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1)
  have hClinear : C ≤ (ε / 2) * r := by
    have hCr : 2 * C / ε ≤ r :=
      le_trans (le_max_right (1 : ℝ) (2 * C / ε)) hrRc
    have hmul : 2 * C ≤ r * ε := (div_le_iff₀ hε).mp hCr
    nlinarith
  have hr_sq : r ≤ r ^ 2 := by nlinarith
  have hCsq : C ≤ (ε / 2) * r ^ 2 :=
    hClinear.trans (mul_le_mul_of_nonneg_left hr_sq (by positivity))
  have hcongr : proximity q ⊤ r = proximity (f * g⁻¹) ⊤ r :=
    proximity_congr_codiscrete hquot hr_ne
  have hmul := proximity_mul_top_le hfmer hgmer.inv r
  have hginvprox : proximity g⁻¹ ⊤ r ≤ characteristic g⁻¹ ⊤ r := by
    have hcount : 0 ≤ logCounting g⁻¹ ⊤ r := logCounting_nonneg hr1
    simp only [characteristic, Pi.add_apply]
    linarith
  have hfirst := characteristic_sub_characteristic_inv_le hgmer (R := r)
  have hginvchar : characteristic g⁻¹ ⊤ r ≤
      characteristic g ⊤ r + C := by
    have hdiff : characteristic g⁻¹ ⊤ r - characteristic g ⊤ r ≤ C := by
      calc
        characteristic g⁻¹ ⊤ r - characteristic g ⊤ r ≤
            |characteristic g⁻¹ ⊤ r - characteristic g ⊤ r| :=
          le_abs_self _
        _ = |characteristic g ⊤ r - characteristic g⁻¹ ⊤ r| :=
          abs_sub_comm _ _
        _ ≤ C := hfirst
    linarith
  calc
    proximity q ⊤ r = proximity (f * g⁻¹) ⊤ r := hcongr
    _ ≤ proximity f ⊤ r + proximity g⁻¹ ⊤ r := hmul
    _ ≤ proximity f ⊤ r + characteristic g⁻¹ ⊤ r := by
      gcongr
    _ ≤ proximity f ⊤ r + (characteristic g ⊤ r + C) := by
      linarith
    _ ≤ (ε / 4) * r ^ 2 + ((ε / 4) * r ^ 2 + C) :=
      add_le_add (hfbound r hrRf) (by linarith [hgbound r hrRg])
    _ ≤ (ε / 4) * r ^ 2 +
        ((ε / 4) * r ^ 2 + (ε / 2) * r ^ 2) := by
      gcongr
    _ = ε * r ^ 2 := by ring

/-- If `q = f * g⁻¹` away from a codiscrete exceptional set, then
subquadratic characteristics of `f` and `g` imply subquadratic proximity of
`q`.  Common zeros need no pointwise division or lower product estimate. -/
theorem hasSubquadraticProximityGrowthAtInfinity_of_characteristic_factors
    {f g q : ℂ → ℂ}
    (hfmer : Meromorphic f) (hgmer : Meromorphic g)
    (hquot : q =ᶠ[codiscrete ℂ] f * g⁻¹)
    (hfchar : HasSubquadraticCharacteristicGrowthAtInfinity f)
    (hgchar : HasSubquadraticCharacteristicGrowthAtInfinity g) :
    HasSubquadraticProximityGrowthAtInfinity q := by
  intro ε hε
  obtain ⟨Rf, hRf, hfbound⟩ := hfchar (ε / 4) (by positivity)
  obtain ⟨Rg, hRg, hgbound⟩ := hgchar (ε / 4) (by positivity)
  let C : ℝ := max |log ‖g 0‖| |log ‖meromorphicTrailingCoeffAt g 0‖|
  let Rc : ℝ := max 1 (2 * C / ε)
  let R : ℝ := max Rf (max Rg Rc)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_max_of_le_left (abs_nonneg _)
  have hRnonneg : 0 ≤ R := hRf.trans (le_max_left _ _)
  refine ⟨R, hRnonneg, ?_⟩
  intro r hr
  have hrRf : Rf ≤ r := le_trans (le_max_left _ _) hr
  have hrRg : Rg ≤ r :=
    le_trans (le_max_left Rg Rc) (le_trans (le_max_right Rf _) hr)
  have hrRc : Rc ≤ r :=
    le_trans (le_max_right Rg Rc) (le_trans (le_max_right Rf _) hr)
  have hr1 : 1 ≤ r := le_trans (le_max_left (1 : ℝ) _) hrRc
  have hr_ne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1)
  have hClinear : C ≤ (ε / 2) * r := by
    have hCr : 2 * C / ε ≤ r :=
      le_trans (le_max_right (1 : ℝ) (2 * C / ε)) hrRc
    have hmul : 2 * C ≤ r * ε := (div_le_iff₀ hε).mp hCr
    nlinarith
  have hr_sq : r ≤ r ^ 2 := by nlinarith
  have hCsq : C ≤ (ε / 2) * r ^ 2 :=
    hClinear.trans (mul_le_mul_of_nonneg_left hr_sq (by positivity))
  have hcongr : proximity q ⊤ r = proximity (f * g⁻¹) ⊤ r :=
    proximity_congr_codiscrete hquot hr_ne
  have hmul := proximity_mul_top_le hfmer hgmer.inv r
  have hfprox : proximity f ⊤ r ≤ characteristic f ⊤ r := by
    have hcount : 0 ≤ logCounting f ⊤ r := logCounting_nonneg hr1
    simp only [characteristic, Pi.add_apply]
    linarith
  have hginvprox : proximity g⁻¹ ⊤ r ≤ characteristic g⁻¹ ⊤ r := by
    have hcount : 0 ≤ logCounting g⁻¹ ⊤ r := logCounting_nonneg hr1
    simp only [characteristic, Pi.add_apply]
    linarith
  have hfirst := characteristic_sub_characteristic_inv_le hgmer (R := r)
  have hginvchar : characteristic g⁻¹ ⊤ r ≤ characteristic g ⊤ r + C := by
    have hdiff : characteristic g⁻¹ ⊤ r - characteristic g ⊤ r ≤ C := by
      calc
        characteristic g⁻¹ ⊤ r - characteristic g ⊤ r ≤
            |characteristic g⁻¹ ⊤ r - characteristic g ⊤ r| :=
          le_abs_self _
        _ = |characteristic g ⊤ r - characteristic g⁻¹ ⊤ r| :=
          abs_sub_comm _ _
        _ ≤ C := hfirst
    linarith
  calc
    proximity q ⊤ r = proximity (f * g⁻¹) ⊤ r := hcongr
    _ ≤ proximity f ⊤ r + proximity g⁻¹ ⊤ r := hmul
    _ ≤ characteristic f ⊤ r + characteristic g⁻¹ ⊤ r :=
      add_le_add hfprox hginvprox
    _ ≤ characteristic f ⊤ r + (characteristic g ⊤ r + C) := by
      linarith
    _ ≤ (ε / 4) * r ^ 2 + ((ε / 4) * r ^ 2 + C) :=
      add_le_add (hfbound r hrRf) (by linarith [hgbound r hrRg])
    _ ≤ (ε / 4) * r ^ 2 +
        ((ε / 4) * r ^ 2 + (ε / 2) * r ^ 2) := by
      gcongr
    _ = ε * r ^ 2 := by ring

end OverflowResidueRH
