/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.BorelCaratheodory
import RiemannHypothesis.ComplexAnalysis.GrowthRigidity

/-!
# From real-part growth to polynomial rigidity

Borel--Caratheodory converts a one-sided upper bound on the real part of an
entire function into a norm bound on a smaller disk.  Consequently, to prove
that an entire logarithm is affine it is enough to control its real part; one
does not need an a priori bound on its imaginary part or on a reciprocal
quotient.

The logarithmic formulation is particularly useful for a nowhere-zero entire
function `q`.  If `exp h = q`, then

`(h z).re = log ‖q z‖`.

Thus subquadratic upper growth of `log ‖q‖` forces every entire logarithm of
`q` to be affine.
-/

namespace OverflowResidueRH

open Metric Set

/-- One-sided subquadratic growth of the real part.  The additive constant is
uniform in `z` but may depend on `ε`.  This global-with-a-constant form is the
natural input for Borel--Caratheodory and is equivalent to the corresponding
eventual little-oh condition for continuous functions. -/
def HasSubquadraticUpperRealGrowth (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, (f z).re ≤ C + ε * ‖z‖ ^ 2

/-- The corresponding one-sided little-oh condition stated only at
infinity. -/
def HasSubquadraticUpperRealGrowthAtInfinity (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → (f z).re ≤ ε * ‖z‖ ^ 2

/-- For a continuous function, the eventual one-sided estimate can be made
global by adding a constant. -/
theorem HasSubquadraticUpperRealGrowthAtInfinity.toGlobal
    {f : ℂ → ℂ} (hupper : HasSubquadraticUpperRealGrowthAtInfinity f)
    (hf : Continuous f) : HasSubquadraticUpperRealGrowth f := by
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hupper ε hε
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hf.continuousOn
  let C : ℝ := max 0 C₀
  refine ⟨C, le_max_left _ _, fun z ↦ ?_⟩
  by_cases hz : R ≤ ‖z‖
  · exact (hbound z hz).trans <| by
      have hC : 0 ≤ C := le_max_left _ _
      linarith
  · have hzball : z ∈ closedBall (0 : ℂ) R := by
      simp only [mem_closedBall, dist_zero_right]
      exact le_of_not_ge hz
    have hre : (f z).re ≤ ‖f z‖ := Complex.re_le_norm _
    have hnorm : ‖f z‖ ≤ C :=
      (hC₀ z hzball).trans (le_max_right _ _)
    have hquad : 0 ≤ ε * ‖z‖ ^ 2 := mul_nonneg hε.le (sq_nonneg _)
    exact hre.trans <| hnorm.trans <| by linarith

/-- Borel--Caratheodory upgrades a one-sided subquadratic real-part estimate
for an entire function to subquadratic norm growth. -/
theorem hasSubquadraticNormGrowth_of_upperRealGrowth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hupper : HasSubquadraticUpperRealGrowth f) :
    HasSubquadraticNormGrowth f := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hupper (ε / 16) (by positivity)
  let K : ℝ := 2 * C + 2 + 3 * ‖f 0‖
  let R₀ : ℝ := max 1 (2 * K / ε)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨R₀, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro z hz
  have hz_one : 1 ≤ ‖z‖ :=
    le_trans (le_max_left (1 : ℝ) (2 * K / ε)) hz
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz_one
  let R : ℝ := 2 * ‖z‖
  let M : ℝ := C + (ε / 16) * R ^ 2 + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hmaps : MapsTo f (ball 0 R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hwR : ‖w‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hw
    have hsq : ‖w‖ ^ 2 ≤ R ^ 2 := by
      nlinarith [norm_nonneg w]
    exact (hbound w).trans <| by
      dsimp [M]
      nlinarith
  have hzball : z ∈ ball (0 : ℂ) R := by
    simp only [mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  have hbc := Complex.borelCaratheodory hM hf.differentiableOn
    hmaps hR hzball
  have hbc' : ‖f z‖ ≤ 2 * M + 3 * ‖f 0‖ := by
    calc
      ‖f z‖ ≤
          2 * M * ‖z‖ / (R - ‖z‖) +
            ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := hbc
      _ = 2 * M + 3 * ‖f 0‖ := by
        dsimp [R]
        field_simp [ne_of_gt hz_pos]
        ring
  have hzK : 2 * K / ε ≤ ‖z‖ :=
    le_trans (le_max_right (1 : ℝ) (2 * K / ε)) hz
  have hmul : 2 * K ≤ ‖z‖ * ε := (div_le_iff₀ hε).mp hzK
  have hKlinear : K ≤ (ε / 2) * ‖z‖ := by
    nlinarith
  have hnorm_sq : ‖z‖ ≤ ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg z]
  have hKsq : K ≤ (ε / 2) * ‖z‖ ^ 2 :=
    hKlinear.trans <|
      mul_le_mul_of_nonneg_left hnorm_sq (by positivity)
  calc
    ‖f z‖ ≤ 2 * M + 3 * ‖f 0‖ := hbc'
    _ = (ε / 2) * ‖z‖ ^ 2 + K := by
      dsimp [M, R, K]
      ring
    _ ≤ (ε / 2) * ‖z‖ ^ 2 + (ε / 2) * ‖z‖ ^ 2 :=
      add_le_add (le_refl _) hKsq
    _ = ε * ‖z‖ ^ 2 := by ring

/-- A quotient has subquadratic logarithmic norm growth if its logarithmic
maximum is `o(r²)`, with an additive constant allowed for each `ε`. -/
def HasSubquadraticLogNormGrowth (q : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, Real.log ‖q z‖ ≤ C + ε * ‖z‖ ^ 2

/-- One-sided logarithmic norm growth stated as a genuine little-oh
condition at infinity. -/
def HasSubquadraticLogNormGrowthAtInfinity (q : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → Real.log ‖q z‖ ≤ ε * ‖z‖ ^ 2

/-- A maximum-modulus form of order strictly below two: for every positive
quadratic coefficient, the norm is bounded by a constant times
`exp (ε ‖z‖²)`. -/
def HasSubquadraticExponentialNormGrowth (q : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
    ∀ z : ℂ, ‖q z‖ ≤ A * Real.exp (ε * ‖z‖ ^ 2)

/-- A conventional finite-exponential-type estimate. -/
def HasLinearExponentialNormGrowth (q : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
    ∀ z : ℂ, ‖q z‖ ≤ A * Real.exp (B * ‖z‖)

/-- Every finite-exponential-type bound is subquadratic in the
maximum-modulus sense. -/
theorem HasLinearExponentialNormGrowth.toSubquadraticExponentialNormGrowth
    {q : ℂ → ℂ} (hq : HasLinearExponentialNormGrowth q) :
    HasSubquadraticExponentialNormGrowth q := by
  obtain ⟨A, B, hA, hB, hbound⟩ := hq
  intro ε hε
  let D : ℝ := B ^ 2 / (4 * ε)
  refine ⟨A * Real.exp D, mul_pos hA (Real.exp_pos D), fun z ↦ ?_⟩
  have hexponent : B * ‖z‖ ≤ D + ε * ‖z‖ ^ 2 := by
    dsimp [D]
    have hsquare : 0 ≤ (B - 2 * ε * ‖z‖) ^ 2 := sq_nonneg _
    have haux : B * ‖z‖ - ε * ‖z‖ ^ 2 ≤ B ^ 2 / (4 * ε) := by
      apply (le_div_iff₀ (show 0 < 4 * ε by positivity)).mpr
      nlinarith
    linarith
  calc
    ‖q z‖ ≤ A * Real.exp (B * ‖z‖) := hbound z
    _ ≤ A * Real.exp (D + ε * ‖z‖ ^ 2) := by
      gcongr
    _ = (A * Real.exp D) * Real.exp (ε * ‖z‖ ^ 2) := by
      rw [Real.exp_add]
      ring

/-- For a nowhere-zero function, a subquadratic maximum-modulus estimate
implies subquadratic logarithmic norm growth. -/
theorem HasSubquadraticExponentialNormGrowth.toLogNormGrowth
    {q : ℂ → ℂ} (hq : HasSubquadraticExponentialNormGrowth q)
    (hq_ne : ∀ z : ℂ, q z ≠ 0) :
    HasSubquadraticLogNormGrowth q := by
  intro ε hε
  obtain ⟨A, hA, hbound⟩ := hq ε hε
  let C : ℝ := max 0 (Real.log A)
  refine ⟨C, le_max_left _ _, fun z ↦ ?_⟩
  have hqnorm : 0 < ‖q z‖ := norm_pos_iff.mpr (hq_ne z)
  calc
    Real.log ‖q z‖ ≤
        Real.log (A * Real.exp (ε * ‖z‖ ^ 2)) :=
      Real.log_le_log hqnorm (hbound z)
    _ = Real.log A + ε * ‖z‖ ^ 2 := by
      rw [Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp]
    _ ≤ C + ε * ‖z‖ ^ 2 := by
      exact add_le_add
        (show Real.log A ≤ C from le_max_right (0 : ℝ) (Real.log A))
        (le_refl _)

/-- The real part of any entire logarithm inherits logarithmic norm growth
from its exponential. -/
theorem HasSubquadraticLogNormGrowth.upperRealGrowth_of_exp
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowth q)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    HasSubquadraticUpperRealGrowth h := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hq ε hε
  refine ⟨C, hC, fun z ↦ ?_⟩
  calc
    (h z).re = Real.log ‖q z‖ := by
      rw [← hexp z, Complex.norm_exp, Real.log_exp]
    _ ≤ C + ε * ‖z‖ ^ 2 := hbound z

/-- The at-infinity logarithmic bound transfers pointwise to the real part
of any exponential logarithm. -/
theorem HasSubquadraticLogNormGrowthAtInfinity.upperRealGrowth_of_exp
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowthAtInfinity q)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    HasSubquadraticUpperRealGrowthAtInfinity h := by
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hq ε hε
  refine ⟨R, hR, fun z hz ↦ ?_⟩
  calc
    (h z).re = Real.log ‖q z‖ := by
      rw [← hexp z, Complex.norm_exp, Real.log_exp]
    _ ≤ ε * ‖z‖ ^ 2 := hbound z hz

/-- If the quotient has a continuous global logarithm, an at-infinity
logarithmic norm estimate extends across the omitted compact disk.  This is
the precise bridge between the asymptotic `o(‖z‖²)` formulation and the
global-with-a-constant formulation used by Borel--Caratheodory. -/
theorem HasSubquadraticLogNormGrowthAtInfinity.toGlobal_of_exp
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowthAtInfinity q)
    (hh : Continuous h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    HasSubquadraticLogNormGrowth q := by
  have hupper : HasSubquadraticUpperRealGrowth h :=
    (hq.upperRealGrowth_of_exp hexp).toGlobal hh
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hupper ε hε
  refine ⟨C, hC, fun z ↦ ?_⟩
  calc
    Real.log ‖q z‖ = (h z).re := by
      rw [← hexp z, Complex.norm_exp, Real.log_exp]
    _ ≤ C + ε * ‖z‖ ^ 2 := hbound z

/-- An entire logarithm of a quotient with subquadratic logarithmic norm
growth has subquadratic norm growth.  This is the reusable
Borel--Caratheodory transfer theorem. -/
theorem HasSubquadraticLogNormGrowth.log_hasSubquadraticNormGrowth
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowth q)
    (hh : Differentiable ℂ h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    HasSubquadraticNormGrowth h :=
  hasSubquadraticNormGrowth_of_upperRealGrowth hh
    (hq.upperRealGrowth_of_exp hexp)

/-- Genuine one-sided little-oh growth of `log ‖q‖` at infinity already
controls the full norm of an entire logarithm.  Continuity on the omitted
compact disk supplies the harmless additive constant. -/
theorem
    HasSubquadraticLogNormGrowthAtInfinity.log_hasSubquadraticNormGrowth
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowthAtInfinity q)
    (hh : Differentiable ℂ h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    HasSubquadraticNormGrowth h :=
  hasSubquadraticNormGrowth_of_upperRealGrowth hh <|
    (hq.upperRealGrowth_of_exp hexp).toGlobal hh.continuous

/-- Subquadratic logarithmic norm growth of a zero-free quotient is enough
to make any entire logarithm affine. -/
theorem eq_exp_affine_of_subquadraticLogNormGrowth
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowth q)
    (hh : Differentiable ℂ h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    ∃ a b : ℂ, ∀ z : ℂ, q z = Complex.exp (a + b * z) := by
  obtain ⟨a, b, hab⟩ :=
    differentiable_eq_affine_of_subquadraticNormGrowth hh
      (hq.log_hasSubquadraticNormGrowth hh hexp)
  exact ⟨a, b, fun z ↦ by rw [← hexp z, hab z]⟩

/-- At-infinity logarithmic norm growth is likewise enough for an affine
exponential quotient. -/
theorem eq_exp_affine_of_subquadraticLogNormGrowthAtInfinity
    {q h : ℂ → ℂ} (hq : HasSubquadraticLogNormGrowthAtInfinity q)
    (hh : Differentiable ℂ h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z) :
    ∃ a b : ℂ, ∀ z : ℂ, q z = Complex.exp (a + b * z) := by
  obtain ⟨a, b, hab⟩ :=
    differentiable_eq_affine_of_subquadraticNormGrowth hh
      (hq.log_hasSubquadraticNormGrowth hh hexp)
  exact ⟨a, b, fun z ↦ by rw [← hexp z, hab z]⟩

end OverflowResidueRH
