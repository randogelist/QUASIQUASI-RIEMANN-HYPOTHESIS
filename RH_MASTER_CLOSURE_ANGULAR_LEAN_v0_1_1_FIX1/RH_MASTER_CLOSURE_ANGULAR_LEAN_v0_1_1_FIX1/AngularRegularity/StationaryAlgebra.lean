import Mathlib

/-!
# Algebra and calculus of real Euler-logarithmic levels

This module contains identities for an arbitrary complex function `f`.
Every division by `f z` is accompanied by an explicit nonvanishing hypothesis
in the theorem that interprets the quotient.  The level-function and curvature
numerator identities themselves are division-free and also hold at zeros.

No sign condition, zero-location claim, or Riemann-hypothesis endpoint is
asserted here.  The real parameter `n` may in particular be an integer or a
dyadic level after coercion to `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate

namespace AngularRegularity

/-- The Euler logarithmic derivative, interpreted analytically away from zeros.
Lean's quotient is total; subsequent interpretation lemmas require `f z ≠ 0`. -/
def eulerLog (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv f z / f z

/-- The division-free function whose zeros are the real level `n` of `eulerLog`
at points where `f` is nonzero. -/
def levelFunction (f : ℂ → ℂ) (n : ℝ) (z : ℂ) : ℂ :=
  z * deriv f z - (n : ℂ) * f z

/-- The derivative of `levelFunction` when `f` and `deriv f` are differentiable. -/
def levelDerivativeModel (f : ℂ → ℂ) (n : ℝ) (z : ℂ) : ℂ :=
  z * deriv (deriv f) z + (1 - (n : ℂ)) * deriv f z

/-- A division-free form of the level equation. -/
theorem levelFunction_eq_zero_iff_mul_eq
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ) :
    levelFunction f n z = 0 ↔ z * deriv f z = (n : ℂ) * f z := by
  unfold levelFunction
  exact sub_eq_zero

/-- A level-function zero is an Euler-logarithmic level only when `f z ≠ 0`. -/
theorem levelFunction_eq_zero_iff_eulerLog_eq
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ) (hf0 : f z ≠ 0) :
    levelFunction f n z = 0 ↔ eulerLog f z = (n : ℂ) := by
  unfold levelFunction eulerLog
  rw [sub_eq_zero, div_eq_iff hf0]

/-- The level parameter is real, so a regular level-function zero has zero
imaginary part of the Euler logarithmic derivative. -/
theorem eulerLog_im_eq_zero_of_levelFunction_eq_zero
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ) (hf0 : f z ≠ 0)
    (hlevel : levelFunction f n z = 0) :
    (eulerLog f z).im = 0 := by
  rw [(levelFunction_eq_zero_iff_eulerLog_eq f n z hf0).mp hlevel]
  simp

/-- Exact complex derivative of the division-free level function. -/
theorem hasDerivAt_levelFunction
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z)
    (hdf : DifferentiableAt ℂ (deriv f) z) :
    HasDerivAt (levelFunction f n) (levelDerivativeModel f n z) z := by
  have hprod :
      HasDerivAt (fun w : ℂ => w * deriv f w)
        ((1 : ℂ) * deriv f z + z * deriv (deriv f) z) z :=
    (hasDerivAt_id z).mul hdf.hasDerivAt
  rw [one_mul] at hprod
  have hraw :
      HasDerivAt
        (fun w : ℂ => w * deriv f w - (n : ℂ) * f w)
        (deriv f z + z * deriv (deriv f) z -
          (n : ℂ) * deriv f z) z :=
    hprod.sub (hf.hasDerivAt.const_mul (n : ℂ))
  have hcoef :
      deriv f z + z * deriv (deriv f) z -
          (n : ℂ) * deriv f z =
        levelDerivativeModel f n z := by
    unfold levelDerivativeModel
    ring
  rw [hcoef] at hraw
  change HasDerivAt
    (fun w : ℂ => w * deriv f w - (n : ℂ) * f w)
    (levelDerivativeModel f n z) z
  exact hraw

theorem deriv_levelFunction
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z)
    (hdf : DifferentiableAt ℂ (deriv f) z) :
    deriv (levelFunction f n) z = levelDerivativeModel f n z :=
  (hasDerivAt_levelFunction f n z hf hdf).deriv

/-- Quotient-rule derivative of `eulerLog`, with the nonzero denominator visible. -/
theorem hasDerivAt_eulerLog
    (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z)
    (hdf : DifferentiableAt ℂ (deriv f) z)
    (hf0 : f z ≠ 0) :
    HasDerivAt (eulerLog f)
      (((deriv f z + z * deriv (deriv f) z) * f z -
        z * deriv f z * deriv f z) / (f z) ^ 2) z := by
  have hprod :
      HasDerivAt (fun w : ℂ => w * deriv f w)
        ((1 : ℂ) * deriv f z + z * deriv (deriv f) z) z :=
    (hasDerivAt_id z).mul hdf.hasDerivAt
  rw [one_mul] at hprod
  have hraw :
      HasDerivAt
        (fun w : ℂ => w * deriv f w / f w)
        (((deriv f z + z * deriv (deriv f) z) * f z -
          z * deriv f z * deriv f z) / (f z) ^ 2) z :=
    hprod.div hf.hasDerivAt hf0
  change HasDerivAt
    (fun w : ℂ => w * deriv f w / f w)
    (((deriv f z + z * deriv (deriv f) z) * f z -
      z * deriv f z * deriv f z) / (f z) ^ 2) z
  exact hraw

/-- At a regular real level, the derivative of `eulerLog` is the derivative
model of the level function divided by `f`. -/
theorem deriv_eulerLog_eq_levelDerivativeModel_div
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z)
    (hdf : DifferentiableAt ℂ (deriv f) z)
    (hf0 : f z ≠ 0)
    (hlevel : levelFunction f n z = 0) :
    deriv (eulerLog f) z = levelDerivativeModel f n z / f z := by
  rw [(hasDerivAt_eulerLog f z hf hdf hf0).deriv]
  have heq : z * deriv f z = (n : ℂ) * f z :=
    (levelFunction_eq_zero_iff_mul_eq f n z).mp hlevel
  calc
    _ = ((deriv f z + z * deriv (deriv f) z) * f z -
        ((n : ℂ) * f z) * deriv f z) / (f z) ^ 2 := by rw [heq]
    _ = levelDerivativeModel f n z / f z := by
      unfold levelDerivativeModel
      field_simp [hf0]
      ring

/-- Exact division-free complex curvature numerator at a level-function zero.
This is an algebraic identity: no differentiability or nonvanishing is needed. -/
theorem curvatureNumerator_complex_eq_of_levelFunction_eq_zero
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ)
    (hlevel : levelFunction f n z = 0) :
    z * levelDerivativeModel f n z * conj (f z) =
      z ^ 2 * deriv (deriv f) z * conj (f z) +
        ((n : ℂ) * (1 - (n : ℂ))) * (f z * conj (f z)) := by
  have heq : z * deriv f z = (n : ℂ) * f z :=
    (levelFunction_eq_zero_iff_mul_eq f n z).mp hlevel
  calc
    _ = z ^ 2 * deriv (deriv f) z * conj (f z) +
        (1 - (n : ℂ)) * (z * deriv f z) * conj (f z) := by
      unfold levelDerivativeModel
      ring
    _ = _ := by
      rw [heq]
      ring

/-- The real division-free curvature identity, with the scalar norm square
written explicitly.  It remains valid when `f z = 0`. -/
theorem curvatureNumerator_eq_of_levelFunction_eq_zero
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ)
    (hlevel : levelFunction f n z = 0) :
    (z * levelDerivativeModel f n z * conj (f z)).re =
      (z ^ 2 * deriv (deriv f) z * conj (f z)).re +
        n * (1 - n) * Complex.normSq (f z) := by
  rw [curvatureNumerator_complex_eq_of_levelFunction_eq_zero f n z hlevel]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- The same real identity using the actual derivative of `levelFunction`. -/
theorem actualCurvatureNumerator_eq_of_levelFunction_eq_zero
    (f : ℂ → ℂ) (n : ℝ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z)
    (hdf : DifferentiableAt ℂ (deriv f) z)
    (hlevel : levelFunction f n z = 0) :
    (z * deriv (levelFunction f n) z * conj (f z)).re =
      (z ^ 2 * deriv (deriv f) z * conj (f z)).re +
        n * (1 - n) * Complex.normSq (f z) := by
  rw [deriv_levelFunction f n z hf hdf]
  exact curvatureNumerator_eq_of_levelFunction_eq_zero f n z hlevel

end AngularRegularity
