/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The completed ξ function and its critical-line pullback

The textbook completed xi function
`ξ(s) = ½·s·(s−1)·π^(−s/2)·Γ(s/2)·ζ(s)`
and the critical-line pullback `Ξ(z) := ξ(½ + i·z)`, under which the Riemann
Hypothesis becomes "all zeros of `XiPullback` are real".

(The Mathlib-grounded entire `Ξ` and the entire pullback are added in
`Xi.FunctionalEquation` / later in this directory.)
-/

namespace OverflowResidueRH

open Complex

/-- The completed xi function
  ξ(s) = ½ · s · (s − 1) · π^(−s/2) · Γ(s/2) · ζ(s).
Entire, with zeros exactly at the nontrivial Riemann-zeta zeros. -/
noncomputable def completedXiFunction (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)
    * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
    * Complex.Gamma (s / 2)
    * riemannZeta s

/-- The **critical-line pullback** `Ξ(z) := ξ(½ + i·z)`. The map
`z ↦ ½ + i·z` sends `z ∈ ℝ` to the critical line `Re = ½`, converting
RH into "all zeros of `XiPullback` are real". -/
noncomputable def XiPullback (z : ℂ) : ℂ :=
  completedXiFunction ((1 / 2 : ℂ) + Complex.I * z)

/-- **Completed-xi regularity package.** Bundles the three classical facts
about `ξ` that the rest of the chain consumes — entire differentiability,
Schwarz reflection (`ξ(s̄) = conj ξ(s)`), and the functional equation
(`ξ(s) = ξ(1 − s)`).

Insulates downstream lemmas from the choice of definition for `ξ`: the
current `completedXiFunction` formula exposes `Γ`-poles whose cancellation
with trivial `ζ`-zeros is non-trivial to formalize directly, so we route
through this abstract interface. A later phase inhabits it via the
Mathlib-grounded entire `ξ`. -/
structure CompletedXiRegularity : Prop where
  differentiable :
    ∀ s : ℂ, DifferentiableAt ℂ completedXiFunction s
  schwarz :
    ∀ s : ℂ, completedXiFunction (star s) = star (completedXiFunction s)
  functional_equation :
    ∀ s : ℂ, completedXiFunction s = completedXiFunction (1 - s)

/-- **PROVED — real part of the critical shift.** `Re(½ + I·z) = ½ − Im z`. -/
theorem critical_shift_re (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z).re = 1 / 2 - z.im := by
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub]
  have h_half : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  rw [h_half]
  ring

/-- **PROVED — algebraic star/critical-shift identity.**
`star ((½ : ℂ) + I · z) = (½ : ℂ) − I · star z.` The `−I · star z`
(not `+I · star z`) is what makes the pullback Schwarz identity require the
functional equation in addition to ξ-Schwarz. -/
theorem critical_shift_star (z : ℂ) :
    star ((1 / 2 : ℂ) + Complex.I * z) =
      (1 / 2 : ℂ) - Complex.I * star z := by
  simp only [Complex.star_def]
  rw [map_add, map_mul, Complex.conj_I]
  have h_half : (starRingEnd ℂ) ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        Complex.conj_ofReal]
  rw [h_half]
  ring

-- =====================================================================
-- Mathlib-grounded entire ξ
-- =====================================================================

/-- **Mathlib-grounded entire ξ.** `entireRiemannXi s :=
½·s·(s−1)·completedRiemannZeta₀ s + ½`. Entire *by construction* (Mathlib's
pole-subtracted `completedRiemannZeta₀` is entire), and equal to the classical
`½·s·(s−1)·Λ(s)` after substituting
`Λ(s) = completedRiemannZeta₀ s − 1/s − 1/(1−s)`. -/
noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

/-- **Schwarz reflection condition for `entireRiemannXi`.** The classical
fact `ξ(s̄) = conj ξ(s)`, named as a `Prop`; discharged unconditionally in
`Xi.FunctionalEquation` via the Mellin transform / Hurwitz even FE-pair. -/
def EntireXi.schwarzReflection : Prop :=
  ∀ s : ℂ, entireRiemannXi (star s) = star (entireRiemannXi s)

/-- **Regularity package for the Mathlib-grounded ξ.** Analogue of
`CompletedXiRegularity`, built on `completedRiemannZeta₀`. -/
structure EntireRiemannXiRegularity : Prop where
  differentiable :
    ∀ s : ℂ, DifferentiableAt ℂ entireRiemannXi s
  schwarz :
    ∀ s : ℂ, entireRiemannXi (star s) = star (entireRiemannXi s)
  functional_equation :
    ∀ s : ℂ, entireRiemannXi s = entireRiemannXi (1 - s)

/-- **Mathlib-grounded critical-line pullback.**
`EntireXiPullback z := entireRiemannXi (½ + i·z)`. -/
noncomputable def EntireXiPullback (z : ℂ) : ℂ :=
  entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z)

/-- **Non-triviality of `EntireXiPullback`.** Not identically zero. -/
def EntireXiPullback_nontrivial : Prop :=
  ∃ z : ℂ, EntireXiPullback z ≠ 0

end OverflowResidueRH
