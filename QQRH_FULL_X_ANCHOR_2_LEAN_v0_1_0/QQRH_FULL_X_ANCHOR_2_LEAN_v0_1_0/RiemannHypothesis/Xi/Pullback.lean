/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import RiemannHypothesis.ComplexAnalysis.LogDerivative
import RiemannHypothesis.Xi.Definitions
import RiemannHypothesis.Xi.FunctionalEquation

/-!
# Pullback chain rule between the z-plane and s-plane

The chain rule `Λ[Ξ](z) = i · Λ[ξ](½ + i·z)` for the critical-line pullback,
plus the differentiability facts it consumes. Converts the z-plane
anti-Herglotz statement into the s-plane left-half-plane sign statement.
-/

namespace OverflowResidueRH

open Complex

/-- **PROVED — inner derivative.** `HasDerivAt (fun z => ½ + I·z) I z`,
the derivative of the critical-shift map is `I` at every point. -/
theorem hasDerivAt_critical_shift (z : ℂ) :
    HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) Complex.I z := by
  have h1 : HasDerivAt (fun z : ℂ => z) (1 : ℂ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z : ℂ => Complex.I * z) (Complex.I * 1) z :=
    h1.const_mul Complex.I
  have h3 : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z)
                       (0 + Complex.I * 1) z :=
    (hasDerivAt_const z (1 / 2 : ℂ)).add h2
  simpa using h3

/-- ⭐ **PROVED — chain rule for `XiPullback`.** Under differentiability
of `completedXiFunction` at the pullback point,
  `Λ[Ξ](z) = I · Λ[ξ](½ + I·z)`.
The explicit converter that unlocks attacks on the explicit ξ formula. -/
theorem XiPullback_logDeriv_chain_rule
    {z : ℂ}
    (hxi_diff : DifferentiableAt ℂ completedXiFunction
                  ((1 / 2 : ℂ) + Complex.I * z)) :
    logDerivativeResponse XiPullback z =
      Complex.I *
        (deriv completedXiFunction ((1 / 2 : ℂ) + Complex.I * z) /
          completedXiFunction ((1 / 2 : ℂ) + Complex.I * z)) := by
  have h_outer : HasDerivAt completedXiFunction
                  (deriv completedXiFunction ((1 / 2 : ℂ) + Complex.I * z))
                  ((1 / 2 : ℂ) + Complex.I * z) := hxi_diff.hasDerivAt
  have h_inner := hasDerivAt_critical_shift z
  have h_chain : HasDerivAt
                  (fun w : ℂ => completedXiFunction ((1 / 2 : ℂ) + Complex.I * w))
                  (deriv completedXiFunction ((1 / 2 : ℂ) + Complex.I * z)
                    * Complex.I) z := by
    have h := h_outer.comp z h_inner
    simpa [Function.comp_def] using h
  unfold logDerivativeResponse XiPullback
  rw [h_chain.deriv]
  ring

/-- **Hypothesis — `completedXiFunction` is differentiable on the open
left half-plane `{s : Re s < ½}`.** Non-trivial to inhabit for the
Γ-based definition (Γ has poles at non-positive integers; the actual `ξ`
is entire), routed through `CompletedXiRegularity`. -/
def CompletedXiDifferentiableOnLeftHalfPlane : Prop :=
  ∀ s : ℂ, s.re < (1 / 2 : ℝ) → DifferentiableAt ℂ completedXiFunction s

/-- ⭐ **PROVED — completed-xi regularity ⟹ left-half-plane
differentiability.** -/
theorem completedXiRegularity_gives_leftHalfDiff
    (H : CompletedXiRegularity) :
    CompletedXiDifferentiableOnLeftHalfPlane :=
  fun s _ => H.differentiable s

/-- ⭐ **PROVED — `XiPullback` is differentiable from `CompletedXiRegularity`.**
The composition of the entire inner map `z ↦ (1/2) + I·z` with the
everywhere-differentiable outer `completedXiFunction`. -/
theorem XiPullback_differentiableAt_of_completedXiRegularity
    (H : CompletedXiRegularity) (z : ℂ) :
    DifferentiableAt ℂ XiPullback z := by
  unfold XiPullback
  have h_inner : DifferentiableAt ℂ
                  (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z :=
    (differentiableAt_const _).add
      ((differentiableAt_const _).mul differentiableAt_fun_id)
  have h_outer : DifferentiableAt ℂ completedXiFunction
                  ((1 / 2 : ℂ) + Complex.I * z) :=
    H.differentiable _
  exact h_outer.comp z h_inner

/-- ⭐ **PROVED — chain rule for `EntireXiPullback`.**
`Λ[EntireXiPullback](z) = I · Λ[entireRiemannXi](½ + I·z)`. The
Mathlib-grounded analogue; the critical-shift arithmetic is ξ-agnostic. -/
theorem EntireXiPullback_logDeriv_chain_rule (z : ℂ) :
    logDerivativeResponse EntireXiPullback z =
      Complex.I *
        (deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z) /
          entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z)) := by
  have h_outer : HasDerivAt entireRiemannXi
                  (deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z))
                  ((1 / 2 : ℂ) + Complex.I * z) :=
    (entireRiemannXi_differentiableAt _).hasDerivAt
  have h_inner := hasDerivAt_critical_shift z
  have h_chain : HasDerivAt
                  (fun w : ℂ => entireRiemannXi ((1 / 2 : ℂ) + Complex.I * w))
                  (deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z)
                    * Complex.I) z := by
    have h := h_outer.comp z h_inner
    simpa [Function.comp_def] using h
  unfold logDerivativeResponse EntireXiPullback
  rw [h_chain.deriv]
  ring

end OverflowResidueRH
